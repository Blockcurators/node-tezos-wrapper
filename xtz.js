const axios = require('axios');
const bs58check = require('bs58check');
const tempSodium = require('libsodium-wrappers');
const bip39 = require('bip39');
const pbkdf2 = require('pbkdf2');
const bcrypt = require('bcrypt');
const MyCronJobs = require('cron').CronJob;
const xtzDb = require('./drivers/xtz-db');
const CONFIG = require('../configs/coins/xtz');
const logger = require('./logger');

const tezosCoinInfo = {
  NAME: CONFIG.NAME,
  SHORT_NAME: CONFIG.SHORT_NAME,
  SHORT_NAME_CAPS: CONFIG.SHORT_NAME_CAPS,
  WEBSITE_URL: CONFIG.WEBSITE_URL,
  BLOCKEXPLORER_URL: CONFIG.BLOCKEXPLORER_URL,
  COINMARKETCAP_URL: CONFIG.COINMARKETCAP_URL,
};

const RPC_URL = `http://${CONFIG.HOST}:${CONFIG.PORT}`;

let sodium;
const counters = {};
const reveals = {};
/*
  {
    addressSender: {
      addressReceiver1: count,
      addressReceiver2: count,
    },
  },
*/
let transferIncrements = {};
let currentBlockHeight = -1;

const helpers = {
  insertTransactionIncrement: (senderAddress, receiverAddress) => {
    if (transferIncrements[senderAddress]) {
      if (transferIncrements[senderAddress][receiverAddress]) {
        transferIncrements[senderAddress][receiverAddress] += 1;
      } else {
        transferIncrements[senderAddress][receiverAddress] = 1;
      }
    } else {
      transferIncrements[senderAddress] = {};
      transferIncrements[senderAddress][receiverAddress] = 1;
    }
  },
  getTransferIncrement: (senderAddress, receiverAddress) => {
    if (!transferIncrements[senderAddress]) {
      return 0;
    }
    if (!transferIncrements[senderAddress][receiverAddress]) {
      return 0;
    }
    return transferIncrements[senderAddress][receiverAddress];
  },
  getAddedTransferIncrement: (senderAddress, receivingAddress) => {
    const increment = helpers.getTransferIncrement(senderAddress, receivingAddress);
    const addedTransferIncrement = increment * CONFIG.DEFAULT_COUNTER_INCREMENT_AMOUNT;
    return addedTransferIncrement;
  },
};

const prefix = {
  tz1: new Uint8Array([6, 161, 159]),
  tz2: new Uint8Array([6, 161, 161]),
  KT: new Uint8Array([2, 90, 121]),

  edpk: new Uint8Array([13, 15, 37, 217]),
  edsk2: new Uint8Array([13, 15, 58, 7]),
  spsk: new Uint8Array([17, 162, 224, 201]),
  p2sk: new Uint8Array([16, 81, 238, 189]),

  sppk: new Uint8Array([3, 254, 226, 86]),
  p2pk: new Uint8Array([3, 178, 139, 127]),

  edsk: new Uint8Array([43, 246, 78, 7]),
  edsig: new Uint8Array([9, 245, 205, 134, 18]),
  spsig1: new Uint8Array([13, 115, 101, 19, 63]),
  p2sig: new Uint8Array([54, 240, 44, 52]),
  sig: new Uint8Array([4, 130, 43]),

  Net: new Uint8Array([87, 82, 0]),
  nce: new Uint8Array([69, 220, 169]),
  b: new Uint8Array([1, 52]),
  o: new Uint8Array([5, 116]),
  Lo: new Uint8Array([133, 233]),
  LLo: new Uint8Array([29, 159, 109]),
  P: new Uint8Array([2, 170]),
  Co: new Uint8Array([79, 179]),
  id: new Uint8Array([153, 103]),
};

const watermark = {
  block: new Uint8Array([1]),
  endorsement: new Uint8Array([2]),
  generic: new Uint8Array([3]),
};

const utility = {
  mutez: (tz) => {
    let r = tz.toFixed(6) * 1000000;
    if (r > 4294967296) r = r.toString();
    return r;
  },
  b58cencode: (payload, tprefix) => {
    const n = new Uint8Array(tprefix.length + payload.length);
    n.set(tprefix);
    n.set(payload, tprefix.length);
    return bs58check.encode(Buffer.from(n, 'hex'));
  },
  b58cdecode: (enc, tprefix) => bs58check.decode(enc).slice(tprefix.length),
  buf2hex: (buffer) => {
    const byteArray = new Uint8Array(buffer);
    const hexParts = [];
    for (let i = 0; i < byteArray.length; i += 1) {
      const hex = byteArray[i].toString(16);
      const paddedHex = (`00${hex}`).slice(-2);
      hexParts.push(paddedHex);
    }
    return hexParts.join('');
  },
  hex2buf: (hex) => new Uint8Array(hex.match(/[\da-f]{2}/gi).map((h) => parseInt(h, 16))),
  mergebuf: (b1, b2) => {
    const r = new Uint8Array(b1.length + b2.length);
    r.set(b1);
    r.set(b2, b1.length);
    return r;
  },
};

const cryptoService = {
  init: async () => {
    await tempSodium.ready;
    sodium = tempSodium;
  },
  extractKeys: (sk) => {
    const pref = sk.substr(0, 4);
    switch (pref) {
      case 'edsk':
        if (sk.length === 98) {
          return {
            pk: utility.b58cencode(utility.b58cdecode(sk, prefix.edsk).slice(32), prefix.edpk),
            pkh: utility.b58cencode(sodium.crypto_generichash(20, utility.b58cdecode(sk, prefix.edsk).slice(32)), prefix.tz1),
            sk,
          };
        }
        if (sk.length === 54) { // seed
          const s = utility.b58cdecode(sk, prefix.edsk2);
          const kp = sodium.crypto_sign_seed_keypair(s);
          return {
            sk: utility.b58cencode(kp.privateKey, prefix.edsk),
            pk: utility.b58cencode(kp.publicKey, prefix.edpk),
            pkh: utility.b58cencode(sodium.crypto_generichash(20, kp.publicKey), prefix.tz1),
          };
        }
        return false;
      default:
        return false;
    }
  },
  generateMnemonic: () => bip39.generateMnemonic(160),
  checkAddress: (a) => {
    try {
      utility.b58cdecode(a, prefix.tz1);
      return true;
    } catch (e) {
      return false;
    }
  },
  generateKeysNoSeed: () => {
    const kp = sodium.crypto_sign_keypair();
    return {
      sk: utility.b58cencode(kp.privateKey, prefix.edsk),
      pk: utility.b58cencode(kp.publicKey, prefix.edpk),
      pkh: utility.b58cencode(sodium.crypto_generichash(20, kp.publicKey), prefix.tz1),
    };
  },
  generateKeys: (m, p) => {
    const s = bip39.mnemonicToSeed(m, p).slice(0, 32);
    const kp = sodium.crypto_sign_seed_keypair(s);
    return {
      mnemonic: m,
      passphrase: p,
      sk: utility.b58cencode(kp.privateKey, prefix.edsk),
      pk: utility.b58cencode(kp.publicKey, prefix.edpk),
      pkh: utility.b58cencode(sodium.crypto_generichash(20, kp.publicKey), prefix.tz1),
    };
  },
  generateKeysFromSeedMulti: (m, p, n) => {
    // eslint-disable-next-line no-bitwise
    const nNew = n / (256 ^ 2);
    const s = bip39.mnemonicToSeed(m, pbkdf2.pbkdf2Sync(p, n.toString(36).slice(2), 0, 32, 'sha512').toString()).slice(0, 32);
    const kp = sodium.crypto_sign_seed_keypair(s);
    return {
      mnemonic: m,
      passphrase: p,
      n: nNew,
      sk: utility.b58cencode(kp.privateKey, prefix.edsk),
      pk: utility.b58cencode(kp.publicKey, prefix.edpk),
      pkh: utility.b58cencode(sodium.crypto_generichash(20, kp.publicKey), prefix.tz1),
    };
  },
  sign: (bytes, sk, wm) => {
    let bb = utility.hex2buf(bytes);
    if (wm) {
      bb = utility.mergebuf(wm, bb);
    }
    const sig = sodium.crypto_sign_detached(sodium.crypto_generichash(32, bb), utility.b58cdecode(sk, prefix.edsk), 'uint8array');
    const edsig = utility.b58cencode(sig, prefix.edsig);
    const sbytes = bytes + utility.buf2hex(sig);
    return {
      bytes,
      sig,
      edsig,
      sbytes,
    };
  },
};

const node = {
  activeProvider: RPC_URL,
  query: async (e, o, t) => {
    let method = '';
    let content = o;
    if (!o) {
      if (!t) {
        method = 'GET';
      } else {
        content = {};
      }
    } else if (!t) {
      method = 'POST';
    }
    try {
      const result = await axios({
        method,
        url: `${node.activeProvider}${e}`,
        data: content,
        headers: {
          'Content-Type': 'application/json',
        },
      });
      return result.data;
    } catch (exception) {
      if (exception.response) {
        logger.logError(`${node.activeProvider}${e} ${JSON.stringify(exception.response.data)}`);
      } else {
        logger.logError(`${node.activeProvider}${e} ${exception}`);
      }
      return {
        error: exception,
      };
    }
  },
};

const rpc = {
  getBalance: async (address) => {
    const balance = await node.query(`/chains/main/blocks/head/context/contracts/${address}/balance`);
    return balance;
  },
  sendTransaction: async (keys, to, amount) => {
    const operations = [];
    const head = await rpc.getHeader();

    const transferOperation = {
      kind: 'transaction',
      fee: CONFIG.TRANSACTION_FEE,
      gas_limit: CONFIG.TRANSACTION_GAS_LIMIT,
      storage_limit: CONFIG.TRANSACTION_STORAGE_LIMIT,
      amount: utility.mutez(amount).toString(),
      destination: to,
      source: keys.pkh,
    };
    operations.push(transferOperation);

    let counter;
    if (!counters[keys.pkh]) {
      counter = await rpc.getCounter(keys.pkh);
    } else {
      counter = counters[keys.pkh];
    }
    const managerKey = await rpc.getManager(keys.pkh);

    if (!managerKey && !reveals[keys.pkh]) {
      operations.unshift({
        kind: 'reveal',
        fee: CONFIG.REVEAL_FEE,
        gas_limit: CONFIG.REVEAL_GAS_LIMIT,
        storage_limit: CONFIG.REVEAL_STORAGE_LIMIT,
        public_key: keys.pk,
        source: keys.pkh,
      });
      reveals[keys.pkh] = true;
    }

    for (let i = 0; i < operations.length; i += 1) {
      const newCounter = parseInt(counter, 10) + i + 1;
      counters[keys.pkh] = newCounter;
      operations[i].counter = newCounter.toString();
      operations[i].fee = operations[i].fee.toString();
      operations[i].gas_limit = operations[i].gas_limit.toString();
      operations[i].storage_limit = operations[i].storage_limit.toString();
    }

    const operationsWithBranch = {
      branch: head.hash,
      contents: operations,
    };

    const forgedOperation = await node.query(`/chains/${head.chain_id}/blocks/${head.hash}/helpers/forge/operations`, operationsWithBranch);
    if (forgedOperation.error) {
      delete counters[keys.pkh];
    }
    const signed = cryptoService.sign(forgedOperation, keys.sk, watermark.generic);
    operationsWithBranch.protocol = head.protocol;
    operationsWithBranch.signature = signed.edsig;
    const preAppliedOp = await node.query(`/chains/${head.chain_id}/blocks/${head.hash}/helpers/preapply/operations`, [operationsWithBranch]);
    if (preAppliedOp.error) {
      reveals[keys.pkh] = false;
      delete counters[keys.pkh];
    }

    if (!Array.isArray(preAppliedOp)) {
      reveals[keys.pkh] = false;
      return {
        error: `Rpc Fail: ${preAppliedOp}`,
        msg: 'There was an error forging your transaction. Please wait one confirmation until you tip again',
      };
    }

    const opResponse = [];
    let errors = '';
    for (let i = 0; i < preAppliedOp.length; i += 1) {
      for (let j = 0; j < preAppliedOp[i].contents.length; j += 1) {
        opResponse.push(preAppliedOp[i].contents[j]);
        if (typeof preAppliedOp[i].contents[j].metadata.operation_result !== 'undefined' && preAppliedOp[i].contents[j].metadata.operation_result.status === 'failed') {
          errors = errors.concat(preAppliedOp[i].contents[j].metadata.operation_result.errors);
        }
      }
    }

    if (errors.length) {
      reveals[keys.pkh] = false;
      return {
        error: `Rpc Fail: ${JSON.stringify(errors)}`,
        msg: 'There was an error forging your transaction. Please wait one confirmation until you tip again',
      };
    }
    const injectedResult = await node.query('/injection/operation', JSON.stringify(signed.sbytes));
    if (injectedResult.error) {
      reveals[keys.pkh] = false;
      delete counters[keys.pkh];
    }

    return {
      hash: injectedResult,
    };
  },
  sendBatchedTransaction: async (keys, addresses) => {
    const operations = [];
    const head = await rpc.getHeader();

    const entries = Object.entries(addresses);

    for (let i = 0; i < entries.length; i += 1) {
      const transferOperation = {
        kind: 'transaction',
        fee: CONFIG.TRANSACTION_FEE,
        gas_limit: CONFIG.TRANSACTION_GAS_LIMIT,
        storage_limit: CONFIG.TRANSACTION_STORAGE_LIMIT,
        amount: utility.mutez(parseFloat(entries[i][1])).toString(),
        destination: entries[i][0],
        source: keys.pkh,
      };
      operations.push(transferOperation);
    }

    let counter;
    if (!counters[keys.pkh]) {
      counter = await rpc.getCounter(keys.pkh);
    } else {
      counter = counters[keys.pkh];
    }
    const managerKey = await rpc.getManager(keys.pkh);

    if (!managerKey && !reveals[keys.pkh]) {
      operations.unshift({
        kind: 'reveal',
        fee: CONFIG.REVEAL_FEE,
        gas_limit: CONFIG.REVEAL_GAS_LIMIT,
        storage_limit: CONFIG.REVEAL_STORAGE_LIMIT,
        public_key: keys.pk,
        source: keys.pkh,
      });
      reveals[keys.pkh] = true;
    }

    for (let i = 0; i < operations.length; i += 1) {
      const newCounter = parseInt(counter, 10) + i + 1;
      counters[keys.pkh] = newCounter;
      operations[i].counter = newCounter.toString();
      operations[i].fee = operations[i].fee.toString();
      operations[i].gas_limit = operations[i].gas_limit.toString();
      operations[i].storage_limit = operations[i].storage_limit.toString();
    }

    const operationsWithBranch = {
      branch: head.hash,
      contents: operations,
    };

    const forgedOperation = await node.query(`/chains/${head.chain_id}/blocks/${head.hash}/helpers/forge/operations`, operationsWithBranch);
    if (forgedOperation.error) {
      delete counters[keys.pkh];
    }
    const signed = cryptoService.sign(forgedOperation, keys.sk, watermark.generic);
    operationsWithBranch.protocol = head.protocol;
    operationsWithBranch.signature = signed.edsig;
    const preAppliedOp = await node.query(`/chains/${head.chain_id}/blocks/${head.hash}/helpers/preapply/operations`, [operationsWithBranch]);
    if (preAppliedOp.error) {
      delete counters[keys.pkh];
    }

    if (!Array.isArray(preAppliedOp)) {
      return {
        error: `Rpc Fail: ${preAppliedOp}`,
        msg: 'There was an error forging your transaction. Please wait one confirmation until you tip again',
      };
    }

    const opResponse = [];
    let errors = '';
    for (let i = 0; i < preAppliedOp.length; i += 1) {
      for (let j = 0; j < preAppliedOp[i].contents.length; j += 1) {
        opResponse.push(preAppliedOp[i].contents[j]);
        if (typeof preAppliedOp[i].contents[j].metadata.operation_result !== 'undefined' && preAppliedOp[i].contents[j].metadata.operation_result.status === 'failed') {
          errors = errors.concat(preAppliedOp[i].contents[j].metadata.operation_result.errors);
        }
      }
    }

    if (errors.length) {
      return {
        error: `Rpc Fail: ${JSON.stringify(errors)}`,
        msg: 'There was an error forging your transaction. Please wait one confirmation until you tip again',
      };
    }
    const injectedResult = await node.query('/injection/operation', JSON.stringify(signed.sbytes));
    if (injectedResult.error) {
      delete counters[keys.pkh];
    }

    return {
      hash: injectedResult,
    };
  },
  tryToRevealAddress: async (keys) => {
    const operations = [];
    const head = await rpc.getHeader();
    const managerKey = await rpc.getManager(keys.pkh);
    let counter;
    if (!counters[keys.pkh]) {
      counter = await rpc.getCounter(keys.pkh);
    } else {
      counter = counters[keys.pkh];
    }

    if (!managerKey && !reveals[keys.pkh]) {
      operations.unshift({
        kind: 'reveal',
        fee: CONFIG.REVEAL_FEE,
        gas_limit: CONFIG.REVEAL_GAS_LIMIT,
        storage_limit: CONFIG.REVEAL_STORAGE_LIMIT,
        public_key: keys.pk,
        source: keys.pkh,
      });
      reveals[keys.pkh] = true;
    } else {
      return {
        result: 'Already revealed',
      };
    }

    for (let i = 0; i < operations.length; i += 1) {
      const newCounter = parseInt(counter, 10) + i + 1;
      counters[keys.pkh] = newCounter;
      operations[i].counter = newCounter.toString();
      operations[i].fee = operations[i].fee.toString();
      operations[i].gas_limit = operations[i].gas_limit.toString();
      operations[i].storage_limit = operations[i].storage_limit.toString();
    }

    const operationsWithBranch = {
      branch: head.hash,
      contents: operations,
    };

    const forgedOperation = await node.query(`/chains/${head.chain_id}/blocks/${head.hash}/helpers/forge/operations`, operationsWithBranch);
    if (forgedOperation.error) {
      reveals[keys.pkh] = false;
      delete counters[keys.pkh];
    }
    const signed = cryptoService.sign(forgedOperation, keys.sk, watermark.generic);
    operationsWithBranch.protocol = head.protocol;
    operationsWithBranch.signature = signed.edsig;
    const preAppliedOp = await node.query(`/chains/${head.chain_id}/blocks/${head.hash}/helpers/preapply/operations`, [operationsWithBranch]);
    if (preAppliedOp.error) {
      delete counters[keys.pkh];
    }

    if (!Array.isArray(preAppliedOp)) {
      reveals[keys.pkh] = false;
      return {
        error: `Rpc Fail: ${preAppliedOp}`,
        msg: 'There was an error forging your address reveal. Please wait one confirmation until you tip again',
      };
    }

    const opResponse = [];
    let errors = '';
    for (let i = 0; i < preAppliedOp.length; i += 1) {
      for (let j = 0; j < preAppliedOp[i].contents.length; j += 1) {
        opResponse.push(preAppliedOp[i].contents[j]);
        if (typeof preAppliedOp[i].contents[j].metadata.operation_result !== 'undefined' && preAppliedOp[i].contents[j].metadata.operation_result.status === 'failed') {
          errors = errors.concat(preAppliedOp[i].contents[j].metadata.operation_result.errors);
        }
      }
    }

    if (errors.length) {
      reveals[keys.pkh] = false;
      return {
        error: `Rpc Fail: ${JSON.stringify(errors)}`,
        msg: 'There was an error forging your address reveal. Please wait one confirmation until you tip again',
      };
    }
    const injectedResult = await node.query('/injection/operation', JSON.stringify(signed.sbytes));
    if (injectedResult.error) {
      reveals[keys.pkh] = false;
      delete counters[keys.pkh];
    }

    return {
      hash: injectedResult,
    };
  },
  getManager: async (address) => node.query(`/chains/main/blocks/head/context/contracts/${address}/manager_key`),
  getCounter: async (address) => node.query(`/chains/main/blocks/head/context/contracts/${address}/counter`),
  getHead: async () => node.query('/chains/main/blocks/head'),
  getHeader: async () => node.query('/chains/main/blocks/head/header'),
  updateLocalBlockHeight: async () => {
    const head = await rpc.getHead();
    currentBlockHeight = head.header.level;
  },
};
