require("@nomicfoundation/hardhat-toolbox");

module.exports = {
  solidity: {
    version: "0.8.20",
    settings: {
      optimizer: {
        enabled: true,
        runs: 20000,
      },
      evmVersion: "london",
    },
  },
  networks: {
    arbitrum: {
      url: `https://arb1.arbitrum.io/rpc`, 
      accounts: ["Private Key Address"]
    },
    goerli: {
      url: `https://goerli.infura.io/v3/def61e49a0f4447d86d6c4b60252ff30`,
      accounts: ["Private Key Address"]
    },
    arbitrumSepolia: {
      url: `https://sepolia-rollup.arbitrum.io/rpc`,
      accounts: ["Private Key Address"]
    }
  },
  etherscan: {
    apiKey: {
      arbitrum: 'MXRXWW5CWJAWD1MKWGFZQB7S7NFAAPMI7J',
      goerli: 'UZGSDXRHUQW98WSZW77467VMD734A6Y5II',
      arbitrumSepolia: '2767FIJIRQ4FVIJKITDXI9VDCTNI36FD5Q'
    },
    customChains: [
      {
        network: "arbitrumSepolia",
        chainId: 421614,
        urls: {
          apiURL: "https://api-sepolia.arbiscan.io/api",
          browserURL: "https://sepolia.arbiscan.io"
        }
      },
      {
        network: "arbitrum",
        chainId: 42161,
        urls: {
          apiURL: "https://api.arbiscan.io/api",
          browserURL: "https://arbiscan.io"
        }
      }
    ]
  }
};
