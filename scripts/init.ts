// Migrations are an early feature. Currently, they're nothing more than this
// single deploy script that's invoked from the CLI, injecting a provider
// configured from the workspace's Anchor.toml.

import * as anchor from "@project-serum/anchor";
import { OlympusproSol } from '../target/types/olympuspro_sol';
import { Program } from '@project-serum/anchor';

const init = async() => {
    // Configure client to use the provider.
    anchor.setProvider(anchor.Provider.env());

    // Add your deploy script here.
    const program = anchor.workspace.OlympusproSol as Program<OlympusproSol>;
    const [olympusData, olympusDataBump] = await anchor.web3.PublicKey.findProgramAddress([Buffer.from("olympus")], program.programId);
    const olympusDao = anchor.getProvider().wallet;

    const initTx = program.transaction.initialize({
        accounts : {
          olympusData,
          olympusDao : olympusDao.publicKey,
          systemProgram: anchor.web3.SystemProgram.programId,
          payer : olympusDao.publicKey
        }
      });
    
      initTx.feePayer = olympusDao.publicKey;
      initTx.recentBlockhash = (await anchor.getProvider().connection.getRecentBlockhash()).blockhash;
      const signedTx = await olympusDao.signTransaction(initTx);
      const txId = await anchor.getProvider().connection.sendRawTransaction(signedTx.serialize())
      console.log(`init txid: ${txId}`);
      await anchor.getProvider().connection.confirmTransaction(txId);
      console.log("init confirmed");
}  

init();