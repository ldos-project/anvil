# Making these code snippets

Run the following shell script on existing heuristics:

```
grep -rl "state->accesses" . | xargs sed -i 's/state->accesses/f_accesses/g'
grep -rl "state->config" . | xargs sed -i 's/state->config/f_config/g'
grep -rl "state->dram_bw" . | xargs sed -i 's/state->dram_bw/f_dram_bw/g'
grep -rl "state->nvm_bw" . | xargs sed -i 's/state->nvm_bw/f_nvm_bw/g'
```

All of these files are examples of heuristics that should PASS the Anvil checker. 