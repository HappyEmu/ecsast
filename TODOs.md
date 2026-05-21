# TODOs

- **T1** — `lex/stress_big_blocks` regressed +10.2% in `ffd90e6` vs. `4907572`; profile `lex_ident_or_keyword` (extra `use`/`pub` arms) and the `::` peek in `lex_one`.
