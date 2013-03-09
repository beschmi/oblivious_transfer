oblivious_transfer
==================

Oblivious transfer proof for Naor & Pinkas 2001.

prime_fields.ec : Axiomatization of F_q, do not use integer operation modulo q.

groups_prime_order.ec : Use F_q axiomatization for exponents.

chooser2.ec : chooser security

simul_sender2.ec : sender security in a single step (requires patch
                   for easycrypt trunk)

simul_sender2_multiple_games.ec: sender security in multiple steps (also
                                 requires patch)

patch_pop_uniform.patch : Consider sampling operators (pop) with name
                          sample_uniform_* as uniform.
