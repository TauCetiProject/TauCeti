module

public import TauCeti.Probability.Martingale.Crossings.Pathwise
public import TauCeti.Probability.Martingale.Crossings.Bounds
public import TauCeti.Probability.Martingale.Crossings.AntitoneLimit

/-!
# Downcrossings and pathwise reversal lemmas — re-export shim

Umbrella for the crossing-based reverse-martingale infrastructure. The contents live in three
sub-files:

* `Crossings/Pathwise.lean` — `downcrossingsBefore`, `downcrossings`, congruence lemmas,
  `upBefore_le_downBefore_rev_succ`
* `Crossings/Bounds.lean` — `upcrossings_bdd_uniform` (uniform-in-`N` bound on upcrossings of the
  reverse martingale)
* `Crossings/AntitoneLimit.lean` — `condExp_exists_ae_limit_antitone`, `ae_limit_is_condexp_iInf`

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Crossings.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/
