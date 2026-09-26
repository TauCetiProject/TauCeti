/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# Tame ramification and the global different exponent

At a finite prime `w` over `v` of a number-field extension, the coefficient of the different
equals `e(w/v) - 1` exactly when the canonical completed extension `L_w / K_v` is tamely ramified,
and it is at least `e(w/v)` exactly when `L_w / K_v` is wildly ramified. These criteria read tame
and wild ramification of the completed extension directly from the global different exponent.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, Theorem 2.6.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The global different exponent at `w` is `e(w/v) - 1` precisely when the canonical
completed extension is tamely ramified. -/
theorem multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff_isTamelyRamified :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) =
      w.asIdeal.ramificationIdx (𝓞 K) - 1 ↔
    TauCeti.IsTamelyRamified (v.adicCompletion K) (w.adicCompletion L) :=
  (TauCeti.multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff (𝓞 K) v.ne_bot
    w.asIdeal).trans <| (and_iff_right (by infer_instance)).trans
      (isTamelyRamified_adicCompletion_iff v w).symm

/-- The global different exponent at `w` is at least `e(w/v)` precisely when the canonical
completed extension is wildly ramified. -/
theorem ramificationIdx_le_multiplicity_differentIdeal_iff_isWildlyRamified :
    w.asIdeal.ramificationIdx (𝓞 K) ≤
      multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ↔
    TauCeti.IsWildlyRamified (v.adicCompletion K) (w.adicCompletion L) :=
  (TauCeti.ramificationIdx_le_multiplicity_differentIdeal_iff (𝓞 K) v.ne_bot w.asIdeal).trans <|
    (or_iff_right (not_not_intro (by infer_instance))).trans
      (isWildlyRamified_adicCompletion_iff v w).symm

end IsDedekindDomain.HeightOneSpectrum

end
