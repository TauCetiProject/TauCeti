/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.LinearAlgebra.Dual.FinitePresentation
public import TauCeti.RingTheory.SplitAlgebra.Basic

import Mathlib.RingTheory.Flat.Localization

/-!
# Descent and local detection of splittings

Let `S` be an `R`-algebra that is finitely presented as an `R`-module (for instance a finite
algebra over a noetherian ring, by `Module.finitePresentation_of_finite`). The values `ρ 1` of
the linear functionals `ρ : S → R` form an ideal `I` of `R`, the range of evaluation at `1` on
the dual, and `S` is split over `R` exactly when `I = R`
(`TauCeti.splitAlgebra_iff_range_eval_eq_top`). Because `Hom_R(S, R)` commutes with flat base
change for finitely presented `S` (`Module.FinitePresentation.isBaseChange_map`), the ideal
attached to `R' ⊗[R] S` over a flat `R`-algebra `R'` is the extension `I R'`
(`TauCeti.Module.Dual.range_eval_one_tmul`). Two consequences
follow:

* splitting descends along faithfully flat maps;
* splitting can be detected after localizing at every maximal ideal.

These are the reductions used to check the direct summand theorem for finite extensions of
regular rings locally and after completion.

## Main results

* `TauCeti.splitAlgebra_tensorProduct_iff_map_range_eval`: for `R'` flat over `R` and `S`
  finitely presented, `R' ⊗[R] S` is split over `R'` exactly when the ideal of values at `1`
  of functionals on `S` generates the unit ideal of `R'`.
* `TauCeti.splitAlgebra_tensorProduct_iff_of_faithfullyFlat`: for `R'` faithfully flat over `R`,
  `R' ⊗[R] S` is split over `R'` exactly when `S` is split over `R`.
* `TauCeti.splitAlgebra_iff_localized_maximal`: `S` is split over `R` exactly when `S_m` is split
  over `R_m` for every maximal ideal `m` of `R`.

## References

* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), Annexe A.2,
  Lemme A.2.1.
-/

public section

open TensorProduct

namespace TauCeti

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

/-- For a flat `R`-algebra `R'` and an `R`-algebra `S` finitely presented as an `R`-module,
`R' ⊗[R] S` is split over `R'` exactly when the ideal of values `ρ 1` of linear functionals
`ρ : S → R` generates the unit ideal of `R'`. -/
theorem splitAlgebra_tensorProduct_iff_map_range_eval (R' : Type*) [CommRing R'] [Algebra R R']
    [Module.Flat R R'] [Module.FinitePresentation R S] :
    SplitAlgebra R' (R' ⊗[R] S) ↔
      Ideal.map (algebraMap R R') (LinearMap.range (Module.Dual.eval R S 1)) = ⊤ := by
  rw [splitAlgebra_iff_range_eval_eq_top, Algebra.TensorProduct.one_def,
    Module.Dual.range_eval_one_tmul]

/-- Splittings descend along faithfully flat maps: for a faithfully flat `R`-algebra `R'` and an
`R`-algebra `S` finitely presented as an `R`-module, `R' ⊗[R] S` is split over `R'` exactly when
`S` is split over `R`. -/
theorem splitAlgebra_tensorProduct_iff_of_faithfullyFlat (R' : Type*) [CommRing R']
    [Algebra R R'] [Module.FaithfullyFlat R R'] [Module.FinitePresentation R S] :
    SplitAlgebra R' (R' ⊗[R] S) ↔ SplitAlgebra R S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.baseChange R'⟩
  rw [splitAlgebra_tensorProduct_iff_map_range_eval] at h
  rw [splitAlgebra_iff_range_eval_eq_top,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') (LinearMap.range _), h]
  exact Ideal.comap_top

/-- Splitting is detected at maximal ideals: an `R`-algebra `S` finitely presented as an
`R`-module is split over `R` exactly when `R_m ⊗[R] S` is split over the localization `R_m` for
every maximal ideal `m` of `R`. -/
theorem splitAlgebra_iff_localized_maximal [Module.FinitePresentation R S] :
    SplitAlgebra R S ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        SplitAlgebra (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] S) := by
  refine ⟨fun h m _ ↦ h.baseChange _, fun h ↦ ?_⟩
  rw [splitAlgebra_iff_range_eval_eq_top]
  by_contra hI
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have := (splitAlgebra_tensorProduct_iff_map_range_eval (Localization.AtPrime m)).1 (h m)
  refine (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime m)).ne_top ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, eq_top_iff, ← this]
  exact Ideal.map_mono hle

end TauCeti
