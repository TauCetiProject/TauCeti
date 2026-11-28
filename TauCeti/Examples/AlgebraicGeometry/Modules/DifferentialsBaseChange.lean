/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.RingTheory.Kaehler.BaseChange
import TauCeti.FieldTheory.RatFunc.Kaehler
import TauCeti.RingTheory.Kaehler.UnramifiedBase

/-!
# Examples of the base-change map of relative differentials

Let `R → R'` be a ring map, `X` a scheme over `R` and `X' = X ×_R R'`, with projection `g'`. Over
an affine chart `X = Spec A`, `X' = Spec B` with `B = R' ⊗_R A`, the comparison map
`c_{g'} : g'^* Ω_{X/R} → Ω_{X'/R}` is `KaehlerDifferential.mapBaseChange R A B`
(`TauCeti.AlgebraicGeometry.cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv`), the map
`e : Ω_{X'/R} → Ω_{X'/R'}` is `KaehlerDifferential.map R R' B B`, and the base-change map
`b_{g'} = e ∘ c_{g'}` is Mathlib's isomorphism `KaehlerDifferential.tensorKaehlerEquiv`
(`TauCeti.map_comp_mapBaseChange_eq_tensorKaehlerEquiv`); on schemes it is
`TauCeti.AlgebraicGeometry.relativeDifferentialsBaseChangeIso`. These examples check the ring
forms of two of these maps:

* for a field `k` and the rational function field `k(s)`, with `X = Spec k`: the comparison map
  `k(s) ⊗_k Ω_{k/k} → Ω_{k(s)/k}` is not surjective, since `Ω_{k/k} = 0` while `ds ≠ 0`
  (`RatFunc.D_X_ne_zero`); `e` kills `ds`; and `b = e ∘ c` is bijective. So a
  base-change map with target the differentials over `R` would not be an isomorphism;
* for `ℤ → 𝔽₂` and `X = 𝔸¹_ℤ`: `b` sends `1 ⊗ dT` to `dT`, and `e` is already bijective, as
  `Ω_{𝔽₂/ℤ} = 0`.

## References

* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0) (Morphisms,
  Lemma 29.33.10): `b_{g'}` is an isomorphism.
-/

public section

open KaehlerDifferential Polynomial TensorProduct

namespace TauCeti.NashBlowups

section RationalFunctionField

variable (k : Type*) [Field k]

/-- For `X = Spec k` and `X' = Spec k(s)`, the comparison map
`c_{g'} : k(s) ⊗_k Ω_{k/k} → Ω_{k(s)/k}` is not surjective: its source vanishes, while
`ds ≠ 0`. -/
theorem not_surjective_mapBaseChange_ratFunc :
    ¬ Function.Surjective (mapBaseChange k k (RatFunc k)) := by
  intro h
  obtain ⟨x, hx⟩ := h (D k (RatFunc k) RatFunc.X)
  rw [Subsingleton.elim x 0, map_zero] at hx
  exact RatFunc.D_X_ne_zero k hx.symm

/-- The map `e : Ω_{k(s)/k} → Ω_{k(s)/k(s)}` kills `ds`, as `Ω_{k(s)/k(s)} = 0`. -/
theorem map_D_X_ratFunc_eq_zero :
    map k (RatFunc k) (RatFunc k) (RatFunc k) (D k (RatFunc k) RatFunc.X) = 0 :=
  Subsingleton.elim _ _

/-- For `X = Spec k` and `X' = Spec k(s)`, the base-change map `b_{g'} = e ∘ c_{g'}` from
`k(s) ⊗_k Ω_{k/k}` to `Ω_{k(s)/k(s)}` is bijective, although `c_{g'}` is not surjective
(`TauCeti.NashBlowups.not_surjective_mapBaseChange_ratFunc`). -/
theorem bijective_map_comp_mapBaseChange_ratFunc :
    Function.Bijective
      ((map k (RatFunc k) (RatFunc k) (RatFunc k)).comp (mapBaseChange k k (RatFunc k))) := by
  rw [map_comp_mapBaseChange_eq_tensorKaehlerEquiv]
  exact LinearEquiv.bijective _

end RationalFunctionField

section IntegersModTwo

attribute [local instance] Polynomial.algebra

/-- For `ℤ → 𝔽₂` and `X = 𝔸¹_ℤ`, the base-change map `𝔽₂[T] ⊗_{ℤ[T]} Ω_{ℤ[T]/ℤ} ≅ Ω_{𝔽₂[T]/𝔽₂}`
sends `1 ⊗ dT` to `dT`. -/
theorem tensorKaehlerEquiv_one_tmul_D_X_zmod_two :
    tensorKaehlerEquiv ℤ (ZMod 2) ℤ[X] (ZMod 2)[X] (1 ⊗ₜ D ℤ ℤ[X] X) =
      D (ZMod 2) (ZMod 2)[X] X := by
  simp

/-- For `ℤ → 𝔽₂` and `X = 𝔸¹_ℤ`, the map `e : Ω_{𝔽₂[T]/ℤ} → Ω_{𝔽₂[T]/𝔽₂}` is already bijective,
since `Ω_{𝔽₂/ℤ} = 0`. -/
theorem bijective_map_zmod_two :
    Function.Bijective (map ℤ (ZMod 2) (ZMod 2)[X] (ZMod 2)[X]) := by
  have : Algebra.FormallyUnramified ℤ (ZMod 2) :=
    ⟨subsingleton_of_surjective ℤ (ZMod 2) ZMod.intCast_surjective⟩
  exact map_bijective_of_formallyUnramified_base ℤ (ZMod 2) (ZMod 2)[X]

end IntegersModTwo

end TauCeti.NashBlowups
