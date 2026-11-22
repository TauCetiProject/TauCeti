/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.LinearAlgebra.Unimodular

import Mathlib.Tactic.NormNum

/-!
# Split algebras

An `R`-algebra `S` is *split* over `R` when its unit map `R → S` admits an `R`-linear
retraction, that is, an `R`-linear map `ρ : S → R` with `ρ 1 = 1`. No multiplicativity is asked
of `ρ`: the real part `ℂ → ℝ` splits `ℝ → ℂ` although it is not a ring map. This is the notion
in the statement of the direct summand theorem (Hochster's conjecture, proved by André), which
asserts that every finite injective algebra over a regular ring is split.

This file sets up the predicate and its elementary laws: the evaluation-at-one description,
composition along towers, restriction along algebra maps, base change, injectivity of the unit
map and the tensor purity of split algebras. The descent of splittings along faithfully flat
maps and their detection at maximal ideals are in
`TauCeti/RingTheory/SplitAlgebra/Descent.lean`.

## Main definitions

* `TauCeti.SplitAlgebra R S`: the unit map `R → S` has an `R`-linear retraction.

## Main results

* `TauCeti.splitAlgebra_iff_eval_surjective`: `S` is split exactly when evaluation at `1` on the
  dual `Module.Dual R S` is surjective.
* `TauCeti.splitAlgebra_iff_range_eval_eq_top`: `S` is split exactly when the ideal of values
  `ρ 1` of functionals `ρ : S → R` is the unit ideal.
* `TauCeti.SplitAlgebra.trans`: splittings compose along a tower `R → S → T`.
* `TauCeti.SplitAlgebra.of_algHom`: if `T` is split over `R`, so is every `R`-algebra mapping to
  `T`.
* `TauCeti.SplitAlgebra.baseChange`: splittings are stable under base change.
* `TauCeti.SplitAlgebra.algebraMap_injective`: the unit map of a split algebra is injective.
* `TauCeti.SplitAlgebra.tmul_one_injective`: a split algebra is tensor-pure, i.e.
  `m ↦ m ⊗ 1 : M → M ⊗[R] S` is injective for every `R`-module `M`.
* `TauCeti.not_splitAlgebra_int_rat`: the injective flat map `ℤ → ℚ` is not split.

## References

* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), §0.1 and
  Annexe A.2.
* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212
  (2018), Theorem 1.1.
-/

public section

open TensorProduct

namespace TauCeti

/-- An `R`-algebra `S` is split over `R` when its unit map `R → S` has an `R`-linear retraction:
some `R`-linear map `ρ : S → R` takes `1` to `1`. The retraction need not be multiplicative. -/
def SplitAlgebra (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] : Prop :=
  ∃ ρ : S →ₗ[R] R, ρ 1 = 1

section Semiring

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- Unfolding `SplitAlgebra`: `S` is split over `R` exactly when some `R`-linear map `S → R`
takes `1` to `1`. -/
theorem splitAlgebra_iff_exists_linearMap :
    SplitAlgebra R S ↔ ∃ ρ : S →ₗ[R] R, ρ 1 = 1 :=
  Iff.rfl

/-- An algebra is split exactly when its unit is unimodular as a module element. -/
theorem splitAlgebra_iff_isUnimodular_one :
    SplitAlgebra R S ↔ Module.IsUnimodular R (1 : S) :=
  splitAlgebra_iff_exists_linearMap.trans Module.isUnimodular_iff.symm

/-- A linear map `ρ : S → R` with `ρ 1 = 1` splits `S` over `R`. -/
theorem SplitAlgebra.of_map_one (ρ : S →ₗ[R] R) (hρ : ρ 1 = 1) : SplitAlgebra R S :=
  ⟨ρ, hρ⟩

/-- A linear functional `ρ : S → R` whose value at `1` is a unit already gives a splitting,
after rescaling by the inverse of that unit. -/
theorem SplitAlgebra.of_isUnit_map_one (ρ : S →ₗ[R] R) (hρ : IsUnit (ρ 1)) :
    SplitAlgebra R S :=
  splitAlgebra_iff_isUnimodular_one.mpr (Module.isUnimodular_iff_exists_isUnit_apply.mpr ⟨ρ, hρ⟩)

variable (R S) in
/-- `S` is split over `R` exactly when evaluation at `1` on the dual `Hom_R(S, R)` is surjective.
The range of this evaluation is the ideal of `R` formed by the values `ρ 1`. -/
theorem splitAlgebra_iff_eval_surjective :
    SplitAlgebra R S ↔ Function.Surjective (Module.Dual.eval R S 1) :=
  splitAlgebra_iff_isUnimodular_one.trans Module.isUnimodular_iff_eval_surjective

variable (R S) in
/-- `S` is split over `R` exactly when the ideal of `R` formed by the values `ρ 1` of linear
functionals `ρ : S → R`, the range of evaluation at `1` on the dual, is the unit ideal. -/
theorem splitAlgebra_iff_range_eval_eq_top :
    SplitAlgebra R S ↔ LinearMap.range (Module.Dual.eval R S 1) = ⊤ :=
  splitAlgebra_iff_isUnimodular_one.trans Module.isUnimodular_iff_range_eval_eq_top

variable (R) in
/-- Every commutative semiring is split over itself, by the identity. -/
theorem SplitAlgebra.self : SplitAlgebra R R :=
  ⟨LinearMap.id, rfl⟩

/-- If `T` is split over `R`, then so is every `R`-algebra `S` with an `R`-algebra map to `T`.
In particular, in a tower `R → S → T` with `T` split over `R`, the middle term is split over
`R`, and being split is invariant under `R`-algebra isomorphism. -/
theorem SplitAlgebra.of_algHom [Semiring T] [Algebra R T] (f : S →ₐ[R] T)
    (h : SplitAlgebra R T) : SplitAlgebra R S := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ ∘ₗ f.toLinearMap, by simp [hρ]⟩

/-- Being split is invariant under isomorphism of `R`-algebras. -/
theorem SplitAlgebra.iff_of_equiv [Semiring T] [Algebra R T] (e : S ≃ₐ[R] T) :
    SplitAlgebra R S ↔ SplitAlgebra R T :=
  ⟨of_algHom e.symm.toAlgHom, of_algHom e.toAlgHom⟩

/-- The unit map of a split algebra has a left inverse, namely any splitting. -/
theorem SplitAlgebra.exists_leftInverse (h : SplitAlgebra R S) :
    ∃ ρ : S →ₗ[R] R, Function.LeftInverse ρ (algebraMap R S) := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, fun r ↦ by simp [Algebra.algebraMap_eq_smul_one, hρ]⟩

/-- An algebra is split exactly when its unit map has a linear left inverse. -/
theorem splitAlgebra_iff_exists_leftInverse :
    SplitAlgebra R S ↔ ∃ ρ : S →ₗ[R] R, Function.LeftInverse ρ (algebraMap R S) :=
  ⟨SplitAlgebra.exists_leftInverse, fun ⟨ρ, hρ⟩ ↦ .of_map_one ρ (by simpa using hρ 1)⟩

/-- The unit map of a split algebra is injective. -/
theorem SplitAlgebra.algebraMap_injective (h : SplitAlgebra R S) :
    Function.Injective (algebraMap R S) := by
  intro a b hab
  exact (splitAlgebra_iff_isUnimodular_one.mp h).smul_left_injective
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hab)

/-- A split algebra over a nontrivial semiring is nontrivial. In particular the zero algebra
over a nontrivial semiring is not split. -/
theorem SplitAlgebra.nontrivial [Nontrivial R] (h : SplitAlgebra R S) : Nontrivial S :=
  h.algebraMap_injective.nontrivial

/-- A nonzero algebra over a semifield that is projective as a module (for instance any
nonzero algebra over a field) is split: `1` extends to a linear functional taking the
value `1`. -/
theorem splitAlgebra_of_projective {K : Type*} [Semifield K] [Algebra K S]
    [Module.Projective K S] [Nontrivial S] : SplitAlgebra K S :=
  Module.Projective.exists_dual_eq_one K one_ne_zero

end Semiring

section Tower

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Splittings compose: if `S` is split over `R` and `T` is split over `S`, then `T` is split
over `R`. -/
theorem SplitAlgebra.trans (hRS : SplitAlgebra R S) (hST : SplitAlgebra S T) :
    SplitAlgebra R T := by
  obtain ⟨ρ, hρ⟩ := hRS
  obtain ⟨σ, hσ⟩ := hST
  exact ⟨ρ ∘ₗ σ.restrictScalars R, by simp [hσ, hρ]⟩

end Tower

section BaseChange

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- Splittings are stable under base change: if `S` is split over `R`, then `R' ⊗[R] S` is split
over `R'` for every commutative `R`-algebra `R'`. -/
theorem SplitAlgebra.baseChange (R' : Type*) [CommSemiring R'] [Algebra R R']
    (h : SplitAlgebra R S) : SplitAlgebra R' (R' ⊗[R] S) := by
  apply splitAlgebra_iff_isUnimodular_one.mpr
  simpa only [Algebra.TensorProduct.one_def] using
    (splitAlgebra_iff_isUnimodular_one.mp h).one_tmul (S := R')

/-- A split algebra is tensor-pure: for every `R`-module `M`, the map `m ↦ m ⊗ 1` from `M` to
`M ⊗[R] S` is injective. -/
theorem SplitAlgebra.tmul_one_injective (h : SplitAlgebra R S) (M : Type*) [AddCommMonoid M]
    [Module R M] : Function.Injective fun m : M ↦ m ⊗ₜ[R] (1 : S) :=
  (splitAlgebra_iff_isUnimodular_one.mp h).tmul_left_injective

end BaseChange

section Examples

/-- The injective flat map `ℤ → ℚ` is not split: a `ℤ`-linear map `ρ : ℚ → ℤ` satisfies
`ρ 1 = 2 * ρ (1 / 2)`, so `ρ 1` is even. In fact `Hom_ℤ(ℚ, ℤ) = 0`. -/
theorem not_splitAlgebra_int_rat : ¬ SplitAlgebra ℤ ℚ := by
  rintro ⟨ρ, hρ⟩
  have h2 : ρ 1 = 2 * ρ (1 / 2) := by
    rw [← smul_eq_mul, ← map_smul]
    norm_num
  omega

end Examples

end TauCeti
