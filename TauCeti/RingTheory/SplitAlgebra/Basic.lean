/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange

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
map, splittings of free algebras, contraction of ideals and the tensor purity of split algebras.
The descent of splittings along faithfully flat
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
* `TauCeti.splitAlgebra_of_free`: a nontrivial algebra that is free as a module is split.
* `TauCeti.SplitAlgebra.comap_map_eq_self`: every ideal `I` of `R` is contracted from a split
  algebra `S`, i.e. `I S ∩ R = I`.
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

/-- A linear map `ρ : S → R` with `ρ 1 = 1` splits `S` over `R`. -/
theorem SplitAlgebra.of_map_one (ρ : S →ₗ[R] R) (hρ : ρ 1 = 1) : SplitAlgebra R S :=
  ⟨ρ, hρ⟩

/-- A linear functional `ρ : S → R` whose value at `1` is a unit already gives a splitting,
after rescaling by the inverse of that unit. -/
theorem SplitAlgebra.of_isUnit_map_one (ρ : S →ₗ[R] R) (hρ : IsUnit (ρ 1)) :
    SplitAlgebra R S :=
  ⟨hρ.unit⁻¹.val • ρ, by simp⟩

variable (R S) in
/-- `S` is split over `R` exactly when evaluation at `1` on the dual `Hom_R(S, R)` is surjective.
The range of this evaluation is the ideal of `R` formed by the values `ρ 1`. -/
theorem splitAlgebra_iff_eval_surjective :
    SplitAlgebra R S ↔ Function.Surjective (Module.Dual.eval R S 1) := by
  refine ⟨fun ⟨ρ, hρ⟩ r ↦ ⟨r • ρ, by simp [hρ]⟩, fun h ↦ ?_⟩
  obtain ⟨ρ, hρ⟩ := h 1
  exact ⟨ρ, by rwa [Module.Dual.eval_apply] at hρ⟩

variable (R S) in
/-- `S` is split over `R` exactly when the ideal of `R` formed by the values `ρ 1` of linear
functionals `ρ : S → R`, the range of evaluation at `1` on the dual, is the unit ideal. -/
theorem splitAlgebra_iff_range_eval_eq_top :
    SplitAlgebra R S ↔ LinearMap.range (Module.Dual.eval R S 1) = ⊤ := by
  rw [splitAlgebra_iff_eval_surjective, LinearMap.range_eq_top]

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

/-- The unit map of a split algebra is injective. -/
theorem SplitAlgebra.algebraMap_injective (h : SplitAlgebra R S) :
    Function.Injective (algebraMap R S) := by
  obtain ⟨ρ, hρ⟩ := h.exists_leftInverse
  exact hρ.injective

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

/-- A nontrivial algebra that is free as a module is split: for a basis `b` and any index `i`,
the functional `x ↦ b.coord i (b i * x)` takes `1` to `1`. -/
theorem splitAlgebra_of_free [Module.Free R S] [Nontrivial S] : SplitAlgebra R S := by
  let b := Module.Free.chooseBasis R S
  obtain ⟨i⟩ := b.index_nonempty
  exact ⟨b.coord i ∘ₗ LinearMap.mulLeft R (b i), by simp⟩

end Semiring

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Every ideal of `R` is contracted from a split `R`-algebra `S`: `I S ∩ R = I`. Applying a
splitting `ρ` to `∑ aᵢ sᵢ` with `aᵢ ∈ I` gives `∑ aᵢ ρ(sᵢ) ∈ I`. -/
theorem SplitAlgebra.comap_map_eq_self (h : SplitAlgebra R S) (I : Ideal R) :
    (I.map (algebraMap R S)).comap (algebraMap R S) = I := by
  refine le_antisymm (fun x hx ↦ ?_) Ideal.le_comap_map
  obtain ⟨ρ, hρ⟩ := h
  rw [Ideal.mem_comap, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at hx
  have hI : ρ (algebraMap R S x) ∈ I :=
    Submodule.smul_induction_on (p := fun y ↦ ρ y ∈ I) hx
      (fun a ha s _ ↦ by simpa using I.mul_mem_right _ ha)
      fun y z hy hz ↦ by simpa using add_mem hy hz
  simpa [Algebra.algebraMap_eq_smul_one, hρ] using hI

end CommSemiring

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
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨Module.Dual.baseChange R' ρ, by rw [Module.Dual.baseChange_apply_one, hρ, map_one]⟩

/-- A split algebra is tensor-pure: for every `R`-module `M`, the map `m ↦ m ⊗ 1` from `M` to
`M ⊗[R] S` is injective. -/
theorem SplitAlgebra.tmul_one_injective (h : SplitAlgebra R S) (M : Type*) [AddCommMonoid M]
    [Module R M] : Function.Injective fun m : M ↦ m ⊗ₜ[R] (1 : S) := by
  obtain ⟨ρ, hρ⟩ := h
  refine Function.LeftInverse.injective (g := TensorProduct.rid R M ∘ₗ ρ.lTensor M) fun m ↦ ?_
  simp [hρ]

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
