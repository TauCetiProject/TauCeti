/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple

/-!
# Second Frobenius–Schur indicators of simple objects

For an object `V` with a right dual in a `k`-linear monoidal category, Frobenius reciprocity
identifies the invariant space `𝟙_ C ⟶ tensorPow V 2` with `Vᘁ ⟶ V`
(`TauCeti.homTensorPowTwoLinearEquiv`).

In a `k`-linear pivotal category with kernels, Schur's lemma controls this hom space whenever `V`
and `Vᘁ` are simple (which holds automatically for `Vᘁ` when `C` is abelian, by
`TauCeti.simple_rightDual`):

* If `V` is not isomorphic to `Vᘁ`, then `Vᘁ ⟶ V` is zero and `ν₂(V) = 0` over any commutative
  ring `k` (`TauCeti.frobeniusSchurIndicator_two_eq_zero_of_isEmpty_iso`).
* Over an algebraically closed field `k` (of any characteristic), if `V ≅ Vᘁ` and `V ⟶ V` is
  finite-dimensional, then `𝟙_ C ⟶ tensorPow V 2` is one-dimensional and `E_V^{(2)}` is an
  involution on it, so `ν₂(V) = 1` or `ν₂(V) = -1`
  (`TauCeti.frobeniusSchurIndicator_two_eq_one_or_eq_neg_one_of_nonempty_iso`).

Combining the two cases gives the Ng–Schauenburg trichotomy `ν₂(V) ∈ {1, 0, -1}`
(`TauCeti.frobeniusSchurIndicator_two_eq_one_or_eq_zero_or_eq_neg_one`) and the self-duality
criterion `ν₂(V) ≠ 0 ↔ Nonempty (V ≅ Vᘁ)` (`TauCeti.frobeniusSchurIndicator_two_ne_zero_iff`),
valid in arbitrary characteristic.

## Main declarations

* `TauCeti.frobeniusSchurIndicator_two_eq_zero_of_isEmpty_iso` and
  `TauCeti.frobeniusSchurIndicator_two_eq_one_or_eq_neg_one_of_nonempty_iso`: the non-self-dual
  and self-dual cases for `ν₂(V)`;
* `TauCeti.frobeniusSchurIndicator_two_eq_one_or_eq_zero_or_eq_neg_one`: the trichotomy
  `ν₂(V) = 1 ∨ ν₂(V) = 0 ∨ ν₂(V) = -1` for simple objects;
* `TauCeti.frobeniusSchurIndicator_two_ne_zero_iff` and
  `TauCeti.frobeniusSchurIndicator_two_eq_zero_iff`: `ν₂(V) ≠ 0` iff `V ≅ Vᘁ`.

## References

* S.-H. Ng, P. Schauenburg, *Higher Frobenius–Schur indicators for pivotal categories*, in
  *Hopf algebras and generalizations*, Contemp. Math. **441** (2007), 63–90, §§4–5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

section Pivotal

variable [RigidCategory C] [PivotalCategory C] [HasKernels C]

/-- If `V` and `Vᘁ` are simple and `V` is not isomorphic to `Vᘁ`, then `ν₂(V) = 0`. -/
theorem frobeniusSchurIndicator_two_eq_zero_of_isEmpty_iso (k : Type w) [CommRing k] [Linear k C]
    [MonoidalLinear k C] (V : C) [Simple V] [Simple Vᘁ] (h : IsEmpty (V ≅ Vᘁ)) :
    frobeniusSchurIndicator k V 2 = 0 := by
  have : Subsingleton (Vᘁ ⟶ V) :=
    subsingleton_of_forall_eq 0 fun f ↦ by
      by_contra hf
      have : IsIso f := isIso_of_hom_simple hf
      exact h.false (asIso f).symm
  have : Subsingleton (𝟙_ C ⟶ tensorPow V 2) :=
    (homTensorPowTwoLinearEquiv k V).subsingleton
  rw [frobeniusSchurIndicator_two, Subsingleton.elim (frobeniusSchurEnd k V 1) 0, map_zero]

section IsAlgClosed

variable (k : Type w) [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
variable (V : C) [Simple V] [FiniteDimensional k (V ⟶ V)]

/-- If `V` is simple with finite-dimensional endomorphisms over an algebraically closed field and
`V ≅ Vᘁ`, then `ν₂(V) = 1` or `ν₂(V) = -1`. -/
theorem frobeniusSchurIndicator_two_eq_one_or_eq_neg_one_of_nonempty_iso
    (h : Nonempty (V ≅ Vᘁ)) :
    frobeniusSchurIndicator k V 2 = 1 ∨ frobeniusSchurIndicator k V 2 = -1 := by
  obtain ⟨e⟩ := h
  let L : (𝟙_ C ⟶ tensorPow V 2) ≃ₗ[k] (V ⟶ V) :=
    (homTensorPowTwoLinearEquiv k V).trans (Linear.homCongr k e.symm (Iso.refl V))
  let T : Module.End k (V ⟶ V) := L.conj (frobeniusSchurEnd k V 1)
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (T (𝟙 V))
  have hT : T = c • 1 := by
    ext g
    obtain ⟨d, rfl⟩ := endomorphism_simple_eq_smul_id k g
    rw [map_smul, ← hc, LinearMap.smul_apply, one_apply_eq_self, smul_comm]
  have hc_sq : c ^ 2 = 1 := by
    have hT2 : T (T (𝟙 V)) = 𝟙 V := by
      have h1 := LinearMap.congr_fun (frobeniusSchurEnd_pow_eq_one k V 1) (L.symm (𝟙 V))
      simpa [T, sq] using congrArg L h1
    rw [← hc, map_smul, ← hc, smul_smul, ← sq] at hT2
    exact smul_left_injective k (CategoryTheory.id_ne_zero V) (by simpa using hT2)
  have htr : frobeniusSchurIndicator k V 2 = c := by
    rw [frobeniusSchurIndicator_two, ← LinearMap.trace_conj' (frobeniusSchurEnd k V 1) L]
    -- `T` is definitionally `L.conj (frobeniusSchurEnd k V 1)`.
    change LinearMap.trace k (V ⟶ V) T = c
    rw [hT, map_smul, LinearMap.trace_one, finrank_endomorphism_simple_eq_one k V,
      Nat.cast_one, smul_eq_mul, mul_one]
  rw [htr]
  exact sq_eq_one_iff.mp hc_sq

/-- **Ng–Schauenburg trichotomy**: for a simple object `V` (with `Vᘁ` simple and `V ⟶ V`
finite-dimensional over an algebraically closed field `k`), the second Frobenius–Schur indicator
takes values in `{1, 0, -1}`. -/
theorem frobeniusSchurIndicator_two_eq_one_or_eq_zero_or_eq_neg_one [Simple Vᘁ] :
    frobeniusSchurIndicator k V 2 = 1 ∨ frobeniusSchurIndicator k V 2 = 0 ∨
      frobeniusSchurIndicator k V 2 = -1 := by
  by_cases h : Nonempty (V ≅ Vᘁ)
  · rcases frobeniusSchurIndicator_two_eq_one_or_eq_neg_one_of_nonempty_iso k V h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl
      (frobeniusSchurIndicator_two_eq_zero_of_isEmpty_iso k V (not_nonempty_iff.mp h)))

/-- For a simple object `V` (with `Vᘁ` simple and `V ⟶ V` finite-dimensional over an algebraically
closed field `k`), `ν₂(V) ≠ 0` if and only if `V` is self-dual (`Nonempty (V ≅ Vᘁ)`). -/
theorem frobeniusSchurIndicator_two_ne_zero_iff [Simple Vᘁ] :
    frobeniusSchurIndicator k V 2 ≠ 0 ↔ Nonempty (V ≅ Vᘁ) := by
  refine ⟨fun hne ↦ ?_, fun h ↦ ?_⟩
  · by_contra hemp
    exact hne (frobeniusSchurIndicator_two_eq_zero_of_isEmpty_iso k V (not_nonempty_iff.mp hemp))
  · rcases frobeniusSchurIndicator_two_eq_one_or_eq_neg_one_of_nonempty_iso k V h with h1 | h1 <;>
      simp [h1]

/-- For a simple object `V` (with `Vᘁ` simple and `V ⟶ V` finite-dimensional over an algebraically
closed field `k`), `ν₂(V) = 0` if and only if `V` is not isomorphic to `Vᘁ`. -/
theorem frobeniusSchurIndicator_two_eq_zero_iff [Simple Vᘁ] :
    frobeniusSchurIndicator k V 2 = 0 ↔ IsEmpty (V ≅ Vᘁ) := by
  rw [← not_iff_not, not_isEmpty_iff]
  exact frobeniusSchurIndicator_two_ne_zero_iff k V

end IsAlgClosed

end Pivotal

end TauCeti
