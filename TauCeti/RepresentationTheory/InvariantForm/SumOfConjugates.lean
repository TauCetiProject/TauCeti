/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.PermutationForm

/-!
# Summing a bilinear form over the conjugates of a representation

Summing a bilinear form over the orbit of a representation of a finite group,
`∑_g B (σ g ·) (σ g ·)`, makes it invariant: this is the standard construction that produces
invariant forms out of arbitrary ones.  No division by `|G|` is performed -- as in Mathlib's
`MonoidAlgebra.sumOfConjugates` for a linear map, the undivided sum is the construction, and it
needs no invertibility of the group order.  The sum over the conjugates of a symmetric form is
symmetric.

Over an ordered field the construction also produces a *nonzero* invariant symmetric form on any
nontrivial representation: sum the coordinate dot product read in a basis.
Positivity is what makes the sum nonzero -- on the diagonal the sum of a nonnegative form dominates
its term at `g = 1`, so the sum of a positive definite form is again positive definite -- so it is
the ordering of the field, not a division by `|G|`, that does the work.  For an irreducible complex
representation of a finite group with a real form, this form on the real form, transported to the
complex space, is the nonzero invariant symmetric form that gives Frobenius-Schur indicator `+1`
(`Representation.IsRealForm.frobeniusSchurIndicator_eq_one`).

## Main definitions

* `Representation.sumOfConjugatesForm`: the sum of a bilinear form over the conjugates of a
  representation of a finite group.

## Main results

* `Representation.sumOfConjugatesForm_eq_norm`: that sum is the `Representation.norm` of the form
  for the conjugation action of `G` on bilinear forms.
* `Representation.isInvariantForm_sumOfConjugatesForm`: that sum is invariant.
* `Representation.isSymm_sumOfConjugatesForm`: that sum is symmetric if the form is.
* `Representation.le_sumOfConjugatesForm_apply_self`,
  `Representation.posDef_toQuadraticMap_sumOfConjugatesForm`: over an ordered semiring, that sum
  dominates the form on the diagonal, and is positive definite if the form is.
* `Representation.exists_isInvariantForm_isSymm_ne_zero`: **a representation of a finite group on a
  nontrivial space over an ordered field carries a nonzero invariant symmetric form.**

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

open LinearMap (BilinForm)

open TauCeti

namespace Representation

open TauCeti.Representation

/-! ### Summing a bilinear form over a finite group -/

section Monoid

variable {k G W : Type*} [CommSemiring k] [Monoid G] [Fintype G] [AddCommMonoid W] [Module k W]

/-- The **sum of a bilinear form over the conjugates** of a representation of a finite monoid,
`∑_g B (σ g ·) (σ g ·)`.  No division by `|G|` is performed, so no invertibility of the monoid order
is needed; when `G` is a group the plain sum is already invariant
(`Representation.isInvariantForm_sumOfConjugatesForm`), being the `Representation.norm` of `B` for
the conjugation action of `G` on bilinear forms.  The name follows Mathlib's
`MonoidAlgebra.sumOfConjugates`, the same undivided sum for a linear map. -/
def sumOfConjugatesForm (σ : Representation k G W) (B : BilinForm k W) : BilinForm k W :=
  ∑ g : G, B.comp (σ g) (σ g)

@[simp]
theorem sumOfConjugatesForm_apply (σ : Representation k G W) (B : BilinForm k W) (x y : W) :
    sumOfConjugatesForm σ B x y = ∑ g : G, B (σ g x) (σ g y) := by
  simp [sumOfConjugatesForm, BilinForm.comp_apply]

/-- The sum over the conjugates of a symmetric bilinear form is symmetric. -/
theorem isSymm_sumOfConjugatesForm {σ : Representation k G W} {B : BilinForm k W} (hB : B.IsSymm) :
    (sumOfConjugatesForm σ B).IsSymm :=
  ⟨fun x y => by
    simpa only [sumOfConjugatesForm_apply] using
      Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hB.eq (σ g x) (σ g y)⟩

end Monoid

/-! ### Positivity of the sum over the conjugates -/

section OrderedMonoid

variable {k G W : Type*} [CommSemiring k] [PartialOrder k] [IsOrderedAddMonoid k] [Monoid G]
  [Fintype G] [AddCommMonoid W] [Module k W]

/-- The sum over the conjugates of a form with nonnegative diagonal dominates its term at `g = 1`,
which is the value of the form itself. -/
theorem le_sumOfConjugatesForm_apply_self {σ : Representation k G W} {B : BilinForm k W}
    (hB : ∀ y, 0 ≤ B y y) (x : W) : B x x ≤ sumOfConjugatesForm σ B x x := by
  rw [sumOfConjugatesForm_apply]
  have h := Finset.single_le_sum (f := fun g : G => B (σ g x) (σ g x)) (fun g _ => hB _)
    (Finset.mem_univ 1)
  rwa [map_one, one_apply_eq_self] at h

/-- The sum over the conjugates of a positive-definite form is positive definite. -/
theorem posDef_toQuadraticMap_sumOfConjugatesForm {σ : Representation k G W} {B : BilinForm k W}
    (hB : B.toQuadraticMap.PosDef) : (sumOfConjugatesForm σ B).toQuadraticMap.PosDef := by
  have hnonneg (y : W) : 0 ≤ B y y := by
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using hB.nonneg y
  intro x hx
  have hpos := hB x hx
  rw [LinearMap.BilinMap.toQuadraticMap_apply] at hpos ⊢
  exact hpos.trans_le (le_sumOfConjugatesForm_apply_self hnonneg x)

end OrderedMonoid

section Group

variable {k G W : Type*} [CommSemiring k] [Group G] [Fintype G] [AddCommMonoid W] [Module k W]

/-- **The conjugate sum of a form is the norm of the form** for the conjugation action of `G` on
bilinear forms, `Representation.linHom σ σ.dual`: the two sums differ only by the reindexing
`g ↦ g⁻¹`, since the conjugation action moves `σ g⁻¹` into both arguments. -/
theorem sumOfConjugatesForm_eq_norm (σ : Representation k G W) (B : BilinForm k W) :
    sumOfConjugatesForm σ B = norm (linHom σ σ.dual) B := by
  ext x y
  rw [sumOfConjugatesForm_apply, norm]
  simp only [LinearMap.sum_apply, linHom_apply, LinearMap.coe_comp, Function.comp_apply,
    dual_apply, Module.Dual.transpose_apply]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp

/-- The sum of a bilinear form over the conjugates of a representation of a finite group is
invariant: it is a norm for the conjugation action of `G` on bilinear forms
(`Representation.sumOfConjugatesForm_eq_norm`), and a norm is fixed by that action. -/
@[simp]
theorem isInvariantForm_sumOfConjugatesForm (σ : Representation k G W) (B : BilinForm k W) :
    IsInvariantForm σ (sumOfConjugatesForm σ B) := by
  rw [isInvariantForm_iff, sumOfConjugatesForm_eq_norm]
  intro h x y
  simpa only [linHom_apply, LinearMap.coe_comp, Function.comp_apply, dual_apply,
    Module.Dual.transpose_apply, inv_inv] using
    DFunLike.congr_fun (DFunLike.congr_fun (self_norm_apply (linHom σ σ.dual) h⁻¹ B) x) y

end Group

/-! ### A nonzero invariant symmetric form over an ordered field -/

section OrderedField

variable {k G W : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [Group G] [Finite G]
  [AddCommGroup W] [Module k W]

/-- **A representation of a finite group on a nontrivial space over an ordered field carries a
nonzero invariant symmetric form.**  The space need not be finite-dimensional.  This is the input
over `ℝ` to the orthogonality of a representation with a real form. -/
theorem exists_isInvariantForm_isSymm_ne_zero (σ : Representation k G W) [Nontrivial W] :
    ∃ B : BilinForm k W, IsInvariantForm σ B ∧ B.IsSymm ∧ B ≠ 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  -- The permutation form of the coordinate space, pulled back along the coordinates of a basis, is
  -- symmetric and positive definite, hence so is its sum over the conjugates, which is nonzero.
  let e : W ≃ₗ[k] MonoidAlgebra k (Module.Free.ChooseBasisIndex k W) :=
    (Module.Free.chooseBasis k W).repr.trans (MonoidAlgebra.coeffLinearEquiv k).symm
  set B₀ : BilinForm k W :=
    (TauCeti.permutationForm k (Module.Free.ChooseBasisIndex k W)).compl₁₂ e.toLinearMap
      e.toLinearMap with hB₀
  have hB₀pos : B₀.toQuadraticMap.PosDef := fun y hy => by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hB₀, LinearMap.compl₁₂_apply]
    exact TauCeti.permutationForm_self_pos (e.map_ne_zero_iff.mpr hy)
  refine ⟨sumOfConjugatesForm σ B₀, isInvariantForm_sumOfConjugatesForm σ B₀,
    isSymm_sumOfConjugatesForm ?_, ?_⟩
  · exact ⟨fun x y => TauCeti.permutationForm_comm _ _⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : W)
    intro hzero
    have := posDef_toQuadraticMap_sumOfConjugatesForm (σ := σ) hB₀pos x hx
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hzero] at this
    exact lt_irrefl _ this

end OrderedField

end Representation
