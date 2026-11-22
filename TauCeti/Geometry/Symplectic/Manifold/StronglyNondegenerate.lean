/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Flat
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Strongly nondegenerate two-forms and their contraction inverse

A smooth two-form `σ` on a manifold modelled on a real normed space `E` has at each point the
flat map `σ♭_x : T_x M → (T_x M →L[ℝ] ℝ)`, `v ↦ σ_x(v, ·)` (`TauCeti.SmoothTwoForm.flat`).
Nondegeneracy (`TauCeti.SmoothTwoForm.IsNondegenerate`) asks that every flat map be injective;
this is *weak* nondegeneracy. *Strong* nondegeneracy asks that every flat map be onto the
continuous dual, and is stated here as the unbundled hypothesis
`∀ x, Function.Surjective (σ.flat x)`. In finite dimensions the two agree
(`TauCeti.SmoothTwoForm.isNondegenerate_iff_isInvertible_flat`); in infinite dimensions strong
nondegeneracy is what makes covectors correspond to vectors. For instance, the canonical form on
`V × (V →L[ℝ] ℝ)` is always weakly nondegenerate, and strongly nondegenerate exactly when `V` is
reflexive.

This file develops the strongly nondegenerate case on any model.

* Strong nondegeneracy implies weak nondegeneracy, with no completeness: if `σ_x(w, ·) = 0`, then
  every `σ_x(v, ·)` vanishes at `w` because `σ` is alternating, hence so does every continuous
  linear form, and `w = 0` by the Hahn–Banach theorem
  (`TauCeti.SmoothTwoForm.injective_flat_of_surjective`,
  `TauCeti.SmoothTwoForm.isNondegenerate_of_surjective_flat`).
* On a Banach model the flat map at a point is then a continuous linear equivalence with the
  continuous dual, by the open mapping theorem (`TauCeti.SmoothTwoForm.flatEquiv`,
  `TauCeti.SmoothTwoForm.isInvertible_flat_iff_surjective`). Its inverse, the **contraction
  inverse**, acts on arbitrary covectors: `(σ♭_x)⁻¹ α` is the unique vector `v` with
  `ι_v σ = α`.
* The contraction inverses depend smoothly on the base point: on a Banach manifold whose flat
  maps are all invertible, they form a smooth section of the bundle `Hom(T*M, TM)`
  (`TauCeti.SmoothTwoForm.contMDiff_inverse_flat`), so the vector field `(σ♭)⁻¹ α` of a `C^n`
  covector field `α` is `C^n` (`TauCeti.SmoothTwoForm.contMDiff_inverse_flat_apply`). This is the
  regularity of the solution of a contraction equation `ι_X σ = α`, as in Moser's argument, and
  of Hamiltonian vector fields, the case `α = df`, in
  `TauCeti.Geometry.Symplectic.Hamiltonian.Manifold`.

## Main declarations

* `TauCeti.SmoothTwoForm.injective_flat_of_surjective`: a flat map onto the dual is injective.
* `TauCeti.SmoothTwoForm.isNondegenerate_of_surjective_flat`: strongly nondegenerate forms are
  nondegenerate.
* `TauCeti.SmoothTwoForm.isInvertible_flat_iff_surjective`: on a Banach model, a flat map is
  invertible exactly when it is onto the dual.
* `TauCeti.SmoothTwoForm.flatEquiv`: the flat map at a point where it is onto the dual, as a
  continuous linear equivalence `T_x M ≃L[ℝ] (T_x M →L[ℝ] ℝ)`.
* `TauCeti.SmoothTwoForm.contMDiff_inverse_flat`: invertible flat maps have contraction inverses
  forming a smooth section of `Hom(T*M, TM)`.
* `TauCeti.SmoothTwoForm.contMDiff_inverse_flat_apply`: the contraction inverse of a `C^n`
  covector field is a `C^n` vector field.

## References

* P. R. Chernoff, J. E. Marsden, *Properties of Infinite Dimensional Hamiltonian Systems*,
  Lecture Notes in Mathematics 425, Springer, 1974, Section 1.2 (weak and strong
  nondegeneracy).
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Addison-Wesley, 1978,
  Section 3.2.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {x : M}

/-- **A flat map onto the dual is injective.** If every continuous linear form on `T_x M` is of
the form `σ_x(v, ·)`, then no nonzero vector `w` has `σ_x(w, ·) = 0`. This holds in any model,
with no completeness. -/
theorem injective_flat_of_surjective (hx : Function.Surjective (σ.flat x)) :
    Function.Injective (σ.flat x) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦
    SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) (V := E) fun ℓ ↦ ?_
  obtain ⟨v, rfl⟩ := hx ℓ
  -- `σ(v, w) = -σ(w, v)`, and `σ(w, ·) = 0`. The goal is stated in the dual of the model space
  -- `E`, so the computation is done in the tangent space and then closed by `exact`.
  have h : σ.flat x v w = 0 := by
    rw [flat_apply, SmoothBundleForm.eval₂_swap, ← flat_apply, hw, zero_apply, neg_zero]
  exact h

/-- **Strong nondegeneracy implies nondegeneracy.** A two-form whose flat maps are all onto the
continuous dual is nondegenerate, in any model. -/
theorem isNondegenerate_of_surjective_flat (h : ∀ x, Function.Surjective (σ.flat x)) :
    σ.IsNondegenerate :=
  isNondegenerate_iff_separatingLeft.2 fun x w hw ↦
    injective_flat_of_surjective (h x) <| by
      ext v
      rw [flat_apply, hw, map_zero, zero_apply]

variable [CompleteSpace E]

/-- On a Banach model, the flat map of a two-form at a point is invertible exactly when it is
onto the continuous dual, by the open mapping theorem. -/
theorem isInvertible_flat_iff_surjective :
    (σ.flat x).IsInvertible ↔ Function.Surjective (σ.flat x) :=
  ⟨fun h ↦ h.surjective, fun h ↦
    ContinuousLinearMap.isInvertible_iff_bijective (E := E) (F := E →L[ℝ] ℝ).2
      ⟨injective_flat_of_surjective h, h⟩⟩

variable (σ x) in
/-- The **flat map as an isomorphism** with the continuous dual, at a point of a Banach manifold
where it is onto the dual: `v ↦ σ_x(v, ·)` as a continuous linear equivalence
`T_x M ≃L[ℝ] (T_x M →L[ℝ] ℝ)`. Its inverse is the contraction inverse, sending a covector `α` to
the vector `v` with `σ_x(v, ·) = α`. -/
def flatEquiv (hx : Function.Surjective (σ.flat x)) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  .ofBijective (E := E) (F := E →L[ℝ] ℝ) (σ.flat x)
    (LinearMap.ker_eq_bot.2 (injective_flat_of_surjective hx)) (LinearMap.range_eq_top.2 hx)

@[simp]
theorem coe_flatEquiv (hx : Function.Surjective (σ.flat x)) :
    (σ.flatEquiv x hx : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) = σ.flat x :=
  ContinuousLinearEquiv.coe_ofBijective (E := E) (F := E →L[ℝ] ℝ) _ _ _

@[simp]
theorem flatEquiv_apply (hx : Function.Surjective (σ.flat x)) (v : TangentSpace I x) :
    σ.flatEquiv x hx v = σ.flat x v :=
  congr($(coe_flatEquiv hx) v)

/-- The inverse of `flatEquiv` is the contraction inverse `(σ♭_x)⁻¹`, Mathlib's inverse of the
flat map as a continuous linear map. -/
@[simp]
theorem flatEquiv_symm_apply (hx : Function.Surjective (σ.flat x))
    (α : TangentSpace I x →L[ℝ] ℝ) :
    (σ.flatEquiv x hx).symm α = (σ.flat x).inverse α := by
  have h := ContinuousLinearMap.inverse_equiv (σ.flatEquiv x hx)
  rw [coe_flatEquiv] at h
  rw [h, ContinuousLinearEquiv.coe_coe]

/-- **Smooth dependence of the contraction inverse.** On a Banach manifold, if every flat map of
`σ` is invertible, as for a strongly nondegenerate form (`isInvertible_flat_iff_surjective`), the
contraction inverses `x ↦ (σ♭_x)⁻¹` form a smooth section of the bundle of linear maps from the
cotangent bundle to the tangent bundle. -/
theorem contMDiff_inverse_flat (h : ∀ x, (σ.flat x).IsInvertible) :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E)
        (E := fun x : M ↦ (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) x
        (σ.flat x).inverse) :=
  σ.contMDiff_flat.clm_bundle_inverse h

/-- **The contraction inverse of a smooth covector field is smooth.** On a Banach manifold, if
every flat map of `σ` is invertible, as for a strongly nondegenerate form, then for a `C^n`
covector field `α`, `n ≤ ∞`, the vector field `x ↦ (σ♭_x)⁻¹ (α x)`, the unique solution `X` of
`ι_X σ = α`, is `C^n`. -/
theorem contMDiff_inverse_flat_apply (h : ∀ x, (σ.flat x).IsInvertible) {n : WithTop ℕ∞}
    (hn : n ≤ ∞) {α : (x : M) → TangentSpace I x →L[ℝ] ℝ}
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (α x))) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, (σ.flat x).inverse (α x)⟩ : TangentBundle I M)) :=
  ((contMDiff_inverse_flat h).of_le hn).clm_bundle_apply hα

end SmoothTwoForm

end TauCeti
