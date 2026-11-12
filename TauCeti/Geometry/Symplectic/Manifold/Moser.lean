/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Moser's stability theorem for families of symplectic forms

A smooth time-dependent family of two-forms `σ_t` on a manifold `M` is represented by a single
smooth two-form `σ` on `ℝ × M`, whose slices `σ_t = ι_t^* σ` are the forms of the family, and
whose time derivative `∂_t σ` (`TauCeti.SmoothForm.timeDeriv`) has as slices the velocities
`d/dt σ_t`. A second smooth form `α` on `ℝ × M`, of degree one, gives a family of one-forms
`α_t`. When every `σ_t` is nondegenerate, the **Moser vector field**
`TauCeti.SmoothTwoForm.moserVectorField` is the time-dependent vector field `X_t` determined by

`ι_{X_t} σ_t = -α_t`,

that is `X_t = (σ_t♭)⁻¹ (-α_t)`, with `σ_t♭ : v ↦ σ_t(v, ·)` the flat map
(`TauCeti.SmoothTwoForm.eq_moserVectorField_iff`). It depends smoothly on time and point
(`TauCeti.SmoothTwoForm.contMDiff_moserVectorField`). If moreover every `σ_t` is closed and the
family moves by exact forms with the chosen primitives, `∂_t σ_t = dα_t`, then Cartan's formula
gives **Moser's equation** `∂_t σ_t + L_{X_t} σ_t = d α_t + d ι_{X_t} σ_t = 0`
(`TauCeti.SmoothTwoForm.timeDeriv_add_mlieDerivForm_moserVectorField`).

On a compact manifold without boundary, the time-dependent flow `φ_{s,t}` of the Moser vector
field is defined for all times (`TauCeti.SmoothTwoForm.moserDiffeomorph`). **Moser's stability
theorem** says that this isotopy carries the forms of the family into one another:

`φ_{s,t}^* σ_t = σ_s`

(`TauCeti.SmoothTwoForm.mpullback_moserDiffeomorph`). In particular, a smooth family of symplectic
forms on a closed manifold whose velocities are exact, with primitives depending smoothly on
time, consists of mutually symplectomorphic forms, by symplectomorphisms isotopic to the identity.
The isotopy fixes every point at which all the primitives `α_t` vanish, because the Moser vector
field vanishes there (`TauCeti.SmoothTwoForm.moserDiffeomorph_apply_eq_self`). This is the form in
which relative versions of the theorem are used: primitives vanishing along a submanifold give an
isotopy fixing that submanifold pointwise.

The primitives `α_t` are part of the data of the theorem. Producing them from a family of
cohomologous symplectic forms is a separate step, not taken here.

## Main definitions

* `TauCeti.SmoothTwoForm.moserVectorField`: the Moser vector field `X_t = (σ_t♭)⁻¹ (-α_t)`.
* `TauCeti.SmoothTwoForm.moserDiffeomorph`: on a compact manifold, its time-dependent flow from
  time `s` to time `t`, as a diffeomorphism.

## Main results

* `TauCeti.SmoothTwoForm.eq_moserVectorField_iff`: the Moser vector field is characterized by
  `ι_{X_t} σ_t = -α_t`.
* `TauCeti.SmoothTwoForm.contMDiff_moserVectorField`: the Moser vector field is jointly smooth.
* `TauCeti.SmoothTwoForm.timeDeriv_add_mlieDerivForm_moserVectorField`: Moser's equation
  `∂_t σ_t + L_{X_t} σ_t = 0`.
* `TauCeti.SmoothTwoForm.mpullback_moserDiffeomorph`: Moser's stability theorem
  `φ_{s,t}^* σ_t = σ_s`.
* `TauCeti.SmoothTwoForm.contMDiff_moserDiffeomorph`: the flow maps form a smooth isotopy.
* `TauCeti.SmoothTwoForm.moserDiffeomorph_apply_eq_self`: the isotopy fixes the points at which
  every primitive `α_t` vanishes.

## Implementation notes

The formalization is adapted from Tau Ceti's Gray stability theorem for contact structures,
`TauCeti.Geometry.Contact.Gray`: the representation of families as forms on `ℝ × M`, the
construction of the isotopy from the complete time-dependent flow on a compact manifold, and its
identity, inverse, composition and smoothness laws follow `TauCeti.SmoothForm.grayDiffeomorph`
and its API, and both theorems conclude via the same Moser principle for form families,
`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq`.

## References

* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965), 286–294.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy and Moser stability).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 7.2 (the Moser trick).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The Moser vector field -/

variable (σ : SmoothTwoForm (𝓘(ℝ, ℝ).prod I) (ℝ × M))
  (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)

/-- The **Moser vector field** of a smooth family of two-forms `σ_t = ι_t^* σ` and a smooth family
of one-forms `α_t = ι_t^* α` on `M`, represented by forms `σ` and `α` on `ℝ × M`. At time `t` it is
`(σ_t♭)⁻¹ (-α_t)`, with `σ_t♭` the flat map of the slice: when `σ_t` is nondegenerate, this is the
unique vector field `X_t` with `ι_{X_t} σ_t = -α_t`
(`TauCeti.SmoothTwoForm.eq_moserVectorField_iff`). The inverse is `ContinuousLinearMap.inverse`,
so the field vanishes at points where the flat map is not invertible. -/
def moserVectorField (t : ℝ) (x : M) : TangentSpace I x :=
  (SmoothTwoForm.flat (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)
      x).inverse
    (SmoothForm.degreeOneEquiv
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α)) x)

/-- The Moser vector field is the inverse flat map of the slice applied to `-α_t`. -/
theorem moserVectorField_def (t : ℝ) (x : M) :
    σ.moserVectorField α t x =
      (SmoothTwoForm.flat (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
          σ) x).inverse
        (SmoothForm.degreeOneEquiv
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α)) x) :=
  (rfl)

variable {σ} [FiniteDimensional ℝ E]
  (hσ : ∀ t, SmoothTwoForm.IsNondegenerate
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
include hσ

/-- At each time, the Moser vector field is the smooth vector field which the nondegenerate
contraction equivalence `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` of the slice `σ_t`
assigns to `-α_t`. -/
theorem moserVectorField_eq_interiorEquiv_symm (t : ℝ) :
    σ.moserVectorField α t = (hσ t).interiorEquiv.symm
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (-α)) :=
  funext fun x ↦ ((hσ t).interiorEquiv_symm_apply _ x).symm

/-- **The Moser equation** `ι_{X_t} σ_t = -α_t`, as an identity of forms. -/
theorem interior_moserVectorField (t : ℝ) :
    RoughForm.interior (σ.moserVectorField α t)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 =
      -(SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 := by
  rw [moserVectorField_eq_interiorEquiv_symm α hσ, ← coe_interiorₗ,
    IsNondegenerate.interiorₗ_interiorEquiv_symm, map_neg, NegMemClass.coe_neg]

/-- **The Moser equation** `ι_{X_t} σ_t = -α_t`, evaluated on a tangent vector:
`σ_t(X_t, v) = -α_t(v)`. -/
theorem apply_moserVectorField (t : ℝ) (x : M) (v : TangentSpace I x) :
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 x
        ![σ.moserVectorField α t x, v] =
      -(SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] := by
  have h := congr($(interior_moserVectorField α hσ t) x ![v])
  rwa [RoughForm.interior_apply] at h

/-- **The Moser vector field is characterized by the Moser equation**: a tangent vector is the
value of the Moser vector field at time `t` exactly when `σ_t(v, w) = -α_t(w)` for every `w`. -/
theorem eq_moserVectorField_iff {t : ℝ} {x : M} {v : TangentSpace I x} :
    v = σ.moserVectorField α t x ↔
      ∀ w, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 x ![v, w] =
        -(SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w] := by
  refine ⟨fun hv w ↦ hv ▸ apply_moserVectorField α hσ t x w, fun hv ↦ ?_⟩
  refine sub_eq_zero.1 <| (isNondegenerate_iff_separatingLeft.1 (hσ t)) x _ fun w ↦ ?_
  -- By bilinearity, `σ_t(v - X_t, w) = -α_t(w) + α_t(w) = 0`.
  rw [← flat_apply, map_sub, sub_apply, flat_apply, flat_apply,
    SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, hv w,
    apply_moserVectorField α hσ, sub_self]

/-- **The Moser vector field vanishes where the primitive does**: `X_t(x) = 0` exactly when
`α_t` vanishes at `x`. -/
@[simp]
theorem moserVectorField_eq_zero_iff {t : ℝ} {x : M} :
    σ.moserVectorField α t x = 0 ↔
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x = 0 := by
  rw [eq_comm, eq_moserVectorField_iff α hσ]
  -- The form `σ_t` vanishes on pairs with a zero entry, so the Moser equation for `v = 0` says
  -- that `α_t` vanishes at `x`.
  have h₀ (w : TangentSpace I x) :
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 x ![0, w] = 0 :=
    ContinuousAlternatingMap.map_coord_zero _ 0 rfl
  refine ⟨fun h ↦ ?_, fun h w ↦ by rw [h₀, h]; simp⟩
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  rw [hv, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ← neg_eq_zero, ← h, h₀]

/-- **Joint regularity of the Moser vector field.** For a smooth family of nondegenerate two-forms
`σ_t` and a smooth family of one-forms `α_t`, the Moser vector field depends smoothly on time and
point: `(t, x) ↦ (x, X_t(x))` is smooth into the tangent bundle. -/
theorem contMDiff_moserVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, σ.moserVectorField α p.1 p.2⟩ : TangentBundle I M)) := fun p ↦ by
  -- The flat maps of the slices and their inverses depend smoothly on the parameter.
  have hflat := SmoothTwoForm.contMDiffAt_sectionAlong_flatL (b := Prod.snd)
    (σ := fun q : ℝ × M ↦
      (SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) σ).1 q.2)
    (SmoothForm.contMDiff_mpullback_prodMk σ p)
  have hinv := ContMDiffAt.clm_bundle_inverse (E₁ := TangentSpace I)
    (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) (b := Prod.snd) (x := p)
    (ϕ := fun q : ℝ × M ↦ SmoothTwoForm.flat
      (SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) σ) q.2)
    (hflat.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ by simp only [flat_def]))
    ((hσ p.1).isInvertible_flat p.2)
  -- So do the slices of `-α`, as covector fields.
  have hα := (SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
    (α := fun q : ℝ × M ↦
      SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) (-α))).2
    (SmoothForm.contMDiff_mpullback_prodMk (-α) p)
  exact hinv.clm_bundle_apply hα

/-- At a fixed time, the Moser vector field is a differentiable vector field. -/
theorem mdifferentiable_moserVectorField (t : ℝ) :
    MDifferentiable I I.tangent (fun x ↦ (σ.moserVectorField α t x : TangentBundle I M)) :=
  ((contMDiff_moserVectorField α hσ).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable
    (by simp)

variable {α}
  (hcl : ∀ t, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).IsClosed)
  (hdα : ∀ t, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      σ.timeDeriv).1 =
    mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1)

include hcl hdα in
/-- **Moser's equation.** If the slices `σ_t` are closed and nondegenerate, and their velocities
are the exterior derivatives `∂_t σ_t = dα_t`, then the Moser vector field satisfies
`∂_t σ_t + L_{X_t} σ_t = 0`. By Cartan's formula, `L_{X_t} σ_t = d ι_{X_t} σ_t = -dα_t`. -/
theorem timeDeriv_add_mlieDerivForm_moserVectorField (t : ℝ) :
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ.timeDeriv).1 +
        mlieDerivForm (σ.moserVectorField α t)
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 =
      0 := by
  rw [SmoothForm.mlieDerivForm_eq_mextDeriv_interior (mdifferentiable_moserVectorField α hσ t)
    (hcl t), interior_moserVectorField α hσ, mextDeriv_neg, hdα, add_neg_cancel]

/-! ### Moser's stability theorem on compact manifolds -/

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

variable (α) in
/-- On a compact manifold, the Moser vector field has a complete suspension: its time-dependent
flow is defined for all times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_moserVectorField :
    IsCompleteVectorField (timeDependentSuspensionField (σ.moserVectorField α)) :=
  isCompleteVectorField_timeDependentSuspensionField
    ((contMDiff_moserVectorField α hσ).of_le (by simp)) isCompact_univ (by simp)

variable (α) in
/-- **Moser's isotopy.** On a compact manifold without boundary, the time-dependent flow of the
Moser vector field of a smooth family of nondegenerate two-forms `σ_t` and one-forms `α_t`, from
time `s` to time `t`, as a diffeomorphism. When the forms `σ_t` are closed and `∂_t σ_t = dα_t`,
it pulls `σ_t` back to `σ_s` (`TauCeti.SmoothTwoForm.mpullback_moserDiffeomorph`). -/
def moserDiffeomorph (s t : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  timeDependentFlowDiffeomorph
    (isCompleteVectorField_timeDependentSuspensionField_moserVectorField α hσ) le_top
    (contMDiff_moserVectorField α hσ) s t

variable (α) in
/-- Moser's isotopy is the time-dependent flow of the Moser vector field. -/
theorem moserDiffeomorph_apply (s t : ℝ) (x : M) :
    moserDiffeomorph α hσ s t x = timeDependentFlowOf (σ.moserVectorField α) s t x :=
  timeDependentFlowDiffeomorph_apply _ _ _ s t x

variable (α) in
/-- The inverse of Moser's isotopy from `s` to `t` is Moser's isotopy from `t` to `s`. -/
@[simp]
theorem moserDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (moserDiffeomorph α hσ s t).symm x = moserDiffeomorph α hσ t s x :=
  (timeDependentFlowDiffeomorph_symm_apply _ _ _ s t x).trans
    (moserDiffeomorph_apply α hσ t s x).symm

variable (α) in
/-- Moser's isotopy from a time to itself is the identity. -/
@[simp]
theorem moserDiffeomorph_self (s : ℝ) (x : M) : moserDiffeomorph α hσ s s x = x := by
  rw [moserDiffeomorph_apply, timeDependentFlowOf_self]

variable (α) in
/-- Moser's isotopy composes: flowing from `r` to `s` and then from `s` to `t` is flowing from `r`
to `t`. -/
@[simp]
theorem moserDiffeomorph_moserDiffeomorph (r s t : ℝ) (x : M) :
    moserDiffeomorph α hσ s t (moserDiffeomorph α hσ r s x) = moserDiffeomorph α hσ r t x := by
  simp only [moserDiffeomorph_apply]
  exact timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_moserVectorField α hσ)
    ((contMDiff_moserVectorField α hσ).of_le (by simp)) r s t x

variable (α) in
/-- Moser's isotopy depends smoothly on the final time and the point. -/
theorem contMDiff_moserDiffeomorph (s : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ moserDiffeomorph α hσ s p.1 p.2) := by
  simp only [moserDiffeomorph_apply]
  exact (contMDiff_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_moserVectorField α hσ) le_top
    (contMDiff_moserVectorField α hσ)).comp
      (((contMDiff_const (c := s)).prodMk contMDiff_fst).prodMk contMDiff_snd)

include hcl hdα in
/-- **Moser's stability theorem.** On a compact manifold without boundary, let `σ_t` be a smooth
family of symplectic forms whose velocities are exact, `∂_t σ_t = dα_t` for a smooth family of
one-forms `α_t`. Then the time-dependent flow `φ_{s,t}` of the Moser vector field, defined by
`ι_{X_t} σ_t = -α_t`, carries the forms into one another: `φ_{s,t}^* σ_t = σ_s`. -/
theorem mpullback_moserDiffeomorph (s t : ℝ) :
    SmoothForm.mpullback (moserDiffeomorph α hσ s t) (moserDiffeomorph α hσ s t).contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) σ := by
  have hL (t : ℝ) :
      TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.1) +
        mlieDerivForm (σ.moserVectorField α t)
          (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) σ.1) =
      0 := by
    simpa only [SmoothForm.coe_mpullback, SmoothForm.coe_timeDeriv] using
      timeDeriv_add_mlieDerivForm_moserVectorField hσ hcl hdα t
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_eq
    ((contMDiff_moserVectorField α hσ).of_le (by simp))
    (isCompleteVectorField_timeDependentSuspensionField_moserVectorField α hσ)
    (σ.contMDiff.of_le (by simp)) hL s t
  have hφ : ⇑(moserDiffeomorph α hσ s t) = timeDependentFlowOf (σ.moserVectorField α) s t :=
    funext (moserDiffeomorph_apply α hσ s t)
  exact Subtype.ext (by simpa only [SmoothForm.coe_mpullback, hφ] using h)

/-- **Moser's isotopy fixes the zeros of the primitives**: if `α_t` vanishes at `x` for every time
`t`, then every map of Moser's isotopy fixes `x`. -/
theorem moserDiffeomorph_apply_eq_self {x : M}
    (hx : ∀ u, (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x = 0)
    (s t : ℝ) : moserDiffeomorph α hσ s t x = x := by
  rw [moserDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    ((contMDiff_moserVectorField α hσ).of_le (by simp))
    (fun u ↦ (moserVectorField_eq_zero_iff α hσ).2 (hx u)) s t

end TauCeti.SmoothTwoForm
