/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.Flow.Eulerian
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.MixedPartial
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The two-parameter identity for flux forms

Let `σ` be a closed two-form on a manifold `M`, for instance a symplectic form, and let
`φ_(t, u)` be a two-parameter family of diffeomorphisms of `M`, jointly smooth in
`((t, u), x)`. Write

`X = (∂_t φ) ∘ φ⁻¹`, `Y = (∂_u φ) ∘ φ⁻¹`

for its Eulerian velocity fields in the two parameter directions (`TauCeti.eulerianField`), and

`β_t = φ^* ι_X σ`, `β_u = φ^* ι_Y σ`,

for the pulled-back contraction one-forms, so that `β_t` is the integrand `φ_t^* ι_(X_t) σ` of the
flux form of the isotopy `t ↦ φ_(t, u)` (`TauCeti.Diffeotopy.fluxForm`). This file proves the
**two-parameter identity**

`∂_u β_t - ∂_t β_u = d_M (σ(X, Y) ∘ φ)`

(`TauCeti.SmoothForm.IsClosed.deriv_sub_deriv_eq_mvfderiv_eulerianField`), evaluated on a tangent
vector `v ∈ T_x M`: `(β_t)_x(v) = σ_(φ x)(X (φ x), dφ_x v)` and `(σ(X, Y) ∘ φ)(x) =
σ_(φ x)(X (φ x), Y (φ x))`. Integrated over a square of parameters, it is the classical argument
that the flux of an isotopy only depends on its homotopy class with fixed end points; Tau Ceti
proves that invariance through the homotopy operator instead
(`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`). Only the closedness of `σ` is used:
the maps `φ_(t, u)` need not preserve `σ`, `σ` need not be nondegenerate, and `M` need not be
compact.

The identity is the mixed-partial identity of the closed two-form `Φ^* σ` on `(ℝ × ℝ) × M`, for
`Φ((t, u), x) = φ_(t, u) x` (`TauCeti.SmoothForm.fderiv_apply_sub_fderiv_apply_eq_mvfderiv_apply`):
the differential of `Φ` sends `∂_t` and `∂_u` to the velocities `X ∘ φ` and `Y ∘ φ`, and a vertical
vector `v` to `dφ_x v`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism and its homotopy invariance).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Bundle TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The differential of a two-parameter family -/

section Family

variable {φ : ℝ × ℝ → M ≃ M}
  (hφ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) I ∞ (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2))
include hφ

/-- The differential of the uncurried family sends `∂_t` to the Eulerian velocity of
`t ↦ φ_(t, u)`. -/
private theorem mfderiv_apply_one_zero (q : ℝ × ℝ) (y : M) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) I (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2) (q, y) ((1, 0), 0) =
      eulerianField I (fun s ↦ φ (s, q.2)) q.1 (φ q y) :=
  (eulerianField_apply_eq_mfderiv_apply_mk_zero (g := fun s ↦ (s, q.2))
    ((hφ (q, y)).mdifferentiableAt (by simp))
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).symm

/-- The differential of the uncurried family sends `∂_u` to the Eulerian velocity of
`u ↦ φ_(t, u)`. -/
private theorem mfderiv_apply_zero_one (q : ℝ × ℝ) (y : M) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) I (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2) (q, y) ((0, 1), 0) =
      eulerianField I (fun s ↦ φ (q.1, s)) q.2 (φ q y) :=
  (eulerianField_apply_eq_mfderiv_apply_mk_zero (g := fun s ↦ (q.1, s))
    ((hφ (q, y)).mdifferentiableAt (by simp))
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))).symm

/-- The differential of the uncurried family sends a vertical vector `(0, w)` to `dφ_q w`. -/
private theorem mfderiv_apply_zero_mk (q : ℝ × ℝ) (y : M) (w : TangentSpace I y) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) I (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2) (q, y) (0, w) =
      mfderiv I I (φ q) y w :=
  ((hφ (q, y)).mdifferentiableAt (by simp)).mfderiv_uncurry_apply_zero_mk (f := fun q y ↦ φ q y) w

end Family

/-! ### The two-parameter identity -/

variable [CompleteSpace E] [IsManifold I 2 M]

/-- **The two-parameter identity for flux forms.** Let `σ` be a closed two-form and `φ_(t, u)` a
jointly smooth two-parameter family of diffeomorphisms, with Eulerian velocity fields `X` in the
direction of `t` and `Y` in the direction of `u`. The pulled-back contraction one-forms
`β_t = φ^* ι_X σ` and `β_u = φ^* ι_Y σ` satisfy `∂_u β_t - ∂_t β_u = d (σ(X, Y) ∘ φ)`, here
evaluated on a tangent vector `v` at `x`. -/
theorem SmoothForm.IsClosed.deriv_sub_deriv_eq_mvfderiv_eulerianField {σ : SmoothForm I M F 2}
    (hσ : σ.IsClosed) (φ : ℝ × ℝ → M ≃ M)
    (hφ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) I ∞ (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2))
    (t u : ℝ) (x : M) (v : TangentSpace I x) :
    deriv (fun u' ↦ σ.val (φ (t, u') x)
        ![eulerianField I (fun s ↦ φ (s, u')) t (φ (t, u') x), mfderiv I I (φ (t, u')) x v]) u -
      deriv (fun t' ↦ σ.val (φ (t', u) x)
        ![eulerianField I (fun s ↦ φ (t', s)) u (φ (t', u) x), mfderiv I I (φ (t', u)) x v]) t =
      mvfderiv I (fun y ↦ σ.val (φ (t, u) y)
        ![eulerianField I (fun s ↦ φ (s, u)) t (φ (t, u) y),
          eulerianField I (fun s ↦ φ (t, s)) u (φ (t, u) y)]) x v := by
  -- The pullback `η = Φ^* σ` along the uncurried family is a closed form on `(ℝ × ℝ) × M`.
  set η := SmoothForm.mpullback (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2) hφ σ
  have hηc : mextDeriv η.val ((t, u), x) = 0 :=
    congrFun ((isClosed_def _).1 (hσ.mpullback _ hφ)) ((t, u), x)
  have hval (z : (ℝ × ℝ) × M) (w₁ w₂ : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) z) :
      η.val z ![w₁, w₂] = σ.val (φ z.1 z.2) ![mfderiv _ I (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2) z w₁,
        mfderiv _ I (fun z : (ℝ × ℝ) × M ↦ φ z.1 z.2) z w₂] := by
    rw [SmoothForm.coe_mpullback, mpullback_apply_pair]
  -- Parameter derivatives along the coordinate directions are ordinary derivatives.
  have hdu {g : ℝ × ℝ → F} (hg : DifferentiableAt ℝ g (t, u)) :
      fderiv ℝ g (t, u) (0, 1) = deriv (fun u' ↦ g (t, u')) u :=
    (hg.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_const u t).prodMk (hasDerivAt_id u))).deriv.symm
  have hdt {g : ℝ × ℝ → F} (hg : DifferentiableAt ℝ g (t, u)) :
      fderiv ℝ g (t, u) (1, 0) = deriv (fun t' ↦ g (t', u)) t :=
    (hg.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))).deriv.symm
  have h := fderiv_apply_sub_fderiv_apply_eq_mvfderiv_apply η hηc ((1 : ℝ), (0 : ℝ))
    ((0 : ℝ), (1 : ℝ)) v
  rw [hdu (g := fun q ↦ η.val (q, x) ![((1, 0), 0), (0, v)])
      (differentiableAt_apply_prodMk η (t, u) x ![((1, 0), 0), (0, v)]),
    hdt (g := fun q ↦ η.val (q, x) ![((0, 1), 0), (0, v)])
      (differentiableAt_apply_prodMk η (t, u) x ![((0, 1), 0), (0, v)])] at h
  -- Read the three functions through `σ`, the Eulerian velocities and the differential of `φ`.
  have e₁ : (fun u' ↦ η.val ((t, u'), x) ![((1, 0), 0), (0, v)]) = fun u' ↦ σ.val (φ (t, u') x)
      ![eulerianField I (fun s ↦ φ (s, u')) t (φ (t, u') x), mfderiv I I (φ (t, u')) x v] :=
    funext fun u' ↦ (hval _ _ _).trans
      (by rw [mfderiv_apply_one_zero hφ, mfderiv_apply_zero_mk hφ])
  have e₂ : (fun t' ↦ η.val ((t', u), x) ![((0, 1), 0), (0, v)]) = fun t' ↦ σ.val (φ (t', u) x)
      ![eulerianField I (fun s ↦ φ (t', s)) u (φ (t', u) x), mfderiv I I (φ (t', u)) x v] :=
    funext fun t' ↦ (hval _ _ _).trans
      (by rw [mfderiv_apply_zero_one hφ, mfderiv_apply_zero_mk hφ])
  have e₃ : (fun y ↦ η.val ((t, u), y) ![((1, 0), 0), ((0, 1), 0)]) = fun y ↦ σ.val (φ (t, u) y)
      ![eulerianField I (fun s ↦ φ (s, u)) t (φ (t, u) y),
        eulerianField I (fun s ↦ φ (t, s)) u (φ (t, u) y)] :=
    funext fun y ↦ (hval _ _ _).trans
      (by rw [mfderiv_apply_one_zero hφ, mfderiv_apply_zero_one hφ])
  rw [← e₁, ← e₂, ← e₃]
  exact h

end TauCeti
