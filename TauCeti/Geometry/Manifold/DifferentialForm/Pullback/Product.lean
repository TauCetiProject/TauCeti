/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# Closed forms on a product with a line or a circle that are pulled back from the other factor

Let `M` be a manifold and let `L` be the real line `ℝ` or a circle `AddCircle p`. On `L × M`, let
`∂ₛ = (1, 0)` be the unit vector field along the first factor, and for `s ∈ L` let
`ιₛ : M → L × M`, `y ↦ (s, y)`, be the inclusion of the slice `{s} × M`.

A form `α` on `L × M` is the pullback `pr₂^* β` of a form `β` on `M` when it is basic for the
projection `pr₂`: the contraction `ι_{∂ₛ} α` vanishes, and `α` is invariant along `∂ₛ`. For a
closed form the invariance follows from the vanishing of the contraction, by Cartan's formula
`L_{∂ₛ} α = ι_{∂ₛ} dα + d ι_{∂ₛ} α = 0`. Since the slice restrictions `ιₛ^* α` move with velocity
`ιₛ^* L_{∂ₛ} α` (`TauCeti.hasDerivAt_mpullback_prodMk`), they then do not depend on `s`. As
`ι_{∂ₛ} α = 0`, the form `α` does not see the `∂ₛ`-components of its arguments either, so `α` is
the pullback along `pr₂` of its restriction to any slice:

`α = pr₂^* (ιₛ^* α)`    whenever `dα = 0` and `ι_{∂ₛ} α = 0`.

On the circle the slice restrictions are compared through the covering `ℝ × M → AddCircle p × M`,
whose derivative is the identity. The converse holds for any form pulled back from `M`, so a
smooth closed form on `AddCircle p × M` is pulled back from `M` exactly when `ι_{∂ₛ} α = 0`.

This is the last step of the energy argument for the unperturbed Seiberg–Witten equations on a
product `X = S¹ × Y` of a circle with a three-manifold, with the product metric. There the
integrated energy identity forces the curvature of a solution to satisfy `ι_{∂ₛ} F_A = 0` when
`⟨c₁(L)², [X]⟩ ≥ 0`. The real two-form `i F_A` is closed by the Bianchi identity, so it is the
pullback of a closed two-form on `Y`, and the real first Chern class of the determinant line `L`
is pulled back from `Y`. The energy identity itself is not proved here.

## Main results

* `TauCeti.eq_mpullback_snd_of_interior_eq_zero`: on `G × M` with `G` modelled on `ℝ`, a form with
  `ι_{∂ₛ} α = 0` whose restrictions to the slices are all equal to `β` is `pr₂^* β`.
* `TauCeti.mpullback_prodMk_eq_of_mlieDerivForm_eq_zero`: on `ℝ × M`, a differentiable form with
  `L_{∂ₛ} α = 0` has the same restriction to every slice.
* `TauCeti.mpullback_prodMk_eq_of_interior_eq_zero`: on `ℝ × M`, a differentiable closed form with
  `ι_{∂ₛ} α = 0` has the same restriction to every slice.
* `TauCeti.mpullback_snd_mpullback_prodMk_of_mlieDerivForm_eq_zero`: on `ℝ × M`, a differentiable
  form with `L_{∂ₛ} α = 0` and `ι_{∂ₛ} α = 0` is the pullback along `pr₂` of its restriction to
  any slice.
* `TauCeti.mpullback_snd_mpullback_prodMk_of_interior_eq_zero`: on `ℝ × M`, a differentiable
  closed form with `ι_{∂ₛ} α = 0` is the pullback along `pr₂` of its restriction to any slice.
* `TauCeti.SmoothForm.mpullback_snd_mpullback_prodMk_of_interior_eq_zero`: the same for smooth
  forms on `AddCircle p × M`.
* `TauCeti.SmoothForm.exists_mpullback_snd_eq_iff_interior_eq_zero`: a smooth closed form on
  `AddCircle p × M` is pulled back from `M` exactly when `ι_{∂ₛ} α = 0`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 14.35
  (Cartan's formula).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The slice restrictions of a form on a product -/

/-- Let `G` be a manifold modelled on `ℝ`, such as `ℝ` or a circle. A form on `G × M` whose
contraction with `∂ₛ = (1, 0)` vanishes, and whose restrictions to the slices `{g} × M` are all
equal to `β`, is the pullback of `β` along the second projection. -/
theorem eq_mpullback_snd_of_interior_eq_zero {G : Type*} [TopologicalSpace G]
    [ChartedSpace ℝ G] {α : RoughForm (𝓘(ℝ, ℝ).prod I) (G × M) F (k + 1)}
    {β : RoughForm I M F (k + 1)} (hι : α.interior (fun _ ↦ ((1 : ℝ), (0 : E))) = 0)
    (hβ : ∀ g, mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk g) α = β) :
    α = mpullback (𝓘(ℝ, ℝ).prod I) I Prod.snd β := by
  funext q
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  -- The value of `α` at `q`, read on the model `ℝ × E` of the tangent space.
  let f : (ℝ × E) [⋀^Fin (k + 1)]→ₗ[ℝ] F := (α q).toAlternatingMap
  have hx : f.curryLeft ((1 : ℝ), (0 : E)) = 0 := by
    ext w
    exact (RoughForm.interior_apply _ α q w).symm.trans congr(($hι) q w)
  -- Each tangent vector `v i = (a, w)` is `(0, w) + a • ∂ₛ`, and `α` does not see `∂ₛ`.
  have h := AlternatingMap.map_add_smul_of_curryLeft_eq_zero hx
    (fun i ↦ ((0 : ℝ), (v i).2)) (fun i ↦ (v i).1)
  have hv : (fun i ↦ ((0 : ℝ), (v i).2) + (v i).1 • ((1 : ℝ), (0 : E))) =
      (v : Fin (k + 1) → ℝ × E) := by
    funext i
    ext <;> simp
  rw [hv] at h
  rw [mpullback_apply, ← hβ q.1, mpullback_apply, mfderiv_snd, mfderiv_prod_right]
  -- The derivative of `y ↦ (q.1, y)` sends the second component `w` of `v i` to `(0, w)`.
  exact h

variable [I.Boundaryless] [IsManifold I 2 M]

/-- On `ℝ × M`, a differentiable form invariant along `∂ₛ = (1, 0)`, that is with
`L_{∂ₛ} α = 0`, has the same restriction to every slice `{s} × M`. -/
theorem mpullback_prodMk_eq_of_mlieDerivForm_eq_zero
    {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k}
    (hα : MDifferentiable (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p)))
    (hL : mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α = 0) (s t : ℝ) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α = mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α := by
  funext x
  have hd (u : ℝ) := hasDerivAt_mpullback_prodMk u x (hα (u, x))
  simp only [hL, mpullback_zero, Pi.zero_apply] at hd
  exact is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt) (fun u ↦ (hd u).deriv) s t

/-- On `ℝ × M`, a differentiable closed form whose contraction with `∂ₛ = (1, 0)` vanishes has the
same restriction to every slice `{s} × M`: by Cartan's formula it is invariant along `∂ₛ`. -/
theorem mpullback_prodMk_eq_of_interior_eq_zero
    {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    (hα : MDifferentiable (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F) p (α p)))
    (hdα : mextDeriv α = 0) (hι : α.interior (fun _ ↦ ((1 : ℝ), (0 : E))) = 0) (s t : ℝ) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α = mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α := by
  have hV : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M ↦ (⟨p, ((1 : ℝ), (0 : E))⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    contMDiff_const_prod_field (X := fun _ _ ↦ 0) 1
      ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd)
  refine mpullback_prodMk_eq_of_mlieDerivForm_eq_zero hα ?_ s t
  rw [mlieDerivForm_eq_mextDeriv_interior hα (hV.mdifferentiable one_ne_zero) hdα, hι,
    mextDeriv_zero]

/-- On `ℝ × M`, a differentiable form `α` invariant along `∂ₛ = (1, 0)` whose contraction with
`∂ₛ` vanishes is the pullback along the second projection of its restriction to any slice
`{t} × M`: `α = pr₂^* (ιₜ^* α)`. -/
theorem mpullback_snd_mpullback_prodMk_of_mlieDerivForm_eq_zero
    {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    (hα : MDifferentiable (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F) p (α p)))
    (hL : mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α = 0)
    (hι : α.interior (fun _ ↦ ((1 : ℝ), (0 : E))) = 0) (t : ℝ) :
    mpullback (𝓘(ℝ, ℝ).prod I) I Prod.snd (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) = α :=
  (eq_mpullback_snd_of_interior_eq_zero hι fun s ↦
    mpullback_prodMk_eq_of_mlieDerivForm_eq_zero hα hL s t).symm

/-- On `ℝ × M`, a differentiable closed form `α` whose contraction with `∂ₛ = (1, 0)` vanishes is
the pullback along the second projection of its restriction to any slice `{t} × M`:
`α = pr₂^* (ιₜ^* α)`. -/
theorem mpullback_snd_mpullback_prodMk_of_interior_eq_zero
    {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    (hα : MDifferentiable (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F) p (α p)))
    (hdα : mextDeriv α = 0) (hι : α.interior (fun _ ↦ ((1 : ℝ), (0 : E))) = 0) (t : ℝ) :
    mpullback (𝓘(ℝ, ℝ).prod I) I Prod.snd (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) = α :=
  (eq_mpullback_snd_of_interior_eq_zero hι fun s ↦
    mpullback_prodMk_eq_of_interior_eq_zero hα hdα hι s t).symm

/-! ### Forms on the product with a circle -/

namespace SmoothForm

variable {p : ℝ} [Fact (0 < p)]

/-- On `AddCircle p × M`, a smooth closed form `α` whose contraction with `∂ₛ = (1, 0)` vanishes is
the pullback along the second projection of its restriction to any slice `{θ} × M`:
`α = pr₂^* (ι_θ^* α)`. -/
theorem mpullback_snd_mpullback_prodMk_of_interior_eq_zero
    {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × M) F (k + 1)} (hα : α.IsClosed)
    (hι : RoughForm.interior (I := 𝓘(ℝ).prod I) (M := AddCircle p × M) (F := F)
      (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0) (θ : AddCircle p) :
    mpullback Prod.snd contMDiff_snd
      (mpullback (Prod.mk θ) (contMDiff_const.prodMk contMDiff_id) α) = α := by
  let V : (q : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) q := fun _ ↦ ((1 : ℝ), (0 : E))
  let W : (q : AddCircle p × M) → TangentSpace (𝓘(ℝ).prod I) q := fun _ ↦ ((1 : ℝ), (0 : E))
  let cover := Prod.map ((↑) : ℝ → AddCircle p) (id : M → M)
  have hcover : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ).prod I) ∞ cover :=
    (AddCircle.contMDiff_coe p ∞).prodMap contMDiff_id
  -- The covering has derivative the identity, so it relates `∂ₛ` on `ℝ × M` to `∂ₛ`.
  have hdcover (q : ℝ × M) :
      mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ).prod I) cover q (V q) = W (cover q) := by
    rw [mfderiv_prodMap (AddCircle.hasMFDerivAt_coe p q.1).mdifferentiableAt
      mdifferentiableAt_id, AddCircle.mfderiv_coe, mfderiv_id]
    -- Both components of `(1, 0)` are fixed by the identity maps.
    rfl
  -- The lift `cover^* α` to `ℝ × M` is closed with vanishing contraction, so its slices agree.
  have hι' : RoughForm.interior (F := F) V (mpullback cover hcover α).1 = 0 := by
    rw [coe_mpullback]
    exact (mpullback_interior (F := F) cover V W α.1 hdcover).symm.trans
      ((congrArg _ hι).trans (mpullback_zero _))
  have hslice (t : ℝ) :
      TauCeti.mpullback (F := F) I (𝓘(ℝ).prod I)
          (Prod.mk (t : AddCircle p) : M → AddCircle p × M) α.1 =
        TauCeti.mpullback (F := F) I (𝓘(ℝ, ℝ).prod I) (Prod.mk t : M → ℝ × M)
          (mpullback cover hcover α).1 := by
    rw [coe_mpullback]
    -- `cover ∘ (y ↦ (t, y))` is `y ↦ (↑t, y)`.
    exact TauCeti.mpullback_comp (F := F) (g := cover)
      ((contMDiff_const.prodMk contMDiff_id).mdifferentiable one_ne_zero)
      (hcover.mdifferentiable (by simp)) α.1
  have hconst (g : AddCircle p) :
      TauCeti.mpullback (F := F) I (𝓘(ℝ).prod I) (Prod.mk g : M → AddCircle p × M) α.1 =
        TauCeti.mpullback (F := F) I (𝓘(ℝ).prod I) (Prod.mk θ : M → AddCircle p × M) α.1 := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective g
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [hslice, hslice]
    exact mpullback_prodMk_eq_of_interior_eq_zero (mpullback cover hcover α).mdifferentiable
      ((isClosed_def _).1 (hα.mpullback cover hcover)) hι' s t
  refine Subtype.ext ?_
  rw [coe_mpullback, coe_mpullback]
  exact (eq_mpullback_snd_of_interior_eq_zero hι hconst).symm

/-- A smooth closed form `α` on `AddCircle p × M` is the pullback of a smooth form on `M` along
the second projection exactly when its contraction with `∂ₛ = (1, 0)` vanishes. -/
theorem exists_mpullback_snd_eq_iff_interior_eq_zero
    {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × M) F (k + 1)} (hα : α.IsClosed) :
    (∃ β : SmoothForm I M F (k + 1), mpullback Prod.snd contMDiff_snd β = α) ↔
      RoughForm.interior (I := 𝓘(ℝ).prod I) (M := AddCircle p × M) (F := F)
        (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0 := by
  refine ⟨?_, fun hι ↦ ⟨_, mpullback_snd_mpullback_prodMk_of_interior_eq_zero hα hι 0⟩⟩
  rintro ⟨β, rfl⟩
  -- The second projection kills `∂ₛ`.
  let W : (q : AddCircle p × M) → TangentSpace (𝓘(ℝ).prod I) q := fun _ ↦ ((1 : ℝ), (0 : E))
  rw [coe_mpullback]
  refine (mpullback_interior (F := F) Prod.snd W 0 β.1 fun _ ↦ ?_).symm.trans ?_
  · simp only [mfderiv_snd, W]
    -- The second projection of `(1, 0)` is `0`.
    rfl
  · rw [RoughForm.interior_zero_field, mpullback_zero]

end SmoothForm

end TauCeti
