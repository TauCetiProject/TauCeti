/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Eulerian
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Product

/-!
# Forms on `S¹ × Y` pulled back from `Y`

Let `Y` be a boundaryless manifold and `X = AddCircle p × Y`, with the unit vector field
`∂ₛ = (1, 0)` of the circle factor. The rotations `(s, y) ↦ (s + [t], y)` of the circle factor
move every point with velocity `∂ₛ`. `TauCeti/Geometry/Manifold/DifferentialForm/Pullback/Product`
shows that a closed form `α` on `X` with `ι_{∂ₛ} α = 0` is pulled back from `Y`. This file treats
forms that need not be closed, and records what the descended form of a closed form is:

* a differentiable form `α` is invariant under every rotation `(s, y) ↦ (s + c, y)` exactly when
  its Lie derivative `L_{∂ₛ} α` vanishes
  (`TauCeti.forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero`), since the
  rotations form an isotopy whose velocity field is `∂ₛ`;
* hence a smooth form of positive degree is a pullback `pr₂^* β` exactly when `ι_{∂ₛ} α = 0` and
  `L_{∂ₛ} α = 0` (`TauCeti.SmoothForm.exists_mpullback_snd_eq_iff`), and then `β` is the
  restriction of `α` to any slice `{c} × Y`
  (`TauCeti.SmoothForm.mpullback_snd_mpullback_prodMk_of_mlieDerivForm_eq_zero`);
* a closed form `α` with `ι_{∂ₛ} α = 0` is the pullback of a unique form `β` on `Y`, and `β` is
  closed (`TauCeti.SmoothForm.existsUnique_isClosed_mpullback_snd_eq`).

In the energy argument for the unperturbed Seiberg–Witten equations on a product `S¹ × Y` with a
product metric, the closedness of the descended form is what makes the curvature `i F_A`, once
`ι_{∂ₛ} F_A = 0`, define a de Rham class on `Y` whose pullback is the real first Chern class of
the determinant line.

## Main results

* `TauCeti.forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero`: a differentiable
  form is invariant under the rotations of the circle factor exactly when `L_{∂ₛ} α = 0`.
* `TauCeti.SmoothForm.mpullback_snd_mpullback_prodMk_of_mlieDerivForm_eq_zero`: if
  `ι_{∂ₛ} α = 0` and `L_{∂ₛ} α = 0`, then `α` is the pullback along `pr₂` of its restriction to
  any slice `{c} × Y`.
* `TauCeti.SmoothForm.exists_mpullback_snd_eq_iff`: a smooth form is a pullback along `pr₂`
  exactly when `ι_{∂ₛ} α = 0` and `L_{∂ₛ} α = 0`.
* `TauCeti.SmoothForm.existsUnique_isClosed_mpullback_snd_eq`: a closed form with
  `ι_{∂ₛ} α = 0` is the pullback of a unique closed form on `Y`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 12 (Lie derivatives and invariance under flows).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H Y F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {p : ℝ} [Fact (0 < p)]

/-! ### Invariance under the rotations of the circle factor -/

variable (Y p) in
/-- The rotation of the circle factor of `AddCircle p × Y` by `[u]`, as an equivalence. -/
private def rotation (u : ℝ) : AddCircle p × Y ≃ AddCircle p × Y :=
  (Equiv.addRight (u : AddCircle p)).prodCongr (Equiv.refl Y)

omit [TopologicalSpace Y] [Fact (0 < p)] in
private theorem rotation_apply (u : ℝ) (x : AddCircle p × Y) :
    rotation Y p u x = (x.1 + (u : AddCircle p), x.2) :=
  (rfl)

omit [TopologicalSpace Y] [Fact (0 < p)] in
private theorem rotation_symm_apply (u : ℝ) (x : AddCircle p × Y) :
    (rotation Y p u).symm x = (x.1 + ((-u : ℝ) : AddCircle p), x.2) := by
  rw [AddCircle.coe_neg, ← sub_eq_add_neg]
  -- The inverse of `Equiv.addRight a` is `x ↦ x - a` by definition.
  rfl

/-- The rotations of the circle factor depend smoothly on the angle and the point. -/
private theorem contMDiff_rotation :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod I) 2
      (fun q : ℝ × (AddCircle p × Y) ↦ rotation Y p q.1 q.2) := by
  simp only [rotation_apply]
  exact ((contMDiff_snd.fst).add ((AddCircle.contMDiff_coe p 2).comp contMDiff_fst)).prodMk
    contMDiff_snd.snd

private theorem contMDiff_rotation_symm :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod I) 2
      (fun q : ℝ × (AddCircle p × Y) ↦ (rotation Y p q.1).symm q.2) := by
  simp only [rotation_symm_apply]
  exact ((contMDiff_snd.fst).add
    ((AddCircle.contMDiff_coe p 2).comp (contMDiff_fst.neg))).prodMk contMDiff_snd.snd

/-- The Eulerian velocity field of the rotations is the unit field `∂ₛ = (1, 0)` of the circle
factor. -/
private theorem eulerianField_rotation (t : ℝ) :
    eulerianField (𝓘(ℝ).prod I) (rotation Y p) t = fun _ ↦ ((1 : ℝ), (0 : E)) := by
  funext y
  obtain ⟨x, rfl⟩ := (rotation Y p t).surjective y
  rw [eulerianField_apply_apply, Manifold.curveVelocity_apply]
  -- The curve `u ↦ (x.1 + [u], x.2)` has velocity `(1, 0)`.
  have h : HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod I) (fun u ↦ rotation Y p u x) t
      (((1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℝ)).prod 0) :=
    (AddCircle.hasMFDerivAt_add_coe_comp (hasDerivAt_id t) x.1).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := I) x.2 t)
  have hc : ((((1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℝ)).prod (0 : ℝ →L[ℝ] E)) 1 : ℝ × E) =
      ((1 : ℝ), (0 : E)) := by
    simp
  rw [h.mfderiv]
  exact hc

/-- A rotation-invariant form has the same restriction to every slice `{s} × Y`. -/
private theorem mpullback_prodMk_eq_of_forall_mpullback_eq
    {α : RoughForm (𝓘(ℝ).prod I) (AddCircle p × Y) F k}
    (hα : ∀ c : AddCircle p,
      mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + c) id) α = α)
    (s c : AddCircle p) :
    mpullback I (𝓘(ℝ).prod I) (Prod.mk s) α = mpullback I (𝓘(ℝ).prod I) (Prod.mk c) α := by
  -- The slice at `s` is the slice at `c` followed by the rotation by `s - c`.
  have h : (Prod.mk s : Y → AddCircle p × Y) = Prod.map (· + (s - c)) id ∘ Prod.mk c := by
    funext y
    simp
  rw [h, mpullback_comp (f := Prod.mk c) (g := Prod.map (· + (s - c)) id)
    (mdifferentiable_const.prodMk mdifferentiable_id)
    (mdifferentiable_add_right.prodMap mdifferentiable_id), hα]

section Rotation

variable [I.Boundaryless] [IsManifold I 2 Y]

/-- **Rotation invariance.** A differentiable form on `AddCircle p × Y` is invariant under every
rotation `(s, y) ↦ (s + c, y)` of the circle factor exactly when its Lie derivative along the unit
field `∂ₛ = (1, 0)` of the circle factor vanishes. -/
theorem forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero
    {α : RoughForm (𝓘(ℝ).prod I) (AddCircle p × Y) F k}
    (hα : MDifferentiable (𝓘(ℝ).prod I) ((𝓘(ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) z (α z))) :
    (∀ c : AddCircle p,
      mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + c) id) α = α) ↔
      mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α = 0 := by
  have h := forall_mpullback_eq_iff_forall_mlieDerivForm_eulerianField_eq_zero
    (contMDiff_rotation (p := p) (Y := Y) (I := I)) contMDiff_rotation_symm hα
  simp only [eulerianField_rotation, forall_const] at h
  rw [← h]
  -- The rotation by `[u]` is `Prod.map (· + [u]) id`, and the rotation by `[0]` is the identity.
  have hrot (u : ℝ) : (rotation Y p u : AddCircle p × Y → AddCircle p × Y) =
      Prod.map (· + (u : AddCircle p)) id :=
    (rfl)
  have h0 : (Prod.map (· + ((0 : ℝ) : AddCircle p)) id : AddCircle p × Y → AddCircle p × Y) =
      id := by
    funext x
    refine Prod.ext ?_ ?_ <;> simp
  simp only [hrot]
  refine ⟨fun hc s t ↦ by rw [hc, hc], fun hst c ↦ ?_⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [hst u 0, h0, mpullback_id]

end Rotation

/-! ### Descent along the projection to `Y` -/

namespace SmoothForm

variable [I.Boundaryless] [IsManifold I ∞ Y]

/-- **Descent.** If a smooth form `α` on `AddCircle p × Y` has vanishing contraction with and
vanishing Lie derivative along the unit field `∂ₛ = (1, 0)` of the circle factor, then `α` is the
pullback along the projection to `Y` of its restriction to any slice `{c} × Y`. -/
theorem mpullback_snd_mpullback_prodMk_of_mlieDerivForm_eq_zero
    {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)}
    (hL : mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0)
    (hι : RoughForm.interior (I := 𝓘(ℝ).prod I) (M := AddCircle p × Y) (F := F)
      (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0)
    (c : AddCircle p) :
    mpullback Prod.snd contMDiff_snd
      (mpullback (Prod.mk c) (contMDiff_const.prodMk contMDiff_id) α) = α := by
  have hinv := (forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero
    α.mdifferentiable).2 hL
  refine Subtype.ext ?_
  rw [coe_mpullback, coe_mpullback]
  exact (eq_mpullback_snd_of_interior_eq_zero hι fun s ↦
    mpullback_prodMk_eq_of_forall_mpullback_eq hinv s c).symm

/-- **Pullbacks from `Y`.** A smooth form of positive degree on `AddCircle p × Y` is the pullback
of a smooth form on `Y` along the projection exactly when its contraction with and its Lie
derivative along the unit field `∂ₛ = (1, 0)` of the circle factor vanish. -/
theorem exists_mpullback_snd_eq_iff {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)} :
    (∃ β : SmoothForm I Y F (k + 1), mpullback Prod.snd contMDiff_snd β = α) ↔
      RoughForm.interior (I := 𝓘(ℝ).prod I) (M := AddCircle p × Y) (F := F)
          (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0 ∧
        mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0 := by
  refine ⟨?_, fun ⟨hι, hL⟩ ↦
    ⟨_, mpullback_snd_mpullback_prodMk_of_mlieDerivForm_eq_zero hL hι 0⟩⟩
  rintro ⟨β, rfl⟩
  refine ⟨?_, ?_⟩
  · -- The second projection kills `∂ₛ`.
    let W : (q : AddCircle p × Y) → TangentSpace (𝓘(ℝ).prod I) q := fun _ ↦ ((1 : ℝ), (0 : E))
    rw [coe_mpullback]
    refine (mpullback_interior (F := F) Prod.snd W 0 β.1 fun _ ↦ ?_).symm.trans ?_
    · simp only [mfderiv_snd, W]
      -- The second projection of `(1, 0)` is `0`.
      rfl
    · rw [RoughForm.interior_zero_field, mpullback_zero]
  · -- Pullbacks along the projection are invariant under the rotations of the circle factor.
    refine (forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero
      (mpullback Prod.snd contMDiff_snd β).mdifferentiable).1 fun c ↦ ?_
    rw [coe_mpullback, ← TauCeti.mpullback_comp
      (mdifferentiable_add_right.prodMap mdifferentiable_id)
      mdifferentiable_snd]
    -- `Prod.snd ∘ Prod.map (· + c) id` is `Prod.snd` by definition.
    rfl

/-- **Closed forms with vanishing contraction are pulled back from `Y`.** A closed smooth form
`α` of positive degree on `AddCircle p × Y` whose contraction with the unit field `∂ₛ = (1, 0)` of
the circle factor vanishes is the pullback along the projection of a unique smooth form `β` on
`Y`, and `β` is closed. -/
theorem existsUnique_isClosed_mpullback_snd_eq
    {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)} (hα : α.IsClosed)
    (hι : RoughForm.interior (I := 𝓘(ℝ).prod I) (M := AddCircle p × Y) (F := F)
      (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 = 0) :
    ∃! β : SmoothForm I Y F (k + 1), β.IsClosed ∧ mpullback Prod.snd contMDiff_snd β = α := by
  have hs : ContMDiff I (𝓘(ℝ).prod I) ∞ (Prod.mk (0 : AddCircle p) : Y → AddCircle p × Y) :=
    contMDiff_const.prodMk contMDiff_id
  have hpull := mpullback_snd_mpullback_prodMk_of_interior_eq_zero hα hι 0
  refine ⟨mpullback _ hs α, ⟨hα.mpullback _ hs, hpull⟩,
    fun β ⟨_, hβ⟩ ↦ mpullback_injective_of_rightInverse contMDiff_snd hs (fun _ ↦ rfl) ?_⟩
  rw [hβ, hpull]

end SmoothForm

end TauCeti
