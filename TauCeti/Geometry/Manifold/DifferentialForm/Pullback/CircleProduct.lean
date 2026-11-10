/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Eulerian
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.VectorField.AddCircle
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.LinearAlgebra.Alternating.Translate

/-!
# Forms on `S¹ × Y` pulled back from `Y`

Let `Y` be a boundaryless manifold and `X = AddCircle p × Y`, with the unit vector field
`T = ∂ₛ` of the circle factor, the product of `AddCircle.timeVectorField p` with the zero field
of `Y`. The rotations `(s, y) ↦ (s + [t], y)` of the circle factor move every point with velocity
`T`. This file characterizes the forms on `X` that are pullbacks of forms on `Y` along the
projection `pr₂ : X → Y`:

* a differentiable form `α` is invariant under every rotation `(s, y) ↦ (s + c, y)` exactly when
  its Lie derivative `L_T α` vanishes
  (`TauCeti.forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero`), since the
  rotations form an isotopy whose velocity field is `T`;
* if `ι_T α = 0` at a point, the value of `α` there only depends on the `Y`-components of the
  tangent vectors (`TauCeti.RoughForm.apply_eq_apply_of_interior_eq_zero`), since adding
  multiples of `T` to the arguments does not change it;
* hence a smooth form of positive degree is a pullback `pr₂^* β` exactly when `ι_T α = 0` and
  `L_T α = 0` (`TauCeti.SmoothForm.exists_mpullback_snd_eq_iff`), and then `β` is the restriction
  of `α` to any slice `{c} × Y` (`TauCeti.SmoothForm.mpullback_snd_mpullback_prodMk_eq`).

For a closed form, Cartan's formula `L_T α = ι_T dα + d(ι_T α)` makes the second condition a
consequence of the first. So a closed form `α` with `ι_T α = 0` is the pullback of a unique form
`β` on `Y`, and `β` is closed (`TauCeti.SmoothForm.existsUnique_isClosed_mpullback_snd_eq`).

This is how the energy argument for the unperturbed Seiberg–Witten equations on a product
`S¹ × Y` with a product metric concludes: there the integrated Weitzenböck identity forces the
contraction `ι_T F_A` of the curvature with `T` to vanish, and as `F_A` is closed by the Bianchi
identity it is the pullback of a closed two-form on `Y`. That the curvature is pulled back from `Y`
does not mean that the connection itself descends.

## Main results

* `TauCeti.forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero`: a differentiable
  form is invariant under the rotations of the circle factor exactly when `L_T α = 0`.
* `TauCeti.RoughForm.apply_eq_apply_of_interior_eq_zero`: where `ι_T α` vanishes, `α` only
  sees the `Y`-components of tangent vectors.
* `TauCeti.SmoothForm.mpullback_snd_mpullback_prodMk_eq`: if `ι_T α = 0` and `L_T α = 0`, then
  `α` is the pullback along `pr₂` of its restriction to any slice `{c} × Y`.
* `TauCeti.SmoothForm.exists_mpullback_snd_eq_iff`: a smooth form is a pullback along `pr₂`
  exactly when `ι_T α = 0` and `L_T α = 0`.
* `TauCeti.SmoothForm.existsUnique_isClosed_mpullback_snd_eq`: a closed form with `ι_T α = 0` is
  the pullback of a unique closed form on `Y`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 12 (Lie derivatives and invariance under flows) and
  Theorem 14.35 (Cartan's magic formula).
-/

public section

noncomputable section

open Function Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H Y F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {p : ℝ} [Fact (0 < p)]

/-! ### Horizontality -/

/-- The unit field `∂ₛ` of the circle factor is `(1, 0)` in every tangent space. -/
private theorem prodVectorField_timeVectorField_apply (x : AddCircle p × Y) :
    Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y) x =
      ((1 : ℝ), (0 : E)) :=
  Prod.ext ((Manifold.prodVectorField_fst _ _ x).trans (AddCircle.timeVectorField_apply p x.1))
    (Manifold.prodVectorField_snd _ _ x)

/-- **Horizontality.** If the contraction of a form `α` on `AddCircle p × Y` with the unit field
`∂ₛ` of the circle factor vanishes at `x`, then the value of `α` at `x` only depends on the images
of the tangent vectors under the derivative of the projection to `Y`. -/
theorem RoughForm.apply_eq_apply_of_interior_eq_zero
    {α : RoughForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)} {x : AddCircle p × Y}
    (hα : RoughForm.interior
      (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
      α x = 0)
    {v w : Fin (k + 1) → TangentSpace (𝓘(ℝ).prod I) x}
    (hvw : ∀ i, mfderiv (𝓘(ℝ).prod I) I Prod.snd x (v i) =
      mfderiv (𝓘(ℝ).prod I) I Prod.snd x (w i)) :
    α x v = α x w := by
  set T := Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y)
  have hT : (α x).toAlternatingMap.curryLeft (T x) = 0 := by
    ext u
    have h := RoughForm.interior_apply T α x u
    rw [hα] at h
    simpa [AlternatingMap.curryLeft_apply_apply] using h.symm
  -- The vectors differ by multiples of `T x = (1, 0)`, since their second components agree.
  have key (a b t : ℝ × E) (h : a.2 = b.2) (ht₁ : t.1 = 1) (ht₂ : t.2 = 0) :
      b = a + (b.1 - a.1) • t :=
    Prod.ext (by simp [ht₁]) (by simp [h, ht₂])
  have hTx : T x = ((1 : ℝ), (0 : E)) := prodVectorField_timeVectorField_apply x
  have hw : w = fun i ↦ v i + ((w i).1 - (v i).1) • T x := by
    funext i
    have h := hvw i
    rw [mfderiv_snd_apply, mfderiv_snd_apply] at h
    exact key (v i) (w i) (T x) h (by rw [hTx]) (by rw [hTx])
  rw [hw]
  exact (AlternatingMap.map_add_smul_of_curryLeft_eq_zero hT _ _).symm

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

/-- The Eulerian velocity field of the rotations is the unit field `∂ₛ` of the circle factor. -/
private theorem eulerianField_rotation (t : ℝ) :
    eulerianField (𝓘(ℝ).prod I) (rotation Y p) t =
      Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y) := by
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
  exact hc.trans (prodVectorField_timeVectorField_apply _).symm

/-- The rotations of the circle factor are the identity on tangent vectors. -/
private theorem mfderiv_prodMap_add_right (c : AddCircle p) (x : AddCircle p × Y)
    (w : TangentSpace (𝓘(ℝ).prod I) x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + c) id) x w = w := by
  rw [((mdifferentiableAt_add_right (I := 𝓘(ℝ)) (a := c) (b := x.1)).hasMFDerivAt.prodMap
    (hasMFDerivAt_id (I := I) x.2)).mfderiv, AddCircle.mfderiv_add_right, mfderiv_id]
  -- `(id ×ₗ id) w = (w.1, w.2)`, which is `w` by the eta rule for pairs.
  rfl

/-- A rotation-invariant form takes the same values on the same tangent vectors at all points of
a circle `AddCircle p × {y}`. -/
private theorem apply_eq_apply_of_forall_mpullback_eq
    {α : RoughForm (𝓘(ℝ).prod I) (AddCircle p × Y) F k}
    (hα : ∀ c : AddCircle p,
      mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + c) id) α = α)
    (s c : AddCircle p) (y : Y) (v : Fin k → TangentSpace (𝓘(ℝ).prod I) (s, y)) :
    α (c, y) v = α (s, y) v := by
  have h := congrFun (hα (c - s)) (s, y)
  rw [← h, mpullback_apply]
  -- The rotation by `c - s` moves `(s, y)` to `(c, y)` and is the identity on tangent vectors.
  have hpt : Prod.map (· + (c - s)) id (s, y) = (c, y) := by
    refine Prod.ext ?_ ?_ <;> simp
  simp only [mfderiv_prodMap_add_right]
  rw [hpt]

section Rotation

variable [I.Boundaryless] [IsManifold I 2 Y]

/-- **Rotation invariance.** A differentiable form on `AddCircle p × Y` is invariant under every
rotation `(s, y) ↦ (s + c, y)` of the circle factor exactly when its Lie derivative along the unit
field `∂ₛ` of the circle factor vanishes. -/
theorem forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero
    {α : RoughForm (𝓘(ℝ).prod I) (AddCircle p × Y) F k}
    (hα : MDifferentiable (𝓘(ℝ).prod I) ((𝓘(ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) z (α z))) :
    (∀ c : AddCircle p,
      mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + c) id) α = α) ↔
      mlieDerivForm
        (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
        α = 0 := by
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
vanishing Lie derivative along the unit field `∂ₛ` of the circle factor, then `α` is the pullback
along the projection to `Y` of its restriction to any slice `{c} × Y`. -/
theorem mpullback_snd_mpullback_prodMk_eq
    {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)}
    (hι : RoughForm.interior (F := F) (k := k)
      (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
      α.1 = 0)
    (hL : mlieDerivForm
      (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
      α.1 = 0)
    (c : AddCircle p) :
    mpullback Prod.snd contMDiff_snd
        (mpullback (fun y : Y ↦ (c, y)) (contMDiff_const.prodMk contMDiff_id) α) = α := by
  have hinv := (forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero
    α.mdifferentiable).2 hL
  apply Subtype.ext
  funext x
  ext v
  obtain ⟨s, y⟩ := x
  rw [coe_mpullback, TauCeti.mpullback_apply, coe_mpullback, TauCeti.mpullback_apply]
  refine (apply_eq_apply_of_forall_mpullback_eq hinv s c y _).trans ?_
  refine RoughForm.apply_eq_apply_of_interior_eq_zero (congrFun hι (s, y)) fun i ↦ ?_
  simp only [mfderiv_snd, mfderiv_prod_right]
  -- Both sides are the second component of `v i`.
  rfl

/-- **Pullbacks from `Y`.** A smooth form of positive degree on `AddCircle p × Y` is the pullback
of a smooth form on `Y` along the projection exactly when its contraction with and its Lie
derivative along the unit field `∂ₛ` of the circle factor vanish. -/
theorem exists_mpullback_snd_eq_iff {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)} :
    (∃ β : SmoothForm I Y F (k + 1), mpullback Prod.snd contMDiff_snd β = α) ↔
      RoughForm.interior (F := F) (k := k)
          (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
          α.1 = 0 ∧
        mlieDerivForm
          (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
          α.1 = 0 := by
  refine ⟨?_, fun ⟨hι, hL⟩ ↦ ⟨_, mpullback_snd_mpullback_prodMk_eq hι hL 0⟩⟩
  rintro ⟨β, rfl⟩
  refine ⟨?_, ?_⟩
  · -- The projection kills `∂ₛ`, so the contraction has a zero argument.
    funext x
    ext u
    rw [RoughForm.interior_apply, coe_mpullback, TauCeti.mpullback_apply]
    refine (β.1 x.2).map_coord_zero 0 ?_
    rw [Matrix.cons_val_zero, mfderiv_snd_apply, prodVectorField_timeVectorField_apply]
    -- The second component of `(1, 0)` is `0`; the two zeros differ only in the name of their
    -- type, `E` or the tangent space of `Y`.
    rfl
  · -- Pullbacks along the projection are invariant under the rotations of the circle factor.
    refine (forall_mpullback_prodMap_add_right_eq_iff_mlieDerivForm_eq_zero
      (mpullback Prod.snd contMDiff_snd β).mdifferentiable).1 fun c ↦ ?_
    rw [coe_mpullback, ← TauCeti.mpullback_comp
      (mdifferentiable_add_right.prodMap mdifferentiable_id)
      mdifferentiable_snd]
    -- `Prod.snd ∘ Prod.map (· + c) id` is `Prod.snd` by definition.
    rfl

/-- **Closed forms with vanishing contraction are pulled back from `Y`.** A closed smooth form
`α` of positive degree on `AddCircle p × Y` whose contraction with the unit field `∂ₛ` of the
circle factor vanishes is the pullback along the projection of a unique smooth form `β` on `Y`,
and `β` is closed. -/
theorem existsUnique_isClosed_mpullback_snd_eq
    {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)} (hα : α.IsClosed)
    (hι : RoughForm.interior (F := F) (k := k)
      (Manifold.prodVectorField (AddCircle.timeVectorField p) (0 : Π y : Y, TangentSpace I y))
      α.1 = 0) :
    ∃! β : SmoothForm I Y F (k + 1), β.IsClosed ∧ mpullback Prod.snd contMDiff_snd β = α := by
  have hT : MDifferentiable (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent
      (T% (Manifold.prodVectorField (AddCircle.timeVectorField p)
        (0 : Π y : Y, TangentSpace I y))) :=
    (Manifold.contMDiff_prodVectorField (n := 1) (AddCircle.contMDiff_timeVectorField p)
      (contMDiff_zeroSection ℝ (TangentSpace I))).mdifferentiable one_ne_zero
  -- Cartan's formula: `L_T α = d (ι_T α) = 0`.
  have hL := mlieDerivForm_eq_mextDeriv_interior hT hα
  rw [hι, mextDeriv_zero] at hL
  have hs : ContMDiff I (𝓘(ℝ).prod I) ∞ fun y : Y ↦ ((0 : AddCircle p), y) :=
    contMDiff_const.prodMk contMDiff_id
  refine ⟨mpullback _ hs α, ⟨hα.mpullback _ hs, mpullback_snd_mpullback_prodMk_eq hι hL 0⟩,
    fun β ⟨_, hβ⟩ ↦ mpullback_injective_of_rightInverse contMDiff_snd hs (fun _ ↦ rfl) ?_⟩
  rw [hβ, mpullback_snd_mpullback_prodMk_eq hι hL 0]

end SmoothForm

end TauCeti
