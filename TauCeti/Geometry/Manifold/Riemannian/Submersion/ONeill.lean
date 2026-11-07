/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# O'Neill tensors of a Riemannian submersion

The fundamental tensors `oneillA` and `oneillT` are continuous bilinear maps on each
source tangent space. With `h` and `v` denoting the orthogonal horizontal and vertical
projections for the given metric, their defining field formulas are

* `A_X Y = v ∇_(hX)(hY) + h ∇_(hX)(vY)`;
* `T_X Y = v ∇_(vX)(hY) + h ∇_(vX)(vY)`.

The construction uses the induced endomorphism connection: both tensors are obtained
from `(v - h) ∇h`, by restricting the direction to the horizontal or vertical space.
Thus dependence on the two tangent vectors, rather than their field extensions, is
built into the construction. Both tensors are smooth for smooth metrics. These are
the tensors entering the connection and curvature equations of a submersion; no
integrability or curvature identities are asserted here.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

local notation "∇" => CovariantDerivative.leviCivitaConnection I M
local notation "hp" => (fun x : M ↦ Submodule.starProjection
  (Submodule.orthogonal (LinearMap.ker (ContinuousLinearMap.toLinearMap (mfderiv I J f x)))))
local notation "vp" => (fun x : M ↦ Submodule.starProjection
  (LinearMap.ker (ContinuousLinearMap.toLinearMap (mfderiv I J f x))))

section Basic

variable [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- O'Neill's horizontal-direction tensor, as a continuous bilinear map. -/
def oneillA (h : IsRiemannianSubmersion I J f) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.compL ℝ _ _ _ (vp x - hp x)).comp
    ((∇.hom ∇ hp x).comp
      ((h.horizontalLift x).toContinuousLinearMap.comp (mfderiv I J f x)))

/-- O'Neill's vertical-direction tensor, as a continuous bilinear map. -/
def oneillT (h : IsRiemannianSubmersion I J f) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.compL ℝ _ _ _ (vp x - hp x)).comp
    ((∇.hom ∇ hp x).comp
      (ContinuousLinearMap.id ℝ _ -
        (h.horizontalLift x).toContinuousLinearMap.comp (mfderiv I J f x)))

/-- Evaluation of the horizontal tensor using the covariant derivative of horizontal projection. -/
theorem oneillA_apply (x : M) (u w : TangentSpace I x) :
    h.oneillA x u w = (vp x - hp x) (∇.hom ∇ hp x (hp x u) w) := by
  simp only [oneillA, h.horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

/-- Evaluation of the vertical tensor using the covariant derivative of horizontal projection. -/
theorem oneillT_apply (x : M) (u w : TangentSpace I x) :
    h.oneillT x u w = (vp x - hp x) (∇.hom ∇ hp x (vp x u) w) := by
  simp only [oneillT, h.id_sub_horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

variable [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

include h in
/-- Remove the derivative-of-field term in the projected endomorphism derivative. -/
private theorem projected_hom_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    (vp x - hp x) (∇.hom ∇ hp x u (Y x)) =
      vp x (∇ (fun y ↦ hp y (Y y)) x u) +
        hp x (∇ (fun y ↦ vp y (Y y)) x u) := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hh := (h.contMDiff_starProjection_orthogonal_ker (n := 1) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hhY := hh.clm_bundle_apply hY
  have heq : (fun y ↦ vp y (Y y)) = Y - fun y ↦ hp y (Y y) := by
    ext y
    simp
  rw [CovariantDerivative.hom_apply ∇ ∇ hh hY, heq,
    ∇.isCovariantDerivativeOnUniv.sub hY hhY]
  simp [Submodule.starProjection_orthogonal, Submodule.starProjection_apply, map_sub,
    -Submodule.coe_orthogonalProjectionOnto_apply]
  abel

/-- The defining covariant-derivative formula for O'Neill's `A` tensor.
Only differentiability of the second field at the point is needed. -/
theorem oneillA_eq {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillA x u (Y x) =
      vp x (∇ (fun y ↦ hp y (Y y)) x (hp x u)) +
        hp x (∇ (fun y ↦ vp y (Y y)) x (hp x u)) := by
  rw [h.oneillA_apply, h.projected_hom_apply hY]

/-- The defining covariant-derivative formula for O'Neill's `T` tensor.
Only differentiability of the second field at the point is needed. -/
theorem oneillT_eq {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillT x u (Y x) =
      vp x (∇ (fun y ↦ hp y (Y y)) x (vp x u)) +
        hp x (∇ (fun y ↦ vp y (Y y)) x (vp x u)) := by
  rw [h.oneillT_apply, h.projected_hom_apply hY]

omit [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- `A` vanishes on vertical directions. -/
@[simp] theorem oneillA_eq_zero_of_mem_ker (x : M) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).ker) (w : TangentSpace I x) :
    h.oneillA x u w = 0 := by
  simp [oneillA_apply, Submodule.starProjection_orthogonal_apply_eq_zero hu]

omit [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- `T` vanishes on horizontal directions. -/
@[simp] theorem oneillT_eq_zero_of_mem_orthogonal_ker (x : M) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (w : TangentSpace I x) :
    h.oneillT x u w = 0 := by
  have hz : vp x u = 0 := (Submodule.starProjection_apply_eq_zero_iff _).mpr hu
  simp [oneillT_apply, hz]

end Basic

section Smooth

variable [T2Space M] [IsManifold I ∞ M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

include h in
/-- Smoothness of the common unprojected expression used by both fundamental tensors. -/
private theorem contMDiff_projected_hom_apply
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiff I (I.tangent) ∞ (T% X))
    (hY : ContMDiff I (I.tangent) ∞ (T% Y)) :
    ContMDiff I (I.tangent) ∞
      (T% (fun x ↦ (vp x - hp x) (∇.hom ∇ hp x (X x) (Y x)))) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hh := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hv := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hD := (CovariantDerivative.contMDiff_hom ∇ ∇ hh).clm_bundle_apply hX
  have hDY := hD.clm_bundle_apply hY
  exact (hv.clm_bundle_apply hDY).sub_section (hh.clm_bundle_apply hDY)

/-- O'Neill's `A` tensor is a smooth section of the bilinear tangent bundle. -/
theorem contMDiff_oneillA :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillA x)) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  have hhX := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).clm_bundle_apply hX
  exact (h.contMDiff_projected_hom_apply hhX hY).congr fun x ↦
    congrArg (TotalSpace.mk' E x) (h.oneillA_apply x (X x) (Y x))

/-- O'Neill's `T` tensor is a smooth section of the bilinear tangent bundle. -/
theorem contMDiff_oneillT :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillT x)) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  have hvX := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hX
  exact (h.contMDiff_projected_hom_apply hvX hY).congr fun x ↦
    congrArg (TotalSpace.mk' E x) (h.oneillT_apply x (X x) (Y x))

end Smooth

end TauCeti.IsRiemannianSubmersion
