/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Forms read through a partial diffeomorphism into a normed space

Let `Φ` be a smooth partial diffeomorphism from a manifold `M` to a normed space `V`. A form `φ` on
`M` is read in the coordinates `Φ` as its pullback `(Φ⁻¹)^* φ` along the inverse, a flat form on the
open set `Φ.target`. This file records the three facts needed to work with this flat form:

* evaluated at `Φ y` on the images under `dΦ_y` of tangent vectors at `y`, it is `φ` on them
  (`PartialDiffeomorph.mpullbackWithin_symm_apply_mvfderiv`);
* it is smooth on `Φ.target` when `φ` is smooth
  (`PartialDiffeomorph.contDiffOn_mpullbackWithin_symm`);
* it is closed on `Φ.target` when `φ` is closed
  (`PartialDiffeomorph.extDeriv_mpullbackWithin_symm_eq_zero`).
-/

public section

open Set TauCeti
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E H M V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Read through a partial diffeomorphism `Φ` into a normed space, the pullback of a form `φ` along
`Φ⁻¹` is `φ`: evaluated at `Φ y` on the images under `dΦ_y` of tangent vectors at `y`, it is `φ` on
them. -/
theorem mpullbackWithin_symm_apply_mvfderiv {n : WithTop ℕ∞}
    (Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V n) (hn : n ≠ 0) (φ : RoughForm I M F k) {y : M}
    (hy : y ∈ Φ.source) (v : Fin k → TangentSpace I y) :
    mpullbackWithin 𝓘(ℝ, V) I Φ.symm Φ.target φ (Φ y) (fun i ↦ mvfderiv I Φ y (v i)) =
      φ y v := by
  -- The base point `Φ⁻¹ (Φ y)` of the pulled back form is `y`.
  have key : ∀ z, z = y → ∀ w : Fin k → E, φ z w = φ y w := by
    rintro z rfl w
    rfl
  refine (mpullbackWithin_apply (I := 𝓘(ℝ, V)) _ _ _ (Φ y) _).trans ?_
  rw [mfderivWithin_of_isOpen Φ.open_target (Φ.map_source hy)]
  refine (key _ (Φ.left_inv hy) _).trans (congrArg (φ y) (funext fun i ↦ ?_))
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact Φ.mfderiv_symm_apply_mfderiv_apply hn hy (v i)

variable [IsManifold I 1 M]

/-- Read through a smooth partial diffeomorphism `Φ` into a normed space, a smooth form is smooth:
its pullback along `Φ⁻¹` is smooth on `Φ.target`. -/
theorem contDiffOn_mpullbackWithin_symm (Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V ∞)
    (φ : SmoothForm I M F k) :
    ContDiffOn ℝ (E := V) (F := V [⋀^Fin k]→L[ℝ] F) ∞
      (mpullbackWithin 𝓘(ℝ, V) I Φ.symm Φ.target φ.val) Φ.target := fun p hp ↦
  RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
    (ContMDiffOn.mpullbackWithin_form (φ.contMDiff.contMDiffOn (s := univ))
      Φ.contMDiffOn_invFun (by simp) (mapsTo_univ _ _) Φ.open_target.uniqueMDiffOn p hp)

/-- Read through a smooth partial diffeomorphism `Φ` into a normed space, a closed form is closed:
the exterior derivative of its pullback along `Φ⁻¹` vanishes on `Φ.target`. -/
theorem extDeriv_mpullbackWithin_symm_eq_zero [IsManifold I 2 M]
    (Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V ∞)
    {φ : SmoothForm I M F k} (hφ : φ.IsClosed) {p : V} (hp : p ∈ Φ.target) :
    extDeriv (mpullbackWithin 𝓘(ℝ, V) I Φ.symm Φ.target φ.val) p = 0 := by
  refine (extDerivWithin_of_isOpen Φ.open_target hp).symm.trans
    ((extDerivWithin_mpullbackWithin ((Φ.contMDiffOn_invFun p hp).of_le (by simp))
      Φ.open_target.uniqueDiffOn (subset_closure (by rwa [Φ.open_target.interior_eq])) hp
      ((φ.contMDiff _).mdifferentiableAt (by simp))).trans ?_)
  rw [(SmoothForm.isClosed_def φ).1 hφ, mpullbackWithin_zero, Pi.zero_apply]
  -- The two zeros are alternating maps on `TangentSpace 𝓘(ℝ, V) p` and on `V`, which Mathlib
  -- identifies definitionally.
  rfl

end PartialDiffeomorph
