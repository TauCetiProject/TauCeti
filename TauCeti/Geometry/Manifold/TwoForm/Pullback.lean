/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Kernels of pulled-back smooth two-forms

If the derivative of a smooth map is surjective, the kernel of a pulled-back two-form is the
preimage of the original kernel under that derivative
(`TauCeti.SmoothTwoForm.ker_bilinFormAt_mpullback`). This identity supports the nondegeneracy
criterion for descended symplectic forms. If the derivative is bijective, for instance for a
diffeomorphism, the pullback is nondegenerate at a point exactly when the original form is
nondegenerate at its image (`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_iff`).
-/

public section

open Function
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothTwoForm

variable {E H Z E' H' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {p : Z → Q}

/-- If the derivative of `p` at `z` is surjective, the null space of the pullback `p^* η` at `z`
is the preimage under `dp_z` of the null space of `η` at `p z`. -/
theorem ker_bilinFormAt_mpullback (hp : ContMDiff I J ∞ p) (η : SmoothTwoForm J Q) {z : Z}
    (hdp : Surjective (mfderiv I J p z)) :
    LinearMap.ker ((SmoothForm.mpullback p hp η).bilinFormAt z) =
      (LinearMap.ker (η.bilinFormAt (p z))).comap (mfderiv I J p z).toLinearMap := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
  refine ⟨fun h ↦ LinearMap.ext fun u ↦ ?_, fun h ↦ LinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := hdp u
    have hw := LinearMap.congr_fun h w
    simp only [SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback,
      LinearMap.zero_apply] at hw ⊢
    exact hw
  · have hw := LinearMap.congr_fun h (mfderiv I J p z w)
    simp only [SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback,
      LinearMap.zero_apply] at hw ⊢
    exact hw

/-- If the derivative of `p` at `z` is bijective, the pullback `p^* η` is nondegenerate at `z`
exactly when `η` is nondegenerate at `p z`. -/
theorem nondegenerate_bilinFormAt_mpullback_iff (hp : ContMDiff I J ∞ p) (η : SmoothTwoForm J Q)
    {z : Z} (hdp : Bijective (mfderiv I J p z)) :
    ((SmoothForm.mpullback p hp η).bilinFormAt z).Nondegenerate ↔
      (η.bilinFormAt (p z)).Nondegenerate := by
  rw [LinearMap.BilinForm.Nondegenerate, LinearMap.BilinForm.Nondegenerate,
    (SmoothForm.isAlt_bilinFormAt _ z).isRefl.nondegenerate_iff_separatingLeft,
    (SmoothForm.isAlt_bilinFormAt η _).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.separatingLeft_iff_ker_eq_bot,
    ker_bilinFormAt_mpullback hp η hdp.2,
    ← LinearMap.ker_eq_bot_of_injective hdp.1,
    ← Submodule.comap_bot]
  exact (Submodule.comap_injective_of_surjective hdp.2).eq_iff

end TauCeti.SmoothTwoForm
