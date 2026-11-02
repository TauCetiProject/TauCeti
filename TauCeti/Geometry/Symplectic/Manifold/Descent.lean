/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Descending symplectic forms along submersions

Let `p : Z → Q` be a surjective smooth submersion and `σ` a two-form on `Z`. If `σ = p^* η`, then
at every point `z` the null space `ker σ_z = {v | σ_z(v, ·) = 0}` is the preimage under `dp_z` of
the null space of `η` at `p z` (`TauCeti.SmoothTwoForm.ker_bilinFormAt_mpullback`), because `dp_z`
is surjective. Hence `η` is nondegenerate exactly when the null space of `σ` is the kernel of `dp`
at every point (`TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_mpullback`), and
`η` is symplectic exactly when moreover `σ` is closed
(`TauCeti.SmoothTwoForm.isSymplectic_iff_of_mpullback_eq`).

Combined with the descent of basic forms along submersions
(`TauCeti.SmoothForm.descendBasic`), this gives the **descent of symplectic forms**: if `σ` is a
closed basic two-form whose null space at every point is exactly `ker dp`, there is a unique
two-form `η` on `Q` with `p^* η = σ`, and it is symplectic
(`TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`). Here basic means that the
values of `σ` at two points of a fibre agree on pairs of tangent vectors with the same images
under `dp` (`TauCeti.RoughForm.IsBasic`).

This is the last step of symplectic reduction: for a moment map `μ` with regular value `c`, the
restriction of the symplectic form to the level `μ⁻¹(c)` is closed, it is basic for the quotient
map onto the reduced space `μ⁻¹(c) / G_c`, and its null space is the tangent space to the
`G_c`-orbits, which is the kernel of the derivative of the quotient map.

## Main results

* `TauCeti.SmoothTwoForm.ker_bilinFormAt_mpullback`: the null space of a pullback along a map with
  surjective derivative.
* `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_mpullback`: a form is
  nondegenerate exactly when the null spaces of its pullback along a surjective submersion are
  the kernels of the derivative.
* `TauCeti.SmoothTwoForm.isSymplectic_iff_of_mpullback_eq`: the same characterization of
  symplectic forms.
* `TauCeti.SmoothTwoForm.isSymplectic_descendBasic`: the descent of a closed basic two-form whose
  null spaces are the kernels of the derivative is symplectic.
* `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`: existence and uniqueness of the
  descended symplectic form.

## References

* Jerrold Marsden and Alan Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 23 (reduction).
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H Z E' H' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {p : Z → Q} {σ : SmoothTwoForm I Z} {η : SmoothTwoForm J Q}

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

/-- For a surjective `p` with surjective derivatives, `η` is nondegenerate exactly when, at every
point `z`, the null space of the pullback `p^* η` is the kernel of the derivative of `p`. -/
theorem isNondegenerate_iff_forall_ker_bilinFormAt_mpullback (hp : ContMDiff I J ∞ p)
    (hsurj : Surjective p) (hdp : ∀ z, Surjective (mfderiv I J p z)) :
    η.IsNondegenerate ↔ ∀ z, LinearMap.ker ((SmoothForm.mpullback p hp η).bilinFormAt z) =
      (mfderiv I J p z).ker := by
  simp only [ker_bilinFormAt_mpullback hp η (hdp _), ← Submodule.comap_bot,
    isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot]
  refine ⟨fun h z ↦ by rw [h], fun h y ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hsurj y
  exact Submodule.comap_injective_of_surjective (hdp z) (h z)

/-- **Symplectic forms through a surjective submersion.** If `p` is a surjective smooth submersion
and `p^* η = σ`, then `η` is symplectic exactly when `σ` is closed and its null space at every
point is the kernel of the derivative of `p`. -/
theorem isSymplectic_iff_of_mpullback_eq (hp : IsSubmersion I J ∞ p) (hsurj : Surjective p)
    (hη : SmoothForm.mpullback p hp.contMDiff η = σ) :
    η.IsSymplectic ↔
      σ.IsClosed ∧ ∀ z, LinearMap.ker (σ.bilinFormAt z) = (mfderiv I J p z).ker := by
  subst hη
  rw [hp.isClosed_mpullback_iff hsurj, ← isNondegenerate_iff_forall_ker_bilinFormAt_mpullback
    hp.contMDiff hsurj (hp.surjective_mfderiv (by simp))]
  exact ⟨fun h ↦ ⟨h.isClosed, h.isNondegenerate⟩, fun h ↦ ⟨h.1, h.2⟩⟩

variable [I.Boundaryless]

/-- **Descent of symplectic forms.** For a surjective smooth submersion `p` out of a manifold whose
model has no boundary, the descent of a closed basic two-form whose null space at every point is
the kernel of the derivative of `p` is symplectic. -/
theorem isSymplectic_descendBasic (hp : IsSubmersion I J ∞ p) (hsurj : Surjective p)
    (hσ : σ.IsClosed) (hbasic : RoughForm.IsBasic (V := ℝ) (k := 2) I J p σ.1)
    (hker : ∀ z, LinearMap.ker (σ.bilinFormAt z) = (mfderiv I J p z).ker) :
    SmoothTwoForm.IsSymplectic (SmoothForm.descendBasic hp hsurj σ hbasic) :=
  (isSymplectic_iff_of_mpullback_eq hp hsurj SmoothForm.mpullback_descendBasic).mpr ⟨hσ, hker⟩

/-- **Existence and uniqueness of the descended symplectic form.** For a surjective smooth
submersion `p` out of a manifold whose model has no boundary, and a closed basic two-form `σ`
whose null space at every point is the kernel of the derivative of `p`, there is exactly one
two-form `η` with `p^* η = σ`, and it is symplectic. -/
theorem existsUnique_isSymplectic_mpullback_eq (hp : IsSubmersion I J ∞ p)
    (hsurj : Surjective p) (hσ : σ.IsClosed)
    (hbasic : RoughForm.IsBasic (V := ℝ) (k := 2) I J p σ.1)
    (hker : ∀ z, LinearMap.ker (σ.bilinFormAt z) = (mfderiv I J p z).ker) :
    ∃! η : SmoothTwoForm J Q, η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = σ :=
  ⟨SmoothForm.descendBasic hp hsurj σ hbasic,
    ⟨isSymplectic_descendBasic hp hsurj hσ hbasic hker, SmoothForm.mpullback_descendBasic⟩,
    fun _ h ↦ SmoothForm.eq_descendBasic_iff.mpr h.2⟩

end SmoothTwoForm

end TauCeti
