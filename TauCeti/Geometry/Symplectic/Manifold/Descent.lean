/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Symplectic forms descended along submersions

Let `f : M → M'` be a surjective smooth submersion from a boundaryless manifold, and let `σ` be a
smooth two-form on `M` that is basic for `f` (`TauCeti.RoughForm.IsBasic`). Then `σ` is the
pullback of a unique smooth two-form `β` on `M'`, its descent
`TauCeti.SmoothForm.descendedForm`. This file determines when `β` is symplectic.

Since `σ_x(u, w) = β_(f x)(df_x u, df_x w)` and `df_x` is surjective, a vector `u` lies in the
kernel of `σ_x` exactly when `df_x u` lies in the kernel of `β_(f x)`. So `β` is nondegenerate
exactly when the kernel of `σ_x` is the kernel of `df_x` at every point
(`TauCeti.SmoothTwoForm.isNondegenerate_descendedForm_iff`). As descent detects closedness, `β` is
symplectic exactly when `σ` is closed and has these kernels
(`TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`).

Basicness is usually checked through a family of self-maps of `M` over `f` that is transitive on
its fibres, such as a group action whose orbits are the fibres: a two-form invariant under these
maps whose null spaces contain the kernels of `df` is basic
(`TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq`), an instance of
`TauCeti.RoughForm.isBasic_of_mpullback_eq`.

This is the final step of symplectic reduction: on a regular level `Z = μ⁻¹(c)` of a moment map
with free and proper stabilizer action, the restriction of the symplectic form is closed, basic for
the orbit projection `Z → Z / G_c`, and has kernel the tangent spaces of the orbits, which are the
kernels of the derivative of the projection; its descent is the reduced symplectic form.

## Main results

* `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`: a closed basic two-form with
  these kernels descends to a unique symplectic form.
* `TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq`: an invariant two-form vanishing on the kernels
  of `df` is basic.
* `TauCeti.SmoothTwoForm.eval₂_descendedForm_mfderiv`: the descent evaluates on images under the
  derivative of `f` as the form.
* `TauCeti.SmoothTwoForm.isNondegenerate_descendedForm_iff`: the descent of a basic two-form is
  nondegenerate exactly when the kernel of the form is the kernel of the derivative of `f`.
* `TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`: the descent is symplectic exactly when
  the form is moreover closed.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the Marsden–Weinstein–Meyer theorem: the reduced form as the
  descent of the restricted form).
* Jerrold Marsden and Alan Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports
  on Mathematical Physics 5 (1974), 121–130.
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

section Descent

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] [I.Boundaryless]
  {f : M → M'} {hf : IsSubmersion I I' ∞ f} {hsurj : Surjective f} {σ : SmoothTwoForm I M}
  {hσ : RoughForm.IsBasic (V := ℝ) I' f σ.1}

/-- The descent `β` of a basic two-form `σ` evaluates on images under the derivative of `f` as
`σ`: `σ_x(u, w) = β_(f x)(df_x u, df_x w)`. -/
theorem eval₂_descendedForm_mfderiv (x : M) (u w : TangentSpace I x) :
    SmoothBundleForm.eval₂ (SmoothForm.descendedForm hf hsurj σ hσ) (f x)
        (mfderiv I I' f x u) (mfderiv I I' f x w) =
      SmoothBundleForm.eval₂ σ x u w := by
  rw [← SmoothForm.eval₂_mpullback f hf.contMDiff, SmoothForm.mpullback_descendedForm]

/-- **The descended form is nondegenerate exactly when the kernels match.** The descent of a
two-form `σ` basic for a surjective smooth submersion `f` is nondegenerate exactly when, at every
point `x`, the kernel of `σ_x` is the kernel of the derivative of `f` at `x`. -/
theorem isNondegenerate_descendedForm_iff :
    IsNondegenerate (SmoothForm.descendedForm hf hsurj σ hσ) ↔
      ∀ x, LinearMap.ker (σ.bilinFormAt x) = (mfderiv I I' f x).ker := by
  simpa only [SmoothForm.mpullback_descendedForm] using
    (isNondegenerate_iff_forall_ker_bilinFormAt_mpullback
      (η := SmoothForm.descendedForm hf hsurj σ hσ) hf.contMDiff hsurj
      (hf.surjective_mfderiv (by simp)))

/-- **Symplectic descent.** The descent of a two-form `σ` basic for a surjective smooth
submersion `f` is symplectic exactly when `σ` is closed and, at every point `x`, the kernel of
`σ_x` is the kernel of the derivative of `f` at `x`. -/
theorem isSymplectic_descendedForm_iff :
    IsSymplectic (SmoothForm.descendedForm hf hsurj σ hσ) ↔
      SmoothForm.IsClosed σ ∧
        ∀ x, LinearMap.ker (σ.bilinFormAt x) = (mfderiv I I' f x).ker :=
  isSymplectic_iff_of_mpullback_eq hf.contMDiff hsurj (hf.surjective_mfderiv (by simp))
    SmoothForm.mpullback_descendedForm

end Descent

section Existence

variable {E H Z E' H' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {p : Z → Q} {σ : SmoothTwoForm I Z} {η : SmoothTwoForm J Q}

omit [IsManifold J ∞ Q] in
/-- **Invariant two-forms vanishing on vertical vectors are basic.** Let `τ` be a family of smooth
self-maps of `Z` over a differentiable map `p` (`p ∘ τ i = p`) that is transitive on the fibres of
`p`. A two-form `σ` invariant under every `τ i` whose null space at every point contains the
kernel of the derivative of `p` is basic for `p`. -/
theorem isBasic_of_mpullback_eq {ι : Type*} (hp : MDifferentiable I J p) {τ : ι → Z → Z}
    (hτ : ∀ i, ContMDiff I I ∞ (τ i)) (hpτ : ∀ i, p ∘ τ i = p)
    (hτp : ∀ x y, p x = p y → x = y ∨ ∃ i, τ i x = y)
    (hστ : ∀ i, SmoothForm.mpullback (τ i) (hτ i) σ = σ)
    (hker : ∀ z, (mfderiv I J p z).ker ≤ LinearMap.ker (σ.bilinFormAt z)) :
    RoughForm.IsBasic (V := ℝ) (k := 2) J p σ.1 := by
  refine RoughForm.isBasic_of_mpullback_eq hp (fun i ↦ (hτ i).mdifferentiable (by simp)) hpτ hτp
    (fun i ↦ by rw [← SmoothForm.coe_mpullback _ (hτ i), hστ i]) fun z v j hj ↦ ?_
  -- A two-form vanishes on a pair of vectors one of which lies in its null space.
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  have hj' := hker z hj
  rw [hv, ← SmoothBundleForm.eval₂_apply, ← SmoothForm.bilinFormAt_apply]
  fin_cases j
  · exact LinearMap.congr_fun hj' (v 1)
  · exact (SmoothForm.isAlt_bilinFormAt σ z).isRefl _ _ (LinearMap.congr_fun hj' (v 0))

variable [I.Boundaryless]

/-- **Existence and uniqueness of the descended symplectic form.** For a surjective smooth
submersion `p` out of a manifold whose model has no boundary, and a closed basic two-form `σ`
whose null space at every point is the kernel of the derivative of `p`, there is exactly one
symplectic two-form `η` with `p^* η = σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq (hp : IsSubmersion I J ∞ p)
    (hsurj : Surjective p) (hσ : σ.IsClosed)
    (hbasic : RoughForm.IsBasic (V := ℝ) (k := 2) J p σ.1)
    (hker : ∀ z, LinearMap.ker (σ.bilinFormAt z) = (mfderiv I J p z).ker) :
    ∃! η : SmoothTwoForm J Q, η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = σ :=
  ⟨SmoothForm.descendedForm hp hsurj σ hbasic,
    ⟨(isSymplectic_descendedForm_iff (hf := hp) (hsurj := hsurj) (hσ := hbasic)).mpr ⟨hσ, hker⟩,
      SmoothForm.mpullback_descendedForm⟩,
    fun _ h ↦ SmoothForm.eq_descendedForm_iff.mpr h.2⟩

end Existence

end TauCeti.SmoothTwoForm
