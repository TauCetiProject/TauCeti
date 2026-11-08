/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Manifold.MaximumPrinciple

/-!
# No escape for `J`-holomorphic strips in a Liouville completion

Let `M` be a completion of the Liouville domain `W ⊆ M` for the symplectic form `ω = dα`, and let
`r = TauCeti.liouvilleRadialCoordinate Z W` be the radial coordinate of its cylindrical end
`M \ W`, smooth there by `TauCeti.IsLiouvilleCompletion.contMDiffAt_liouvilleRadialCoordinate`.
An almost complex structure `J` is of contact type on the part `{r > R}` of the end when
`dr ∘ J = -α` there.

This file proves that holomorphic strips cannot escape into the cylindrical end. If `J` is of
contact type and tamed by `ω` on `{r > R}`, for some `R ≥ 1`, then a `J`-holomorphic strip
`ℝ × [0, 1] → M` whose two boundary lines and two ends `|ℜ z| ≥ T` lie in `{r ≤ R}` lies entirely
in `{r ≤ R}`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_of_le_strip_boundary_of_le_ends`).
This is the a priori bound on the images of Floer strips between exact Lagrangians contained in
`{r ≤ R}`, needed before compactness for holomorphic curves can be applied. It is the maximum
principle `TauCeti.Pseudoholomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends` for the
radial coordinate and the Liouville primitive, whose exterior derivative is `ω`.

The almost complex structure does not depend on the point of the strip, and the equation carries
no Hamiltonian term.

## Main results

* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_of_le_strip_boundary_of_le_ends`:
  a `J`-holomorphic strip with boundary lines and ends in `{r ≤ R}` lies in `{r ≤ R}`.

## References

* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol.
  **14** (2010), 627--718; arXiv:0712.3177v2, Lemma 7.2.
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (completions and almost complex structures of contact type).
-/

public section

open Set Complex
open scoped Manifold Topology

namespace TauCeti

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {J : SmoothAlmostComplexStructure I M} {u : ℂ → M} {z : ℂ}

/-- **No escape for strips in a Liouville completion.** Let `r` be the radial coordinate of a
completion of the Liouville domain `W`, and let `R ≥ 1`. Suppose that on `{r > R}` the almost
complex structure `J` is of contact type, `dr ∘ J = -α`, and is tamed by `ω`, that is
`ω(v, J v) ≥ 0`. Let `u` be `C²` and `J`-holomorphic on the open strip `ℝ × (0, 1)`, with `r ∘ u`
continuous on the closed strip `ℝ × [0, 1]`. If `u` maps both boundary lines `ℑ z = 0` and
`ℑ z = 1` into `{r ≤ R}`, and also the two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u`
maps the whole strip into `{r ≤ R}`. -/
theorem liouvilleRadialCoordinate_le_of_le_strip_boundary_of_le_ends
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) {R T : ℝ}
    (hR : 1 ≤ R)
    (hJ : ∀ x, R < liouvilleRadialCoordinate Z W x → ∀ v,
      mvfderiv I (liouvilleRadialCoordinate Z W) x (J x v) = -α.1 x ![v])
    (htame : ∀ x, R < liouvilleRadialCoordinate Z W x → ∀ v, 0 ≤ ω.eval₂ x v (J x v))
    (hf : ContinuousOn (liouvilleRadialCoordinate Z W ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (h₀ : ∀ z : ℂ, z.im = 0 → liouvilleRadialCoordinate Z W (u z) ≤ R)
    (h₁ : ∀ z : ℂ, z.im = 1 → liouvilleRadialCoordinate Z W (u z) ≤ R)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → liouvilleRadialCoordinate Z W (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : liouvilleRadialCoordinate Z W (u z) ≤ R := by
  -- On `{r > R}` the point lies outside `W`, where `r` is smooth.
  have hρ (x : M) (hx : R < liouvilleRadialCoordinate Z W x) :
      ContMDiffAt I 𝓘(ℝ) 2 (liouvilleRadialCoordinate Z W) x :=
    (h.contMDiffAt_liouvilleRadialCoordinate hZ
      ((h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (hR.trans_lt hx))).of_le (by simp)
  refine Pseudoholomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends hf hu hCR hρ
    (fun x _ ↦ ((isSmoothForm_def _ _).1 α.isSmoothForm x).mdifferentiableAt (by simp)) hJ
    (fun x hx v ↦ ?_) h₀ h₁ hends hz₀ hz₁
  rw [h.mextDeriv_eq]
  simpa only [SmoothBundleForm.eval₂_apply] using htame x hx v

end IsLiouvilleCompletion

end TauCeti
