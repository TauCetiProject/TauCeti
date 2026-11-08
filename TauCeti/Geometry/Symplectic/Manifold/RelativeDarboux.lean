/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Symplectic.Darboux.Immersion
import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The point-germ relative Darboux theorem on manifolds

Let `M` be a smooth manifold modelled on a finite-dimensional real normed space, and let
`i : Q → M` be a smooth map from a second such manifold which is an immersion at `p`: its
differential at `p` is injective. For instance, `i` may be the inclusion of an embedded
submanifold. Let `σ₀`, `σ₁` be closed two-forms on `M`, nondegenerate at `i p`, whose pullbacks
along `i` agree near `p`. These pullbacks may have any rank; in particular `Q` need not be a
symplectic, isotropic or coisotropic submanifold.

The **point-germ relative Darboux theorem**
(`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_fix_immersion_mpullback_eq`) gives a smooth
partial diffeomorphism `Φ` of `M`, defined near `i p`, which fixes `i q` for every `q` near `p` and
pulls `σ₁` back to `σ₀` on its source. So `σ₀` and `σ₁` have symplectomorphic germs at `i p`, by a
germ fixing the image of `Q` near `i p`. Away from the image of `Q` the two forms are unrelated,
and nothing is assumed about `Q` away from `p`.

The proof reads everything in the preferred charts at `p` and at `i p`. The forms become flat
closed forms on the interior of the chart target of `M`, `i` becomes a smooth map between model
spaces with injective derivative at the chart point of `p`, and the pullback hypothesis transfers
by the chain rule. The flat theorem along an immersion
(`TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`) gives a
partial diffeomorphism of the model space, which the chart at `i p` carries back to `M`.

The main theorem only needs `p` and `i p` to be interior points; the boundaryless form is
`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_fix_immersion_mpullback_eq`.

## Main results

* `TauCeti.SmoothTwoForm.exists_partialDiffeomorph_fix_immersion_mpullback_eq_of_isInteriorPoint`:
  the relative Darboux theorem at interior points.
* `TauCeti.SmoothTwoForm.exists_partialDiffeomorph_fix_immersion_mpullback_eq`: the relative
  Darboux theorem on boundaryless manifolds.

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346 (the relative Darboux theorem).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 7 (Moser's relative theorem).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M E' H' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Near the chart point of `p`, the map `i` read in the preferred charts at `p` and `i p` is smooth
and pulls the coordinate expressions of `σ₀` and `σ₁` back to the same form, when `i` is smooth near
`p`, `σ₀` and `σ₁` have the same pullback along `i` near `p`, and `p` is an interior point. -/
private theorem eventually_contDiffAt_and_compContinuousLinearMap_eq {σ₀ σ₁ : SmoothTwoForm I M}
    {i : Q → M} {p : Q} (hp : J.IsInteriorPoint p) (hi : ∀ᶠ q in 𝓝 p, ContMDiffAt J I ∞ i q)
    (htan : ∀ᶠ q in 𝓝 p, mpullback J I i σ₁.1 q = mpullback J I i σ₀.1 q) :
    ∀ᶠ y in 𝓝 (extChartAt J p p),
      ContDiffAt ℝ ∞ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y ∧
      ContinuousAlternatingMap.compContinuousLinearMap
          (RoughForm.inChartAt σ₁.1 (i p) ((extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y))
          (fderiv ℝ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y) =
        ContinuousAlternatingMap.compContinuousLinearMap
          (RoughForm.inChartAt σ₀.1 (i p) ((extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y))
          (fderiv ℝ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y) := by
  have hsrc : ∀ᶠ q in 𝓝 p, i q ∈ (extChartAt I (i p)).source :=
    (hi.self_of_nhds.continuousAt).preimage_mem_nhds (extChartAt_source_mem_nhds (i p))
  have h := (continuousAt_extChartAt_symm (I := J) p).eventually
    (by rw [extChartAt_to_inv]; exact hi.and (hsrc.and htan))
  filter_upwards [isOpen_interior.mem_nhds
    ((ModelWithCorners.isInteriorPoint_iff (I := J)).mp hp), h] with y hy ⟨hiy, hφy, ht⟩
  have hψd : MDifferentiableAt 𝓘(ℝ, E') J (extChartAt J p).symm y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)).mdifferentiableAt (by simp)
  have hid : MDifferentiableAt J I i ((extChartAt J p).symm y) := hiy.mdifferentiableAt (by simp)
  -- The flat pullback along `i` read in charts is the pullback along `i ∘ ψ⁻¹`, which factors
  -- through the pullback along `i`.
  have hflat (σ : SmoothTwoForm I M) :
      ContinuousAlternatingMap.compContinuousLinearMap
          (RoughForm.inChartAt σ.1 (i p) ((extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y))
          (fderiv ℝ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y) =
        mpullback 𝓘(ℝ, E') J (extChartAt J p).symm (mpullback J I i σ.1) y := by
    rw [← TauCeti.mpullback_comp_at hψd hid,
      ← mpullbackWithin_univ (I := 𝓘(ℝ, E')) (i ∘ (extChartAt J p).symm) σ.1,
      RoughForm.mpullbackWithin_eq_compContinuousLinearMap (f := i ∘ (extChartAt J p).symm) σ.1
        (i p) hφy (hid.comp y hψd).mdifferentiableWithinAt uniqueDiffWithinAt_univ,
      fderivWithin_univ, Function.comp_apply]
  refine ⟨hiy.contDiffAt_extChartAt_comp_extChartAt_symm hy hφy, ?_⟩
  rw [hflat σ₁, hflat σ₀]
  ext v
  simp only [mpullback_apply, ht]

/-- **The point-germ relative Darboux theorem at interior points.** Let `i : Q → M` be smooth near
`p` with injective differential at `p`, where `p` and `i p` are interior points, and let `σ₀`, `σ₁`
be closed two-forms on `M`, nondegenerate at `i p`, whose pullbacks along `i` agree near `p`. Then
some smooth partial diffeomorphism `Φ` of `M` with `i p` in its source fixes `i q` for every `q`
near `p` and pulls `σ₁` back to `σ₀` on its source. -/
theorem exists_partialDiffeomorph_fix_immersion_mpullback_eq_of_isInteriorPoint
    {σ₀ σ₁ : SmoothTwoForm I M} (hσ₀ : σ₀.IsClosed) (hσ₁ : σ₁.IsClosed) {i : Q → M} {p : Q}
    (hp : J.IsInteriorPoint p) (hip : I.IsInteriorPoint (i p))
    (hi : ∀ᶠ q in 𝓝 p, ContMDiffAt J I ∞ i q) (hinj : Function.Injective (mfderiv J I i p))
    (htan : ∀ᶠ q in 𝓝 p, mpullback J I i σ₁.1 q = mpullback J I i σ₀.1 q)
    (hnd₀ : (σ₀.bilinFormAt (i p)).Nondegenerate) (hnd₁ : (σ₁.bilinFormAt (i p)).Nondegenerate) :
    ∃ Φ : PartialDiffeomorph I I M M ∞, i p ∈ Φ.source ∧ (∀ᶠ q in 𝓝 p, Φ (i q) = i q) ∧
      ∀ x ∈ Φ.source, mpullback I I Φ σ₁.1 x = σ₀.1 x := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- The preferred charts `φ` at `i p` and `ψ` at `p`, and `i` read in them.
  set φ := extChartAt I (i p) with hφ
  set ψ := extChartAt J p with hψ
  let g : E' → E := φ ∘ i ∘ ψ.symm
  have hgψ (q : Q) (hq : q ∈ ψ.source) : g (ψ q) = φ (i q) := by
    simp only [g, Function.comp_apply, ψ.left_inv hq]
  have hx₀ : φ (i p) ∈ interior φ.target := (ModelWithCorners.isInteriorPoint_iff (I := I)).mp hip
  have hgy₀ : g (ψ p) = φ (i p) := hgψ p (mem_extChartAt_source p)
  -- The hypotheses of the flat theorem along `g`, for the coordinate expressions of the forms.
  have hev := eventually_contDiffAt_and_compContinuousLinearMap_eq hp hi htan
  have hinjflat : Function.Injective (fderiv ℝ g (ψ p)) := by
    have h : (fderiv ℝ g (ψ p) : E' → E) = mfderiv J I i p := by
      rw [(hi.self_of_nhds.mdifferentiableAt (by simp)).mfderiv, fderivWithin_of_mem_nhds
        (mem_of_superset (isOpen_interior.mem_nhds
          ((ModelWithCorners.isInteriorPoint_iff (I := J)).mp hp))
          (interior_subset.trans (extChartAt_target_subset_range p))), writtenInExtChartAt]
      -- `g` is the unfolded `writtenInExtChartAt J I p i`, and the tangent spaces
      -- `TangentSpace J p` and `TangentSpace I (i p)` are `E'` and `E` by definition.
      rfl
    rwa [h]
  obtain ⟨Φf, hsrc, hfix, hpb⟩ :=
    exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq le_top
      isOpen_interior (hgy₀ ▸ hx₀) (σ₀.isSmoothForm.contDiffOn_inChartAt_interior_target (i p))
      (σ₁.isSmoothForm.contDiffOn_inChartAt_interior_target (i p))
      (fun _ hx ↦ hσ₀.extDeriv_inChartAt_eq_zero (i p) hx)
      (fun _ hx ↦ hσ₁.extDeriv_inChartAt_eq_zero (i p) hx)
      (hev.mono fun y hy ↦ (show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ∞ by simp) ▸ hy.1) hinjflat
      (hev.mono fun _ hy ↦ hy.2)
      (hgy₀ ▸ σ₀.inChartAt_extChartAt_self_nondegenerate hnd₀)
      (hgy₀ ▸ σ₁.inChartAt_extChartAt_self_nondegenerate hnd₁)
  -- Carry `Φf` back to `M` through the chart `φ`; it fixes the chart points `g (ψ q) = φ (i q)`.
  obtain ⟨Φ, hΦsrc, hΦ, hΦpb⟩ :=
    RoughForm.exists_partialDiffeomorph_mpullback_eq_of_inChartAt (by simp) (i p) Φf hpb
  refine ⟨Φ, ?_, ?_, hΦpb⟩
  · have hf₀ : Φf (φ (i p)) = φ (i p) := hgy₀ ▸ hfix.self_of_nhds
    rw [hΦsrc, ← hφ, hf₀]
    exact ⟨⟨mem_extChartAt_source (i p), hx₀⟩, hgy₀ ▸ hsrc, hx₀⟩
  · have hfq : ∀ᶠ q in 𝓝 p, Φf (g (ψ q)) = g (ψ q) := (continuousAt_extChartAt p).eventually hfix
    have hφq : ∀ᶠ q in 𝓝 p, i q ∈ φ.source :=
      (hi.self_of_nhds.continuousAt).preimage_mem_nhds (extChartAt_source_mem_nhds (i p))
    filter_upwards [hφq, hfq, extChartAt_source_mem_nhds (I := J) p] with q hφq hq hqψ
    rw [hΦ, ← hφ, ← hgψ q hqψ, hq, hgψ q hqψ, φ.left_inv hφq]

/-- **The point-germ relative Darboux theorem.** Let `i : Q → M` be a smooth map between
boundaryless manifolds with injective differential at `p`, and let `σ₀`, `σ₁` be closed two-forms
on `M`, nondegenerate at `i p`, whose pullbacks along `i` agree near `p`. Then some smooth partial
diffeomorphism `Φ` of `M` with `i p` in its source fixes `i q` for every `q` near `p` and pulls
`σ₁` back to `σ₀` on its source. -/
theorem exists_partialDiffeomorph_fix_immersion_mpullback_eq [BoundarylessManifold I M]
    [BoundarylessManifold J Q] {σ₀ σ₁ : SmoothTwoForm I M} (hσ₀ : σ₀.IsClosed)
    (hσ₁ : σ₁.IsClosed) {i : Q → M} {p : Q} (hi : ∀ᶠ q in 𝓝 p, ContMDiffAt J I ∞ i q)
    (hinj : Function.Injective (mfderiv J I i p))
    (htan : ∀ᶠ q in 𝓝 p, mpullback J I i σ₁.1 q = mpullback J I i σ₀.1 q)
    (hnd₀ : (σ₀.bilinFormAt (i p)).Nondegenerate) (hnd₁ : (σ₁.bilinFormAt (i p)).Nondegenerate) :
    ∃ Φ : PartialDiffeomorph I I M M ∞, i p ∈ Φ.source ∧ (∀ᶠ q in 𝓝 p, Φ (i q) = i q) ∧
      ∀ x ∈ Φ.source, mpullback I I Φ σ₁.1 x = σ₀.1 x :=
  exists_partialDiffeomorph_fix_immersion_mpullback_eq_of_isInteriorPoint hσ₀ hσ₁
    (BoundarylessManifold.isInteriorPoint) (BoundarylessManifold.isInteriorPoint) hi hinj htan
    hnd₀ hnd₁

end TauCeti.SmoothTwoForm
