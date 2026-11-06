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
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Darboux.Immersion

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
/-- Read in the preferred charts at `p` and at `i p`, a map `i` which is smooth at a point `q` of
the chart domain at `p` and maps `q` into the chart domain at `i p` is smooth at the chart point `y`
of `q`, provided `y` lies in the interior of the chart target. Its derivative there is the
differential of `i` at `q`, read in the charts. -/
private theorem contDiffAt_extChartAt_comp_comp_extChartAt_symm {i : Q → M} {p : Q} {y : E'}
    (hy : y ∈ interior (extChartAt J p).target)
    (hiy : ContMDiffAt J I ∞ i ((extChartAt J p).symm y))
    (hφy : i ((extChartAt J p).symm y) ∈ (extChartAt I (i p)).source) :
    ContDiffAt ℝ ∞ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y ∧
      ∀ v, fderiv ℝ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y v =
        mvfderiv I (extChartAt I (i p)) (i ((extChartAt J p).symm y))
          (mfderiv J I i ((extChartAt J p).symm y)
            (mfderiv 𝓘(ℝ, E') J (extChartAt J p).symm y v)) := by
  have hφs : i ((extChartAt J p).symm y) ∈ (chartAt H (i p)).source := by
    rwa [← extChartAt_source (I := I)]
  have hψs : (extChartAt J p).symm y ∈ (chartAt H' p).source := by
    rw [← extChartAt_source (I := J)]
    exact (extChartAt J p).map_target (interior_subset hy)
  have h := ((contMDiffAt_iff_of_mem_source hψs hφs).1 hiy).2
  rw [(extChartAt J p).right_inv (interior_subset hy)] at h
  refine ⟨h.contDiffAt (mem_of_superset (isOpen_interior.mem_nhds hy)
    (interior_subset.trans (extChartAt_target_subset_range p))), fun v ↦ ?_⟩
  have hψd : MDifferentiableAt 𝓘(ℝ, E') J (extChartAt J p).symm y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)).mdifferentiableAt (by simp)
  have hid : MDifferentiableAt J I i ((extChartAt J p).symm y) := hiy.mdifferentiableAt (by simp)
  have hfd : fderiv ℝ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y v =
      mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y v := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hfd, mvfderiv_apply_eq_mfderiv_apply]
  exact (mfderiv_comp_apply y (mdifferentiableAt_extChartAt hφs) (hid.comp y hψd) v).trans
    (congrArg _ (mfderiv_comp_apply y hid hψd v))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- In the setting of `contDiffAt_extChartAt_comp_comp_extChartAt_symm`, pulling the coordinate
expression of a form in the chart at `i p` back along `i` read in charts gives the pullback of the
form along `i`, read in the chart at `p`. -/
private theorem compContinuousLinearMap_inChartAt_extChartAt_comp_comp_extChartAt_symm
    (σ : SmoothTwoForm I M) {i : Q → M} {p : Q} {y : E'}
    (hy : y ∈ interior (extChartAt J p).target)
    (hiy : ContMDiffAt J I ∞ i ((extChartAt J p).symm y))
    (hφy : i ((extChartAt J p).symm y) ∈ (extChartAt I (i p)).source) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (RoughForm.inChartAt σ.1 (i p) (extChartAt I (i p) (i ((extChartAt J p).symm y))))
        (fderiv ℝ (extChartAt I (i p) ∘ i ∘ (extChartAt J p).symm) y) =
      (mpullback J I i σ.1 ((extChartAt J p).symm y)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, E') J (extChartAt J p).symm y) := by
  ext v
  change RoughForm.inChartAt σ.1 (i p) _ (fun j ↦ fderiv ℝ _ y (v j)) =
    mpullback J I i σ.1 _ (fun j ↦ mfderiv 𝓘(ℝ, E') J (extChartAt J p).symm y (v j))
  rw [mpullback_apply, RoughForm.apply_eq_inChartAt_mvfderiv σ.1 hφy]
  congr 1
  funext j
  exact (contDiffAt_extChartAt_comp_comp_extChartAt_symm hy hiy hφy).2 (v j)

omit [FiniteDimensional ℝ E] in
/-- **Transport through a chart.** Let `φ` be the preferred chart at `x₀`, and let `Φf` be a smooth
partial diffeomorphism of the model space which pulls the coordinate expression of `σ₁` in `φ` back
to that of `σ₀` on its source. Then `φ⁻¹ ∘ Φf ∘ φ` is a smooth partial diffeomorphism of `M` which
pulls `σ₁` back to `σ₀` on its source. -/
private theorem exists_partialDiffeomorph_of_inChartAt {σ₀ σ₁ : SmoothTwoForm I M} (x₀ : M)
    (Φf : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hpb : ∀ z ∈ Φf.source, (RoughForm.inChartAt σ₁.1 x₀ (Φf z)).compContinuousLinearMap
      (fderiv ℝ Φf z) = RoughForm.inChartAt σ₀.1 x₀ z) :
    ∃ Φ : PartialDiffeomorph I I M M ∞, (∀ x, x ∈ Φ.source ↔
        (x ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ x ∈ interior (extChartAt I x₀).target) ∧
          extChartAt I x₀ x ∈ Φf.source ∧
            Φf (extChartAt I x₀ x) ∈ interior (extChartAt I x₀).target) ∧
      (∀ x, Φ x = (extChartAt I x₀).symm (Φf (extChartAt I x₀ x))) ∧
      ∀ x ∈ Φ.source, mpullback I I Φ σ₁.1 x = σ₀.1 x := by
  set φ := extChartAt I x₀ with hφ
  let e₀ := extChartPartialDiffeomorph I ∞ x₀
  let Φ : PartialDiffeomorph I I M M ∞ := e₀.trans (Φf.trans e₀.symm)
  have hΦeq : Φ.toPartialEquiv =
      e₀.toPartialEquiv.trans (Φf.toPartialEquiv.trans e₀.toPartialEquiv.symm) := by
    simp only [Φ, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv]
  have hΦ (x : M) : Φ x = φ.symm (Φf (φ x)) := by
    rw [hΦeq]
    simp [e₀, hφ]
  have hΦsrc (x : M) : x ∈ Φ.source ↔ (x ∈ φ.source ∧ φ x ∈ interior φ.target) ∧
      φ x ∈ Φf.source ∧ Φf (φ x) ∈ interior φ.target := by
    rw [hΦeq]
    simp [e₀, hφ, extChartPartialDiffeomorph_source]
  refine ⟨Φ, hΦsrc, hΦ, fun x hx ↦ ?_⟩
  obtain ⟨⟨hxs, -⟩, hxf, hfW⟩ := (hΦsrc x).1 hx
  have hΦxs : Φ x ∈ φ.source := hΦ x ▸ φ.map_target (interior_subset hfW)
  have hφΦ : φ (Φ x) = Φf (φ x) := by rw [hΦ, φ.right_inv (interior_subset hfW)]
  have hφd (z : M) (hz : z ∈ φ.source) : MDifferentiableAt I 𝓘(ℝ, E) φ z :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := I)])
  -- The chain rule for `φ ∘ Φ = Φf ∘ φ`, valid near `x`.
  have hloc : φ ∘ Φ =ᶠ[𝓝 x] Φf ∘ φ :=
    eventually_of_mem (Φ.open_source.mem_nhds hx) fun x' hx' ↦ by
      obtain ⟨-, -, hW'⟩ := (hΦsrc x').1 hx'
      rw [Function.comp_apply, hΦ, φ.right_inv (interior_subset hW'), Function.comp_apply]
  have hchain (w : TangentSpace I x) :
      mvfderiv I φ (Φ x) (mfderiv I I Φ x w) = fderiv ℝ Φf (φ x) (mvfderiv I φ x w) := by
    rw [← mvfderiv_comp_apply x (hφd _ hΦxs) (Φ.mdifferentiableAt (by simp) hx),
      hloc.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt
        (mdifferentiableAt_iff_differentiableAt.1 (Φf.mdifferentiableAt (by simp) hxf))
        (hφd x hxs)]
  ext v
  have h := congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A (fun j ↦ mvfderiv I φ x (v j)))
    (hpb (φ x) hxf)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] at h
  rw [mpullback_apply, RoughForm.apply_eq_inChartAt_mvfderiv σ₁.1 hΦxs,
    RoughForm.apply_eq_inChartAt_mvfderiv σ₀.1 hxs, ← hφ, hφΦ]
  simp only [hchain]
  exact h

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
  refine ⟨(contDiffAt_extChartAt_comp_comp_extChartAt_symm hy hiy hφy).1, ?_⟩
  have h₁ := compContinuousLinearMap_inChartAt_extChartAt_comp_comp_extChartAt_symm σ₁ hy hiy hφy
  rw [ht] at h₁
  exact h₁.trans
    (compContinuousLinearMap_inChartAt_extChartAt_comp_comp_extChartAt_symm σ₀ hy hiy hφy).symm

omit [FiniteDimensional ℝ E] in
/-- The coordinate expression of a two-form, nondegenerate at `x`, in the preferred chart at `x` is
nondegenerate at the chart point of `x`. -/
private theorem inChartAt_extChartAt_self_nondegenerate {σ : SmoothTwoForm I M} {x : M}
    (hnd : (σ.bilinFormAt x).Nondegenerate) :
    ∀ v, (∀ w, RoughForm.inChartAt σ.1 x (extChartAt I x x) ![v, w] = 0) → v = 0 := fun v hv ↦
  hnd.1 v fun w ↦ by
    have h := hv w
    rw [RoughForm.inChartAt_extChartAt_self] at h
    let v' : TangentSpace I x := v
    let w' : TangentSpace I x := w
    exact (SmoothForm.bilinFormAt_apply σ x v' w').trans
      ((SmoothBundleForm.eval₂_apply σ x v' w').trans h)

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
          (interior_subset.trans (extChartAt_target_subset_range p)))]
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
      (hgy₀ ▸ inChartAt_extChartAt_self_nondegenerate hnd₀)
      (hgy₀ ▸ inChartAt_extChartAt_self_nondegenerate hnd₁)
  -- Carry `Φf` back to `M` through the chart `φ`; it fixes the chart points `g (ψ q) = φ (i q)`.
  obtain ⟨Φ, hΦsrc, hΦ, hΦpb⟩ := exists_partialDiffeomorph_of_inChartAt (i p) Φf hpb
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
