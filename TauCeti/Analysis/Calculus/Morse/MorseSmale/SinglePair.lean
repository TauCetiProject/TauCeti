/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Surjective
public import TauCeti.Analysis.Calculus.Morse.SpectralSplitting
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import TauCeti.Analysis.Calculus.Morse.GlobalChart
import TauCeti.Analysis.Fredholm.LevelSet.Transverse
import TauCeti.Analysis.Calculus.Morse.FlowExistence
import TauCeti.Dynamics.Flow.TangentCone

/-!
# Transversality for one pair of critical points, by perturbation on a slab

Let `f` be a function on a finite-dimensional real inner product space, `p` and `q` nondegenerate
critical points, and `c₁ < c₂` two levels. Perturb `f` by a finite family `h` of functions
supported in the slab `c₁ < f < c₂`: `f_s = f + ∑ sᵢ hᵢ`. Above `c₂` the unstable set of `p` does
not move, and below `c₁` the stable set of `q` does not move
(`TauCeti.unstableSet_perturb_inter_preimage_Ici`, `TauCeti.stableSet_perturb_inter_preimage_Iic`).
So the only effect of the perturbation is to move the trajectories while they cross the slab.

Fix a compact set `C` of points of the unstable set of `p` above `c₂` and a time `T`. If, at the
parameter `0`, the derivative in the parameter of `s ↦ φ^{f_s}_T x` spans `E` together with the flow
direction at every `x ∈ C` (as
`TauCeti.exists_admissible_forall_mem_range_fderiv_perturbedFlow_sup_span_eq_top` provides), then
for almost every small parameter `s` the unstable set of `p` and the stable set of `q` for `f_s` are
transverse at every point `φ^{f_s}_T x`, `x ∈ C`, that lies on a trajectory to `q` below `c₁`
(`exists_pos_ae_span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_perturb_eq_top`).

The proof applies the parametric transversality theorem
`TauCeti.ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top` to the universal map
`G (v, s) = φ^{f_s}_T (e.symm v)`, where `e` is a chart flattening the unstable set of `p` onto its
unstable subspace (`TauCeti.IsNondegenerateCriticalPoint.exists_unstableSet_chart`), and to the
stable set of `q` for `f`, flattened by
`TauCeti.IsNondegenerateCriticalPoint.exists_stableSet_chart`. The derivative of `G` in the
parameter, together with the flow direction, spans `E`
(`TauCeti.exists_pos_forall_range_fderiv_perturbedFlow_sup_span_eq_top`), and the flow direction is
tangent to the stable set; so `G` is transverse to the stable set. For almost every `s`, the
derivative of `G` in `v` is then transverse to it too, and that derivative spans the image under
the flow of the tangent space of the unstable set.

## Main results

* `exists_pos_ae_span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_perturb_eq_top`:
  for almost every small parameter, the perturbed unstable set of `p` and stable set of `q` are
  transverse along the images of `C`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014
  (transversality of the unstable and stable manifolds of a Morse function by perturbation).
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, Theorem 2.7.
-/

public section

open Set Filter Topology MeasureTheory Module
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0} {ι : Type*} [Fintype ι] {h : ι → E → ℝ}
  (ν : Measure (EuclideanSpace ℝ ι)) [ν.IsAddHaarMeasure]

namespace IsNondegenerateCriticalPoint

/-- **The stable set as a slice-chart set.** For a `C^(n+1)` function with Lipschitz gradient,
every point of the stable set of a nondegenerate critical point `q` has a `C^n` chart with
differentiable inverse flattening the stable set onto the stable Hessian subspace, in the form of
`TauCeti.IsSliceChart`. -/
private theorem exists_isSliceChart_stableSet {q : E} (hq : IsNondegenerateCriticalPoint f q)
    {n : ℕ}
    (hn : n ≠ 0) (hfs : ContDiff ℝ (n + 1) f) (hf : LipschitzWith K (∇ f)) {y : E}
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧ (∀ z ∈ e.source, ContDiffAt ℝ n e z) ∧
      (∀ z ∈ e.source, DifferentiableAt ℝ e.symm (e z)) ∧
      IsSliceChart e (hq.contDiffAt.stableLinearSubspace : Set E)
        (Flow.stableSet (negativeGradientFlow f hf) q) := by
  obtain ⟨e, hy, he, hes, hS⟩ := hq.exists_stableSet_chart hfs hf hy
  exact ⟨e, hy, he, fun z hz ↦ (hes _ (e.map_source hz)).differentiableAt (by exact_mod_cast hn),
    isSliceChart_iff.2 hS⟩

/-- **The excess dimension of a transverse intersection.** For nondegenerate critical points `p`
and `q`, the dimension of the unstable Hessian subspace of `p` minus the codimension of the stable
Hessian subspace of `q` is `ind p - ind q`. -/
private theorem finrank_unstableLinearSubspace_sub_codim_stableLinearSubspace {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q) :
    finrank ℝ hp.contDiffAt.unstableLinearSubspace -
        (finrank ℝ E - finrank ℝ hq.contDiffAt.stableLinearSubspace) =
      morseIndex f p - morseIndex f q := by
  have h₂ := hq.finrank_stableLinearSubspace_add_morseIndex
  rw [hp.contDiffAt.finrank_unstableLinearSubspace]
  omega

end IsNondegenerateCriticalPoint

omit [FiniteDimensional ℝ E] in
/-- The derivative of a flow map started through the inverse of a chart, restricted to a linear
subspace `L` of starting points: the chain rule for `(v, s) ↦ (Φ_T (e.symm v, s)).1`. -/
private theorem hasFDerivAt_fst_apply_symm {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    {L : Submodule ℝ E} {e : OpenPartialHomeomorph E E} {Ψ : E × Λ → E × Λ} {z : L × Λ}
    (he : DifferentiableAt ℝ e.symm (z.1 : E)) (hΨ : DifferentiableAt ℝ Ψ (e.symm (z.1 : E), z.2)) :
    HasFDerivAt (fun z : L × Λ ↦ (Ψ (e.symm (z.1 : E), z.2)).1)
      ((ContinuousLinearMap.fst ℝ E Λ).comp ((fderiv ℝ Ψ (e.symm (z.1 : E), z.2)).comp
        (((fderiv ℝ e.symm (z.1 : E)).comp (L.subtypeL.comp (ContinuousLinearMap.fst ℝ L Λ))).prod
          (ContinuousLinearMap.snd ℝ L Λ)))) z :=
  hasFDerivAt_fst.comp z (hΨ.hasFDerivAt.comp z ((he.hasFDerivAt.comp z
    (L.subtypeL.hasFDerivAt.comp z hasFDerivAt_fst)).prodMk hasFDerivAt_snd))

/-- Below the supports of the family, a linear map whose range spans `E` together with the gradient
of the perturbation spans `E` together with the tangent space of the stable set of `q` for `f`: the
gradients agree there, and the flow direction is tangent to the stable set. -/
private theorem range_sup_span_tangentConeAt_stableSet_eq_top {W : Type*} [AddCommGroup W]
    [Module ℝ W] (hf : LipschitzWith K (∇ f)) {s : EuclideanSpace ℝ ι} {c : ℝ}
    (hc : ∀ i, tsupport (h i) ⊆ f ⁻¹' Ioi c) {q y : E} (hy : f y < c)
    (hyS : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) {A : W →ₗ[ℝ] E}
    (hA : LinearMap.range A ⊔ (ℝ ∙ ∇ (perturb f h s) y) = ⊤) :
    LinearMap.range A ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) = ⊤ := by
  have hgrad : ∇ (perturb f h s) y = ∇ f y :=
    gradient_perturb_of_forall_notMem_tsupport s fun i hi ↦ (hc i hi).not_gt hy
  have hmem := Submodule.subset_span (R := ℝ)
    (neg_gradient_mem_tangentConeAt_of_isInvariant f hf (Flow.isInvariant_stableSet _ q) hyS)
  have hneg : ∇ f y ∈ Submodule.span ℝ
      (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) := by
    simpa using Submodule.neg_mem _ hmem
  rw [eq_top_iff, ← hA, hgrad]
  exact sup_le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 hneg) _

/-- Above the supports of the family, the derivative of the perturbed flow sends the tangent space
of the unstable set of `p` at `x`, read through a chart `e` flattening it onto `L`, into the
tangent space of the perturbed unstable set of `p` at the end point. -/
private theorem range_fderiv_comp_le_span_tangentConeAt_unstableSet_perturb
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i)) {c : ℝ}
    (hc : ∀ i, tsupport (h i) ⊆ f ⁻¹' Iio c) {p x : E} {L : Submodule ℝ E}
    {e : OpenPartialHomeomorph E E}
    (hS : IsSliceChart e (L : Set E) (Flow.unstableSet (negativeGradientFlow f hf) p))
    (hxe : x ∈ e.source) (hxu : x ∈ Flow.unstableSet (negativeGradientFlow f hf) p) (hx : c < f x)
    (he : DifferentiableAt ℝ e x) (hes : DifferentiableAt ℝ e.symm (e x)) (s : EuclideanSpace ℝ ι)
    {K' : ℝ≥0} (hf' : LipschitzWith K' (∇ (perturb f h s))) (T : ℝ) :
    LinearMap.range ((fderiv ℝ (negativeGradientFlow (perturb f h s) hf' T) x).comp
        ((fderiv ℝ e.symm (e x)).comp L.subtypeL) : L →ₗ[ℝ] E) ≤
      Submodule.span ℝ (tangentConeAt ℝ
        (Flow.unstableSet (negativeGradientFlow (perturb f h s) hf') p)
        (negativeGradientFlow (perturb f h s) hf' T x)) := by
  have hφs : ContDiff ℝ 2 (perturb f h s) := contDiff_perturb hfs hh s
  obtain ⟨A, hA⟩ := e.exists_hasFDerivAt_of_chart hxe he hes
  have hAs : fderiv ℝ e.symm (e x) = (A.symm : E →L[ℝ] E) :=
    (e.hasFDerivAt_symm (e.map_source hxe) (by rwa [e.left_inv hxe])).fderiv
  rw [Flow.span_tangentConeAt_apply (Flow.isInvariant_unstableSet _ p)
    (differentiable_negativeGradientFlow_apply _ hf' hφs (-T) _)
    (differentiable_negativeGradientFlow_apply _ hf' hφs T x),
    tangentConeAt_unstableSet_perturb hf hf' hc p hx hfs.continuous.continuousAt,
    hS.span_tangentConeAt_eq_comap (Submodule.isClosed_of_finiteDimensional _) hxe hxu hA, hAs]
  rintro _ ⟨w, rfl⟩
  exact ⟨A.symm (w : E), by simp, rfl⟩

/-- **Transversality in one chart of the unstable set.** The statement of
`exists_pos_ae_span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_perturb_eq_top`
for the points of `C` in the source of one chart `e` flattening the unstable set of `p`, given the
spanning condition for all parameters of norm less than `δ ≤ 1`. -/
private theorem ae_span_tangentConeAt_sup_span_tangentConeAt_perturb_eq_top_of_unstableSet_chart
    {m : ℕ}
    (hfs : ContDiff ℝ (m + 2) f) (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (hhs : ∀ i, ContDiff ℝ (m + 2) (h i)) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hm : morseIndex f p ≤ morseIndex f q + m) {c₁ c₂ : ℝ}
    (hc₁ : ∀ i, tsupport (h i) ⊆ f ⁻¹' Ioi c₁) (hc₂ : ∀ i, tsupport (h i) ⊆ f ⁻¹' Iio c₂)
    {C : Set E} (hCu : C ⊆ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hCc : C ⊆ f ⁻¹' Ioi c₂) {T δ : ℝ} (hδ : δ ≤ 1)
    (hspan : ∀ s : EuclideanSpace ℝ ι, ‖s‖ < δ → ∀ x ∈ C,
      LinearMap.range (((ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ ι)).comp
          ((fderiv ℝ (perturbedFlow f h hf hh hc T) (x, s)).comp
            (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ ι)))) :
            EuclideanSpace ℝ ι →ₗ[ℝ] E) ⊔
        (ℝ ∙ ∇ (perturb f h s) (perturbedFlow f h hf hh hc T (x, s)).1) = ⊤)
    {e : OpenPartialHomeomorph E E} (he : ∀ z ∈ e.source, ContDiffAt ℝ (m + 1 : ℕ) e z)
    (hes : ∀ z ∈ e.target, ContDiffAt ℝ (m + 1 : ℕ) e.symm z)
    (heS : ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ↔
      e z ∈ hp.contDiffAt.unstableLinearSubspace) :
    ∀ᵐ s ∂ν, ‖s‖ < δ → ∀ ⦃K' : ℝ≥0⦄ (hf' : LipschitzWith K' (∇ (perturb f h s))),
      ∀ x ∈ C, x ∈ e.source → f (negativeGradientFlow (perturb f h s) hf' T x) < c₁ →
        negativeGradientFlow (perturb f h s) hf' T x ∈
          Flow.stableSet (negativeGradientFlow (perturb f h s) hf') q →
        Submodule.span ℝ (tangentConeAt ℝ
            (Flow.unstableSet (negativeGradientFlow (perturb f h s) hf') p)
            (negativeGradientFlow (perturb f h s) hf' T x)) ⊔
          Submodule.span ℝ (tangentConeAt ℝ
            (Flow.stableSet (negativeGradientFlow (perturb f h s) hf') q)
            (negativeGradientFlow (perturb f h s) hf' T x)) = ⊤ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hfs2 : ContDiff ℝ 2 f := hfs.of_le (by exact_mod_cast (by omega : 2 ≤ m + 2))
  have hm0 : ((m + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
  set Lu := hp.contDiffAt.unstableLinearSubspace
  set Ls := hq.contDiffAt.stableLinearSubspace
  set Φ := perturbedFlow f h hf hh hc
  set S := Flow.stableSet (negativeGradientFlow f hf) q
  -- The universal map: start on the unstable set of `p`, through the chart, and flow for time `T`.
  set G : Lu × EuclideanSpace ℝ ι → E := fun z ↦ (Φ T (e.symm (z.1 : E), z.2)).1
  set U : Set (Lu × EuclideanSpace ℝ ι) :=
    {z | (z.1 : E) ∈ e.target ∧ e.symm (z.1 : E) ∈ C ∧ ‖z.2‖ < δ ∧ f (G z) < c₁}
  have hΦ : ContDiff ℝ (m + 1 : ℕ) (Function.uncurry Φ) := by
    exact_mod_cast contDiff_perturbedFlow_of_contDiff m hfs hf hh hc hhs
  have hΦT : ContDiff ℝ (m + 1 : ℕ) (Φ T) :=
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  -- The derivative of `G` at `(v, s)`, through the chain rule.
  have hGd : ∀ z ∈ U, HasFDerivAt G ((ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ ι)).comp
      ((fderiv ℝ (Φ T) (e.symm (z.1 : E), z.2)).comp
        (((fderiv ℝ e.symm (z.1 : E)).comp (Lu.subtypeL.comp
          (ContinuousLinearMap.fst ℝ Lu (EuclideanSpace ℝ ι)))).prod
          (ContinuousLinearMap.snd ℝ Lu (EuclideanSpace ℝ ι))))) z := fun z hz ↦
    hasFDerivAt_fst_apply_symm ((hes _ hz.1).differentiableAt hm0)
      ((hΦT.differentiable hm0) _)
  have hGcont : ∀ z ∈ U, G z ∈ S → ContDiffAt ℝ (m + 1 : ℕ) G z := fun z hz _ ↦
    contDiffAt_fst.comp z (hΦT.contDiffAt.comp z (((hes _ hz.1).comp z
      (Lu.subtypeL.contDiff.contDiffAt.comp z contDiffAt_fst)).prodMk contDiffAt_snd))
  -- The stable set of `q` is flattened by `C^(m+1)` charts.
  have hchart : ∀ z ∈ U, G z ∈ S → ∃ e' : OpenPartialHomeomorph E E, G z ∈ e'.source ∧
      (∀ y ∈ e'.source, y ∈ S → ContDiffAt ℝ (m + 1 : ℕ) e' y) ∧
      (∀ y ∈ e'.source, y ∈ S → DifferentiableAt ℝ e'.symm (e' y)) ∧
      IsSliceChart e' (Ls : Set E) S := fun z _ hz ↦ by
    obtain ⟨e', hz', he', hes', hS'⟩ :=
      hq.exists_isSliceChart_stableSet (n := m + 1) (by omega) (by exact_mod_cast hfs) hf hz
    exact ⟨e', hz', fun y hy _ ↦ he' y hy, fun y hy _ ↦ hes' y hy, hS'⟩
  -- `G` is transverse to the stable set: its parameter derivative spans with the flow direction.
  have htotal : ∀ z ∈ U, G z ∈ S →
      LinearMap.range (fderiv ℝ G z : Lu × EuclideanSpace ℝ ι →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G z)) = ⊤ := by
    rintro ⟨v, s⟩ hz hGS
    obtain ⟨-, hxC, hs, hlt⟩ := id hz
    have hD : (fderiv ℝ G (v, s)).comp (ContinuousLinearMap.inr ℝ Lu (EuclideanSpace ℝ ι)) =
        (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ ι)).comp
          ((fderiv ℝ (Φ T) (e.symm (v : E), s)).comp
            (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ ι))) := by
      rw [(hGd _ hz).fderiv]
      ext w; simp
    refine eq_top_iff.2 ((range_sup_span_tangentConeAt_stableSet_eq_top hf hc₁ hlt hGS
      (hspan s hs _ hxC)).symm.le.trans (sup_le_sup_right ?_ _))
    rw [← hD]
    exact LinearMap.range_comp_le_range
      (ContinuousLinearMap.inr ℝ Lu (EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] Lu × EuclideanSpace ℝ ι)
      (fderiv ℝ G (v, s) : Lu × EuclideanSpace ℝ ι →ₗ[ℝ] E)
  have hn : ((finrank ℝ Lu - (finrank ℝ E - finrank ℝ Ls) + 1 : ℕ) : WithTop ℕ∞) ≤
      ((m + 1 : ℕ) : WithTop ℕ∞) := by
    rw [hp.finrank_unstableLinearSubspace_sub_codim_stableLinearSubspace hq]
    exact_mod_cast (by omega : morseIndex f p - morseIndex f q + 1 ≤ m + 1)
  have hae := ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top ν hGcont hchart htotal hn
  filter_upwards [hae] with s hs hsδ K' hf' x hxC hxe hlt hys
  -- Read the conclusion at `v = e x`.
  set φ := negativeGradientFlow (perturb f h s) hf'
  have hΦφ : ∀ x', (Φ T (x', s)).1 = φ T x' := fun x' ↦ by
    rw [perturbedFlow_apply_of_norm_le (hfs2.differentiable two_ne_zero) hf hh hc
      (hsδ.le.trans hδ) hf']
  set v : Lu := ⟨e x, (heS x hxe).1 (hCu hxC)⟩
  have hxv : e.symm (v : E) = x := e.left_inv hxe
  have hGv : G (v, s) = φ T x := by simp only [G, hxv, hΦφ]
  have hyS : φ T x ∈ S :=
    ((stableSet_perturb_inter_preimage_Iic hf hf' hc₁ q).subset ⟨hys, hlt.le⟩).1
  have hU : (v, s) ∈ U := ⟨e.map_source hxe, by rwa [hxv], hsδ, by rwa [hGv]⟩
  have key := hs v hU (hGv ▸ hyS)
  rw [hGv] at key
  refine eq_top_iff.2 (key.symm.le.trans (sup_le_sup ?_ ?_))
  · -- The derivative in `v` is the image under the flow of the tangent space of the unstable set.
    have hD : (fderiv ℝ G (v, s)).comp (ContinuousLinearMap.inl ℝ Lu (EuclideanSpace ℝ ι)) =
        (fderiv ℝ (φ T) x).comp ((fderiv ℝ e.symm (e x)).comp Lu.subtypeL) := by
      rw [(hGd _ hU).fderiv,
        fderiv_negativeGradientFlow_perturb hfs2 hf hh hc (hsδ.le.trans hδ) hf']
      ext w
      simp [hxv, v, Φ]
    rw [hD]
    exact range_fderiv_comp_le_span_tangentConeAt_unstableSet_perturb hfs2 hf hh hc₂
      (isSliceChart_iff.2 heS) hxe (hCu hxC) (hCc hxC) ((he x hxe).differentiableAt hm0)
      ((hes _ (e.map_source hxe)).differentiableAt hm0) s hf' T
  · rw [tangentConeAt_stableSet_perturb hf hf' hc₁ q hlt hfs2.continuous.continuousAt]

/-- **Transversality for one pair of critical points, for almost every small perturbation.** Let
`h` be a family of `C^(m+2)` functions with compact supports in the slab `c₁ < f < c₂`, `p` and `q`
nondegenerate critical points of a `C^(m+2)` function `f` with Lipschitz gradient, with
`ind p ≤ ind q + m`, and `C` a compact set of points of the unstable set of `p` above `c₂`. If, at
every `x ∈ C`, the derivative at the parameter `0` of `s ↦ φ^{f_s}_T x` spans `E` together with the
flow direction, then for almost every small parameter `s`, at every point `y = φ^{f_s}_T x` with
`x ∈ C` lying below `c₁` on a trajectory of `f_s` to `q`, the unstable set of `p` and the stable set
of `q` for `f_s` are transverse. -/
theorem exists_pos_ae_span_tangentConeAt_unstableSet_sup_span_tangentConeAt_stableSet_perturb_eq_top
    {m : ℕ}
    (hfs : ContDiff ℝ (m + 2) f) (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (hhs : ∀ i, ContDiff ℝ (m + 2) (h i)) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hm : morseIndex f p ≤ morseIndex f q + m) {c₁ c₂ : ℝ}
    (hc₁ : ∀ i, tsupport (h i) ⊆ f ⁻¹' Ioi c₁) (hc₂ : ∀ i, tsupport (h i) ⊆ f ⁻¹' Iio c₂)
    {C : Set E} (hC : IsCompact C) (hCu : C ⊆ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hCc : C ⊆ f ⁻¹' Ioi c₂) {T : ℝ}
    (hspan : ∀ x ∈ C,
      LinearMap.range (((ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ ι)).comp
          ((fderiv ℝ (perturbedFlow f h hf hh hc T) (x, 0)).comp
            (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ ι)))) :
            EuclideanSpace ℝ ι →ₗ[ℝ] E) ⊔
        (ℝ ∙ ∇ f (negativeGradientFlow f hf T x)) = ⊤) :
    ∃ δ > 0, ∀ᵐ s ∂ν, ‖s‖ < δ → ∀ ⦃K' : ℝ≥0⦄ (hf' : LipschitzWith K' (∇ (perturb f h s))),
      ∀ x ∈ C, f (negativeGradientFlow (perturb f h s) hf' T x) < c₁ →
        negativeGradientFlow (perturb f h s) hf' T x ∈
          Flow.stableSet (negativeGradientFlow (perturb f h s) hf') q →
        Submodule.span ℝ (tangentConeAt ℝ
            (Flow.unstableSet (negativeGradientFlow (perturb f h s) hf') p)
            (negativeGradientFlow (perturb f h s) hf' T x)) ⊔
          Submodule.span ℝ (tangentConeAt ℝ
            (Flow.stableSet (negativeGradientFlow (perturb f h s) hf') q)
            (negativeGradientFlow (perturb f h s) hf' T x)) = ⊤ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hfs2 : ContDiff ℝ 2 f := hfs.of_le (by exact_mod_cast (by omega : 2 ≤ m + 2))
  obtain ⟨δ₀, hδ₀, hδspan⟩ :=
    exists_pos_forall_range_fderiv_perturbedFlow_sup_span_eq_top hfs2 hf hh hc hC hspan
  have hfs' : ContDiff ℝ ((m + 1 : ℕ) + 1) f := by exact_mod_cast hfs
  -- Finitely many charts of the unstable set of `p` cover `C`.
  have key : ∀ x : C, ∃ e : OpenPartialHomeomorph E E, (x : E) ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ (m + 1 : ℕ) e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ (m + 1 : ℕ) e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ↔
        e z ∈ hp.contDiffAt.unstableLinearSubspace := fun x ↦
    hp.exists_unstableSet_chart hfs' hf (hCu x.2)
  choose e hxe he hes heS using key
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C ↦ (e x).source)
    (fun x ↦ (e x).open_source) fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxe _⟩
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  have hall := (Filter.eventually_all_finset t).2 fun i _ ↦
    ae_span_tangentConeAt_sup_span_tangentConeAt_perturb_eq_top_of_unstableSet_chart ν hfs hf
      hh hc hhs hp hq hm hc₁ hc₂ hCu hCc (min_le_right _ _)
      (fun s hs ↦ hδspan s (hs.trans_le (min_le_left _ _))) (he i) (hes i) (heS i)
  filter_upwards [hall] with s hs hsδ K' hf' x hx hlt hys
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  exact hs i hi hsδ hf' x hx hxi hlt hys

end TauCeti
