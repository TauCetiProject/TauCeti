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
(`TauCeti.exists_pos_ae_span_tangentConeAt_unstableSet_sup_stableSet_perturb_eq_top`).

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

* `TauCeti.exists_pos_ae_span_tangentConeAt_unstableSet_sup_stableSet_perturb_eq_top`: for almost
  every small parameter, the perturbed unstable set of `p` and stable set of `q` are transverse
  along the images of `C`.

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

/-- **Transversality in one chart of the unstable set.** The statement of
`TauCeti.exists_pos_ae_span_tangentConeAt_unstableSet_sup_stableSet_perturb_eq_top` for the points
of `C` in the source of one chart `e` flattening the unstable set of `p`, given the spanning
condition for all parameters of norm less than `δ ≤ 1`. -/
private theorem ae_span_tangentConeAt_unstableSet_sup_stableSet_perturb_eq_top_of_chart {m : ℕ}
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
          (ContinuousLinearMap.snd ℝ Lu (EuclideanSpace ℝ ι))))) z := fun z hz ↦ by
    have hψ : HasFDerivAt (fun z : Lu × EuclideanSpace ℝ ι ↦ (e.symm (z.1 : E), z.2))
        (((fderiv ℝ e.symm (z.1 : E)).comp (Lu.subtypeL.comp
          (ContinuousLinearMap.fst ℝ Lu (EuclideanSpace ℝ ι)))).prod
          (ContinuousLinearMap.snd ℝ Lu (EuclideanSpace ℝ ι))) z :=
      (((hes _ hz.1).differentiableAt hm0).hasFDerivAt.comp z
        (Lu.subtypeL.hasFDerivAt.comp z (hasFDerivAt_fst))).prodMk hasFDerivAt_snd
    exact hasFDerivAt_fst.comp z (((hΦT.differentiable hm0) _).hasFDerivAt.comp z hψ)
  have hGcont : ∀ z ∈ U, G z ∈ S → ContDiffAt ℝ (m + 1 : ℕ) G z := fun z hz _ ↦
    contDiffAt_fst.comp z (hΦT.contDiffAt.comp z (((hes _ hz.1).comp z
      (Lu.subtypeL.contDiff.contDiffAt.comp z contDiffAt_fst)).prodMk contDiffAt_snd))
  -- The stable set of `q` is flattened by `C^(m+1)` charts.
  have hfs' : ContDiff ℝ ((m + 1 : ℕ) + 1) f := by
    convert hfs using 1
    push_cast
    rw [add_assoc, one_add_one_eq_two]
  have hchart : ∀ z ∈ U, G z ∈ S → ∃ e' : OpenPartialHomeomorph E E, G z ∈ e'.source ∧
      (∀ y ∈ e'.source, y ∈ S → ContDiffAt ℝ (m + 1 : ℕ) e' y) ∧
      (∀ y ∈ e'.source, y ∈ S → DifferentiableAt ℝ e'.symm (e' y)) ∧
      IsSliceChart e' (Ls : Set E) S := fun z _ hz ↦ by
    obtain ⟨e', hz', he', hes', hS'⟩ := hq.exists_stableSet_chart hfs' hf hz
    exact ⟨e', hz', fun y hy _ ↦ he' y hy,
      fun y hy _ ↦ (hes' _ (e'.map_source hy)).differentiableAt hm0, isSliceChart_iff.2 hS'⟩
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
    have hnot : ∀ i, G (v, s) ∉ tsupport (h i) := fun i hi ↦ (hc₁ i hi).not_gt hlt
    have hgrad : ∇ (perturb f h s) (G (v, s)) = ∇ f (G (v, s)) :=
      gradient_perturb_of_forall_notMem_tsupport s hnot
    have hmem : ∇ f (G (v, s)) ∈ Submodule.span ℝ (tangentConeAt ℝ S (G (v, s))) := by
      have := Submodule.subset_span (R := ℝ) (neg_gradient_mem_tangentConeAt_of_isInvariant f hf
        (Flow.isInvariant_stableSet _ q) hGS)
      simpa using Submodule.neg_mem _ this
    rw [eq_top_iff, ← hspan s hs _ hxC]
    refine sup_le_sup ?_ ?_
    · rw [← hD]
      exact LinearMap.range_comp_le_range
        (ContinuousLinearMap.inr ℝ Lu (EuclideanSpace ℝ ι) :
          EuclideanSpace ℝ ι →ₗ[ℝ] Lu × EuclideanSpace ℝ ι)
        (fderiv ℝ G (v, s) : Lu × EuclideanSpace ℝ ι →ₗ[ℝ] E)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hgrad ▸ hmem
  have hn : ((finrank ℝ Lu - (finrank ℝ E - finrank ℝ Ls) + 1 : ℕ) : WithTop ℕ∞) ≤
      ((m + 1 : ℕ) : WithTop ℕ∞) := by
    have h₁ : finrank ℝ Lu = morseIndex f p := hp.contDiffAt.finrank_unstableLinearSubspace
    have h₂ : finrank ℝ Ls + morseIndex f q = finrank ℝ E :=
      hq.finrank_stableLinearSubspace_add_morseIndex
    have h₃ : finrank ℝ E - finrank ℝ Ls = morseIndex f q := by omega
    rw [h₃, h₁]
    exact_mod_cast (by omega : morseIndex f p - morseIndex f q + 1 ≤ m + 1)
  have hae := ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top ν hGcont hchart htotal hn
  filter_upwards [hae] with s hs hsδ K' hf' x hxC hxe hlt hys
  -- Read the conclusion at `v = e x`.
  set φ := negativeGradientFlow (perturb f h s) hf'
  have hφs : ContDiff ℝ 2 (perturb f h s) := contDiff_perturb hfs2 hh s
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
    obtain ⟨A, hA⟩ := e.exists_hasFDerivAt_of_chart hxe ((he x hxe).differentiableAt hm0)
      ((hes _ (e.map_source hxe)).differentiableAt hm0)
    have hAs : fderiv ℝ e.symm (v : E) = (A.symm : E →L[ℝ] E) :=
      (e.hasFDerivAt_symm (e.map_source hxe) (by rwa [e.left_inv hxe])).fderiv
    rw [Flow.span_tangentConeAt_apply (Flow.isInvariant_unstableSet _ p)
      (differentiable_negativeGradientFlow_apply _ hf' hφs (-T) _)
      (differentiable_negativeGradientFlow_apply _ hf' hφs T x),
      tangentConeAt_unstableSet_perturb hf hf' hc₂ p (hCc hxC) hfs2.continuous.continuousAt,
      (isSliceChart_iff.2 heS).span_tangentConeAt_eq_comap
        (Submodule.isClosed_of_finiteDimensional _) hxe (hCu hxC) hA,
      fderiv_negativeGradientFlow_perturb hfs2 hf hh hc (hsδ.le.trans hδ) hf']
    rintro _ ⟨w, rfl⟩
    refine ⟨A.symm (w : E), by simp, ?_⟩
    simp [(hGd _ hU).fderiv, hAs, hxv]
    rfl
  · rw [tangentConeAt_stableSet_perturb hf hf' hc₁ q hlt hfs2.continuous.continuousAt]

/-- **Transversality for one pair of critical points, for almost every small perturbation.** Let
`h` be a family of `C^(m+2)` functions with compact supports in the slab `c₁ < f < c₂`, `p` and `q`
nondegenerate critical points of a `C^(m+2)` function `f` with Lipschitz gradient, with
`ind p ≤ ind q + m`, and `C` a compact set of points of the unstable set of `p` above `c₂`. If, at
every `x ∈ C`, the derivative at the parameter `0` of `s ↦ φ^{f_s}_T x` spans `E` together with the
flow direction, then for almost every small parameter `s`, at every point `y = φ^{f_s}_T x` with
`x ∈ C` lying below `c₁` on a trajectory of `f_s` to `q`, the unstable set of `p` and the stable set
of `q` for `f_s` are transverse. -/
theorem exists_pos_ae_span_tangentConeAt_unstableSet_sup_stableSet_perturb_eq_top {m : ℕ}
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
  have hfs' : ContDiff ℝ ((m + 1 : ℕ) + 1) f := by
    convert hfs using 1
    push_cast
    rw [add_assoc, one_add_one_eq_two]
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
    ae_span_tangentConeAt_unstableSet_sup_stableSet_perturb_eq_top_of_chart ν hfs hf hh hc hhs hp hq
      hm hc₁ hc₂ hCu hCc (min_le_right _ _)
      (fun s hs ↦ hδspan s (hs.trans_le (min_le_left _ _))) (he i) (hes i) (heS i)
  filter_upwards [hall] with s hs hsδ K' hf' x hx hlt hys
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  exact hs i hi hsδ hf' x hx hxi hlt hys

end TauCeti
