/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The degree formula for integrals

Let `E` be a finite-dimensional real inner product space and `f : E → E` a proper `C¹` map. For
every continuous compactly supported `g : E → F` with values in a real normed space,

`∫ det Df(x) • g (f x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the homological degree of `f` for any orientation of `E`, used on both source
and target (`TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_smul_integral`).
For a two-form `β = b dy₁ ∧ dy₂` on the plane the pullback is `f^* β = (b ∘ f) det Df dx₁ ∧ dx₂`, so
this is the classical formula `∫ f^* β = deg f ∫ β` for compactly supported top-degree forms, here
proved with the degree defined by local homology rather than by counting preimages of regular
values or by de Rham cohomology.

The proof has two halves. The first is the signed area formula with multiplicity
(`TauCeti.integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul`), valid for any
differentiable map with almost every fibre finite, any strongly measurable `g`, and integrable
`det Df • g ∘ f`:

`∫ det Df(x) • g (f x) dx = ∫ (N⁺(y) - N⁻(y)) • g(y) dy`,

where `N^±(y)` is the number of preimages of `y` at which `det Df` is positive, respectively
negative. It splits the regular set into the measurable sets where the Jacobian is positive and
negative, where the area formula with multiplicity
(`TauCeti.lintegral_normDet_fderiv_mul_eq_lintegral_tsum_of_injective_fderiv`) identifies the
pushforward of `|det Df| dx` with the counting density `N^±(y) dy`
(`TauCeti.map_withDensity_abs_det_fderiv_eq_withDensity_encard`). For a proper `C¹` map the
integrand is continuous with compact support, hence integrable. The second half is that
`N⁺(y) - N⁻(y) = deg f` at every regular value `y`
(`TauCeti.HomologicalOrientation.degree_eq_ncard_sub_ncard`), and that almost every point is a
regular value by Sard's theorem (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).

The formula also holds for a proper map `f : U → V` between open subsets of `E`, with `V`
preconnected, which agrees on `U` with a map `φ : E → E` that is `C¹` on `U`, and a continuous `g`
compactly supported in `V`:

`∫_U det Dφ(x) • g (φ x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the degree of `f` for the orientations of `U` and `V` restricted from that of `E`
(`TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_comap_smul_integral`).
For a proper `C¹` self-map `θ` of an open disc `D` in the plane this is `∫_D θ^* β = deg θ ∫_D β`
for compactly supported two-forms `β` on `D`. The proof is the same, applied to the parts of `U`
where the Jacobian is positive and negative, with the degree of `f` identified with the signed count
of a regular fibre by `TauCeti.HomologicalOrientation.degree_comap_eq_ncard_sub_ncard`.

## Main results

* `TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_smul_integral`: the
  degree formula.
* `TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_comap_smul_integral`:
  the degree formula for maps between open subsets.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
-/

public section

noncomputable section

open Set Function MeasureTheory Measure Module
open scoped ENNReal Topology

namespace TauCeti

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **The degree formula for integrals.** Let `o` be an orientation of the finite-dimensional real
inner product space `E`, and let `f : E → E` be a proper `C¹` map. For every continuous compactly
supported `g : E → F`,

`∫ det Df(x) • g (f x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the degree of `f` for the orientation `o` on both source and target. -/
theorem integral_det_fderiv_smul_comp_eq_degree_smul_integral (o : HomologicalOrientation E E n)
    (hE : finrank ℝ E = n) {f : C(E, E)} (hf : ContDiff ℝ 1 f) (hp : IsProperMap f) {g : E → F}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ x, (fderiv ℝ f x).det • g (f x) = o.degree o hE f • ∫ y, g y := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  -- The integrand is continuous with compact support, since `f` is proper.
  have hgf : HasCompactSupport (g ∘ f) :=
    IsCompact.of_isClosed_subset (hp.isCompact_preimage hgc) (isClosed_tsupport _)
      (closure_minimal (by rw [support_comp_eq_preimage]; exact preimage_mono (subset_tsupport g))
        ((isClosed_tsupport g).preimage f.continuous))
  have hint : Integrable fun x ↦ (fderiv ℝ f x).det • g (f x) :=
    ((ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv one_ne_zero)).smul
      (hg.comp f.continuous)).integrable_of_hasCompactSupport hgf.smul_left
  -- By Sard's theorem almost every point is a regular value.
  have hsard : ∀ᵐ y, ∀ x ∈ f ⁻¹' {y}, (fderiv ℝ f x).det ≠ 0 := by
    have h0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) (f := f)
      (s := {x | (fderiv ℝ f x).det = 0}) (fun x _ ↦ (hd x).hasFDerivAt.hasFDerivWithinAt)
      fun x hx ↦ hx
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy x hx hJx
    exact hy ⟨x, hJx, hx⟩
  -- The fibre over a regular value is finite, and its signed count is the degree.
  have hfin : ∀ᵐ y, (f ⁻¹' {y}).Finite := hsard.mono fun y hy ↦
    (hp.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt
      (fun x _ ↦ (hd x).hasFDerivAt) fun x hx ↦
        ⟨_, ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hy x hx)).antilipschitzWith⟩
  rw [integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul hd hfin
      hg.stronglyMeasurable hint, ← Int.cast_smul_eq_zsmul ℝ, ← integral_smul]
  refine integral_congr_ae (hsard.mono fun y hy ↦ ?_)
  simp [o.degree_eq_ncard_sub_ncard hE hp (fun x _ ↦ (hd x).hasFDerivAt) hy]

/-- **The degree formula for integrals over open subsets.** Let `o` be an orientation of the
finite-dimensional real inner product space `E`, let `U` and `V` be open subsets of `E`, oriented
by restricting `o`, with `V` preconnected, and let `f : U → V` be a proper map agreeing on `U`
with a map `φ : E → E` that is `C¹` on `U`. For every continuous compactly supported
`g : E → F` whose support lies in `V`,

`∫_U det Dφ(x) • g (φ x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the degree of `f : U → V`. For an open disc `U = V = D` in the plane and a two-form
`β = b dy₁ ∧ dy₂` compactly supported in `D`, this is `∫_D θ^* β = deg θ ∫_D β` for a proper `C¹`
self-map `θ` of `D`. -/
theorem integral_det_fderiv_smul_comp_eq_degree_comap_smul_integral
    (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n) {U V : TopologicalSpace.Opens E}
    [PreconnectedSpace V] {f : C(U, V)} (hp : IsProperMap f) {φ : E → E}
    (hφ : ∀ z : U, φ z = f z) (hφd : ContDiffOn ℝ 1 φ U) {g : E → F} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgV : tsupport g ⊆ V) :
    ∫ x in U, (fderiv ℝ φ x).det • g (φ x) =
      (o.comap U.isOpenEmbedding').degree (o.comap V.isOpenEmbedding') hE f • ∫ y, g y := by
  classical
  have hs : IsOpen (U : Set E) := U.isOpen
  have hd : ∀ x ∈ (U : Set E), HasFDerivAt φ (fderiv ℝ φ x) x := fun x hx ↦
    ((hφd.differentiableOn one_ne_zero x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt
  have hJ : ContinuousOn (fun x ↦ (fderiv ℝ φ x).det) U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hφd.continuousOn_fderiv_of_isOpen hs le_rfl)
  -- The integrand is continuous on `U` and vanishes on `U` off the compact set `f⁻¹(supp g)`.
  have hK : IsCompact (Subtype.val ⁻¹' tsupport g : Set V) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_of_subset fun y hy ↦ ⟨⟨y, hgV hy⟩, rfl⟩]
    exact hgc
  have hC : IsCompact (Subtype.val '' (f ⁻¹' (Subtype.val ⁻¹' tsupport g))) :=
    (hp.isCompact_preimage hK).image continuous_subtype_val
  have hCs : Subtype.val '' (f ⁻¹' (Subtype.val ⁻¹' tsupport g)) ⊆ U := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hint' : ∀ c : E → ℝ, ContinuousOn c U → IntegrableOn (fun x ↦ c x • g (φ x)) U :=
    fun c hc ↦ (((hc.smul (hg.comp_continuousOn hφd.continuousOn)).mono hCs).integrableOn_compact'
      hC hC.measurableSet).of_forall_sdiff_eq_zero hs.measurableSet fun x hx ↦ by
        by_cases hgx : g (φ x) = 0
        · simp [hgx]
        · refine absurd ⟨⟨x, hx.1⟩, ?_, rfl⟩ hx.2
          rw [mem_preimage, mem_preimage, ← hφ]
          exact subset_tsupport g hgx
  have hint := hint' _ hJ
  -- Split `U` into the open sets where the Jacobian is positive and negative.
  have hP : IsOpen ((U : Set E) ∩ {x | 0 < (fderiv ℝ φ x).det}) :=
    hJ.isOpen_inter_preimage hs isOpen_Ioi
  have hN : IsOpen ((U : Set E) ∩ {x | (fderiv ℝ φ x).det < 0}) :=
    hJ.isOpen_inter_preimage hs isOpen_Iio
  have hsplit : ∫ x in U, (fderiv ℝ φ x).det • g (φ x) =
      (∫ x in (U : Set E) ∩ {x | 0 < (fderiv ℝ φ x).det}, |(fderiv ℝ φ x).det| • g (φ x)) -
        ∫ x in (U : Set E) ∩ {x | (fderiv ℝ φ x).det < 0}, |(fderiv ℝ φ x).det| • g (φ x) := by
    have hdisj : Disjoint ((U : Set E) ∩ {x | 0 < (fderiv ℝ φ x).det})
        ((U : Set E) ∩ {x | (fderiv ℝ φ x).det < 0}) :=
      disjoint_left.2 fun x hxP hxN ↦ lt_asymm (a := 0) (b := (fderiv ℝ φ x).det) hxP.2 hxN.2
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hs.measurableSet
        (union_subset inter_subset_left inter_subset_left) fun x hx ↦ ?_,
      setIntegral_union hdisj hN.measurableSet
        (hint.mono_set inter_subset_left) (hint.mono_set inter_subset_left),
      sub_eq_add_neg, ← integral_neg]
    · congr 1
      · exact setIntegral_congr_fun hP.measurableSet fun x hx ↦ by
          simp only [abs_of_pos (a := (fderiv ℝ φ x).det) hx.2]
      · exact setIntegral_congr_fun hN.measurableSet fun x hx ↦ by
          simp only [abs_of_neg (a := (fderiv ℝ φ x).det) hx.2, neg_smul, neg_neg]
    · rcases lt_trichotomy (fderiv ℝ φ x).det 0 with h | h | h
      · exact absurd (Or.inr ⟨hx.1, h⟩) hx.2
      · simp [h]
      · exact absurd (Or.inl ⟨hx.1, h⟩) hx.2
  -- A measurable map agreeing with `φ` on `U`, to which the area formula applies.
  set ψ : E → E := (U : Set E).piecewise φ fun _ ↦ 0
  have hψm : Measurable ψ := hφd.continuousOn.measurable_piecewise continuousOn_const
    hs.measurableSet
  have hψφ : ∀ x ∈ (U : Set E), ψ =ᶠ[𝓝 x] φ := fun x hx ↦
    Filter.eventually_of_mem (hs.mem_nhds hx) fun z hz ↦ piecewise_eq_of_mem _ _ _ hz
  -- By Sard's theorem almost every point is a regular value of `φ` on `U`, and the fibres over
  -- regular values are finite.
  have hsard : ∀ᵐ y, ∀ x ∈ (U : Set E), φ x = y → (fderiv ℝ φ x).det ≠ 0 := by
    have h0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) (f := φ)
      (s := (U : Set E) ∩ {x | (fderiv ℝ φ x).det = 0})
      (fun x hx ↦ (hd x hx.1).hasFDerivWithinAt) fun x hx ↦ hx.2
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy x hx hxy hJx
    exact hy ⟨x, ⟨hx, hJx⟩, hxy⟩
  have hfib : ∀ y, (U : Set E) ∩ φ ⁻¹' {y} = Subtype.val '' (Subtype.val ∘ f ⁻¹' {y}) := by
    intro y
    ext w
    constructor
    · rintro ⟨hwU, hw⟩
      exact ⟨⟨w, hwU⟩, (hφ ⟨w, hwU⟩).symm.trans hw, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (hφ z).trans hz⟩
  have hfin : ∀ᵐ y, ((U : Set E) ∩ φ ⁻¹' {y}).Finite := hsard.mono fun y hy ↦ by
    refine (IsCompact.finite_inter_preimage_of_hasFDerivAt ?_ (fun x hx ↦ hd x hx.1) fun x hx ↦
      ⟨_, ((fderiv ℝ φ x).toContinuousLinearEquivOfDetNeZero
        (hy x hx.1 hx.2)).antilipschitzWith⟩)
    rw [hfib, preimage_comp]
    exact (hp.isCompact_preimage (Subtype.isCompact_iff.2
      ((finite_singleton y).subset (image_preimage_subset _ _)).isCompact)).image
        continuous_subtype_val
  -- The area formula with multiplicity on an open subset of `U` where the Jacobian does not
  -- vanish, applied to the measurable map `ψ`.
  have harea : ∀ S : Set E, IsOpen S → S ⊆ U → (∀ x ∈ S, (fderiv ℝ φ x).det ≠ 0) →
      (∫ x in S, |(fderiv ℝ φ x).det| • g (φ x)) =
        ∫ y, ((S ∩ φ ⁻¹' {y}).ncard : ℝ) • g y ∧
      Integrable fun y ↦ ((S ∩ φ ⁻¹' {y}).ncard : ℝ) • g y := by
    intro S hSo hSU hSJ
    have hψS : ∀ x ∈ S, fderiv ℝ ψ x = fderiv ℝ φ x ∧ ψ x = φ x := fun x hx ↦
      ⟨(hψφ x (hSU hx)).fderiv_eq, (hψφ x (hSU hx)).eq_of_nhds⟩
    have hfibS : ∀ y, S ∩ ψ ⁻¹' {y} = S ∩ φ ⁻¹' {y} := fun y ↦ by
      ext x
      exact and_congr_right fun hx ↦ by rw [mem_preimage, mem_preimage, (hψS x hx).2]
    have hdS : ∀ x ∈ S, DifferentiableAt ℝ ψ x := fun x hx ↦
      ((hd x (hSU hx)).congr_of_eventuallyEq (hψφ x (hSU hx))).differentiableAt
    have hJS : ∀ x ∈ S, (fderiv ℝ ψ x).det ≠ 0 := fun x hx ↦ (hψS x hx).1 ▸ hSJ x hx
    have hfinS : ∀ᵐ y, (S ∩ ψ ⁻¹' {y}).Finite := hfin.mono fun y hy ↦ by
      rw [hfibS]
      exact hy.subset (inter_subset_inter_left _ hSU)
    have hcongr : EqOn (fun x ↦ |(fderiv ℝ ψ x).det| • g (ψ x))
        (fun x ↦ |(fderiv ℝ φ x).det| • g (φ x)) S := fun x hx ↦ by
      simp only [(hψS x hx).1, (hψS x hx).2]
    have hintS : IntegrableOn (fun x ↦ |(fderiv ℝ ψ x).det| • g (ψ x)) S :=
      ((hint' _ (continuous_abs.comp_continuousOn hJ)).mono_set hSU).congr_fun hcongr.symm
        hSo.measurableSet
    simp only [← hfibS]
    exact ⟨(setIntegral_congr_fun hSo.measurableSet hcongr).symm.trans
        (setIntegral_abs_det_fderiv_smul_comp_eq_integral_ncard_smul hSo.measurableSet hψm hdS
          hJS hfinS hg.stronglyMeasurable),
      integrable_ncard_smul_of_integrableOn_abs_det_fderiv_smul hSo.measurableSet hψm hdS hJS
        hfinS hg.stronglyMeasurable hintS⟩
  obtain ⟨hPe, hPi⟩ := harea _ hP inter_subset_left fun x hx ↦ (hx.2 : 0 < (fderiv ℝ φ x).det).ne'
  obtain ⟨hNe, hNi⟩ := harea _ hN inter_subset_left fun x hx ↦ (hx.2 : (fderiv ℝ φ x).det < 0).ne
  rw [hsplit, hPe, hNe, ← integral_sub hPi hNi, ← Int.cast_smul_eq_zsmul ℝ, ← integral_smul]
  -- At a regular value in `V`, the signed count of the fibre is the degree.
  refine integral_congr_ae (hsard.mono fun y hy ↦ ?_)
  by_cases hgy : g y = 0
  · simp [hgy]
  have hyV : y ∈ (V : Set E) := hgV (subset_tsupport g hgy)
  rw [o.degree_comap_eq_ncard_sub_ncard hE hp hφ (f' := fderiv ℝ φ) (y := ⟨y, hyV⟩)
    (fun x _ ↦ hd x x.2) fun x hx ↦ hy x x.2 ((hφ x).trans (congrArg Subtype.val hx))]
  push_cast
  rw [sub_smul]

end HomologicalOrientation

end TauCeti
