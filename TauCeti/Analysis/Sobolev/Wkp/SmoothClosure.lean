/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.UniformSpace.UniformEmbedding
import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative
import TauCeti.Analysis.Sobolev.Wkp.LipschitzRepresentative
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Smooth Sobolev representatives on convex domain closures

A scalar function that belongs to every `L²` Sobolev order on a convex open set agrees almost
everywhere with a single function smooth on its closure. On each bounded convex patch,
Sobolev–Poincaré and Morrey embedding give uniformly continuous representatives of the
derivatives. Their extensions form a Taylor series on the closure of the patch.

## Main result

* `TauCeti.exists_contDiffOn_closure_ae_eq_of_forall_wkp` is the smooth representative on the
  closure of a convex domain.
-/

public section

open Bornology Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology

namespace TauCeti

private theorem exists_continuousOn_closure_eqOn {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    [CompleteSpace Y] [T2Space Y] {U : Set X} {f : X → Y}
    (hf : UniformContinuousOn f U) :
    ∃ g : X → Y, ContinuousOn g (closure U) ∧ EqOn g f U := by
  let i : U → closure U := Set.inclusion subset_closure
  have hi : IsUniformInducing i :=
    (isUniformInducing_val (closure U)).of_comp_iff.1 (isUniformInducing_val U)
  have hd : DenseRange i := (denseRange_inclusion_iff subset_closure).2 subset_rfl
  let g := (hi.isDenseInducing hd).extend (fun x : U ↦ f x)
  have hg : Continuous g :=
    (uniformContinuous_uniformly_extend hi hd (uniformContinuousOn_iff_restrict.1 hf)).continuous
  let G : X → Y := Function.extend (fun x : closure U ↦ (x : X)) g f
  have hG (x : closure U) : G x = g x := Subtype.val_injective.extend_apply g f x
  refine ⟨G, continuousOn_iff_continuous_domRestrict.2 (hg.congr fun x ↦ (hG x).symm), ?_⟩
  intro x hx
  rw [hG ⟨x, subset_closure hx⟩]
  exact (hi.isDenseInducing hd).extend_eq hf.restrict.continuous ⟨x, hx⟩

private theorem exists_contDiffOn_closure_eqOn_of_uniformContinuousOn_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    (hderiv : ∀ n, UniformContinuousOn (iteratedFDeriv ℝ n f) U) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g (closure U) ∧ EqOn g f U := by
  choose p hp hpeq using fun n ↦ exists_continuousOn_closure_eqOn (hderiv n)
  let g (x : E) := (p 0 x).curry0
  refine ⟨g, HasFTaylorSeriesUpToOn.contDiffOn (f' := fun x n ↦ p n x)
    ⟨fun _ _ ↦ rfl, ?_, fun n _ ↦ hp n⟩, ?_⟩
  · intro n _ x hx
    let d (y : E) := (p (n + 1) y).curryLeft
    have hd : ContinuousOn d (closure U) :=
      Continuous.comp_continuousOn
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F).continuous (hp (n + 1))
    have hp_diff (y : E) (hy : y ∈ U) : DifferentiableAt ℝ (p n) y :=
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv (m := n)
        (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top n))).congr_of_eventuallyEq
          ((hpeq n).eventuallyEq_of_mem (hU.mem_nhds hy))
    have hfd : EqOn (fderiv ℝ (p n)) d U := by
      intro y hy
      rw [((hpeq n).eventuallyEq_of_mem (hU.mem_nhds hy)).fderiv_eq,
        fderiv_iteratedFDeriv]
      simp only [d, Function.comp_apply, hpeq (n + 1) hy]
      rfl
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy ↦ (hp_diff y hy).differentiableWithinAt) hconv hU
      (fun y hy ↦ (hp n y hy).mono subset_closure)
      (((hd x hx).mono subset_closure).tendsto.congr'
        ((hfd.eventuallyEq_of_mem self_mem_nhdsWithin).symm))
  · intro x hx
    simp [g, hpeq 0 hx, iteratedFDeriv_zero_eq_comp]

section ConvexDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

private theorem exists_wkp_exponent_of_memLp {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hmem : ∀ w : W1p volume Ω p, MemLp (W1p.value w) q (volume.restrict (Ω : Set E))) :
    ∀ j (w : Wkp volume Ω p (j + 1)), ∃ v : Wkp volume Ω q j,
      Wkp.value j v =ᵐ[volume.restrict (Ω : Set E)] Wkp.value (j + 1) w
  | 0, w => by
    have h := hmem (w : W1p volume Ω p)
    refine ⟨h.toLp _, ?_⟩
    rw [Wkp.value_zero, Wkp.value_one]
    exact h.coeFn_toLp
  | j + 1, w => by
    have hm : MemLp (Wkp.value (j + 2) w) q (volume.restrict (Ω : Set E)) := by
      rw [← Wkp.value_firstOrder (j + 1) w]
      exact hmem (Wkp.firstOrder (j + 1) w)
    let b := stdOrthonormalBasis ℝ E
    obtain ⟨v, hv⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b (hm.toLp _) j
      fun i ↦ by
        obtain ⟨d, hd⟩ := exists_wkp_exponent_of_memLp hmem j (Wkp.lineDerivL (b i) (j + 1) w)
        exact ⟨d, (((Wkp.hasWeakLineDerivOn_lineDerivL (b i) (j + 1) w).congr_ae
          hm.coeFn_toLp.symm).congr_ae_deriv hd.symm)⟩
    exact ⟨v, by rw [hv]; exact hm.coeFn_toLp⟩

section PositiveDimension

variable [Nontrivial E]

private theorem memLp_w1p_value_of_subcritical_of_convex (hc : Convex ℝ (Ω : Set E))
    (hb : IsBounded (Ω : Set E)) {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0}
    (hpq : p ≤ q) (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹)
    (w : W1p volume Ω p) :
    MemLp (W1p.value w) q (volume.restrict (Ω : Set E)) := by
  have hp : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hpq
  let μ := (volume : Measure E).restrict (Ω : Set E)
  have hfin : (volume : Measure E) Ω ≠ ⊤ := hb.measure_lt_top.ne
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hfin
  by_cases h0 : (volume : Measure E) Ω = 0
  · have hzero (g : E → ℝ) : MemLp g q μ := by
      simp [μ, Measure.restrict_eq_zero.2 h0]
    exact hzero _
  let m : ℝ := ⨍ x in Ω, W1p.value w x
  have hmem : MemLp (fun x ↦ W1p.value w x - m) q μ := by
    apply memLp_iff.2
    refine (W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_of_convex hp hc hb
      subset_rfl h0 hpq rfl hδ w).trans_lt ?_
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top h0
      · exact ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.2 hδ.le) hfin
    · finiteness
  convert hmem.add (memLp_const m) using 1
  ext x
  exact (sub_add_cancel (W1p.value w x) m).symm

omit [Nontrivial E] in
private theorem memLp_w1p_value_top_of_convex (hc : Convex ℝ (Ω : Set E))
    (hb : IsBounded (Ω : Set E)) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : (finrank ℝ E : ℝ≥0∞) < q) (w : W1p volume Ω q) :
    MemLp (W1p.value w) ⊤ (volume.restrict (Ω : Set E)) := by
  obtain ⟨C, -, hC⟩ := W1p.exists_holderOnWith_closure_ae_eq_of_convex (μ := volume) hq hc hb
  obtain ⟨g, hg, hgv⟩ := hC w
  have hq₀ : q ≠ 0 := (zero_le.trans_lt hq).ne'
  have hlt : (finrank ℝ E : ℝ≥0∞) / q < 1 := by
    by_cases hqt : q = ⊤
    · simp [hqt]
    exact (ENNReal.div_lt_iff (.inl hq₀) (.inl hqt)).2 (by simpa only [one_mul] using hq)
  have hα : 0 < ((1 : ℝ≥0∞) - finrank ℝ E / q).toNNReal :=
    ENNReal.toNNReal_pos (tsub_pos_of_lt hlt).ne'
      ((tsub_le_self.trans_lt (by simp)).ne)
  exact ((hg.continuousOn hα).memLp_top_restrict_of_subset_isCompact
    hb.isCompact_closure Ω.isOpen.measurableSet subset_closure).ae_eq hgv.symm

private theorem exists_wkp_exponent_of_inv_add_eq (hc : Convex ℝ (Ω : Set E))
    (hb : IsBounded (Ω : Set E)) (j : ℕ)
    {t : ℝ≥0∞} (ht : t < (finrank ℝ E : ℝ≥0∞)⁻¹) :
    ∀ (k : ℕ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], q ≠ ⊤ →
      q⁻¹ + k * t = p⁻¹ → ∀ u : Wkp volume Ω p (j + k),
        ∃ v : Wkp volume Ω q j,
          Wkp.value j v =ᵐ[volume.restrict (Ω : Set E)] Wkp.value (j + k) u
  | 0, p, q, _, _, _, h, u => by
    have hqp : q = p := by simpa using h
    subst p
    exact ⟨u, .rfl⟩
  | k + 1, p, q, _, _, hq, h, u => by
    obtain ⟨r, hr, hrinv⟩ := exists_inv_eq_inv_add_of_ne_top hq (k * t)
    have hre : r⁻¹ + t = p⁻¹ := by
      rw [hrinv, ← h]
      push_cast
      ring
    have hr₁ : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hre⟩
    have hpr : p ≤ (r.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal hr, ← ENNReal.inv_le_inv, ← hre]
      exact le_self_add
    have ht₀ : t ≠ ⊤ := ht.ne_top
    have hri : r⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ((zero_lt_one.trans_le hr₁.out).ne')
    have hni : (finrank ℝ E : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    have htr : t.toReal < (finrank ℝ E : ℝ)⁻¹ := by
      simpa only [ENNReal.toReal_inv, ENNReal.toReal_natCast] using
        (ENNReal.toReal_lt_toReal ht₀ hni).2 ht
    have hδ : p.toReal⁻¹ - (r.toNNReal : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹ := by
      rw [← ENNReal.toReal_inv, ← hre, ENNReal.toReal_add hri ht₀,
        ENNReal.toReal_inv, ENNReal.coe_toNNReal_eq_toReal, add_sub_cancel_left]
      exact htr
    have hm (z : W1p volume Ω p) : MemLp (W1p.value z) r (volume.restrict (Ω : Set E)) :=
      (ENNReal.coe_toNNReal hr) ▸ memLp_w1p_value_of_subcritical_of_convex hc hb hpr hδ z
    obtain ⟨w, hw⟩ := exists_wkp_exponent_of_memLp hm (j + k) u
    obtain ⟨v, hv⟩ := exists_wkp_exponent_of_inv_add_eq hc hb j ht k hq hrinv.symm w
    exact ⟨v, hv.trans hw⟩

private theorem exists_contDiffOn_closure_ae_eq_of_forall_wkp_bounded
    (hb : IsBounded (Ω : Set E)) (hc : Convex ℝ (Ω : Set E)) {u : E → ℝ}
    (hu : ∀ m, ∃ w : Wkp volume Ω 2 m, Wkp.value m w =ᵐ[volume.restrict (Ω : Set E)] u) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (closure (Ω : Set E)) ∧
      u =ᵐ[volume.restrict (Ω : Set E)] g := by
  let n := finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  let q : ℝ≥0∞ := (n + 2 : ℕ)
  have hnq : (n : ℝ≥0∞) < q := by dsimp [q]; exact_mod_cast Nat.lt_add_of_pos_right (by decide)
  have hq₂ : (2 : ℝ≥0∞) ≤ q := by dsimp [q]; exact_mod_cast Nat.le_add_left 2 n
  have hq : Fact (1 ≤ q) := ⟨one_le_two.trans hq₂⟩
  have hqi : q⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 hq₂
  let t := ((2 : ℝ≥0∞)⁻¹ - q⁻¹) / n
  have hn₀ : (n : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
  have hnInf : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hn.ne')
  have ht : t < (n : ℝ≥0∞)⁻¹ := by
    change _ * (n : ℝ≥0∞)⁻¹ < _
    calc _ < 1 * (n : ℝ≥0∞)⁻¹ :=
          ENNReal.mul_lt_mul_left hn₀ hnInf (tsub_le_self.trans_lt (by norm_num))
      _ = _ := one_mul _
  have he : q⁻¹ + n * t = (2 : ℝ≥0∞)⁻¹ := by
    dsimp only [t]
    rw [ENNReal.mul_div_cancel (Nat.cast_ne_zero.2 hn.ne') (ENNReal.natCast_ne_top n),
      add_tsub_cancel_of_le hqi]
  obtain ⟨v, hv, huv⟩ := exists_contDiffOn_ae_eq_of_forall_wkp hu
  have hjets (j : ℕ) : UniformContinuousOn (iteratedFDeriv ℝ j v) Ω := by
    obtain ⟨w, hw⟩ := hu (j + 2 + n)
    obtain ⟨z, hz⟩ := exists_wkp_exponent_of_inv_add_eq hc hb (j + 2) ht n
      (ENNReal.natCast_ne_top _) he w
    obtain ⟨B, hB⟩ := exists_wkp_exponent_of_memLp
      (q := ⊤) (memLp_w1p_value_top_of_convex hc hb hnq) (j + 1) z
    obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex hc j
    obtain ⟨g, hg, hBg, hd⟩ := hK B
    have hvg : EqOn v g Ω := Measure.eqOn_open_of_ae_eq
      (huv.symm.trans ((hB.trans (hz.trans hw)).symm.trans hBg)) Ω.isOpen
      hv.continuousOn hg.continuousOn
    refine ((hd j le_rfl).2.uniformContinuousOn).congr ?_
    intro x hx
    exact ((hvg.eventuallyEq_of_mem (Ω.isOpen.mem_nhds hx)).iteratedFDeriv ℝ j).eq_of_nhds.symm
  obtain ⟨g, hg, hgv⟩ :=
    exists_contDiffOn_closure_eqOn_of_uniformContinuousOn_iteratedFDeriv Ω.isOpen hc hv hjets
  exact ⟨g, hg, huv.trans ((ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx ↦ (hgv hx).symm)⟩

end PositiveDimension

/-- A real-valued function in all Sobolev orders `W^{m,2}(Ω)` on a convex open set agrees
almost everywhere on `Ω` with a single function smooth on its closure. -/
theorem exists_contDiffOn_closure_ae_eq_of_forall_wkp
    (hc : Convex ℝ (Ω : Set E)) {u : E → ℝ}
    (hu : ∀ m, ∃ w : Wkp volume Ω 2 m, Wkp.value m w =ᵐ[volume.restrict (Ω : Set E)] u) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (closure (Ω : Set E)) ∧
      u =ᵐ[volume.restrict (Ω : Set E)] g := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨u, (contDiff_const (c := u 0)).contDiffOn.congr ?_, .rfl⟩
    exact fun x _ ↦ congrArg u (Subsingleton.elim x 0)
  let U (x : E) : Opens E := ⟨(Ω : Set E) ∩ ball x 1, Ω.isOpen.inter isOpen_ball⟩
  have hU (x : E) : U x ≤ Ω := fun _ hx ↦ hx.1
  have hlocal (x : E) := exists_contDiffOn_closure_ae_eq_of_forall_wkp_bounded
    (isBounded_ball.subset (inter_subset_right : (U x : Set E) ⊆ ball x 1))
    (hc.inter (convex_ball x 1)) (u := u) fun m ↦ by
      obtain ⟨w, hw⟩ := hu m
      exact ⟨Wkp.restrictL (hU x) m w, (Wkp.value_restrictL_ae (hU x) m w).trans
        (ae_restrict_of_ae_restrict_of_subset (hU x) hw)⟩
  choose f hf hfu using hlocal
  obtain ⟨v, hv, huv⟩ := exists_contDiffOn_ae_eq_of_forall_wkp hu
  have hev (x : E) : EqOn v (f x) (U x) := by
    have huv' : u =ᵐ[volume.restrict (U x : Set E)] v :=
      ae_restrict_of_ae_restrict_of_subset (hU x) huv
    exact Measure.eqOn_open_of_ae_eq (huv'.symm.trans (hfu x)) (U x).isOpen
      (hv.continuousOn.mono (hU x)) ((hf x).continuousOn.mono subset_closure)
  let g := extendFrom (Ω : Set E) v
  have hsub (x : E) : closure (Ω : Set E) ∩ ball x 1 ⊆ closure (U x : Set E) := by
    simpa only [U, Opens.coe_mk, inter_comm] using
      (isOpen_ball (x := x) (ε := 1)).inter_closure (t := (Ω : Set E))
  have hEq (x : E) : EqOn g (f x) (closure (Ω : Set E) ∩ ball x 1) := by
    intro y hy
    apply extendFrom_eq hy.1
    have hlim := ((hf x).continuousOn y (hsub x hy)).mono subset_closure
    have he : Tendsto v (𝓝[(U x : Set E)] y) (𝓝 (f x y)) :=
      hlim.tendsto.congr' ((hev x).eventuallyEq_of_mem self_mem_nhdsWithin).symm
    rw [show (U x : Set E) = (Ω : Set E) ∩ ball x 1 from rfl,
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hy.2))] at he
    exact he
  refine ⟨g, contDiffOn_of_locally_contDiffOn fun x _ ↦
    ⟨ball x 1, isOpen_ball, mem_ball_self zero_lt_one, ((hf x).mono (hsub x)).congr (hEq x)⟩, ?_⟩
  exact huv.trans ((ae_restrict_mem Ω.isOpen.measurableSet).mono
    fun x hx ↦ (extendFrom_extends hv.continuousOn x hx).symm)

end ConvexDomain

end TauCeti
