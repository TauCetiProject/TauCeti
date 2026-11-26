/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.LittlewoodPaley
import TauCeti.Algebra.BigOperators.Finset.BoundedOverlap
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Projection
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.Analysis.Fourier.Torus.UnitCube
import TauCeti.MeasureTheory.Constructions.EuclideanSpace
import TauCeti.MeasureTheory.Function.Lp.SquareFunction
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# The Littlewood–Paley square function theorem on the torus

Let `φ` be a smooth bump function on `ℝᵈ` and let `Δⱼ` be the periodic Littlewood–Paley blocks on
the torus `𝕋ᵈ = UnitAddTorus d` built from it (`TauCeti.UnitAddTorus.littlewoodPaleyBlock`): the
Fourier multipliers with the symbols `n ↦ ψⱼ(n)` of the inhomogeneous Littlewood–Paley partition
`ψ₀ = φ, ψ₁, ψ₂, …`. The **square function** of `f ∈ L²(𝕋ᵈ)` is `S f = (∑ⱼ |Δⱼ f|²)^{1/2}`. For
`1 < p < ∞` there is a constant `C`, depending on `φ` and `p`, with

`‖S f‖_p ≤ C ‖f‖_p` and `‖f‖_p ≤ C ‖S f‖_p`

for every `f ∈ L²(𝕋ᵈ)`
(`TauCeti.UnitAddTorus.exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le` and
`TauCeti.UnitAddTorus.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow`).
Neither side is assumed finite, so `f ∈ Lᵖ(𝕋ᵈ)` exactly when `S f ∈ Lᵖ(𝕋ᵈ)`. This is the periodic
form of the Littlewood–Paley theorem on `ℝᵈ`
(`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le`); at `p = 2` it is the `L²`
square function `TauCeti.UnitAddTorus.hasSum_norm_sq_littlewoodPaleyBlock`.

## The argument

The first inequality is transferred from `ℝᵈ`. Read a trigonometric polynomial `g` on `ℝᵈ` as the
periodic function `G = g ∘ π`, `π : ℝᵈ → 𝕋ᵈ` the projection (`TauCeti.UnitAddTorus.proj`). The
block `Δⱼ g` lifts to the convolution `𝓕⁻ ψⱼ ⋆ G` on `ℝᵈ`, since
`∫ 𝓕⁻ ψⱼ (v - y) eₙ(y) dy = ψⱼ(n) eₙ(v)` on every Fourier mode. Measure the square function
on the unit cube `[0, 1]ᵈ`, which carries the measure of the torus, and split `G` into its part `h`
in the box `(-1, 2]ᵈ` and the rest.

* The part `h` lies in `L²(ℝᵈ)`, and its square function on `ℝᵈ` is bounded by `C ‖h‖_p` by the
  theorem on `ℝᵈ`; the box is covered by `3ᵈ` translates of the cube, so `‖h‖_p ≤ 3^{d/p} ‖g‖_p`.
* The rest vanishes at distance less than one from the cube, so on the cube it only meets the tails
  `1_{‖z‖ ≥ 1} |𝓕⁻ ψⱼ(z)|` of the kernels. These sum, over all `j`, to an integrable function `κ`,
  since the first moments of the kernels are `O(2^{-j})`; bounding the `ℓ²` sum by the `ℓ¹` sum,
  their contribution is at most `∫ κ(z) |G(· - z)| dz`, whose `Lᵖ` norm on the cube is at most
  `‖κ‖₁ ‖g‖_p` by Minkowski's integral inequality and periodicity.

A general `f ∈ L²(𝕋ᵈ)` has, for each `N`, the same blocks `Δⱼ`, `j < N`, as one of its low-pass
truncations, which are trigonometric polynomials bounded on `Lᵖ` uniformly in the truncation
(`TauCeti.UnitAddTorus.eLpNorm_sum_littlewoodPaleyBlock_range_le`); the square sums over `j < N`
increase to the full square function.

The reverse inequality follows from the first one at the conjugate exponent by the duality
argument shared with `ℝᵈ` (`TauCeti.eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow_of_card_le`): the
blocks are self-adjoint (`TauCeti.UnitAddTorus.isSelfAdjoint_littlewoodPaleyBlock`), `Δⱼ Δₖ = 0`
for `|j - k|` large (`TauCeti.UnitAddTorus.exists_littlewoodPaleyBlock_comp_eq_zero`), and their
partial sums converge to the identity (`TauCeti.UnitAddTorus.tendsto_sum_littlewoodPaleyBlock`).

As for the blocks, `Lᵖ(𝕋ᵈ)` is taken for the product of the Haar probability measures on the
circle factors.

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Theorem 6.1.2 (the Littlewood–Paley theorem) and Section 4.3 (multipliers on
  the torus and transference from `ℝⁿ`).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter VII,
  Section 3 (transference of multipliers from `ℝⁿ` to the torus).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal FourierTransform InnerProductSpace RealInnerProductSpace SchwartzMap

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*}

-- The periodic Littlewood–Paley blocks live on `L²` for the product of the Haar probability
-- measures on the circle factors, given by this instance; use it here so that the square function
-- is measured on that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

-- The two facts about this measure that Mathlib records with file-local instances: it is a Haar
-- measure and a probability measure.
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Periodic functions on `ℝᵈ`, the unit cube and the box `(-1, 2]ᵈ` -/

/-- The lift `𝕋ᵈ → (0, 1]ᵈ ⊆ ℝᵈ`. -/
private def _root_.UnitAddTorus.lift (t : UnitAddTorus d) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 ((measurableEquivPiIoc 0 t : _) : d → ℝ)

private theorem _root_.UnitAddTorus.proj_lift (t : UnitAddTorus d) : proj (lift t) = t := by
  ext i
  simp [UnitAddTorus.lift]

/-- The closed unit cube `[0, 1]ᵈ` of `ℝᵈ`. -/
private def cube : Set (EuclideanSpace ℝ d) := {v | ∀ i, v i ∈ Icc (0 : ℝ) 1}

private theorem _root_.UnitAddTorus.lift_mem_cube (t : UnitAddTorus d) : lift t ∈ cube := by
  intro i
  have h := (measurableEquivPiIoc 0 t).property i
  simp only [Pi.zero_apply, zero_add] at h
  exact Ioc_subset_Icc_self h

/-- The box `(-1, 2]ᵈ`, which contains the points at distance less than one from the unit cube. -/
private def box : Set (EuclideanSpace ℝ d) := {v | ∀ i, v i ∈ Ioc (-1 : ℝ) 2}

/-- The box is covered by the `3ᵈ` translates of the unit cube by the integer vectors with
coordinates in `{-1, 0, 1}`. -/
private theorem exists_sub_latticePoint_mem_cube {y : EuclideanSpace ℝ d} (hy : y ∈ box) :
    ∃ ℓ : d → ℤ, (∀ i, ℓ i ∈ ({-1, 0, 1} : Finset ℤ)) ∧ y - latticePoint ℓ ∈ cube := by
  refine ⟨fun i ↦ ⌈y i⌉ - 1, fun i ↦ ?_, fun i ↦ ?_⟩
  · have hc₁ : 0 ≤ ⌈y i⌉ := Int.ceil_nonneg_of_neg_one_lt (hy i).1
    have hc₂ : ⌈y i⌉ ≤ 2 := Int.ceil_le.2 (by exact_mod_cast (hy i).2)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · simp only [PiLp.sub_apply, latticePoint_apply, Int.cast_sub, Int.cast_one, mem_Icc]
    constructor
    · linarith [Int.ceil_lt_add_one (y i)]
    · linarith [Int.le_ceil (y i)]

variable [Fintype d]

/-- A point of the cube and a point outside the box are at distance at least one. -/
private theorem one_le_norm_sub_of_mem_cube_of_notMem_box {w y : EuclideanSpace ℝ d}
    (hw : w ∈ cube) (hy : y ∉ box) : 1 ≤ ‖w - y‖ := by
  simp only [box, mem_ofPred_eq, not_forall, mem_Ioc, not_and_or, not_lt, not_le] at hy
  obtain ⟨i, hi⟩ := hy
  refine le_trans ?_ (PiLp.norm_apply_le (w - y) i)
  rw [PiLp.sub_apply, Real.norm_eq_abs]
  rcases hi with hi | hi
  · exact (by linarith [(hw i).1] : (1 : ℝ) ≤ w i - y i).trans (le_abs_self _)
  · exact (by linarith [(hw i).2] : (1 : ℝ) ≤ -(w i - y i)).trans (neg_le_abs _)

omit [Fintype d] in
private theorem measurableSet_cube [Countable d] : MeasurableSet (cube (d := d)) :=
  EuclideanSpace.measurableSet_setOf_forall_mem fun _ ↦ measurableSet_Icc

omit [Fintype d] in
private theorem measurableSet_box [Countable d] : MeasurableSet (box (d := d)) :=
  EuclideanSpace.measurableSet_setOf_forall_mem fun _ ↦ measurableSet_Ioc

/-- The part in the box of a bounded continuous function on `ℝᵈ` is in `L²(ℝᵈ)`. -/
private theorem memLp_box_indicator {G : EuclideanSpace ℝ d → ℂ} (hG : Continuous G) {M : ℝ}
    (hGM : ∀ y, ‖G y‖ ≤ M) : MemLp (box.indicator G) 2 volume := by
  refine (memLp_indicator_iff_restrict measurableSet_box.nullMeasurableSet).2 ?_
  have hb : Bornology.IsBounded (box (d := d)) :=
    ((isCompact_univ_pi fun _ : d ↦ isCompact_Icc (a := (-1 : ℝ)) (b := 2)).image
      (PiLp.continuous_toLp 2 _)).isBounded.subset fun v hv ↦
        ⟨WithLp.ofLp v, fun i _ ↦ Ioc_subset_Icc_self (hv i), rfl⟩
  have : IsFiniteMeasure (volume.restrict (box (d := d))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  exact MemLp.of_bound hG.aestronglyMeasurable _ (.of_forall hGM)

omit [Fintype d] in
private theorem measurableEmbedding_lift [Countable d] : MeasurableEmbedding (lift (d := d)) :=
  (MeasurableEquiv.toLp 2 (d → ℝ)).measurableEmbedding.comp
    measurableEmbedding_coe_measurableEquivPiIoc

/-- The lift preserves measure onto the unit cube. -/
private theorem measurePreserving_lift :
    MeasurePreserving (lift (d := d)) volume (volume.restrict cube) := by
  have h := (PiLp.volume_preserving_toLp d).restrict_preimage (s := cube) measurableSet_cube
  have hpre : (WithLp.toLp 2 : (d → ℝ) → EuclideanSpace ℝ d) ⁻¹' cube =
      univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_preimage, mem_univ_pi]
  rw [hpre] at h
  exact h.comp measurePreserving_coe_measurableEquivPiIoc

/-- Lifting to the unit cube does not increase `Lᵖ` norms. -/
private theorem eLpNorm_comp_lift_le {F : EuclideanSpace ℝ d → ℝ≥0∞} (hF : AEMeasurable F)
    (p : ℝ≥0∞) : eLpNorm (fun t ↦ F (lift t)) p volume ≤ eLpNorm F p volume :=
  (eLpNorm_comp_measurePreserving hF.restrict.aestronglyMeasurable measurePreserving_lift).trans_le
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- A periodic function integrates over every translate of the unit cube to its integral over the
torus. -/
private theorem setLIntegral_cube_comp_proj_add (H : UnitAddTorus d → ℝ≥0∞)
    (z : EuclideanSpace ℝ d) : ∫⁻ w in cube, H (proj (w + z)) = ∫⁻ t, H t := by
  rw [← measurePreserving_lift.lintegral_comp_emb measurableEmbedding_lift]
  simp_rw [proj_add, proj_lift]
  exact lintegral_add_right_eq_self H (proj z)

/-- A periodic function integrates over the box to at most `3ᵈ` times its integral over the
torus. -/
private theorem setLIntegral_box_comp_proj_le (H : UnitAddTorus d → ℝ≥0∞) :
    ∫⁻ y in box, H (proj y) ≤ 3 ^ Fintype.card d * ∫⁻ t, H t := by
  classical
  set S := Fintype.piFinset fun _ : d ↦ ({-1, 0, 1} : Finset ℤ)
  have hcover : box ⊆ ⋃ ℓ : S, (fun y ↦ y - latticePoint (ℓ : d → ℤ)) ⁻¹' cube := fun y hy ↦ by
    obtain ⟨ℓ, hℓ, h⟩ := exists_sub_latticePoint_mem_cube hy
    exact mem_iUnion.2 ⟨⟨ℓ, Fintype.mem_piFinset.2 hℓ⟩, h⟩
  have htrans (ℓ : d → ℤ) : ∫⁻ y in (fun y ↦ y - latticePoint ℓ) ⁻¹' cube, H (proj y) =
      ∫⁻ t, H t := by
    have h := (measurePreserving_sub_right volume (latticePoint ℓ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.subRight (latticePoint ℓ)).measurableEmbedding
      (fun w ↦ H (proj (w + latticePoint ℓ))) cube
    simp only [sub_add_cancel] at h
    rw [h, setLIntegral_cube_comp_proj_add]
  have hcard : (S.card : ℝ≥0∞) = 3 ^ Fintype.card d := by
    simp [S, Fintype.card_piFinset, Finset.prod_const]
  calc ∫⁻ y in box, H (proj y)
      ≤ ∫⁻ y in ⋃ ℓ : S, (fun y ↦ y - latticePoint (ℓ : d → ℤ)) ⁻¹' cube, H (proj y) :=
        lintegral_mono_set hcover
    _ ≤ ∑' ℓ : S, ∫⁻ y in (fun y ↦ y - latticePoint (ℓ : d → ℤ)) ⁻¹' cube, H (proj y) :=
        lintegral_iUnion_le _ _
    _ = ∑ ℓ ∈ S, ∫⁻ t, H t := by
        rw [Finset.tsum_subtype S fun ℓ ↦
          ∫⁻ y in (fun y ↦ y - latticePoint ℓ) ⁻¹' cube, H (proj y)]
        exact Finset.sum_congr rfl fun ℓ _ ↦ htrans ℓ
    _ = 3 ^ Fintype.card d * ∫⁻ t, H t := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- The `Lᵖ(ℝᵈ)` norm of the part in the box `(-1, 2]ᵈ` of the lift of a function `F` on the torus
is at most `3^{d/p}` times its `Lᵖ(𝕋ᵈ)` norm. -/
private theorem eLpNorm_box_indicator_comp_proj_le {F : UnitAddTorus d → ℂ} (hF : Continuous F)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (box.indicator fun y ↦ F (proj y)) p volume ≤
      (3 ^ Fintype.card d) ^ (1 / p.toReal) * eLpNorm F p volume := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_box.nullMeasurableSet,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top (f := fun y ↦ F (proj y))
      (hF.comp continuous_proj).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hF.aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  gcongr
  exact setLIntegral_box_comp_proj_le fun t ↦ ‖F t‖ₑ ^ p.toReal

/-- **Minkowski's inequality for a convolution with a periodic function.** Read at the lifted
points of the torus, `∫ κ(z) |F(· - z)| dz` has `Lᵖ(𝕋ᵈ)` norm at most `‖κ‖₁ ‖F‖_p`. -/
private theorem eLpNorm_lintegral_mul_comp_proj_lift_sub_le {κ : EuclideanSpace ℝ d → ℝ≥0∞}
    (hκ : Measurable κ) {F : UnitAddTorus d → ℂ} (hF : Continuous F) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ∞) :
    eLpNorm (fun t ↦ ∫⁻ z, κ z * ‖F (proj (lift t - z))‖ₑ) p volume ≤
      (∫⁻ z, κ z) * eLpNorm F p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  have hq0 : 0 < p.toReal := zero_lt_one.trans_le hq
  have hf : Measurable (Function.uncurry fun w z ↦ κ z * ‖F (proj (w - z))‖ₑ) :=
    (hκ.comp measurable_snd).mul (hF.eNorm.measurable.comp
      (continuous_proj.measurable.comp (measurable_fst.sub measurable_snd)))
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top
      (f := fun t ↦ ∫⁻ z, κ z * ‖F (proj (lift t - z))‖ₑ)
      ((Measurable.lintegral_prod_right' hf).comp
        measurableEmbedding_lift.measurable).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hF.aestronglyMeasurable]
  simp only [eNorm_eq_self]
  rw [measurePreserving_lift.lintegral_comp_emb measurableEmbedding_lift
    (fun w ↦ (∫⁻ z, κ z * ‖F (proj (w - z))‖ₑ) ^ p.toReal)]
  refine (lintegral_Lp_lintegral_le hf.aemeasurable hq).trans (le_of_eq ?_)
  rw [← lintegral_mul_const _ hκ]
  refine lintegral_congr fun z ↦ ?_
  have hHz : Measurable fun w ↦ ‖F (proj (w - z))‖ₑ ^ p.toReal :=
    (hF.eNorm.measurable.comp (continuous_proj.measurable.comp
      (measurable_id.sub_const z))).pow_const _
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
  rw [lintegral_const_mul _ hHz, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div,
    ENNReal.rpow_rpow_inv hq0.ne']
  congr 2
  simpa only [sub_eq_add_neg] using
    setLIntegral_cube_comp_proj_add (fun t ↦ ‖F t‖ₑ ^ p.toReal) (-z)

/-! ### Kernels on plane waves and trigonometric polynomials -/

/-- The kernel of the Fourier multiplier with a Schwartz symbol `σ` acts on the lift of a
trigonometric polynomial by multiplying its coefficients by `σ`. -/
private theorem integral_fourierInv_sub_mul_sum_mFourier (σ : 𝓢(EuclideanSpace ℝ d, ℂ))
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (w : EuclideanSpace ℝ d) :
    ∫ y, 𝓕⁻ σ (w - y) * ∑ n ∈ s, mFourier n (proj y) • c n =
      ∑ n ∈ s, mFourier n (proj w) • (σ (latticePoint n) * c n) := by
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun n _ ↦ ?_]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    have h (y : EuclideanSpace ℝ d) : 𝓕⁻ σ (w - y) * (mFourier n (proj y) * c n) =
        c n * (𝓕⁻ σ (w - y) * mFourier n (proj y)) := by ring
    simp_rw [h, integral_const_mul, mFourier_proj, σ.integral_fourierInv_sub_mul_fourierChar]
    ring
  · exact ((𝓕⁻ σ).integrable.comp_sub_left w).mul_bdd (c := ‖c n‖)
      (((mFourier n).continuous.comp continuous_proj).mul continuous_const).aestronglyMeasurable
      (.of_forall fun y ↦ by simp [norm_mFourier_apply])

/-! ### The square function of a trigonometric polynomial -/

/-- The blocks of a trigonometric polynomial `g`, read at the lifted points of the torus, are the
convolutions of its periodic lift with the kernels `𝓕⁻ ψⱼ`. -/
private theorem ae_littlewoodPaleyBlock_eq_integral (φ : ContDiffBump (0 : EuclideanSpace ℝ d))
    {s : Finset (d → ℤ)} {g : L²(UnitAddTorus d)} (hs : ∀ n ∉ s, mFourierCoeff g n = 0) :
    ∀ᵐ t, ∀ j, littlewoodPaleyBlock φ j g t =
      ∫ y, 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (lift t - y) *
        ∑ n ∈ s, mFourier n (proj y) • mFourierCoeff g n := by
  rw [ae_all_iff]
  intro j
  have hs' : ∀ n ∉ s, mFourierCoeff (littlewoodPaleyBlock φ j g) n = 0 := fun n hn ↦ by
    simp [hs n hn]
  filter_upwards [coeFn_ae_eq_sum_mFourier_smul_mFourierCoeff hs'] with t ht
  rw [ht, integral_fourierInv_sub_mul_sum_mFourier, proj_lift]
  simp

/-- The Fourier multipliers with Schwartz symbols `σ j` of an `L²(ℝᵈ)` function `h`, read at the
lifted points of the torus, are the convolutions of `h` with the kernels `𝓕⁻ (σ j)`. -/
private theorem ae_fourierMultiplierCLM_lift_eq_integral (σ : ℕ → 𝓢(EuclideanSpace ℝ d, ℂ))
    {h : EuclideanSpace ℝ d → ℂ} (hh : MemLp h 2 volume) :
    ∀ᵐ t : UnitAddTorus d, ∀ j, Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞) (hh.toLp h) (lift t) =
      ∫ y, 𝓕⁻ (σ j) (lift t - y) * h y := by
  have hV : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ d)), ∀ j,
      Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞) (hh.toLp h) w = ∫ y, 𝓕⁻ (σ j) (w - y) * h y := by
    rw [ae_all_iff]
    intro j
    filter_upwards [(σ j).coeFn_fourierMultiplierCLM_toLp (hh.toLp h)] with w hw
    rw [hw]
    exact integral_congr_ae (hh.coeFn_toLp.mono fun y hy ↦ by simp [hy])
  exact measurePreserving_lift.quasiMeasurePreserving.ae (ae_restrict_of_ae hV)

/-- The tail `1_{‖z‖ ≥ 1} |𝓕⁻ σ (z)|` of the kernel of the Fourier multiplier with symbol `σ`. -/
private def kernelTail (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) : EuclideanSpace ℝ d → ℝ≥0∞ :=
  {z | 1 ≤ ‖z‖}.indicator fun z ↦ ‖𝓕⁻ σ z‖ₑ

private theorem measurable_kernelTail (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    Measurable (kernelTail σ) :=
  (𝓕⁻ σ).continuous.eNorm.measurable.indicator (measurableSet_le measurable_const measurable_norm)

/-- On the unit cube, the convolution of `𝓕⁻ σ` with a bounded continuous `G` differs from the
convolution with its part in the box `(-1, 2]ᵈ` by at most the convolution of `|G|` with the tail
`1_{‖z‖ ≥ 1} |𝓕⁻ σ (z)|` of the kernel. -/
private theorem eNorm_integral_fourierInv_sub_mul_le (σ : 𝓢(EuclideanSpace ℝ d, ℂ))
    {G : EuclideanSpace ℝ d → ℂ} (hG : Continuous G) {M : ℝ} (hGM : ∀ y, ‖G y‖ ≤ M)
    {w : EuclideanSpace ℝ d} (hw : w ∈ cube) :
    ‖∫ y, 𝓕⁻ σ (w - y) * G y‖ₑ ≤ ‖∫ y, 𝓕⁻ σ (w - y) * box.indicator G y‖ₑ +
      ∫⁻ y, kernelTail σ (w - y) * ‖G y‖ₑ := by
  have hbound (S : Set (EuclideanSpace ℝ d)) (y : EuclideanSpace ℝ d) : ‖S.indicator G y‖ ≤ M :=
    (norm_indicator_le_norm_self _ _).trans (hGM y)
  have hsplit : ∫ y, 𝓕⁻ σ (w - y) * G y = (∫ y, 𝓕⁻ σ (w - y) * box.indicator G y) +
      ∫ y, 𝓕⁻ σ (w - y) * boxᶜ.indicator G y := by
    have hk := ((𝓕⁻ σ).integrable (μ := volume)).comp_sub_left w
    refine Eq.trans ?_ (integral_add
      (hk.mul_bdd (hG.aestronglyMeasurable.indicator measurableSet_box) (.of_forall (hbound box)))
      (hk.mul_bdd (hG.aestronglyMeasurable.indicator measurableSet_box.compl)
        (.of_forall (hbound boxᶜ))))
    congr with y
    rw [← mul_add, indicator_self_add_compl_apply]
  rw [hsplit]
  refine (eNorm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun y ↦ ?_)
  by_cases hy : y ∈ box
  · simp [hy]
  · have h1 : w - y ∈ {z : EuclideanSpace ℝ d | 1 ≤ ‖z‖} :=
      one_le_norm_sub_of_mem_cube_of_notMem_box hw hy
    rw [indicator_of_mem (mem_compl hy), eNorm_mul, kernelTail, indicator_of_mem h1]

/-- The tails `1_{‖z‖ ≥ 1} |𝓕⁻ ψⱼ (z)|` of the kernels of the Littlewood–Paley blocks have finite
total integral: the first moments of the kernels are `O(2^{-j})`. -/
private theorem lintegral_tsum_kernelTail_ne_top (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) :
    ∫⁻ z, ∑' j, kernelTail (φ.inhomogeneousLittlewoodPaleySchwartz j) z ≠ ∞ := by
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 1
  rw [lintegral_tsum fun j ↦ (measurable_kernelTail _).aemeasurable]
  refine ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j * C) ?_
    (tsum_le_tsum fun j ↦ ?_)
  · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
  set k := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hk : ⇑k = 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
    rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  calc ∫⁻ z, kernelTail (φ.inhomogeneousLittlewoodPaleySchwartz j) z
      ≤ ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 1 * ‖k z‖) := lintegral_mono fun z ↦ by
        rw [kernelTail]
        by_cases hz : 1 ≤ ‖z‖
        · rw [indicator_of_mem hz, pow_one, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
            ofReal_norm]
          refine le_mul_of_one_le_left zero_le ?_
          rw [← ofReal_norm]
          exact ENNReal.one_le_ofReal.2 hz
        · rw [indicator_of_notMem hz]
          exact zero_le
    _ = ENNReal.ofReal (∫ z, ‖z‖ ^ 1 * ‖k z‖) :=
        (ofReal_integral_eq_lintegral_ofReal (k.integrable_pow_mul volume 1)
          (.of_forall fun z ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal (((2 ^ j) ^ 1)⁻¹ * C) := by
        rw [hk]
        exact ENNReal.ofReal_le_ofReal (hC j)
    _ = (2⁻¹ : ℝ≥0∞) ^ j * C := by
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_inv_of_pos, ENNReal.inv_pow]

/-- Pointwise on the torus, the square function of `g` is at most the square function on `ℝᵈ` of
the part in the box `(-1, 2]ᵈ` of the periodic lift of a bounded continuous `F`, plus the
convolution of the lift with the sum `κ` of the tails `1_{‖z‖ ≥ 1} |𝓕⁻ ψⱼ (z)|` of the kernels,
provided the blocks of `g` are the convolutions of the lift of `F` with the kernels `𝓕⁻ ψⱼ`. -/
private theorem ae_rpow_sum_sq_littlewoodPaleyBlock_le
    (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) {g : L²(UnitAddTorus d)}
    {F : UnitAddTorus d → ℂ} (hF : Continuous F) {M : ℝ} (hFM : ∀ t, ‖F t‖ ≤ M)
    (hgF : ∀ᵐ t, ∀ j, littlewoodPaleyBlock φ j g t =
      ∫ y, 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (lift t - y) * F (proj y))
    (hmem : MemLp (box.indicator fun y ↦ F (proj y)) 2 volume) (u : Finset ℕ) :
    ∀ᵐ t, (∑ j ∈ u, ‖littlewoodPaleyBlock φ j g t‖ₑ ^ 2) ^ (2⁻¹ : ℝ) ≤
      (∑' j, ‖Lp.fourierMultiplierCLM ℂ ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞)
        (hmem.toLp _) (lift t)‖ₑ ^ 2) ^ (2⁻¹ : ℝ) +
      ∫⁻ z, (∑' j, kernelTail (φ.inhomogeneousLittlewoodPaleySchwartz j) z) *
          ‖F (proj (lift t - z))‖ₑ := by
  set σ := φ.inhomogeneousLittlewoodPaleySchwartz
  set G : EuclideanSpace ℝ d → ℂ := fun y ↦ F (proj y)
  have hG : Continuous G := hF.comp continuous_proj
  filter_upwards [hgF, ae_fourierMultiplierCLM_lift_eq_integral σ hmem] with t hbt hPt
  -- Each block is at most `a j + c j`, the near part plus the tail part.
  have hac (j : ℕ) : ‖littlewoodPaleyBlock φ j g t‖ₑ ≤
      ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞) (hmem.toLp _) (lift t)‖ₑ +
        ∫⁻ y, kernelTail (σ j) (lift t - y) * ‖G y‖ₑ := by
    rw [hbt j, hPt j]
    exact eNorm_integral_fourierInv_sub_mul_le (σ j) hG (fun y ↦ hFM _) (lift_mem_cube t)
  set a : ℕ → ℝ≥0∞ := fun j ↦ ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞) (hmem.toLp _) (lift t)‖ₑ
  set c : ℕ → ℝ≥0∞ := fun j ↦ ∫⁻ y, kernelTail (σ j) (lift t - y) * ‖G y‖ₑ
  -- So the `ℓ²` sum of the blocks is at most `‖a‖_{ℓ²} + ‖c‖_{ℓ²} ≤ ‖a‖_{ℓ²} + ‖c‖_{ℓ¹}`.
  have hLp := ENNReal.Lp_add_le u a c (p := 2) one_le_two
  simp only [ENNReal.rpow_two, one_div] at hLp
  have hc : (∑ j ∈ u, c j ^ 2) ^ (2⁻¹ : ℝ) ≤ ∑ j ∈ u, c j := by
    refine (ENNReal.rpow_sum_le_sum_rpow (s := u) (fun j ↦ c j ^ 2) (p := 2⁻¹) (by norm_num)
      (by norm_num)).trans_eq (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  refine ((ENNReal.rpow_le_rpow (Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ zero_le (hac j) 2)
    (by norm_num)).trans hLp).trans (add_le_add (ENNReal.rpow_le_rpow (sum_le_tsum u)
      (by norm_num)) (hc.trans ((sum_le_tsum u).trans (le_of_eq ?_))))
  · rw [← lintegral_tsum (f := fun j y ↦ kernelTail (σ j) (lift t - y) * ‖G y‖ₑ) fun j ↦
      ((measurable_kernelTail (σ j)).comp (measurable_const.sub measurable_id)).mul
        hG.eNorm.measurable |>.aemeasurable]
    simp_rw [ENNReal.tsum_mul_right]
    have h := lintegral_sub_left_eq_self (μ := volume)
      (fun z ↦ (∑' j, kernelTail (σ j) z) * ‖G (lift t - z)‖ₑ) (lift t)
    simp only [sub_sub_cancel] at h
    exact h

/-- **The square function bound for trigonometric polynomials.** For `1 < p < ∞` there is `C` with
`‖(∑_{j ∈ u} |Δⱼ g|²)^{1/2}‖_p ≤ C ‖g‖_p` for every finite set `u` of indices and every
`g ∈ L²(𝕋ᵈ)` with finitely many nonzero Fourier coefficients. -/
private theorem exists_eLpNorm_sum_sq_le_of_mFourierCoeff_eq_zero
    (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (s : Finset (d → ℤ)) (g : L²(UnitAddTorus d)),
      (∀ n ∉ s, mFourierCoeff g n = 0) → ∀ u : Finset ℕ,
        eLpNorm (fun t ↦ (∑ j ∈ u, ‖littlewoodPaleyBlock φ j g t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume ≤
          C * eLpNorm g p volume := by
  set σ := φ.inhomogeneousLittlewoodPaleySchwartz
  -- The sum `κ` of the tails of the kernels.
  set κ : EuclideanSpace ℝ d → ℝ≥0∞ := fun z ↦ ∑' j, kernelTail (σ j) z
  have hκ : Measurable κ := Measurable.tsum fun j ↦ measurable_kernelTail (σ j)
  obtain ⟨C₁, hC₁⟩ :=
    exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le (F := ℂ) φ hp hp_top
  have hm : ∀ j, ((σ j).toLp ∞ volume : EuclideanSpace ℝ d → ℂ) =ᵐ[volume]
      fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := fun j ↦
    ((σ j).coeFn_toLp ∞ volume).trans (.of_eq (φ.coe_inhomogeneousLittlewoodPaleySchwartz j))
  refine ⟨C₁ * (3 ^ Fintype.card d) ^ (1 / p.toReal) + ∫⁻ z, κ z,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (by positivity) (by simp)), lintegral_tsum_kernelTail_ne_top φ⟩,
    fun s g hs u ↦ ?_⟩
  -- The trigonometric polynomial `g` agrees with the bounded continuous function `F`.
  set F : UnitAddTorus d → ℂ := fun t ↦ ∑ n ∈ s, mFourier n t • mFourierCoeff g n
  have hFc : Continuous F :=
    continuous_finsetSum _ fun n _ ↦ (mFourier n).continuous.smul continuous_const
  have hFM : ∀ t, ‖F t‖ ≤ ∑ n ∈ s, ‖mFourierCoeff g n‖ := fun t ↦
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ by simp [norm_mFourier_apply])
  have hmem : MemLp (box.indicator fun y ↦ F (proj y)) 2 volume :=
    memLp_box_indicator (hFc.comp continuous_proj) fun y ↦ hFM _
  have hA : AEMeasurable fun w ↦ (∑' j, ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞)
      (hmem.toLp _) w‖ₑ ^ 2) ^ (2⁻¹ : ℝ) :=
    (AEMeasurable.tsum fun j ↦ (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  have hgF : eLpNorm g p volume = eLpNorm F p volume :=
    eLpNorm_congr_ae (coeFn_ae_eq_sum_mFourier_smul_mFourierCoeff hs)
  rw [hgF, add_mul]
  have hS : AEStronglyMeasurable
      (fun t ↦ (∑ j ∈ u, ‖littlewoodPaleyBlock φ j g t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) volume :=
    ((Finset.aemeasurable_fun_sum _ fun j _ ↦
      (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _).aestronglyMeasurable
  calc _ ≤ eLpNorm ((fun t ↦ (∑' j, ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞) (hmem.toLp _)
          (lift t)‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) + fun t ↦ ∫⁻ z, κ z * ‖F (proj (lift t - z))‖ₑ) p volume :=
        eLpNorm_mono_eNorm_ae hS ((ae_rpow_sum_sq_littlewoodPaleyBlock_le φ hFc hFM
          (ae_littlewoodPaleyBlock_eq_integral φ hs) hmem u).mono
          fun t ht ↦ by simpa only [eNorm_eq_self, Pi.add_apply] using ht)
    _ ≤ _ := (eLpNorm_add_le hp.le).trans (add_le_add ?_ ?_)
  -- The part in the box, by the Littlewood–Paley theorem on `ℝᵈ`.
  · rw [mul_assoc]
    refine (eLpNorm_comp_lift_le hA p).trans ((hC₁ (fun j ↦ (σ j).toLp ∞ volume) hm _).trans ?_)
    rw [eLpNorm_congr_ae hmem.coeFn_toLp]
    gcongr
    exact eLpNorm_box_indicator_comp_proj_le hFc (zero_lt_one.trans hp).ne' hp_top
  -- The rest, by Minkowski's inequality.
  · exact eLpNorm_lintegral_mul_comp_proj_lift_sub_le hκ hFc hp.le hp_top

/-! ### The square function inequality -/

/-- **The Littlewood–Paley square function inequality on the torus.** Let `φ` be a smooth bump
function on `ℝᵈ`, let `Δⱼ` be the periodic Littlewood–Paley blocks built from it, and let
`1 < p < ∞`. There is a constant `C` such that for every `f ∈ L²(𝕋ᵈ)`,

`‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p ≤ C ‖f‖_p`. -/
theorem exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le
    (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : L²(UnitAddTorus d),
      eLpNorm (fun t ↦ (∑' j, ‖littlewoodPaleyBlock φ j f t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume ≤
        C * eLpNorm f p volume := by
  obtain ⟨C, hC, hCf⟩ := exists_eLpNorm_sum_sq_le_of_mFourierCoeff_eq_zero φ hp hp_top
  set C₀ := ENNReal.ofReal (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖)
  refine ⟨(C * C₀).toNNReal, fun f ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)]
  -- The full square sum is the increasing limit of the square sums over `j < N`.
  set G : ℕ → UnitAddTorus d → ℝ≥0∞ := fun N t ↦
    (∑ j ∈ Finset.range N, ‖littlewoodPaleyBlock φ j f t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hG : ∀ t, (∑' j, ‖littlewoodPaleyBlock φ j f t‖ₑ ^ 2) ^ (2⁻¹ : ℝ) = ⨆ N, G N t :=
    fun t ↦ by rw [← ENNReal.iSup_rpow_of_pos (by norm_num), ENNReal.tsum_eq_iSup_nat]
  have hmeas : ∀ N, AEMeasurable (G N) := fun N ↦
    (Finset.aemeasurable_fun_sum _ fun j _ ↦
      (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  have hmono : ∀ t, Monotone fun N ↦ G N t := fun t a b hab ↦ ENNReal.rpow_le_rpow
    (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hab)) (by norm_num)
  simp_rw [hG]
  rw [eLpNorm_iSup_eq_iSup_eLpNorm hmeas (.of_forall hmono)]
  refine iSup_le fun N ↦ ?_
  -- Replace `f` by a low-pass truncation, a trigonometric polynomial with the same blocks `j < N`.
  obtain ⟨M, hM⟩ := exists_littlewoodPaleyBlock_sum_range_eq φ N
  calc eLpNorm (G N) p volume
      = eLpNorm (fun t ↦ (∑ j ∈ Finset.range N, ‖littlewoodPaleyBlock φ j
          ((∑ k ∈ Finset.range (M + 1), littlewoodPaleyBlock φ k) f) t‖ₑ ^ 2) ^ (2⁻¹ : ℝ))
          p volume := by
        refine congrArg (eLpNorm · p volume) (funext fun t ↦ ?_)
        refine congrArg (· ^ (2⁻¹ : ℝ)) (Finset.sum_congr rfl fun j hj ↦ ?_)
        rw [hM j (Finset.mem_range.1 hj)]
    _ ≤ C * eLpNorm ((∑ k ∈ Finset.range (M + 1), littlewoodPaleyBlock φ k) f) p volume :=
        hCf _ _ (mFourierCoeff_sum_littlewoodPaleyBlock_range_eq_zero φ M f) (Finset.range N)
    _ ≤ C * (C₀ * eLpNorm f p volume) := by
        gcongr
        exact eLpNorm_sum_littlewoodPaleyBlock_range_le φ M hp.le f
    _ = C * C₀ * eLpNorm f p volume := (mul_assoc _ _ _).symm

/-! ### The reverse inequality -/

/-- **The reverse Littlewood–Paley inequality on the torus.** Let `φ` be a smooth bump function
on `ℝᵈ`, let `Δⱼ` be the periodic Littlewood–Paley blocks built from it, and let `1 < p < ∞`. There
is a constant `C` such that for every `f ∈ L²(𝕋ᵈ)`,

`‖f‖_p ≤ C ‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p`.

Neither side is assumed finite: in particular `f ∈ Lᵖ` as soon as its square function is. -/
theorem exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow
    (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : L²(UnitAddTorus d),
      eLpNorm f p volume ≤
        C * eLpNorm (fun t ↦ (∑' j, ‖littlewoodPaleyBlock φ j f t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  -- The conjugate exponent `q = (1 - p⁻¹)⁻¹` also lies in `(1, ∞)`.
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have : p.HolderConjugate q := ENNReal.HolderConjugate.inv_one_sub_inv' hp.le
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 hp_top.lt_top
  have hq_top : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  obtain ⟨C, hC⟩ := exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le φ hq hq_top
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  have hWL : ∀ j k, k ∈ Finset.Ico (j + 1 - L) (j + L) → |(k : ℤ) - j| < L :=
    fun j k hk ↦ abs_sub_lt_iff.2 (by rw [Finset.mem_Ico] at hk; omega)
  exact ⟨_, fun f ↦ eLpNorm_le_mul_eLpNorm_tsum_enorm_sq_rpow_of_card_le _
    (isSelfAdjoint_littlewoodPaleyBlock φ) (fun j ↦ Finset.Ico (j + 1 - L) (j + L))
    (fun j ↦ card_le_two_mul_of_abs_sub_lt Nat.cast_injective (hWL j))
    (card_filter_mem_le_two_mul_of_abs_sub_lt Nat.cast_injective hWL)
    (sum_littlewoodPaleyBlock_littlewoodPaleyBlock φ hL) hC
    (tendsto_sum_littlewoodPaleyBlock φ f)⟩

end TauCeti.UnitAddTorus
