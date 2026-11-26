/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.LittlewoodPaley
import TauCeti.Algebra.BigOperators.Finset.BoundedOverlap
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import TauCeti.Analysis.MeanInequalities
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# The Littlewood–Paley square function theorem on the torus

Let `φ` be a smooth bump function on `ℝᵈ = EuclideanSpace ℝ d` and let `Δⱼ` be the periodic
Littlewood–Paley blocks on `L²(𝕋ᵈ)`, `𝕋ᵈ = UnitAddTorus d`
(`TauCeti.UnitAddTorus.littlewoodPaleyBlock`): the Fourier multipliers `(Δⱼ f)^(n) = ψⱼ(n) f̂(n)`
with the pieces `ψⱼ` of the inhomogeneous Littlewood–Paley partition built from `φ`. For
`1 < p < ∞` there is a constant `C`, depending on `φ` and `p`, such that for every `f ∈ L²(𝕋ᵈ)`

`‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p ≤ C ‖f‖_p` and `‖f‖_p ≤ C ‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p`

(`TauCeti.UnitAddTorus.exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le` and
`TauCeti.UnitAddTorus.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow`).
Neither side is assumed finite, so `f ∈ Lᵖ(𝕋ᵈ)` exactly when its square function is. This is the
periodic counterpart of the Littlewood–Paley theorem on `ℝᵈ`
(`TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le`), and the `L²` case is
`TauCeti.UnitAddTorus.exists_tsum_norm_sq_littlewoodPaleyBlock_le`.

## The argument

The direct inequality is transferred from `ℝᵈ` rather than proved again by Calderón–Zygmund theory
on the torus.

* **Trigonometric polynomials.** Let `f = ∑_{n ∈ s} f̂(n) eₙ` be a trigonometric polynomial. Its
  lift `F x = ∑_{n ∈ s} f̂(n) 𝐞 ⟪x, n⟫` to `ℝᵈ` is bounded but not in `Lᵖ(ℝᵈ)`, so it is cut off
  to the cube `(-2r, 2r]ᵈ`. The Euclidean blocks are convolutions with the Schwartz kernels
  `𝓕⁻ ψⱼ`, which reproduce characters exactly: `𝓕⁻ ψⱼ ⋆ 𝐞 ⟪·, n⟫ = ψⱼ(n) 𝐞 ⟪·, n⟫`. A point of
  the cube `(-r, r]ᵈ` is at distance at least `r` from the outside of `(-2r, 2r]ᵈ`, so there the
  Euclidean blocks of the cut-off lift are the lifts of the periodic blocks `Δⱼ f`, up to the tails
  `∫_{‖z‖ ≥ r} |𝓕⁻ ψⱼ|` of the kernels. The cube `(-r, r]ᵈ` covers the torus `(2r)ᵈ` times when
  `r` is an integer, so the Euclidean inequality gives
  `‖(∑_{j < J} |Δⱼ f|²)^{1/2}‖_p ≤ 2^{d/p} C ‖f‖_p + error`, and for finitely many blocks the error
  vanishes as `r → ∞`.
* **All of `L²(𝕋ᵈ)`.** The low-pass truncation `∑_{k ≤ N} Δₖ f` is a trigonometric polynomial with
  the same blocks `Δⱼ`, `j < J`, once `N` is large, and it is bounded on `Lᵖ` uniformly in `N`
  (`TauCeti.UnitAddTorus.eLpNorm_sum_littlewoodPaleyBlock_range_le`). Monotone convergence in `J`
  gives the full square function.
* **The reverse inequality** follows from the direct one at the conjugate exponent by duality, as on
  `ℝᵈ`: the pieces whose indices differ by at least `L` have disjoint supports, so
  `⟪f, g⟫ = ∑ⱼ ∑_{|k - j| < L} ⟪Δⱼ f, Δₖ g⟫`, which Cauchy–Schwarz for the banded double sum and
  Hölder's inequality bound by a multiple of `‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p ‖g‖_q`.

As in `TauCeti.Analysis.Fourier.Torus.LittlewoodPaley`, `Lᵖ(𝕋ᵈ)` is taken for the product of the
Haar probability measures on the circle factors.

## Main declarations

* `TauCeti.UnitAddTorus.exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le`: the square
  function is bounded on `Lᵖ(𝕋ᵈ)`, `1 < p < ∞`.
* `TauCeti.UnitAddTorus.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow`: the
  reverse inequality.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press, 1971, Chapter VII, Section 3 (the transference of multipliers from `ℝᵈ` to the
  torus).
* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 4.3 (multipliers on the torus and transference) and Section 6.1
  (Littlewood–Paley theory).
-/

public section

noncomputable section

open Filter MeasureTheory Topology Set
open scoped lp ENNReal NNReal FourierTransform SchwartzMap Real InnerProductSpace

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### Integer cubes cover the torus evenly -/

/-- The Haar probability measure on the circle is Mathlib's volume on `UnitAddCircle`. -/
private theorem haarAddCircle_eq_volume :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) =
      @volume UnitAddCircle (AddCircle.measureSpace 1) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- Lebesgue measure on `(a, a + n]` pushed to the circle is `n` times its Haar measure. -/
private theorem map_coe_restrict_Ioc (a : ℝ) (n : ℕ) :
    (volume.restrict (Ioc a (a + n))).map ((↑) : ℝ → UnitAddCircle) =
      (n : ℝ≥0) • (volume : Measure UnitAddCircle) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hU : Ioc a (a + ↑(n + 1)) = Ioc a (a + n) ∪ Ioc (a + n) (a + n + 1) := by
      push_cast
      rw [← add_assoc, Ioc_union_Ioc_eq_Ioc (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)]
    rw [hU, Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add _ _ (by fun_prop), ih, (UnitAddCircle.measurePreserving_mk (a + n)).map_eq,
      ← haarAddCircle_eq_volume]
    push_cast
    rw [add_smul, one_smul]
    -- The volume on `UnitAddCircle` is, by the local instance, the Haar probability measure.
    rfl

/-- The product of `d` copies of `c` times the Haar measure on the circle is `c ^ card d` times the
Haar measure on the torus. -/
private theorem pi_smul_volume_eq (c : ℝ≥0) :
    Measure.pi (fun _ : d ↦ c • (volume : Measure UnitAddCircle)) =
      (c ^ Fintype.card d) • (volume : Measure (UnitAddTorus d)) := by
  refine Measure.pi_eq (μ := fun _ : d ↦ c • (volume : Measure UnitAddCircle)) fun s _ ↦ ?_
  rw [smul_apply, volume_pi, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul]
  simp only [smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/-- The cube `(-r, r]ᵈ` of `EuclideanSpace ℝ d`, in coordinates. -/
private def cube (r : ℝ) : Set (EuclideanSpace ℝ d) :=
  WithLp.ofLp ⁻¹' univ.pi fun _ ↦ Ioc (-r) r

/-- The projection of `ℝᵈ` onto the torus `ℝᵈ / ℤᵈ`. -/
private def proj (x : EuclideanSpace ℝ d) : UnitAddTorus d := fun i ↦ (x i : UnitAddCircle)

omit [Fintype d] in
private theorem continuous_proj : Continuous (proj (d := d)) :=
  continuous_pi fun i ↦ continuous_quotient_mk'.comp
    ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _))

omit [Fintype d] in
private theorem measurableSet_cube [Finite d] (r : ℝ) : MeasurableSet (cube (d := d) r) := by
  have := Fintype.ofFinite d
  exact (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc).preimage
    (PiLp.continuous_ofLp 2 _).measurable

/-- **The cube `(-N, N]ᵈ` covers the torus `(2N)ᵈ` times**: Lebesgue measure on it, pushed to the
torus, is `(2N)ᵈ` times the Haar probability measure. -/
private theorem map_proj_restrict_cube (N : ℕ) :
    (volume.restrict (cube (d := d) N)).map proj =
      ((2 * N : ℝ≥0) ^ Fintype.card d) • (volume : Measure (UnitAddTorus d)) := by
  have h1 : (volume.restrict (cube (d := d) N)).map WithLp.ofLp =
      (volume : Measure (d → ℝ)).restrict (univ.pi fun _ ↦ Ioc (-(N : ℝ)) N) :=
    ((PiLp.volume_preserving_ofLp d).restrict_preimage
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc)).map_eq
  have h2 : proj (d := d) = (fun (y : d → ℝ) i ↦ (y i : UnitAddCircle)) ∘ WithLp.ofLp := rfl
  rw [h2, ← Measure.map_map (by fun_prop) (PiLp.continuous_ofLp 2 _).measurable, h1,
    volume_pi, Measure.restrict_pi_pi, Measure.pi_map_pi (fun _ ↦ by fun_prop)]
  have h3 : ((volume : Measure ℝ).restrict (Ioc (-(N : ℝ)) N)).map
      ((↑) : ℝ → UnitAddCircle) = ((2 * N : ℕ) : ℝ≥0) • (volume : Measure UnitAddCircle) := by
    rw [show Ioc (-(N : ℝ)) N = Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)) by push_cast; ring_nf,
      map_coe_restrict_Ioc]
  rw [funext fun _ : d ↦ h3, pi_smul_volume_eq]
  push_cast
  -- The two sides differ only in the instance arguments through which `volume` on the torus, the
  -- product of the Haar probability measures, is reached.
  rfl

/-! ### Exponentials and the Littlewood–Paley kernels on `ℝᵈ` -/

/-- Lifted to `ℝᵈ`, the exponential monomial `eₙ` is the character `x ↦ 𝐞 ⟪x, n⟫`. -/
private theorem mFourier_proj (n : d → ℤ) (x : EuclideanSpace ℝ d) :
    mFourier n (proj x) = (𝐞 ⟪x, latticePoint n⟫_ℝ : ℂ) := by
  simp only [mFourier, ContinuousMap.coe_mk, proj, fourier_coe_apply, Real.fourierChar_apply,
    ← Complex.exp_sum, PiLp.inner_apply, latticePoint_apply, RCLike.inner_apply, conj_trivial]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Convolution with the kernel `𝓕⁻ σ` multiplies the character `y ↦ 𝐞 ⟪y, ξ⟫` by `σ ξ`. -/
private theorem integral_fourierInv_sub_mul_fourierChar (σ : 𝓢(EuclideanSpace ℝ d, ℂ))
    (ξ x : EuclideanSpace ℝ d) :
    ∫ y, 𝓕⁻ σ (x - y) * (𝐞 ⟪y, ξ⟫_ℝ : ℂ) = σ ξ * 𝐞 ⟪x, ξ⟫_ℝ := by
  have h := integral_sub_left_eq_self (fun z ↦ 𝓕⁻ σ z * (𝐞 ⟪x - z, ξ⟫_ℝ : ℂ)) volume x
  simp only [sub_sub_cancel] at h
  rw [h]
  have hz : ∀ z, 𝓕⁻ σ z * (𝐞 ⟪x - z, ξ⟫_ℝ : ℂ) =
      (𝐞 ⟪x, ξ⟫_ℝ : ℂ) * (𝐞 (-⟪z, ξ⟫_ℝ) • 𝓕⁻ σ z) := fun z ↦ by
    rw [inner_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  simp_rw [hz, integral_const_mul]
  rw [← Real.fourier_eq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq,
    mul_comm]

/-! ### Trigonometric polynomials and their lifts to `ℝᵈ` -/

/-- The lift to `ℝᵈ` of the trigonometric polynomial with coefficients `c` on `s`:
`x ↦ ∑_{n ∈ s} c n 𝐞 ⟪x, n⟫`. -/
private def lift (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (x : EuclideanSpace ℝ d) : ℂ :=
  ∑ n ∈ s, c n * 𝐞 ⟪x, latticePoint n⟫_ℝ

private theorem sum_mul_mFourier_proj (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ)
    (x : EuclideanSpace ℝ d) :
    ∑ n ∈ s, c n * mFourier n (proj x) = lift s c x := by
  simp [lift, mFourier_proj]

private theorem continuous_lift (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    Continuous (lift s c) := by
  unfold lift
  fun_prop

/-- The lift of a trigonometric polynomial is bounded by the sum of the norms of its
coefficients. -/
private theorem norm_lift_le (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (x : EuclideanSpace ℝ d) :
    ‖lift s c x‖ ≤ ∑ n ∈ s, ‖c n‖ :=
  (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun n _ ↦ by simp)

/-- Convolution with the kernel `𝓕⁻ σ` multiplies the coefficients of the lift of a
trigonometric polynomial by the values of `σ` at the lattice points. -/
private theorem integral_fourierInv_sub_mul_lift (σ : 𝓢(EuclideanSpace ℝ d, ℂ))
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (x : EuclideanSpace ℝ d) :
    ∫ y, 𝓕⁻ σ (x - y) * lift s c y = lift s (fun n ↦ σ (latticePoint n) * c n) x := by
  have hK : Integrable fun y ↦ 𝓕⁻ σ (x - y) := (𝓕⁻ σ).integrable.comp_sub_left x
  simp only [lift, Finset.mul_sum]
  rw [integral_finsetSum _ fun n _ ↦ ?_]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp_rw [mul_left_comm _ (c n), integral_const_mul,
      integral_fourierInv_sub_mul_fourierChar]
    ring
  · exact hK.mul_bdd (g := fun y ↦ c n * (𝐞 ⟪y, latticePoint n⟫_ℝ : ℂ)) (c := ‖c n‖)
      (by fun_prop) (.of_forall fun y ↦ by simp)

/-! ### Cutting off the lift to a cube -/

/-- The cube `(-r, r]ᵈ` has volume `(2r)ᵈ`. -/
private theorem volume_cube (N : ℕ) :
    volume (cube (d := d) N) = ((2 * N : ℝ≥0) ^ Fintype.card d : ℝ≥0) := by
  have h := congrArg (fun μ : Measure (UnitAddTorus d) ↦ μ univ) (map_proj_restrict_cube (d := d) N)
  simp only [Measure.map_apply continuous_proj.measurable MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul,
    mul_one] at h
  exact h

/-- The `Lᵖ` norm on the cube `(-N, N]ᵈ` of a lifted function `g ∘ proj` is `((2N)ᵈ)^{1/p}` times
the `Lᵖ` norm of `g` on the torus. -/
private theorem eLpNorm_comp_proj_restrict_cube {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {g : UnitAddTorus d → ε} (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : p ≠ ∞)
    (N : ℕ) :
    eLpNorm (g ∘ proj) p (volume.restrict (cube N)) =
      (((2 * N : ℝ≥0) : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * eLpNorm g p volume := by
  have hg' : AEStronglyMeasurable g ((volume.restrict (cube (d := d) N)).map proj) := by
    rw [map_proj_restrict_cube]
    exact hg.smul_measure _
  have hsmul : ((2 * N : ℝ≥0) ^ Fintype.card d • volume : Measure (UnitAddTorus d)) =
      (((2 * N : ℝ≥0) ^ Fintype.card d : ℝ≥0) : ℝ≥0∞) • volume := by
    ext s
    simp [ENNReal.smul_def]
  rw [← eLpNorm_map_measure hg' continuous_proj.measurable.aemeasurable, map_proj_restrict_cube,
    hsmul, eLpNorm_smul_measure_of_ne_top hp _ _ hg, smul_eq_mul, ENNReal.coe_pow]

/-- A point of `(-r, r]ᵈ` is at distance at least `r` from every point outside
`(-2r, 2r]ᵈ`. -/
private theorem le_norm_sub_of_mem_cube {r : ℝ} {x y : EuclideanSpace ℝ d} (hx : x ∈ cube r)
    (hy : y ∉ cube (2 * r)) : r ≤ ‖x - y‖ := by
  simp only [cube, mem_preimage, mem_univ_pi, mem_Ioc, not_forall] at hx hy
  obtain ⟨i, hi⟩ := hy
  have hxi := hx i
  have h : r ≤ |x i - y i| := by
    rcases not_and_or.1 hi with h | h
    · rw [not_lt] at h
      exact le_abs.2 (Or.inl (by linarith))
    · rw [not_le] at h
      exact le_abs.2 (Or.inr (by linarith))
  exact h.trans (by simpa using PiLp.norm_apply_le (x - y) i)

/-- **The cut-off error.** For `x ∈ (-r, r]ᵈ`, convolving a kernel `K` with a function bounded by
`M` and supported outside `(-2r, 2r]ᵈ` gives at most `M` times the tail `∫_{‖z‖ ≥ r} ‖K‖` of
the kernel. -/
private theorem enorm_integral_mul_indicator_compl_le {K g : EuclideanSpace ℝ d → ℂ}
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hg : ∀ y, ‖g y‖ₑ ≤ M) {r : ℝ}
    {x : EuclideanSpace ℝ d} (hx : x ∈ cube r) :
    ‖∫ y, K (x - y) * (cube (2 * r))ᶜ.indicator g y‖ₑ ≤
      M * ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖K z‖ₑ) z := by
  calc _ ≤ ∫⁻ y, ‖K (x - y) * (cube (2 * r))ᶜ.indicator g y‖ₑ := eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ y, M * {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖K z‖ₑ) (x - y) := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ cube (2 * r)
        · simp [hy]
        · have hxy : x - y ∈ {z : EuclideanSpace ℝ d | r ≤ ‖z‖} := le_norm_sub_of_mem_cube hx hy
          rw [indicator_of_mem (mem_compl hy), indicator_of_mem hxy, eNorm_mul, mul_comm]
          gcongr
          exact hg y
    _ = M * ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖K z‖ₑ) z := by
        rw [lintegral_const_mul' _ _ hM, lintegral_sub_left_eq_self]

/-- The tail `∫_{‖z‖ ≥ r} ‖𝓕⁻ σ‖` of the kernel of a Schwartz symbol `σ` tends to zero. -/
private theorem tendsto_lintegral_indicator_enorm_fourierInv (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    Tendsto (fun N : ℕ ↦ ∫⁻ z, {z | (N : ℝ) ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ σ z‖ₑ) z) atTop
      (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume) (f := fun _ ↦ 0)
    (F := fun (N : ℕ) z ↦ {z : EuclideanSpace ℝ d | (N : ℝ) ≤ ‖z‖}.indicator
      (fun z ↦ ‖𝓕⁻ σ z‖ₑ) z) (fun z ↦ ‖𝓕⁻ σ z‖ₑ)
    (fun N ↦ (𝓕⁻ σ).continuous.measurable.eNorm.indicator
      (measurableSet_le measurable_const measurable_norm))
    (fun N ↦ .of_forall fun z ↦ indicator_le_self _ _ z)
    (𝓕⁻ σ).integrable.hasFiniteIntegral.ne
    (.of_forall fun z ↦ tendsto_const_nhds.congr' <|
      (tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖z‖).mono fun N hN ↦
        (indicator_of_notMem (by simpa using hN) _).symm)
  simpa using h

/-- **Convolving the cut-off lift.** For `x ∈ (-r, r]ᵈ`, convolving the lift of a trigonometric
polynomial, cut off to `(-2r, 2r]ᵈ`, with the kernel `𝓕⁻ σ` gives the lift with coefficients
multiplied by `σ`, up to `M` times the tail of the kernel, where `M` bounds the coefficients'
`ℓ¹` norm. -/
private theorem enorm_lift_sub_integral_le (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) (s : Finset (d → ℤ))
    (c : (d → ℤ) → ℂ) {r : ℝ} {x : EuclideanSpace ℝ d} (hx : x ∈ cube r) :
    ‖lift s (fun n ↦ σ (latticePoint n) * c n) x -
        ∫ y, 𝓕⁻ σ (x - y) * (cube (2 * r)).indicator (lift s c) y‖ₑ ≤
      (∑ n ∈ s, ‖c n‖ₑ) * ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ σ z‖ₑ) z := by
  have hK : Integrable fun y ↦ 𝓕⁻ σ (x - y) := (𝓕⁻ σ).integrable.comp_sub_left x
  have hb : ∀ y, ‖lift s c y‖ ≤ ∑ n ∈ s, ‖c n‖ := norm_lift_le s c
  have hint : ∀ t : Set (EuclideanSpace ℝ d), MeasurableSet t →
      Integrable fun y ↦ 𝓕⁻ σ (x - y) * t.indicator (lift s c) y := fun t ht ↦
    hK.mul_bdd ((continuous_lift s c).aestronglyMeasurable.indicator ht)
      (.of_forall fun y ↦ (norm_indicator_le_norm_self _ _).trans (hb y))
  have hsplit : ∫ y, 𝓕⁻ σ (x - y) * lift s c y =
      (∫ y, 𝓕⁻ σ (x - y) * (cube (2 * r)).indicator (lift s c) y) +
        ∫ y, 𝓕⁻ σ (x - y) * (cube (2 * r))ᶜ.indicator (lift s c) y := by
    rw [← integral_add (hint _ (measurableSet_cube _)) (hint _ (measurableSet_cube _).compl)]
    congr 1 with y
    rw [← mul_add, indicator_self_add_compl_apply]
  rw [← integral_fourierInv_sub_mul_lift, hsplit, add_sub_cancel_left]
  refine enorm_integral_mul_indicator_compl_le (ENNReal.sum_ne_top.2 fun n _ ↦ eNorm_ne_top)
    (fun y ↦ ?_) hx
  refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  rw [eNorm_mul]
  simp

/-- **The square function on the cube.** Let `σⱼ` be Schwartz symbols. On `(-r, r]ᵈ`, the square
function of the lifts of the blocks `∑_{n ∈ s} σⱼ(n) c n eₙ`, `j < J`, is at most the square
function of the `L²` multipliers `T_{σⱼ}` applied to the lift cut off to `(-2r, 2r]ᵈ`, plus the
square sum of the cut-off errors. -/
private theorem ae_sum_enorm_lift_sq_rpow_le (σ : ℕ → 𝓢(EuclideanSpace ℝ d, ℂ))
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) {r : ℝ}
    (hu : MemLp ((cube (2 * r)).indicator (lift s c)) 2 volume) (J : ℕ) :
    ∀ᵐ x ∂volume.restrict (cube r),
      (∑ j ∈ Finset.range J, ‖lift s (fun n ↦ σ j (latticePoint n) * c n) x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) ≤
        (∑' j, ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞ volume) (hu.toLp _) x‖ₑ ^ 2) ^
            (2⁻¹ : ℝ) +
          (∑ j ∈ Finset.range J, ((∑ n ∈ s, ‖c n‖ₑ) *
            ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ (σ j) z‖ₑ) z) ^ 2) ^ (2⁻¹ : ℝ) := by
  set B := fun j ↦ Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞ volume) (hu.toLp _)
  have hB : ∀ j, ∀ᵐ x ∂volume,
      B j x = ∫ y, 𝓕⁻ (σ j) (x - y) * (cube (2 * r)).indicator (lift s c) y := fun j ↦ by
    filter_upwards [SchwartzMap.coeFn_fourierMultiplierCLM_toLp (σ j) (hu.toLp _)] with x hx
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with y hy
    rw [hy, smul_eq_mul]
  filter_upwards [ae_restrict_mem (measurableSet_cube r), ae_restrict_of_ae (ae_all_iff.2 hB)]
    with x hx hBx
  calc (∑ j ∈ Finset.range J, ‖lift s (fun n ↦ σ j (latticePoint n) * c n) x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
      ≤ (∑ j ∈ Finset.range J, (‖B j x‖ₑ + (∑ n ∈ s, ‖c n‖ₑ) *
          ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ (σ j) z‖ₑ) z) ^ 2) ^ (2⁻¹ : ℝ) := by
        gcongr with j
        rw [hBx j, ← add_sub_cancel (∫ y, 𝓕⁻ (σ j) (x - y) * (cube (2 * r)).indicator (lift s c) y)
          (lift s (fun n ↦ σ j (latticePoint n) * c n) x)]
        exact (eNorm_add_le _ _).trans (add_le_add le_rfl (enorm_lift_sub_integral_le _ _ _ hx))
    _ ≤ (∑ j ∈ Finset.range J, ‖B j x‖ₑ ^ 2) ^ (2⁻¹ : ℝ) + (∑ j ∈ Finset.range J,
          ((∑ n ∈ s, ‖c n‖ₑ) * ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ (σ j) z‖ₑ) z) ^ 2) ^
            (2⁻¹ : ℝ) := by
        simpa only [ENNReal.rpow_two, one_div] using ENNReal.Lp_add_le (Finset.range J)
          (fun j ↦ ‖B j x‖ₑ) (fun j ↦ (∑ n ∈ s, ‖c n‖ₑ) *
            ∫⁻ z, {z | r ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ (σ j) z‖ₑ) z) one_le_two
    _ ≤ _ := by
        gcongr
        exact _root_.sum_le_tsum _

/-! ### Transference for trigonometric polynomials -/

/-- The lift of a trigonometric polynomial, cut off to a cube, is square integrable. -/
private theorem memLp_indicator_cube_lift (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (N : ℕ) :
    MemLp ((cube (N : ℝ)).indicator (lift s c)) 2 volume := by
  have : IsFiniteMeasure (volume.restrict (cube (d := d) N)) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.coe_ne_top)
  refine (memLp_indicator_iff_restrict (measurableSet_cube _).nullMeasurableSet).2 ?_
  exact MemLp.of_bound (continuous_lift s c).aestronglyMeasurable _ (.of_forall (norm_lift_le s c))

/-- The factor `((4N)ᵈ)^{1/p}` by which the cube `(-2N, 2N]ᵈ` covers the torus is `(2ᵈ)^{1/p}` times
the factor `((2N)ᵈ)^{1/p}` of the cube `(-N, N]ᵈ`. -/
private theorem rpow_two_mul_cube_factor (N : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    (((2 * (2 * N : ℕ) : ℝ≥0) : ℝ≥0∞) ^ Fintype.card d) ^ q =
      ((2 : ℝ≥0∞) ^ Fintype.card d) ^ q * (((2 * N : ℝ≥0) : ℝ≥0∞) ^ Fintype.card d) ^ q := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hq, ← mul_pow]
  push_cast
  ring_nf

/-- **Transference on one cube.** Let `σⱼ` be Schwartz symbols whose `L²` multipliers `T_{σⱼ}` have
a square function bounded on `Lᵖ(ℝᵈ)` with constant `C`, and let `N > 0`. For the trigonometric
polynomials `g = ∑_{n ∈ s} c n eₙ` and `gⱼ = ∑_{n ∈ s} σⱼ(n) c n eₙ`,

`‖(∑_{j < J} |gⱼ|²)^{1/2}‖_p ≤ 2^{d/p} C ‖g‖_p + E_N`,

where `E_N` is the square sum over `j < J` of the tails `∫_{‖z‖ ≥ N} |𝓕⁻ σⱼ|`, times the `ℓ¹`
norm of `c`. The lift of `g` is cut off to the cube `(-2N, 2N]ᵈ`; on the cube `(-N, N]ᵈ` its
Euclidean blocks are the lifts of the `gⱼ` up to those tails, and the two cubes cover the torus
`(4N)ᵈ` and `(2N)ᵈ` times. -/
private theorem eLpNorm_sum_sq_rpow_le_add (σ : ℕ → 𝓢(EuclideanSpace ℝ d, ℂ)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) {C : ℝ≥0∞}
    (hC : ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ d)),
      eLpNorm (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞ volume) u x‖ₑ ^ 2) ^
        (2⁻¹ : ℝ)) p volume ≤ C * eLpNorm u p volume)
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (J : ℕ) {N : ℕ} (hN : 0 < N) :
    eLpNorm (fun z ↦ (∑ j ∈ Finset.range J,
        ‖∑ n ∈ s, σ j (latticePoint n) * c n * mFourier n z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume ≤
      ((2 : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * C *
          eLpNorm (fun z ↦ ∑ n ∈ s, c n * mFourier n z) p volume +
        (∑ j ∈ Finset.range J, ((∑ n ∈ s, ‖c n‖ₑ) *
          ∫⁻ z, {z | (N : ℝ) ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ (σ j) z‖ₑ) z) ^ 2) ^ (2⁻¹ : ℝ) := by
  set T : UnitAddTorus d → ℝ≥0∞ := fun z ↦ (∑ j ∈ Finset.range J,
    ‖∑ n ∈ s, σ j (latticePoint n) * c n * mFourier n z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  set g : UnitAddTorus d → ℂ := fun z ↦ ∑ n ∈ s, c n * mFourier n z
  set E := (∑ j ∈ Finset.range J, ((∑ n ∈ s, ‖c n‖ₑ) *
    ∫⁻ z, {z | (N : ℝ) ≤ ‖z‖}.indicator (fun z ↦ ‖𝓕⁻ (σ j) z‖ₑ) z) ^ 2) ^ (2⁻¹ : ℝ)
  have hTm : Measurable T := by fun_prop
  have hgproj : g ∘ proj = lift s c := funext (sum_mul_mFourier_proj s c)
  have hc2 : cube (d := d) (2 * N) = cube ((2 * N : ℕ) : ℝ) := by push_cast; rfl
  have hu : MemLp ((cube (2 * N : ℝ)).indicator (lift s c)) 2 volume :=
    hc2 ▸ memLp_indicator_cube_lift s c (2 * N)
  set SU : EuclideanSpace ℝ d → ℝ≥0∞ := fun x ↦ (∑' j,
    ‖Lp.fourierMultiplierCLM ℂ ((σ j).toLp ∞ volume) (hu.toLp _) x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  -- The cube `(-N, N]ᵈ` covers the torus `(2N)ᵈ` times.
  set a : ℝ≥0∞ := (((2 * N : ℝ≥0) : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal
  have ha0 : a ≠ 0 := by positivity
  have hatop : a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hvol : volume (cube (d := d) N) ^ (1 / p.toReal) = a := by
    rw [volume_cube, one_div, ← ENNReal.toReal_inv, ← one_div, ENNReal.coe_pow]
  refine (ENNReal.mul_le_mul_iff_right ha0 hatop).1 ?_
  calc a * eLpNorm T p volume = eLpNorm (T ∘ proj) p (volume.restrict (cube N)) :=
        (eLpNorm_comp_proj_restrict_cube hTm.aestronglyMeasurable hp_top N).symm
    _ ≤ eLpNorm (fun x ↦ SU x + E) p (volume.restrict (cube N)) := by
        refine eLpNorm_mono_eNorm_ae
          (hTm.comp continuous_proj.measurable).aestronglyMeasurable ?_
        filter_upwards [ae_sum_enorm_lift_sq_rpow_le σ s c hu J] with x hx
        simpa only [T, Function.comp_apply, eNorm_eq_self, sum_mul_mFourier_proj] using hx
    _ ≤ eLpNorm SU p (volume.restrict (cube N)) +
          eLpNorm (fun _ ↦ E) p (volume.restrict (cube N)) :=
        eLpNorm_add_le (f := SU) (g := fun _ ↦ E) hp
    _ ≤ C * eLpNorm (hu.toLp _) p volume + E * a := by
        refine add_le_add ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC _)) ?_
        rw [eLpNorm_const' _ (zero_lt_one.trans_le hp).ne' hp_top, Measure.restrict_apply_univ,
          hvol, eNorm_eq_self]
    _ = a * (((2 : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * C * eLpNorm g p volume + E) := by
        rw [eLpNorm_congr_ae hu.coeFn_toLp,
          eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_cube _).nullMeasurableSet,
          ← hgproj, hc2, eLpNorm_comp_proj_restrict_cube
            (by fun_prop : Continuous g).aestronglyMeasurable hp_top,
          rpow_two_mul_cube_factor N _ ENNReal.toReal_nonneg]
        ring

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-- **The square function inequality for trigonometric polynomials**, transferred from `ℝᵈ`. If the
Littlewood–Paley square function on `ℝᵈ` is bounded on `Lᵖ` with constant `C`, then for every
`f ∈ L²(𝕋ᵈ)` with finitely many nonzero Fourier coefficients and every `J`,
`‖(∑_{j < J} |Δⱼ f|²)^{1/2}‖_p ≤ 2^{d/p} C ‖f‖_p`: the error of
`eLpNorm_sum_sq_rpow_le_add` vanishes as `N → ∞`. -/
private theorem eLpNorm_sum_littlewoodPaleyBlock_le_of_mFourierCoeff_eq_zero {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) {C : ℝ≥0∞}
    (hC : ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ d)),
      eLpNorm (fun x ↦ (∑' j, ‖Lp.fourierMultiplierCLM ℂ
        ((φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) u x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
        volume ≤ C * eLpNorm u p volume)
    {f : L²(UnitAddTorus d)} {s : Finset (d → ℤ)} (hs : ∀ n ∉ s, mFourierCoeff f n = 0)
    (J : ℕ) :
    eLpNorm (fun z ↦ (∑ j ∈ Finset.range J, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p
        volume ≤ ((2 : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * C * eLpNorm f p volume := by
  set σ := φ.inhomogeneousLittlewoodPaleySchwartz
  set c : (d → ℤ) → ℂ := fun n ↦ mFourierCoeff f n
  -- The blocks of `f`, and `f` itself, are trigonometric polynomials.
  have hpoly : ∀ g : L²(UnitAddTorus d), (∀ n ∉ s, mFourierCoeff g n = 0) →
      g =ᵐ[volume] fun z ↦ ∑ n ∈ s, mFourierCoeff g n * mFourier n z := fun g hg ↦ by
    -- `Integrable.ae_eq_sum_mFourier_smul_mFourierCoeff` is stated for Mathlib's volume on the
    -- torus, which is the product of the Haar probability measures used here.
    have h := Integrable.ae_eq_sum_mFourier_smul_mFourierCoeff
      (by rw [volume_eq_pi_haarAddCircle]; exact (Lp.memLp g).integrable one_le_two) hg
    rw [volume_eq_pi_haarAddCircle] at h
    filter_upwards [h] with z hz
    simp [hz, mul_comm]
  have h : ∀ j, (littlewoodPaleyBlock φ j f : UnitAddTorus d → ℂ) =ᵐ[volume]
      fun z ↦ ∑ n ∈ s, σ j (latticePoint n) * c n * mFourier n z := fun j ↦ by
    simpa [σ, c, ContDiffBump.inhomogeneousLittlewoodPaleySchwartz_apply] using
      hpoly (littlewoodPaleyBlock φ j f) fun n hn ↦ by simp [hs n hn]
  have hT : (fun z ↦ (∑ j ∈ Finset.range J, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ))
      =ᵐ[volume] fun z ↦ (∑ j ∈ Finset.range J,
        ‖∑ n ∈ s, σ j (latticePoint n) * c n * mFourier n z‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
    filter_upwards [ae_all_iff.2 h] with z hz
    simp only [hz]
  rw [eLpNorm_congr_ae hT, eLpNorm_congr_ae (hpoly f hs)]
  -- The cut-off errors vanish as the cubes grow.
  have hE := tendsto_finsetSum (Finset.range J) fun j _ ↦ ENNReal.Tendsto.pow (n := 2)
    (ENNReal.Tendsto.const_mul (a := ∑ n ∈ s, ‖c n‖ₑ)
      (tendsto_lintegral_indicator_enorm_fourierInv (σ j))
      (Or.inr (ENNReal.sum_ne_top.2 fun n _ ↦ eNorm_ne_top)))
  replace hE := ((ENNReal.continuous_rpow_const (y := 2⁻¹)).tendsto _).comp
    (hE.comp (tendsto_add_atTop_nat 1))
  refine ge_of_tendsto' (x := atTop) ?_ fun N : ℕ ↦
    eLpNorm_sum_sq_rpow_le_add σ hp hp_top hC s c J (Nat.succ_pos N)
  simpa [Function.comp_def] using tendsto_const_nhds.add hE

/-! ### The square function inequality on the torus -/

/-- The low-pass truncation `∑_{k ≤ N} Δₖ` leaves the block `Δⱼ` unchanged once `j + L ≤ N + 1`,
where pieces of the partition whose indices differ by at least `L` have disjoint supports. -/
private theorem littlewoodPaleyBlock_sum_range {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : EuclideanSpace ℝ d,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    {j N : ℕ} (hjN : j + L ≤ N + 1) (f : L²(UnitAddTorus d)) :
    littlewoodPaleyBlock φ j ((∑ k ∈ Finset.range (N + 1), littlewoodPaleyBlock φ k) f) =
      littlewoodPaleyBlock φ j f := by
  refine mFourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
  simp only [mFourierBasis_repr, mFourierCoeff_littlewoodPaleyBlock,
    mFourierCoeff_sum_littlewoodPaleyBlock_range, ← mul_assoc]
  congr 1
  rw [← φ.sum_inhomogeneousLittlewoodPaley_range, mul_comm, ← Complex.ofReal_mul,
    Finset.sum_mul, ← Finset.sum_subset (s₁ := Finset.Ico (j + 1 - L) (j + L))
      (fun k hk ↦ Finset.mem_range.2 (by rw [Finset.mem_Ico] at hk; omega)) fun k _ hk ↦ ?_,
    ← Finset.sum_mul, ← φ.enlargedLittlewoodPaley_apply,
    φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL]
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
  rcases hk with hk | hk
  · exact hL k j (by omega) _
  · rw [mul_comm]
    exact hL j k hk _

/-- The square function of the periodic blocks is the increasing limit of its truncations to
the blocks `Δⱼ`, `j < J`. -/
private theorem eLpNorm_tsum_eq_iSup (p : ℝ≥0∞) (f : L²(UnitAddTorus d)) :
    eLpNorm (fun z ↦ (∑' j, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume =
      ⨆ J, eLpNorm (fun z ↦ (∑ j ∈ Finset.range J, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^
        (2⁻¹ : ℝ)) p volume := by
  simp_rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  refine eLpNorm_iSup_eq_iSup_eLpNorm (fun J ↦ ?_) (.of_forall fun z a b hab ↦ ?_)
  · exact (Finset.aemeasurable_fun_sum _ fun j _ ↦
      (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  · exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hab))
      (by norm_num)

/-- **The Littlewood–Paley square function inequality on the torus.** Let `φ` be a smooth bump
function on `ℝᵈ`, let `Δⱼ` be the periodic Littlewood–Paley blocks on `L²(𝕋ᵈ)`, the Fourier
multipliers with the pieces `ψⱼ` of the inhomogeneous partition built from `φ` sampled on `ℤᵈ`, and
let `1 < p < ∞`. There is a constant `C` such that for every `f ∈ L²(𝕋ᵈ)`,

`‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p ≤ C ‖f‖_p`.

Neither side is assumed finite. -/
theorem exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : L²(UnitAddTorus d),
      eLpNorm (fun z ↦ (∑' j, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume ≤
        C * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := TauCeti.exists_eLpNorm_tsum_enorm_fourierMultiplierCLM_sq_rpow_le (F := ℂ) φ
    hp hp_top
  have hC' := hC (fun j ↦ (φ.inhomogeneousLittlewoodPaleySchwartz j).toLp ∞ volume) fun j ↦
    ((φ.inhomogeneousLittlewoodPaleySchwartz j).coeFn_toLp ∞ volume).trans
      (.of_forall fun ξ ↦ φ.inhomogeneousLittlewoodPaleySchwartz_apply j ξ)
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  set C₀ : ℝ≥0∞ := ENNReal.ofReal (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖)
  set K : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * C * C₀
  have hK : K ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (by simp)
  refine ⟨K.toNNReal, fun f ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hK, eLpNorm_tsum_eq_iSup]
  refine iSup_le fun J ↦ ?_
  -- Replace `f` by its low-pass truncation `g`, a trigonometric polynomial with the same blocks
  -- `Δⱼ`, `j < J`.
  set g := (∑ k ∈ Finset.range (J + L + 1), littlewoodPaleyBlock φ k) f
  have hgs : ∀ n ∉ (finite_setOf_norm_latticePoint_le (ι := d)
      (2 ^ (J + L) * φ.rOut)).toFinset, mFourierCoeff g n = 0 := fun n hn ↦ by
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hn
    rw [mFourierCoeff_sum_littlewoodPaleyBlock_range, φ.zero_of_le_dist, Complex.ofReal_zero,
      zero_mul]
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity),
      inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
    exact hn.le
  have hgf : ∀ j ∈ Finset.range J, littlewoodPaleyBlock φ j g = littlewoodPaleyBlock φ j f :=
    fun j hj ↦ littlewoodPaleyBlock_sum_range φ hL (by rw [Finset.mem_range] at hj; omega) f
  calc eLpNorm (fun z ↦ (∑ j ∈ Finset.range J, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^
        (2⁻¹ : ℝ)) p volume
      = eLpNorm (fun z ↦ (∑ j ∈ Finset.range J, ‖littlewoodPaleyBlock φ j g z‖ₑ ^ 2) ^
        (2⁻¹ : ℝ)) p volume := by
        refine congrArg (eLpNorm · p volume) (funext fun z ↦ ?_)
        rw [Finset.sum_congr rfl fun j hj ↦ by rw [← hgf j hj]]
    _ ≤ ((2 : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * C * eLpNorm g p volume :=
        eLpNorm_sum_littlewoodPaleyBlock_le_of_mFourierCoeff_eq_zero φ hp.le hp_top hC' hgs J
    _ ≤ ((2 : ℝ≥0∞) ^ Fintype.card d) ^ (1 / p).toReal * C * (C₀ * eLpNorm f p volume) := by
        gcongr
        exact eLpNorm_sum_littlewoodPaleyBlock_range_le φ (J + L) hp.le f
    _ = K * eLpNorm f p volume := by ring

/-! ### The reverse inequality -/

/-- The periodic Littlewood–Paley blocks are self-adjoint, since their symbols are real. -/
private theorem inner_littlewoodPaleyBlock_left (j : ℕ) (a b : L²(UnitAddTorus d)) :
    ⟪littlewoodPaleyBlock φ j a, b⟫_ℂ = ⟪a, littlewoodPaleyBlock φ j b⟫_ℂ := by
  simp only [L2.inner_def, RCLike.inner_apply, mul_comm (b _),
    mul_comm (littlewoodPaleyBlock φ j b _)]
  refine (hasSum_prod_mFourierCoeff (littlewoodPaleyBlock φ j a) b).unique
    ((hasSum_prod_mFourierCoeff a (littlewoodPaleyBlock φ j b)).congr_fun fun n ↦ ?_)
  simp only [mFourierCoeff_littlewoodPaleyBlock, map_mul, Complex.conj_ofReal]
  ring

/-- The block `Δⱼ f` only sees the blocks `Δₖ g` with `k` within `L` of `j`:
`⟪Δⱼ f, g⟫ = ∑_{|k - j| < L} ⟪Δⱼ f, Δₖ g⟫`, where `L` separates the supports of the pieces. -/
private theorem inner_littlewoodPaleyBlock_eq_sum {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : EuclideanSpace ℝ d,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (j : ℕ) (f g : L²(UnitAddTorus d)) :
    ⟪littlewoodPaleyBlock φ j f, g⟫_ℂ = ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
      ⟪littlewoodPaleyBlock φ j f, littlewoodPaleyBlock φ k g⟫_ℂ := by
  have h : littlewoodPaleyBlock φ j f = ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
      littlewoodPaleyBlock φ k (littlewoodPaleyBlock φ j f) := by
    refine mFourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
    simp only [map_sum, lp.coeFn_sum, Finset.sum_apply, mFourierBasis_repr,
      mFourierCoeff_littlewoodPaleyBlock]
    have h := φ.enlargedLittlewoodPaley_mul_inhomogeneousLittlewoodPaley hL j (latticePoint n)
    rw [φ.enlargedLittlewoodPaley_apply] at h
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_mul, h]
  conv_lhs => rw [h]
  rw [sum_inner]
  exact Finset.sum_congr rfl fun k _ ↦ inner_littlewoodPaleyBlock_left φ k _ _

/-- **The pairing bound.** For the partial sums of the blocks of `f`,
`|⟪∑_{j < N} Δⱼ f, g⟫| ≤ 2L ∫ S f · S g`, where `S` is the square function and `L` separates the
supports of the pieces. -/
private theorem enorm_inner_sum_littlewoodPaleyBlock_le {L : ℕ}
    (hL : ∀ j k : ℕ, j + L ≤ k → ∀ ξ : EuclideanSpace ℝ d,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0)
    (N : ℕ) (f g : L²(UnitAddTorus d)) :
    ‖⟪∑ j ∈ Finset.range N, littlewoodPaleyBlock φ j f, g⟫_ℂ‖ₑ ≤
      (2 * L : ℕ) * ∫⁻ z, (∑' j, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
        (∑' k, ‖littlewoodPaleyBlock φ k g z‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
  set W : ℕ → Finset ℕ := fun j ↦ Finset.Ico (j + 1 - L) (j + L)
  have hWL : ∀ j k, k ∈ W j → |(k : ℤ) - j| < L := fun j k hk ↦
    abs_sub_lt_iff.2 (by simp only [W, Finset.mem_Ico] at hk; omega)
  set B := littlewoodPaleyBlock φ
  have hmeas : ∀ i k, AEMeasurable (fun z ↦ ‖B i f z‖ₑ * ‖B k g z‖ₑ) :=
    fun i k ↦ (Lp.aestronglyMeasurable _).eNorm.mul (Lp.aestronglyMeasurable _).eNorm
  calc ‖⟪∑ j ∈ Finset.range N, B j f, g⟫_ℂ‖ₑ
      = ‖∑ j ∈ Finset.range N, ∑ k ∈ W j, ∫ z, ⟪B j f z, B k g z⟫_ℂ‖ₑ := by
        rw [sum_inner]
        refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
        rw [inner_littlewoodPaleyBlock_eq_sum φ hL]
        simp only [B, W, L2.inner_def]
    _ ≤ ∑ j ∈ Finset.range N, ∑ k ∈ W j, ∫⁻ z, ‖B j f z‖ₑ * ‖B k g z‖ₑ :=
        (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ (eNorm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ (eNorm_integral_le_lintegral_eNorm _).trans
            (lintegral_mono fun z ↦ eNorm_inner_le_eNorm _ _)))
    _ = ∫⁻ z, ∑ j ∈ Finset.range N, ∑ k ∈ W j, ‖B j f z‖ₑ * ‖B k g z‖ₑ := by
        rw [lintegral_finsetSum' _ fun j _ ↦ Finset.aemeasurable_fun_sum _ fun k _ ↦ hmeas j k]
        exact Finset.sum_congr rfl fun j _ ↦
          (lintegral_finsetSum' _ fun k _ ↦ hmeas j k).symm
    _ ≤ ∫⁻ z, (2 * L : ℕ) * ((∑' j, ‖B j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ) *
          (∑' k, ‖B k g z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) :=
        lintegral_mono fun z ↦ (_root_.sum_le_tsum _).trans (ENNReal.tsum_sum_mul_le_of_card_le W
            (fun j ↦ card_le_two_mul_of_abs_sub_lt Nat.cast_injective (hWL j))
            (card_filter_mem_le_two_mul_of_abs_sub_lt Nat.cast_injective hWL) _ _)
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

/-- **The reverse Littlewood–Paley inequality on the torus.** With the notation of
`TauCeti.UnitAddTorus.exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le`, for
`1 < p < ∞` there is a constant `C` such that for every `f ∈ L²(𝕋ᵈ)`,

`‖f‖_p ≤ C ‖(∑ⱼ |Δⱼ f|²)^{1/2}‖_p`.

Neither side is assumed finite, so together with the direct inequality, `f ∈ Lᵖ(𝕋ᵈ)` exactly when
its square function is. -/
theorem exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : L²(UnitAddTorus d),
      eLpNorm f p volume ≤
        C * eLpNorm (fun z ↦ (∑' j, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) p volume := by
  -- The conjugate exponent `q = (1 - p⁻¹)⁻¹` also lies in `(1, ∞)`.
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have : p.HolderConjugate q := ENNReal.HolderConjugate.inv_one_sub_inv' hp.le
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 hp_top.lt_top
  have hq_top : q ≠ (∞ : ℝ≥0∞) := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  obtain ⟨C, hC⟩ := exists_eLpNorm_tsum_enorm_littlewoodPaleyBlock_sq_rpow_le φ hq hq_top
  obtain ⟨L, hL⟩ := φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ
  refine ⟨(2 * L : ℕ) * C, fun f ↦ ?_⟩
  set S : L²(UnitAddTorus d) → UnitAddTorus d → ℝ≥0∞ := fun f z ↦
    (∑' j, ‖littlewoodPaleyBlock φ j f z‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  have hS : ∀ f, AEMeasurable (S f) := fun f ↦
    (AEMeasurable.tsum fun j ↦ (Lp.aestronglyMeasurable _).eNorm.pow_const 2).pow_const _
  -- By duality, it suffices to bound the pairing of `f` with a bounded `g` of finite-measure
  -- support, which is an element `G` of `L²`.
  refine (Lp.aestronglyMeasurable f).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ)
    (q' := q) fun g s hs hgs hg ↦ ?_
  have hg2 : MemLp g 2 volume := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  set G := hg2.toLp g
  have hGg : (G : UnitAddTorus d → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hpair : ∫ z, ⟪f z, g z⟫_ℂ = ⟪f, G⟫_ℂ := by
    rw [L2.inner_def]
    exact integral_congr_ae (hGg.mono fun z hz ↦ by simp only [hz])
  -- Hölder's inequality and the square function inequality at the exponent `q` for `G`.
  have hHolder : ∫⁻ z, S f z * S G z ≤ eLpNorm (S f) p volume * eLpNorm (S G) q volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (μ := volume) (p := p) (q := q)
      (r := 1) (fun a b : ℝ≥0∞ ↦ a * b) 1 (f := S f) (g := S G)
      (fun _ _ ↦ ((hS f).mul (hS G)).aestronglyMeasurable)
      (ae_of_all _ fun z ↦ by simp) zero_lt_one
    rw [eLpNorm_one_eq_lintegral_eNorm (f := fun z ↦ S f z * S G z)
      ((hS f).mul (hS G)).aestronglyMeasurable] at h
    simpa only [eNorm_eq_self, one_mul] using h
  have hSG : eLpNorm (S G) q volume ≤ C * eLpNorm g q volume := by
    rw [← eLpNorm_congr_ae hGg]
    exact hC G
  -- The pairing is the limit of the pairings of the partial sums of `f`.
  have hlim : ‖⟪f, G⟫_ℂ‖ₑ ≤ (2 * L : ℕ) * ∫⁻ z, S f z * S G z :=
    le_of_tendsto' ((continuous_eNorm.tendsto _).comp
      ((tendsto_sum_littlewoodPaleyBlock φ f).inner tendsto_const_nhds))
      fun N ↦ enorm_inner_sum_littlewoodPaleyBlock_le φ hL N f G
  rw [hpair]
  calc ‖⟪f, G⟫_ℂ‖ₑ ≤ (2 * L : ℕ) * ∫⁻ z, S f z * S G z := hlim
    _ ≤ (2 * L : ℕ) * (eLpNorm (S f) p volume * (C * eLpNorm g q volume)) := by
        gcongr
        exact hHolder.trans (by gcongr)
    _ = ↑(((2 * L : ℕ) : ℝ≥0) * C) * eLpNorm (S f) p volume * eLpNorm g q volume := by
        push_cast
        ring

end TauCeti.UnitAddTorus
