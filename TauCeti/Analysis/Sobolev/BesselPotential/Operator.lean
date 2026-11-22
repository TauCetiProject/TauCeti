/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian.Power
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# The directional derivative on Bessel-potential spaces, and real-valued elements

A continuous linear operator `A` on tempered distributions that maps `H^{s,p}(E, F)` into
`H^{r,p}(E, G)` is automatically bounded between these Banach spaces, by the closed graph theorem;
`BesselPotentialSpace.mapCLM` bundles such restrictions. This file applies the construction to the
directional derivative `∂_v : H^{s+1,p}(E, F) → H^{s,p}(E, F)` for `1 < p < ∞`
(`BesselPotentialSpace.lineDerivCLM`), and to the Laplacian `Δ : H^{s+2}(E, F) → H^s(E, F)`
(`BesselPotentialSpace.laplacianCLM`). Combined with
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`, `mapCLM` likewise yields
multiplication by a function with bounded derivatives as a bounded operator on `H^{k,p}`; these
are the linear building blocks of differential operators with nondecaying smooth coefficients on
the Sobolev scale.

For an order `s ≥ -1`, the norm of `H^{s+1,p}` is controlled by the `Lᵖ` norm and the `H^{s,p}`
norms of the first derivatives along an orthonormal basis
(`BesselPotentialSpace.exists_norm_le_mul_norm_inclusionLp_add_sum_norm_lineDerivCLM`). The map
`u ↦ (u, (∂_{b i} u)ᵢ)` into `H^{0,p} × ∏ᵢ H^{s,p}` is injective with closed range, because a
distribution in `H^{0,p}` whose derivatives lie in `H^{s,p}` lies in `H^{s+1,p}`
(`TemperedDistribution.memSobolev_add_one_of_lineDerivOp`, applied one order at a time); the open
mapping theorem bounds its inverse. In particular elements of `H^{s+1,p}` converge as soon as they
converge in `Lᵖ` and their first derivatives converge in `H^{s,p}`
(`BesselPotentialSpace.tendsto_of_tendsto_inclusionLp_of_tendsto_lineDerivCLM`). For `p = 2` the
same holds for smooth families: a family that is `C^n` in `H^s` together with its first
derivatives is `C^n` in `H^{s+1}`
(`BesselPotentialSpace.exists_contDiff_inclusion_eq_of_lineDerivOp_eq`), since
`u = (1 - Δ)⁻¹ (u - ∑ᵢ ∂_{b i} ∂_{b i} u)`.

For `s ≥ 0` an element `u` of `H^{s,p}(E)` is an `Lᵖ` function, `BesselPotentialSpace.inclusionLp`.
The second part of the file describes the operators on these functions when `u` is real-valued:

* a real function `f` lies in `realSobolevFunctions E s p` exactly when `f`, viewed as a complex
  function, is almost everywhere the `Lᵖ` function of some `u ∈ H^{s,p}(E)`
  (`TemperedDistribution.mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq`), which
  `BesselPotentialSpace.ofRealSobolevFunction` chooses;
* if moreover `f` is `C¹`, `1 < p < ∞` and `u ∈ H^{s+1,p}(E)`, then the `Lᵖ` function of `∂_v u`
  is almost everywhere the classical derivative `x ↦ fderiv ℝ f x v`
  (`BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq`);
* if `f` is `C²` and `u ∈ H^{s+2}(E)`, then the `L²` function of `Δu` is almost everywhere the
  classical Laplacian `Δf` (`BesselPotentialSpace.coeFn_inclusionLp_laplacianCLM_ae_eq`);
* if `w` has the tempered distribution `g u` for a bounded function `g` of temperate growth, then
  the `Lᵖ` function of `w` is almost everywhere `g` times that of `u`
  (`BesselPotentialSpace.coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM`).

## Main declarations

* `BesselPotentialSpace.lineDerivCLM`: the directional derivative
  `H^{s+1,p}(E, F) →L[ℂ] H^{s,p}(E, F)` for `1 < p < ∞`.
* `BesselPotentialSpace.laplacianCLM`: the Laplacian `H^{s+2}(E, F) →L[ℂ] H^s(E, F)`.
* `BesselPotentialSpace.ofRealSobolevFunction`: the element of `H^{s,p}(E)` of a real function in
  `realSobolevFunctions E s p`.
* `BesselPotentialSpace.exists_norm_le_mul_norm_inclusionLp_add_sum_norm_lineDerivCLM` and
  `BesselPotentialSpace.tendsto_of_tendsto_inclusionLp_of_tendsto_lineDerivCLM`: the norm of
  `H^{s+1,p}` is controlled by the `Lᵖ` norm and the first derivatives.
* `BesselPotentialSpace.exists_contDiff_inclusion_eq_of_lineDerivOp_eq`: a family that is `C^n`
  in `H^s` together with its first derivatives is `C^n` in `H^{s+1}`.
-/

public section

noncomputable section

open Filter MeasureTheory TemperedDistribution Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

section lineDerivCLM

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **The directional derivative on the Sobolev scale.** For `1 < p < ∞`, the derivative `∂_v` in
the direction `v`, as a bounded operator `H^{s+1,p}(E, F) →L[ℂ] H^{s,p}(E, F)`
(`TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`). -/
def lineDerivCLM (hp : 1 < p) (hp_top : p ≠ ∞) (v : E) :
    H^{s + 1, p}(E, F) →L[ℂ] H^{s, p}(E, F) :=
  mapCLM (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, F) v) fun u ↦ by
    simpa using u.memSobolev_toDistr.lineDerivOp_of_one_lt hp hp_top (m := v)

/-- `lineDerivCLM hp hp_top v` acts on the underlying tempered distributions by `∂_v`. -/
@[simp]
theorem toDistr_lineDerivCLM (hp : 1 < p) (hp_top : p ≠ ∞) (v : E) (u : H^{s + 1, p}(E, F)) :
    (lineDerivCLM hp hp_top v u).toDistr = ∂_{v} u.toDistr := by
  simp [lineDerivCLM]

end lineDerivCLM

section laplacianCLM

open scoped Laplacian

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Laplacian on the Sobolev scale.** The Laplacian `Δ`, as a bounded operator
`H^{s+2}(E, F) →L[ℂ] H^s(E, F)` (`TemperedDistribution.MemSobolev.laplacian`). -/
def laplacianCLM (s : ℝ) : H^{s + 2}(E, F) →L[ℂ] H^{s}(E, F) :=
  mapCLM (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)) fun u ↦ by
    simpa using u.memSobolev_toDistr.laplacian

/-- `laplacianCLM s` acts on the underlying tempered distributions by `Δ`. -/
@[simp]
theorem toDistr_laplacianCLM (s : ℝ) (u : H^{s + 2}(E, F)) :
    (laplacianCLM s u).toDistr = Δ u.toDistr := by
  simp [laplacianCLM]

end laplacianCLM

section Gradient

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {ι : Type*} [Fintype ι]

/-- The map `u ↦ (u, (∂_{b i} u)ᵢ)` from `H^{s+1,p}` to `H^{0,p} × ∏ᵢ H^{s,p}`. -/
private def gradientCLM (hp : 1 < p) (hp_top : p ≠ ∞) (hs : 0 ≤ s + 1)
    (b : OrthonormalBasis ι ℝ E) :
    H^{s + 1, p}(E, F) →L[ℂ] H^{0, p}(E, F) × (ι → H^{s, p}(E, F)) :=
  (inclusion hs).prod (ContinuousLinearMap.pi fun i ↦ lineDerivCLM hp hp_top (b i))

private theorem injective_gradientCLM (hp : 1 < p) (hp_top : p ≠ ∞) (hs : 0 ≤ s + 1)
    (b : OrthonormalBasis ι ℝ E) : Function.Injective (gradientCLM (F := F) hp hp_top hs b) :=
  fun _ _ h ↦ inclusion_injective _ (congrArg Prod.fst h)

/-- The range of `u ↦ (u, (∂_{b i} u)ᵢ)` consists of the pairs whose second entry is the
distributional gradient of the first: a distribution in `H^{0,p}` whose derivatives along an
orthonormal basis lie in `H^{s,p}` lies in `H^{s+1,p}`. -/
private theorem range_gradientCLM (hp : 1 < p) (hp_top : p ≠ ∞) (hs : 0 ≤ s + 1)
    (b : OrthonormalBasis ι ℝ E) : Set.range (gradientCLM (F := F) hp hp_top hs b) =
      {q | ∀ i, ∂_{b i} q.1.toDistr = (q.2 i).toDistr} := by
  ext q
  refine ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨u, rfl⟩ i
    simp [gradientCLM, toDistr_inclusion]
  -- Raise the order of `q.1` one step at a time, through `min (s + 1) n` for `n = 0, 1, …`.
  have hmem (n : ℕ) : MemSobolev (min (s + 1) n) p q.1.toDistr := by
    induction n with
    | zero => exact q.1.memSobolev_toDistr.mono_of_one_lt hp hp_top (by simp)
    | succ n ih =>
      have h := memSobolev_add_one_of_lineDerivOp hp hp_top b
        (ih.mono_of_one_lt hp hp_top (min_le_min (by linarith) le_rfl)) fun i ↦ by
          rw [hq i]
          exact (q.2 i).memSobolev_toDistr.mono_of_one_lt hp hp_top (min_le_left s n)
      rwa [← min_add_add_right, ← Nat.cast_succ] at h
  have hk := hmem ⌈s + 1⌉₊
  rw [min_eq_left (Nat.le_ceil _)] at hk
  refine ⟨hk.toBesselPotentialSpace, Prod.ext (ext ?_) (funext fun i ↦ ext ?_)⟩
  · simp [gradientCLM, toDistr_inclusion, MemSobolev.toBesselPotentialSpace_toDistr]
  · simp [gradientCLM, MemSobolev.toBesselPotentialSpace_toDistr, hq i]

private theorem isClosed_range_gradientCLM (hp : 1 < p) (hp_top : p ≠ ∞) (hs : 0 ≤ s + 1)
    (b : OrthonormalBasis ι ℝ E) :
    IsClosed (Set.range (gradientCLM (F := F) hp hp_top hs b)) := by
  rw [range_gradientCLM, Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_eq
    ((LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, F) (b i)).continuous.comp
      (continuous_toDistr.comp continuous_fst))
    (continuous_toDistr.comp ((continuous_apply i).comp continuous_snd))

/-- **The `H^{s+1,p}` norm is controlled by the `Lᵖ` norm and the first derivatives.** For
`1 < p < ∞`, an order `s ≥ -1` and an orthonormal basis `b`, there is a constant `C` with
`‖u‖_{H^{s+1,p}} ≤ C (‖u‖_{Lᵖ} + ∑ᵢ ‖∂_{b i} u‖_{H^{s,p}})` for every `u ∈ H^{s+1,p}(E, F)`. -/
theorem exists_norm_le_mul_norm_inclusionLp_add_sum_norm_lineDerivCLM (hp : 1 < p)
    (hp_top : p ≠ ∞) (hs : 0 ≤ s + 1) (b : OrthonormalBasis ι ℝ E) :
    ∃ C, ∀ u : H^{s + 1, p}(E, F), ‖u‖ ≤ C * (‖inclusionLp hs u‖ +
      ∑ i, ‖lineDerivCLM hp hp_top (b i) u‖) := by
  obtain ⟨K, hK⟩ :=
    (gradientCLM (F := F) hp hp_top hs b).antilipschitz_of_injective_of_isClosed_range
      (injective_gradientCLM hp hp_top hs b) (isClosed_range_gradientCLM hp hp_top hs b)
  refine ⟨K, fun u ↦ ?_⟩
  have h := hK.le_mul_dist u 0
  rw [dist_zero_right, map_zero, dist_zero_right] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ K.property)
  rw [gradientCLM, ContinuousLinearMap.prod_apply, Prod.norm_def]
  refine max_le ?_ ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_)
  · rw [← norm_toLp_eq, toLp_inclusion]
    exact le_add_of_nonneg_right (by positivity)
  · exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (norm_nonneg _))

/-- **Convergence in `H^{s+1,p}` from convergence of the function and its first derivatives.**
For `1 < p < ∞` and `s ≥ -1`, elements `u a` of `H^{s+1,p}(E, F)` converge to `u₀` as soon as they
converge in `Lᵖ` and their derivatives along an orthonormal basis converge in `H^{s,p}`. -/
theorem tendsto_of_tendsto_inclusionLp_of_tendsto_lineDerivCLM (hp : 1 < p) (hp_top : p ≠ ∞)
    (hs : 0 ≤ s + 1) (b : OrthonormalBasis ι ℝ E) {α : Type*} {l : Filter α}
    {u : α → H^{s + 1, p}(E, F)} {u₀ : H^{s + 1, p}(E, F)}
    (h₀ : Tendsto (fun a ↦ inclusionLp hs (u a)) l (𝓝 (inclusionLp hs u₀)))
    (hd : ∀ i, Tendsto (fun a ↦ lineDerivCLM hp hp_top (b i) (u a)) l
      (𝓝 (lineDerivCLM hp hp_top (b i) u₀))) :
    Tendsto u l (𝓝 u₀) := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_inclusionLp_add_sum_norm_lineDerivCLM (F := F)
    hp hp_top hs b
  rw [tendsto_iff_norm_sub_tendsto_zero] at h₀ ⊢
  have hd' (i : ι) := tendsto_iff_norm_sub_tendsto_zero.1 (hd i)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun a ↦ ?_) (by
    simpa using (h₀.add (tendsto_finsetSum Finset.univ fun i _ ↦ hd' i)).const_mul C)
  simpa only [map_sub] using hC (u a - u₀)

end Gradient

section ContDiff

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ}
  {ι : Type*} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}

/-- The tempered distribution of a finite sum is the sum of the tempered distributions. -/
@[simp]
theorem toDistr_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] (t : Finset ι) (u : ι → H^{s, p}(E, F)) :
    (∑ i ∈ t, u i).toDistr = ∑ i ∈ t, (u i).toDistr := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [toDistr_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toDistr_add, ih]

variable [Fintype ι]

/-- **Smooth families in `H^{s+1}` from their first derivatives.** Let `b` be an orthonormal basis
of `E`, and let `w` be a `C^n` map into `H^s(E, F)` whose distributional derivatives `∂_{b i} w`
are given by `C^n` maps `w' i` into `H^s(E, F)`. Then `w` is a `C^n` map into `H^{s+1}(E, F)`:
there is a `C^n` map `u` into `H^{s+1}(E, F)` with `u x = w x` in `H^s(E, F)`. Indeed
`u = (1 - Δ)⁻¹ (w - ∑ᵢ ∂_{b i} w' i)`, where `(1 - Δ)⁻¹` maps `H^{s-1}` boundedly to `H^{s+1}`. -/
theorem exists_contDiff_inclusion_eq_of_lineDerivOp_eq (b : OrthonormalBasis ι ℝ E)
    {w : X → H^{s}(E, F)} {w' : ι → X → H^{s}(E, F)} (hw : ContDiff ℝ n w)
    (hw' : ∀ i, ContDiff ℝ n (w' i)) (hd : ∀ x i, ∂_{b i} (w x).toDistr = (w' i x).toDistr) :
    ∃ u : X → H^{s + 1}(E, F), ContDiff ℝ n u ∧
      ∀ x, inclusion (by linarith : s ≤ s + 1) (u x) = w x := by
  -- `(1 - Δ)⁻¹ : H^s → H^{s+1}`, and `(1 - Δ)⁻¹ ∂_{b i} : H^s → H^{s+1}`.
  set R₀ : H^{s}(E, F) →L[ℂ] H^{s + 1}(E, F) :=
    mapCLM (laplacianResolvent F 1) fun v ↦
      (v.memSobolev_toDistr.laplacianResolvent one_pos).mono (by linarith)
  set R : ι → H^{s}(E, F) →L[ℂ] H^{s + 1}(E, F) := fun i ↦
    mapCLM ((laplacianResolvent F 1).comp (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, F) (b i))) fun v ↦ by
      have h := (v.memSobolev_toDistr.lineDerivOp_of_one_lt ENNReal.one_lt_two
        ENNReal.ofNat_ne_top (m := b i)).laplacianResolvent one_pos
      rw [show s - 1 + 2 = s + 1 by ring] at h
      simpa using h
  refine ⟨fun x ↦ R₀ (w x) - ∑ i, R i (w' i x), ((R₀.restrictScalars ℝ).contDiff.comp hw).sub
    (ContDiff.sum fun i _ ↦ ((R i).restrictScalars ℝ).contDiff.comp (hw' i)), fun x ↦ ext ?_⟩
  simp only [toDistr_inclusion, toDistr_sub, toDistr_sum, R₀, R, toDistr_mapCLM,
    ContinuousLinearMap.comp_apply, LineDeriv.lineDerivOpCLM_apply, ← hd, ← map_sum, ← map_sub,
    ← laplacian_eq_sum b]
  rw [show (w x).toDistr - Δ (w x).toDistr = -Δ (w x).toDistr + (1 : ℝ) • (w x).toDistr by
    rw [one_smul]; abel, laplacianResolvent_neg_laplacian_add_smul one_pos]

end ContDiff

end BesselPotentialSpace

/-! ### Real-valued elements -/

namespace TemperedDistribution

/-- **Real Sobolev functions are elements of `H^{s,p}(E)`.** For `s ≥ 0`, a real function `f` lies
in `realSobolevFunctions E s p` exactly when the complex function `x ↦ (f x : ℂ)` is almost
everywhere the `Lᵖ` function of an element of `H^{s,p}(E)`. -/
theorem mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hs : 0 ≤ s) {f : E → ℝ} :
    f ∈ realSobolevFunctions E s p ↔
      ∃ u : H^{s, p}(E), ⇑(BesselPotentialSpace.inclusionLp hs u) =ᵐ[volume]
        fun x ↦ (f x : ℂ) := by
  constructor
  · rintro hf
    obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
    refine ⟨hu.toBesselPotentialSpace, ?_⟩
    rw [(BesselPotentialSpace.inclusionLp_eq_iff hs (f := Complex.ofRealCLM.compLp u)).2 (by simp)]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u, huf]
      with x h h'
    rw [h, Complex.ofRealCLM_apply, h']
  · rintro ⟨u, hu⟩
    refine mem_realSobolevFunctions_of_ae_eq_ofReal ?_ hu
    rw [BesselPotentialSpace.toTemperedDistribution_inclusionLp]
    exact u.memSobolev_toDistr

end TemperedDistribution

namespace BesselPotentialSpace

/-- **The element of `H^{s,p}(E)` of a real Sobolev function.** For `s ≥ 0` and a real function
`f ∈ realSobolevFunctions E s p`, the element of `H^{s,p}(E)` whose `Lᵖ` function is
`x ↦ (f x : ℂ)` (`BesselPotentialSpace.coeFn_inclusionLp_ofRealSobolevFunction`). -/
def ofRealSobolevFunction {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hs : 0 ≤ s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s p) : H^{s, p}(E) :=
  ((mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq hs).1 hf).choose

/-- The `Lᵖ` function of `ofRealSobolevFunction hs hf` is `x ↦ (f x : ℂ)`. -/
theorem coeFn_inclusionLp_ofRealSobolevFunction {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hs : 0 ≤ s)
    {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s p) :
    ⇑(inclusionLp hs (ofRealSobolevFunction hs hf)) =ᵐ[volume] fun x ↦ (f x : ℂ) :=
  ((mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq hs).1 hf).choose_spec

/-- An element of `H^{s,p}(E)` whose `Lᵖ` function is almost everywhere `x ↦ (f x : ℂ)` is
`ofRealSobolevFunction hs hf`. -/
theorem eq_ofRealSobolevFunction_of_ae {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hs : 0 ≤ s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s p) {w : H^{s, p}(E)}
    (hw : ⇑(inclusionLp hs w) =ᵐ[volume] fun x ↦ (f x : ℂ)) :
    w = ofRealSobolevFunction hs hf :=
  inclusionLp_injective hs <| Lp.ext <|
    hw.trans (coeFn_inclusionLp_ofRealSobolevFunction hs hf).symm

/-- **Classical derivatives of real elements of `H^{s+1,p}`.** For `1 < p < ∞` and `s ≥ 0`, if the
`Lᵖ` function of `u ∈ H^{s+1,p}(E)` is almost everywhere a real `C¹` function `f`, then the `Lᵖ`
function of the derivative `∂_v u ∈ H^{s,p}(E)` is almost everywhere its classical derivative
`x ↦ fderiv ℝ f x v`. -/
theorem coeFn_inclusionLp_lineDerivCLM_ae_eq {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) (hs : 0 ≤ s) {f : E → ℝ} (hf : ContDiff ℝ 1 f) {u : H^{s + 1, p}(E)}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] fun x ↦ (f x : ℂ)) (v : E) :
    ⇑(inclusionLp hs (lineDerivCLM hp hp_top v u)) =ᵐ[volume] fun x ↦ (fderiv ℝ f x v : ℂ) := by
  have hmem := (mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq (by linarith)).2 ⟨u, hu⟩
  obtain ⟨u₀, hu₀f, -⟩ := mem_realSobolevFunctions.1 hmem
  obtain ⟨u', hu'f, -⟩ := mem_realSobolevFunctions.1
    (fderiv_apply_mem_realSobolevFunctions hp hp_top hs hf hmem v)
  -- The tempered distribution of `u` is that of the real function `u₀`.
  have hu₀ : u.toDistr = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u₀) := by
    rw [← toTemperedDistribution_inclusionLp (by linarith : 0 ≤ s + 1)]
    congr 1
    refine Lp.ext ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u₀, hu₀f, hu]
      with x h h' h''
    rw [h'', h, Complex.ofRealCLM_apply, h']
  have hd : inclusionLp hs (lineDerivCLM hp hp_top v u) = Complex.ofRealCLM.compLp u' := by
    rw [inclusionLp_eq_iff, toDistr_lineDerivCLM, hu₀,
      TauCeti.lineDerivOp_toTemperedDistribution_ofReal_eq_of_contDiff hf hu₀f hu'f]
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u', hu'f] with x h h'
  rw [hd, h, Complex.ofRealCLM_apply, h']

/-- **The classical Laplacian of real elements of `H^{s+2}`.** For `s ≥ 0`, if the `L²` function
of `u ∈ H^{s+2}(E)` is almost everywhere a real `C²` function `f`, then the `L²` function of
`Δu ∈ H^s(E)` is almost everywhere the classical Laplacian `Δf`. In particular `Δf` is square
integrable. -/
theorem coeFn_inclusionLp_laplacianCLM_ae_eq {s : ℝ} (hs : 0 ≤ s) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {u : H^{s + 2}(E)}
    (hu : ⇑(inclusionLp (by linarith) u) =ᵐ[volume] fun x ↦ (f x : ℂ)) :
    ⇑(inclusionLp hs (laplacianCLM s u)) =ᵐ[volume] fun x ↦ (Δ f x : ℂ) := by
  set b := stdOrthonormalBasis ℝ E
  set u' : H^{s + 1 + 1}(E) := u.copy (s + 1 + 1) (by ring)
  set D : E → H^{s + 1}(E) →L[ℂ] H^{s}(E) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
  set D' : E → H^{s + 1 + 1}(E) →L[ℂ] H^{s + 1}(E) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
  have hu' : ⇑(inclusionLp (by linarith) u') =ᵐ[volume] fun x ↦ (f x : ℂ) := by
    have h : inclusionLp (by linarith : (0 : ℝ) ≤ s + 1 + 1) u' = inclusionLp (by linarith) u := by
      rw [inclusionLp_eq_iff, toTemperedDistribution_inclusionLp]
      exact (toDistr_copy u (by ring : s + 2 = s + 1 + 1)).symm
    rwa [h]
  -- Each second derivative `∂_{b i} ∂_{b i} u` is the classical one.
  have hd (i : _) : ⇑(inclusionLp hs (D (b i) (D' (b i) u'))) =ᵐ[volume]
      fun x ↦ (fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) : ℂ) :=
    coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top hs
      ((hf.fderiv_right le_rfl).clm_apply contDiff_const)
      (coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top (by linarith)
        (hf.of_le one_le_two) hu' (b i)) (b i)
  -- `Δu` is the sum of the second derivatives `∂_{b i} ∂_{b i} u`.
  have hsum : laplacianCLM s u = ∑ i, D (b i) (D' (b i) u') := by
    refine ext ?_
    have hmap := map_sum (toDistrCLM E ℂ s 2) (fun i ↦ D (b i) (D' (b i) u')) Finset.univ
    simp only [toDistrCLM_apply] at hmap
    rw [hmap, toDistr_laplacianCLM, TemperedDistribution.laplacian_eq_sum b]
    have hcopy : u'.toDistr = u.toDistr := toDistr_copy u (by ring)
    simp only [D, D', toDistr_lineDerivCLM, hcopy]
  rw [hsum, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun i ↦ inclusionLp hs (D (b i) (D' (b i) u')),
    ae_all_iff.2 hd] with x h₁ h₂
  rw [h₁, TauCeti.laplacian_eq_sum_fderiv_fderiv_apply b
    ((hf.fderiv_right le_rfl).differentiable one_ne_zero x), Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ ↦ h₂ i

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {r s : ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **Multiplication by a bounded function on `Lᵖ` functions.** For `r, s ≥ 0`, if
`w ∈ H^{r,p}(E, F)` has the tempered distribution `g u` of `u ∈ H^{s,p}(E, F)`, for a bounded
function `g` of temperate growth, then the `Lᵖ` function of `w` is almost everywhere `g` times
that of `u`. -/
theorem coeFn_inclusionLp_ae_eq_smul_of_toDistr_eq_smulLeftCLM (hr : 0 ≤ r) (hs : 0 ≤ s)
    {g : E → ℂ} (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    {u : H^{s, p}(E, F)} {w : H^{r, p}(E, F)} (hw : w.toDistr = smulLeftCLM F g u.toDistr) :
    ⇑(inclusionLp hr w) =ᵐ[volume] fun x ↦ g x • inclusionLp hs u x := by
  have hmem : MemLp g ⊤ (volume : Measure E) :=
    memLp_top_of_bound hg.1.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  have h : inclusionLp hr w = hmem.toLp g • inclusionLp hs u := by
    rw [inclusionLp_eq_iff, Lp.toTemperedDistribution_smul_eq hg hmem, hw,
      toTemperedDistribution_inclusionLp]
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := p) (r := p) (hmem.toLp g) (inclusionLp hs u),
    hmem.coeFn_toLp] with x h₁ h₂
  rw [h, h₁, Pi.smul_apply', h₂]

end BesselPotentialSpace
