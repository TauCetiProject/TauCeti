/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.StandardKernel
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.StrongType

/-!
# Calderón–Zygmund operators on a finite-dimensional inner product space

The Calderón–Zygmund theorems
(`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`,
`TauCeti.exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le`) are stated on
`ℝⁿ = ι → ℝ` with the sup distance, because the Calderón–Zygmund decomposition runs on dyadic
cubes. The singular integral kernels of analysis, such as the second derivatives `D²Gₙ (x - y)` of
the Newtonian kernel, are instead estimated in the Euclidean distance. This file states the
theorems on a finite-dimensional real inner product space `V` of dimension `n ≥ 1`, with its
Lebesgue measure `volume`.

Let `T` be a bounded linear operator on `L²(V)` given off the support of its argument by a kernel
`K`: if `b ∈ L²` vanishes off a compact set `s`, then `T b x = ∫ K x y (b y) dy` for almost every
`x ∉ s`. Let `K` be a **standard kernel**: for some `δ > 0` it satisfies the size estimate and the
smoothness estimate

`‖K x y‖ ≤ C₀ ‖x - y‖ ^ (-n)` for `x ≠ y`, and
`‖K x y - K x y'‖ ≤ C ‖y - y'‖ ^ δ ‖x - y'‖ ^ (-(n + δ))` whenever `‖x - y'‖ > 2 ‖y - y'‖`.

Then `T` is of weak type `(1, 1)`
(`ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`). If moreover the
adjoint `T†` has a standard kernel, then for every `1 < p < ∞` there is a constant `C` with
`‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L²`
(`ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`).

An orthonormal basis `b` identifies `ι → ℝ` with `V` through `x ↦ ∑ xᵢ bᵢ`, preserving Lebesgue
measure, and precomposition with it conjugates `T` to an operator on `L²(ι → ℝ)` whose kernel is
`K` in coordinates. Since `‖x‖_∞ ≤ ‖∑ xᵢ bᵢ‖ ≤ √n ‖x‖_∞`, the coordinate kernel satisfies the
smoothness estimate for the sup distance only when `dist x y' > 2 √n dist y y'`, and the size
estimate extends it to `dist x y' > 2 dist y y'`
(`TauCeti.norm_sub_le_mul_rpow_of_norm_le_mul_rpow`). The kernel representation is assumed off
compact sets, rather than off balls of `V`, because a sup-distance ball of `ι → ℝ` is a cube of `V`.

Kernels that are not standard, such as the kernels of the Fourier multipliers of the
Mihlin–Hörmander theorem, often satisfy only **Hörmander's condition**

`∫_{‖x - y'‖ > 2 ‖y - y'‖} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`.

Without a size estimate, the region `‖x - y'‖ > 2 ‖y - y'‖` cannot be enlarged, so this is used
with the cancellation condition in coordinates for the dilation factor `2 √n`: the complement of
the sup-distance ball of radius `2 √n r` around the centre of a cube of `V` lies in the region of
Hörmander's condition for every point of the cube. The resulting weak type `(1, 1)` and strong
type `(p, p)` bounds (`TauCeti.exists_mul_volume_lt_enorm_le_of_hormander`,
`TauCeti.exists_eLpNorm_le_of_hormander`) have constants depending only on `n`, `p`,
`B` and a bound for `‖T‖`, so they hold uniformly over families of operators.

## Main declarations

* `ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`: an operator on
  `L²(V)` with a standard kernel is of weak type `(1, 1)`.
* `ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`: an operator on `L²(V)` such that
  both it and its adjoint have standard kernels is bounded in the `Lᵖ` norm for `1 < p < ∞`.
* `TauCeti.exists_mul_volume_lt_enorm_le_of_hormander`: operators on `L²(V)` with
  kernels satisfying Hörmander's condition are of weak type `(1, 1)`, uniformly.
* `TauCeti.exists_eLpNorm_le_of_hormander`: operators on `L²(V)` such that both they
  and their adjoints have kernels satisfying Hörmander's condition are bounded in the `Lᵖ` norm
  for `1 < p < ∞`, uniformly.

## References

* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
* L. Grafakos, *Classical Fourier Analysis*, Sections 5.3 and 5.4.
* L. Hörmander, *Estimates for translation invariant operators in Lᵖ spaces*, Acta Math. **104**
  (1960), 93–140.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti WithLp
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V]

section Coordinates

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- The coordinate map `x ↦ ∑ xᵢ bᵢ` of an orthonormal basis, as a measurable equivalence. -/
private noncomputable def coord : (ι → ℝ) ≃ᵐ V :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).trans b.measurableEquiv.symm

private theorem coord_apply (x : ι → ℝ) : coord b x = b.repr.symm (toLp 2 x) := rfl

private theorem continuous_coord : Continuous (coord b) :=
  b.repr.symm.continuous.comp (PiLp.continuous_toLp 2 _)

/-- The coordinate map does not decrease distances, measured in the sup distance on `ι → ℝ`. -/
private theorem dist_le_dist_coord (x x' : ι → ℝ) : dist x x' ≤ dist (coord b x) (coord b x') := by
  rw [coord_apply, coord_apply, LinearIsometryEquiv.dist_map]
  simpa using (PiLp.lipschitzWith_ofLp 2 (fun _ : ι => ℝ)).dist_le_mul (toLp 2 x) (toLp 2 x')

/-- The coordinate map increases distances by at most the factor `√n`. -/
private theorem dist_coord_le (x x' : ι → ℝ) :
    dist (coord b x) (coord b x') ≤ NNReal.sqrt (Fintype.card ι) * dist x x' := by
  rw [coord_apply, coord_apply, LinearIsometryEquiv.dist_map]
  have h := (PiLp.lipschitzWith_toLp 2 (fun _ : ι => ℝ)).dist_le_mul x x'
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  rwa [NNReal.sqrt_eq_rpow]

/-- **A standard kernel in coordinates.** If `k` satisfies the size and smoothness estimates on
`V`, then `k` in coordinates satisfies the smoothness estimate for the sup distance on `ι → ℝ`,
with the constant `C √n ^ δ + 2 C₀ (2 √n) ^ (n + δ)`. -/
private theorem norm_coord_sub_le [Nonempty ι] {G : Type*} [SeminormedAddGroup G]
    {k : V → V → G} {C₀ C : ℝ≥0} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(Fintype.card ι : ℝ)))
    (hk : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Fintype.card ι + δ))))
    {x y y' : ι → ℝ} (h : 2 * dist y y' < dist x y') :
    ‖k (coord b x) (coord b y) - k (coord b x) (coord b y')‖ ≤
      (C * NNReal.sqrt (Fintype.card ι) ^ δ +
          2 * C₀ * (2 * NNReal.sqrt (Fintype.card ι)) ^ (Fintype.card ι + δ) : ℝ≥0) *
        (dist y y' ^ δ * dist x y' ^ (-(Fintype.card ι + δ))) := by
  set e := coord b
  set n : ℝ := (Fintype.card ι : ℝ)
  set L := NNReal.sqrt (Fintype.card ι)
  have hL : 1 ≤ L := NNReal.one_le_sqrt.2 (by exact_mod_cast Fintype.card_pos)
  -- Euclidean distances dominate sup distances, so the size estimate holds in coordinates.
  have hsize' : ∀ x y, 0 < dist x y → ‖k (e x) (e y)‖ ≤ C₀ * dist x y ^ (-n) := fun x y hxy => by
    have h := dist_le_dist_coord b x y
    refine (hsize _ _ (dist_pos.1 (hxy.trans_le h))).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hxy h (by simp [n]))
      C₀.coe_nonneg
  -- Euclidean distances are at most `√n` times sup distances, so the smoothness estimate holds
  -- in coordinates for the factor `2 √n`.
  have hsmooth : ∀ x y y', (2 * L : ℝ≥0) * dist y y' < dist x y' →
      ‖k (e x) (e y) - k (e x) (e y')‖ ≤
        (C * L ^ δ : ℝ≥0) * (dist y y' ^ δ * dist x y' ^ (-(n + δ))) := by
    intro x y y' h
    have h₁ : dist (e y) (e y') ≤ L * dist y y' := dist_coord_le b y y'
    have h₂ : dist x y' ≤ dist (e x) (e y') := dist_le_dist_coord b x y'
    have hxy' : 0 < dist x y' := lt_of_le_of_lt (by positivity) h
    push_cast at h ⊢
    refine (hk _ _ _ (by linarith)).trans ?_
    have h₃ : dist (e y) (e y') ^ δ ≤ (L : ℝ) ^ δ * dist y y' ^ δ := by
      rw [← Real.mul_rpow L.coe_nonneg dist_nonneg]
      exact Real.rpow_le_rpow dist_nonneg h₁ hδ
    have h₄ : dist (e x) (e y') ^ (-(n + δ)) ≤ dist x y' ^ (-(n + δ)) :=
      Real.rpow_le_rpow_of_nonpos hxy' h₂ (by simp only [n]; linarith)
    calc (C : ℝ) * (dist (e y) (e y') ^ δ * dist (e x) (e y') ^ (-(n + δ)))
        ≤ C * ((L ^ δ * dist y y' ^ δ) * dist x y' ^ (-(n + δ))) := by gcongr
      _ = C * L ^ δ * (dist y y' ^ δ * dist x y' ^ (-(n + δ))) := by ring
  exact norm_sub_le_mul_rpow_of_norm_le_mul_rpow (K := fun x y => k (e x) (e y))
    (by positivity) (by positivity) (le_mul_of_one_le_right zero_le_two hL) hsize' hsmooth h

variable [FiniteDimensional ℝ V]

private theorem measurePreserving_coord : MeasurePreserving (coord b) :=
  b.measurePreserving_measurableEquiv.symm.comp (PiLp.volume_preserving_toLp ι)

/-- Precomposition with the coordinate map, as an isometric equivalence of `L²` spaces. -/
private noncomputable def lpCoord (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 (volume : Measure V) ≃ₗᵢ[ℝ] Lp E 2 (volume : Measure (ι → ℝ)) :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_coord b)
    (measurePreserving_coord b).symm (.of_forall fun v => (coord b).apply_symm_apply v)

private theorem coeFn_lpCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume : Measure V)) : lpCoord b E f =ᵐ[volume] f ∘ coord b :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv ..

private theorem coeFn_lpCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    (lpCoord b E).symm f =ᵐ[volume] f ∘ (coord b).symm :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv_symm ..

private theorem eLpNorm_lpCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume : Measure V)) (p : ℝ≥0∞) :
    eLpNorm (lpCoord b E f) p volume = eLpNorm f p volume :=
  (eLpNorm_congr_ae (coeFn_lpCoord b f)).trans
    (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (measurePreserving_coord b))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- An operator on `L²(V)` in coordinates, as an operator on `L²(ι → ℝ)`. -/
private noncomputable def coordConj
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) :
    Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)) :=
  (lpCoord b F : Lp F 2 (volume : Measure V) →L[ℝ] _) ∘L T ∘L
    ((lpCoord b E).symm : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] _)

private theorem coordConj_apply
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    coordConj b T f = lpCoord b F (T ((lpCoord b E).symm f)) := rfl

private theorem coordConj_lpCoord
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    (f : Lp E 2 (volume : Measure V)) :
    coordConj b T (lpCoord b E f) = lpCoord b F (T f) := by
  rw [coordConj_apply, LinearIsometryEquiv.symm_apply_apply]

private theorem adjoint_coordConj {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (T : Lp H 2 (volume : Measure V) →L[ℝ] Lp K 2 (volume : Measure V)) :
    adjoint (coordConj b T) = coordConj b (adjoint T) := by
  simp only [coordConj, adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, comp_assoc]

/-- **The kernel representation in coordinates.** If `T` is given by the kernel `k` off compact
sets, then `T` in coordinates is given by `k` in coordinates off sup-distance balls. -/
private theorem coordConj_ae_eq_integral
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) {k : V → V → E →L[ℝ] F}
    (hrep : ∀ (f : Lp E 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z))
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ)
    (hf : ∀ᵐ x, x ∉ closedBall y r → f x = 0) :
    ∀ᵐ x, x ∉ closedBall y r → coordConj b T f x = ∫ z, k (coord b x) (coord b z) (f z) := by
  set e := coord b
  have he := measurePreserving_coord b
  set g := (lpCoord b E).symm f
  have hg := coeFn_lpCoord_symm b f
  -- `g = f ∘ e⁻¹` vanishes off the compact image of the ball.
  have hs : IsCompact (e '' closedBall y r) :=
    (isCompact_closedBall y r).image (continuous_coord b)
  have hgs : ∀ᵐ v, v ∉ e '' closedBall y r → g v = 0 := by
    filter_upwards [hg, he.symm.quasiMeasurePreserving.ae hf] with v hv hv' hvs
    rw [hv]
    exact hv' fun hmem => hvs ⟨e.symm v, hmem, e.apply_symm_apply v⟩
  have hge : g ∘ e =ᵐ[volume] f := by
    filter_upwards [he.quasiMeasurePreserving.ae_eq_comp hg] with x hx
    simpa using hx
  filter_upwards [coeFn_lpCoord b (T g), he.quasiMeasurePreserving.ae (hrep g _ hs hgs)]
    with x hx hrepx hxr
  rw [coordConj_apply, hx, Function.comp_apply,
    hrepx fun ⟨z, hz, hzx⟩ => hxr (e.injective hzx ▸ hz),
    ← he.integral_comp' (fun z => k (e x) z (g z))]
  exact integral_congr_ae (hge.mono fun z hz => congrArg (k (e x) (e z)) hz)

/-- Conjugating by the coordinate map preserves the operator norm. -/
private theorem enorm_coordConj
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) :
    ‖coordConj b T‖ₑ = ‖T‖ₑ := by
  simp only [coordConj, enorm_eq_nnnorm, opNNNorm_linearIsometryEquiv_comp]
  exact congrArg _ (opNNNorm_comp_linearIsometryEquiv T (lpCoord b E).symm)

/-- A weak type `(1, 1)` bound for `T` in coordinates is a weak type `(1, 1)` bound for `T`, with
the same constant. -/
private theorem mul_volume_lt_enorm_le_of_coordConj
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V)) {A : ℝ≥0∞}
    (hA : ∀ (f : Lp E 2 (volume : Measure (ι → ℝ))) (t : ℝ≥0∞),
      t * volume {x | t < ‖coordConj b T f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ)
    (f : Lp E 2 (volume : Measure V)) (t : ℝ≥0∞) :
    t * volume {x | t < ‖T f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ := by
  have he := measurePreserving_coord b
  have h := hA (lpCoord b E f) t
  -- Transfer the level set of `T' (f ∘ e) = (T f) ∘ e` and the `L¹` norm of `f ∘ e` back to `V`.
  have hS : MeasurableSet {v | t < ‖T f v‖ₑ} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable (T f)).enorm
  have hlevel : volume {x | t < ‖coordConj b T (lpCoord b E f) x‖ₑ} =
      volume {v | t < ‖T f v‖ₑ} := by
    rw [← he.measure_preimage hS.nullMeasurableSet]
    refine measure_congr ?_
    filter_upwards [coeFn_lpCoord b (T f)] with x hx
    simp only [coordConj_lpCoord, hx, Function.comp_apply, mem_ofPred_eq, mem_preimage]
  have hnorm : ∫⁻ x, ‖lpCoord b E f x‖ₑ = ∫⁻ v, ‖f v‖ₑ := by
    rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
      ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _), eLpNorm_lpCoord]
  rwa [hlevel, hnorm] at h

variable [CompleteSpace E] [CompleteSpace F]

/-- **The cancellation condition in coordinates.** If `T` has a standard kernel on `V`, the
operator `T` in coordinates satisfies the cancellation condition of the Calderón–Zygmund theorem
on `ι → ℝ` with a finite constant. -/
private theorem exists_cancellation [Nonempty ι]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    {k : V → V → E →L[ℝ] F} (hkm : StronglyMeasurable (Function.uncurry k)) {C₀ C : ℝ≥0}
    {δ : ℝ} (hδ : 0 < δ)
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(Module.finrank ℝ V : ℝ)))
    (hk : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))))
    (hrep : ∀ (f : Lp E 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z)) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ (f : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → f x = 0) → ∫ x, f x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖coordConj b T f x‖ₑ ≤ B * ∫⁻ x, ‖f x‖ₑ := by
  have hn : Module.finrank ℝ V = Fintype.card ι := Module.finrank_eq_card_basis b.toBasis
  rw [hn] at hsize hk
  have he := measurePreserving_coord b
  refine ⟨_, ?_, setLIntegral_compl_closedBall_enorm_apply_le_of_hormander (coordConj b T)
    (K := fun x y => k (coord b x) (coord b y))
    (hkm.comp_measurable (he.measurable.prodMap he.measurable))
    (fun y y' => setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi
      (K := fun x y => k (coord b x) (coord b y)) hδ fun x => norm_coord_sub_le b hδ.le hsize hk)
    (coordConj_ae_eq_integral b T hrep)⟩
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

/-- **Hörmander's condition in coordinates.** If `T` is given off compact sets by a kernel `k`
satisfying Hörmander's condition for the distance of `V`, then `T` in coordinates satisfies the
cancellation condition of the Calderón–Zygmund theorem on `ι → ℝ` with dilation factor `2 √n` and
the same constant. A sup-distance ball of radius `r` lies in the Euclidean ball of radius `√n r`
with the same centre, and the complement of the sup-distance ball of radius `2 √n r` lies in the
complement of the Euclidean ball of radius `2 √n r`, where Hörmander's condition applies. -/
private theorem setLIntegral_compl_closedBall_enorm_coordConj_le_of_hormander
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    {k : V → V → E →L[ℝ] F} (hkm : StronglyMeasurable (Function.uncurry k)) {B : ℝ≥0∞}
    (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖k x y - k x y'‖ₑ ≤ B)
    (hrep : ∀ (f : Lp E 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z))
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ)
    (hf : ∀ᵐ x, x ∉ closedBall y r → f x = 0) (hmean : ∫ x, f x = 0) :
    ∫⁻ x in (closedBall y (2 * NNReal.sqrt (Fintype.card ι) * r))ᶜ, ‖coordConj b T f x‖ₑ ≤
      B * ∫⁻ x, ‖f x‖ₑ := by
  set e := coord b
  set L : ℝ := (NNReal.sqrt (Fintype.card ι) : ℝ)
  have he := measurePreserving_coord b
  set g := (lpCoord b E).symm f
  have hge : g ∘ e =ᵐ[volume] f := by
    filter_upwards [he.quasiMeasurePreserving.ae_eq_comp (coeFn_lpCoord_symm b f)] with x hx
    simpa using hx
  -- `g = f ∘ e⁻¹` vanishes off the Euclidean ball of radius `√n r`, and has integral zero.
  have hgs : ∀ᵐ v, v ∉ closedBall (e y) (L * r) → g v = 0 := by
    filter_upwards [coeFn_lpCoord_symm b f, he.symm.quasiMeasurePreserving.ae hf]
      with v hv hv' hvs
    rw [hv]
    refine hv' fun hmem => hvs ?_
    rw [mem_closedBall] at hmem ⊢
    calc dist v (e y) = dist (e (e.symm v)) (e y) := by rw [e.apply_symm_apply]
      _ ≤ L * dist (e.symm v) y := dist_coord_le b _ _
      _ ≤ L * r := by gcongr
  have : IsFiniteMeasure (volume.restrict (closedBall (e y) (L * r))) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hg : Integrable g := IntegrableOn.integrable_of_ae_notMem_eq_zero
    (((Lp.memLp g).restrict _).integrable one_le_two) hgs
  have hgmean : ∫ v, g v = 0 := by
    rw [← he.integral_comp' (fun v => g v), ← hmean]
    exact integral_congr_ae hge
  have hcanc := TauCeti.setLIntegral_compl_closedBall_enorm_le_of_hormander hkm hB hg hgs hgmean
    (hrep g _ (isCompact_closedBall _ _) hgs)
  -- Transfer back to coordinates, where `T` in coordinates is `(T g) ∘ e`.
  have hsub : (closedBall y (2 * L * r))ᶜ ⊆ e ⁻¹' (closedBall (e y) (2 * (L * r)))ᶜ :=
    fun x hx hx' => hx <| by
      rw [mem_closedBall, ← mul_assoc] at hx'
      exact (dist_le_dist_coord b x y).trans hx'
  calc ∫⁻ x in (closedBall y (2 * L * r))ᶜ, ‖coordConj b T f x‖ₑ
      ≤ ∫⁻ x in e ⁻¹' (closedBall (e y) (2 * (L * r)))ᶜ, ‖coordConj b T f x‖ₑ :=
        lintegral_mono_set hsub
    _ = ∫⁻ x in e ⁻¹' (closedBall (e y) (2 * (L * r)))ᶜ, ‖T g (e x)‖ₑ := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [coeFn_lpCoord b (T g)] with x hx
        rw [coordConj_apply, hx, Function.comp_apply]
    _ = ∫⁻ v in (closedBall (e y) (2 * (L * r)))ᶜ, ‖T g v‖ₑ :=
        he.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun v => ‖T g v‖ₑ) _
    _ ≤ B * ∫⁻ v, ‖g v‖ₑ := hcanc
    _ = B * ∫⁻ x, ‖f x‖ₑ := by
        rw [← he.lintegral_comp_emb e.measurableEmbedding]
        exact congrArg _ (lintegral_congr_ae (hge.mono fun x hx => congrArg enorm hx))

end Coordinates

variable [FiniteDimensional ℝ V]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Calderón–Zygmund theorem on an inner product space**, weak type `(1, 1)`. Let `V` be a
finite-dimensional real inner product space of dimension `n ≥ 1`, and let `T` be a bounded linear
operator on `L²(V)` such that `T f x = ∫ K x y (f y) dy` for almost every `x` off any compact set
outside which `f` vanishes, where for some `δ > 0` the kernel `K` satisfies the size and smoothness
estimates

`‖K x y‖ ≤ C₀ ‖x - y‖ ^ (-n)` for `x ≠ y`, and
`‖K x y - K x y'‖ ≤ C ‖y - y'‖ ^ δ ‖x - y'‖ ^ (-(n + δ))` whenever `‖x - y'‖ > 2 ‖y - y'‖`.

Then there is a constant `A` with `t · |{‖T f‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`. -/
theorem exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow [Nontrivial V]
    (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
    {k : V → V → E →L[ℝ] F} (hkm : StronglyMeasurable (Function.uncurry k)) {C₀ C : ℝ≥0}
    {δ : ℝ} (hδ : 0 < δ)
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(Module.finrank ℝ V : ℝ)))
    (hk : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))))
    (hrep : ∀ (f : Lp E 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z)) :
    ∃ A : ℝ≥0, ∀ (f : Lp E 2 (volume : Measure V)) (t : ℝ≥0∞),
      t * volume {x | t < ‖T f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ := by
  set b := stdOrthonormalBasis ℝ V
  have : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨B, hB, hT⟩ := exists_cancellation b T hkm hδ hsize hk hrep
  refine ⟨(2 ^ Fintype.card (Fin (Module.finrank ℝ V)) * (4 * ‖coordConj b T‖ₑ ^ 2) +
    ENNReal.ofReal 2 ^ Fintype.card (Fin (Module.finrank ℝ V)) + 4 * B).toNNReal, ?_⟩
  rw [ENNReal.coe_toNNReal (by finiteness)]
  exact mul_volume_lt_enorm_le_of_coordConj b T
    (mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le (coordConj b T) hT)

/-- **The Calderón–Zygmund theorem on an inner product space under Hörmander's condition**, weak
type `(1, 1)`, with a constant depending only on the data. Let `V` be a finite-dimensional real
inner product space of dimension `n ≥ 1`, and let `M` and `B` be finite. There is a constant `A`
with the following property. Let `T` be a bounded linear operator on `L²(V)` with `‖T‖ ≤ M`, such
that `T f x = ∫ k x y (f y) dy` for almost every `x` off any compact set outside which `f` vanishes,
where the kernel `k` satisfies **Hörmander's condition**

`∫_{‖x - y'‖ > 2 ‖y - y'‖} ‖k x y - k x y'‖ dx ≤ B` for all `y`, `y'`.

Then `t · |{‖T f‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`. One can take
`A = 4 · 2ⁿ M² + (2 √n)ⁿ + 4 B`. -/
theorem _root_.TauCeti.exists_mul_volume_lt_enorm_le_of_hormander [Nontrivial V] {M B : ℝ≥0∞}
    (hM : M ≠ ∞) (hB : B ≠ ∞) :
    ∃ A : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V))
      (k : V → V → E →L[ℝ] F), ‖T‖ₑ ≤ M → StronglyMeasurable (Function.uncurry k) →
      (∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖k x y - k x y'‖ₑ ≤ B) →
      (∀ (f : Lp E 2 (volume : Measure V)) (s : Set V), IsCompact s →
        (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z)) →
      ∀ (f : Lp E 2 (volume : Measure V)) (t : ℝ≥0∞),
        t * volume {x | t < ‖T f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ := by
  set b := stdOrthonormalBasis ℝ V
  have : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨(2 ^ Fintype.card (Fin (Module.finrank ℝ V)) * (4 * M ^ 2) +
    ENNReal.ofReal (2 * NNReal.sqrt (Fintype.card (Fin (Module.finrank ℝ V)))) ^
      Fintype.card (Fin (Module.finrank ℝ V)) + 4 * B).toNNReal,
    fun T k hTM hkm hk hrep f t => ?_⟩
  rw [ENNReal.coe_toNNReal (by finiteness)]
  refine mul_volume_lt_enorm_le_of_coordConj b T (fun g s => ?_) f t
  refine (mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le (coordConj b T)
    (setLIntegral_compl_closedBall_enorm_coordConj_le_of_hormander b T hkm hk hrep) g s).trans ?_
  rw [enorm_coordConj]
  gcongr

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] {p : ℝ≥0∞}

/-- **The Calderón–Zygmund theorem on an inner product space**, strong type `(p, p)` for
`1 < p < ∞`. Let `V` be a finite-dimensional real inner product space of dimension `n ≥ 1`, and let
`T` be a bounded linear operator on `L²(V)` of Hilbert space valued functions. Suppose that `T` and
its adjoint `T†` are given off the support of their argument by kernels `k` and `k'`: for every
compact set `s` and every `f` vanishing off `s`, `T f x = ∫ k x y (f y) dy` (respectively
`T† f x = ∫ k' x y (f y) dy`) for almost every `x ∉ s`. Suppose that, for some `δ > 0`, the
kernel `k` satisfies the size and smoothness estimates

`‖k x y‖ ≤ C₀ ‖x - y‖ ^ (-n)` for `x ≠ y`, and
`‖k x y - k x y'‖ ≤ C ‖y - y'‖ ^ δ ‖x - y'‖ ^ (-(n + δ))` whenever `‖x - y'‖ > 2 ‖y - y'‖`,

and that `k'` satisfies the same estimates with its own constants `C₀'`, `C'` and exponent
`δ' > 0`.

Then for every `1 < p < ∞` there is a constant `C` with `‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L²`. -/
theorem exists_eLpNorm_le_of_norm_sub_le_mul_rpow [Nontrivial V]
    (T : Lp H 2 (volume : Measure V) →L[ℝ] Lp K 2 (volume : Measure V))
    {k : V → V → H →L[ℝ] K} (hkm : StronglyMeasurable (Function.uncurry k))
    {k' : V → V → K →L[ℝ] H} (hk'm : StronglyMeasurable (Function.uncurry k'))
    {C₀ C C₀' C' : ℝ≥0} {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ C₀ * dist x y ^ (-(Module.finrank ℝ V : ℝ)))
    (hsize' : ∀ x y, x ≠ y → ‖k' x y‖ ≤ C₀' * dist x y ^ (-(Module.finrank ℝ V : ℝ)))
    (hk : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k x y - k x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))))
    (hk' : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖k' x y - k' x y'‖ ≤ C' * (dist y y' ^ δ' * dist x y' ^ (-(Module.finrank ℝ V + δ'))))
    (hrep : ∀ (f : Lp H 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z))
    (hrep' : ∀ (f : Lp K 2 (volume : Measure V)) (s : Set V), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → adjoint T f x = ∫ z, k' x z (f z))
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : Lp H 2 (volume : Measure V),
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume := by
  set b := stdOrthonormalBasis ℝ V
  have : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨B, hB, hT⟩ := exists_cancellation b T hkm hδ hsize hk hrep
  obtain ⟨B', hB', hT'⟩ := exists_cancellation b (adjoint T) hk'm hδ' hsize' hk' hrep'
  rw [← adjoint_coordConj] at hT'
  obtain ⟨A, hA⟩ := exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le
    (ι := Fin (Module.finrank ℝ V)) (H := H) (K := K) 2 (M := ‖coordConj b T‖ₑ) enorm_ne_top hB hB'
    hp hp_top
  refine ⟨A, fun f => ?_⟩
  simpa only [coordConj_lpCoord, eLpNorm_lpCoord] using
    hA (coordConj b T) le_rfl hT hT' (lpCoord b H f)


/-- **The Calderón–Zygmund theorem on an inner product space under Hörmander's condition**, strong
type `(p, p)` for `1 < p < ∞`, with a constant depending only on the data. Let `V` be a
finite-dimensional real inner product space of dimension `n ≥ 1`, let `M`, `B` and `B'` be finite,
and let `1 < p < ∞`. There is a constant `C` with the following property. Let `T` be a bounded
linear operator on `L²(V)` of Hilbert space valued functions with `‖T‖ ≤ M`. Suppose that `T` and
its adjoint `T†` are given off the support of their argument by kernels `k` and `k'`: for every
compact set `s` and every `f` vanishing off `s`, `T f x = ∫ k x y (f y) dy` (respectively
`T† f x = ∫ k' x y (f y) dy`) for almost every `x ∉ s`. Suppose that both kernels satisfy
**Hörmander's condition**

`∫_{‖x - y'‖ > 2 ‖y - y'‖} ‖k x y - k x y'‖ dx ≤ B` and
`∫_{‖x - y'‖ > 2 ‖y - y'‖} ‖k' x y - k' x y'‖ dx ≤ B'` for all `y`, `y'`.

Then `‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L²`. Since `C` does not depend on `T`, the theorem applies
uniformly to families of operators, such as the truncations of a Fourier multiplier. -/
theorem _root_.TauCeti.exists_eLpNorm_le_of_hormander [Nontrivial V] {M B B' : ℝ≥0∞}
    (hM : M ≠ ∞) (hB : B ≠ ∞) (hB' : B' ≠ ∞) (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (T : Lp H 2 (volume : Measure V) →L[ℝ] Lp K 2 (volume : Measure V))
      (k : V → V → H →L[ℝ] K) (k' : V → V → K →L[ℝ] H), ‖T‖ₑ ≤ M →
      StronglyMeasurable (Function.uncurry k) → StronglyMeasurable (Function.uncurry k') →
      (∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖k x y - k x y'‖ₑ ≤ B) →
      (∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖k' x y - k' x y'‖ₑ ≤ B') →
      (∀ (f : Lp H 2 (volume : Measure V)) (s : Set V), IsCompact s →
        (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ z, k x z (f z)) →
      (∀ (f : Lp K 2 (volume : Measure V)) (s : Set V), IsCompact s →
        (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → adjoint T f x = ∫ z, k' x z (f z)) →
      ∀ f : Lp H 2 (volume : Measure V), eLpNorm (T f) p volume ≤ C * eLpNorm f p volume := by
  set b := stdOrthonormalBasis ℝ V
  have : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le
    (ι := Fin (Module.finrank ℝ V)) (H := H) (K := K)
    (2 * NNReal.sqrt (Fintype.card (Fin (Module.finrank ℝ V)))) hM hB hB' hp hp_top
  refine ⟨C, fun T k k' hTM hkm hk'm hk hk' hrep hrep' f => ?_⟩
  have hT' :=
    setLIntegral_compl_closedBall_enorm_coordConj_le_of_hormander b (adjoint T) hk'm hk' hrep'
  rw [← adjoint_coordConj] at hT'
  simpa only [coordConj_lpCoord, eLpNorm_lpCoord] using
    hC (coordConj b T) ((enorm_coordConj b T).trans_le hTM)
      (setLIntegral_compl_closedBall_enorm_coordConj_le_of_hormander b T hkm hk hrep) hT'
      (lpCoord b H f)

end ContinuousLinearMap
