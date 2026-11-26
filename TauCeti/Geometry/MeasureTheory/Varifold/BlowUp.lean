/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.ApproximateTangentSpace
public import TauCeti.Geometry.MeasureTheory.Varifold.Euclidean
public import TauCeti.Geometry.MeasureTheory.Varifold.LineVarifold
public import TauCeti.Geometry.MeasureTheory.Varifold.Stationary

/-!
# Dilations of varifolds in a Euclidean space

Let `E` be a finite-dimensional real inner product space, `W ⊆ E` open and `V` a `k`-varifold on
`W`, a Radon measure on `W × G(E, k)`. For `x ∈ E` and `r > 0` let `η_{x,r}(y) = r⁻¹ (y - x)` be
the dilation that blows up the ball of radius `r` about `x` to the unit ball. Its differential is
`r⁻¹ id`, which maps every plane to itself with `k`-dimensional Jacobian `r⁻ᵏ`, so the varifold
push-forward of `V` along `η_{x,r}` is

`V_{x,r} = r⁻ᵏ · (image of V under (y, P) ↦ (r⁻¹ (y - x), P))`

(`Euclidean.blowUp V x r`). It is read as a measure on `E × G(E, k)`, the varifolds on the whole
of `E` (with `E` seen as the open set `⊤`), carried by `η_{x,r}(W)`. It is finite on the compact
subsets of `η_{x,r}(W)` (`Euclidean.blowUp_lt_top_of_isCompact`), which exhaust `E` as `r ↓ 0`
when `x ∈ W`; it need not be finite on the other compact sets. The varifold tangents of `V` at `x`
are the limits of `V_{x,r}` as `r ↓ 0` (Simon, *Lectures on Geometric Measure Theory*, §38 and
§42).

* **Scaling law.** The weight of `V_{x,r}` is the `k`-dimensional blow-up of the weight of `V`
  (`Euclidean.weight_blowUp`), so `‖V_{x,r}‖(A) = r⁻ᵏ ‖V‖(x + r A)`, and
  `∫ f dV_{x,r} = r⁻ᵏ ∫ f(r⁻¹ (y - x), P) dV(y, P)` (`Euclidean.integral_blowUp`); dilations
  compose, `(V_{x,r})_{0,t} = V_{x,rt}` (`Euclidean.blowUp_blowUp`).
* Dilation commutes with sums, scalar multiples and the restriction `V⌞A`
  (`Euclidean.blowUp_restrict`), and it is continuous for varifold convergence against the test
  functions supported over `η_{x,r}(W)` (`Euclidean.tendsto_integral_blowUp`); for varifolds on
  all of `E` it is continuous for varifold convergence (`Euclidean.varifoldTendsto_blowUp`).
* **First variation.** For a vector field `Y`,
  `∫ div_P Y d V_{x,r} = r^{1-k} ∫ div_P (Y ∘ η_{x,r}) dV`
  (`Euclidean.integral_tangentialDivergence_blowUp`), since `D(Y ∘ η_{x,r}) = r⁻¹ DY ∘ η_{x,r}`.
  Consequently dilations of stationary varifolds are stationary
  (`Euclidean.IsStationary.integral_tangentialDivergence_blowUp_eq_zero`,
  `Euclidean.IsStationary.blowUp`).
* For the line varifold `V` of `a + ℝu` with constant plane `P ∈ G(E, k)`,
  `V_{x,r} = r^{1-k} V'`, where `V'` is the line varifold of the dilated line `r⁻¹ (a - x) + ℝu`
  with the same plane (`Euclidean.blowUp_lineVarifold`); for `k = 1` the dilations of a line are
  lines, and those of a line through `x` are all the line through `0`
  (`Euclidean.blowUp_lineVarifold_one_dim`).

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 3.
* L. Simon, *Lectures on Geometric Measure Theory*, §38, §39 and §42.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ENNReal NNReal Distributions CompactlySupported

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
  {W : Opens E} {x : E} {r : ℝ}

/-! ### The dilation map -/

/-- The dilation `(y, P) ↦ (r⁻¹ (y - x), P)` of `W × G(E, k)` into `E × G(E, k)`. -/
private def blowUpMap (x : E) (r : ℝ) (p : W × grassmannian ℝ E k) :
    (⊤ : Opens E) × grassmannian ℝ E k :=
  (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2)

private theorem blowUpMap_apply (x : E) (r : ℝ) (p : W × grassmannian ℝ E k) :
    blowUpMap x r p = (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2) :=
  rfl

private theorem continuous_blowUpMap (x : E) (r : ℝ) :
    Continuous (blowUpMap (W := W) (k := k) x r) :=
  ((continuous_const_smul r⁻¹).comp
    ((continuous_subtypeVal.comp continuous_fst).sub continuous_const)).subtype_mk _ |>.prodMk
    continuous_snd

private theorem isOpenEmbedding_blowUpMap (x : E) (hr : r ≠ 0) :
    IsOpenEmbedding (blowUpMap (W := W) (k := k) x r) := by
  have hη := (Measure.blowUpDilation x hr).isOpenEmbedding
  rw [Measure.coe_blowUpDilation] at hη
  have h : IsOpenEmbedding fun y : W ↦ (⟨r⁻¹ • ((y : E) - x), Opens.mem_top _⟩ : (⊤ : Opens E)) :=
    (IsOpenEmbedding.of_comp_iff _ (⊤ : Opens E).isOpenEmbedding').1
      (hη.comp W.isOpenEmbedding')
  exact h.prodMap .id

/-- The dilation map takes the pairs over `W` onto the pairs whose base point `y` has
`x + r y ∈ W`. -/
private theorem range_blowUpMap (x : E) (hr : r ≠ 0) :
    range (blowUpMap (W := W) (k := k) x r) = {q | x + r • (q.1 : E) ∈ W} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    simp [blowUpMap, smul_smul, mul_inv_cancel₀ hr]
  · intro hq
    exact ⟨(⟨x + r • (q.1 : E), hq⟩, q.2), by simp [blowUpMap, smul_smul, inv_mul_cancel₀ hr]⟩

/-- The pairs over `W` that the dilation sends into a compact set lying over `η_{x,r}(W)` form a
compact set. -/
private theorem isCompact_preimage_blowUpMap (hr : r ≠ 0)
    {K : Set ((⊤ : Opens E) × grassmannian ℝ E k)} (hK : IsCompact K)
    (hKW : ∀ q ∈ K, x + r • (q.1 : E) ∈ W) : IsCompact (blowUpMap (W := W) x r ⁻¹' K) := by
  refine (isOpenEmbedding_blowUpMap x hr).isInducing.isCompact_preimage' hK ?_
  rw [range_blowUpMap x hr]
  exact hKW

/-! ### The dilation of a varifold -/

variable [MeasurableSpace E]

/-- The **dilation** `V_{x,r} = (η_{x,r})_# V` of a varifold `V` on `W` by
`η_{x,r}(y) = r⁻¹ (y - x)`: the image of `V` under `(y, P) ↦ (r⁻¹ (y - x), P)` multiplied by
`r⁻ᵏ`, read as a measure on `E × G(E, k)` carried by `η_{x,r}(W)` (Simon, *Lectures on Geometric
Measure Theory*, §38). It is meant for `r > 0`. -/
def blowUp (V : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    Measure ((⊤ : Opens E) × grassmannian ℝ E k) :=
  (ENNReal.ofReal r)⁻¹ ^ k • V.map fun p ↦ (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2)

variable {V V₁ V₂ : Measure (W × grassmannian ℝ E k)}

/-- The defining formula of `Euclidean.blowUp`. -/
theorem blowUp_def (V : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    blowUp V x r = (ENNReal.ofReal r)⁻¹ ^ k •
      V.map fun p ↦ (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2) :=
  (rfl)

private theorem blowUp_eq (V : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    blowUp V x r = (ENNReal.ofReal r)⁻¹ ^ k • V.map (blowUpMap x r) :=
  (rfl)

variable [BorelSpace E]

private theorem measurableEmbedding_blowUpMap (x : E) (hr : r ≠ 0) :
    MeasurableEmbedding (blowUpMap (W := W) (k := k) x r) :=
  (isOpenEmbedding_blowUpMap x hr).measurableEmbedding

/-- The dilation gives a set of pairs `r⁻ᵏ` times the mass that `V` gives to its preimage. -/
theorem blowUp_apply (hr : r ≠ 0) (s : Set ((⊤ : Opens E) × grassmannian ℝ E k)) :
    blowUp V x r s = (ENNReal.ofReal r)⁻¹ ^ k *
      V {p | ((⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2) :
        (⊤ : Opens E) × grassmannian ℝ E k) ∈ s} := by
  rw [blowUp_eq, smul_apply, smul_eq_mul, (measurableEmbedding_blowUpMap x hr).map_apply V s]
  simp only [preimage, blowUpMap_apply]

/-- The mass of the dilation is `r⁻ᵏ` times the mass of `V`. -/
theorem blowUp_apply_univ (V : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    blowUp V x r univ = (ENNReal.ofReal r)⁻¹ ^ k * V univ := by
  rw [blowUp_eq, smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_blowUpMap x r).measurable MeasurableSet.univ, preimage_univ]

omit [BorelSpace E] in
@[simp]
theorem blowUp_zero (x : E) (r : ℝ) : blowUp (0 : Measure (W × grassmannian ℝ E k)) x r = 0 := by
  simp [blowUp_def]

@[simp]
theorem blowUp_add (V₁ V₂ : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    blowUp (V₁ + V₂) x r = blowUp V₁ x r + blowUp V₂ x r := by
  rw [blowUp_eq, blowUp_eq, blowUp_eq,
    Measure.map_add _ _ (continuous_blowUpMap x r).measurable, smul_add]

@[simp]
theorem blowUp_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [SMulCommClass ℝ≥0∞ R ℝ≥0∞] (c : R) (V : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    blowUp (c • V) x r = c • blowUp V x r := by
  rw [blowUp_eq, blowUp_eq, Measure.map_smul c (continuous_blowUpMap x r).measurable.aemeasurable,
    smul_comm]

omit [BorelSpace E] in
/-- Dilating about `0` by the factor `1` does nothing to a varifold on `E`. -/
@[simp]
theorem blowUp_zero_one (V : Measure ((⊤ : Opens E) × grassmannian ℝ E k)) : blowUp V 0 1 = V := by
  simp [blowUp_def]

/-- **Dilations compose**: `(V_{x,r})_{0,t} = V_{x,rt}`. -/
theorem blowUp_blowUp (V : Measure (W × grassmannian ℝ E k)) (x : E) (hr : 0 ≤ r) (t : ℝ) :
    blowUp (blowUp V x r) 0 t = blowUp V x (r * t) := by
  rw [blowUp_eq, blowUp_eq, blowUp_eq,
    Measure.map_smul (hf := (continuous_blowUpMap 0 t).measurable.aemeasurable),
    Measure.map_map (continuous_blowUpMap 0 t).measurable (continuous_blowUpMap x r).measurable,
    smul_smul]
  congr 1
  · simp [ENNReal.ofReal_mul hr, mul_pow, ENNReal.mul_inv, mul_comm]
  · congr 1
    ext p <;> simp [blowUpMap, smul_smul, mul_comm]

/-! ### Weight, integrals and local finiteness -/

/-- The weight of the dilation `V_{x,r}` is the `k`-dimensional blow-up `‖V‖_{x,r}` of the weight
of `V`; in particular `‖V_{x,r}‖(A) = r⁻ᵏ ‖V‖(x + r A)` for `r > 0`
(`MeasureTheory.Measure.blowUp_apply_vadd_smul`). -/
@[simp]
theorem weight_blowUp (V : Measure (W × grassmannian ℝ E k)) (x : E) (r : ℝ) :
    weight (blowUp V x r) = (weight V).blowUp k x r := by
  have hη : Measurable fun y : E ↦ r⁻¹ • (y - x) := (continuous_const_smul r⁻¹).measurable.comp
    (measurable_id.sub_const x)
  have hfst {U : Opens E} : Measurable fun p : U × grassmannian ℝ E k ↦ (p.1 : E) :=
    measurable_subtypeVal.comp measurable_fst
  rw [blowUp_eq, weight_smul, Measure.blowUp_def, weight_def, weight_def,
    Measure.map_map hfst (continuous_blowUpMap x r).measurable, Measure.map_map hη hfst]
  simp only [Function.comp_def, blowUpMap]

/-- Integrals against the dilation: `∫ f dV_{x,r} = r⁻ᵏ ∫ f(r⁻¹ (y - x), P) dV(y, P)`. -/
theorem integral_blowUp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (hr : 0 < r)
    (V : Measure (W × grassmannian ℝ E k)) (x : E) (f : (⊤ : Opens E) × grassmannian ℝ E k → G) :
    ∫ q, f q ∂blowUp V x r =
      (r ^ k)⁻¹ • ∫ p, f (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2) ∂V := by
  rw [blowUp_eq, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hr.le, inv_pow, (measurableEmbedding_blowUpMap x hr.ne').integral_map f]
  simp only [blowUpMap_apply]

/-- Lower integrals against the dilation:
`∫⁻ f dV_{x,r} = r⁻ᵏ ∫⁻ f(r⁻¹ (y - x), P) dV(y, P)`. -/
theorem lintegral_blowUp (hr : r ≠ 0) (V : Measure (W × grassmannian ℝ E k)) (x : E)
    (f : (⊤ : Opens E) × grassmannian ℝ E k → ℝ≥0∞) :
    ∫⁻ q, f q ∂blowUp V x r =
      (ENNReal.ofReal r)⁻¹ ^ k * ∫⁻ p, f (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2) ∂V := by
  rw [blowUp_eq, lintegral_smul_measure, (measurableEmbedding_blowUpMap x hr).lintegral_map f]
  simp only [blowUpMap_apply, smul_eq_mul]

/-- The dilation of a varifold on `W` is finite on the compact sets lying over `η_{x,r}(W)`, that
is, of pairs `(y, P)` with `x + r y ∈ W`. -/
theorem blowUp_lt_top_of_isCompact [IsFiniteMeasureOnCompacts V] (hr : 0 < r)
    {K : Set ((⊤ : Opens E) × grassmannian ℝ E k)} (hK : IsCompact K)
    (hKW : ∀ q ∈ K, x + r • (q.1 : E) ∈ W) : blowUp V x r K < ∞ := by
  rw [blowUp_eq, smul_apply, smul_eq_mul,
    (measurableEmbedding_blowUpMap x hr.ne').map_apply]
  exact ENNReal.mul_lt_top (by simp [hr])
    (isCompact_preimage_blowUpMap hr.ne' hK hKW).measure_lt_top

/-- The dilation of a varifold on `E` is a varifold on `E`. -/
theorem isFiniteMeasureOnCompacts_blowUp (V : Measure ((⊤ : Opens E) × grassmannian ℝ E k))
    [IsFiniteMeasureOnCompacts V] (x : E) (hr : 0 < r) :
    IsFiniteMeasureOnCompacts (blowUp V x r) :=
  ⟨fun _ hK ↦ blowUp_lt_top_of_isCompact hr hK fun _ _ ↦ Opens.mem_top _⟩

/-- Dilation commutes with the restriction `V⌞A` to the pairs with base point in `A`: the dilation
of `V⌞A` is `V_{x,r}` restricted to the pairs whose base point `y` has `x + r y ∈ A`. -/
theorem blowUp_restrict (V : Measure (W × grassmannian ℝ E k)) (x : E) (hr : r ≠ 0) (A : Set E) :
    blowUp (V.restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' A))) x r =
      (blowUp V x r).restrict (Prod.fst ⁻¹' (Subtype.val ⁻¹' ((fun z ↦ r • z + x) ⁻¹' A))) := by
  rw [blowUp_eq, blowUp_eq, Measure.restrict_smul,
    (measurableEmbedding_blowUpMap x hr).restrict_map]
  congr 3
  ext p
  simp [blowUpMap, smul_smul, mul_inv_cancel₀ hr]

/-! ### Continuity under varifold convergence -/

/-- **Continuity of dilations under varifold convergence.** If `V_n → V` as varifolds on `W`,
then `∫ f d(V_n)_{x,r} → ∫ f dV_{x,r}` for every compactly supported continuous `f` on
`E × G(E, k)` supported over `η_{x,r}(W)`. -/
theorem tendsto_integral_blowUp {V : ℕ → Measure (W × grassmannian ℝ E k)}
    {V₀ : Measure (W × grassmannian ℝ E k)} (h : TauCeti.VarifoldTendsto V V₀) (hr : 0 < r)
    (f : C_c((⊤ : Opens E) × grassmannian ℝ E k, ℝ))
    (hf : ∀ q ∈ tsupport f, x + r • (q.1 : E) ∈ W) :
    Tendsto (fun n ↦ ∫ q, f q ∂blowUp (V n) x r) atTop (𝓝 (∫ q, f q ∂blowUp V₀ x r)) := by
  let g : C_c(W × grassmannian ℝ E k, ℝ) :=
    { toFun := f ∘ blowUpMap x r
      continuous_toFun := f.continuous.comp (continuous_blowUpMap x r)
      hasCompactSupport' := HasCompactSupport.intro
        (isCompact_preimage_blowUpMap hr.ne' f.hasCompactSupport hf)
        fun _ hp ↦ image_eq_zero_of_notMem_tsupport (f := ⇑f) hp }
  have hg (p : W × grassmannian ℝ E k) :
      g p = f (⟨r⁻¹ • ((p.1 : E) - x), Opens.mem_top _⟩, p.2) := by
    simp [g, blowUpMap_apply]
  simp_rw [integral_blowUp hr, ← hg]
  exact (h.tendsto_integral g).const_smul _

/-- **Continuity of dilations under varifold convergence**, for varifolds on all of `E`: if
`V_n → V` then `(V_n)_{x,r} → V_{x,r}`. -/
theorem varifoldTendsto_blowUp {V : ℕ → Measure ((⊤ : Opens E) × grassmannian ℝ E k)}
    {V₀ : Measure ((⊤ : Opens E) × grassmannian ℝ E k)} (h : TauCeti.VarifoldTendsto V V₀)
    (x : E) (hr : 0 < r) : TauCeti.VarifoldTendsto (fun n ↦ blowUp (V n) x r) (blowUp V₀ x r) :=
  TauCeti.varifoldTendsto_iff.2 fun f ↦
    tendsto_integral_blowUp (x := x) h hr f fun _ _ ↦ Opens.mem_top _

/-! ### The first variation of a dilation -/

/-- **The first variation of a dilation**: for every vector field `Y`,
`∫ div_P Y d V_{x,r} = r^{1-k} ∫ div_P (Y ∘ η_{x,r}) dV`, where `η_{x,r}(y) = r⁻¹ (y - x)`. -/
theorem integral_tangentialDivergence_blowUp (V : Measure (W × grassmannian ℝ E k)) (x : E)
    (hr : 0 < r) (Y : E → E) :
    ∫ q, tangentialDivergence Y q.1 q.2 ∂blowUp V x r =
      r ^ (1 - k : ℤ) * ∫ p, tangentialDivergence (fun y ↦ Y (r⁻¹ • (y - x))) p.1 p.2 ∂V := by
  have hη (y : E) (P : E →L[ℝ] E) :
      tangentialDivergence Y (r⁻¹ • (y - x)) P =
        r * tangentialDivergence (fun y ↦ Y (r⁻¹ • (y - x))) y P := by
    rw [tangentialDivergence_comp_sub (fun z ↦ Y (r⁻¹ • z)), tangentialDivergence_comp_smul,
      mul_inv_cancel_left₀ hr.ne']
  rw [integral_blowUp hr, smul_eq_mul]
  simp only [hη, integral_const_mul, ← mul_assoc]
  rw [zpow_sub₀ hr.ne', zpow_one, zpow_natCast, div_eq_inv_mul]

/-- **Dilations of a stationary varifold are stationary**: if `V` is stationary in `W`, then
`∫ div_P Y d V_{x,r} = 0` for every `C¹` vector field `Y` with compact support whose dilation
`Y ∘ η_{x,r}` is supported in `W`. -/
theorem IsStationary.integral_tangentialDivergence_blowUp_eq_zero [IsFiniteMeasureOnCompacts V]
    (hV : IsStationary V) (x : E) (hr : 0 < r) {Y : E → E} (hY : ContDiff ℝ 1 Y)
    (hYc : HasCompactSupport Y) (hYW : ∀ y ∈ tsupport Y, x + r • y ∈ W) :
    ∫ q, tangentialDivergence Y q.1 q.2 ∂blowUp V x r = 0 := by
  let η := Measure.blowUpDilation x hr.ne'
  have hsupp : tsupport (Y ∘ η) ⊆ W := by
    rw [tsupport_comp_eq_preimage]
    intro y hy
    simpa [η, smul_smul, mul_inv_cancel₀ hr.ne'] using hYW _ hy
  let X : 𝓓^{1}(W, E) := ⟨Y ∘ η, hY.comp (by rw [Measure.coe_blowUpDilation]; fun_prop),
    hYc.comp_homeomorph η, hsupp⟩
  have hX := (isStationary_iff.1 hV) X
  rw [firstVariation_apply] at hX
  -- `X` is `Y ∘ η_{x,r}` as a function, so `hX` is the vanishing of `∫ div_P (Y ∘ η_{x,r}) dV`.
  have hX' : ∫ p, tangentialDivergence (fun y ↦ Y (r⁻¹ • (y - x))) p.1 p.2 ∂V = 0 := by
    simpa [X, η, Function.comp_def] using hX
  rw [integral_tangentialDivergence_blowUp V x hr Y, hX', mul_zero]

/-- **Dilations of a stationary varifold on `E` are stationary.** -/
theorem IsStationary.blowUp {V : Measure ((⊤ : Opens E) × grassmannian ℝ E k)}
    [IsFiniteMeasureOnCompacts V] (hV : IsStationary V) (x : E) (hr : 0 < r) :
    IsStationary (blowUp V x r) := by
  have := isFiniteMeasureOnCompacts_blowUp V x hr
  refine isStationary_iff.2 fun Y ↦ ?_
  rw [firstVariation_apply]
  exact hV.integral_tangentialDivergence_blowUp_eq_zero x hr Y.contDiff Y.hasCompactSupport
    fun _ _ ↦ Opens.mem_top _

/-! ### Lines -/

/-- The dilation about `x` of the line varifold of `a + ℝu` with constant plane `P` is `r^{1-k}`
times the line varifold of the dilated line `r⁻¹ (a - x) + ℝu` with the same plane. -/
theorem blowUp_lineVarifold (a u : E) (P : grassmannian ℝ E k) (x : E) (hr : 0 < r) :
    blowUp (lineVarifold a u P) x r =
      ((ENNReal.ofReal r)⁻¹ ^ k * ENNReal.ofReal r) • lineVarifold (r⁻¹ • (a - x)) u P := by
  -- The dilation maps the line `a + ℝu` onto the line `r⁻¹ (a - x) + ℝ (r⁻¹ u)`, preserving
  -- the parameter.
  have hcomp : blowUpMap x r ∘ lineVarifoldParam a u P =
      lineVarifoldParam (r⁻¹ • (a - x)) (r⁻¹ • u) P := by
    ext t <;> simp [blowUpMap_apply, smul_sub, smul_add, smul_comm r⁻¹ t, add_sub_right_comm]
  rw [blowUp_eq, lineVarifold_def,
    Measure.map_map (continuous_blowUpMap x r).measurable
      (continuous_lineVarifoldParam a u P).measurable, hcomp, ← lineVarifold_def,
    lineVarifold_smul_direction _ u P (inv_ne_zero hr.ne'), smul_smul]
  simp [abs_of_pos hr]

/-- **The dilations of a line are lines**: for `1`-planes, the dilation about `x` of the line
varifold of `a + ℝu` with constant plane `P` is the line varifold of `r⁻¹ (a - x) + ℝu` with the
plane `P`, for every `r > 0`; for `a = x` this is the line through `0`, whatever `r`. -/
theorem blowUp_lineVarifold_one_dim (a u : E) (P : grassmannian ℝ E 1) (x : E) (hr : 0 < r) :
    blowUp (lineVarifold a u P) x r = lineVarifold (r⁻¹ • (a - x)) u P := by
  rw [blowUp_lineVarifold a u P x hr, pow_one,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top, one_smul]

end Euclidean
