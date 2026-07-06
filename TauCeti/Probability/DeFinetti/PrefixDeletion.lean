module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.ProcessShift
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.Independence.Conditional
import TauCeti.Probability.Process.Tail

/-!
# Prefix-deletion conditional-expectation identity (Kallenberg 1.3 input)

For a contractable process `X`, this file proves the "prefix-deletion" conditional-expectation
identity feeding the de Finetti martingale route: for `r ≤ m` and a measurable `B`,
```
μ[𝟙_{(X r)⁻¹ B} | σ(U) ⊔ σ(W)] =ᵐ[μ] μ[𝟙_{(X r)⁻¹ B} | σ(W)],
```
where `U ω = (X 0 ω, …, X (r-1) ω)` is the length-`r` prefix and `W = processShift X (m+1)` is the
far tail from time `m+1`.  Informally, `X r` is conditionally independent of the prefix given the
far tail, so conditioning the `X r`-indicator on `σ(U) ⊔ σ(W)` collapses to conditioning on `σ(W)`.

## Main results

The public interface consists of two theorems:

* `Contractable.condIndep_Xr_prefix_tail` — the conditional-independence statement (primary result):
  for a contractable process and `r ≤ m`, `X r` is conditionally independent of the prefix `U`
  given the far tail `W = processShift X (m+1)`, packaged as a `ProbabilityTheory.CondIndep` object.
* `Contractable.condExp_indicator_prefix_sup_tail_eq` — the prefix-deletion drop-info identity read
  off from that conditional independence: for `r ≤ m` and a measurable `B`,
  `μ[𝟙_{(X r)⁻¹ B} | σ(U) ⊔ σ(W)] =ᵐ μ[𝟙_{(X r)⁻¹ B} | σ(W)]`.

The pair-law/Kallenberg-1.3 engine feeding the conditional independence is internal proof machinery,
kept `private` to this module; the conditional-independence projection step is imported from
`TauCeti.Probability.Independence.Conditional`.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/PairLawEquality.lean`,
`Probability/TripleLawDropInfo/*`, `Probability/CondIndep/*`).
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSpace γ] {μ : Measure Ω}

/-! ### The two reindexing maps -/

/-- Injection `φ₀` for contractability: indices `0,…,r-1, m+1, m+2, …` (skips `r,…,m`). -/
private def phi0 (r m : ℕ) : ℕ → ℕ := fun n => if n < r then n else n + (m - r + 1)

/-- Injection `φ₁` for contractability: indices `0,…,r, m+1, m+2, …` (skips `r+1,…,m`). -/
private def phi1 (r m : ℕ) : ℕ → ℕ := fun n => if n ≤ r then n else n + (m - r)

private lemma phi0_strictMono (r m : ℕ) : StrictMono (phi0 r m) := by
  intro i j hij
  simp only [phi0]
  by_cases hi : i < r
  · by_cases hj : j < r
    · simp [hi, hj, hij]
    · simp only [hi, if_true, hj, if_false]
      omega
  · simp only [hi, if_false]
    have hj : ¬j < r := fun h => hi (Nat.lt_of_lt_of_le hij (Nat.le_of_lt h))
    simp only [hj, if_false]
    omega

private lemma phi1_strictMono (r m : ℕ) : StrictMono (phi1 r m) := by
  intro i j hij
  simp only [phi1]
  by_cases hi : i ≤ r
  · by_cases hj : j ≤ r
    · simp [hi, hj, hij]
    · simp only [hi, if_true, hj, if_false]
      omega
  · simp only [hi, if_false]
    have hj : ¬j ≤ r := fun h => hi (Nat.le_trans (Nat.le_of_lt hij) h)
    simp only [hj, if_false]
    omega

/-! ### Pair-law equality from contractability -/

/-- **Pair-law equality from contractability:** `(U, W) =ᵈ (U, W')`, where `U` is the length-`r`
prefix, `W = processShift X (m+1)` is the far tail, and `W' = processCons (X r) W`.  Both pairs
arise from strictly increasing reindexings (`phi0`, `phi1`) of the same contractable process, so
they have the same law. -/
private lemma pair_law_eq_of_contractable [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX : ∀ n, Measurable (X n))
    (r m : ℕ) (hr : r ≤ m) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    let W' := processCons (fun ω => X r ω) W
    Measure.map (fun ω => (U ω, W ω)) μ =
    Measure.map (fun ω => (U ω, W' ω)) μ := by
  intro U W W'
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX i).aemeasurable
  -- Reindexing a contractable process by a strictly increasing map preserves the path law.
  have hreindex : ∀ φ : ℕ → ℕ, StrictMono φ →
      μ.map (fun ω (i : ℕ) => X (φ i) ω) = pathLaw μ X := by
    intro φ hφ
    calc μ.map (fun ω (i : ℕ) => X (φ i) ω)
        = (pathLaw μ X).map (fun x : ℕ → α => fun i => x (φ i)) :=
          (map_reindex_pathLaw μ hX_ae φ).symm
      _ = pathLaw μ X := (hContr.measurePreserving_reindex hX_ae hφ).map_eq
  -- Concatenation map: glue prefix `(Fin r → α)` and tail `(ℕ → α)` into `(ℕ → α)`.
  let concat : (Fin r → α) × (ℕ → α) → (ℕ → α) := fun p n =>
    if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r)
  -- Split map: extract prefix and tail from `(ℕ → α)`.
  let split : (ℕ → α) → (Fin r → α) × (ℕ → α) := fun f =>
    (fun i => f i.val, fun n => f (r + n))
  have h_split_concat : ∀ p : (Fin r → α) × (ℕ → α), split (concat p) = p := fun ⟨u, w⟩ => by
    simp only [split, concat, Prod.mk.injEq]
    constructor
    · ext i
      have hi : (i : ℕ) < r := i.isLt
      simp only [hi, dite_true, Fin.eta]
    · ext n
      have h : ¬(r + n < r) := Nat.not_lt.mpr (Nat.le_add_right r n)
      simp only [h, dite_false, Nat.add_sub_cancel_left]
  have h_concat_meas : Measurable concat := by
    refine measurable_pi_lambda _ fun n => ?_
    by_cases hn : n < r
    · have h : (fun p : (Fin r → α) × (ℕ → α) => concat p n) = fun p => p.1 ⟨n, hn⟩ := by
        funext p; simp only [concat, dif_pos hn]
      rw [h]; exact (measurable_pi_apply _).comp measurable_fst
    · have h : (fun p : (Fin r → α) × (ℕ → α) => concat p n) = fun p => p.2 (n - r) := by
        funext p; simp only [concat, dif_neg hn]
      rw [h]; exact (measurable_pi_apply _).comp measurable_snd
  have h_split_meas : Measurable split := by fun_prop
  -- Concatenated sequences.
  let seq0 : Ω → ℕ → α := fun ω => concat (U ω, W ω)
  let seq1 : Ω → ℕ → α := fun ω => concat (U ω, W' ω)
  have h_seq0 : ∀ ω n, seq0 ω n = X (phi0 r m n) ω := fun ω n => by
    simp only [seq0, concat, U, phi0]
    by_cases hn : n < r
    · simp only [hn, dite_true, ite_true]
    · simp only [hn, dite_false, ite_false, W, processShift_apply]
      congr 1
      omega
  have h_seq1 : ∀ ω n, seq1 ω n = X (phi1 r m n) ω := fun ω n => by
    simp only [seq1, concat, U, phi1]
    by_cases hn : n < r
    · have hle : n ≤ r := Nat.le_of_lt hn
      simp only [hn, dite_true, hle, ite_true]
    · simp only [hn, dite_false]
      by_cases hn' : n = r
      · subst hn'
        simp only [Nat.sub_self, le_refl, ite_true, W', processCons_zero]
      · have hgt : r < n := Nat.lt_of_le_of_ne (Nat.not_lt.mp hn) (Ne.symm hn')
        simp only [Nat.not_le.mpr hgt, ite_false]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
        subst hk
        have h_idx : (r + k + 1) - r = k + 1 := by omega
        rw [h_idx]
        simp only [W', processCons_succ, W, processShift_apply]
        congr 1
        omega
  -- Measurability of the building blocks.
  have hU_meas : Measurable U := measurable_pi_lambda _ fun i => hX i.val
  have hW_meas : Measurable W := measurable_processShift fun n => hX (m + 1 + n)
  have hW'_meas : Measurable W' :=
    measurable_processCons (hX r) fun n => (measurable_pi_apply n).comp hW_meas
  have hseq0_meas : Measurable seq0 := h_concat_meas.comp (hU_meas.prodMk hW_meas)
  have hseq1_meas : Measurable seq1 := h_concat_meas.comp (hU_meas.prodMk hW'_meas)
  -- Both concatenated sequences are reindexings of `X`, hence have the same law `pathLaw μ X`.
  have hseq0_eq : seq0 = fun ω (i : ℕ) => X (phi0 r m i) ω :=
    funext fun ω => funext fun n => h_seq0 ω n
  have hseq1_eq : seq1 = fun ω (i : ℕ) => X (phi1 r m i) ω :=
    funext fun ω => funext fun n => h_seq1 ω n
  have h_seq_eq : Measure.map seq0 μ = Measure.map seq1 μ := by
    rw [hseq0_eq, hseq1_eq, hreindex (phi0 r m) (phi0_strictMono r m),
      hreindex (phi1 r m) (phi1_strictMono r m)]
  -- Pull back via `split`.
  have h0 : Measure.map (fun ω => (U ω, W ω)) μ = Measure.map (split ∘ seq0) μ :=
    congrArg (Measure.map · μ) <| funext fun ω => (h_split_concat (U ω, W ω)).symm
  have h1 : Measure.map (fun ω => (U ω, W' ω)) μ = Measure.map (split ∘ seq1) μ :=
    congrArg (Measure.map · μ) <| funext fun ω => (h_split_concat (U ω, W' ω)).symm
  rw [h0, h1, ← Measure.map_map h_split_meas hseq0_meas,
    ← Measure.map_map h_split_meas hseq1_meas, h_seq_eq]

/-! ### Kallenberg Lemma 1.3 (contraction-independence) -/

/-- From the pair-law equality `(X, W) =ᵈ (X, W')`, extract the marginal `W =ᵈ W'`. -/
private lemma marginal_law_eq_of_pair_law (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ) :
    Measure.map W μ = Measure.map W' μ := by
  have h := congrArg (Measure.map (Prod.snd : α × γ → γ)) h_law
  rwa [Measure.map_map measurable_snd (hX.prodMk hW),
    Measure.map_map measurable_snd (hX.prodMk hW')] at h

/-- Helper for Kallenberg 1.3: the square-integrals of the two conditional expectations agree. -/
private lemma integral_sq_condExp_eq_of_pair_law [IsFiniteMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) :
    ∫ ω, (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
            | MeasurableSpace.comap W inferInstance]) ω
        * (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
            | MeasurableSpace.comap W inferInstance]) ω ∂μ
      = ∫ ω, (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
              | MeasurableSpace.comap W' inferInstance]) ω
          * (μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ))
              | MeasurableSpace.comap W' inferInstance]) ω ∂μ := by
  have hρ_eq : Measure.map W μ = Measure.map W' μ :=
    marginal_law_eq_of_pair_law X W W' hX hW hW' h_law
  let φ : Ω → ℝ := (X ⁻¹' A).indicator (fun _ => (1 : ℝ))
  let μ₁ : Ω → ℝ := μ[φ | MeasurableSpace.comap W inferInstance]
  let μ₂ : Ω → ℝ := μ[φ | MeasurableSpace.comap W' inferInstance]
  have hmW_le : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› :=
    measurable_iff_comap_le.mp hW
  have hmW'_le : MeasurableSpace.comap W' inferInstance ≤ ‹MeasurableSpace Ω› :=
    measurable_iff_comap_le.mp hW'
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) (hX hA)
  -- Doob–Dynkin factorisation `μ₁ = g₁ ∘ W`, `μ₂ = g₂ ∘ W'`.
  have hμ₁_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] μ₁ :=
    stronglyMeasurable_condExp
  obtain ⟨g₁, hg₁_sm, hμ₁_eq⟩ := hμ₁_sm.exists_eq_measurable_comp
  have hμ₂_sm : StronglyMeasurable[MeasurableSpace.comap W' inferInstance] μ₂ :=
    stronglyMeasurable_condExp
  obtain ⟨g₂, hg₂_sm, hμ₂_eq⟩ := hμ₂_sm.exists_eq_measurable_comp
  have hg₁_int : Integrable g₁ (Measure.map W μ) := by
    have h : Integrable (g₁ ∘ W) μ := by rw [← hμ₁_eq]; exact integrable_condExp
    exact (integrable_map_measure hg₁_sm.aestronglyMeasurable hW.aemeasurable).mpr h
  have hg₂_int : Integrable g₂ (Measure.map W' μ) := by
    have h : Integrable (g₂ ∘ W') μ := by rw [← hμ₂_eq]; exact integrable_condExp
    exact (integrable_map_measure hg₂_sm.aestronglyMeasurable hW'.aemeasurable).mpr h
  have hg₂_int' : Integrable g₂ (Measure.map W μ) := by rw [hρ_eq]; exact hg₂_int
  -- `g₁ = g₂` a.e. on `ρ`, via the set-integral characterisation and the pair law.
  have hg_eq : g₁ =ᵐ[Measure.map W μ] g₂ := by
    refine Integrable.ae_eq_of_forall_setIntegral_eq g₁ g₂ hg₁_int hg₂_int' fun B hB _ => ?_
    have h1 : ∫ y in B, g₁ y ∂(Measure.map W μ) = ∫ ω in W ⁻¹' B, φ ω ∂μ := by
      calc ∫ y in B, g₁ y ∂(Measure.map W μ)
          = ∫ y, g₁ y ∂((μ.restrict (W ⁻¹' B)).map W) := by rw [Measure.restrict_map hW hB]
        _ = ∫ ω in W ⁻¹' B, g₁ (W ω) ∂μ :=
              integral_map hW.aemeasurable.restrict hg₁_sm.aestronglyMeasurable
        _ = ∫ ω in W ⁻¹' B, μ₁ ω ∂μ :=
              setIntegral_congr_fun (hW hB) fun ω _ => (congrFun hμ₁_eq ω).symm
        _ = ∫ ω in W ⁻¹' B, φ ω ∂μ :=
              setIntegral_condExp hmW_le hφ_int (measurableSet_comap.mpr ⟨B, hB, rfl⟩)
    have h2 : ∫ y in B, g₂ y ∂(Measure.map W μ) = ∫ ω in W' ⁻¹' B, φ ω ∂μ := by
      rw [hρ_eq]
      calc ∫ y in B, g₂ y ∂(Measure.map W' μ)
          = ∫ y, g₂ y ∂((μ.restrict (W' ⁻¹' B)).map W') := by rw [Measure.restrict_map hW' hB]
        _ = ∫ ω in W' ⁻¹' B, g₂ (W' ω) ∂μ :=
              integral_map hW'.aemeasurable.restrict hg₂_sm.aestronglyMeasurable
        _ = ∫ ω in W' ⁻¹' B, μ₂ ω ∂μ :=
              setIntegral_congr_fun (hW' hB) fun ω _ => (congrFun hμ₂_eq ω).symm
        _ = ∫ ω in W' ⁻¹' B, φ ω ∂μ :=
              setIntegral_condExp hmW'_le hφ_int (measurableSet_comap.mpr ⟨B, hB, rfl⟩)
    have h3 : ∫ ω in W ⁻¹' B, φ ω ∂μ = ∫ ω in W' ⁻¹' B, φ ω ∂μ := by
      rw [setIntegral_indicator (hX hA), setIntegral_indicator (hX hA),
        setIntegral_const, setIntegral_const]
      congr 1
      rw [Set.inter_comm (W ⁻¹' B), Set.inter_comm (W' ⁻¹' B)]
      have heq1 : (X ⁻¹' A) ∩ (W ⁻¹' B) = (fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B) := by
        ext ω; simp [Set.mem_prod]
      have heq2 : (X ⁻¹' A) ∩ (W' ⁻¹' B) = (fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B) := by
        ext ω; simp [Set.mem_prod]
      rw [heq1, heq2]
      have h_meas1 : μ ((fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B))
          = (Measure.map (fun ω => (X ω, W ω)) μ) (A ×ˢ B) :=
        (Measure.map_apply (hX.prodMk hW) (hA.prod hB)).symm
      have h_meas2 : μ ((fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B))
          = (Measure.map (fun ω => (X ω, W' ω)) μ) (A ×ˢ B) :=
        (Measure.map_apply (hX.prodMk hW') (hA.prod hB)).symm
      simp only [Measure.real, ENNReal.toReal_eq_toReal_iff]
      left
      rw [h_meas1, h_meas2, h_law]
    rw [h1, h3, ← h2]
  -- Push the square through `integral_map` on both sides.
  calc ∫ ω, μ₁ ω * μ₁ ω ∂μ
      = ∫ ω, (g₁ (W ω)) ^ 2 ∂μ := by
        refine integral_congr_ae (.of_forall fun ω => ?_)
        simp only [hμ₁_eq, Function.comp_apply, pow_two]
    _ = ∫ y, (g₁ y) ^ 2 ∂(Measure.map W μ) :=
        (integral_map hW.aemeasurable (hg₁_sm.pow 2).aestronglyMeasurable).symm
    _ = ∫ y, (g₂ y) ^ 2 ∂(Measure.map W μ) := by
        refine integral_congr_ae ?_; filter_upwards [hg_eq] with y hy; rw [hy]
    _ = ∫ ω, (g₂ (W' ω)) ^ 2 ∂μ := by
        rw [hρ_eq]; exact integral_map hW'.aemeasurable (hg₂_sm.pow 2).aestronglyMeasurable
    _ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := by
        refine integral_congr_ae (.of_forall fun ω => ?_)
        simp only [hμ₂_eq, Function.comp_apply, pow_two]

/-- **Kallenberg Lemma 1.3 (contraction-independence).** If `(X, W) =ᵈ (X, W')` and
`σ(W) ≤ σ(W')` (so `W` is a contraction of `W'`), then conditioning the indicator of `X` on the
finer `σ(W')` equals conditioning on the coarser `σ(W)`, almost everywhere. -/
private lemma condExp_indicator_eq_of_law_eq_of_comap_le [IsFiniteMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    (h_le : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap W' inferInstance)
    {A : Set α} (hA : MeasurableSet A) :
    μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[(X ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  have h_sq_eq_raw := integral_sq_condExp_eq_of_pair_law X W W' hX hW hW' h_law hA
  let φ : Ω → ℝ := (X ⁻¹' A).indicator (fun _ => (1 : ℝ))
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
  let mW' : MeasurableSpace Ω := MeasurableSpace.comap W' inferInstance
  have hmW_le : mW ≤ _ := measurable_iff_comap_le.mp hW
  have hmW'_le : mW' ≤ _ := measurable_iff_comap_le.mp hW'
  haveI hσW : SigmaFinite (μ.trim hmW_le) :=
    (inferInstance : IsFiniteMeasure (μ.trim hmW_le)).toSigmaFinite
  haveI hσW' : SigmaFinite (μ.trim hmW'_le) :=
    (inferInstance : IsFiniteMeasure (μ.trim hmW'_le)).toSigmaFinite
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) (hX hA)
  set μ₁ := μ[φ | mW] with hμ₁_def
  set μ₂ := μ[φ | mW'] with hμ₂_def
  have h_tower : μ[μ₂ | mW] =ᵐ[μ] μ₁ := condExp_condExp_of_le h_le hmW'_le
  have hφ_bdd : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1 := fun ω => by
    by_cases hω : ω ∈ X ⁻¹' A
    · have h : φ ω = 1 := Set.indicator_of_mem hω _
      rw [h]; exact ⟨zero_le_one, le_rfl⟩
    · have h : φ ω = 0 := Set.indicator_of_notMem hω _
      rw [h]; exact ⟨le_rfl, zero_le_one⟩
  -- `|φ| ≤ 1` a.e., so each conditional expectation `μ[φ | ·]` inherits the same bound via
  -- Mathlib's `ae_bdd_condExp_of_ae_bdd`; the helper is applied once per σ-algebra below.
  have hφ_abs : ∀ᵐ ω ∂μ, |φ ω| ≤ ((1 : NNReal) : ℝ) := by
    filter_upwards with ω
    rw [abs_of_nonneg (hφ_bdd ω).1, NNReal.coe_one]; exact (hφ_bdd ω).2
  have condExp_abs_le : ∀ m' : MeasurableSpace Ω, ∀ᵐ ω ∂μ, |μ[φ | m'] ω| ≤ 1 := fun m' => by
    simpa using ae_bdd_condExp_of_ae_bdd (m := m') (R := 1) hφ_abs
  have hμ₁_int : Integrable μ₁ μ := integrable_condExp
  have hμ₂_int : Integrable μ₂ μ := integrable_condExp
  have hμ₁_bound : ∀ᵐ ω ∂μ, ‖μ₁ ω‖ ≤ 1 := by
    filter_upwards [condExp_abs_le mW] with ω hω; rwa [Real.norm_eq_abs, hμ₁_def]
  have hμ₂_bound : ∀ᵐ ω ∂μ, ‖μ₂ ω‖ ≤ 1 := by
    filter_upwards [condExp_abs_le mW'] with ω hω; rwa [Real.norm_eq_abs, hμ₂_def]
  have hμ₁sq_int : Integrable (fun ω => μ₁ ω * μ₁ ω) μ :=
    hμ₁_int.bdd_mul hμ₁_int.aestronglyMeasurable hμ₁_bound
  have hμ₂sq_int : Integrable (fun ω => μ₂ ω * μ₂ ω) μ :=
    hμ₂_int.bdd_mul hμ₂_int.aestronglyMeasurable hμ₂_bound
  have hμ₂μ₁_int : Integrable (fun ω => μ₂ ω * μ₁ ω) μ :=
    hμ₁_int.bdd_mul hμ₂_int.aestronglyMeasurable hμ₂_bound
  -- Cross term `∫ μ₂ μ₁ = ∫ μ₁ μ₁` via pull-out and the tower property.
  have h_cross : ∫ ω, μ₂ ω * μ₁ ω ∂μ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
    have hμ₁_meas : StronglyMeasurable[mW] μ₁ := stronglyMeasurable_condExp
    have h_pullout := condExp_mul_of_stronglyMeasurable_right (m := mW) hμ₁_meas hμ₂μ₁_int hμ₂_int
    calc ∫ ω, μ₂ ω * μ₁ ω ∂μ
        = ∫ ω, μ[fun ω => μ₂ ω * μ₁ ω | mW] ω ∂μ := (integral_condExp hmW_le).symm
      _ = ∫ ω, μ[μ₂ | mW] ω * μ₁ ω ∂μ := integral_congr_ae h_pullout
      _ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
          refine integral_congr_ae ?_; filter_upwards [h_tower] with ω hω; rw [hω]
  have h_sq_eq : ∫ ω, μ₁ ω * μ₁ ω ∂μ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := h_sq_eq_raw
  -- `∫ (μ₂ - μ₁)² = 0`.
  have h_L2_zero : ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 ∂μ = 0 := by
    have h_expand : ∀ᵐ ω ∂μ,
        (μ₂ ω - μ₁ ω) ^ 2 = μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω) + μ₁ ω * μ₁ ω := by
      filter_upwards with ω; ring
    have hc2_int : Integrable (fun ω => 2 * (μ₂ ω * μ₁ ω)) μ := hμ₂μ₁_int.const_mul 2
    have hsub_int : Integrable (fun ω => μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω)) μ := hμ₂sq_int.sub hc2_int
    have h1 : ∫ ω, (μ₂ ω - μ₁ ω) ^ 2 ∂μ =
        ∫ ω, μ₂ ω * μ₂ ω ∂μ - 2 * ∫ ω, μ₂ ω * μ₁ ω ∂μ + ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
      rw [integral_congr_ae h_expand, integral_add hsub_int hμ₁sq_int,
        integral_sub hμ₂sq_int hc2_int, integral_const_mul]
    rw [h1, h_cross, h_sq_eq]; ring
  have h_diff_zero : ∀ᵐ ω ∂μ, (μ₂ ω - μ₁ ω) ^ 2 = 0 := by
    have h_diff_int : Integrable (μ₂ - μ₁) μ := hμ₂_int.sub hμ₁_int
    have h_diff_bound : ∀ᵐ ω ∂μ, ‖(μ₂ - μ₁) ω‖ ≤ 2 := by
      filter_upwards [hμ₁_bound, hμ₂_bound] with ω h₁ h₂
      rw [Real.norm_eq_abs, abs_le] at h₁ h₂
      simp only [Pi.sub_apply]
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    have h_sq_int : Integrable (fun ω => (μ₂ ω - μ₁ ω) ^ 2) μ := by
      have h_sq_eq_mul : (fun ω => (μ₂ ω - μ₁ ω) ^ 2)
          = fun ω => (μ₂ - μ₁) ω * (μ₂ - μ₁) ω := by funext ω; simp only [Pi.sub_apply]; ring
      rw [h_sq_eq_mul]
      exact h_diff_int.bdd_mul h_diff_int.aestronglyMeasurable h_diff_bound
    exact (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ fun ω => sq_nonneg _) h_sq_int).mp
      h_L2_zero
  filter_upwards [h_diff_zero] with ω hω
  nlinarith [sq_nonneg (μ₂ ω - μ₁ ω)]

/-- **Drop-info for the prefix `U`.** For a contractable process and `r ≤ m`, conditioning the
indicator of the prefix `U` on `σ(W') = σ(X r) ⊔ σ(W)` equals conditioning on `σ(W)`; here
`W = processShift X (m+1)` and `W' = processCons (X r) W`. -/
private lemma condExp_indicator_eq_of_contractable [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m) {A : Set (Fin r → α)} (hA : MeasurableSet A) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    let W' := processCons (fun ω => X r ω) W
    μ[(U ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[(U ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  intro U W W'
  have hU : Measurable U := measurable_pi_lambda _ fun i => hX_meas i.val
  have hW : Measurable W := measurable_processShift fun n => hX_meas (m + 1 + n)
  have hW' : Measurable W' :=
    measurable_processCons (hX_meas r) fun n => (measurable_pi_apply n).comp hW
  exact condExp_indicator_eq_of_law_eq_of_comap_le U W W' hU hW hW'
    (pair_law_eq_of_contractable hContr hX_meas r m hrm)
    (comap_le_comap_processCons (fun ω => X r ω) W) hA

/-! ### Conditional independence and the prefix-deletion identity (main target) -/

/-- **Prefix/tail conditional independence.** For a contractable process and `r ≤ m`, the value
`X r` is conditionally independent of the length-`r` prefix `U` given the far tail
`W = processShift X (m+1)`, packaged as Mathlib's `ProbabilityTheory.CondIndep` object.  This is the
primary result; the prefix-deletion drop-info identity is read off from it below. -/
theorem Contractable.condIndep_Xr_prefix_tail [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    CondIndep (MeasurableSpace.comap W inferInstance)
      (MeasurableSpace.comap (X r) inferInstance) (MeasurableSpace.comap U inferInstance)
      (measurable_processShift fun n => hX_meas (m + 1 + n)).comap_le μ := by
  intro U W
  let W' : Ω → ℕ → α := processCons (X r) W
  have hU_meas : Measurable U := measurable_pi_lambda _ fun i => hX_meas i.val
  have hW_meas : Measurable W := measurable_processShift fun n => hX_meas (m + 1 + n)
  have hmU : MeasurableSpace.comap U inferInstance ≤ ‹MeasurableSpace Ω› := hU_meas.comap_le
  have hmW : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› := hW_meas.comap_le
  have hmXr : MeasurableSpace.comap (X r) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (hX_meas r).comap_le
  -- `σ(W') = σ(X r) ⊔ σ(W)`, since `W'` conses `X r` onto the far tail `W`.
  have h_sup : MeasurableSpace.comap W' inferInstance
      = MeasurableSpace.comap (X r) inferInstance ⊔ MeasurableSpace.comap W inferInstance :=
    comap_processCons_eq_sup (X r) W
  -- Drop-`X r` form: conditioning a prefix indicator on `σ(X r) ⊔ σ(W)` collapses to `σ(W)`,
  -- supplied by the private drop-info wrapper `condExp_indicator_eq_of_contractable`.
  have h_drop : ∀ H, MeasurableSet[MeasurableSpace.comap U inferInstance] H →
      μ[H.indicator (fun _ => (1 : ℝ))
          | MeasurableSpace.comap (X r) inferInstance ⊔ MeasurableSpace.comap W inferInstance]
        =ᵐ[μ]
      μ[H.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
    rintro H ⟨A, hA, rfl⟩
    have h := condExp_indicator_eq_of_contractable hContr hX_meas hrm hA
    rw [← h_sup]
    exact h
  -- `CondIndep σ(W) σ(X r) σ(U)`: `X r` and the prefix `U` are independent given the far tail.
  exact condIndep_of_indicator_condExp_eq hmXr hmW hmU h_drop

/-- **Prefix-deletion conditional-expectation identity.** For a contractable process and `r ≤ m`,
conditioning the indicator of `X r` on `σ(U) ⊔ σ(W)` equals conditioning on `σ(W)`, where `U` is the
length-`r` prefix and `W = processShift X (m+1)` is the far tail.  This is read off from the
prefix/tail conditional independence `Contractable.condIndep_Xr_prefix_tail`. -/
theorem Contractable.condExp_indicator_prefix_sup_tail_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m) {B : Set α} (hB : MeasurableSet B) :
    let Y := X r
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    μ[(Y ⁻¹' B).indicator (fun _ => (1 : ℝ))
       | MeasurableSpace.comap U inferInstance ⊔ MeasurableSpace.comap W inferInstance]
      =ᵐ[μ]
    μ[(Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  intro Y U W
  have hU_meas : Measurable U := measurable_pi_lambda _ fun i => hX_meas i.val
  have hW_meas : Measurable W := measurable_processShift fun n => hX_meas (m + 1 + n)
  have hmU : MeasurableSpace.comap U inferInstance ≤ ‹MeasurableSpace Ω› := hU_meas.comap_le
  have hmW : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› := hW_meas.comap_le
  have hmXr : MeasurableSpace.comap (X r) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (hX_meas r).comap_le
  -- Symmetrise `CondIndep σ(W) σ(X r) σ(U)` to `CondIndep σ(W) σ(U) σ(X r)` and project.
  exact condExp_indicator_sup_eq_of_condIndep hmU hmW hmXr
    (Contractable.condIndep_Xr_prefix_tail hContr hX_meas hrm).symm ⟨B, hB, rfl⟩

end Probability

end TauCeti
