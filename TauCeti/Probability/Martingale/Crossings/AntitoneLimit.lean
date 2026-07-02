module

public import Mathlib.Probability.Martingale.Convergence
public import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
public import TauCeti.Probability.Martingale.Crossings.Bounds

/-!
# Crossings: antitone-filtration convergence

The reverse-martingale convergence chain: a.e. existence of the limit of `μ[f | 𝔽 n]` along an
antitone filtration, and its identification as `μ[f | ⨅ n, 𝔽 n]`.

## Main results

- `condExp_exists_ae_limit_antitone`: a.e. limit existence for antitone filtrations, via the
  upcrossing inequality applied to the time-reversed martingales.
- `tendsto_ae_condExp_iInf_aux`: the a.e. limit equals `μ[f | ⨅ n, 𝔽 n]`, via uniform integrability
  and L¹-continuity of conditional expectation.

Adapted from `cameronfreer/exchangeability`
(`Probability/Martingale/Crossings/AntitoneLimit.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter Set Function

open scoped Topology ENNReal

open TauCeti.MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration.

This uses the upcrossing inequality applied to the time-reversed martingales to show
that the original sequence has finitely many upcrossings and downcrossings a.e.,
hence converges a.e. -/
private lemma condExp_exists_ae_limit_antitone
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ Xlim, (Integrable Xlim μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) := by
  -- Strategy: finite upcrossings a.e., then apply `tendsto_of_uncrossing_lt_top`
  -- First, extract the L¹ bound
  have hL1_bdd : ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ eLpNorm f 1 μ :=
    fun n => eLpNorm_one_condExp_le_eLpNorm _
  -- Extract finite L¹ bound
  have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  have hf_Lp_ne_top : eLpNorm f 1 μ ≠ ⊤ := hf_memLp.eLpNorm_ne_top
  set R := (eLpNorm f 1 μ).toNNReal with hR_def
  have hR : eLpNorm f 1 μ = ↑R := (ENNReal.coe_toNNReal hf_Lp_ne_top).symm
  -- Step 1: Show bounded liminf
  have hbdd_liminf : ∀ᵐ ω ∂μ, (liminf (fun n => ENorm.enorm (μ[f | 𝔽 n] ω)) atTop) < ⊤ := by
    refine ae_bdd_liminf_atTop_of_eLpNorm_bdd (R := R) one_ne_zero (fun n => ?_) (fun n => ?_)
    · -- Measurability
      exact stronglyMeasurable_condExp.measurable.mono (h_le n) le_rfl
    · -- Bound
      simpa [hR] using hL1_bdd n
  -- Step 2: Show finite upcrossings using L¹-boundedness. The expected number of
  -- upcrossings on `[a, b]` is bounded by a finite constant via
  -- `upcrossings_bdd_uniform`, so the upcrossings are themselves a.e. finite.
  have hupcross : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab
    have hab' : (↑a : ℝ) < (↑b : ℝ) := Rat.cast_lt.2 hab
    -- Get bound for upcrossings (forward direction)
    obtain ⟨C_up, h_C_up_finite, hC_up⟩ :=
      upcrossings_bdd_uniform h_antitone h_le f hf (↑a) (↑b) hab'
    -- Get bound for downcrossings via negated process (backward direction)
    obtain ⟨C_down, h_C_down_finite, hC_down⟩ := upcrossings_bdd_uniform h_antitone h_le
        (fun ω => -f ω) hf.neg (-↑b) (-↑a) (by linarith)
    -- Use max of both bounds as the uniform constant
    set C := max C_up C_down with hC_def
    have h_C_finite : C < ⊤ := max_lt h_C_up_finite h_C_down_finite
    -- Establish relationship between original and reversed sequence upcrossings
    -- Key: upcrossingsBefore (original, N) ≤ upcrossings (reversed_at_N)
    -- Bound upcrossings of original by upcrossings of negated reversed process
    have h_le_key (N : ℕ) (ω : Ω) :
        ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω)
        ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
            (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω := by
      -- Use the corrected inequality with N+1 horizon to avoid boundary issues
      have h_ineq := upcrossingsBefore_le_downcrossingsBefore_revProcess_succ
        (fun n => μ[f | 𝔽 n]) (↑a) (↑b) hab' N
      have h_orig_le : upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω
          ≤ downcrossingsBefore (↑a) (↑b) (revProcess (fun n => μ[f | 𝔽 n]) N) (N + 1) ω :=
        h_ineq ω
      -- Expand downcrossingsBefore to upcrossingsBefore with negProcess
      simp only [downcrossingsBefore_eq] at h_orig_le
      -- Recognize that revProcess of condExp = revCondExpFinite
      have h_rev_eq : negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)
                    = negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) := by
        funext n ω; simp only [negProcess_apply, revProcess_apply, revCondExpFinite_apply]
      -- Pick index (N+1) from the supremum definition of upcrossings
      have h_to_iSup :
          ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
              (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) (N + 1) ω)
            ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω := by
        simp only [MeasureTheory.upcrossings]
        apply le_iSup (fun M => (upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
            (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) M ω : ℝ≥0∞)) (N + 1)
      calc ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω)
          ≤ ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)) (N + 1) ω) :=
            Nat.cast_le.mpr h_orig_le
        _ = ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) (N + 1) ω) := by
              rw [h_rev_eq]
        _ ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω := h_to_iSup
    -- For each N, bound the expected upcrossings using the negated reversed martingale
    have h_N_bound : ∀ N,
        ∫⁻ ω, ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C := by
      intro N
      calc ∫⁻ ω, ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω) ∂μ
          ≤ ∫⁻ ω, upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω ∂μ :=
            lintegral_mono (h_le_key N)
        _ = ∫⁻ ω, downcrossings (↑a) (↑b) (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω ∂μ := by
            -- Use identity: up(-b, -a, -X) = down(a, b, X)
            rw [show (fun ω => upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                    (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω)
                   = (fun ω => downcrossings (↑a) (↑b)
                    (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω) from
                upcrossings_neg_flip_eq_downcrossings (↑a) (↑b)
                  (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)]
        _ ≤ C := by
            -- Rewrite `downcrossings(a,b,X) = upcrossings(-b,-a,-X)`
            -- (`upcrossings_neg_flip_eq_downcrossings`), recognise
            -- `negProcess (revCondExpFinite f) =ᵐ revCondExpFinite (-f)` (via `condExp_neg`), and
            -- `upcrossings_bdd_uniform` to `-f` on `[-b,-a]` to get the
            -- precomputed `C_down` bound.
            calc ∫⁻ ω, downcrossings (↑a) (↑b) (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω ∂μ
                = ∫⁻ ω, upcrossings (-↑b) (-↑a)
                    (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω ∂μ := by
                    simp only [upcrossings_neg_flip_eq_downcrossings]
              _ = ∫⁻ ω, upcrossings (-↑b) (-↑a)
                    (fun n => revCondExpFinite (μ := μ) (fun x => -f x) 𝔽 N n) ω ∂μ := by
                    -- lintegral_congr_ae: processes agree ae at all times → upcrossings agree ae
                    apply lintegral_congr_ae
                    -- Get ae equality at each time index via countable intersection
                    have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n,
                        negProcess (fun m => revCondExpFinite (μ := μ) f 𝔽 N m) n ω =
                        revCondExpFinite (μ := μ) (fun x => -f x) 𝔽 N n ω := by
                      rw [ae_all_iff]
                      intro n
                      simp only [negProcess_apply, revCondExpFinite_apply]
                      exact (condExp_neg f (𝔽 (N - n))).symm
                    filter_upwards [h_ae_eq] with ω hω
                    simp [MeasureTheory.upcrossings,
                          upcrossingsBefore_congr (fun k _ => hω k)]
              _ ≤ C_down := hC_down N
              _ ≤ C := le_max_right C_up C_down
    -- The sequence `μ[f | 𝔽 n]` is adapted to the constant ambient filtration; used
    -- below for both `measurable_upcrossingsBefore` and `measurable_upcrossings`.
    let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
      { seq := fun _ => (inferInstance : MeasurableSpace Ω)
        mono' := fun _ _ _ => le_refl _
        le' := fun _ => le_refl _ }
    have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) :=
      fun n => stronglyMeasurable_condExp.mono (h_le n)
    -- Use monotone convergence on the ORIGINAL process (which IS monotone in N)
    have h_exp_orig : ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
      -- Set U N ω := upcrossingsBefore for the original process
      set U : ℕ → Ω → ℝ≥0∞ :=
        fun N ω => (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) with hU
      -- Monotonicity in N (pathwise): more time allows more completed crossings
      have hU_mono : Monotone U := by
        intro m n hmn ω
        simp only [hU]
        have := upcrossingsBefore_mono (f := fun n => μ[f | 𝔽 n]) hab' hmn ω
        exact Nat.cast_le.2 this
      -- Measurability (via the constant filtration `ℱ` set up above)
      have hU_meas : ∀ N, Measurable (U N) := fun _ =>
        measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab')
      -- Apply monotone convergence theorem
      have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := lintegral_iSup hU_meas hU_mono
      -- Bound the supremum of integrals
      have : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := iSup_le h_N_bound
      -- Conclude: upcrossings = ⨆ N, upcrossingsBefore N
      simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans this
    -- Apply ae_lt_top: measurable function with finite expectation is a.e. finite
    refine ae_lt_top ?_ (lt_of_le_of_lt h_exp_orig h_C_finite).ne
    exact h_adapted.measurable_upcrossings hab'
  -- Step 3: Apply convergence theorem to get pointwise limits
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c) := by
    filter_upwards [hbdd_liminf, hupcross] with ω hω₁ hω₂
    -- Convert enorm bound to nnnorm bound (they're equal via coercion)
    have hω₁' : (liminf (fun n => ENNReal.ofNNReal (nnnorm (μ[f | 𝔽 n] ω))) atTop) < ⊤ := by
      -- `ENorm.enorm x = ↑(nnnorm x)` for reals
      simpa only [enorm_eq_nnnorm] using hω₁
    exact tendsto_of_uncrossing_lt_top hω₁' hω₂
  -- Step 4: Define the limit function using classical choice
  classical
  let Xlim : Ω → ℝ := fun ω =>
    if h : ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c)
    then Classical.choose h
    else 0
  -- Step 5: Show Xlim has the desired properties
  use Xlim
  constructor
  · -- Integrability of Xlim (follows from Fatou + L¹ boundedness)
    -- Xlim is a.e. limit of integrable functions with uniform L¹ bound
    have hXlim_ae_meas : AEStronglyMeasurable Xlim μ := by
      apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => μ[f | 𝔽 n])
      · intro n
        have : StronglyMeasurable[𝔽 n] (μ[f | 𝔽 n]) := stronglyMeasurable_condExp
        exact this.mono (h_le n) |>.aestronglyMeasurable
      · filter_upwards [h_ae_conv] with ω hω
        simpa [Xlim, hω] using Classical.choose_spec hω
    -- By Fatou: ‖Xlim‖₁ ≤ liminf ‖μ[f | 𝔽 n]‖₁ ≤ ‖f‖₁ < ∞
    have hXlim_norm : HasFiniteIntegral Xlim μ := by
      rw [hasFiniteIntegral_iff_norm]
      -- Apply Fatou for ofReal ‖·‖
      have h_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω)) := by
        filter_upwards [h_ae_conv] with ω hω
        simpa [Xlim, hω] using Classical.choose_spec hω
      -- Measurability proof (per-index) for the Fatou step
      have hmeas_n : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) μ := fun n =>
        ((stronglyMeasurable_condExp (f := f) (m := 𝔽 n) (μ := μ)).mono
          (h_le n)).norm.measurable.ennreal_ofReal.aemeasurable
      calc
        ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
            ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop := by
              -- Fatou along the a.e. limit: rewrite ‖Xlim‖ as the a.e. `liminf` of ‖μ[f|𝔽 n]‖
              -- (via `Tendsto.liminf_eq`), then apply Mathlib's `lintegral_liminf_le'`.
              have hae_ofReal : ∀ᵐ ω ∂μ,
                  Tendsto (fun n => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) atTop
                    (nhds (ENNReal.ofReal ‖Xlim ω‖)) :=
                h_ae_tendsto.mono fun ω hω =>
                  ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hω
              calc ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
                  = ∫⁻ ω, liminf (fun n => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) atTop ∂μ :=
                    lintegral_congr_ae (hae_ofReal.mono fun ω hω => hω.liminf_eq.symm)
                _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop :=
                    lintegral_liminf_le' hmeas_n
        _ ≤ ↑R := by
              rw [liminf_le_iff]
              intro b hb
              apply Eventually.frequently
              rw [eventually_atTop]
              use 0
              intro n _
              calc ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ
                  = ∫⁻ ω, ‖μ[f | 𝔽 n] ω‖ₑ ∂μ := by
                    congr 1; ext ω
                    rw [Real.enorm_eq_ofReal_abs]
                    simp only [Real.norm_eq_abs]
                _ = eLpNorm (μ[f | 𝔽 n]) 1 μ := MeasureTheory.eLpNorm_one_eq_lintegral_enorm.symm
                _ ≤ eLpNorm f 1 μ := hL1_bdd n
                _ = ↑R := hR
                _ < b := hb
        _ < ⊤ := ENNReal.coe_lt_top
    exact ⟨hXlim_ae_meas, hXlim_norm⟩
  · -- A.e. convergence to Xlim
    filter_upwards [h_ae_conv] with ω hω
    simpa [Xlim, hω] using Classical.choose_spec hω

/-- **Key lemma: a.e. limit of an adapted antitone sequence is `F_inf`-AEStronglyMeasurable.**

For antitone filtration 𝔽 with F_inf = ⨅ 𝔽, if each Xn is 𝔽 n-strongly-measurable and
Xn → Xlim a.e., then Xlim is AEStronglyMeasurable[F_inf].

The key observation: For antitone 𝔽 (𝔽 n decreases as n increases):
- For n ≥ N: 𝔽 n ⊆ 𝔽 N (larger index = smaller σ-algebra)
- So {Xn > a} ∈ 𝔽 n ⊆ 𝔽 N for n ≥ N
- The lim sup set ⋂_N ⋃_{n≥N} {Xn > a} ∈ ⋂_N 𝔽 N = F_inf
- Hence Xlim is F_inf-measurable (up to a.e. equality)

This is crucial for showing that reverse martingale limits satisfy μ[Xlim | F_inf] = Xlim. -/
private lemma aestronglyMeasurable_iInf_of_tendsto_ae_antitone
    {𝔽 : ℕ → MeasurableSpace Ω} (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {g : ℕ → Ω → ℝ} {Xlim : Ω → ℝ}
    (hg_meas : ∀ n, StronglyMeasurable[𝔽 n] (g n))
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (Xlim ω))) :
    AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ := by
  -- Compose the two `SigmaAlgebraHelpers` lemmas: first show
  -- `AEStronglyMeasurable[𝔽 N] Xlim` for each `N` by feeding the shifted
  -- sequence `g (n + N)` into `aestronglyMeasurable_of_tendsto_ae_of_le`; then
  -- combine over `N` via `aestronglyMeasurable_iInf_antitone`.
  refine aestronglyMeasurable_iInf_antitone (μ := μ) h_antitone h_le Xlim (fun N => ?_)
  refine aestronglyMeasurable_of_tendsto_ae_of_le (μ := μ) (h_le N) (f := fun n => g (n + N))
    (fun n => (hg_meas (n + N)).measurable.mono
      (h_antitone (Nat.le_add_left N n)) le_rfl) ?_
  filter_upwards [h_tendsto] with ω hω
  exact hω.comp (Filter.tendsto_add_atTop_nat N)

/-- Identification: the a.s. limit equals `μ[f | ⨅ n, 𝔽 n]`.

Uses uniform integrability to pass from a.e. convergence to L¹ convergence,
then uses L¹-continuity of conditional expectation to identify the limit. -/
lemma tendsto_ae_condExp_iInf_aux
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical
  -- 1) Get a.s. limit Xlim
  obtain ⟨Xlim, hXlimint, h_tendsto⟩ :=
    condExp_exists_ae_limit_antitone (μ := μ) h_antitone h_le f hf
  -- 2) UI ⟹ L¹ convergence via Vitali
  have hUI : UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ := hf.uniformIntegrable_condExp h_le
  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memLp_one_iff_integrable.2 hXlimint
    · exact hUI.unifIntegrable
    · exact h_tendsto
  -- Prove Xlim is AEStronglyMeasurable[⨅ 𝔽] BEFORE introducing F_inf alias
  -- This avoids type class unification issues between F_inf and ⨅ 𝔽
  have hXlim_iInf_meas : AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ :=
    aestronglyMeasurable_iInf_of_tendsto_ae_antitone h_antitone h_le
      (fun n => stronglyMeasurable_condExp) h_tendsto
  -- 3) Pass limit through condExp at F_inf := ⨅ n, 𝔽 n
  set F_inf := iInf 𝔽 with hF_inf_def
  -- Tower property: For every n, μ[μ[f | 𝔽 n] | F_inf] = μ[f | F_inf]
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | F_inf] =ᵐ[μ] μ[f | F_inf] :=
    fun n => condExp_condExp_of_le (iInf_le 𝔽 n) (h_le n)
  -- Final identification: Xlim = μ[f | F_inf]
  -- Strategy: Use L¹-continuity of condExp (non-circular approach)
  have hF_inf_le : F_inf ≤ _ := le_trans (iInf_le 𝔽 0) (h_le 0)
  set Y := μ[f | F_inf] with hY_def
  set Xn : ℕ → Ω → ℝ := fun n => μ[f | 𝔽 n] with hXn_def
  -- Non-circular proof: bound ‖μ[Xlim | F_inf] - Y‖₁ by ‖Xlim - Xn‖₁ via triangle + contraction
  -- Then let n → ∞ using L¹ convergence to get μ[Xlim | F_inf] =ᵐ Y
  -- This avoids using (or assuming) Xlim = Y to prove facts used to show Xlim = Y
  -- First, relate hL1_conv to Xn notation
  have hL1_conv_Xn : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0) := by
    simpa [hXn_def, eLpNorm_sub_comm] using hL1_conv
  -- Key inequality: ‖μ[Xlim | F_inf] - Y‖₁ ≤ ‖Xlim - Xn n‖₁ for all n
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    -- Triangle: (μ[Xlim|F_inf] - Y) = (μ[Xlim|F_inf] - μ[Xn|F_inf]) + (μ[Xn|F_inf] - Y)
    have htri : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ
                  + eLpNorm (μ[Xn n | F_inf] - Y) 1 μ := by
      have : μ[Xlim | F_inf] - Y
              = (μ[Xlim | F_inf] - μ[Xn n | F_inf]) + (μ[Xn n | F_inf] - Y) := by ring
      rw [this]
      refine eLpNorm_add_le ?_ ?_ ?_
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · norm_num
    -- Second term is 0 by tower property
    have hzero : eLpNorm (μ[Xn n | F_inf] - Y) 1 μ = 0 := by
      have : μ[Xn n | F_inf] =ᵐ[μ] Y := by simpa [Xn, Y, hY_def, hXn_def] using h_tower n
      have : μ[Xn n | F_inf] - Y =ᵐ[μ] 0 := by filter_upwards [this] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae this]
      simp
    -- First term ≤ ‖Xlim - Xn‖₁ by L¹-contraction + linearity (condExp_sub)
    have hfirst : eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ
        ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      -- linearity a.e.: μ[Xlim|F_inf] - μ[Xn|F_inf] = μ[Xlim - Xn | F_inf]
      have hsub : μ[Xlim | F_inf] - μ[Xn n | F_inf] =ᵐ[μ] μ[Xlim - Xn n | F_inf] :=
        (condExp_sub hXlimint integrable_condExp F_inf).symm
      -- contraction: ‖μ[g|F]‖₁ ≤ ‖g‖₁
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_one_condExp_le_eLpNorm _
    -- Combine: triangle + zero + contraction
    calc eLpNorm (μ[Xlim | F_inf] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ
            + eLpNorm (μ[Xn n | F_inf] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst
  -- Take limits: constant ≤ sequence → 0, so constant = 0
  have hCE_eqY : μ[Xlim | F_inf] =ᵐ[μ] Y := by
    -- From h_bound: eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ for all n
    -- Since Xn → Xlim in L¹, RHS → 0, so LHS = 0
    have h_norm_zero : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ = 0 := by
      refine le_antisymm ?_ bot_le
      -- Constant ≤ sequence → 0 means constant = 0
      have : ∀ n, eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := h_bound
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hL1_conv_Xn (Eventually.of_forall this)
    rw [eLpNorm_eq_zero_iff (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      one_ne_zero] at h_norm_zero
    -- h_norm_zero : μ[Xlim | F_inf] - Y =ᵐ 0
    filter_upwards [h_norm_zero] with ω hω
    simp only [Pi.zero_apply] at hω
    exact sub_eq_zero.mp hω
  -- Xlim is F_inf-a.e.-measurable (as a.e. limit of F_inf-measurable functions)
  -- Therefore μ[Xlim | F_inf] = Xlim
  -- Combined with hCE_eqY : μ[Xlim | F_inf] =ᵐ Y, we get Y =ᵐ Xlim
  have hXlim_eq : Y =ᵐ[μ] Xlim := by
    -- First prove μ[Xlim | F_inf] = Xlim using the fact that Xlim is (essentially) F_inf-measurable
    -- Xlim is the limit of F_inf-measurable functions, so is itself F_inf-measurable
    -- `Xlim` is `AEStronglyMeasurable[F_inf]` via the earlier `hXlim_iInf_meas`
    -- (`F_inf := iInf 𝔽 = ⨅ n, 𝔽 n` definitionally); apply
    -- `condExp_of_aestronglyMeasurable'`.
    have hXlim_condExp_self : μ[Xlim | F_inf] =ᵐ[μ] Xlim :=
      condExp_of_aestronglyMeasurable' hF_inf_le hXlim_iInf_meas hXlimint
    -- Now use L¹-continuity: μ[Xlim | F_inf] =ᵐ Y and μ[Xlim | F_inf] =ᵐ Xlim
    -- Therefore Y =ᵐ Xlim
    exact hCE_eqY.symm.trans hXlim_condExp_self
  -- Return the desired result: combine h_tendsto with hXlim_eq
  -- We have: h_tendsto : μ[f|𝔽 n] → Xlim
  --          hXlim_eq  : Y =ᵐ Xlim (where Y = μ[f|F_inf])
  -- Goal: μ[f|𝔽 n] → Y
  filter_upwards [h_tendsto, hXlim_eq] with ω h_tend h_eq
  -- h_tend : μ[f|𝔽 n] ω → Xlim ω
  -- h_eq : Y ω = Xlim ω
  -- Want: μ[f|𝔽 n] ω → Y ω
  rw [h_eq]
  exact h_tend

end ProbabilityTheory
