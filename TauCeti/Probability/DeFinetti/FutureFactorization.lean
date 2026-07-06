module

public import Mathlib.Probability.Independence.Conditional
public import TauCeti.Probability.Process.Tail
public import TauCeti.Probability.Exchangeability.Cylinder
public import TauCeti.Probability.Exchangeability.Contractability
import TauCeti.Probability.DeFinetti.PrefixDeletion
import TauCeti.Probability.DeFinetti.CondExpConvergence
import TauCeti.Probability.Exchangeability.PathSpace.ProcessShift

/-!
# Future-level factorization for the de Finetti martingale route

For a contractable process `X`, this file builds the finite-level product factorization of the
block-indicator conditional expectation given the future σ-algebra `tailFamily X (m+1)`. Everything
is phrased through Mathlib's `ProbabilityTheory.CondIndep`.

## Main results

* `block_coord_condIndep` — for `r < m`, the length-`r` prefix block and the single coordinate
  `X r` are conditionally independent given the future `tailFamily X (m+1)`, as Mathlib's
  `CondIndep`. This is Kallenberg's Lemma 1.3 input, packaged from the prefix/tail conditional
  independence `Contractable.condIndep_coord_prefix_tail`.
* `condExp_blockIndicatorProd_future_factor` — for `r ≤ m`, the conditional expectation of the
  length-`r` prefix indicator product factors as the product of the single-coordinate conditional
  expectations, with every coordinate replaced by `X 0`. The conditional-independence step is fed
  through Mathlib's product formula `ProbabilityTheory.condIndep_iff`.

Adapted from `cameronfreer/exchangeability`
(`DeFinetti/ViaMartingale/Factorization.lean`: `block_coord_condIndep`,
`condexp_indicator_inter_of_condIndep`, `finite_level_factorization`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Conditional independence of prefix and coordinate given the future (Kallenberg 1.3).**

For a contractable process `X` and `r < m`, the length-`r` prefix block `σ(X 0, …, X (r-1))` and the
single coordinate `σ(X r)` are conditionally independent given the future `tailFamily X (m+1)`, as
Mathlib's `CondIndep`. This is Kallenberg's Lemma 1.3 input. -/
lemma block_coord_condIndep
    [StandardBorelSpace Ω] [StandardBorelSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r < m) :
    CondIndep (tailFamily X (m + 1))
      (MeasurableSpace.comap (fun (ω : Ω) (i : Fin r) => X (i : ℕ) ω) inferInstance)
      (MeasurableSpace.comap (X r) inferInstance)
      (tailFamily_le_ambient (m + 1) fun k _ => hX_meas k) μ := by
  -- Identify the far tail `σ(processShift X (m+1))` with the future σ-algebra `tailFamily X (m+1)`.
  have hW_eq : MeasurableSpace.comap (processShift X (m + 1)) inferInstance
      = tailFamily X (m + 1) := by
    rw [tailFamily_eq_comap_shift X (m + 1)]
    congr 1
    funext ω n
    exact processShift_apply X (m + 1) n ω
  -- Symmetrise the #723 prefix/tail conditional independence and transport along `hW_eq`.
  simp only [← hW_eq]
  exact (Contractable.condIndep_coord_prefix_tail hX hX_meas (Nat.le_of_lt hrm)).symm

/-- **Finite-level future factorization.**

For a contractable process and any future level `m ≥ r`, the conditional expectation of the
length-`r` prefix indicator product factors as the product of the single-coordinate conditional
expectations, with every coordinate replaced by `X 0`:
```
μ[∏ i<r 𝟙_{X i ∈ C i} | tailFamily X (m+1)] = ∏ i<r μ[𝟙_{X 0 ∈ C i} | tailFamily X (m+1)]   a.e.
```
-/
lemma condExp_blockIndicatorProd_future_factor
    [StandardBorelSpace Ω] [StandardBorelSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) (hm : r ≤ m) :
    μ[blockIndicatorProd X (fun i : Fin r => (i : ℕ)) C | tailFamily X (m + 1)]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
      μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailFamily X (m + 1)] ω) := by
  classical
  induction r with
  | zero =>
    have hle : tailFamily X (m + 1) ≤ (inferInstance : MeasurableSpace Ω) :=
      tailFamily_le_ambient (m + 1) fun k _ => hX_meas k
    rw [blockIndicatorProd_empty X (fun i : Fin 0 => (i : ℕ)) C]
    refine (EventuallyEq.of_eq (condExp_const hle 1)).trans (EventuallyEq.of_eq ?_)
    funext ω; simp
  | succ r ih =>
    have hrm : r < m := Nat.lt_of_succ_le hm
    have hsplit : blockIndicatorProd X (fun i : Fin (r + 1) => (i : ℕ)) C
        = fun ω => blockIndicatorProd X (fun i : Fin r => (i : ℕ)) (fun j => C (Fin.castSucc j)) ω
            * (C (Fin.last r)).indicator (fun _ => (1 : ℝ)) (X r ω) := by
      funext ω
      simp only [blockIndicatorProd_apply]
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
    set cyl : Set Ω :=
      blockCylinder X (fun i : Fin r => (i : ℕ)) (fun j => C (Fin.castSucc j)) with hcyl
    set pre : Set Ω := X r ⁻¹' C (Fin.last r) with hpre
    have hcyl_ind : blockIndicatorProd X (fun i : Fin r => (i : ℕ)) (fun j => C (Fin.castSucc j))
        = cyl.indicator (fun _ => (1 : ℝ)) := by rw [hcyl, blockIndicatorProd_eq_indicator]
    have hpre_ind : (fun ω => (C (Fin.last r)).indicator (fun _ => (1 : ℝ)) (X r ω))
        = pre.indicator (fun _ => (1 : ℝ)) := by
      rw [hpre]; funext ω; simp only [Set.indicator_apply, Set.mem_preimage]
    have hblock_eq : blockIndicatorProd X (fun i : Fin (r + 1) => (i : ℕ)) C
        = (cyl ∩ pre).indicator (fun _ => (1 : ℝ)) := by
      rw [hsplit]; funext ω
      rw [congrFun hpre_ind ω, congrFun hcyl_ind ω]
      simp only [Set.indicator_apply, Set.mem_inter_iff]
      by_cases hc : ω ∈ cyl <;> by_cases hp : ω ∈ pre <;> simp [hc, hp]
    have hA_meas : MeasurableSet[MeasurableSpace.comap
        (fun (ω : Ω) (i : Fin r) => X (i : ℕ) ω) inferInstance] cyl :=
      ⟨Set.univ.pi fun j : Fin r => C (Fin.castSucc j), MeasurableSet.univ_pi fun j => hC _,
        by rw [hcyl, blockCylinder_eq_preimage_univ_pi]⟩
    have hB_meas : MeasurableSet[MeasurableSpace.comap (X r) inferInstance] pre :=
      ⟨C (Fin.last r), hC _, hpre.symm⟩
    -- CondIndep → condExp product formula, via Mathlib's `condIndep_iff`.
    have hbridge := (condIndep_iff (tailFamily X (m + 1))
        (MeasurableSpace.comap (fun (ω : Ω) (i : Fin r) => X (i : ℕ) ω) inferInstance)
        (MeasurableSpace.comap (X r) inferInstance)
        (tailFamily_le_ambient (m + 1) fun k _ => hX_meas k)
        ((measurable_pi_lambda (fun (ω : Ω) (i : Fin r) => X (i : ℕ) ω)
            fun i => hX_meas i).comap_le)
        ((hX_meas r).comap_le) μ).mp
      (block_coord_condIndep X hX hX_meas hrm) cyl pre hA_meas hB_meas
    have hcyl_ce : μ[cyl.indicator (fun _ => (1 : ℝ)) | tailFamily X (m + 1)]
        =ᵐ[μ] (fun ω => ∏ i : Fin r,
          μ[Set.indicator (C (Fin.castSucc i)) (fun _ => (1 : ℝ)) ∘ X 0
            | tailFamily X (m + 1)] ω) :=
      (condExp_congr_ae (EventuallyEq.of_eq hcyl_ind.symm)).trans
        (ih (fun j => C (Fin.castSucc j)) (fun j => hC _) (Nat.le_of_succ_le hm))
    have hpre_ce : μ[pre.indicator (fun _ => (1 : ℝ)) | tailFamily X (m + 1)]
        =ᵐ[μ] μ[Set.indicator (C (Fin.last r)) (fun _ => (1 : ℝ)) ∘ X 0 | tailFamily X (m + 1)] :=
      (condExp_congr_ae (EventuallyEq.of_eq hpre_ind.symm)).trans
        (hX.condExp_indicator_future_eq hX_meas (k := 0) (by omega) (by omega) (hC (Fin.last r)))
    calc μ[blockIndicatorProd X (fun i : Fin (r + 1) => (i : ℕ)) C | tailFamily X (m + 1)]
        _ =ᵐ[μ] μ[(cyl ∩ pre).indicator (fun _ => (1 : ℝ)) | tailFamily X (m + 1)] :=
            condExp_congr_ae (EventuallyEq.of_eq hblock_eq)
        _ =ᵐ[μ] μ[cyl.indicator (fun _ => (1 : ℝ)) | tailFamily X (m + 1)]
                  * μ[pre.indicator (fun _ => (1 : ℝ)) | tailFamily X (m + 1)] := hbridge
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                    μ[Set.indicator (C (Fin.castSucc i)) (fun _ => (1 : ℝ)) ∘ X 0
                      | tailFamily X (m + 1)] ω)
                  * μ[Set.indicator (C (Fin.last r)) (fun _ => (1 : ℝ)) ∘ X 0
                      | tailFamily X (m + 1)] ω) := hcyl_ce.mul hpre_ce
        _ =ᵐ[μ] (fun ω => ∏ i : Fin (r + 1),
                    μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailFamily X (m + 1)] ω) := by
            refine EventuallyEq.of_eq (funext fun ω => ?_)
            rw [Fin.prod_univ_castSucc]

end Probability

end TauCeti
