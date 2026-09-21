/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme
public import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.Exchangeability.PermutationExtension
import TauCeti.Probability.Kernel.Invariant
import TauCeti.Probability.Martingale.Convergence
import TauCeti.Probability.Exchangeability.Arrays.Windows

/-!
# Conditional array laws given the corner tail

Condition a jointly exchangeable array law on its corner-tail σ-algebra. Almost every resulting
conditional law is again jointly exchangeable, and it is jointly dissociated. These conditional
laws are therefore the ergodic components in the decomposition used by the Aldous--Hoover
representation. Constructing their vertex and cell noise is a separate step.

A separately exchangeable law keeps its stronger symmetry under the same conditioning, because a
corner-tail event is fixed by relabelling the two axes independently, and not only by the diagonal
relabellings. Its conditional laws are therefore separately exchangeable and jointly dissociated,
which is the pair of properties the global-variable-free separate coding asks for.

We use Mathlib's `condExpKernel` on array path space. Although the conditioning σ-algebra need
not be standard Borel, the space of arrays is standard Borel when the value space is. Thus no
regularity assumption is imposed on a sample space carrying an original array process.

The corner-tail events are fixed by every finitely supported permutation. Disintegration
uniqueness gives invariance of the conditional laws under each such permutation; countability
puts these statements on one almost-sure set. Finite-dimensional determinacy then gives full
joint exchangeability, including permutations with infinite support.

For dissociation, fix disjoint finite index sets `I` and `J`. Permutations fixing `I` and pushing
`J` past `n` leave conditional probabilities given the tail unchanged and move the square block
over `J` into the `n`-th corner-tail family. The conditional form of Lévy's downward factorization,
`MeasureTheory.condExp_inter_ae_eq_mul_iInf`, then makes the square blocks over `I` and `J`
conditionally independent given the tail. Mathlib's description of conditional independence through
`condExpKernel` turns this into independence under almost every conditional law. Countably many
pairs `I`, `J` share one null set, and independence of finite square blocks gives joint
dissociation (`jointlyDissociated_of_indep_blockSigma_finset`).

## Main results

* `TauCeti.Probability.JointlyExchangeable.ae_jointlyExchangeable_condExpKernel_arrayTail` —
  almost every conditional law given the corner tail is jointly exchangeable;
* `TauCeti.Probability.SeparatelyExchangeable.ae_separatelyExchangeable_condExpKernel_arrayTail` —
  almost every conditional law of a separately exchangeable law is separately exchangeable;
* `TauCeti.Probability.JointlyExchangeable.ae_jointlyDissociated_condExpKernel_arrayTail` —
  almost every conditional law given the corner tail is jointly dissociated.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Filter

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- Almost every conditional law of a jointly exchangeable array, given its corner tail, is
jointly exchangeable. The almost-sure set works simultaneously for all coordinate permutations. -/
theorem JointlyExchangeable.ae_jointlyExchangeable_condExpKernel_arrayTail
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    ∀ᵐ x ∂ρ, JointlyExchangeable
      (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) (fun p y => y p) := by
  have hm := arrayTail_le_ambient (X := fun p (y : ℕ × ℕ → α) => y p) 0
    (fun p _ _ => measurable_pi_apply p)
  have := hρ.smulInvariantMeasure
  have hinv (g : FinitaryPerm) :
      ∀ᵐ x ∂ρ,
        (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x).map (fun y => g • y) =
          condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x :=
    map_condExpKernel_ae_eq_of_invariant hm (measurePreserving_smul g ρ)
      (fun _ hs => Filter.EventuallyEq.of_eq
        (preimage_finitaryPerm_smul_array_eq_self_of_measurableSet_arrayTail hs g))
  filter_upwards [ae_all_iff.2 hinv] with x hx
  have : SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α)
      (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) := by
    constructor
    intro g s hs
    rw [← Measure.map_apply (measurable_const_smul g) hs, hx g]
  exact jointlyExchangeable_of_smulInvariantMeasure

/-- **Almost every conditional law of a separately exchangeable array, given its corner tail, is
separately exchangeable.** A corner-tail event is fixed by relabelling the two axes independently,
not only diagonally, so the stronger symmetry survives the conditioning. The almost-sure set works
simultaneously for all pairs of coordinate permutations. -/
theorem SeparatelyExchangeable.ae_separatelyExchangeable_condExpKernel_arrayTail
    (hρ : SeparatelyExchangeable ρ fun p x => x p) :
    ∀ᵐ x ∂ρ, SeparatelyExchangeable
      (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) (fun p y => y p) := by
  have hm := arrayTail_le_ambient (X := fun p (y : ℕ × ℕ → α) => y p) 0
    (fun p _ _ => measurable_pi_apply p)
  have hinv (g : FinitaryPerm × FinitaryPerm) :
      ∀ᵐ x ∂ρ,
        (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x).map
            (pairReindex (FinitaryPerm.toPerm g.1) (FinitaryPerm.toPerm g.2)) =
          condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x :=
    map_condExpKernel_ae_eq_of_invariant hm (hρ.measurePreserving_pairReindex _ _)
      (fun _ hs => Filter.EventuallyEq.of_eq
        (preimage_pairReindex_eq_self_of_measurableSet_arrayTail hs
          (FinitaryPerm.finite_compl_fixedBy_toPerm g.1)
          (FinitaryPerm.finite_compl_fixedBy_toPerm g.2)))
  filter_upwards [ae_all_iff.2 hinv] with x hx
  refine separatelyExchangeable_of_map_pairReindex_finitary fun σ τ hσ hτ => ?_
  have hστ := hx (FinitaryPerm.ofPerm σ hσ, FinitaryPerm.ofPerm τ hτ)
  rwa [FinitaryPerm.toPerm_ofPerm, FinitaryPerm.toPerm_ofPerm] at hστ

/-- Relabelling the array by a permutation does not change conditional probabilities given the
corner tail. -/
private theorem JointlyExchangeable.condExp_preimage_relabel_arrayTail
    (hρ : JointlyExchangeable ρ fun p x => x p) (σ : Equiv.Perm ℕ) {S : Set (ℕ × ℕ → α)}
    (hS : MeasurableSet S) :
    ρ⟦(fun (y : ℕ × ℕ → α) (p : ℕ × ℕ) => y (σ p.1, σ p.2)) ⁻¹' S |
      arrayTail (fun p (y : ℕ × ℕ → α) => y p)⟧ =ᵐ[ρ]
      ρ⟦S | arrayTail (fun p (y : ℕ × ℕ → α) => y p)⟧ := by
  have hm := arrayTail_le_ambient (X := fun p (y : ℕ × ℕ → α) => y p) 0
    (fun p _ _ => measurable_pi_apply p)
  have hT : Measurable fun (y : ℕ × ℕ → α) (p : ℕ × ℕ) => y (σ p.1, σ p.2) :=
    Measurable.of_eval fun p => measurable_pi_apply _
  refine (condExpKernel_ae_eq_condExp hm (hT hS)).symm.trans (EventuallyEq.trans ?_
    (condExpKernel_ae_eq_condExp hm hS))
  filter_upwards [hρ.ae_jointlyExchangeable_condExpKernel_arrayTail] with x hx
  rw [measureReal_def, measureReal_def, ← Measure.map_apply hT hS, jointlyExchangeable_iff.mp hx σ]
  exact congrArg (fun m : Measure (ℕ × ℕ → α) => (m S).toReal) Measure.map_id'

/-- Square blocks over disjoint finite index sets are conditionally independent given the corner
tail. -/
private theorem JointlyExchangeable.condExp_restrict_inter_arrayTail
    (hρ : JointlyExchangeable ρ fun p x => x p) {I J : Finset ℕ} (hIJ : Disjoint I J)
    {s : Set (↥(I ×ˢ I) → α)} {t : Set (↥(J ×ˢ J) → α)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ρ⟦(fun y : ℕ × ℕ → α => (I ×ˢ I).restrict y) ⁻¹' s ∩
        (fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y) ⁻¹' t |
      arrayTail (fun p (y : ℕ × ℕ → α) => y p)⟧ =ᵐ[ρ]
      ρ⟦(fun y : ℕ × ℕ → α => (I ×ˢ I).restrict y) ⁻¹' s |
        arrayTail (fun p (y : ℕ × ℕ → α) => y p)⟧ *
      ρ⟦(fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y) ⁻¹' t |
        arrayTail (fun p (y : ℕ × ℕ → α) => y p)⟧ := by
  classical
  -- relabelings fixing `I` and pushing `J` past `n`
  choose σ hσI hσJ using fun n ↦ I.exists_perm_eqOn_le_apply J hIJ n
  have hIT : ∀ n, (fun y : ℕ × ℕ → α => (I ×ˢ I).restrict y) ⁻¹' s ∩
      (fun (y : ℕ × ℕ → α) (p : ℕ × ℕ) => y (σ n p.1, σ n p.2)) ⁻¹'
        ((fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y) ⁻¹' t) =
      (fun (y : ℕ × ℕ → α) (p : ℕ × ℕ) => y (σ n p.1, σ n p.2)) ⁻¹'
        ((fun y : ℕ × ℕ → α => (I ×ˢ I).restrict y) ⁻¹' s ∩
          (fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y) ⁻¹' t) := by
    intro n
    rw [Set.preimage_inter]
    congr 1
    ext y
    simp only [Set.mem_preimage]
    congr! 1
    ext ⟨p, hp⟩
    rw [Finset.mem_product] at hp
    simp [hσI n _ hp.1, hσI n _ hp.2]
  have hBn : ∀ n, MeasurableSet[arrayTailFamily (fun p (y : ℕ × ℕ → α) => y p) n]
      ((fun (y : ℕ × ℕ → α) (p : ℕ × ℕ) => y (σ n p.1, σ n p.2)) ⁻¹'
        ((fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y) ⁻¹' t)) := by
    intro n
    have : Measurable[arrayTailFamily (fun p (y : ℕ × ℕ → α) => y p) n]
        fun y : ℕ × ℕ → α => (J ×ˢ J).restrict fun p : ℕ × ℕ => y (σ n p.1, σ n p.2) := by
      let : MeasurableSpace (ℕ × ℕ → α) := arrayTailFamily (fun p (y : ℕ × ℕ → α) => y p) n
      refine Measurable.of_eval fun q ↦ ?_
      have hq := Finset.mem_product.1 q.2
      exact measurable_arrayTailFamily_of_le (X := fun p (y : ℕ × ℕ → α) => y p)
        (hσJ n _ hq.1) (hσJ n _ hq.2)
    exact this ht
  have key := condExp_inter_ae_eq_mul_iInf (μ := ρ)
    (arrayTailFamily_antitone (fun p (y : ℕ × ℕ → α) => y p))
    (arrayTailFamily_le_ambient 0 fun p _ _ ↦ measurable_pi_apply p)
    ((Finset.measurable_restrict _) hs) hBn
    (B := (fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y) ⁻¹' t)
    (fun n ↦ by
      rw [← arrayTail_eq_iInf_arrayTailFamily]
      exact hρ.condExp_preimage_relabel_arrayTail (σ n) ((Finset.measurable_restrict _) ht))
    (fun n ↦ by
      rw [← arrayTail_eq_iInf_arrayTailFamily, hIT n]
      exact hρ.condExp_preimage_relabel_arrayTail (σ n)
        (((Finset.measurable_restrict _) hs).inter ((Finset.measurable_restrict _) ht)))
  rwa [← arrayTail_eq_iInf_arrayTailFamily] at key

/-- **Almost every conditional law of a jointly exchangeable array, given its corner tail, is
jointly dissociated.** Together with
`JointlyExchangeable.ae_jointlyExchangeable_condExpKernel_arrayTail`, almost every conditional law
is a jointly exchangeable, jointly dissociated array law. -/
theorem JointlyExchangeable.ae_jointlyDissociated_condExpKernel_arrayTail
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    ∀ᵐ x ∂ρ, JointlyDissociated
      (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) (fun p y => y p) := by
  have hm := arrayTail_le_ambient (X := fun p (y : ℕ × ℕ → α) => y p) 0
    (fun p _ _ => measurable_pi_apply p)
  -- for each pair of disjoint finite index sets, the square blocks are conditionally independent,
  -- hence independent under almost every conditional law
  have hfin : ∀ I J : Finset ℕ, Disjoint I J → ∀ᵐ x ∂ρ,
      IndepFun (fun y : ℕ × ℕ → α => (I ×ˢ I).restrict y)
        (fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y)
        (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) := by
    intro I J hIJ
    have hcond := (condIndepFun_iff_condExp_inter_preimage_eq_mul (hm' := hm) (μ := ρ)
      (Finset.measurable_restrict _) (Finset.measurable_restrict _)).2
      fun s t hs ht ↦ hρ.condExp_restrict_inter_arrayTail hIJ hs ht
    rw [condIndepFun_iff_map_prod_eq_prod_map_map (Finset.measurable_restrict _)
      (Finset.measurable_restrict _)] at hcond
    filter_upwards [ae_of_ae_trim hm hcond] with x hx
    rw [indepFun_iff_map_prod_eq_prod_map_map (Finset.measurable_restrict _).aemeasurable
      (Finset.measurable_restrict _).aemeasurable]
    rwa [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
      Kernel.map_apply _ (Finset.measurable_restrict _),
      Kernel.map_apply _ (Finset.measurable_restrict _)] at hx
  have hall : ∀ᵐ x ∂ρ, ∀ I J : Finset ℕ, Disjoint I J →
      IndepFun (fun y : ℕ × ℕ → α => (I ×ˢ I).restrict y)
        (fun y : ℕ × ℕ → α => (J ×ˢ J).restrict y)
        (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) := by
    simp only [ae_all_iff, Filter.eventually_imp_distrib_left]
    exact hfin
  filter_upwards [hall] with x hx
  exact (jointlyDissociated_coord_iff_indepFun_restrict _).2 hx

end TauCeti.Probability
