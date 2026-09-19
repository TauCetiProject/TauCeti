/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Basic
public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
import TauCeti.Probability.Exchangeability.Arrays.Extreme

/-!
# Global-free Aldous--Hoover codings are dissociated

Coding through a function that ignores its global variable gives the **ergodic form** of the
Aldous--Hoover representation, and the arrays it produces are dissociated as well as exchangeable:
two blocks over disjoint row sets and disjoint column sets read disjoint sets of noise coordinates
once the global one is out of the way, and the noise coordinates are independent.  This is the
easy direction of the ergodic form of the theorem.  The shared global coordinate obstructs this
disjoint-noise proof, and a nontrivial array built from global noise alone is not dissociated, by
`JointlyDissociated.measure_preimage_eq_zero_or_one_of_const`.

Conversely, the global variable of any joint coding of a jointly dissociated law can be dropped:
freezing it at almost any value leaves the law unchanged. The law of a coding is the mixture over
the uniform global variable of the laws of its frozen codings, each of which is jointly
exchangeable, and a jointly dissociated law is not a nontrivial mixture of jointly exchangeable
laws (`JointlyDissociated.ae_eq_of_comp_eq`). Hence the ergodic form of the representation
follows from the general one.

## Main results

* `TauCeti.Probability.AldousHoover.separatelyDissociated_separateArray_of_snd`;
* `TauCeti.Probability.AldousHoover.jointlyDissociated_jointArray_of_snd`;
* `TauCeti.Probability.AldousHoover.ae_map_jointArray_eq_of_jointlyDissociated` and
  `TauCeti.Probability.AldousHoover.exists_map_jointArray_snd_eq_of_jointlyDissociated`: a jointly
  dissociated law with a joint coding also has one that ignores its global variable.

## References

* D. Aldous, ["Representations for partially exchangeable arrays of random variables"]
  (https://doi.org/10.1016/0047-259X(81)90099-3), *Journal of Multivariate Analysis* 11
  (1981), 581--598.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

namespace AldousHoover

section Dissociation

variable {α : Type*} [MeasurableSpace α]

/-- The noise coordinates that the rectangular block along `e` and `f` of a separate
Aldous--Hoover coding reads, with the global coordinate left out. -/
private def separateBlockNoise (e f : ℕ → ℕ) : Set (NoiseIndex Axis (ℕ × ℕ)) :=
  {q | match q with
    | .global => False
    | .vertex .row i => i ∈ Set.range e
    | .vertex .column j => j ∈ Set.range f
    | .cell p => p.1 ∈ Set.range e ∧ p.2 ∈ Set.range f}

/-- Blocks over disjoint row sets and disjoint column sets read disjoint noise coordinates. The
global coordinate, which every block would read, is the only obstruction, and it has been removed
from `separateBlockNoise`. -/
private theorem disjoint_separateBlockNoise {e f e' f' : ℕ → ℕ}
    (he : Disjoint (Set.range e) (Set.range e')) (hf : Disjoint (Set.range f) (Set.range f')) :
    Disjoint (separateBlockNoise e f) (separateBlockNoise e' f') := by
  rw [Set.disjoint_left]
  rintro (_ | ⟨_ | _, i⟩ | p) hq hq' <;>
    simp only [separateBlockNoise, Set.mem_ofPred_eq] at hq hq'
  · exact Set.disjoint_left.mp he hq hq'
  · exact Set.disjoint_left.mp hf hq hq'
  · exact Set.disjoint_left.mp he hq.1 hq'.1

/-- A rectangular block of a global-free separate coding is measurable for the σ-algebra generated
by the noise coordinates it reads. -/
private theorem measurable_separateBlockNoise (g : I × I × I → α) (hg : Measurable g)
    (e f : ℕ → ℕ) :
    Measurable[blockSigma (fun (q : NoiseIndex Axis (ℕ × ℕ)) u => u q) (separateBlockNoise e f)]
      fun u (p : ℕ × ℕ) => separateArray (fun q => g q.2) (e p.1, f p.2) u := by
  refine @Measurable.of_eval (NoiseIndex Axis (ℕ × ℕ) → I) _ _
    (blockSigma (fun q u => u q) (separateBlockNoise e f)) _ _ fun p => ?_
  have hrow := measurable_blockSigma_of_mem
    (Z := fun (q : NoiseIndex Axis (ℕ × ℕ)) (u : NoiseIndex Axis (ℕ × ℕ) → I) => u q)
    (S := separateBlockNoise e f) (i := .vertex .row (e p.1)) (by simp [separateBlockNoise])
  have hcol := measurable_blockSigma_of_mem
    (Z := fun (q : NoiseIndex Axis (ℕ × ℕ)) (u : NoiseIndex Axis (ℕ × ℕ) → I) => u q)
    (S := separateBlockNoise e f) (i := .vertex .column (f p.2)) (by simp [separateBlockNoise])
  have hcell := measurable_blockSigma_of_mem
    (Z := fun (q : NoiseIndex Axis (ℕ × ℕ)) (u : NoiseIndex Axis (ℕ × ℕ) → I) => u q)
    (S := separateBlockNoise e f) (i := .cell (e p.1, f p.2)) (by simp [separateBlockNoise])
  simpa only [separateArray_apply, Function.comp_def] using
    hg.comp (hrow.prodMk (hcol.prodMk hcell))

/-- **A separate Aldous--Hoover coding that ignores its global variable is dissociated.** This is
the easy direction of the ergodic form of the representation; the coded array is also separately
exchangeable, by `separatelyExchangeable_separateArray` applied to `fun q => g q.2`. -/
theorem separatelyDissociated_separateArray_of_snd (g : I × I × I → α) (hg : Measurable g) :
    SeparatelyDissociated (noiseMeasure Axis (ℕ × ℕ)) (separateArray fun q => g q.2) :=
  separatelyDissociated_iff.mpr fun e f e' f' he hf =>
    indepFun_of_measurable_blockSigma
      ((iIndepFun_eval_noiseMeasure Axis (ℕ × ℕ)).precomp Subtype.val_injective)
      (fun q _ => measurable_pi_apply q) (disjoint_separateBlockNoise he hf)
      (measurable_separateBlockNoise g hg e f) (measurable_separateBlockNoise g hg e' f')

/-- The noise coordinates that the square block along `e` of a joint Aldous--Hoover coding reads,
with the global coordinate left out. A cell variable is read only when **both** its endpoints are
selected, which is what makes two such blocks over disjoint index sets disjoint. -/
private def jointBlockNoise (e : ℕ → ℕ) : Set (NoiseIndex Unit (Sym2 ℕ)) :=
  {q | match q with
    | .global => False
    | .vertex _ i => i ∈ Set.range e
    | .cell s => ∀ i ∈ s, i ∈ Set.range e}

/-- Square blocks over disjoint index sets read disjoint noise coordinates. -/
private theorem disjoint_jointBlockNoise {e e' : ℕ → ℕ}
    (he : Disjoint (Set.range e) (Set.range e')) :
    Disjoint (jointBlockNoise e) (jointBlockNoise e') := by
  rw [Set.disjoint_left]
  rintro (_ | ⟨_, i⟩ | s) hq hq' <;> simp only [jointBlockNoise, Set.mem_ofPred_eq] at hq hq'
  · exact Set.disjoint_left.mp he hq hq'
  · exact Set.disjoint_left.mp he (hq s.out.1 s.out_fst_mem) (hq' s.out.1 s.out_fst_mem)

/-- A square block of a global-free joint coding is measurable for the σ-algebra generated by the
noise coordinates it reads. -/
private theorem measurable_jointBlockNoise (g : I × I × I → α) (hg : Measurable g) (e : ℕ → ℕ) :
    Measurable[blockSigma (fun (q : NoiseIndex Unit (Sym2 ℕ)) u => u q) (jointBlockNoise e)]
      fun u (p : ℕ × ℕ) => jointArray (fun q => g q.2) (e p.1, e p.2) u := by
  refine @Measurable.of_eval (NoiseIndex Unit (Sym2 ℕ) → I) _ _
    (blockSigma (fun q u => u q) (jointBlockNoise e)) _ _ fun p => ?_
  have hcell : ∀ i ∈ s(e p.1, e p.2), i ∈ Set.range e := by
    intro i hi
    rcases Sym2.mem_iff.mp hi with rfl | rfl
    exacts [⟨p.1, rfl⟩, ⟨p.2, rfl⟩]
  have hfst := measurable_blockSigma_of_mem
    (Z := fun (q : NoiseIndex Unit (Sym2 ℕ)) (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
    (S := jointBlockNoise e) (i := .vertex () (e p.1)) (by simp [jointBlockNoise])
  have hsnd := measurable_blockSigma_of_mem
    (Z := fun (q : NoiseIndex Unit (Sym2 ℕ)) (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
    (S := jointBlockNoise e) (i := .vertex () (e p.2)) (by simp [jointBlockNoise])
  have hcellMeas := measurable_blockSigma_of_mem
    (Z := fun (q : NoiseIndex Unit (Sym2 ℕ)) (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
    (S := jointBlockNoise e) (i := .cell s(e p.1, e p.2))
    (by simpa only [jointBlockNoise, Set.mem_ofPred_eq] using hcell)
  simpa only [jointArray_apply, Function.comp_def] using
    hg.comp (hfst.prodMk (hsnd.prodMk hcellMeas))

/-- **A joint Aldous--Hoover coding that ignores its global variable is jointly dissociated.** It
need not be separately dissociated: the entries `X (i, j)` and `X (j, i)` read the same cell
variable `u (.cell s(i, j))`, and for a coding through a symmetric `g` they are equal, which
`SeparatelyDissociated.measure_preimage_eq_zero_or_one_of_symm` rules out unless they are trivial.
The coded array is also jointly exchangeable, by `jointlyExchangeable_jointArray` applied to
`fun q => g q.2`. -/
theorem jointlyDissociated_jointArray_of_snd (g : I × I × I → α) (hg : Measurable g) :
    JointlyDissociated (noiseMeasure Unit (Sym2 ℕ)) (jointArray fun q => g q.2) :=
  jointlyDissociated_iff.mpr fun e e' he =>
    indepFun_of_measurable_blockSigma
      ((iIndepFun_eval_noiseMeasure Unit (Sym2 ℕ)).precomp Subtype.val_injective)
      (fun q _ => measurable_pi_apply q) (disjoint_jointBlockNoise he)
      (measurable_jointBlockNoise g hg e) (measurable_jointBlockNoise g hg e')

end Dissociation

/-! ## Dropping the global variable of a dissociated coding -/

section GlobalNoise

variable {α : Type*} [MeasurableSpace α]

/-- The joint Aldous--Hoover noise with its global coordinate reset to `0`. Every coding that
ignores its global variable reads the same values from `u` and from `resetGlobal u`. -/
private def resetGlobal (u : NoiseIndex Unit (Sym2 ℕ) → I) : NoiseIndex Unit (Sym2 ℕ) → I
  | .global => 0
  | .vertex a i => u (.vertex a i)
  | .cell p => u (.cell p)

/-- `resetGlobal` reads only the non-global noise coordinates. -/
private theorem measurable_resetGlobal :
    Measurable[blockSigma (fun (q : NoiseIndex Unit (Sym2 ℕ)) u => u q) {q | q ≠ .global}]
      resetGlobal := by
  refine @Measurable.of_eval (NoiseIndex Unit (Sym2 ℕ) → I) _ _
    (blockSigma (fun q u => u q) {q | q ≠ .global}) _ _ fun q => ?_
  rcases q with _ | ⟨a, i⟩ | p
  · exact measurable_const
  · exact measurable_blockSigma_of_mem (Z := fun q (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
      (i := .vertex a i) (by simp)
  · exact measurable_blockSigma_of_mem (Z := fun q (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
      (i := .cell p) (by simp)

/-- Under the canonical noise law, the global coordinate is uniform and independent of the
other coordinates. -/
private theorem map_global_resetGlobal_noiseMeasure :
    (noiseMeasure Unit (Sym2 ℕ)).map (fun u => (u .global, resetGlobal u)) =
      (volume : Measure I).prod ((noiseMeasure Unit (Sym2 ℕ)).map resetGlobal) := by
  have hind : IndepFun (fun u : NoiseIndex Unit (Sym2 ℕ) → I => u .global) resetGlobal
      (noiseMeasure Unit (Sym2 ℕ)) :=
    indepFun_of_measurable_blockSigma (Z := fun q (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
      (S := {.global}) (T := {q | q ≠ .global})
      ((iIndepFun_eval_noiseMeasure Unit (Sym2 ℕ)).precomp Subtype.val_injective)
      (fun q _ => measurable_pi_apply q) (Set.disjoint_singleton_left.mpr fun h => h rfl)
      (measurable_blockSigma_of_mem (Z := fun q (u : NoiseIndex Unit (Sym2 ℕ) → I) => u q)
        (i := .global) rfl) measurable_resetGlobal
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
    (measurable_resetGlobal.mono (blockSigma_le _ fun q _ => measurable_pi_apply q)
      le_rfl).aemeasurable,
    map_eval_noiseMeasure]

/-- A joint coding with its global variable frozen, as a function of the frozen value and the
noise. -/
private def frozenArray (f : I × I × I × I → α) (x : I × (NoiseIndex Unit (Sym2 ℕ) → I)) :
    ℕ × ℕ → α :=
  fun p => jointArray (fun q => f (x.1, q.2)) p x.2

private theorem measurable_frozenArray {f : I × I × I × I → α} (hf : Measurable f) :
    Measurable (frozenArray f) := by
  refine Measurable.of_eval fun p => ?_
  simp only [frozenArray, jointArray_apply]
  fun_prop

/-- The laws of the frozen codings, as a Markov kernel in the frozen global value. -/
private def frozenKernel (f : I × I × I × I → α) : Kernel I (ℕ × ℕ → α) :=
  (Kernel.deterministic id measurable_id ×ₖ Kernel.const I (noiseMeasure Unit (Sym2 ℕ))).map
    (frozenArray f)

private theorem isMarkovKernel_frozenKernel {f : I × I × I × I → α} (hf : Measurable f) :
    IsMarkovKernel (frozenKernel f) :=
  Kernel.IsMarkovKernel.map _ (measurable_frozenArray hf)

private theorem frozenKernel_apply {f : I × I × I × I → α} (hf : Measurable f) (t : I) :
    frozenKernel f t =
      (noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray (fun q => f (t, q.2)) p u := by
  rw [frozenKernel, Kernel.map_apply _ (measurable_frozenArray hf), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_frozenArray hf) measurable_prodMk_left]
  -- the two maps agree by unfolding `frozenArray`
  rfl

/-- **The law of a joint coding is the mixture of the laws of its frozen codings** over the
uniform global variable: the global coordinate is independent of the coordinates the frozen
codings read. -/
private theorem frozenKernel_comp_volume {f : I × I × I × I → α} (hf : Measurable f) :
    frozenKernel f ∘ₘ (volume : Measure I) =
      (noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray f p u := by
  have hF := measurable_frozenArray hf
  have hRm : Measurable resetGlobal :=
    measurable_resetGlobal.mono (blockSigma_le _ fun q _ => measurable_pi_apply q) le_rfl
  have hread : (fun u p => jointArray f p u) =
      frozenArray f ∘ fun u => (u .global, resetGlobal u) := by
    funext u p
    simp [frozenArray, resetGlobal]
  have hreset : frozenArray f ∘ Prod.map id resetGlobal = frozenArray f := by
    funext x p
    simp [frozenArray, resetGlobal]
  rw [hread, ← Measure.map_map hF
      ((measurable_pi_apply (NoiseIndex.global : NoiseIndex Unit (Sym2 ℕ))).prodMk hRm),
    map_global_resetGlobal_noiseMeasure, ← Measure.map_id (μ := (volume : Measure I)),
    Measure.map_prod_map _ _ measurable_id hRm, Measure.map_id,
    Measure.map_map hF (measurable_id.prodMap hRm), hreset]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.map_apply hF hs,
    Measure.prod_apply (hF hs)]
  refine lintegral_congr fun t => ?_
  rw [frozenKernel, Kernel.map_apply' _ hF _ hs, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (hF hs), id]

/-- **For a dissociated law, almost every frozen global value gives an Aldous--Hoover coding.**
If a measurable joint coding `f` has a jointly dissociated law `ρ`, then for almost every value
`t` of the global variable, the coding `(a, b, c) ↦ f (t, a, b, c)`, which ignores the global
variable, already has law `ρ`. -/
theorem ae_map_jointArray_eq_of_jointlyDissociated [StandardBorelSpace α]
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyDissociated ρ fun p x => x p)
    {f : I × I × I × I → α} (hf : Measurable f)
    (hcode : (noiseMeasure Unit (Sym2 ℕ)).map (fun u p => jointArray f p u) = ρ) :
    ∀ᵐ t ∂(volume : Measure I),
      (noiseMeasure Unit (Sym2 ℕ)).map (fun u p => jointArray (fun q => f (t, q.2)) p u) = ρ := by
  have : IsProbabilityMeasure ρ :=
    hcode ▸ (Measure.isProbabilityMeasure_map_iff (measurable_jointArray f hf).aemeasurable).2
      inferInstance
  -- Each frozen coding is jointly exchangeable, and they mix to `ρ`; extremality of the
  -- dissociated law `ρ` then forces almost all of them to equal it.
  have hexch (t : I) : JointlyExchangeable (frozenKernel f t) fun p x => x p := by
    have hft : Measurable fun q : I × I × I × I => f (t, q.2) :=
      hf.comp (measurable_const.prodMk measurable_snd)
    rw [frozenKernel_apply hf]
    exact (jointlyExchangeable_map_iff (X := fun p u => jointArray (fun q => f (t, q.2)) p u)
      fun p => ((measurable_pi_apply p).comp (measurable_jointArray _ hft)).aemeasurable).2
      (jointlyExchangeable_jointArray _ hft)
  have := isMarkovKernel_frozenKernel hf
  filter_upwards [JointlyDissociated.ae_eq_of_comp_eq hρ (ae_of_all _ hexch)
    ((frozenKernel_comp_volume hf).trans hcode)] with t ht
  rwa [frozenKernel_apply hf] at ht

/-- **A dissociated law with an Aldous--Hoover coding has one that ignores its global
variable.** This is the ergodic form of the representation, obtained from a coding of the general
form. -/
theorem exists_map_jointArray_snd_eq_of_jointlyDissociated [StandardBorelSpace α]
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyDissociated ρ fun p x => x p)
    {f : I × I × I × I → α} (hf : Measurable f)
    (hcode : (noiseMeasure Unit (Sym2 ℕ)).map (fun u p => jointArray f p u) = ρ) :
    ∃ g : I × I × I → α, Measurable g ∧
      (noiseMeasure Unit (Sym2 ℕ)).map (fun u p => jointArray (fun q => g q.2) p u) = ρ := by
  obtain ⟨t, ht⟩ := (ae_map_jointArray_eq_of_jointlyDissociated hρ hf hcode).exists
  exact ⟨fun q => f (t, q), hf.comp (measurable_const.prodMk measurable_id), ht⟩

end GlobalNoise

end AldousHoover

end Probability

end TauCeti

end
