/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Basic
public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
import TauCeti.Probability.Exchangeability.Arrays.Extreme.Basic
import TauCeti.Probability.Process.Array.AldousHoover.Frozen

/-!
# Global-free Aldous--Hoover codings are dissociated

Coding through a function that ignores its global variable gives the **ergodic form** of the
Aldous--Hoover representation, and the arrays it produces are dissociated as well as exchangeable:
two blocks over disjoint row sets and disjoint column sets read disjoint sets of noise coordinates
once the global one is out of the way, and the noise coordinates are independent.  This is the
easy direction of the ergodic form of the theorem.  The shared global coordinate obstructs this
disjoint-noise proof, and a nontrivial array built from global noise alone is not dissociated, by
`JointlyDissociated.measure_preimage_eq_zero_or_one_of_const`.

Conversely, the global variable of any coding of a dissociated law can be dropped: freezing it at
almost any value leaves the law unchanged.  Freezing the global argument of a coding `f` at `t`
leaves the *frozen coding* `(a, b, c) ↦ f (t, a, b, c)`, which reads no global noise.  Since the
global noise coordinate is uniform and independent of the coordinates the frozen codings read, the
law of `f` is the mixture of the laws of its frozen codings over a uniform `t`
(`map_jointArray_eq_bind_frozen`, `map_separateArray_eq_bind_frozen`, in
`Probability.Process.Array.AldousHoover.Frozen`, where no symmetry hypothesis is needed).  Each
frozen coding is jointly exchangeable, and a jointly dissociated law is not a nontrivial mixture of
jointly exchangeable laws (`JointlyDissociated.ae_eq_of_comp_eq`), so almost every frozen coding
has the original law.  Hence the ergodic form of the representation follows from the general one,
for both array symmetries; and since the frozen codings of a separate coding are separately
exchangeable, hence jointly exchangeable, the separate statement too needs only joint dissociation
of the law.

## Main results

* `TauCeti.Probability.AldousHoover.separatelyDissociated_separateArray_of_snd`;
* `TauCeti.Probability.AldousHoover.jointlyDissociated_jointArray_of_snd`;
* `TauCeti.Probability.AldousHoover.ae_map_jointArray_eq_of_jointlyDissociated` and
  `TauCeti.Probability.AldousHoover.exists_map_jointArray_snd_eq_of_jointlyDissociated`: a jointly
  dissociated law with a joint coding also has one that ignores its global variable;
* `TauCeti.Probability.AldousHoover.ae_map_separateArray_eq_of_jointlyDissociated` and
  `TauCeti.Probability.AldousHoover.exists_map_separateArray_snd_eq_of_jointlyDissociated`: the
  same for a separate coding.

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

/-! ## Dropping the global variable of a coding of a dissociated law -/

section GlobalNoise

variable {α : Type*} [MeasurableSpace α] {κ ι : Type*}

/-- **A dissociated array law is the law of almost every member of a mixing family of codings.**
If `ρ` is jointly dissociated and is the uniform mixture of the laws of a measurable family of
noise-driven arrays `Φ t`, each jointly exchangeable, then almost every `Φ t` already has law
`ρ`. -/
private theorem ae_map_eq_of_jointlyDissociated [StandardBorelSpace α]
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyDissociated ρ fun p x => x p)
    {Φ : I → (NoiseIndex κ ι → I) → (ℕ × ℕ → α)}
    (hΦ : Measurable fun t => (noiseMeasure κ ι).map (Φ t))
    (hsec : ∀ t, Measurable (Φ t))
    (hexch : ∀ t, JointlyExchangeable (noiseMeasure κ ι) fun p u => Φ t u p)
    (hmix : (volume : Measure I).bind (fun t => (noiseMeasure κ ι).map (Φ t)) = ρ) :
    ∀ᵐ t ∂(volume : Measure I), (noiseMeasure κ ι).map (Φ t) = ρ := by
  -- the laws of the `Φ t` form a Markov kernel mixing to `ρ`; each is jointly exchangeable, and
  -- extremality of the dissociated law `ρ` forces almost all of them to equal it
  set K : Kernel I (ℕ × ℕ → α) := Kernel.mk _ hΦ with hK
  have : IsMarkovKernel K := ⟨fun t => by
    rw [hK, Kernel.coe_mk]
    infer_instance⟩
  have hcomp : K ∘ₘ (volume : Measure I) = ρ := by
    rw [hK, Kernel.coe_mk, hmix]
  have : IsProbabilityMeasure ρ := hcomp ▸ inferInstance
  refine JointlyDissociated.ae_eq_of_comp_eq (κ := K) hρ (ae_of_all _ fun t => ?_) hcomp
  rw [hK, Kernel.coe_mk]
  exact (jointlyExchangeable_map_iff (X := fun p u => Φ t u p)
    fun p => ((measurable_pi_apply p).comp (hsec t)).aemeasurable).2 (hexch t)

/-! ### The joint coding -/

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
  have hft (t : I) : Measurable fun q : I × I × I => f (t, q) :=
    hf.comp (measurable_const.prodMk measurable_id)
  exact ae_map_eq_of_jointlyDissociated hρ (measurable_map_jointArray_frozen hf)
    (fun t => measurable_jointArray _ ((hft t).comp measurable_snd))
    (fun t => jointlyExchangeable_jointArray _ ((hft t).comp measurable_snd))
    ((map_jointArray_eq_bind_frozen hf).symm.trans hcode)

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

/-! ### The separate coding -/

/-- **For a dissociated law, almost every frozen global value gives a separate Aldous--Hoover
coding.** The frozen codings are separately exchangeable, hence jointly exchangeable, so joint
dissociation of the law is all the argument needs; a separately dissociated law supplies it through
`SeparatelyDissociated.jointlyDissociated`. -/
theorem ae_map_separateArray_eq_of_jointlyDissociated [StandardBorelSpace α]
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyDissociated ρ fun p x => x p)
    {f : I × I × I × I → α} (hf : Measurable f)
    (hcode : (noiseMeasure Axis (ℕ × ℕ)).map (fun u p => separateArray f p u) = ρ) :
    ∀ᵐ t ∂(volume : Measure I),
      (noiseMeasure Axis (ℕ × ℕ)).map
        (fun u p => separateArray (fun q => f (t, q.2)) p u) = ρ := by
  have hft (t : I) : Measurable fun q : I × I × I => f (t, q) :=
    hf.comp (measurable_const.prodMk measurable_id)
  exact ae_map_eq_of_jointlyDissociated hρ (measurable_map_separateArray_frozen hf)
    (fun t => measurable_separateArray _ ((hft t).comp measurable_snd))
    (fun t => (separatelyExchangeable_separateArray _
      ((hft t).comp measurable_snd)).jointlyExchangeable)
    ((map_separateArray_eq_bind_frozen hf).symm.trans hcode)

/-- **A dissociated law with a separate Aldous--Hoover coding has one that ignores its global
variable.** This is the ergodic form of the separate representation, obtained from a coding of the
general form; the coding it produces is separately dissociated again, by
`separatelyDissociated_separateArray_of_snd`. -/
theorem exists_map_separateArray_snd_eq_of_jointlyDissociated [StandardBorelSpace α]
    {ρ : Measure (ℕ × ℕ → α)} (hρ : JointlyDissociated ρ fun p x => x p)
    {f : I × I × I × I → α} (hf : Measurable f)
    (hcode : (noiseMeasure Axis (ℕ × ℕ)).map (fun u p => separateArray f p u) = ρ) :
    ∃ g : I × I × I → α, Measurable g ∧
      (noiseMeasure Axis (ℕ × ℕ)).map (fun u p => separateArray (fun q => g q.2) p u) = ρ := by
  obtain ⟨t, ht⟩ := (ae_map_separateArray_eq_of_jointlyDissociated hρ hf hcode).exists
  exact ⟨fun q => f (t, q), hf.comp (measurable_const.prodMk measurable_id), ht⟩

end GlobalNoise

end AldousHoover

end Probability

end TauCeti

end
