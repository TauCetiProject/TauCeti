/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Probability.Process.Array.AldousHoover.Basic
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Freezing the global variable of an Aldous--Hoover coding

Freezing the global argument of an Aldous--Hoover coding `f` at a value `t` leaves the *frozen
coding* `(a, b, c) ↦ f (t, a, b, c)`, which reads no global noise.  Since the global noise
coordinate is uniform and independent of the coordinates the frozen codings read, the law of the
array coded by `f` is the mixture, over a uniform `t`, of the laws of the arrays coded by its
frozen codings.  Read from right to left, the same identity assembles one coding out of a
measurable family of global-free ones.

This is a statement about the canonical noise law alone and involves no symmetry hypothesis on an
array law.  It is how a coding of a dissociated array law is reduced to one that ignores its global
variable, and how the graph law of a joint coding is written as a mixture of graphon sampling laws.

## Main results

* `TauCeti.Probability.AldousHoover.measurable_map_jointArray_frozen` and
  `TauCeti.Probability.AldousHoover.measurable_map_separateArray_frozen`: the laws of the frozen
  codings depend measurably on the frozen value;
* `TauCeti.Probability.AldousHoover.map_jointArray_eq_bind_frozen` and
  `TauCeti.Probability.AldousHoover.map_separateArray_eq_bind_frozen`: the law of a coding is the
  uniform mixture of the laws of its frozen codings.

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

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {κ ι : Type*}

/-! ## Mixing over the global coordinate -/

/-- Aldous--Hoover noise with its global coordinate reset to `0`. A coding that ignores its global
variable reads the same values from `u` and from `resetGlobal u`. -/
private def resetGlobal (u : NoiseIndex κ ι → I) : NoiseIndex κ ι → I
  | .global => 0
  | .vertex a i => u (.vertex a i)
  | .cell p => u (.cell p)

/-- `resetGlobal` reads only the non-global noise coordinates. -/
private theorem measurable_resetGlobal :
    Measurable[blockSigma (fun (q : NoiseIndex κ ι) u => u q) {q | q ≠ .global}]
      (resetGlobal (κ := κ) (ι := ι)) := by
  refine @Measurable.of_eval (NoiseIndex κ ι → I) _ _
    (blockSigma (fun q u => u q) {q | q ≠ .global}) _ _ fun q => ?_
  rcases q with _ | ⟨a, i⟩ | p
  · exact measurable_const
  · exact measurable_blockSigma_of_mem (Z := fun q (u : NoiseIndex κ ι → I) => u q)
      (i := .vertex a i) (by simp)
  · exact measurable_blockSigma_of_mem (Z := fun q (u : NoiseIndex κ ι → I) => u q)
      (i := .cell p) (by simp)

/-- Under the canonical noise law, the global coordinate is uniform and independent of the
other coordinates. -/
private theorem map_global_resetGlobal_noiseMeasure :
    (noiseMeasure κ ι).map (fun u => (u .global, resetGlobal u)) =
      (volume : Measure I).prod ((noiseMeasure κ ι).map resetGlobal) := by
  have hind : IndepFun (fun u : NoiseIndex κ ι → I => u .global) resetGlobal
      (noiseMeasure κ ι) :=
    indepFun_of_measurable_blockSigma (Z := fun q (u : NoiseIndex κ ι → I) => u q)
      (S := {.global}) (T := {q | q ≠ .global})
      ((iIndepFun_eval_noiseMeasure κ ι).precomp Subtype.val_injective)
      (fun q _ => measurable_pi_apply q) (Set.disjoint_singleton_left.mpr fun h => h rfl)
      (measurable_blockSigma_of_mem (Z := fun q (u : NoiseIndex κ ι → I) => u q)
        (i := .global) rfl) measurable_resetGlobal
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
    (measurable_resetGlobal.mono (blockSigma_le _ fun q _ => measurable_pi_apply q)
      le_rfl).aemeasurable,
    map_eval_noiseMeasure]

/-- **The law of a noise-driven family read at its own global coordinate is the mixture of the
laws of its frozen sections** over the uniform global variable: the global coordinate is
independent of the coordinates the frozen sections read. -/
private theorem bind_map_eq_map_global {Φ : I → (NoiseIndex κ ι → I) → β}
    (hΦ : Measurable (Function.uncurry Φ))
    (hfree : ∀ t u, Φ t u = Φ t (resetGlobal u)) :
    (volume : Measure I).bind (fun t => (noiseMeasure κ ι).map (Φ t)) =
      (noiseMeasure κ ι).map fun u => Φ (u .global) u := by
  have hRm : Measurable (resetGlobal (κ := κ) (ι := ι)) :=
    measurable_resetGlobal.mono (blockSigma_le _ fun q _ => measurable_pi_apply q) le_rfl
  have hpair : Measurable fun u : NoiseIndex κ ι → I => ((u .global : I), resetGlobal u) :=
    (measurable_pi_apply (NoiseIndex.global : NoiseIndex κ ι)).prodMk hRm
  have hread : (fun u => Φ (u .global) u) =
      Function.uncurry Φ ∘ fun u => (u .global, resetGlobal u) := by
    funext u
    rw [Function.comp_apply, Function.uncurry_apply_pair]
    exact hfree _ u
  have hreset : Function.uncurry Φ ∘ Prod.map id resetGlobal = Function.uncurry Φ := by
    funext x
    rw [Function.comp_apply, Prod.map_apply, id, Function.uncurry_apply_pair,
      Function.uncurry_def]
    exact (hfree x.1 x.2).symm
  rw [hread, ← Measure.map_map hΦ hpair,
    map_global_resetGlobal_noiseMeasure, ← Measure.map_id (μ := (volume : Measure I)),
    Measure.map_prod_map _ _ measurable_id hRm, Measure.map_id,
    Measure.map_map hΦ (measurable_id.prodMap hRm), hreset]
  ext s hs
  rw [Measure.bind_apply hs (MeasureTheory.measurable_map_of_measurable_uncurry hΦ).aemeasurable,
    Measure.map_apply hΦ hs, Measure.prod_apply (hΦ hs)]
  refine lintegral_congr fun t => ?_
  -- the section `Φ t` is `Function.uncurry Φ ∘ Prod.mk t`, so the two preimages agree
  have hsec : Measurable (Φ t) := hΦ.comp measurable_prodMk_left
  rw [Measure.map_apply hsec hs]
  rfl

/-! ## The joint coding -/

omit [MeasurableSpace α] in
/-- A frozen joint coding reads no global noise coordinate. -/
private theorem jointArray_frozen_resetGlobal (f : I × I × I × I → α) (t : I)
    (u : NoiseIndex Unit (Sym2 ℕ) → I) :
    (fun p => jointArray (fun q => f (t, q.2)) p u) =
      fun p => jointArray (fun q => f (t, q.2)) p (resetGlobal u) := by
  funext p
  simp [resetGlobal]

private theorem measurable_uncurry_jointArray_frozen {f : I × I × I × I → α}
    (hf : Measurable f) :
    Measurable (Function.uncurry fun (t : I) (u : NoiseIndex Unit (Sym2 ℕ) → I) (p : ℕ × ℕ) =>
      jointArray (fun q => f (t, q.2)) p u) := by
  refine Measurable.of_eval fun p => ?_
  simp only [Function.uncurry_def, jointArray_apply]
  fun_prop

/-- The laws of the frozen joint codings `(a, b, c) ↦ f (t, a, b, c)` depend measurably on the
frozen value `t`. -/
theorem measurable_map_jointArray_frozen {f : I × I × I × I → α} (hf : Measurable f) :
    Measurable fun t : I =>
      (noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray (fun q => f (t, q.2)) p u :=
  MeasureTheory.measurable_map_of_measurable_uncurry (measurable_uncurry_jointArray_frozen hf)

/-- **The law of a joint Aldous--Hoover coding is the uniform mixture of the laws of its frozen
codings.** Freezing the global argument of `f` at `t` leaves the coding
`(a, b, c) ↦ f (t, a, b, c)`, which reads no global noise; averaging the law of the array it codes
over a uniform `t` returns the law of the original coding. -/
theorem map_jointArray_eq_bind_frozen {f : I × I × I × I → α} (hf : Measurable f) :
    ((noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray f p u) =
      (volume : Measure I).bind fun t =>
        (noiseMeasure Unit (Sym2 ℕ)).map fun u p => jointArray (fun q => f (t, q.2)) p u := by
  rw [bind_map_eq_map_global (measurable_uncurry_jointArray_frozen hf)
    (jointArray_frozen_resetGlobal f)]
  simp

/-! ## The separate coding -/

omit [MeasurableSpace α] in
/-- A frozen separate coding reads no global noise coordinate. -/
private theorem separateArray_frozen_resetGlobal (f : I × I × I × I → α) (t : I)
    (u : NoiseIndex Axis (ℕ × ℕ) → I) :
    (fun p => separateArray (fun q => f (t, q.2)) p u) =
      fun p => separateArray (fun q => f (t, q.2)) p (resetGlobal u) := by
  funext p
  simp [resetGlobal]

private theorem measurable_uncurry_separateArray_frozen {f : I × I × I × I → α}
    (hf : Measurable f) :
    Measurable (Function.uncurry fun (t : I) (u : NoiseIndex Axis (ℕ × ℕ) → I) (p : ℕ × ℕ) =>
      separateArray (fun q => f (t, q.2)) p u) := by
  refine Measurable.of_eval fun p => ?_
  simp only [Function.uncurry_def, separateArray_apply]
  fun_prop

/-- The laws of the frozen separate codings `(a, b, c) ↦ f (t, a, b, c)` depend measurably on the
frozen value `t`. -/
theorem measurable_map_separateArray_frozen {f : I × I × I × I → α} (hf : Measurable f) :
    Measurable fun t : I =>
      (noiseMeasure Axis (ℕ × ℕ)).map fun u p => separateArray (fun q => f (t, q.2)) p u :=
  MeasureTheory.measurable_map_of_measurable_uncurry (measurable_uncurry_separateArray_frozen hf)

/-- **The law of a separate Aldous--Hoover coding is the uniform mixture of the laws of its frozen
codings**, the separate form of `map_jointArray_eq_bind_frozen`. -/
theorem map_separateArray_eq_bind_frozen {f : I × I × I × I → α} (hf : Measurable f) :
    ((noiseMeasure Axis (ℕ × ℕ)).map fun u p => separateArray f p u) =
      (volume : Measure I).bind fun t =>
        (noiseMeasure Axis (ℕ × ℕ)).map fun u p => separateArray (fun q => f (t, q.2)) p u := by
  rw [bind_map_eq_map_global (measurable_uncurry_separateArray_frozen hf)
    (separateArray_frozen_resetGlobal f)]
  simp

end AldousHoover

end Probability

end TauCeti

end
