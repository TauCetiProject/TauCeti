/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Geometry.Manifold.Morse.Bott.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Morse–Bott examples `y²` and `y⁴`

The functions `(x, y) ↦ y²` and `(x, y) ↦ y⁴` on `M × ℝ` both have the critical line `M × {0}`,
since the only critical point of `y ↦ yⁿ` for `2 ≤ n` is `0` (`TauCeti.criticalPoints_pow`). For
`M = ℝ`, with the product charted-space structure, they are the functions `(x, y) ↦ y²` and
`(x, y) ↦ y⁴` on the plane, with the critical line `ℝ × {0}`. The general criteria of
`TauCeti.Geometry.Manifold.Morse.Bott.Prod` decide which of them is Morse–Bott.

* For `y²` the critical line is a Morse–Bott family (`TauCeti.isMorseBottFamily_sq_comp_snd`).
  The kernel of the Hessian along it is the horizontal line, by
  `TauCeti.mem_ker_criticalHessian_comp_snd_iff` applied to
  `TauCeti.isNondegenerateCriticalPoint_sq`. The index is `0` and the coindex is `1`
  (`TauCeti.manifoldMorseIndex_sq_comp_snd` and `TauCeti.manifoldMorseIndex_neg_sq_comp_snd`), so
  for every fibre metric the negative normal bundle has rank `0` and the positive normal bundle has
  rank `1` (`TauCeti.finrank_negativeNormalSpace_sq_comp_snd` and
  `TauCeti.finrank_positiveNormalSpace_sq_comp_snd`).
* For `y⁴` the critical set is the same line, but the critical Hessian vanishes along it
  (`TauCeti.criticalHessian_pow_four_comp_snd`), so its kernel is the whole tangent space, which
  is larger than the tangent space of the line. The line is not a Morse–Bott critical submanifold
  (`TauCeti.not_isNondegenerateCriticalSubmanifold_pow_four_comp_snd`), and the function is not
  Morse–Bott at all (`TauCeti.not_isMorseBottFamily_pow_four_comp_snd`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section Sq

/-- **`y²` is Morse–Bott on `M × ℝ`.** For a nonempty connected manifold `M` without boundary,
the line `M × {0}` is the only piece of a Morse–Bott family for `(x, y) ↦ y²`. -/
theorem isMorseBottFamily_sq_comp_snd [BoundarylessManifold I M] [ConnectedSpace M]
    (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, ℝ)) n (fun x : M ↦ (x, (0 : ℝ)))) :
    IsMorseBottFamily (fun _ : Unit ↦ SmoothEmbedding.ofIsSmoothEmbedding _ h)
      ((fun y : ℝ ↦ y ^ 2) ∘ Prod.snd) :=
  isMorseBottFamily_comp_snd (by fun_prop) isNondegenerateCriticalPoint_sq
    (criticalPoints_pow le_rfl).le h

variable [FiniteDimensional ℝ E]

/-- Along the critical line of `(x, y) ↦ y²` the Morse index is `0`. -/
theorem manifoldMorseIndex_sq_comp_snd (x : M) :
    manifoldMorseIndex (I.prod 𝓘(ℝ, ℝ)) ((fun y : ℝ ↦ y ^ 2) ∘ Prod.snd) (x, 0) = 0 := by
  rw [manifoldMorseIndex_comp_snd (by fun_prop)]
  exact morseIndex_real_of_pos (by simp)

/-- Along the critical line of `(x, y) ↦ y²` the Morse index of the negative `-y²` is `1`. -/
theorem manifoldMorseIndex_neg_sq_comp_snd (x : M) :
    manifoldMorseIndex (I.prod 𝓘(ℝ, ℝ)) (-((fun y : ℝ ↦ y ^ 2) ∘ Prod.snd)) (x, 0) = 1 := by
  have hneg :
      -((fun y : ℝ ↦ y ^ 2) ∘ Prod.snd) = (fun y : ℝ ↦ -y ^ 2) ∘ (Prod.snd : M × ℝ → ℝ) := by
    funext p
    simp
  rw [hneg, manifoldMorseIndex_comp_snd (by fun_prop)]
  exact morseIndex_real_of_neg (by simp)

variable [I.Boundaryless] [IsManifold I 2 M] (hn : n ≠ 0)
  (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, ℝ)) n (fun x : M ↦ (x, (0 : ℝ))))
  (g : Bundle.RiemannianMetric fun x ↦ (SmoothEmbedding.ofIsSmoothEmbedding _ h).NormalSpace x hn)

/-- **The negative normal bundle of `y²` has rank `0`.** For every fibre metric on the normal
bundle of the critical line of `(x, y) ↦ y²`, the negative normal spaces are zero. -/
theorem finrank_negativeNormalSpace_sq_comp_snd (x : M) :
    Module.finrank ℝ ((SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd
      isNondegenerateCriticalPoint_sq h).negativeNormalSpace hn g x) = 0 := by
  rw [(SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd isNondegenerateCriticalPoint_sq
      h).finrank_negativeNormalSpace hn g x,
    SmoothEmbedding.ofIsSmoothEmbedding_apply, manifoldMorseIndex_sq_comp_snd]

/-- **The positive normal bundle of `y²` has rank `1`.** For every fibre metric on the normal
bundle of the critical line of `(x, y) ↦ y²`, the positive normal spaces are lines. -/
theorem finrank_positiveNormalSpace_sq_comp_snd (x : M) :
    Module.finrank ℝ ((SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd
      isNondegenerateCriticalPoint_sq h).positiveNormalSpace hn g x) = 1 := by
  rw [(SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd isNondegenerateCriticalPoint_sq
      h).finrank_positiveNormalSpace hn g x,
    SmoothEmbedding.ofIsSmoothEmbedding_apply, manifoldMorseIndex_neg_sq_comp_snd]

end Sq

section PowFour

/-- **The Hessian of `y⁴` vanishes along its critical line.** The critical Hessian of
`(x, y) ↦ y⁴` at `(x, 0)` is zero, so its kernel is the whole tangent space. -/
theorem criticalHessian_pow_four_comp_snd (x : M) :
    criticalHessian (I.prod 𝓘(ℝ, ℝ)) ((fun y : ℝ ↦ y ^ 4) ∘ Prod.snd) (x, 0) = 0 := by
  ext v w
  rw [criticalHessian_comp_snd_apply (by fun_prop), fderiv_fderiv_apply_eq_smul_iteratedDeriv]
  simp

/-- **The critical line of `y⁴` is not Morse–Bott.** For nonempty `M`, the line `M × {0}`, the
critical set of `(x, y) ↦ y⁴`, is not a Morse–Bott critical submanifold. -/
theorem not_isNondegenerateCriticalSubmanifold_pow_four_comp_snd [Nonempty M] (hn : n ≠ 0)
    (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, ℝ)) n (fun x : M ↦ (x, (0 : ℝ)))) :
    ¬(SmoothEmbedding.ofIsSmoothEmbedding _ h).IsNondegenerateCriticalSubmanifold
      ((fun y : ℝ ↦ y ^ 4) ∘ Prod.snd) := by
  rw [SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd_iff hn]
  exact not_isNondegenerateCriticalPoint_pow_four

/-- **`y⁴` is not Morse–Bott on `M × ℝ`.** For nonempty `M`, no family of embeddings exhibits
`(x, y) ↦ y⁴` as a Morse–Bott function. -/
theorem not_isMorseBottFamily_pow_four_comp_snd [Nonempty M]
    {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
    {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
    {S : ι → Type*} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
    (i : ∀ a, SmoothEmbedding (J a) (I.prod 𝓘(ℝ, ℝ)) n (S a) (M × ℝ)) (hn : n ≠ 0) :
    ¬IsMorseBottFamily i ((fun y : ℝ ↦ y ^ 4) ∘ Prod.snd) :=
  not_isMorseBottFamily_comp_snd i hn (criticalPoints_pow (by norm_num))
    not_isNondegenerateCriticalPoint_pow_four

end PowFour

end TauCeti
