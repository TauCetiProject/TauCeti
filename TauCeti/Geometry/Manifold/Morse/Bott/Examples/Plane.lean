/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.Morse.OneDimensional
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.Morse.Prod

/-!
# A Morse–Bott and a non-Morse–Bott function on the plane

The functions `(x, y) ↦ y²` and `(x, y) ↦ y⁴` on the plane, read as the product manifold `ℝ × ℝ`,
have the same critical set, the line `ℝ × {0}`. They show that the Morse–Bott condition is a
condition on the Hessian along the critical set, not on the critical set alone.

* For `y²` the line, embedded by `x ↦ (x, 0)`, is a Morse–Bott critical submanifold and exhibits
  the function as Morse–Bott (`TauCeti.isMorseBottFamily_snd_sq`). Along the line the kernel of
  the critical Hessian is the tangent line, the vectors with vanishing second component
  (`TauCeti.criticalHessian_snd_sq_apply_eq_zero_iff`),
  and for every fibre metric the negative normal space is zero and the positive normal space is a
  line (`TauCeti.finrank_negativeNormalSpace_snd_sq` and
  `TauCeti.finrank_positiveNormalSpace_snd_sq`): the line consists of minima.
* For `y⁴` the critical Hessian vanishes along the line, so its kernel is the whole plane
  (`TauCeti.criticalHessian_snd_pow_four`), and no family of smooth embeddings exhibits the
  function as Morse–Bott (`TauCeti.not_isMorseBottFamily_snd_pow_four`).

Both are instances of the statements about functions `(x, v) ↦ q v` on a product `M × V`: the
slice `M × {0}` is Morse–Bott exactly when `q` has a nondegenerate critical point at `0`
(`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd_iff`), it then exhibits the
function as Morse–Bott when `0` is the only critical point of `q`
(`TauCeti.isMorseBottFamily_comp_snd`), and an isolated degenerate critical point of `q` rules out
every Morse–Bott family (`TauCeti.not_isMorseBottFamily_comp_snd`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

/-- The functions of the plane studied here are functions of the second coordinate. -/
private theorem snd_pow_eq_comp (m : ℕ) :
    (fun p : ℝ × ℝ ↦ p.2 ^ m) = (fun y : ℝ ↦ y ^ m) ∘ Prod.snd :=
  rfl

/-- The coordinate expression of a function of the real line in its identity chart at `0` is
the function itself, so it is `C²` when the function is. -/
private theorem contDiffAt_comp_extChartAt_symm {q : ℝ → ℝ} (hq : ContDiffAt ℝ 2 q 0) :
    ContDiffAt ℝ 2 (q ∘ (extChartAt 𝓘(ℝ) (0 : ℝ)).symm) (extChartAt 𝓘(ℝ) (0 : ℝ) 0) := by
  simpa using hq

/-! ### The Morse–Bott function `y²` -/

/-- **`y²` is Morse–Bott on the plane.** The critical set of `(x, y) ↦ y²` is the line `ℝ × {0}`,
and the embedding `x ↦ (x, 0)` of this line alone exhibits the function as a Morse–Bott
function. -/
theorem isMorseBottFamily_snd_sq :
    IsMorseBottFamily (fun _ : Unit ↦ SmoothEmbedding.ofIsSmoothEmbedding _
      (isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (n := ∞)
        (M := ℝ) (c := (0 : ℝ)) (by simp))) (fun p : ℝ × ℝ ↦ p.2 ^ 2) :=
  isMorseBottFamily_comp_snd (by simp) (by fun_prop) (criticalPoints_pow le_rfl)
    isNondegenerateCriticalPoint_sq

/-- **The Hessian kernel of `y²` along its critical line is the tangent line.** At every point
`(x, 0)`, a tangent vector `v` lies in the kernel of the critical Hessian of `(x, y) ↦ y²` exactly
when its second component vanishes, that is, when `v` is a multiple of `(1, 0)`. -/
theorem criticalHessian_snd_sq_apply_eq_zero_iff (x : ℝ)
    (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) ((x, 0) : ℝ × ℝ)) :
    criticalHessian (𝓘(ℝ).prod 𝓘(ℝ)) (fun p : ℝ × ℝ ↦ p.2 ^ 2) (x, 0) v = 0 ↔ v.2 = 0 := by
  rw [snd_pow_eq_comp, criticalHessian_comp_snd_apply_eq_zero_iff (by fun_prop)]
  exact isNondegenerateCriticalPoint_sq.isInvertible.injective.eq_iff' (map_zero _)

section NormalSpaces

variable (g : Bundle.RiemannianMetric fun x : ℝ ↦ (SmoothEmbedding.ofIsSmoothEmbedding _
  (isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (n := ∞)
    (M := ℝ) (c := (0 : ℝ)) (by simp))).NormalSpace x (by simp))

/-- **`y²` has negative normal rank `0`.** Along the critical line of `(x, y) ↦ y²`, the negative
normal space is zero for every fibre metric: the line consists of minima. -/
theorem finrank_negativeNormalSpace_snd_sq (x : ℝ) :
    Module.finrank ℝ ((isMorseBottFamily_snd_sq.isNondegenerateCriticalSubmanifold ()
      ).toIsCriticalSubmanifold.negativeNormalSpace (by simp) g x) = 0 := by
  rw [(isMorseBottFamily_snd_sq.isNondegenerateCriticalSubmanifold ()).finrank_negativeNormalSpace,
    SmoothEmbedding.ofIsSmoothEmbedding_apply, snd_pow_eq_comp,
    manifoldMorseIndex_comp_snd (contDiffAt_comp_extChartAt_symm (by fun_prop)),
    manifoldMorseIndex_modelSpace]
  exact morseIndex_real_of_pos (by simp)

/-- **`y²` has positive normal rank `1`.** Along the critical line of `(x, y) ↦ y²`, the positive
normal space is a line for every fibre metric. -/
theorem finrank_positiveNormalSpace_snd_sq (x : ℝ) :
    Module.finrank ℝ ((isMorseBottFamily_snd_sq.isNondegenerateCriticalSubmanifold ()
      ).toIsCriticalSubmanifold.positiveNormalSpace (by simp) g x) = 1 := by
  rw [(isMorseBottFamily_snd_sq.isNondegenerateCriticalSubmanifold ()).finrank_positiveNormalSpace,
    SmoothEmbedding.ofIsSmoothEmbedding_apply, snd_pow_eq_comp, ← Pi.neg_comp,
    manifoldMorseIndex_comp_snd (contDiffAt_comp_extChartAt_symm (q := -fun y : ℝ ↦ y ^ 2)
      (contDiff_id.pow 2).neg.contDiffAt),
    manifoldMorseIndex_modelSpace]
  exact morseIndex_real_of_neg (by simp)

end NormalSpaces

/-! ### The non-Morse–Bott function `y⁴` -/

/-- **The Hessian of `y⁴` vanishes along its critical line.** At every point `(x, 0)` the critical
Hessian of `(x, y) ↦ y⁴` is zero, so its kernel is the whole plane. -/
theorem criticalHessian_snd_pow_four (x : ℝ) :
    criticalHessian (𝓘(ℝ).prod 𝓘(ℝ)) (fun p : ℝ × ℝ ↦ p.2 ^ 4) (x, 0) = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun u ↦ ?_
  rw [snd_pow_eq_comp, criticalHessian_comp_snd_apply (I := 𝓘(ℝ)) (by fun_prop) x,
    fderiv_fderiv_apply_eq_smul_iteratedDeriv, iteratedDeriv_pow]
  simp

/-- **`y⁴` is not Morse–Bott on the plane.** No family of smooth embeddings exhibits
`(x, y) ↦ y⁴` as a Morse–Bott function: along its critical line `ℝ × {0}` the kernel of the
critical Hessian is the whole plane, larger than the tangent space of any piece through the
line. -/
theorem not_isMorseBottFamily_snd_pow_four {ι : Type*} {E' : ι → Type*}
    [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)] {H' : ι → Type*}
    [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)} {S : ι → Type*}
    [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)] {n : ℕ∞ω}
    (i : ∀ a, SmoothEmbedding (J a) (𝓘(ℝ).prod 𝓘(ℝ)) n (S a) (ℝ × ℝ)) :
    ¬IsMorseBottFamily i (fun p : ℝ × ℝ ↦ p.2 ^ 4) := by
  have hcrit := criticalPoints_pow (m := 4) (by norm_num)
  refine not_isMorseBottFamily_comp_snd (M := ℝ) (q := fun y : ℝ ↦ y ^ 4) (y := 0)
    (by simp [hcrit])
    (Filter.Eventually.of_forall fun z hz ↦ by rwa [hcrit] at hz) (fun h ↦ ?_) i
  rw [isNondegenerateCriticalPoint_real_iff (by fun_prop)] at h
  exact h.2 (by simp)

end TauCeti
