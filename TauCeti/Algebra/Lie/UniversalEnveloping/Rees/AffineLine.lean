/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AffineLine
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic
public import TauCeti.RingTheory.MvPolynomial.AffineStar

/-!
# Ordered products for the Rees algebra of the affine Lie algebra

Let `L = TauCeti.LieAlgebra.AffineLine R` be the two-dimensional Lie algebra spanned by the
dilation `x` and the translation `y`, with `[x, y] = y`. Its Rees generators `X = j(x)` and
`Y = j(y)` in the PBW Rees algebra satisfy `X Y = Y (X + t)`, where `t` is the deformation
parameter.

Ordered evaluation `y ^ a x ^ b ↦ Y ^ a X ^ b` into the Rees algebra therefore carries the
ordered product `TauCeti.affineStar` with parameter `t`, over the parameter ring `R[t]`, to the
Rees multiplication: it is a multiplicative linear map. Evaluating the parameter at `1`
intertwines it with ordered evaluation into `U(L)`, which carries the ordered product with
parameter `1` to the multiplication of `U(L)` and is bijective
(`TauCeti.LieAlgebra.AffineLine.orderedEval_ι_affineStar`,
`TauCeti.LieAlgebra.AffineLine.orderedEval_ι_bijective`). Bijectivity is shown only for `U(L)`,
not for the Rees algebra.

## Main results

* `TauCeti.LieAlgebra.AffineLine.reesGenerator_dilation_mul_reesGenerator_translation`: the
  Rees relation `X Y = Y (X + t)`.
* `TauCeti.LieAlgebra.AffineLine.orderedEval_reesGenerator_affineStar`: ordered evaluation into
  the Rees algebra carries the ordered product with parameter `t` to the Rees multiplication.
* `TauCeti.LieAlgebra.AffineLine.evalOne_orderedEval_reesGenerator`: evaluation of the parameter
  at `1` intertwines ordered evaluation into the Rees algebra with ordered evaluation into `U(L)`.

## References

* S. Gutt, *Deformation Quantization and Symmetries*, lectures, Würzburg (2019), Lecture 1, as
  background on star products on duals of Lie algebras.
-/

public section

open scoped Polynomial

namespace TauCeti.LieAlgebra.AffineLine

open TauCeti.UniversalEnvelopingAlgebra

variable (R : Type*) [CommRing R]

local notation "L" => AffineLine R

/-- **The Rees relation of the affine Lie algebra.** The Rees generators `X = j(x)` and
`Y = j(y)` of the dilation and the translation satisfy `X Y = Y (X + t)`. -/
theorem reesGenerator_dilation_mul_reesGenerator_translation :
    reesGenerator R L (dilation R) * reesGenerator R L (translation R) =
      reesGenerator R L (translation R) *
        (reesGenerator R L (dilation R) + algebraMap R[X] (reesAlgebra R L) Polynomial.X) := by
  have h := reesGenerator_mul_sub_mul R L (dilation R) (translation R)
  rw [lie_dilation_translation, sub_eq_iff_eq_add] at h
  rw [h, mul_add, coeffSubalgebra.algebraMap_X,
    (coeffSubalgebra.commute_X (pbwFiltration R L) _ (reesGenerator R L (translation R))).eq,
    add_comm]

/-- **Ordered evaluation into the Rees algebra is multiplicative.** Ordered evaluation
`y ^ a x ^ b ↦ Y ^ a X ^ b` into the PBW Rees algebra carries the ordered product with parameter
`t` to the multiplication of the Rees algebra. -/
@[simp]
theorem orderedEval_reesGenerator_affineStar (p q : MvPolynomial (Fin 2) R[X]) :
    orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R))
        (affineStar (Polynomial.X : R[X]) p q) =
      orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R)) p *
        orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R)) q :=
  orderedEval_affineStar (reesGenerator_dilation_mul_reesGenerator_translation R) p q

/-- **Specializing the parameter at `1`.** Evaluating the Rees parameter at `1` carries ordered
evaluation into the Rees algebra to ordered evaluation into `U(L)` of the polynomial whose
coefficients are evaluated at `1`. -/
@[simp]
theorem evalOne_orderedEval_reesGenerator (p : MvPolynomial (Fin 2) R[X]) :
    coeffSubalgebra.evalOne (pbwFiltration R L)
        (orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R)) p) =
      orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
        (_root_.UniversalEnvelopingAlgebra.ι R (translation R))
        (MvPolynomial.map (Polynomial.evalRingHom (1 : R)) p) := by
  rw [map_orderedEval (Polynomial.evalRingHom 1) _ (fun s ↦ ?_), evalOne_reesGenerator,
    evalOne_reesGenerator]
  simp [coeffSubalgebra.evalOne_apply, Polynomial.eval_map]

end TauCeti.LieAlgebra.AffineLine
