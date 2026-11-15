/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AffineLine
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic
public import TauCeti.RingTheory.MvPolynomial.AffineStar
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis

/-!
# Ordered products for the affine Lie algebra

Let `L = TauCeti.LieAlgebra.AffineLine R` be the two-dimensional Lie algebra spanned by the
dilation `x` and the translation `y`, with `[x, y] = y`. Its Rees generators `X = j(x)` and
`Y = j(y)` in the PBW Rees algebra satisfy `X Y = Y (X + t)`, where `t` is the deformation
parameter, and in `U(L)` the generators satisfy `ι x ι y = ι y (ι x + 1)`.

Through ordered evaluation `y ^ a x ^ b ↦ Y ^ a X ^ b` the multiplication of the Rees algebra is
therefore the ordered product `TauCeti.affineStar` with parameter `t`, over the parameter ring
`R[t]`, and the multiplication of `U(L)` is the ordered product with parameter `1`, over `R`.
Evaluating the parameter at `1` intertwines the two comparisons.

By the Poincaré–Birkhoff–Witt theorem the ordered monomials `ι y ^ a ι x ^ b` form a basis of
`U(L)` over any commutative ring, so the comparison with `U(L)` is bijective. This makes the
ordered product associative at parameter `1`; rescaling `x` by a unit moves any unit parameter
to `1`, and every parameter is a specialization of the Laurent variable, which proves
associativity for every parameter over every commutative ring.

## Main results

* `TauCeti.LieAlgebra.AffineLine.reesGenerator_dilation_mul_reesGenerator_translation`: the
  Rees relation `X Y = Y (X + t)`.
* `TauCeti.LieAlgebra.AffineLine.orderedEval_reesGenerator_affineStar`: ordered evaluation into
  the Rees algebra carries the ordered product with parameter `t` to the Rees multiplication.
* `TauCeti.LieAlgebra.AffineLine.orderedEval_ι_affineStar`: the same for `U(L)` and parameter
  `1`.
* `TauCeti.LieAlgebra.AffineLine.evalOne_orderedEval_reesGenerator`: evaluation of the parameter
  at `1` intertwines the two ordered evaluations.
* `TauCeti.LieAlgebra.AffineLine.orderedEval_ι_bijective`: the ordered comparison with `U(L)` is
  bijective.
* `TauCeti.affineStar_assoc`: the ordered product is associative.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.3, for the
  Poincaré–Birkhoff–Witt basis.
* S. Gutt, *Deformation Quantization and Symmetries*, lectures, Würzburg (2019), Lecture 1, for
  ordered and symmetrized products.
-/

public section

open scoped Polynomial

namespace TauCeti.LieAlgebra.AffineLine

open TauCeti.UniversalEnvelopingAlgebra

variable (R : Type*) [CommRing R]

local notation "L" => AffineLine R

local notation "U" => _root_.UniversalEnvelopingAlgebra R (AffineLine R)

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

/-- **The Rees multiplication is the ordered product.** Ordered evaluation
`y ^ a x ^ b ↦ Y ^ a X ^ b` into the PBW Rees algebra carries the ordered product with parameter
`t` to the multiplication of the Rees algebra. -/
theorem orderedEval_reesGenerator_affineStar (p q : MvPolynomial (Fin 2) R[X]) :
    orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R))
        (affineStar (Polynomial.X : R[X]) p q) =
      orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R)) p *
        orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R)) q :=
  orderedEval_affineStar (reesGenerator_dilation_mul_reesGenerator_translation R) p q

/-- The enveloping-algebra relation of the affine Lie algebra: `ι x ι y = ι y (ι x + 1)`. -/
theorem ι_dilation_mul_ι_translation :
    _root_.UniversalEnvelopingAlgebra.ι R (dilation R) *
        _root_.UniversalEnvelopingAlgebra.ι R (translation R) =
      _root_.UniversalEnvelopingAlgebra.ι R (translation R) *
        (_root_.UniversalEnvelopingAlgebra.ι R (dilation R) + 1) := by
  have h := mul_sub_mul_eq_map_ι_lie (AlgHom.id R U) (dilation R) (translation R)
  rw [lie_dilation_translation, sub_eq_iff_eq_add] at h
  simpa [mul_add, add_comm] using h

/-- **The multiplication of `U(L)` is the ordered product with parameter `1`.** -/
theorem orderedEval_ι_affineStar (p q : MvPolynomial (Fin 2) R) :
    orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
        (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) (affineStar 1 p q) =
      orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
          (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) p *
        orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
          (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) q :=
  orderedEval_affineStar (by simpa using ι_dilation_mul_ι_translation R) p q

/-- **Specializing the parameter at `1`.** Evaluating the Rees parameter at `1` carries ordered
evaluation into the Rees algebra to ordered evaluation into `U(L)` of the polynomial whose
coefficients are evaluated at `1`. Together with `TauCeti.map_affineStar`, it identifies the
specialization of the Rees multiplication with the multiplication of `U(L)`. -/
theorem evalOne_orderedEval_reesGenerator (p : MvPolynomial (Fin 2) R[X]) :
    coeffSubalgebra.evalOne (pbwFiltration R L)
        (orderedEval (reesGenerator R L (dilation R)) (reesGenerator R L (translation R)) p) =
      orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
        (_root_.UniversalEnvelopingAlgebra.ι R (translation R))
        (MvPolynomial.map (Polynomial.evalRingHom (1 : R)) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [orderedEval_monomial, MvPolynomial.map_monomial, orderedEval_monomial,
        Algebra.smul_def, map_mul, map_mul, map_pow, map_pow, evalOne_reesGenerator,
        evalOne_reesGenerator, Algebra.smul_def, coeffSubalgebra.evalOne_apply,
        coeffSubalgebra.coe_algebraMap, Polynomial.eval_map, Polynomial.eval₂_at_one,
        Polynomial.coe_evalRingHom]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

section Associativity

open MvPolynomial

variable {R}

variable (R) in
/-- The basis `(y, x)` of the affine Lie algebra, in which the translation precedes the
dilation, so that its increasing PBW monomials are the ordered monomials `ι y ^ a ι x ^ b`. -/
private noncomputable def translationFirstBasis : Module.Basis (Fin 2) R L :=
  (Module.Basis.finTwoProd R).reindex (Equiv.swap 0 1)

private theorem translationFirstBasis_zero :
    translationFirstBasis R 0 = translation R := by
  ext <;> simp [translationFirstBasis]

private theorem translationFirstBasis_one : translationFirstBasis R 1 = dilation R := by
  ext <;> simp [translationFirstBasis]

private theorem ι_translation_pow_mul_ι_dilation_pow (m n : ℕ) :
    _root_.UniversalEnvelopingAlgebra.ι R (translation R) ^ m *
        _root_.UniversalEnvelopingAlgebra.ι R (dilation R) ^ n =
      (translationFirstBasis R).pbwBasis (Finsupp.single 0 m + Finsupp.single 1 n) := by
  have hword : (List.replicate m (0 : Fin 2) ++ List.replicate n 1).Pairwise (· ≤ ·) := by
    simp [List.pairwise_append, List.pairwise_replicate]
  have hmon : pbwMonomial R L (translationFirstBasis R) (List.replicate m 0 ++ List.replicate n 1) =
      _root_.UniversalEnvelopingAlgebra.ι R (translation R) ^ m *
        _root_.UniversalEnvelopingAlgebra.ι R (dilation R) ^ n := by
    simp [pbwMonomial_def, translationFirstBasis_zero, translationFirstBasis_one,
      List.prod_replicate]
  apply (translationFirstBasis R).pbwEval_bijective.injective
  refine Eq.trans ?_ (Module.Basis.pbwEval_pbwBasis (translationFirstBasis R) _).symm
  rw [← hmon]
  rw [(translationFirstBasis R).pbwEval_pbwMonomial hword]
  refine congrArg (fun s ↦ monomial s 1) ?_
  ext i
  fin_cases i <;> simp [Multiset.toFinsupp_apply, List.count_replicate]

variable (R) in
/-- **The ordered comparison for `U(L)`.** Ordered evaluation `y ^ a x ^ b ↦ ι y ^ a ι x ^ b` is
a linear bijection from polynomials over `R` onto the enveloping algebra of the affine Lie
algebra: the ordered monomials form its Poincaré–Birkhoff–Witt basis. -/
theorem orderedEval_ι_bijective :
    Function.Bijective (orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
      (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) :
        MvPolynomial (Fin 2) R → U) := by
  have h : orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
      (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) =
      ((basisMonomials (Fin 2) R).equiv (translationFirstBasis R).pbwBasis
        (Finsupp.domCongr (Equiv.swap (0 : Fin 2) 1)).toEquiv).toLinearMap := by
    refine (basisMonomials (Fin 2) R).ext fun s ↦ ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, coe_basisMonomials, orderedEval_monomial,
      one_smul, ι_translation_pow_mul_ι_dilation_pow]
    congr 1
    ext i
    fin_cases i <;> simp
  rw [h]
  exact LinearEquiv.bijective _

/-- Rescaling of the variable `x` by `u`. -/
private noncomputable def scaleX (u : R) : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![C u * X 0, X 1]

private theorem scaleX_scaleX (u v : R) (p : MvPolynomial (Fin 2) R) :
    scaleX u (scaleX v p) = scaleX (u * v) p := by
  have h : (scaleX u).comp (scaleX v) = scaleX (u * v) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp [scaleX, mul_comm, mul_left_comm]
  exact AlgHom.congr_fun h p

private theorem scaleX_one (p : MvPolynomial (Fin 2) R) : scaleX 1 p = p := by
  have h : scaleX (1 : R) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i <;> simp [scaleX]
  exact AlgHom.congr_fun h p

private theorem orderedEval_scaleX (u : R) (p : MvPolynomial (Fin 2) R) :
    orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
        (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) (scaleX u p) =
      orderedEval (u • _root_.UniversalEnvelopingAlgebra.ι R (dilation R))
        (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) p := by
  induction p using MvPolynomial.induction_on_X_pow_mul_X_pow with
  | smul a p hp => rw [map_smul, map_smul, map_smul, hp]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | X_pow a b =>
      have h : scaleX u (X 1 ^ a * X 0 ^ b) = u ^ b • (X 1 ^ a * X 0 ^ b) := by
        rw [scaleX, map_mul, map_pow, map_pow, aeval_X, aeval_X]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [mul_pow, ← map_pow, smul_eq_C_mul]
        ring
      rw [h, map_smul, orderedEval_X_pow_mul_X_pow, orderedEval_X_pow_mul_X_pow, smul_pow,
        mul_smul_comm]

private theorem scaleX_affineStar (u : R) (p q : MvPolynomial (Fin 2) R) :
    scaleX u (affineStar u p q) = affineStar 1 (scaleX u p) (scaleX u q) := by
  have hrel : (u • _root_.UniversalEnvelopingAlgebra.ι R (dilation R)) *
      _root_.UniversalEnvelopingAlgebra.ι R (translation R) =
      _root_.UniversalEnvelopingAlgebra.ι R (translation R) *
        (u • _root_.UniversalEnvelopingAlgebra.ι R (dilation R) + algebraMap R U u) := by
    rw [smul_mul_assoc, ι_dilation_mul_ι_translation, mul_add, mul_add, smul_add, mul_smul_comm,
      mul_one, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  apply (orderedEval_ι_bijective R).injective
  rw [orderedEval_scaleX, orderedEval_affineStar hrel, orderedEval_ι_affineStar,
    orderedEval_scaleX, orderedEval_scaleX]

private theorem affineStar_assoc_of_isUnit {u : R} (hu : IsUnit u)
    (p q r : MvPolynomial (Fin 2) R) :
    affineStar u (affineStar u p q) r = affineStar u p (affineStar u q r) := by
  obtain ⟨u, rfl⟩ := hu
  have hinj : Function.Injective (scaleX (u : R)) := fun p q h ↦ by
    have h' := congrArg (scaleX (↑u⁻¹ : R)) h
    rwa [scaleX_scaleX, scaleX_scaleX, Units.inv_mul, scaleX_one, scaleX_one] at h'
  apply hinj
  rw [scaleX_affineStar, scaleX_affineStar, scaleX_affineStar, scaleX_affineStar]
  apply (orderedEval_ι_bijective R).injective
  simp only [orderedEval_ι_affineStar, mul_assoc]

end Associativity

end TauCeti.LieAlgebra.AffineLine

namespace TauCeti

open MvPolynomial LieAlgebra.AffineLine

/-- **Associativity of the ordered product.** For every parameter `h`, the ordered product
`TauCeti.affineStar h` is associative. The proof transports the multiplication of the enveloping
algebra of the affine Lie algebra through its Poincaré–Birkhoff–Witt basis; a unit parameter is
rescaled to `1`, and the general parameter is a specialization of the Laurent variable. -/
theorem affineStar_assoc {S : Type*} [CommRing S] (h : S) (p q r : MvPolynomial (Fin 2) S) :
    affineStar h (affineStar h p q) r = affineStar h p (affineStar h q r) := by
  have key (p q r : MvPolynomial (Fin 2) S[X]) :
      affineStar Polynomial.X (affineStar Polynomial.X p q) r =
        affineStar Polynomial.X p (affineStar Polynomial.X q r) := by
    apply MvPolynomial.map_injective _ (Polynomial.toLaurent_injective (R := S))
    have hX : (Polynomial.toLaurent : S[X] →+* _) Polynomial.X = LaurentPolynomial.T 1 := by
      simp
    simp only [map_affineStar, hX]
    exact affineStar_assoc_of_isUnit (LaurentPolynomial.isUnit_T 1) _ _ _
  have hψ : (Polynomial.eval₂RingHom (RingHom.id S) h).comp Polynomial.C = RingHom.id S := by
    ext; simp
  have := congrArg (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id S) h))
    (key (map Polynomial.C p) (map Polynomial.C q) (map Polynomial.C r))
  simpa only [map_affineStar, map_map, hψ, map_id, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X] using this

end TauCeti
