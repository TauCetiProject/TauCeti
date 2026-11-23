/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AffineLine
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.MvPolynomial.AffineStar
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
import TauCeti.Algebra.MvPolynomial.Fin.Two.Ordered

/-!
# The ordered product and the enveloping algebra of the affine Lie algebra

Let `L = TauCeti.LieAlgebra.AffineLine R` be the two-dimensional Lie algebra spanned by the
dilation `x` and the translation `y`, with `[x, y] = y`. In `U(L)` the generators satisfy
`ι x ι y = ι y (ι x + 1)`, so ordered evaluation `y ^ a x ^ b ↦ ι y ^ a ι x ^ b` is multiplicative:
it carries the ordered product `TauCeti.affineStar` with parameter `1` to the multiplication of
`U(L)`.

By the Poincaré–Birkhoff–Witt theorem the ordered monomials `ι y ^ a ι x ^ b` form a basis of
`U(L)` over any commutative ring, so this comparison is bijective. This makes the ordered product
associative at parameter `1`; rescaling `x` by a unit moves any unit parameter to `1`
(`TauCeti.rescale_affineStar`). Over a commutative semiring every parameter is a specialization of
the polynomial variable `t` over `ℕ[t]`, and ordered monomials are images of ordered monomials over
`ℕ[t]`. Over `ℕ[t]` associativity follows from the case of the unit parameter `t` over
`ℤ[t, t⁻¹]`, into which `ℕ[t]` embeds.

## Main results

* `TauCeti.LieAlgebra.AffineLine.ι_dilation_mul_ι_translation`: the relation
  `ι x ι y = ι y (ι x + 1)`.
* `TauCeti.LieAlgebra.AffineLine.orderedEval_ι_affineStar`: ordered evaluation into `U(L)` is
  multiplicative, carrying the ordered product with parameter `1` to the multiplication of `U(L)`.
* `TauCeti.LieAlgebra.AffineLine.orderedEval_ι_bijective`: the ordered comparison with `U(L)` is
  bijective.
* `TauCeti.affineStar_assoc`: the ordered product is associative.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.3, for the
  Poincaré–Birkhoff–Witt basis.
* S. Gutt, *Deformation Quantization and Symmetries*, lectures, Würzburg (2019), Lecture 1, as
  background on star products on duals of Lie algebras.
-/

public section

open scoped Polynomial

namespace TauCeti.LieAlgebra.AffineLine

open TauCeti.UniversalEnvelopingAlgebra

variable (R : Type*) [CommRing R]

local notation "L" => AffineLine R

local notation "U" => _root_.UniversalEnvelopingAlgebra R (AffineLine R)

/-- The enveloping-algebra relation of the affine Lie algebra: `ι x ι y = ι y (ι x + 1)`. -/
theorem ι_dilation_mul_ι_translation :
    _root_.UniversalEnvelopingAlgebra.ι R (dilation R) *
        _root_.UniversalEnvelopingAlgebra.ι R (translation R) =
      _root_.UniversalEnvelopingAlgebra.ι R (translation R) *
        (_root_.UniversalEnvelopingAlgebra.ι R (dilation R) + 1) := by
  have h := mul_sub_mul_eq_map_ι_lie (AlgHom.id R U) (dilation R) (translation R)
  rw [lie_dilation_translation, sub_eq_iff_eq_add] at h
  simpa [mul_add, add_comm] using h

/-- **Ordered evaluation into `U(L)` is multiplicative.** It carries the ordered product with
parameter `1` to the multiplication of `U(L)`. -/
theorem orderedEval_ι_affineStar (p q : MvPolynomial (Fin 2) R) :
    orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
        (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) (affineStar 1 p q) =
      orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
          (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) p *
        orderedEval (_root_.UniversalEnvelopingAlgebra.ι R (dilation R))
          (_root_.UniversalEnvelopingAlgebra.ι R (translation R)) q :=
  orderedEval_affineStar (by simpa using ι_dilation_mul_ι_translation R) p q

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
    have hs : (Finsupp.domCongr (Equiv.swap (0 : Fin 2) 1)).toEquiv s =
        Finsupp.equivFunOnFinite.symm ![s 1, s 0] := by
      ext i
      fin_cases i <;> simp
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, coe_basisMonomials, orderedEval_monomial,
      one_smul, hs, Module.Basis.pbwBasis_eq_prod_pow_fin]
    simp [List.finRange_succ, translationFirstBasis_zero, translationFirstBasis_one]
  rw [h]
  exact LinearEquiv.bijective _

private theorem affineStar_assoc_of_isUnit {u : R} (hu : IsUnit u)
    (p q r : MvPolynomial (Fin 2) R) :
    affineStar u (affineStar u p q) r = affineStar u p (affineStar u q r) := by
  obtain ⟨u, rfl⟩ := hu
  -- Rescaling `x` by `u` moves the parameter `u` to `1`.
  have hinj : Function.Injective (rescale ![(u : R), 1]) :=
    Function.LeftInverse.injective (g := rescale ![(↑u⁻¹ : R), 1])
      (rescale_rescale_of_mul_eq_one (by simp [Fin.forall_fin_two]))
  have hu1 := rescale_affineStar (u : R) 1 1
  simp only [mul_one] at hu1
  apply hinj
  rw [hu1, hu1, hu1, hu1]
  apply (orderedEval_ι_bijective R).injective
  simp only [orderedEval_ι_affineStar, mul_assoc]

end Associativity

end TauCeti.LieAlgebra.AffineLine

namespace TauCeti

open MvPolynomial LieAlgebra.AffineLine

/-- **Associativity of the ordered product.** For every parameter `h` in a commutative semiring,
the ordered product `TauCeti.affineStar h` is associative. -/
theorem affineStar_assoc {S : Type*} [CommSemiring S] (h : S) (p q r : MvPolynomial (Fin 2) S) :
    affineStar h (affineStar h p q) r = affineStar h p (affineStar h q r) := by
  -- Ordered monomials over `S` are images of ordered monomials over `ℕ[X]`, and the ordered
  -- product over `ℕ[X]` is associative because `ℕ[X]` embeds in `ℤ[X, X⁻¹]`, where `X` is a unit.
  have key (p q r : MvPolynomial (Fin 2) ℕ[X]) :
      affineStar Polynomial.X (affineStar Polynomial.X p q) r =
        affineStar Polynomial.X p (affineStar Polynomial.X q r) := by
    let ι : ℕ[X] →+* LaurentPolynomial ℤ :=
      Polynomial.toLaurent.comp (Polynomial.mapRingHom (Nat.castRingHom ℤ))
    apply MvPolynomial.map_injective ι
      (Polynomial.toLaurent_injective.comp (Polynomial.map_injective _ Nat.cast_injective))
    have hX : ι Polynomial.X = LaurentPolynomial.T 1 := by simp [ι]
    simp only [map_affineStar, hX]
    exact affineStar_assoc_of_isUnit (LaurentPolynomial.isUnit_T 1) _ _ _
  let φ : ℕ[X] →+* S := Polynomial.eval₂RingHom (Nat.castRingHom S) h
  have hφ (a b : ℕ) : map φ (X 1 ^ a * X 0 ^ b) = (X 1 ^ a * X 0 ^ b : MvPolynomial (Fin 2) S) := by
    simp
  have hφX : φ Polynomial.X = h := by simp [φ]
  -- Both sides are trilinear, so it suffices to compare them on ordered monomials.
  have hp : (affineStar h).flip r ∘ₗ (affineStar h).flip q =
      (affineStar h).flip (affineStar h q r) := by
    refine linearMap_ext_X_one_pow_mul_X_zero_pow fun a b ↦ ?_
    have hqr : (affineStar h).comp (affineStar h (X 1 ^ a * X 0 ^ b)) =
        (affineStar h).compr₂ (affineStar h (X 1 ^ a * X 0 ^ b)) := by
      refine linearMap_ext₂_X_one_pow_mul_X_zero_pow fun c d e f ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.compr₂_apply]
      rw [← hφ a b, ← hφ c d, ← hφ e f, ← hφX, ← map_affineStar, ← map_affineStar,
        ← map_affineStar, ← map_affineStar, key]
    exact LinearMap.congr_fun₂ hqr q r
  exact LinearMap.congr_fun hp p

end TauCeti
