/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model
public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial.GaloisAction
import TauCeti.Algebra.Polynomial.Belyi
import TauCeti.FieldTheory.IsAlgClosed.Automorphism

/-!
# Polynomial Belyi pairs are defined over the field of their coefficients

A polynomial `q' ∈ k[X]` of positive degree whose critical values lie in `{0, 1}` defines the
algebraic Belyi pair `TauCeti.AlgebraicBelyiPair.ofPolynomial q'`: the rational function field
`k(x)` over `k(t)`, with `t = q'(x)`. If the coefficients of `q'` lie in a subfield `K`, that is
`q'` is the image of some `q ∈ K[X]` with the same property, then the pair `ofPolynomial q` over
`K` is a model of `ofPolynomial q'` (`TauCeti.AlgebraicBelyiPair.Model.ofPolynomial`): applying
`K → k` to the coefficients embeds `K(x)` into `k(x)`, fixing `x` and hence `t = q(x)`. So the
class of `ofPolynomial q'` is defined over `K`.

The two basic examples have rational coefficients, so they are defined over `ℚ` over every field
of characteristic zero: the power map `t = x ^ n`, totally ramified over `0` and `∞` and
unramified over `1`, and the Chebyshev map `t = 4 x (1 - x)`, of degree `2`, unramified over `0`
and ramified over `1` and `∞`. These are the algebraic counterparts of the analytic Belyi pairs
`z ↦ z ^ n` and `z ↦ 4 z (1 - z)` on the Riemann sphere.

A polynomial pair with coefficients in `K` is also fixed by every automorphism of `k` fixing `K`
(`TauCeti.AlgebraicBelyiPair.IsoClass.smul_mk_ofPolynomial_eq_self`). The general statement for a
class with a model over `K` (`TauCeti.AlgebraicBelyiPair.IsoClass.IsDefinedOver.smul_eq`) needs
`k / K` algebraic; for polynomial pairs it holds over any `k`, such as `ℂ`. For rational
coefficients the stabilizer of the class is therefore the whole of `Gal(k/ℚ)`: the Galois orbit
of the class is a single point, and over an algebraically closed field, such as `ℂ` or
`AlgebraicClosure ℚ`, its field of moduli is `ℚ`.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.Model.ofPolynomial`: the model over `K` of a polynomial Belyi pair
  whose polynomial has coefficients in `K`.

## Main results

* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_mk_ofPolynomial`: the class of a polynomial
  Belyi pair is defined over every field containing the coefficients of its polynomial.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_mk_ofPolynomial_X_pow` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_mk_ofPolynomial_C_four_mul_X_mul_one_sub_X`:
  the power map `x ^ n` and the Chebyshev map `4 x (1 - x)` are defined over `ℚ`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.smul_mk_ofPolynomial_eq_self`: automorphisms of `k` fixing
  the coefficients of the polynomial fix the class.
* `TauCeti.AlgebraicBelyiPair.IsoClass.stabilizer_mk_ofPolynomial_eq_top`,
  `TauCeti.AlgebraicBelyiPair.IsoClass.trueOrbitSize_mk_ofPolynomial` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.fieldOfModuli_mk_ofPolynomial`: for rational coefficients
  the class is fixed by `Gal(k/ℚ)`, its true orbit size is `1`, and over an algebraically closed
  field its field of moduli is `ℚ`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Chapter 3, for fields of
  definition and fields of moduli of Belyi pairs.
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §2.2, for Shabat polynomials and their fields of
  definition.
-/

public section

open Polynomial

universe u v

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k]

/-! ### The model over the field of coefficients -/

section Model

variable {K : Type v} [Field K] [CharZero K] [Algebra K k]
  {q : K[X]} (hq : 0 < q.natDegree)
  (hcrit : ∀ (L : Type v) [Field L] [Algebra K L], q.criticalValues L ⊆ {0, 1})
  {q' : k[X]} (hq' : 0 < q'.natDegree)
  (hcrit' : ∀ (L : Type u) [Field L] [Algebra k L], q'.criticalValues L ⊆ {0, 1})
  (h : q.map (algebraMap K k) = q')

/-- The **coefficient map** `K(x) → k(x)` between the function fields of the polynomial Belyi
pairs `ofPolynomial q` over `K` and `ofPolynomial q'` over `k`: it applies `K → k` to the
coefficients of a rational function in the coordinate `x`, and sends `x` to `x`. It carries `t` to
`t` when `q'` is the image of `q` (`TauCeti.AlgebraicBelyiPair.ofPolynomialMap_algebraMap_X`). -/
noncomputable def ofPolynomialMap : ofPolynomial q hq hcrit →+* ofPolynomial q' hq' hcrit' :=
  ((ofPolynomialEquiv q' hq' hcrit').symm : RatFunc k →+* _).comp <|
    (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap K k))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (by simpa using Polynomial.map_injective _ (algebraMap K k).injective))).comp
      (ofPolynomialEquiv q hq hcrit : _ →+* RatFunc K)

/-- The coefficient map sends a polynomial `p(x)` in the coordinate to `p'(x)`, where `p'` is the
image of `p` in `k[X]`. -/
@[simp]
theorem ofPolynomialMap_aeval (p : K[X]) :
    ofPolynomialMap hq hcrit hq' hcrit' (aeval (ofPolynomialGen q hq hcrit) p) =
      aeval (ofPolynomialGen q' hq' hcrit') (p.map (algebraMap K k)) := by
  simp only [ofPolynomialMap, RingHom.comp_apply, RingHom.coe_coe]
  rw [← aeval_algHom_apply, ofPolynomialEquiv_ofPolynomialGen,
    RatFunc.aeval_X_left_eq_algebraMap, RatFunc.mapRingHom_algebraMap, coe_mapRingHom,
    ← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algHom_apply, ofPolynomialEquiv_symm_X]

/-- The coefficient map fixes the coordinate `x`. -/
@[simp]
theorem ofPolynomialMap_ofPolynomialGen :
    ofPolynomialMap hq hcrit hq' hcrit' (ofPolynomialGen q hq hcrit) =
      ofPolynomialGen q' hq' hcrit' := by
  simpa using ofPolynomialMap_aeval hq hcrit hq' hcrit' X

/-- The coefficient map applies `K → k` to the constants. -/
@[simp]
theorem ofPolynomialMap_algebraMap (c : K) :
    ofPolynomialMap hq hcrit hq' hcrit' (algebraMap K _ c) = algebraMap k _ (algebraMap K k c) := by
  simpa using ofPolynomialMap_aeval hq hcrit hq' hcrit' (C c)

include h in
/-- When `q'` is the image of `q`, the coefficient map carries `t = q(x)` to `t = q'(x)`. -/
theorem ofPolynomialMap_algebraMap_X :
    ofPolynomialMap hq hcrit hq' hcrit' (algebraMap (RatFunc K) _ RatFunc.X) =
      algebraMap (RatFunc k) _ RatFunc.X := by
  rw [algebraMap_ofPolynomial_X, ofPolynomialMap_aeval, h, algebraMap_ofPolynomial_X]

/-- **A polynomial Belyi pair has a model over the field of its coefficients.** If `q' ∈ k[X]` is
the image of `q ∈ K[X]`, then the polynomial pair `ofPolynomial q` over `K`, the rational function
field `K(x)` with `t = q(x)`, is a model over `K` of the polynomial pair `ofPolynomial q'` over
`k`, through the coefficient map `K(x) → k(x)`. -/
@[expose, simps pair embedding]
noncomputable def Model.ofPolynomial : Model K (ofPolynomial q' hq' hcrit') :=
  have hq : 0 < q.natDegree := by rwa [← h, natDegree_map] at hq'
  { pair := AlgebraicBelyiPair.ofPolynomial q hq hcrit
    embedding := ofPolynomialMap hq hcrit hq' hcrit'
    embedding_algebraMap := ofPolynomialMap_algebraMap hq hcrit hq' hcrit'
    embedding_algebraMap_X := ofPolynomialMap_algebraMap_X hq hcrit hq' hcrit' h
    adjoin_range_embedding := by
      refine eq_top_iff.mpr ((adjoin_ofPolynomialGen q' hq' hcrit').symm.le.trans ?_)
      exact IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin k _
        ⟨_, ofPolynomialMap_ofPolynomialGen hq hcrit hq' hcrit'⟩) }

namespace IsoClass

include hcrit h in
/-- **A polynomial Belyi pair is defined over the field of its coefficients**: if `q' ∈ k[X]` is
the image of `q ∈ K[X]`, the class of `ofPolynomial q'` is defined over `K`. -/
theorem isDefinedOver_mk_ofPolynomial : (mk (ofPolynomial q' hq' hcrit')).IsDefinedOver K :=
  isDefinedOver_mk_iff.mpr ⟨Model.ofPolynomial hcrit hq' hcrit' h⟩

end IsoClass

end Model

/-! ### The power map and the Chebyshev map are defined over `ℚ` -/

namespace IsoClass

/-- **The power map is defined over `ℚ`**: the class of the polynomial Belyi pair `t = x ^ n` is
defined over `ℚ`. -/
theorem isDefinedOver_mk_ofPolynomial_X_pow {n : ℕ} (hq : 0 < (X ^ n : k[X]).natDegree)
    (hcrit : ∀ (L : Type u) [Field L] [Algebra k L], (X ^ n : k[X]).criticalValues L ⊆ {0, 1}) :
    (mk (ofPolynomial (X ^ n) hq hcrit)).IsDefinedOver ℚ := by
  have hn : n ≠ 0 := by simpa using hq.ne'
  refine isDefinedOver_mk_ofPolynomial (q := X ^ n) (fun L _ _ ↦ ?_) hq hcrit (by simp)
  rw [← belyiPolynomial_zero_right hn]
  exact criticalValues_belyiPolynomial_subset L n 0

/-- **The Chebyshev map is defined over `ℚ`**: the class of the polynomial Belyi pair
`t = 4 x (1 - x)` is defined over `ℚ`. -/
theorem isDefinedOver_mk_ofPolynomial_C_four_mul_X_mul_one_sub_X
    (hq : 0 < (C 4 * X * (1 - X) : k[X]).natDegree)
    (hcrit : ∀ (L : Type u) [Field L] [Algebra k L],
      (C 4 * X * (1 - X) : k[X]).criticalValues L ⊆ {0, 1}) :
    (mk (ofPolynomial (C 4 * X * (1 - X)) hq hcrit)).IsDefinedOver ℚ := by
  refine isDefinedOver_mk_ofPolynomial (q := C 4 * X * (1 - X)) (fun L _ _ ↦ ?_) hq hcrit
    (by simp)
  rw [← belyiPolynomial_one_one]
  exact criticalValues_belyiPolynomial_subset L 1 1

end IsoClass

/-! ### The Galois action on polynomial pairs with coefficients in a subfield -/

namespace IsoClass

variable {q' : k[X]} (hq' : 0 < q'.natDegree)
  (hcrit' : ∀ (L : Type u) [Field L] [Algebra k L], q'.criticalValues L ⊆ {0, 1})

/-- An automorphism of `k` fixing a subfield `K` that contains the coefficients of `q'` fixes the
class of the polynomial Belyi pair `ofPolynomial q'`. Unlike
`TauCeti.AlgebraicBelyiPair.IsoClass.IsDefinedOver.smul_eq`, this needs no algebraicity of `k`
over `K`. -/
theorem smul_mk_ofPolynomial_eq_self {K : Type*} [CommSemiring K] [Algebra K k]
    (hK : q' ∈ lifts (algebraMap K k)) {g : k ≃ₐ[ℚ] k}
    (hg : ∀ c : K, g (algebraMap K k c) = algebraMap K k c) :
    g • mk (ofPolynomial q' hq' hcrit') = mk (ofPolynomial q' hq' hcrit') := by
  obtain ⟨q, rfl⟩ := (mem_lifts _).mp hK
  refine (smul_mk_ofPolynomial_eq_iff hq' hcrit' g).mpr ⟨1, 0, one_ne_zero, ?_⟩
  have hgK : (MulSemiringAction.toRingHom _ k g).comp (algebraMap K k) = algebraMap K k :=
    RingHom.ext fun c ↦ by simpa using hg c
  rw [Polynomial.map_map, hgK]
  simp

/-- **A polynomial Belyi pair with rational coefficients is fixed by `Gal(k/ℚ)`**: the stabilizer
of its class is the whole automorphism group of `k`. -/
theorem stabilizer_mk_ofPolynomial_eq_top (hℚ : q' ∈ lifts (algebraMap ℚ k)) :
    MulAction.stabilizer (k ≃ₐ[ℚ] k) (mk (ofPolynomial q' hq' hcrit')) = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ smul_mk_ofPolynomial_eq_self hq' hcrit' hℚ g.commutes

/-- The Galois orbit of the class of a polynomial Belyi pair with rational coefficients is a single
point: its true orbit size is `1`. -/
theorem trueOrbitSize_mk_ofPolynomial (hℚ : q' ∈ lifts (algebraMap ℚ k)) :
    (mk (ofPolynomial q' hq' hcrit')).trueOrbitSize = 1 := by
  rw [trueOrbitSize_eq_index, stabilizer_mk_ofPolynomial_eq_top hq' hcrit' hℚ, Subgroup.index_top]

/-- Over an algebraically closed field, such as `ℂ` or `AlgebraicClosure ℚ`, the field of moduli
of the class of a polynomial Belyi pair with rational coefficients is `ℚ`. -/
theorem fieldOfModuli_mk_ofPolynomial [IsAlgClosed k] (hℚ : q' ∈ lifts (algebraMap ℚ k)) :
    (mk (ofPolynomial q' hq' hcrit')).fieldOfModuli = ⊥ := by
  rw [fieldOfModuli_def, stabilizer_mk_ofPolynomial_eq_top hq' hcrit' hℚ,
    IsAlgClosed.fixedField_top_eq_bot]

end IsoClass

end AlgebraicBelyiPair

end TauCeti
