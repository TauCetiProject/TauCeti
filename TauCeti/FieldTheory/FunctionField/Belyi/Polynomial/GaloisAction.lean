/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction
public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial.Bundled

/-!
# The Galois action on polynomial Belyi pairs

A polynomial `q ∈ k[X]` of positive degree whose critical values lie in `{0, 1}` defines an
algebraic Belyi pair, the rational function field `k(x)` over `k(t)` with `t = q(x)`, bundled as
`TauCeti.AlgebraicBelyiPair.ofPolynomial q`. This file computes the action of field automorphisms
on the isomorphism classes of such pairs.

For a field isomorphism `σ : k ≃+* k'`, conjugating a pair along `σ` keeps the function field
and the function `t`, and lets `k'` act through `σ⁻¹`. So if `t = q(x)` on a pair `B`, then on
its conjugate `t = q^σ(x)`, where `q^σ = q.map σ` applies `σ` to the coefficients, and `x` still
generates the function field (`TauCeti.AlgebraicBelyiPair.algebraMap_conj_X_eq_aeval_map` and
`TauCeti.AlgebraicBelyiPair.adjoin_conjRingEquiv_eq_top`). For the bundled pairs this reads

```text
σ · [ofPolynomial q] = [ofPolynomial q^σ] .
```

Isomorphisms of polynomial pairs are affine changes of variable
(`TauCeti.nonempty_algEquiv_iff_exists_comp_eq`). Combining the two, an automorphism `g` of `k`
sends the class of a pair presented by `q` to the class of a pair presented by `q'` exactly when
`q'(a X + b) = q^g` for some `a ≠ 0` and `b`; in particular `g` fixes the class of
`ofPolynomial q` exactly when `q(a X + b) = q^g`. This turns the question whether a Galois
automorphism moves the class of a polynomial Belyi pair into a question about polynomials. It is
the form in which Lenstra's proof that the absolute Galois group of `ℚ` acts faithfully on dessins
compares a polynomial Belyi map with its conjugates.

## Main results

* `TauCeti.AlgebraicBelyiPair.algebraMap_conj_X_eq_aeval_map`: if `t = q(x)` on a pair, then
  `t = q^σ(x)` on its conjugate along `σ`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.conj_mk_eq_mk_iff_of_aeval`: the conjugate of the class of
  a pair presented by `q` is the class of a pair presented by `q'` exactly when `q'` is an affine
  reparametrization of `q^σ`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.conj_mk_ofPolynomial` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.smul_mk_ofPolynomial`: `σ · [ofPolynomial q]` is
  `[ofPolynomial q^σ]`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.smul_mk_ofPolynomial_eq_iff`: `g` fixes the class of
  `ofPolynomial q` exactly when `q(a X + b) = q^g` for some `a ≠ 0` and `b`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, proof of Theorem 4.49 (the
  argument attributed there to Lenstra).
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §2.2, for Shabat polynomials and their Galois
  conjugates.
-/

public section

open Polynomial

open scoped IntermediateField

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k k' : Type u} [Field k] [CharZero k] [Field k'] [CharZero k']

/-! ### Conjugating a polynomial presentation -/

section Conj

variable (σ : k ≃+* k') {B : AlgebraicBelyiPair k} {x : B} {q : k[X]}

/-- **The conjugate of a polynomial presentation**: if the function `t` is `q(x)` on `B`, then on
the conjugate of `B` along `σ` it is `q^σ(x)`, where `q^σ = q.map σ` applies `σ` to the
coefficients of `q`. -/
theorem algebraMap_conj_X_eq_aeval_map (hq : algebraMap (RatFunc k) B RatFunc.X = aeval x q) :
    algebraMap (RatFunc k') (B.conj σ) RatFunc.X =
      aeval (conjRingEquiv σ B x) (q.map (σ : k →+* k')) := by
  rw [← RatFunc.mapRingEquiv_X σ, ← conjRingEquiv_algebraMap_ratFunc, hq]
  exact map_aeval_eq_aeval_map (φ := (σ : k →+* k')) (ψ := (conjRingEquiv σ B : B →+* B.conj σ))
    (by ext c; simp) q x

namespace IsoClass

/-- **Conjugate classes of polynomial pairs**: let `t` be `q(x)` on `B = k(x)` and `q'(y)` on
`B' = k'(y)`. The conjugate along `σ` of the class of `B` is the class of `B'` exactly when
`q'(a X + b) = q^σ` for some `a ≠ 0` and `b` in `k'`. -/
theorem conj_mk_eq_mk_iff_of_aeval (hx : k⟮x⟯ = ⊤)
    (hq : algebraMap (RatFunc k) B RatFunc.X = aeval x q) {B' : AlgebraicBelyiPair k'} {y : B'}
    {q' : k'[X]} (hy : k'⟮y⟯ = ⊤) (hq' : algebraMap (RatFunc k') B' RatFunc.X = aeval y q') :
    (mk B).conj σ = mk B' ↔ ∃ a b : k', a ≠ 0 ∧ q'.comp (C a * X + C b) = q.map (σ : k →+* k') := by
  rw [conj_mk, mk_eq_mk_iff, ← nonempty_algEquiv_iff_exists_comp_eq hy
    (adjoin_conjRingEquiv_eq_top σ hx) hq' (algebraMap_conj_X_eq_aeval_map σ hq)]
  exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩

variable {G : Type*} [Group G] [MulSemiringAction G k]

/-- **The Galois action on classes of polynomial pairs**: let `t` be `q(x)` on `B = k(x)` and
`q'(y)` on `B' = k(y)`. An element `g` of a group acting on `k` by ring automorphisms sends the
class of `B` to the class of `B'` exactly when `q'(a X + b) = q^g` for some `a ≠ 0` and `b`. -/
theorem smul_mk_eq_mk_iff_of_aeval (g : G) (hx : k⟮x⟯ = ⊤)
    (hq : algebraMap (RatFunc k) B RatFunc.X = aeval x q) {B' : AlgebraicBelyiPair k} {y : B'}
    {q' : k[X]} (hy : k⟮y⟯ = ⊤) (hq' : algebraMap (RatFunc k) B' RatFunc.X = aeval y q') :
    g • mk B = mk B' ↔
      ∃ a b : k, a ≠ 0 ∧ q'.comp (C a * X + C b) = q.map (MulSemiringAction.toRingHom G k g) := by
  have hg : ((MulSemiringAction.toRingEquiv G k g : k ≃+* k) : k →+* k) =
      MulSemiringAction.toRingHom G k g := RingHom.ext fun _ ↦ by simp
  rw [smul_def, conj_mk_eq_mk_iff_of_aeval _ hx hq hy hq', hg]

end IsoClass

end Conj

/-! ### The Galois action on polynomial pairs -/

section OfPolynomial

variable {q : k[X]} (hq : 0 < q.natDegree)
  (hcrit : ∀ (L : Type u) [Field L] [Algebra k L], q.criticalValues L ⊆ {0, 1})

namespace IsoClass

/-- **Conjugating a polynomial pair conjugates its polynomial**: the conjugate along `σ` of the
class of `ofPolynomial q` is the class of `ofPolynomial q^σ`, where `q^σ = q.map σ`. -/
theorem conj_mk_ofPolynomial (σ : k ≃+* k') (hqσ : 0 < (q.map (σ : k →+* k')).natDegree)
    (hcritσ : ∀ (L : Type u) [Field L] [Algebra k' L],
      (q.map (σ : k →+* k')).criticalValues L ⊆ {0, 1}) :
    (mk (ofPolynomial q hq hcrit)).conj σ = mk (ofPolynomial (q.map (σ : k →+* k')) hqσ hcritσ) :=
  (conj_mk_eq_mk_iff_of_aeval σ (adjoin_ofPolynomialGen q hq hcrit)
    (algebraMap_ofPolynomial_X q hq hcrit)
    (adjoin_ofPolynomialGen (q.map (σ : k →+* k')) hqσ hcritσ)
    (algebraMap_ofPolynomial_X (q.map (σ : k →+* k')) hqσ hcritσ)).mpr
    ⟨1, 0, one_ne_zero, by simp⟩

variable {G : Type*} [Group G] [MulSemiringAction G k]

/-- **The Galois action on polynomial pairs**: an element `g` of a group acting on `k` by ring
automorphisms sends the class of `ofPolynomial q` to the class of `ofPolynomial q^g`, where `q^g`
applies `g` to the coefficients of `q`. -/
theorem smul_mk_ofPolynomial (g : G)
    (hqg : 0 < (q.map (MulSemiringAction.toRingHom G k g)).natDegree)
    (hcritg : ∀ (L : Type u) [Field L] [Algebra k L],
      (q.map (MulSemiringAction.toRingHom G k g)).criticalValues L ⊆ {0, 1}) :
    g • mk (ofPolynomial q hq hcrit) =
      mk (ofPolynomial (q.map (MulSemiringAction.toRingHom G k g)) hqg hcritg) :=
  (smul_mk_eq_mk_iff_of_aeval g (adjoin_ofPolynomialGen q hq hcrit)
    (algebraMap_ofPolynomial_X q hq hcrit) (adjoin_ofPolynomialGen _ hqg hcritg)
    (algebraMap_ofPolynomial_X _ hqg hcritg)).mpr ⟨1, 0, one_ne_zero, by simp⟩

/-- **The stabilizer of a polynomial pair**: an element `g` of a group acting on `k` by ring
automorphisms fixes the class of `ofPolynomial q` exactly when `q(a X + b) = q^g` for some
`a ≠ 0` and `b`, where `q^g` applies `g` to the coefficients of `q`. -/
theorem smul_mk_ofPolynomial_eq_iff (g : G) :
    g • mk (ofPolynomial q hq hcrit) = mk (ofPolynomial q hq hcrit) ↔
      ∃ a b : k, a ≠ 0 ∧ q.comp (C a * X + C b) = q.map (MulSemiringAction.toRingHom G k g) :=
  smul_mk_eq_mk_iff_of_aeval g (adjoin_ofPolynomialGen q hq hcrit)
    (algebraMap_ofPolynomial_X q hq hcrit) (adjoin_ofPolynomialGen q hq hcrit)
    (algebraMap_ofPolynomial_X q hq hcrit)

end IsoClass

end OfPolynomial

end AlgebraicBelyiPair

end TauCeti
