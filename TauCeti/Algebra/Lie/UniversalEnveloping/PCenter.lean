/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.Frobenius
public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Central `p`-polynomials in a universal enveloping algebra

Let `R` be a commutative ring of exponential characteristic `p` and `L` a Lie `R`-algebra.  A
*linearized polynomial*, or `p`-polynomial, in an element `u` of an `R`-algebra is an `R`-linear
combination of the Frobenius powers `u ^ p ^ i`; it is *monic of degree `p ^ e`* when the
coefficient of `u ^ p ^ e` is `1` and no higher power occurs, and it has *zero constant term*
when the exponent `p ^ 0 = 1` is the smallest one allowed, so that the polynomial is divisible
by `u`.

The theorem of this file is that, as soon as `Module.End R L` is a Noetherian `R`-module — over a
field, as soon as `L` is finite-dimensional — every `x : L` admits such a polynomial in `ι x` that
is central in `U(L)`, and that it automatically lies in the augmentation ideal `U⁺(L)`.  These
elements are Hochschild's central `p`-polynomials: the commutative subalgebra they generate makes
`U(L)` a finite module over a Noetherian commutative ring, and the two-sided ideal they generate
is what the Krull intersection theorem is eventually applied to.

Two ingredients drive the proof, and neither needs the Poincaré-Birkhoff-Witt theorem.

* `LieAlgebra.ad R L x` lives in `Module.End R L`, and as soon as that module is Noetherian the
  chain of submodules spanned by the initial segments of the sequence
  `(LieAlgebra.ad R L x ^ p ^ i)` cannot grow forever.  The first repetition is a monic linearized
  relation.  Over a field this Noetherian hypothesis is finite-dimensionality of `L`, which is the
  form the theory is used in.
* The Frobenius commutator identity `TauCeti.LieAlgebra.ad_pow_expChar_pow` turns that relation
  into a statement about the inner derivation of `U(L)` attached to `ι x`: a linearized
  polynomial in an inner derivation is again a derivation, because each `p`-th power of a
  derivation is one in characteristic `p`, and here that derivation is inner, attached to the
  corresponding polynomial in `ι x`.  A derivation vanishing on the canonical Lie generators
  vanishes, so the polynomial is central.

⚠ Centrality is *not* natural for an arbitrary Lie homomorphism `f : L →ₗ⁅R⁆ L'`.  For the
abelian `L = R x` one may take the polynomial `ι x` itself, since `LieAlgebra.ad R L x = 0`; its
image in `U(L')` for `L' = ⟨x, y⟩` with `⁅x, y⁆ = y` is `ι x`, which is not central there.  What
does survive is naturality along *surjections*, where the image of `ι (L)` still generates, and
that is `TauCeti.UniversalEnvelopingAlgebra.pPolynomial_map_mem_center_of_surjective` below.

## Main statements

* `TauCeti.UniversalEnvelopingAlgebra.mem_center_of_ad_pPolynomial_eq_zero`: a monic linearized
  relation satisfied by `LieAlgebra.ad R L x` makes the corresponding polynomial in `ι x`
  central.
* `TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial_of_isNoetherian`: over a
  commutative ring, every element has such a polynomial as soon as `Module.End R L` is
  Noetherian.
* `TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial`: the specialization to a
  finite-dimensional Lie algebra over a field of characteristic `p`.
* `TauCeti.UniversalEnvelopingAlgebra.pPolynomial_ι_mem_augmentation_toIdeal`: having zero
  constant term, it lies in the augmentation ideal.
* `TauCeti.UniversalEnvelopingAlgebra.exists_pow_ι_mem_center_of_isNilpotent_ad`: if
  `LieAlgebra.ad R L x` is nilpotent the polynomial may be taken to be a single Frobenius power
  `ι x ^ p ^ e`.
* `TauCeti.UniversalEnvelopingAlgebra.isNilpotent_ad_ι_of_isNilpotent_ad`: in that situation
  `LieAlgebra.ad R U(L) (ι x)` is itself nilpotent.
* `TauCeti.UniversalEnvelopingAlgebra.pPolynomial_map_mem_center_of_surjective`: centrality is
  natural along surjective Lie homomorphisms.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531--533.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V and pp. 202--203.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of an enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- **A monic linearized relation on `ad x` produces a central element of `U(L)`.**  If the
Frobenius powers of `LieAlgebra.ad R L x` satisfy the monic relation with coefficients `a`, then
the same linearized polynomial evaluated at the canonical Lie generator `ι x` is central in
`U(L)`.

The passage between the two is the Frobenius commutator identity: bracketing with the polynomial
in `ι x` is the corresponding polynomial in the inner derivation attached to `ι x`, which on the
Lie generators is the polynomial in `LieAlgebra.ad R L x`.  A derivation of `U(L)` vanishing on
the Lie generators vanishes. -/
theorem mem_center_of_ad_pPolynomial_eq_zero (p : ℕ) [ExpChar R p] {e : ℕ} {a : Fin e → R} {x : L}
    (h : LieAlgebra.ad R L x ^ p ^ e +
        ∑ i : Fin e, a i • LieAlgebra.ad R L x ^ p ^ (i : ℕ) = 0) :
    _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
      Subalgebra.center R U := by
  have : ExpChar U p :=
    expChar_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := R) U) p
  rw [mem_center_iff_forall_lie_ι R L]
  intro y
  -- Bracketing with the polynomial in `ι x` is the polynomial in the inner derivation of `ι x`.
  have hlin : LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ)) =
      LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x) ^ p ^ e +
        ∑ i : Fin e,
          a i • LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x) ^ p ^ (i : ℕ) := by
    rw [map_add, map_sum]
    simp only [map_smul, LieAlgebra.ad_pow_expChar_pow]
  -- On the Lie generators it is the image of the polynomial in `LieAlgebra.ad R L x`.
  have happ : LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
          ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ))
        (_root_.UniversalEnvelopingAlgebra.ι R y) =
      _root_.UniversalEnvelopingAlgebra.ι R ((LieAlgebra.ad R L x ^ p ^ e +
        ∑ i : Fin e, a i • LieAlgebra.ad R L x ^ p ^ (i : ℕ)) y) := by
    rw [hlin]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, ad_ι_pow_apply_ι,
      map_add, map_sum, map_smul]
  have hzero : _root_.UniversalEnvelopingAlgebra.ι R ((LieAlgebra.ad R L x ^ p ^ e +
      ∑ i : Fin e, a i • LieAlgebra.ad R L x ^ p ^ (i : ℕ)) y) = 0 := by
    rw [h, LinearMap.zero_apply, map_zero]
  exact happ.trans hzero

variable (R L)

/-- **Every element has a central `p`-polynomial as soon as `Module.End R L` is Noetherian.**
For `x : L` there are an exponent `e` and coefficients `a` making the monic linearized polynomial
`ι x ^ p ^ e + ∑ i, a i • ι x ^ p ^ i` central in `U(L)`.  The displayed indexing gives the
leading exponent `p ^ e` and lower exponents `p ^ i` for `i : Fin e`; it does not assert that `e`
is minimal.  Every exponent is at least `p ^ 0 = 1`, so the element also lies in the augmentation
ideal (`TauCeti.UniversalEnvelopingAlgebra.pPolynomial_ι_mem_augmentation_toIdeal`).

Noetherianity enters only through `Module.End R L`, where the Frobenius powers of
`LieAlgebra.ad R L x` cannot stay linearly independent.  Over a field this is
`TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial`. -/
theorem exists_pCentralPolynomial_of_isNoetherian (p : ℕ) [ExpChar R p]
    [IsNoetherian R (Module.End R L)] (x : L) :
    ∃ (e : ℕ) (a : Fin e → R),
      _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
          ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
        Subalgebra.center R U := by
  obtain ⟨e, c, hc⟩ :=
    exists_sum_smul_eq_of_isNoetherian R fun i : ℕ => LieAlgebra.ad R L x ^ p ^ i
  refine ⟨e, fun i => -c i, mem_center_of_ad_pPolynomial_eq_zero p ?_⟩
  have hneg : ∑ i : Fin e, (-c i) • LieAlgebra.ad R L x ^ p ^ (i : ℕ) =
      -∑ i : Fin e, c i • LieAlgebra.ad R L x ^ p ^ (i : ℕ) := by
    simp [neg_smul]
  rw [hneg, hc, add_neg_cancel]

/-- **A `p`-polynomial with zero constant term lies in the augmentation ideal.**  Every exponent
`p ^ i` occurring is at least `p ^ 0 = 1`, so each summand is a positive power of a canonical Lie
generator.  Together with
`TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial_of_isNoetherian` this places the
central `p`-polynomial of an element in `Z(U(L)) ∩ U⁺(L)`. -/
theorem pPolynomial_ι_mem_augmentation_toIdeal {p : ℕ} (hp : p ≠ 0) (e : ℕ) (a : Fin e → R)
    (x : L) :
    _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
      (HopfIdeal.augmentation R U).toIdeal := by
  refine Ideal.add_mem _ (pow_ι_mem_augmentation_toIdeal R L x (pow_ne_zero e hp))
    (Submodule.sum_mem _ fun i _ => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (pow_ι_mem_augmentation_toIdeal R L x (pow_ne_zero _ hp))

variable {R L}

/-- **The adjoint-nilpotent specialization.**  When `LieAlgebra.ad R L x` is nilpotent the
linearized relation may be taken to be `T ^ p ^ e = 0`, so a single Frobenius power of the
canonical Lie generator is already central.  This is the step that, in the positive-characteristic
half of Ado--Iwasawa, forces an adjoint-nilpotent element to act nilpotently on the finite
quotient. -/
theorem exists_pow_ι_mem_center_of_isNilpotent_ad (p : ℕ) [ExpChar R p] (hp : p ≠ 1) {x : L}
    (h : IsNilpotent (LieAlgebra.ad R L x)) :
    ∃ e : ℕ, _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e ∈ Subalgebra.center R U := by
  obtain ⟨k, hk⟩ := h
  have hp1 : 1 < p := by have := expChar_pos R p; omega
  have hzero : LieAlgebra.ad R L x ^ p ^ k = 0 := by
    rw [← Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_pow_self hp1)), pow_add, hk, mul_zero]
  refine ⟨k, ?_⟩
  simpa using
    mem_center_of_ad_pPolynomial_eq_zero (a := (0 : Fin k → R)) p (by simp [hzero])

/-- **Adjoint nilpotence passes to the enveloping algebra.**  In characteristic `p`, if
`LieAlgebra.ad R L x` is nilpotent on `L` then the inner derivation of `U(L)` attached to `ι x` is
nilpotent on all of `U(L)` — not merely locally nilpotent, as the characteristic-zero
iterated-commutator expansion would give. -/
theorem isNilpotent_ad_ι_of_isNilpotent_ad (p : ℕ) [ExpChar R p] (hp : p ≠ 1) {x : L}
    (h : IsNilpotent (LieAlgebra.ad R L x)) :
    IsNilpotent (LieAlgebra.ad R U (_root_.UniversalEnvelopingAlgebra.ι R x)) := by
  have : ExpChar U p :=
    expChar_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := R) U) p
  obtain ⟨e, he⟩ := exists_pow_ι_mem_center_of_isNilpotent_ad p hp h
  exact LieAlgebra.isNilpotent_ad_of_pow_expChar_pow_mem_center p he

/-- **Centrality of a `p`-polynomial is natural along surjections.**  If `f : L →ₗ⁅R⁆ L'` is
surjective then the image of `ι (L)` still generates `U(L')`, so the image of a central
`p`-polynomial of `x` is a central `p`-polynomial of `f x`, with the same exponent and
coefficients.  Naturality fails for a general Lie homomorphism; see the note in the module
docstring. -/
theorem pPolynomial_map_mem_center_of_surjective {L' : Type w} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) {p e : ℕ} {a : Fin e → R} {x : L}
    (h : _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R x ^ p ^ (i : ℕ) ∈
      Subalgebra.center R U) :
    _root_.UniversalEnvelopingAlgebra.ι R (f x) ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι R (f x) ^ p ^ (i : ℕ) ∈
      Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L') := by
  have himg := Subalgebra.map_center_le_center (f := map R f) (map_surjective_of_surjective R f hf)
  refine himg (Subalgebra.mem_map.mpr ⟨_, h, ?_⟩)
  have hpow : ∀ n : ℕ, map R f (_root_.UniversalEnvelopingAlgebra.ι R x ^ n) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x) ^ n := fun n => by rw [map_pow, map_ι]
  rw [map_add, map_sum, hpow]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [map_smul, hpow])

end CommRing

section Field

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]

/-- **Every element of a finite-dimensional Lie algebra over a field has a central
`p`-polynomial.**  This is the finite-dimensional specialization of
`TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial_of_isNoetherian`: over a field,
finite-dimensionality of `L` makes `Module.End K L` Noetherian. -/
theorem exists_pCentralPolynomial (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L]
    (x : L) :
    ∃ (e : ℕ) (a : Fin e → K),
      _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ e +
          ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ (i : ℕ) ∈
        Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K L) :=
  exists_pCentralPolynomial_of_isNoetherian K L p x

end Field

end TauCeti.UniversalEnvelopingAlgebra
