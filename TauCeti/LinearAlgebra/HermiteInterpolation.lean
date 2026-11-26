/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.Algebra.Polynomial.Taylor
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
public import TauCeti.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Hermite interpolation

Given nodes `a : ι → R` and multiplicities `m : ι → ℕ`, the *Hasse jets* of a polynomial `f` are
the values `(hasseDeriv k f).eval (a i)` for `k < m i`: the first `m i` Taylor coefficients of `f`
at `a i`. Hermite interpolation says that when the nodes are pairwise distinct (over a commutative
ring: when differences of nodes of nonzero multiplicity are units), these `M = ∑ i, m i` numbers
can be prescribed arbitrarily, and determine `f` uniquely among the polynomials of degree below `M`.
This generalises Lagrange interpolation (`Lagrange.funEquivDegreeLT`, every `m i = 1`) to arbitrary
multiplicities, including `0`, and to Hasse rather than ordinary derivatives, so that it holds in
every characteristic.

The kernel of the unrestricted jet map `Polynomial.hasseJet a m` on `R[X]` is the ideal generated
by `∏ i, (X - a i) ^ m i`: at one node this is Taylor's formula
(`Polynomial.X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero`), and the factors are pairwise
coprime. The map is surjective by the Chinese remainder theorem, so it identifies
`R[X] ⧸ (∏ i, (X - a i) ^ m i)` with the jet space (`Polynomial.hasseJetQuotientEquiv`); since the
product is monic of degree `M`, the restriction `Polynomial.hermiteJet a m` to polynomials of
degree below `M` is bijective (`AdjoinRoot.degreeLTEquiv`). The identification factors through
the Chinese remainder isomorphism `R[X] ⧸ (∏ i, (X - a i) ^ m i) ≃ ∏ i, R[X] ⧸ ((X - a i) ^ m i)`
followed by the Taylor coordinates `TauCeti.taylorJetQuotientEquiv` at each node.

For nodes indexed by `Fin r`, the matrix of `Polynomial.hermiteJet a m` from the monomial basis
`Polynomial.degreeLT.basis R M` to the lexicographically ordered standard basis
`TauCeti.lexJetBasis R m` of the jet space is `Matrix.confluentVandermonde a m`
(`Polynomial.toMatrix_hermiteJet`), so the Hermite jet map is bijective iff the confluent
Vandermonde determinant is a unit (`Polynomial.hermiteJet_bijective_iff_isUnit_det`), and the
inverse matrix `(Matrix.confluentVandermonde a m)⁻¹` represents the interpolation operator
`(Polynomial.hermiteJetEquiv ha m).symm` and lists the coefficients of `Polynomial.hermiteBasis`.
Combining this matrix identification with `Matrix.isUnit_det_confluentVandermonde_iff` gives the
exact `↔` characterizations of bijectivity for both Hasse and ordinary-derivative Hermite
interpolation over arbitrary commutative rings and fields (`Polynomial.hermiteJet_bijective_iff`,
`Polynomial.ordinaryHermiteJet_bijective_iff`), allowing repeated nodes of multiplicity `0`.

## Main definitions

* `Polynomial.hasseJet a m`: the `R`-linear map `f ↦ ((hasseDeriv k f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteJet a m`: its restriction to `Polynomial.degreeLT R (∑ i, m i)`.
* `Polynomial.ordinaryHermiteJet a m`: the Hermite jet map built from ordinary derivatives,
  `f ↦ ((derivative^[k] f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteJetEquiv`: for nodes with unit differences, Hermite interpolation as a linear
  equivalence; its inverse sends a jet datum to its interpolation polynomial.
* `Polynomial.hermiteBasis`: the basis of `degreeLT R (∑ i, m i)` dual to the Hasse jets.
* `TauCeti.lexJetBasis R m`: the standard basis of the jet space `∀ i, Fin (m i) → R`, indexed
  by `Fin (∑ i, m i)` through `finSigmaFinEquiv`.

## Main results

* `Polynomial.all_jets_vanish_iff_dvd`: over a commutative ring without zero divisors, for
  injective nodes, the jets of `f` all vanish iff `∏ i, (X - C (a i)) ^ m i ∣ f`;
  `all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub` is the form over a commutative ring.
* `Polynomial.hasseJetQuotientEquiv`: `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteQuotientEquiv`: the Chinese remainder isomorphism
  `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃+* ∀ i, R[X] ⧸ ((X - C (a i)) ^ m i)`, and
  `Polynomial.hasseJetQuotientEquiv_apply`: the jet equivalence is this isomorphism followed by the
  local Taylor coordinates.
* `Polynomial.hermiteJet_injective`, `Polynomial.hermiteJet_injective_of_injOn`,
  `Polynomial.hasseJet_eq_zero_iff`, `Polynomial.hasseJet_eq_zero_iff_of_injOn`,
  `Polynomial.ker_hasseJet`: over a commutative ring without zero divisors, for injective nodes (or
  nodes injective on nonzero multiplicities), `hermiteJet a m` is injective and
  `ker (hasseJet a m)` is generated by `∏ i, (X - C (a i)) ^ m i`;
  `Polynomial.ker_hasseJet_of_pairwise_isUnit_sub` is the kernel for nodes with unit differences,
  and `Polynomial.ordinaryHermiteJet_injective` is the ordinary-derivative form when `k ! ≠ 0`.
* `Polynomial.hermiteJet_bijective`: over a field, for injective nodes, the Hermite jet map is
  bijective; `hermiteJet_bijective_of_pairwise_isUnit_sub` is the form over a commutative ring.
* `Polynomial.eq_hermiteJetEquiv_symm_iff`, `Polynomial.existsUnique_hermite_interpolation`: the
  interpolation polynomial is the unique polynomial of degree below `∑ i, m i` with the prescribed
  jets.
* `Polynomial.hasseJet_map`, `Polynomial.hermiteJet_map`, `Polynomial.map_hermiteJetEquiv_symm`:
  the jet maps and interpolation commute with ring homomorphisms.
* `Polynomial.ordinaryHermiteJet_bijective`,
  `Polynomial.ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub`: the same interpolation with
  ordinary derivatives, when the factorials `k !` with `k < m i` are units.
* `Polynomial.toMatrix_hermiteJet`, `Polynomial.toLin_confluentVandermonde`,
  `Polynomial.toMatrix_hermiteJet_piBasis`,
  `Polynomial.toMatrix_hermiteJetEquiv_symm`, `Polynomial.hermiteBasis_toMatrix_degreeLT_basis`,
  and `Polynomial.degreeLT_basis_toMatrix_hermiteBasis`: `hermiteJet a m`,
  `(hermiteJetEquiv ha m).symm`, and `hermiteBasis ha m` in coordinates are
  `Matrix.confluentVandermonde a m` and its inverse.
* `Polynomial.hermiteJet_bijective_iff_isUnit_det`: for nodes indexed by `Fin r`, the Hermite jet
  map is bijective iff `det (confluentVandermonde a m)` is a unit.
* `Polynomial.hermiteJet_bijective_iff`, `Polynomial.hermiteJet_bijective_iff_ne`,
  `Polynomial.ordinaryHermiteJet_bijective_iff`, and
  `Polynomial.ordinaryHermiteJet_bijective_iff_ne`: exact `↔` characterizations of when Hasse
  and ordinary-derivative Hermite interpolation are bijective over commutative rings and fields.
* `Polynomial.range_hasseJet_comp_degreeLT_eq_range_hermiteJet`,
  `Polynomial.finrank_range_hermiteJet_degreeLT`: over an integral domain, when nodes of nonzero
  multiplicity are pairwise distinct, the image of `hasseJet a m` on polynomials of degree below `N`
  equals the range of `hermiteJet a m` once `∑ i, m i ≤ N`, and has dimension `min N (∑ i, m i)`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6: the Hasse derivatives as Taylor coefficients, pp. 282–283, and the multiplicity
  criterion through Hasse derivatives, Lemma 11.16, pp. 283–284.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Grundlehren 326, 2000),
  proof of Lemma 3.24, p. 100, and Exercise 3.11, p. 111.
-/

public section

open Function Finset
open scoped Matrix Nat

namespace TauCeti

variable {R : Type*} [Semiring R]

variable (R) in
/-- The standard basis of the jet space `∀ i, Fin (m i) → R`, indexed by `Fin (∑ i, m i)` in the
lexicographic order `finSigmaFinEquiv ⟨i, k⟩` of the jets. -/
noncomputable def lexJetBasis {r : ℕ} (m : Fin r → ℕ) :
    Module.Basis (Fin (∑ i, m i)) R (∀ i, Fin (m i) → R) :=
  (Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv

/-- The coordinate of a jet datum at the position `ρ` is its entry at the jet
`finSigmaFinEquiv.symm ρ`. -/
@[simp]
theorem lexJetBasis_repr {r : ℕ} (m : Fin r → ℕ) (c : ∀ i, Fin (m i) → R) (ρ : Fin (∑ i, m i)) :
    (lexJetBasis R m).repr c ρ = c (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 := by
  simp [lexJetBasis]

/-- The basis vector at the position `ρ` is the indicator of the jet `finSigmaFinEquiv.symm ρ`. -/
@[simp]
theorem lexJetBasis_apply {r : ℕ} (m : Fin r → ℕ) (ρ : Fin (∑ i, m i)) :
    lexJetBasis R m ρ =
      Pi.single (finSigmaFinEquiv.symm ρ).1 (Pi.single (finSigmaFinEquiv.symm ρ).2 1) := by
  simp [lexJetBasis, Pi.basis_apply]

end TauCeti

namespace Polynomial

variable {ι R S K : Type*}

section Semiring

variable [Semiring R]

/-- The Hasse jet map at the nodes `a i` with multiplicities `m i`: the `R`-linear map sending a
polynomial `f` to its Hasse jets `(hasseDeriv k f).eval (a i)` of the orders `k < m i`. A node
with `m i = 0` contributes no coordinate. At each node these are the Taylor coordinates
`TauCeti.taylorJet (a i) (m i)`. -/
noncomputable def hasseJet (a : ι → R) (m : ι → ℕ) : R[X] →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => TauCeti.taylorJet (a i) (m i)

@[simp]
theorem hasseJet_apply (a : ι → R) (m : ι → ℕ) (f : R[X]) (i : ι) (k : Fin (m i)) :
    hasseJet a m f i k = (hasseDeriv k f).eval (a i) := by
  simp [hasseJet]

/-- Taking Hasse jets commutes with mapping the coefficients and nodes by a ring homomorphism. -/
theorem hasseJet_map [Semiring S] (ψ : R →+* S) (a : ι → R) (m : ι → ℕ) (f : R[X]) :
    hasseJet (fun i => ψ (a i)) m (f.map ψ) = fun i k => ψ (hasseJet a m f i k) := by
  ext i k
  simp only [hasseJet_apply, hasseDeriv_map, eval_map, eval₂_hom]

/-- The Hasse jet map vanishes at `f` iff every Hasse derivative of order `k < m i` vanishes at
`a i`. -/
theorem hasseJet_eq_zero_iff_forall (a : ι → R) (m : ι → ℕ) (f : R[X]) :
    hasseJet a m f = 0 ↔ ∀ i, ∀ k < m i, (hasseDeriv k f).eval (a i) = 0 := by
  simp only [funext_iff, hasseJet_apply, Pi.zero_apply]
  exact ⟨fun h i k hk => h i ⟨k, hk⟩, fun h i k => h i k k.isLt⟩

variable [Fintype ι]

/-- The Hermite jet map: the Hasse jet map `hasseJet a m` on the polynomials of degree below
`∑ i, m i`, the dimension of the space of jets. -/
noncomputable def hermiteJet (a : ι → R) (m : ι → ℕ) :
    degreeLT R (∑ i, m i) →ₗ[R] ∀ i, Fin (m i) → R :=
  (hasseJet a m).domRestrict _

@[simp]
theorem hermiteJet_apply (a : ι → R) (m : ι → ℕ) (f : degreeLT R (∑ i, m i)) :
    hermiteJet a m f = hasseJet a m f := by
  simp [hermiteJet]

/-- The Hermite jet map commutes with mapping the coefficients and nodes by a ring homomorphism. -/
theorem hermiteJet_map [Semiring S] (ψ : R →+* S) (a : ι → R) (m : ι → ℕ)
    (f : degreeLT R (∑ i, m i)) :
    hermiteJet (fun i => ψ (a i)) m ⟨(f : R[X]).map ψ, map_mem_degreeLT ψ f.property⟩ =
      fun i k => ψ (hermiteJet a m f i k) := by
  rw [hermiteJet_apply, hermiteJet_apply]
  exact hasseJet_map ψ a m f

/-- The Hermite jet map built from ordinary derivatives,
`f ↦ ((derivative^[k] f).eval (a i))_{i, k < m i}`, on polynomials of degree below `∑ i, m i`. -/
noncomputable def ordinaryHermiteJet (a : ι → R) (m : ι → ℕ) :
    degreeLT R (∑ i, m i) →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => LinearMap.pi fun k =>
    leval (a i) ∘ₗ (derivative ^ (k : ℕ)) ∘ₗ (degreeLT R (∑ i, m i)).subtype

/-- The coordinates of the ordinary Hermite jet map are the iterated derivatives at the nodes. -/
@[simp]
theorem ordinaryHermiteJet_apply (a : ι → R) (m : ι → ℕ) (f : degreeLT R (∑ i, m i)) (i : ι)
    (k : Fin (m i)) :
    ordinaryHermiteJet a m f i k = (derivative^[k] (f : R[X])).eval (a i) := by
  simp [ordinaryHermiteJet, pow_apply_eq_iterate]

/-- The ordinary Hermite jets are the Hasse jets scaled by `k !`. -/
theorem ordinaryHermiteJet_eq_factorial_mul (a : ι → R) (m : ι → ℕ) (f : degreeLT R (∑ i, m i))
    (i : ι) (k : Fin (m i)) :
    ordinaryHermiteJet a m f i k = ((k : ℕ) ! : R) * hermiteJet a m f i k := by
  rw [ordinaryHermiteJet_apply, hermiteJet_apply, hasseJet_apply, ← factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- For nodes indexed by an arbitrary finite type `ι`, the matrix of `hermiteJet a m` from
`degreeLT.basis R (∑ i, m i)` to `Pi.basis fun i => Pi.basisFun R (Fin (m i))` has entry
`choose j k * a i ^ (j - k)` in row `⟨i, k⟩` and column `j`. -/
@[simp]
theorem toMatrix_hermiteJet_piBasis [Fintype ι] (a : ι → R) (m : ι → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i))
      (Pi.basis fun i => Pi.basisFun R (Fin (m i))) (hermiteJet a m) =
      Matrix.of fun (x : Σ i, Fin (m i)) (j : Fin (∑ i, m i)) =>
        ((j : ℕ).choose x.2 : R) * a x.1 ^ ((j : ℕ) - x.2) := by
  ext ⟨i, k⟩ j
  simp [LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basisFun_repr,
    ← monomial_one_right_eq_X_pow, hasseDeriv_monomial]

variable {r : ℕ}

/-- **The matrix of the Hermite jet map is the confluent Vandermonde matrix.** With respect to the
monomial basis `degreeLT.basis R (∑ i, m i)` of `degreeLT R (∑ i, m i)` and the lexicographically
ordered standard basis `TauCeti.lexJetBasis R m` of the jet space `∀ i : Fin r, Fin (m i) → R`,
the matrix of `hermiteJet a m` is `Matrix.confluentVandermonde a m`. -/
@[simp]
theorem toMatrix_hermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i)) (TauCeti.lexJetBasis R m) (hermiteJet a m) =
      Matrix.confluentVandermonde a m := by
  ext ρ j
  simp [LinearMap.toMatrix_apply, Matrix.confluentVandermonde_apply]

/-- The Hermite jet map is the linear map of the confluent Vandermonde matrix in the monomial
basis and the lexicographic jet basis. -/
theorem toLin_confluentVandermonde (a : Fin r → R) (m : Fin r → ℕ) :
    Matrix.toLin (degreeLT.basis R (∑ i, m i)) (TauCeti.lexJetBasis R m)
      (Matrix.confluentVandermonde a m) = hermiteJet a m := by
  rw [← toMatrix_hermiteJet, Matrix.toLin_toMatrix]

/-- Multiplying the coefficient vector of `f ∈ degreeLT R (∑ i, m i)` by
`Matrix.confluentVandermonde a m` computes the Hasse jets of `f` in lexicographic order. -/
theorem confluentVandermonde_mulVec_degreeLTEquiv (a : Fin r → R) (m : Fin r → ℕ)
    (f : degreeLT R (∑ i, m i)) :
    Matrix.confluentVandermonde a m *ᵥ degreeLTEquiv R (∑ i, m i) f =
      fun ρ => hermiteJet a m f (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 := by
  have h := LinearMap.toMatrix_mulVec_repr (degreeLT.basis R (∑ i, m i)) (TauCeti.lexJetBasis R m)
    (hermiteJet a m) f
  have hf : ⇑((degreeLT.basis R (∑ i, m i)).repr f) = degreeLTEquiv R (∑ i, m i) f :=
    _root_.funext fun j => degreeLT.basis_repr j f
  rw [toMatrix_hermiteJet, hf] at h
  ext ρ
  simpa using congr_fun h ρ

end CommSemiring

section CommRing

variable [CommRing R] {a : ι → R}

/-- The Hasse jet map is surjective when the differences of the nodes are units: by the Chinese
remainder theorem, a polynomial can be prescribed modulo each `(X - a i) ^ m i`, where its jets at
`a i` are its first Taylor coefficients. -/
theorem hasseJet_surjective [Finite ι] (ha : Pairwise fun i j => IsUnit (a i - a j))
    (m : ι → ℕ) : Surjective (hasseJet a m) := by
  intro c
  obtain ⟨g, hg⟩ := Ideal.exists_forall_sub_mem_ideal
    (I := fun i => Ideal.span {(X - C (a i)) ^ m i})
    (fun _ _ hij => (Ideal.isCoprime_span_singleton_iff _ _).2
      (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow)
    (fun i => ∑ k : Fin (m i), c i k • (X - C (a i)) ^ (k : ℕ))
  refine ⟨g, _root_.funext fun i => ?_⟩
  -- At each node, `g` has the Taylor coordinates of its local representative.
  have h := TauCeti.taylorJet_eq_zero_iff.2 (hg i)
  rw [map_sub, sub_eq_zero, TauCeti.taylorJet_sum_smul_X_sub_C_pow] at h
  exact h

variable [Fintype ι]

/-- **The kernel of the jet map.** If the differences of the nodes are units, the Hasse jets of
`f` of the orders `k < m i` at the nodes `a i` all vanish iff `∏ i, (X - a i) ^ m i` divides `f`.
-/
theorem all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : ι → ℕ) (f : R[X]) :
    (∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = 0) ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f :=
  ⟨fun h => Fintype.prod_dvd_of_coprime
    (fun _ _ hij => (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow) fun i =>
      X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.2 fun k hk => h i ⟨k, hk⟩,
    fun h i k => X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.1
      ((dvd_prod_of_mem _ (mem_univ i)).trans h) k k.isLt⟩

/-- When the differences of the nodes are units, the Hasse jets of `f` vanish iff
`∏ i, (X - C (a i)) ^ m i` divides `f`. -/
theorem hasseJet_eq_zero_iff_of_pairwise_isUnit_sub
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : ι → ℕ) (f : R[X]) :
    hasseJet a m f = 0 ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f := by
  rw [← all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub ha m f]
  simp [funext_iff]

variable (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : ι → ℕ)
include ha

/-- The kernel of the Hasse jet map is the ideal generated by `∏ i, (X - a i) ^ m i`, when the
differences of the nodes are units. -/
theorem ker_hasseJet_of_pairwise_isUnit_sub :
    LinearMap.ker (hasseJet a m) = (Ideal.span {∏ i, (X - C (a i)) ^ m i}).restrictScalars R := by
  ext f
  simp [Ideal.mem_span_singleton, hasseJet_eq_zero_iff_of_pairwise_isUnit_sub ha m f]

/-- When the differences of the nodes are units, the ideal generated by `∏ i, (X - a i) ^ m i`
is the intersection of the ideals generated by its factors `(X - a i) ^ m i`. -/
theorem span_prod_X_sub_C_pow_eq_iInf :
    Ideal.span {∏ i, (X - C (a i)) ^ m i} = ⨅ i, Ideal.span {(X - C (a i)) ^ m i} :=
  (Ideal.iInf_span_singleton fun _ _ hij => (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow).symm

/-- The jet space is the quotient of `R[X]` by `∏ i, (X - a i) ^ m i`, when the differences of
the nodes are units: the Hasse jet map identifies the two. -/
noncomputable def hasseJetQuotientEquiv :
    (R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃ₗ[R] ∀ i, Fin (m i) → R :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ker_hasseJet_of_pairwise_isUnit_sub ha m).symm ≪≫ₗ
      (hasseJet a m).quotKerEquivOfSurjective (hasseJet_surjective ha m)

@[simp]
theorem hasseJetQuotientEquiv_mk (f : R[X]) :
    hasseJetQuotientEquiv ha m (Ideal.Quotient.mk _ f) = hasseJet a m f := by
  simp only [← Ideal.Quotient.mk_eq_mk, hasseJetQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The inverse quotient equivalence sends the jets of a polynomial to its residue class. -/
@[simp]
theorem hasseJetQuotientEquiv_symm_hasseJet (f : R[X]) :
    (hasseJetQuotientEquiv ha m).symm (hasseJet a m f) = Ideal.Quotient.mk _ f := by
  rw [LinearEquiv.symm_apply_eq, hasseJetQuotientEquiv_mk]

/-- **The Chinese remainder theorem** for the nodes: when their differences are units,
`R[X] ⧸ (∏ i, (X - a i) ^ m i)` is the product of the local quotients `R[X] ⧸ ((X - a i) ^ m i)`.
-/
noncomputable def hermiteQuotientEquiv :
    R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i} ≃+*
      ∀ i, R[X] ⧸ Ideal.span {(X - C (a i)) ^ m i} :=
  (Ideal.quotEquivOfEq (span_prod_X_sub_C_pow_eq_iInf ha m)).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hij =>
      (Ideal.isCoprime_span_singleton_iff _ _).2 (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow

@[simp]
theorem hermiteQuotientEquiv_mk (f : R[X]) (i : ι) :
    hermiteQuotientEquiv ha m (Ideal.Quotient.mk _ f) i = Ideal.Quotient.mk _ f := by
  rw [hermiteQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact Ideal.quotientInfRingEquivPiQuotient_mk_apply _ _ _

/-- The jet equivalence `hasseJetQuotientEquiv` is the Chinese remainder isomorphism
`hermiteQuotientEquiv` followed, at each node `a i`, by the Taylor coordinates
`TauCeti.taylorJetQuotientEquiv (a i) (m i)` on `R[X] ⧸ ((X - a i) ^ m i)`. -/
theorem hasseJetQuotientEquiv_apply (x : R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) (i : ι) :
    hasseJetQuotientEquiv ha m x i =
      TauCeti.taylorJetQuotientEquiv (a i) (m i) (hermiteQuotientEquiv ha m x i) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  ext k
  simp

/-- The Hermite jet map is the composite of the projection to `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i)`,
the Chinese remainder isomorphism, and the local Taylor coordinates. -/
theorem hermiteJet_eq_taylorJetQuotientEquiv (f : degreeLT R (∑ i, m i)) (i : ι) :
    hermiteJet a m f i =
      TauCeti.taylorJetQuotientEquiv (a i) (m i)
        (hermiteQuotientEquiv ha m (Ideal.Quotient.mk _ (f : R[X])) i) := by
  rw [hermiteJet_apply, ← hasseJetQuotientEquiv_mk ha m, hasseJetQuotientEquiv_apply]

/-- Hermite interpolation as a linear equivalence, when the differences of the nodes are units: a
polynomial of degree below `∑ i, m i` is determined by its Hasse jets of the orders `k < m i` at
the nodes `a i`, and every jet datum is attained. It is `AdjoinRoot.degreeLTEquiv` for the monic
`∏ i, (X - a i) ^ m i` of degree `∑ i, m i`, followed by `hasseJetQuotientEquiv`. -/
noncomputable def hermiteJetEquiv : degreeLT R (∑ i, m i) ≃ₗ[R] ∀ i, Fin (m i) → R :=
  LinearEquiv.ofEq _ _ (by nontriviality R; rw [natDegree_prod_X_sub_C_pow]) ≪≫ₗ
    AdjoinRoot.degreeLTEquiv (monic_prod_X_sub_C_pow univ a m) ≪≫ₗ hasseJetQuotientEquiv ha m

@[simp]
theorem hermiteJetEquiv_apply (f : degreeLT R (∑ i, m i)) :
    hermiteJetEquiv ha m f = hermiteJet a m f := by
  rw [hermiteJet_apply, ← hasseJetQuotientEquiv_mk ha m]
  -- `hermiteJetEquiv ha m f` unfolds to `hasseJetQuotientEquiv ha m` of `AdjoinRoot.degreeLTEquiv`
  -- of `f`, and `AdjoinRoot.mk g` is `Ideal.Quotient.mk (Ideal.span {g})` by definition.
  -- `LinearEquiv.ofEq` preserves the underlying polynomial (`LinearEquiv.coe_ofEq_apply`).
  exact congr_arg (hasseJetQuotientEquiv ha m) <| AdjoinRoot.degreeLTEquiv_apply
    (monic_prod_X_sub_C_pow univ a m)
    (LinearEquiv.ofEq _ _ (by nontriviality R; rw [natDegree_prod_X_sub_C_pow]) f)

/-- Interpolation recovers a polynomial of degree below the total multiplicity from its jets. -/
@[simp]
theorem hermiteJetEquiv_symm_hasseJet (f : degreeLT R (∑ i, m i)) :
    (hermiteJetEquiv ha m).symm (hasseJet a m f) = f := by
  rw [LinearEquiv.symm_apply_eq, hermiteJetEquiv_apply, hermiteJet_apply]

/-- The interpolation polynomial realizes the prescribed Hasse jet datum. -/
@[simp]
theorem hasseJet_hermiteJetEquiv_symm (c : ∀ i, Fin (m i) → R) :
    hasseJet a m ((hermiteJetEquiv ha m).symm c) = c := by
  rw [← hermiteJet_apply, ← hermiteJetEquiv_apply ha m, LinearEquiv.apply_symm_apply]

/-- **Hermite interpolation** over a commutative ring: when the differences of the nodes are
units, the Hermite jet map on the polynomials of degree below `∑ i, m i` is bijective. -/
theorem hermiteJet_bijective_of_pairwise_isUnit_sub : Bijective (hermiteJet a m) :=
  _root_.funext (hermiteJetEquiv_apply ha m) ▸ (hermiteJetEquiv ha m).bijective

/-- The Hermite interpolation polynomial of the jet datum `c` has the Hasse jets `c`. -/
@[simp]
theorem eval_hasseDeriv_hermiteJetEquiv_symm (c : ∀ i, Fin (m i) → R) (i : ι) (k : Fin (m i)) :
    (hasseDeriv k ((hermiteJetEquiv ha m).symm c : R[X])).eval (a i) = c i k := by
  have := congr_fun (congr_fun ((hermiteJetEquiv ha m).apply_symm_apply c) i) k
  rwa [hermiteJetEquiv_apply, hermiteJet_apply, hasseJet_apply] at this

/-- The Hermite interpolation polynomial of a jet datum has degree below `∑ i, m i`. -/
theorem degree_hermiteJetEquiv_symm_lt (c : ∀ i, Fin (m i) → R) :
    ((hermiteJetEquiv ha m).symm c : R[X]).degree < ∑ i, m i := by
  simpa using mem_degreeLT.1 ((hermiteJetEquiv ha m).symm c).property

/-- The characteristic property of Hermite interpolation: the interpolation polynomial of the jet
datum `c` is the unique polynomial of degree below `∑ i, m i` whose Hasse jet of order `k < m i`
at `a i` is `c i k`. -/
theorem eq_hermiteJetEquiv_symm_iff {f : R[X]} {c : ∀ i, Fin (m i) → R} :
    f = (hermiteJetEquiv ha m).symm c ↔
      f.degree < ∑ i, m i ∧ ∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = c i k := by
  refine ⟨?_, fun ⟨hf, hc⟩ => ?_⟩
  · rintro rfl
    exact ⟨degree_hermiteJetEquiv_symm_lt ha m c, eval_hasseDeriv_hermiteJetEquiv_symm ha m c⟩
  · have hf' : f ∈ degreeLT R (∑ i, m i) := mem_degreeLT.2 (by simpa using hf)
    rw [← Subtype.coe_mk f hf', Subtype.coe_inj, LinearEquiv.eq_symm_apply]
    ext i k
    simpa using hc i k

/-- Every jet datum has a unique interpolating polynomial of degree below `∑ i, m i`, when the
differences of the nodes are units. -/
theorem existsUnique_hermite_interpolation_of_pairwise_isUnit_sub (c : ∀ i, Fin (m i) → R) :
    ∃! f : R[X], f.degree < ∑ i, m i ∧
      ∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = c i k :=
  ⟨(hermiteJetEquiv ha m).symm c, (eq_hermiteJetEquiv_symm_iff ha m).1 rfl,
    fun _ h => (eq_hermiteJetEquiv_symm_iff ha m).2 h⟩

/-- Hermite interpolation commutes with ring homomorphisms: the interpolation polynomial of the
image of a jet datum at the image nodes is the image of the interpolation polynomial. In
particular, for a field extension, the interpolation polynomial of data in the smaller field has
coefficients there. -/
theorem map_hermiteJetEquiv_symm [CommRing S] (ψ : R →+* S) (c : ∀ i, Fin (m i) → R) :
    ((hermiteJetEquiv ha m).symm c : R[X]).map ψ =
      (hermiteJetEquiv (a := fun i => ψ (a i)) (fun _ _ hij => by simpa using (ha hij).map ψ)
        m).symm fun i k => ψ (c i k) := by
  refine (eq_hermiteJetEquiv_symm_iff _ m).2
    ⟨degree_map_le.trans_lt (degree_hermiteJetEquiv_symm_lt ha m c), fun i k => ?_⟩
  rw [hasseDeriv_map, eval_map, eval₂_hom, eval_hasseDeriv_hermiteJetEquiv_symm]

/-- The Hermite basis of the polynomials of degree below `∑ i, m i`, when the differences of the
nodes are units: the basis whose coordinates are the Hasse jets `(hasseDeriv k f).eval (a i)`. -/
noncomputable def hermiteBasis : Module.Basis (Σ i, Fin (m i)) R (degreeLT R (∑ i, m i)) :=
  (Pi.basis fun i => Pi.basisFun R (Fin (m i))).map (hermiteJetEquiv ha m).symm

/-- Each Hermite basis polynomial interpolates a standard basis vector of the jet space. -/
theorem hermiteBasis_apply [DecidableEq ι] (x : Σ i, Fin (m i)) :
    hermiteBasis ha m x = (hermiteJetEquiv ha m).symm (Pi.single x.1 (Pi.single x.2 1)) := by
  simp only [hermiteBasis, Module.Basis.map_apply, Pi.basis_apply, Pi.basisFun_apply]

@[simp]
theorem hermiteBasis_repr (f : degreeLT R (∑ i, m i)) (x : Σ i, Fin (m i)) :
    (hermiteBasis ha m).repr f x = (hasseDeriv x.2 (f : R[X])).eval (a x.1) := by
  simp [hermiteBasis]

/-- The Hermite basis vector `b_{i, k}` has jet `1` at `(i, k)` and `0` elsewhere. -/
@[simp]
theorem hasseJet_hermiteBasis [DecidableEq ι] (x : Σ i, Fin (m i)) :
    hasseJet a m (hermiteBasis ha m x : R[X]) =
      Pi.single (M := fun i => Fin (m i) → R) x.1 (Pi.single x.2 1) := by
  rw [hermiteBasis_apply, hasseJet_hermiteJetEquiv_symm]

/-- The pointwise Hasse jets of the Hermite basis polynomials are the Kronecker deltas. -/
@[simp]
theorem eval_hasseDeriv_hermiteBasis [DecidableEq ι] (x : Σ i, Fin (m i)) (j : ι)
    (l : Fin (m j)) :
    (hasseDeriv l (hermiteBasis ha m x : R[X])).eval (a j) =
      if x = ⟨j, l⟩ then 1 else 0 := by
  rw [← hermiteBasis_repr ha m _ ⟨j, l⟩, Module.Basis.repr_self, Finsupp.single_apply]

/-- Every polynomial of degree below `∑ i, m i` is the combination of the Hermite basis with its
Hasse jets at the nodes as coefficients. -/
theorem sum_eval_hasseDeriv_smul_hermiteBasis {f : R[X]} (hf : f.degree < ∑ i, m i) :
    ∑ x : Σ i, Fin (m i), (hasseDeriv x.2 f).eval (a x.1) • (hermiteBasis ha m x : R[X]) = f := by
  have hf' : f ∈ degreeLT R (∑ i, m i) := mem_degreeLT.2 (by simpa using hf)
  simpa using congr_arg Subtype.val ((hermiteBasis ha m).sum_repr ⟨f, hf'⟩)

/-- Hermite interpolation with ordinary derivatives over a commutative ring: when the differences
of the nodes are units and `k !` is a unit for every order `k < m i` that occurs, the
ordinary-derivative Hermite jet map on polynomials of degree below `∑ i, m i` is bijective. -/
theorem ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    Bijective (ordinaryHermiteJet a m) := by
  let e : (∀ i, Fin (m i) → R) ≃ₗ[R] ∀ i, Fin (m i) → R :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfUnit (hm i k k.isLt).unit
  have h : ⇑(ordinaryHermiteJet a m) = e ∘ hermiteJet a m := by
    ext f i k
    rw [Function.comp_apply, ordinaryHermiteJet_eq_factorial_mul]
    simp [e, LinearEquiv.smulOfUnit, Units.smul_def]
  rw [h]
  exact e.bijective.comp (hermiteJet_bijective_of_pairwise_isUnit_sub ha m)

end CommRing

section ConfluentVandermonde

variable [CommRing R]

section Fin

variable {r : ℕ} {a : Fin r → R}

/-- The change-of-basis matrix expressing the monomial basis in the Hermite basis has rows indexed
by `finSigmaFinEquiv` from `Matrix.confluentVandermonde a m`. -/
@[simp]
theorem hermiteBasis_toMatrix_degreeLT_basis
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : Fin r → ℕ) :
    (hermiteBasis ha m).toMatrix (degreeLT.basis R (∑ i, m i)) =
      (Matrix.confluentVandermonde a m).submatrix finSigmaFinEquiv id := by
  ext ⟨i, k⟩ j
  simp [Module.Basis.toMatrix_apply, ← monomial_one_right_eq_X_pow, hasseDeriv_monomial]

/-- The change-of-basis matrix expressing the monomial basis in the lexicographically ordered
Hermite basis is `Matrix.confluentVandermonde a m`. -/
theorem hermiteBasis_reindex_toMatrix_degreeLT_basis
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : Fin r → ℕ) :
    ((hermiteBasis ha m).reindex finSigmaFinEquiv).toMatrix (degreeLT.basis R (∑ i, m i)) =
      Matrix.confluentVandermonde a m := by
  ext ρ j
  simp

/-- The change-of-basis matrix expressing the lexicographically ordered Hermite basis in the
monomial basis is `(Matrix.confluentVandermonde a m)⁻¹`. -/
theorem degreeLT_basis_toMatrix_hermiteBasis_reindex
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : Fin r → ℕ) :
    (degreeLT.basis R (∑ i, m i)).toMatrix ((hermiteBasis ha m).reindex finSigmaFinEquiv) =
      (Matrix.confluentVandermonde a m)⁻¹ := by
  have h := ((hermiteBasis ha m).reindex finSigmaFinEquiv).toMatrix_mul_toMatrix_flip
    (degreeLT.basis R (∑ i, m i))
  rw [hermiteBasis_reindex_toMatrix_degreeLT_basis] at h
  exact (Matrix.inv_eq_right_inv h).symm

/-- The change-of-basis matrix expressing the Hermite basis in the monomial basis has columns
indexed by `finSigmaFinEquiv` from `(Matrix.confluentVandermonde a m)⁻¹`. -/
@[simp]
theorem degreeLT_basis_toMatrix_hermiteBasis
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : Fin r → ℕ) :
    (degreeLT.basis R (∑ i, m i)).toMatrix (hermiteBasis ha m) =
      (Matrix.confluentVandermonde a m)⁻¹.submatrix id finSigmaFinEquiv := by
  rw [← degreeLT_basis_toMatrix_hermiteBasis_reindex ha m]
  ext j x
  simp [Module.Basis.toMatrix_apply]

/-- For `j < ∑ i, m i`, the `j`-th coefficient of the Hermite basis polynomial
`hermiteBasis ha m x` is the `(j, finSigmaFinEquiv x)` entry of
`(Matrix.confluentVandermonde a m)⁻¹`. -/
theorem coeff_hermiteBasis (ha : Pairwise fun i j => IsUnit (a i - a j))
    (m : Fin r → ℕ) (x : (i : Fin r) × Fin (m i)) (j : Fin (∑ i, m i)) :
    (hermiteBasis ha m x : R[X]).coeff j =
      (Matrix.confluentVandermonde a m)⁻¹ j (finSigmaFinEquiv x) := by
  rw [← degreeLT_basis_toMatrix_hermiteBasis_reindex ha m, Module.Basis.toMatrix_apply,
    Module.Basis.reindex_apply, Equiv.symm_apply_apply, degreeLT.basis_repr]

/-- The matrix of the Hermite interpolation operator `(hermiteJetEquiv ha m).symm` from the
lexicographically ordered standard jet basis to the monomial basis is
`(Matrix.confluentVandermonde a m)⁻¹`. -/
@[simp]
theorem toMatrix_hermiteJetEquiv_symm
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : Fin r → ℕ) :
    LinearMap.toMatrix (TauCeti.lexJetBasis R m) (degreeLT.basis R (∑ i, m i))
      (hermiteJetEquiv ha m).symm.toLinearMap =
      (Matrix.confluentVandermonde a m)⁻¹ := by
  rw [← degreeLT_basis_toMatrix_hermiteBasis_reindex ha m]
  ext j ρ
  simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply, hermiteBasis]

/-- Multiplying a jet vector by `(Matrix.confluentVandermonde a m)⁻¹` computes the coefficient
vector of its Hermite interpolation polynomial. -/
theorem confluentVandermonde_inv_mulVec
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : Fin r → ℕ)
    (c : ∀ i, Fin (m i) → R) :
    (Matrix.confluentVandermonde a m)⁻¹ *ᵥ
        (fun ρ => c (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2) =
      degreeLTEquiv R (∑ i, m i) ((hermiteJetEquiv ha m).symm c) := by
  have h := LinearMap.toMatrix_mulVec_repr (TauCeti.lexJetBasis R m) (degreeLT.basis R (∑ i, m i))
    (hermiteJetEquiv ha m).symm.toLinearMap c
  have hc : ⇑((TauCeti.lexJetBasis R m).repr c) =
      fun ρ => c (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 :=
    _root_.funext (TauCeti.lexJetBasis_repr m c)
  rw [toMatrix_hermiteJetEquiv_symm, hc] at h
  exact h.trans (_root_.funext fun j => degreeLT.basis_repr j _)

/-- The Hermite jet map is bijective iff the confluent Vandermonde determinant is a unit. -/
theorem hermiteJet_bijective_iff_isUnit_det (a : Fin r → R) (m : Fin r → ℕ) :
    Bijective (hermiteJet a m) ↔ IsUnit (Matrix.confluentVandermonde a m).det := by
  rw [← toMatrix_hermiteJet]
  exact (LinearMap.isUnit_det_toMatrix_iff_bijective _ _ _).symm

end Fin

variable [Fintype ι]

/-- **Exact characterization of Hermite interpolation over a commutative ring.** The Hermite jet
map `hermiteJet a m` is bijective if and only if `a i - a j` is a unit whenever `i ≠ j` and both
`m i` and `m j` are nonzero. Unlike `hermiteJet_bijective_of_pairwise_isUnit_sub`, this includes
the converse and allows repeated nodes of multiplicity `0`. -/
theorem hermiteJet_bijective_iff {a : ι → R} {m : ι → ℕ} :
    Bijective (hermiteJet a m) ↔
      ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  let e := Fintype.equivFin ι
  let d := e.symm
  let eL := LinearEquiv.ofEq _ _ (congr_arg (degreeLT R) (d.sum_comp m))
  let eR := Equiv.piCongrLeft' (fun i => Fin (m i) → R) e
  have hcomp : (hermiteJet (a ∘ d) (m ∘ d) :
      degreeLT R (∑ j, (m ∘ d) j) → ∀ j, Fin ((m ∘ d) j) → R) =
      eR ∘ hermiteJet a m ∘ eL := by
    ext f j k
    simp [eR, eL, d]
  rw [← EquivLike.bijective_comp eL, ← EquivLike.comp_bijective _ eR, ← hcomp,
    hermiteJet_bijective_iff_isUnit_det, Matrix.isUnit_det_confluentVandermonde_iff]
  exact ⟨fun h i j hij hi hj => by
      simpa [d] using h (e i) (e j) (e.injective.ne hij) (by simpa [d] using hi)
        (by simpa [d] using hj),
    fun h i j hij => h (d i) (d j) (d.injective.ne hij)⟩

/-- **Exact characterization of ordinary-derivative Hermite interpolation over a commutative
ring.** The ordinary-derivative Hermite jet map `ordinaryHermiteJet a m` is bijective if and only if
`k !` is a unit for every order `k < m i` that occurs and `a i - a j` is a unit whenever `i ≠ j` and
both `m i` and `m j` are nonzero. -/
theorem ordinaryHermiteJet_bijective_iff {a : ι → R} {m : ι → ℕ} :
    Bijective (ordinaryHermiteJet a m) ↔
      (∀ i, ∀ k < m i, IsUnit (k ! : R)) ∧
        ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  let S : (∀ i, Fin (m i) → R) → ∀ i, Fin (m i) → R :=
    Pi.map fun i => Pi.map fun (k : Fin (m i)) => (((k : ℕ) ! : R) * ·)
  have hcomp : ⇑(ordinaryHermiteJet a m) = S ∘ hermiteJet a m := by
    ext f i k
    rw [ordinaryHermiteJet_eq_factorial_mul]
    rfl
  have hS (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) : Bijective S :=
    .piMap fun i => .piMap fun k => IsUnit.isUnit_iff_mulLeft_bijective.1 (hm i k k.isLt)
  rw [hcomp]
  refine ⟨fun h => ?_, fun ⟨hm, ha⟩ => (hS hm).comp (hermiteJet_bijective_iff.2 ha)⟩
  have hm : ∀ i, ∀ k < m i, IsUnit (k ! : R) := by
    obtain ⟨c, hc⟩ := h.surjective.of_comp (fun _ _ => 1)
    exact fun i k hk => IsUnit.of_mul_eq_one (c i ⟨k, hk⟩) (congr_fun (congr_fun hc i) ⟨k, hk⟩)
  exact ⟨hm, hermiteJet_bijective_iff.1 (((hS hm).of_comp_iff' _).1 h)⟩

end ConfluentVandermonde

section NoZeroDivisors

variable [CommRing R] [NoZeroDivisors R] [Fintype ι] {a : ι → R}

/-- **The kernel of the jet map** over a commutative ring without zero divisors: for injective
nodes, the Hasse jets of `f` of the orders `k < m i` at the nodes `a i` all vanish iff
`∏ i, (X - a i) ^ m i` divides `f`. -/
theorem all_jets_vanish_iff_dvd (ha : Injective a) (m : ι → ℕ) (f : R[X]) :
    (∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = 0) ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f := by
  nontriviality R
  let ψ := algebraMap R (FractionRing R)
  have hψ : Injective ψ := IsFractionRing.injective R (FractionRing R)
  rw [← map_dvd_map ψ hψ (monic_prod_X_sub_C_pow univ a m)]
  simp only [Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  rw [← all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub (a := fun i => ψ (a i))
    (fun _ _ hij => (sub_ne_zero.2 ((hψ.comp ha).ne hij)).isUnit) m]
  simp only [hasseDeriv_map, eval_map, eval₂_hom, map_eq_zero_iff _ hψ]

/-- Over a commutative ring without zero divisors, for injective nodes, the Hasse jets of `f`
vanish iff `∏ i, (X - C (a i)) ^ m i` divides `f`. -/
theorem hasseJet_eq_zero_iff (ha : Injective a) (m : ι → ℕ) (f : R[X]) :
    hasseJet a m f = 0 ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f := by
  rw [← all_jets_vanish_iff_dvd ha m f]
  simp [funext_iff]

/-- Over a commutative ring without zero divisors, for injective nodes, the kernel of the Hasse
jet map is the ideal generated by `∏ i, (X - a i) ^ m i`. -/
theorem ker_hasseJet (ha : Injective a) (m : ι → ℕ) :
    LinearMap.ker (hasseJet a m) = (Ideal.span {∏ i, (X - C (a i)) ^ m i}).restrictScalars R := by
  ext f
  simp [Ideal.mem_span_singleton, hasseJet_eq_zero_iff ha m f]

/-- Over a commutative ring without zero divisors, for injective nodes, a polynomial of degree
below `∑ i, m i` is determined by its Hasse jets of the orders `k < m i` at the nodes `a i`, even
when the node differences are not units. -/
theorem hermiteJet_injective (ha : Injective a) (m : ι → ℕ) : Injective (hermiteJet a m) := by
  nontriviality R
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  have hdvd : (∏ i, (X - C (a i)) ^ m i) ∣ (f : R[X]) :=
    (all_jets_vanish_iff_dvd ha m f).1 fun i k => by simpa using congr_fun (congr_fun hf i) k
  refine Subtype.ext (eq_zero_of_dvd_of_degree_lt hdvd ?_)
  rw [degree_eq_natDegree (monic_prod_X_sub_C_pow univ a m).ne_zero, natDegree_prod_X_sub_C_pow]
  exact mem_degreeLT.1 f.property

/-- Over a commutative ring without zero divisors, for injective nodes, the ordinary-derivative
Hermite jet map is injective when `k ! ≠ 0` in `R` for every order `k < m i`. -/
theorem ordinaryHermiteJet_injective (ha : Injective a) (m : ι → ℕ)
    (hm : ∀ i, ∀ k < m i, (k ! : R) ≠ 0) : Injective (ordinaryHermiteJet a m) := by
  have hcomp : ⇑(ordinaryHermiteJet a m) =
      Pi.map (fun i => Pi.map fun (k : Fin (m i)) => (((k : ℕ) ! : R) * ·)) ∘ hermiteJet a m := by
    ext f i k
    rw [ordinaryHermiteJet_eq_factorial_mul]
    rfl
  rw [hcomp]
  exact (Injective.piMap fun i => Injective.piMap fun (k : Fin (m i)) =>
    mul_right_injective₀ (hm i k k.isLt)).comp (hermiteJet_injective ha m)

omit [NoZeroDivisors R] [Fintype ι] in
private noncomputable def hasseJetSubtypeEquiv (m : ι → ℕ) :
    (∀ i, Fin (m i) → R) ≃ₗ[R] (∀ i : {i // m i ≠ 0}, Fin (m i.val) → R) where
  toFun y i := y i.val
  invFun z i := if hi : m i ≠ 0 then z ⟨i, hi⟩ else fun k => Fin.elim0 (k.cast (not_ne_iff.1 hi))
  left_inv y := by
    ext i k
    have hi : m i ≠ 0 := by
      have := k.isLt
      omega
    simp [hi]
  right_inv z := by
    ext i k
    simp [i.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NoZeroDivisors R] [Fintype ι] in
private theorem hasseJetSubtypeEquiv_hasseJet (a : ι → R) (m : ι → ℕ) (f : R[X]) :
    hasseJetSubtypeEquiv m (hasseJet a m f) =
      hasseJet (fun i : {i // m i ≠ 0} => a i.val) (fun i => m i.val) f :=
  rfl

omit [CommRing R] [NoZeroDivisors R] in
private theorem sum_nonzero_multiplicity (m : ι → ℕ) :
    ∑ i : {i // m i ≠ 0}, m i.val = ∑ i, m i := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => m i ≠ 0) m
  have hzero : ∑ i : {x : ι // ¬ m x ≠ 0}, m i.val = 0 :=
    Finset.sum_eq_zero fun i _ => not_ne_iff.1 i.property
  rwa [hzero, add_zero] at h

omit [CommRing R] [NoZeroDivisors R] [Fintype ι] in
private theorem injective_on_nonzero {m : ι → ℕ} (ha : Set.InjOn a {i | m i ≠ 0}) :
    Injective (fun i : {i // m i ≠ 0} => a i.val) :=
  fun i j hij => Subtype.ext (ha i.property j.property hij)

/-- Over a commutative ring without zero divisors, when `a` is injective on the nodes of nonzero
multiplicity, the Hasse jets of `f` vanish iff `∏ i, (X - C (a i)) ^ m i` divides `f`. -/
theorem hasseJet_eq_zero_iff_of_injOn (m : ι → ℕ) (ha : Set.InjOn a {i | m i ≠ 0})
    (f : R[X]) :
    hasseJet a m f = 0 ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f := by
  classical
  have hprod : ∏ i : {i // m i ≠ 0}, (X - C (a i.val)) ^ m i.val = ∏ i, (X - C (a i)) ^ m i := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun i => m i ≠ 0)
      (fun i => (X - C (a i)) ^ m i)
    have hone : ∏ i : {x : ι // ¬ m x ≠ 0}, (X - C (a i.val)) ^ m i.val = 1 :=
      Finset.prod_eq_one fun i _ => by simp [not_ne_iff.1 i.property]
    rwa [hone, mul_one] at h
  rw [← (hasseJetSubtypeEquiv m).map_eq_zero_iff, hasseJetSubtypeEquiv_hasseJet,
    hasseJet_eq_zero_iff (injective_on_nonzero ha), hprod]

/-- Over a commutative ring without zero divisors, `hermiteJet a m` is injective when the nodes of
nonzero multiplicity are pairwise distinct. -/
theorem hermiteJet_injective_of_injOn (m : ι → ℕ) (ha : Set.InjOn a {i | m i ≠ 0}) :
    Injective (hermiteJet a m) := by
  let eDeg : degreeLT R (∑ i : {i // m i ≠ 0}, m i.val) ≃ₗ[R] degreeLT R (∑ i, m i) :=
    LinearEquiv.ofEq _ _ (congrArg (degreeLT R) (sum_nonzero_multiplicity m))
  have hcomp :
      (hasseJetSubtypeEquiv m).toLinearMap ∘ₗ hermiteJet a m ∘ₗ eDeg.toLinearMap =
        hermiteJet (fun i : {i // m i ≠ 0} => a i.val) (fun i => m i.val) := by
    ext f i k
    simp [hasseJetSubtypeEquiv, eDeg]
  have hinj : Injective
      ((hasseJetSubtypeEquiv m).toLinearMap ∘ₗ hermiteJet a m ∘ₗ eDeg.toLinearMap) := by
    rw [hcomp]
    exact hermiteJet_injective (injective_on_nonzero ha) _
  intro x y h
  have hxy : eDeg.symm x = eDeg.symm y := hinj (by simp [LinearMap.comp_apply, h])
  simpa using congrArg eDeg hxy

end NoZeroDivisors

section IsDomain

variable [CommRing R] [IsDomain R] [Fintype ι] {a : ι → R}

/-- Over an integral domain, when nodes of nonzero multiplicity are pairwise distinct and
`∑ i, m i ≤ N`, the range of `hasseJet a m` on polynomials of degree below `N` equals the range of
`hermiteJet a m`. -/
theorem range_hasseJet_comp_degreeLT_eq_range_hermiteJet (m : ι → ℕ)
    (ha : Set.InjOn a {i | m i ≠ 0}) {N : ℕ} (hge : ∑ i, m i ≤ N) :
    LinearMap.range ((hasseJet a m).comp (degreeLT R N).subtype) =
      LinearMap.range (hermiteJet a m) := by
  classical
  let P : R[X] := ∏ i, (X - C (a i)) ^ m i
  have hP_monic : P.Monic := monic_prod_X_sub_C_pow univ a m
  have hP_deg : P.natDegree = ∑ i, m i := natDegree_prod_X_sub_C_pow univ a m
  refine le_antisymm ?_ ?_
  · -- Reduce modulo `P`: the remainder has degree below `∑ i, m i` and the same Hasse jets.
    rintro _ ⟨f, rfl⟩
    have hrem : (f : R[X]) %ₘ P ∈ degreeLT R (∑ i, m i) :=
      hP_deg ▸ modByMonic_mem_degreeLT hP_monic (f : R[X])
    refine ⟨⟨(f : R[X]) %ₘ P, hrem⟩, ?_⟩
    rw [LinearMap.comp_apply, Submodule.coe_subtype, hermiteJet_apply]
    have hdiff : hasseJet a m (P * ((f : R[X]) /ₘ P)) = 0 :=
      (hasseJet_eq_zero_iff_of_injOn m ha _).2 (dvd_mul_right _ _)
    have hadd := congrArg (hasseJet a m) (modByMonic_add_div (f : R[X]) P)
    simpa [map_add, hdiff] using hadd
  · have hcomp : ((hasseJet a m).comp (degreeLT R N).subtype).comp
        (Submodule.inclusion (degreeLT_mono hge)) = hermiteJet a m := by
      ext f i r
      simp
    rw [← hcomp]
    exact LinearMap.range_comp_le_range _ _

/-- Over an integral domain, when nodes of nonzero multiplicity are pairwise distinct, the image of
`hasseJet a m` on polynomials of degree below `N` has dimension `min N (∑ i, m i)`. -/
theorem finrank_range_hermiteJet_degreeLT (m : ι → ℕ) (ha : Set.InjOn a {i | m i ≠ 0}) (N : ℕ) :
    Module.finrank R (LinearMap.range ((hasseJet a m).comp (degreeLT R N).subtype)) =
      min N (∑ i, m i) := by
  classical
  let L : degreeLT R N →ₗ[R] ∀ i, Fin (m i) → R := (hasseJet a m).comp (degreeLT R N).subtype
  rcases le_total N (∑ i, m i) with hle | hge
  · -- When `N ≤ ∑ i, m i`, `degreeLT R N` embeds into `degreeLT R (∑ i, m i)`, so `L` is
    -- injective because `hermiteJet a m` is.
    have hcomp : L = (hermiteJet a m).comp (Submodule.inclusion (degreeLT_mono hle)) := by
      ext f i r
      simp [L]
    have hinj : Injective L := by
      rw [hcomp]
      exact (hermiteJet_injective_of_injOn m ha).comp (Submodule.inclusion_injective _)
    rw [min_eq_left hle, LinearMap.finrank_range_of_inj hinj, Polynomial.finrank_degreeLT]
  · -- When `∑ i, m i ≤ N`, reducing modulo `∏_{m i ≠ 0} (X - aᵢ)^{mᵢ}` identifies the range of
    -- `L` with the range of `hermiteJet a m`.
    rw [min_eq_right hge, range_hasseJet_comp_degreeLT_eq_range_hermiteJet m ha hge,
      LinearMap.finrank_range_of_inj (hermiteJet_injective_of_injOn m ha),
      Polynomial.finrank_degreeLT]

end IsDomain

section Field

variable [Field K] [Fintype ι] {a : ι → K}

/-- **Hermite interpolation** over a field: for injective nodes and arbitrary multiplicities, the
Hermite jet map on the polynomials of degree below `∑ i, m i` is bijective. -/
theorem hermiteJet_bijective (ha : Injective a) (m : ι → ℕ) : Bijective (hermiteJet a m) :=
  hermiteJet_bijective_of_pairwise_isUnit_sub
    (fun _ _ hij => (sub_ne_zero.2 (ha.ne hij)).isUnit) m

/-- **Exact characterization of Hermite interpolation over a field.** The Hermite jet map
`hermiteJet a m` is bijective if and only if `a i ≠ a j` whenever `i ≠ j` and both `m i` and `m j`
are nonzero. -/
theorem hermiteJet_bijective_iff_ne {m : ι → ℕ} :
    Bijective (hermiteJet a m) ↔
      ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  simp only [hermiteJet_bijective_iff, isUnit_iff_ne_zero, sub_ne_zero]

/-- **Exact characterization of ordinary-derivative Hermite interpolation over a field.**
The ordinary-derivative Hermite jet map `ordinaryHermiteJet a m` is bijective if and only if
`(k ! : K) ≠ 0` for every order `k < m i` that occurs and `a i ≠ a j` whenever `i ≠ j` and
both `m i` and `m j` are nonzero. -/
theorem ordinaryHermiteJet_bijective_iff_ne {m : ι → ℕ} :
    Bijective (ordinaryHermiteJet a m) ↔
      (∀ i, ∀ k < m i, (k ! : K) ≠ 0) ∧
        ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  simp only [ordinaryHermiteJet_bijective_iff, isUnit_iff_ne_zero, sub_ne_zero]

/-- Over a field of characteristic zero, the ordinary-derivative Hermite jet map is bijective if
and only if `a i ≠ a j` whenever `i ≠ j` and both `m i` and `m j` are nonzero. -/
theorem ordinaryHermiteJet_bijective_iff_of_charZero [CharZero K] {m : ι → ℕ} :
    Bijective (ordinaryHermiteJet a m) ↔
      ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  simp [ordinaryHermiteJet_bijective_iff_ne, Nat.factorial_ne_zero]

/-- Over a field with injective nodes, every jet datum has a unique interpolating polynomial of
degree below `∑ i, m i`. -/
theorem existsUnique_hermite_interpolation (ha : Injective a) (m : ι → ℕ)
    (c : ∀ i, Fin (m i) → K) :
    ∃! f : K[X], f.degree < ∑ i, m i ∧
      ∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = c i k :=
  existsUnique_hermite_interpolation_of_pairwise_isUnit_sub
    (fun _ _ hij => (sub_ne_zero.2 (ha.ne hij)).isUnit) m c

/-- Hermite interpolation with ordinary derivatives over a field: for injective nodes, when every
`k !` with `k < m i` is a unit, the ordinary-derivative Hermite jet map is bijective. -/
theorem ordinaryHermiteJet_bijective (ha : Injective a) (m : ι → ℕ)
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : K)) : Bijective (ordinaryHermiteJet a m) :=
  ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub
    (fun _ _ hij => (sub_ne_zero.2 (ha.ne hij)).isUnit) m hm

end Field

/-! ### Checks -/

section Checks

/-- At integer nodes `0, 1` with multiplicities `(2, 1)`, the jet datum
`f(0) = 1, f'(0) = 0, f(1) = 0` has the unique solution `1 - X ^ 2` of degree below `3`. -/
example : ((hermiteJetEquiv (a := ![(0 : ℤ), 1])
      (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all) ![2, 1]).symm
      (fun i k => if (i : ℕ) = 0 ∧ (k : ℕ) = 0 then 1 else 0) : ℤ[X]) = 1 - X ^ 2 := by
  symm
  refine (eq_hermiteJetEquiv_symm_iff _ ![2, 1]).2 ⟨(degree_sub_le _ _).trans_lt ?_, fun i k => ?_⟩
  · rw [Fin.sum_univ_two]
    exact max_lt (by simp) ((degree_X_pow_le 2).trans_lt (by decide))
  · fin_cases i <;> fin_cases k <;> simp [hasseDeriv_one]

/-- The matrix of the Hermite jet map at the double node `0` and the simple node `1`. -/
example : LinearMap.toMatrix (degreeLT.basis ℤ (∑ i, ![2, 1] i)) (TauCeti.lexJetBasis ℤ ![2, 1])
    (hermiteJet ![(0 : ℤ), 1] ![2, 1]) = !![1, 0, 0; 0, 1, 0; 1, 1, 1] := by
  rw [toMatrix_hermiteJet]
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [Matrix.confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

/-- The nodes `(1, 0)` give the matrix `[[1, 1], [1, 0]]`, whose determinant `-1` pins the sign. -/
example : LinearMap.toMatrix (degreeLT.basis ℤ (∑ i, ![1, 1] i)) (TauCeti.lexJetBasis ℤ ![1, 1])
    (hermiteJet ![(1 : ℤ), 0] ![1, 1]) = !![1, 1; 1, 0] := by
  rw [toMatrix_hermiteJet]
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [Matrix.confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

/-- A repeated node of multiplicity `0` does not obstruct Hermite interpolation: `a = ![0, 0, 1]`
is not injective, yet `hermiteJet ![(0 : ℤ), 0, 1] ![1, 0, 1]` is bijective. -/
example : ¬ Injective ![(0 : ℤ), 0, 1] ∧
    Bijective (hermiteJet ![(0 : ℤ), 0, 1] ![1, 0, 1]) := by
  refine ⟨fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide), ?_⟩
  rw [hermiteJet_bijective_iff]
  intro i j hij hi hj
  fin_cases i <;> fin_cases j <;> simp_all

/-- Over `ℤ`, distinct nodes whose difference is not `±1` give a non-bijective Hermite jet map,
while over `ℚ` the same nodes give a bijection. -/
example : ¬ Bijective (hermiteJet ![(0 : ℤ), 2] ![1, 1]) ∧
    Bijective (hermiteJet ![(0 : ℚ), 2] ![1, 1]) := by
  refine ⟨?_, (hermiteJet_bijective_iff_ne (a := ![(0 : ℚ), 2]) (m := ![1, 1])).2 (by decide)⟩
  rw [hermiteJet_bijective_iff]
  intro h
  simpa using Int.isUnit_eq_one_or (h 1 0 (by decide) (by decide) (by decide))

/-- In prime characteristic `p`, at a single node `c` of multiplicity `p + 1`, the Hasse Hermite
jet map is bijective while the ordinary-derivative jet map fails to be bijective because `p ! = 0`.
-/
example {p : ℕ} [Fact (Nat.Prime p)] [Field K] [CharP K p] (c : K) :
    Bijective (hermiteJet ![c] ![p + 1]) ∧
      ¬ Bijective (ordinaryHermiteJet ![c] ![p + 1]) := by
  refine ⟨hermiteJet_bijective (injective_of_subsingleton _) _, ?_⟩
  rw [ordinaryHermiteJet_bijective_iff_ne, not_and]
  intro h _
  exact h 0 p (by simp)
    ((CharP.cast_eq_zero_iff K p _).2 (Nat.dvd_factorial (Fact.out : Nat.Prime p).pos le_rfl))

/-- One node `c` of multiplicity `2`: `c₀ + c₁ X ↦ (c₀ + c₁ c, c₁)`. -/
example (c c₀ c₁ : ℚ) (h : C c₀ + C c₁ * X ∈ degreeLT ℚ (∑ i, ![2] i)) :
    hermiteJet ![c] ![2] ⟨_, h⟩ 0 ⟨0, by simp⟩ = c₀ + c₁ * c ∧
      hermiteJet ![c] ![2] ⟨_, h⟩ 0 ⟨1, by simp⟩ = c₁ := by
  simp only [hermiteJet_apply, hasseJet_apply]
  simp

/-- Simple nodes `0, 1`: `c₀ + c₁ X ↦ (c₀, c₀ + c₁)`, the values at the nodes. -/
example (c₀ c₁ : ℚ) (h : C c₀ + C c₁ * X ∈ degreeLT ℚ (∑ i, ![1, 1] i)) :
    hermiteJet ![0, 1] ![1, 1] ⟨_, h⟩ 0 ⟨0, by simp⟩ = c₀ ∧
      hermiteJet ![0, 1] ![1, 1] ⟨_, h⟩ 1 ⟨0, by simp⟩ = c₀ + c₁ := by
  simp only [hermiteJet_apply, hasseJet_apply]
  simp

/-- No nodes: the map from the zero space to the one-point space is bijective. -/
example : Bijective (hermiteJet (![] : Fin 0 → ℚ) ![]) :=
  hermiteJet_bijective (injective_of_subsingleton _) _

/-- A repeated node: `X ↦ (0, 0)`, so injectivity of the nodes is necessary. -/
example : ¬ Injective (hermiteJet ![(0 : ℚ), 0] ![1, 1]) := by
  intro h
  have hX : (X : ℚ[X]) ∈ degreeLT ℚ (∑ i, ![1, 1] i) := by
    simp [mem_degreeLT]
  refine X_ne_zero (congrArg Subtype.val (@h ⟨X, hX⟩ 0 ?_))
  ext i k
  rw [hermiteJet_apply, hasseJet_apply, map_zero, Pi.zero_apply, Pi.zero_apply]
  fin_cases i <;> fin_cases k <;> simp

/-- A node of multiplicity `0` contributes nothing: at `(5, 0)` with multiplicities `(0, 3)`, the
jets at `0` read off the coefficients of `c₀ + c₁ X + c₂ X²`. -/
example (c₀ c₁ c₂ : ℚ)
    (h : C c₀ + C c₁ * X + C c₂ * X ^ 2 ∈ degreeLT ℚ (∑ i, ![0, 3] i)) :
    hermiteJet ![5, 0] ![0, 3] ⟨_, h⟩ 1 ⟨0, by simp⟩ = c₀ ∧
      hermiteJet ![5, 0] ![0, 3] ⟨_, h⟩ 1 ⟨1, by simp⟩ = c₁ ∧
      hermiteJet ![5, 0] ![0, 3] ⟨_, h⟩ 1 ⟨2, by simp⟩ = c₂ := by
  rw [hermiteJet_apply, hasseJet_apply, hasseJet_apply, hasseJet_apply]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, ← taylor_coeff, taylor_zero']
  simp

/-- In characteristic `2` the ordinary jet of order `2` of `X²` at `0` vanishes, while the Hasse
jet is `1`. -/
example (h : (X ^ 2 : (ZMod 2)[X]) ∈ degreeLT (ZMod 2) (∑ i, ![3] i)) :
    ordinaryHermiteJet ![0] ![3] ⟨_, h⟩ 0 ⟨2, by simp⟩ = 0 ∧
      hermiteJet ![0] ![3] ⟨_, h⟩ 0 ⟨2, by simp⟩ = 1 := by
  refine ⟨?_, ?_⟩
  · rw [ordinaryHermiteJet_eq_factorial_mul]
    exact zero_mul _
  · rw [hermiteJet_apply, hasseJet_apply]
    simpa using eval_hasseDeriv_X_sub_C_pow (0 : ZMod 2) 2 2

/-- In characteristic `2` the ordinary jet map with one node of multiplicity `3` is not injective:
it kills `X²`, so the unit hypothesis on the factorials in
`ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub` is necessary. -/
example : ¬ Injective (ordinaryHermiteJet ![(0 : ZMod 2)] ![3]) := by
  intro h
  have hX : (X ^ 2 : (ZMod 2)[X]) ∈ degreeLT (ZMod 2) (∑ i, ![3] i) := by
    rw [mem_degreeLT]
    compute_degree!
  have h0 : (X ^ 2 : (ZMod 2)[X]) = 0 := by
    refine congrArg Subtype.val (@h ⟨_, hX⟩ 0 ?_)
    ext i k
    rw [ordinaryHermiteJet_apply, map_zero, Pi.zero_apply, Pi.zero_apply]
    fin_cases i
    fin_cases k <;> simp [CharTwo.add_self_eq_zero]
  have := congrArg (fun p : (ZMod 2)[X] => p.coeff 2) h0
  simp only [coeff_X_pow_self, coeff_zero] at this
  exact absurd this (by decide)

/-- `X² ∤ X`: the jet of order `1` of `X` at `0` is `1`. -/
example : ¬ (∏ i, (X - C (![(0 : ℚ)] i)) ^ ![2] i) ∣ X := by
  rw [← all_jets_vanish_iff_dvd (injective_of_subsingleton _)]
  intro h
  simpa [hasseDeriv_one'] using h 0 ⟨1, by simp⟩

/-- Worked example: `1 - X²` is the only polynomial of degree below `3` with `f(0) = 1`,
`f'(0) = 0` and `f(1) = 0`. -/
example (f : ℚ[X]) (hf : f ∈ degreeLT ℚ 3) (h₀ : f.eval 0 = 1) (h₁ : (derivative f).eval 0 = 0)
    (h₂ : f.eval 1 = 0) : f = 1 - X ^ 2 := by
  have hM : ∑ i, ![2, 1] i = 3 := rfl
  have hg : (1 - X ^ 2 : ℚ[X]) ∈ degreeLT ℚ (∑ i, ![2, 1] i) := by
    rw [hM, mem_degreeLT]
    compute_degree!
  refine congrArg Subtype.val ((hermiteJet_bijective (a := ![(0 : ℚ), 1]) (by decide) ![2, 1]).1
    (a₁ := ⟨f, hM ▸ hf⟩) (a₂ := ⟨_, hg⟩) ?_)
  ext i k
  simp only [hermiteJet_apply, hasseJet_apply]
  fin_cases i <;> fin_cases k <;> simp [h₀, h₁, h₂]

/-- `X (X - 1) ∣ X² - X` over `ℤ`. -/
example : (∏ i, (X - C (![(0 : ℤ), 1] i)) ^ ![1, 1] i) ∣ X ^ 2 - X := by
  rw [← all_jets_vanish_iff_dvd (by decide)]
  intro i k
  fin_cases i <;> fin_cases k <;> simp

/-- Worked example over `ℤ`: since `1 - 0 = 1` is a unit in `ℤ`, Hermite interpolation holds over
`ℤ` itself, and `1 - X²` is the unique polynomial of degree below `3` with `f(0) = 1`, `f'(0) = 0`,
and `f(1) = 0`. -/
example (f : ℤ[X]) (hf : f ∈ degreeLT ℤ 3) (h₀ : f.eval 0 = 1) (h₁ : (derivative f).eval 0 = 0)
    (h₂ : f.eval 1 = 0) : f = 1 - X ^ 2 := by
  have ha : Pairwise fun i j : Fin 2 => IsUnit (![(0 : ℤ), 1] i - ![(0 : ℤ), 1] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hM : ∑ i, ![2, 1] i = 3 := rfl
  have hg : (1 - X ^ 2 : ℤ[X]) ∈ degreeLT ℤ (∑ i, ![2, 1] i) := by
    rw [hM, mem_degreeLT]
    compute_degree!
  refine congrArg Subtype.val ((hermiteJet_bijective_of_pairwise_isUnit_sub ha ![2, 1]).1
    (a₁ := ⟨f, hM ▸ hf⟩) (a₂ := ⟨_, hg⟩) ?_)
  ext i k
  simp only [hermiteJet_apply, hasseJet_apply]
  fin_cases i <;> fin_cases k <;> simp [h₀, h₁, h₂]

/-- Over `ℤ`, the nodes `0, 2` give an injective Hermite jet map although `2 - 0` is not a unit
and the map is not bijective. -/
example : Injective (hermiteJet ![(0 : ℤ), 2] ![1, 1]) :=
  hermiteJet_injective (by decide) ![1, 1]

end Checks

end Polynomial
