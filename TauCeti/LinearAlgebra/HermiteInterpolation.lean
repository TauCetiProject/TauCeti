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
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Algebra.Polynomial.Taylor
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
degree below `M` is bijective (`AdjoinRoot.degreeLTEquiv`).

For nodes indexed by `Fin r`, the matrix of `Polynomial.hermiteJet a m` from the monomial basis
`Polynomial.degreeLT.basis R M` to the lexicographically ordered standard basis of the jet space is
`Matrix.confluentVandermonde a m` (`Polynomial.toMatrix_hermiteJet`), and the inverse matrix
`(Matrix.confluentVandermonde a m)⁻¹` represents the interpolation operator
`(Polynomial.hermiteJetEquiv ha m).symm` and lists the coefficients of `Polynomial.hermiteBasis`.
Combining this matrix identification with `Matrix.isUnit_det_confluentVandermonde_iff` gives the
exact `↔` characterizations of bijectivity for both Hasse and ordinary-derivative Hermite
interpolation over arbitrary commutative rings and fields (`Polynomial.hermiteJet_bijective_iff`,
`Polynomial.eval_iterate_derivative_bijective_iff`), allowing repeated nodes of multiplicity `0`.

## Main definitions

* `Polynomial.hasseJet a m`: the `R`-linear map `f ↦ ((hasseDeriv k f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteJet a m`: its restriction to `Polynomial.degreeLT R (∑ i, m i)`.
* `Polynomial.hermiteJetEquiv`: for nodes with unit differences, Hermite interpolation as a linear
  equivalence; its inverse sends a jet datum to its interpolation polynomial.
* `Polynomial.hermiteBasis`: the basis of `degreeLT R (∑ i, m i)` dual to the Hasse jets.

## Main results

* `Polynomial.all_jets_vanish_iff_dvd`: over a domain, for injective nodes, the jets of `f` all
  vanish iff `∏ i, (X - C (a i)) ^ m i ∣ f`; `all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub` is
  the form over a commutative ring.
* `Polynomial.hasseJetQuotientEquiv`: `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteJet_bijective`: over a field, for injective nodes, the Hermite jet map is
  bijective; `hermiteJet_bijective_of_pairwise_isUnit_sub` is the form over a commutative ring.
* `Polynomial.eq_hermiteJetEquiv_symm_iff`: the interpolation polynomial is the unique polynomial
  of degree below `∑ i, m i` with the prescribed jets.
* `Polynomial.map_hermiteJetEquiv_symm`: interpolation commutes with ring homomorphisms.
* `Polynomial.eval_iterate_derivative_bijective`: the same interpolation with ordinary
  derivatives, when the factorials `k !` with `k < m i` are units.
* `Polynomial.toMatrix_hermiteJet`, `Polynomial.toMatrix_hermiteJet_piBasis`,
  `Polynomial.toMatrix_hermiteJetEquiv_symm`, `Polynomial.hermiteBasis_toMatrix_degreeLT_basis`,
  and `Polynomial.degreeLT_basis_toMatrix_hermiteBasis`: `hermiteJet a m`,
  `(hermiteJetEquiv ha m).symm`, and `hermiteBasis ha m` in coordinates are
  `Matrix.confluentVandermonde a m` and its inverse.
* `Polynomial.hermiteJet_bijective_iff`, `Polynomial.hermiteJet_bijective_iff_ne`,
  `Polynomial.eval_iterate_derivative_bijective_iff`, and
  `Polynomial.eval_iterate_derivative_bijective_iff_ne`: exact `↔` characterizations of when Hasse
  and ordinary-derivative Hermite interpolation are bijective over commutative rings and fields.

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

namespace Polynomial

variable {ι R S K : Type*}

section Semiring

variable [Semiring R]

/-- The Hasse jet map at the nodes `a i` with multiplicities `m i`: the `R`-linear map sending a
polynomial `f` to its Hasse jets `(hasseDeriv k f).eval (a i)` of the orders `k < m i`. A node
with `m i = 0` contributes no coordinate. -/
noncomputable def hasseJet (a : ι → R) (m : ι → ℕ) : R[X] →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => LinearMap.pi fun k => leval (a i) ∘ₗ hasseDeriv (k : ℕ)

@[simp]
theorem hasseJet_apply (a : ι → R) (m : ι → ℕ) (f : R[X]) (i : ι) (k : Fin (m i)) :
    hasseJet a m f i k = (hasseDeriv k f).eval (a i) := by
  simp [hasseJet]

/-- Taking Hasse jets commutes with mapping the coefficients and nodes by a ring homomorphism. -/
theorem hasseJet_map [Semiring S] (ψ : R →+* S) (a : ι → R) (m : ι → ℕ) (f : R[X]) :
    hasseJet (fun i => ψ (a i)) m (f.map ψ) = fun i k => ψ (hasseJet a m f i k) := by
  ext i k
  simp only [hasseJet_apply, hasseDeriv_map, eval_map, eval₂_hom]

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
ordered standard basis of the jet space `∀ i : Fin r, Fin (m i) → R`, the matrix of
`hermiteJet a m` is `Matrix.confluentVandermonde a m`. -/
@[simp]
theorem toMatrix_hermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i))
      ((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv)
      (hermiteJet a m) =
      Matrix.confluentVandermonde a m := by
  ext ρ j
  simp [LinearMap.toMatrix_apply, Matrix.confluentVandermonde_apply, Pi.basis_repr,
    Pi.basisFun_repr]

/-- Multiplying the coefficient vector of `f ∈ degreeLT R (∑ i, m i)` by
`Matrix.confluentVandermonde a m` computes the Hasse jets of `f` in lexicographic order. -/
theorem confluentVandermonde_mulVec_degreeLTEquiv (a : Fin r → R) (m : Fin r → ℕ)
    (f : degreeLT R (∑ i, m i)) :
    Matrix.confluentVandermonde a m *ᵥ degreeLTEquiv R (∑ i, m i) f =
      fun ρ => hermiteJet a m f (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 := by
  have h := LinearMap.toMatrix_mulVec_repr (degreeLT.basis R (∑ i, m i))
    ((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv)
    (hermiteJet a m) f
  have hf : ⇑((degreeLT.basis R (∑ i, m i)).repr f) = degreeLTEquiv R (∑ i, m i) f :=
    _root_.funext fun j => degreeLT.basis_repr j f
  rw [toMatrix_hermiteJet, hf] at h
  ext ρ
  simpa [Pi.basis_repr, Pi.basisFun_repr] using congr_fun h ρ

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
  refine ⟨g, ?_⟩
  ext i k
  have h := X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.1
    (Ideal.mem_span_singleton.1 (hg i)) k k.2
  rw [map_sub, eval_sub, sub_eq_zero] at h
  simp [h, map_sum, eval_finsetSum, Fin.val_inj]

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
      ((dvd_prod_of_mem _ (mem_univ i)).trans h) k k.2⟩

variable (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : ι → ℕ)
include ha

/-- The kernel of the Hasse jet map is the ideal generated by `∏ i, (X - a i) ^ m i`, when the
differences of the nodes are units. -/
theorem ker_hasseJet :
    LinearMap.ker (hasseJet a m) = (Ideal.span {∏ i, (X - C (a i)) ^ m i}).restrictScalars R := by
  ext f
  simp [Ideal.mem_span_singleton, ← all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub ha m f,
    funext_iff]

/-- The jet space is the quotient of `R[X]` by `∏ i, (X - a i) ^ m i`, when the differences of
the nodes are units: the Hasse jet map identifies the two. -/
noncomputable def hasseJetQuotientEquiv :
    (R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃ₗ[R] ∀ i, Fin (m i) → R :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ker_hasseJet ha m).symm ≪≫ₗ
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
  simpa using mem_degreeLT.1 ((hermiteJetEquiv ha m).symm c).2

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

/-- The Hasse jets of the Hermite basis polynomials are the Kronecker deltas. -/
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
    LinearMap.toMatrix
      ((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv)
      (degreeLT.basis R (∑ i, m i)) (hermiteJetEquiv ha m).symm.toLinearMap =
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
  have h := LinearMap.toMatrix_mulVec_repr
    ((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv)
    (degreeLT.basis R (∑ i, m i)) (hermiteJetEquiv ha m).symm.toLinearMap c
  have hc : ⇑(((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv).repr c) =
      fun ρ => c (finSigmaFinEquiv.symm ρ).1 (finSigmaFinEquiv.symm ρ).2 := by
    ext ρ
    simp [Pi.basis_repr, Pi.basisFun_repr]
  rw [toMatrix_hermiteJetEquiv_symm, hc] at h
  exact h.trans (_root_.funext fun j => degreeLT.basis_repr j _)

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
    ← LinearMap.isUnit_det_toMatrix_iff_bijective (degreeLT.basis R (∑ j, (m ∘ d) j))
      ((Pi.basis fun j => Pi.basisFun R (Fin ((m ∘ d) j))).reindex finSigmaFinEquiv),
    toMatrix_hermiteJet, Matrix.isUnit_det_confluentVandermonde_iff]
  exact ⟨fun h i j hij hi hj => by
      simpa [d] using h (e i) (e j) (e.injective.ne hij) (by simpa [d] using hi)
        (by simpa [d] using hj),
    fun h i j hij => h (d i) (d j) (d.injective.ne hij)⟩

/-- **Exact characterization of ordinary-derivative Hermite interpolation over a commutative
ring.** Evaluating iterated ordinary derivatives `(derivative^[k] f).eval (a i)` for `k < m i` is
bijective on `degreeLT R (∑ i, m i)` if and only if `k !` is a unit for every order `k < m i` that
occurs and `a i - a j` is a unit whenever `i ≠ j` and both `m i` and `m j` are nonzero. -/
theorem eval_iterate_derivative_bijective_iff {a : ι → R} {m : ι → ℕ} :
    Bijective (fun (f : degreeLT R (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : R[X])).eval (a i)) ↔
      (∀ i, ∀ k < m i, IsUnit (k ! : R)) ∧
        ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  let S : (∀ i, Fin (m i) → R) → ∀ i, Fin (m i) → R :=
    Pi.map fun i => Pi.map fun (k : Fin (m i)) => (((k : ℕ) ! : R) * ·)
  have hcomp : (fun (f : degreeLT R (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : R[X])).eval (a i)) = S ∘ hermiteJet a m := by
    ext f i k
    simp [S, ← factorial_smul_hasseDeriv]
  have hS (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) : Bijective S :=
    .piMap fun i => .piMap fun k => IsUnit.isUnit_iff_mulLeft_bijective.1 (hm i k k.2)
  rw [hcomp]
  refine ⟨fun h => ?_, fun ⟨hm, ha⟩ => (hS hm).comp (hermiteJet_bijective_iff.2 ha)⟩
  have hm : ∀ i, ∀ k < m i, IsUnit (k ! : R) := by
    obtain ⟨c, hc⟩ := h.surjective.of_comp (fun _ _ => 1)
    exact fun i k hk => IsUnit.of_mul_eq_one (c i ⟨k, hk⟩) (congr_fun (congr_fun hc i) ⟨k, hk⟩)
  exact ⟨hm, hermiteJet_bijective_iff.1 (((hS hm).of_comp_iff' _).1 h)⟩

/-- Hermite interpolation with ordinary derivatives: when the differences of the nodes are units
and `k !` is a unit for every order `k < m i` that occurs, the jets `(derivative^[k] f).eval (a i)`
determine a polynomial of degree below `∑ i, m i`, and every such datum is attained. They are
`k !` times the Hasse jets. -/
theorem eval_iterate_derivative_bijective {a : ι → R}
    (ha : Pairwise fun i j => IsUnit (a i - a j)) (m : ι → ℕ)
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    Bijective fun (f : degreeLT R (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : R[X])).eval (a i) :=
  eval_iterate_derivative_bijective_iff.2 ⟨hm, fun _ _ hij _ _ => ha hij⟩

end ConfluentVandermonde

section NoZeroDivisors

variable [CommRing R] [NoZeroDivisors R] [Fintype ι] {a : ι → R}

/-- **The kernel of the jet map** over a domain: for injective nodes, the Hasse jets of `f` of the
orders `k < m i` at the nodes `a i` all vanish iff `∏ i, (X - a i) ^ m i` divides `f`. -/
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

end NoZeroDivisors

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
Evaluating iterated ordinary derivatives `(derivative^[k] f).eval (a i)` for `k < m i` is bijective
on `degreeLT K (∑ i, m i)` if and only if `(k ! : K) ≠ 0` for every order `k < m i` that occurs and
`a i ≠ a j` whenever `i ≠ j` and both `m i` and `m j` are nonzero. -/
theorem eval_iterate_derivative_bijective_iff_ne {m : ι → ℕ} :
    Bijective (fun (f : degreeLT K (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : K[X])).eval (a i)) ↔
      (∀ i, ∀ k < m i, (k ! : K) ≠ 0) ∧
        ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  simp only [eval_iterate_derivative_bijective_iff, isUnit_iff_ne_zero, sub_ne_zero]

/-- Over a field of characteristic zero, ordinary-derivative Hermite interpolation on
`degreeLT K (∑ i, m i)` is bijective if and only if `a i ≠ a j` whenever `i ≠ j` and both `m i`
and `m j` are nonzero. -/
theorem eval_iterate_derivative_bijective_iff_of_charZero [CharZero K] {m : ι → ℕ} :
    Bijective (fun (f : degreeLT K (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : K[X])).eval (a i)) ↔
      ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  simp [eval_iterate_derivative_bijective_iff_ne, Nat.factorial_ne_zero]

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
      ¬ Bijective (fun (f : degreeLT K (∑ i, ![p + 1] i)) i (k : Fin (![p + 1] i)) =>
        (derivative^[k] (f : K[X])).eval (![c] i)) := by
  refine ⟨hermiteJet_bijective (injective_of_subsingleton _) _, ?_⟩
  rw [eval_iterate_derivative_bijective_iff_ne, not_and]
  intro h _
  exact h 0 p (by simp)
    ((CharP.cast_eq_zero_iff K p _).2 (Nat.dvd_factorial (Fact.out : Nat.Prime p).pos le_rfl))

end Checks

end Polynomial
