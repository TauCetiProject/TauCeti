/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Factorial
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Algebra.Polynomial.RingDivision
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Hermite interpolation

Given nodes `a : ι → R` and multiplicities `m : ι → ℕ`, the *Hasse jets* of a polynomial `f` are
the values `(hasseDeriv k f).eval (a i)` for `k < m i`: the first `m i` Taylor coefficients of `f`
at `a i`. Hermite interpolation says that when the nodes are pairwise distinct (over a commutative
ring: when their differences are units), these `M = ∑ i, m i` numbers can be prescribed
arbitrarily, and determine `f` uniquely among the polynomials of degree below `M`. This
generalises Lagrange interpolation (`Lagrange.funEquivDegreeLT` and `Lagrange.interpolate`, every
`m i = 1`) to arbitrary multiplicities, including `0`, and to Hasse rather than ordinary
derivatives, so that it holds in every characteristic.

The kernel of the unrestricted jet map `Polynomial.hasseJet a m` on `R[X]` is the ideal generated
by `∏ i, (X - a i) ^ m i`: at one node this is Taylor's formula
(`Polynomial.X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero`), and the factors are pairwise
coprime. The map is surjective by the Chinese remainder theorem, so it identifies
`R[X] ⧸ (∏ i, (X - a i) ^ m i)` with the jet space (`Polynomial.hasseJetQuotientEquiv`); since the
product is monic of degree `M`, the restriction `Polynomial.hermiteJet a m` to polynomials of
degree below `M` is bijective (`AdjoinRoot.degreeLTEquiv`). More sharply, over any commutative ring
`hermiteJet a m` is bijective if and only if `a i - a j` is a unit whenever `i ≠ j` and both `m i`
and `m j` are nonzero (`Polynomial.hermiteJet_bijective_iff`), permitting repeated nodes of
multiplicity `0`.

In the monomial basis of `degreeLT R (∑ i, m i)` and the lexicographic jet basis indexed via
`finSigmaFinEquiv`, the matrix of `hermiteJet a m` is `Matrix.confluentVandermonde a m`
(`Polynomial.toMatrix_hermiteJet`), while the ordinary-derivative jet map
`Polynomial.hermiteOrdinaryJet a m` acquires factorial row factors and is bijective over a field of
prime characteristic `p` (for injective nodes) if and only if `∀ i, m i ≤ p`
(`Polynomial.hermiteOrdinaryJet_bijective_charP_iff`).

## Main definitions

* `Polynomial.hasseJet a m`: the `R`-linear map `f ↦ ((hasseDeriv k f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteJet a m`: its restriction to `Polynomial.degreeLT R (∑ i, m i)`.
* `Polynomial.hermiteJetEquiv`: for nodes with unit differences, Hermite interpolation as a linear
  equivalence; its inverse sends a jet datum to its interpolation polynomial.
* `Polynomial.hermiteBasis`: the basis of `degreeLT R (∑ i, m i)` dual to the Hasse jets.
* `Polynomial.hermiteOrdinaryJetEval`, `Polynomial.hermiteOrdinaryJet`: the unrestricted and
  degree-bounded jet maps formed with iterated ordinary derivatives `derivative^[k]`.

## Main results

* `Polynomial.all_jets_vanish_iff_dvd`: over a domain, for injective nodes, the jets of `f` all
  vanish iff `∏ i, (X - C (a i)) ^ m i ∣ f`; `all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub` and
  `hasseJet_eq_zero_iff_dvd` are the forms over a commutative ring.
* `Polynomial.hasseJetQuotientEquiv`: `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteJet_bijective`: over a field, for injective nodes, the Hermite jet map is
  bijective; `hermiteJet_bijective_of_pairwise_isUnit_sub` and the exact characterization
  `hermiteJet_bijective_iff` give the commutative-ring forms.
* `Polynomial.eq_hermiteJetEquiv_symm_iff`, `Polynomial.coe_hermiteJetEquiv_symm_hasseJet`:
  characterization of the Hermite interpolant and identification of the interpolant of `hasseJet`
  with the remainder modulo `∏ i, (X - C (a i)) ^ m i`.
* `Polynomial.map_hermiteJetEquiv_symm`: interpolation commutes with ring homomorphisms.
* `Polynomial.coe_hermiteJetEquiv_symm_one_eq_lagrangeInterpolate`,
  `Polynomial.hermiteJet_one_apply`: agreement with `Lagrange.interpolate` and
  `Lagrange.funEquivDegreeLT` when all multiplicities are `1`.
* `Polynomial.eval_iterate_derivative_bijective`, `Polynomial.hermiteOrdinaryJet_bijective_iff`,
  `Polynomial.hermiteOrdinaryJet_bijective_of_charZero`,
  `Polynomial.hermiteOrdinaryJet_bijective_charP_iff`: invertibility of the ordinary-derivative jet
  map via invertibility of factorials, including the sharp `m i ≤ p` threshold in characteristic
  `p`.
* `Polynomial.toMatrix_hermiteJet`, `Polynomial.toMatrix_hermiteOrdinaryJet`: matrix of
  `hermiteJet` (and `hermiteOrdinaryJet`) in the monomial and lexicographic jet bases, matching
  `Matrix.confluentVandermonde`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6: the Hasse derivatives as Taylor coefficients, pp. 282–283, and the multiplicity
  criterion through Hasse derivatives, Lemma 11.16, pp. 283–284.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326 (2000),
  Lemma 3.24, p. 100.
-/

public section

open Function Finset
open scoped Nat

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

/-- The unrestricted jet map formed with iterated ordinary derivatives `derivative^[k]`. -/
noncomputable def hermiteOrdinaryJetEval (a : ι → R) (m : ι → ℕ) :
    R[X] →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => LinearMap.pi fun k => leval (a i) ∘ₗ (derivative ^ (k : ℕ))

@[simp]
theorem hermiteOrdinaryJetEval_apply (a : ι → R) (m : ι → ℕ) (f : R[X]) (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJetEval a m f i k = (derivative ^[(k : ℕ)] f).eval (a i) := by
  simp [hermiteOrdinaryJetEval, pow_apply_eq_iterate]

/-- Each ordinary jet of order `k` is `k !` times the corresponding Hasse jet. -/
theorem hermiteOrdinaryJetEval_apply_eq_factorial_mul (a : ι → R) (m : ι → ℕ) (f : R[X])
    (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJetEval a m f i k = ((k : ℕ)! : R) * hasseJet a m f i k := by
  have h := map_nsmul (leval (a i)) ((k : ℕ)!) (hasseDeriv (k : ℕ) f)
  rw [leval_apply, leval_apply, ← LinearMap.smul_apply, factorial_smul_hasseDeriv,
    nsmul_eq_mul] at h
  rwa [hermiteOrdinaryJetEval_apply, hasseJet_apply]

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

/-- The jet map on `degreeLT R (∑ i, m i)` formed with iterated ordinary derivatives
`derivative^[k]`. Unlike `hermiteJet`, its `(i, k)` coordinate carries a factor of `k !`. -/
noncomputable def hermiteOrdinaryJet (a : ι → R) (m : ι → ℕ) :
    degreeLT R (∑ i, m i) →ₗ[R] ∀ i, Fin (m i) → R :=
  (hermiteOrdinaryJetEval a m).domRestrict _

@[simp]
theorem hermiteOrdinaryJet_apply (a : ι → R) (m : ι → ℕ) (f : degreeLT R (∑ i, m i)) :
    hermiteOrdinaryJet a m f = hermiteOrdinaryJetEval a m f := by
  simp [hermiteOrdinaryJet]

/-- On `degreeLT R (∑ i, m i)`, each ordinary jet of order `k` is `k !` times the corresponding
Hasse jet. -/
theorem hermiteOrdinaryJet_apply_eq_factorial_mul (a : ι → R) (m : ι → ℕ)
    (p : degreeLT R (∑ i, m i)) (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJet a m p i k = ((k : ℕ)! : R) * hermiteJet a m p i k :=
  hermiteOrdinaryJetEval_apply_eq_factorial_mul a m (p : R[X]) i k

end Semiring

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

/-- Interpolating the Hasse jets of an arbitrary polynomial `f : R[X]` computes its remainder
`f %ₘ ∏ i, (X - C (a i)) ^ m i` modulo the product of the local factors. -/
theorem coe_hermiteJetEquiv_symm_hasseJet (f : R[X]) :
    ((hermiteJetEquiv ha m).symm (hasseJet a m f) : R[X]) =
      f %ₘ ∏ i, (X - C (a i)) ^ m i := by
  nontriviality R
  symm
  refine (eq_hermiteJetEquiv_symm_iff ha m).2 ⟨?_, fun i k => ?_⟩
  · have hP := monic_prod_X_sub_C_pow univ a m
    simpa [degree_eq_natDegree hP.ne_zero, natDegree_prod_X_sub_C_pow] using
      degree_modByMonic_lt f hP
  · have hdvd : (∏ j, (X - C (a j)) ^ m j) ∣ f - f %ₘ ∏ j, (X - C (a j)) ^ m j :=
      ⟨_, sub_eq_of_eq_add' (modByMonic_add_div f _).symm⟩
    have h0 := (all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub ha m _).2 hdvd i k
    rw [hasseJet_apply]
    rwa [map_sub, eval_sub, sub_eq_zero, eq_comm] at h0

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

/-- Hermite interpolation with ordinary derivatives: when the differences of the nodes are units
and `k !` is a unit for every order `k < m i` that occurs, the jets `(derivative^[k] f).eval (a i)`
determine a polynomial of degree below `∑ i, m i`, and every such datum is attained. They are
`k !` times the Hasse jets. -/
theorem eval_iterate_derivative_bijective (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    Bijective fun (f : degreeLT R (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : R[X])).eval (a i) := by
  have : (fun (f : degreeLT R (∑ i, m i)) i (k : Fin (m i)) =>
      (derivative^[k] (f : R[X])).eval (a i)) =
      (fun (c : ∀ i, Fin (m i) → R) i (k : Fin (m i)) => ((k : ℕ) ! : R) * c i k) ∘
        hermiteJet a m := by
    ext f i k
    simp [← factorial_smul_hasseDeriv]
  rw [this]
  refine Bijective.comp ⟨fun c d h => ?_, fun c => ⟨fun i k => ↑(hm i k k.2).unit⁻¹ * c i k, ?_⟩⟩
    (hermiteJet_bijective_of_pairwise_isUnit_sub ha m)
  · ext i k
    exact (hm i k k.2).mul_left_cancel (congr_fun (congr_fun h i) k)
  · ext i k
    simp [← mul_assoc]

end CommRing

/-! ### Exact unit-difference criteria with zero multiplicities -/

section ExactCriteria

variable [CommRing R]

/-- If `hasseJet a m` is surjective, then `a i - a j` is a unit whenever `i ≠ j` and both `m i`
and `m j` are nonzero. -/
theorem isUnit_sub_of_hasseJet_surjective {a : ι → R} {m : ι → ℕ}
    (hsurj : Surjective (hasseJet a m)) ⦃i j : ι⦄ (hij : i ≠ j)
    (hmi : m i ≠ 0) (hmj : m j ≠ 0) : IsUnit (a i - a j) := by
  classical
  obtain ⟨f, hf⟩ := hsurj fun l _ => if l = i then 1 else 0
  have hfi : f.eval (a i) = 1 := by
    have h0 := congr_fun (congr_fun hf i) ⟨0, Nat.pos_of_ne_zero hmi⟩
    simpa using h0
  have hfj : f.eval (a j) = 0 := by
    have h0 := congr_fun (congr_fun hf j) ⟨0, Nat.pos_of_ne_zero hmj⟩
    simpa [hij.symm] using h0
  have hdvd := sub_dvd_eval_sub (a i) (a j) f
  rw [hfi, hfj, sub_zero] at hdvd
  exact isUnit_of_dvd_one hdvd

/-- For finitely many nodes over a commutative ring, the unrestricted Hasse jet map `hasseJet a m`
is surjective if and only if `a i - a j` is a unit whenever `i ≠ j` and `m i, m j ≠ 0`. -/
theorem hasseJet_surjective_iff [Finite ι] (a : ι → R) (m : ι → ℕ) :
    Surjective (hasseJet a m) ↔
      ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  refine ⟨fun h i j hij hmi hmj => isUnit_sub_of_hasseJet_surjective h hij hmi hmj,
    fun ha c => ?_⟩
  obtain ⟨g, hg⟩ := Ideal.exists_forall_sub_mem_ideal
    (I := fun i => Ideal.span {(X - C (a i)) ^ m i})
    (fun i j hij => (Ideal.isCoprime_span_singleton_iff _ _).2
      ((pairwise_isCoprime_X_sub_C_pow_iff a m).2 ha hij))
    (fun i => ∑ k : Fin (m i), c i k • (X - C (a i)) ^ (k : ℕ))
  refine ⟨g, ?_⟩
  ext i k
  have h := X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.1
    (Ideal.mem_span_singleton.1 (hg i)) k k.2
  rw [map_sub, eval_sub, sub_eq_zero] at h
  simp [h, map_sum, eval_finsetSum, Fin.val_inj]

variable [Fintype ι]

/-- When `a i - a j` is a unit for distinct nodes of nonzero multiplicity, `hasseJet a m f = 0`
holds if and only if `∏ i, (X - C (a i)) ^ m i` divides `f`. -/
theorem hasseJet_eq_zero_iff_dvd {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) :
    hasseJet a m f = 0 ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f := by
  have hcop := (pairwise_isCoprime_X_sub_C_pow_iff a m).2 ha
  refine ⟨fun h => Fintype.prod_dvd_of_coprime hcop fun i => ?_, fun hdvd => ?_⟩
  · exact X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.2 fun k hk => by
      simpa using congr_fun (congr_fun h i) ⟨k, hk⟩
  · ext i k
    simpa using X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.1
      ((dvd_prod_of_mem _ (mem_univ i)).trans hdvd) k k.2

/-- Reducing modulo `∏ i, (X - C (a i)) ^ m i` leaves all prescribed Hasse jets unchanged. -/
theorem hasseJet_modByMonic_prod_X_sub_C_pow {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) :
    hasseJet a m (f %ₘ ∏ i, (X - C (a i)) ^ m i) = hasseJet a m f := by
  have hdvd : (∏ i, (X - C (a i)) ^ m i) ∣ f - f %ₘ ∏ i, (X - C (a i)) ^ m i :=
    ⟨_, sub_eq_of_eq_add' (modByMonic_add_div f _).symm⟩
  have hzero := (hasseJet_eq_zero_iff_dvd ha _).2 hdvd
  rwa [map_sub, sub_eq_zero, eq_comm] at hzero

/-- On `degreeLT R (∑ i, m i)`, the kernel of `hermiteJet a m` is trivial whenever `a i - a j` is
a unit for distinct nodes of nonzero multiplicity. -/
theorem ker_hermiteJet {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    LinearMap.ker (hermiteJet a m) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  nontriviality R
  rw [LinearMap.mem_ker, hermiteJet_apply] at hp
  have hdvd : (∏ i, (X - C (a i)) ^ m i) ∣ (p : R[X]) :=
    (hasseJet_eq_zero_iff_dvd ha (p : R[X])).1 hp
  have hP : (∏ i, (X - C (a i)) ^ m i).Monic := monic_prod_X_sub_C_pow univ a m
  have hdeg : (p : R[X]).degree < (∏ i, (X - C (a i)) ^ m i).degree := by
    rw [degree_eq_natDegree hP.ne_zero, natDegree_prod_X_sub_C_pow]
    exact mem_degreeLT.1 p.2
  exact Subtype.ext (((modByMonic_eq_self_iff hP).2 hdeg).symm.trans
    ((modByMonic_eq_zero_iff_dvd hP).2 hdvd))

/-- **Hermite interpolation over a commutative ring**: `hermiteJet a m` is bijective if and only if
`a i - a j` is a unit whenever `i ≠ j` and both `m i` and `m j` are nonzero. -/
theorem hermiteJet_bijective_iff (a : ι → R) (m : ι → ℕ) :
    Bijective (hermiteJet a m) ↔
      ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  refine ⟨fun hbij i j hij hmi hmj => ?_, fun ha => ?_⟩
  · refine isUnit_sub_of_hasseJet_surjective (fun c => ?_) hij hmi hmj
    obtain ⟨p, hp⟩ := hbij.2 c
    exact ⟨(p : R[X]), (hermiteJet_apply a m p).symm.trans hp⟩
  · refine ⟨LinearMap.ker_eq_bot.1 (ker_hermiteJet ha), fun c => ?_⟩
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact ⟨0, Subsingleton.elim _ _⟩
    obtain ⟨f, hf⟩ := (hasseJet_surjective_iff a m).2 ha c
    set P := ∏ i, (X - C (a i)) ^ m i
    have hP : P.Monic := monic_prod_X_sub_C_pow univ a m
    have hmem : f %ₘ P ∈ degreeLT R (∑ i, m i) := by
      rw [mem_degreeLT, ← natDegree_prod_X_sub_C_pow univ a m, ← degree_eq_natDegree hP.ne_zero]
      exact degree_modByMonic_lt f hP
    exact ⟨⟨f %ₘ P, hmem⟩,
      (hermiteJet_apply a m _).trans ((hasseJet_modByMonic_prod_X_sub_C_pow ha f).trans hf)⟩

end ExactCriteria

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

end Field

/-! ### Specialization to Lagrange interpolation for simple nodes -/

section LagrangeComparison

variable [Field K] [DecidableEq ι]

/-- When every multiplicity is `1`, Hermite interpolation on a finite set `s` of injective nodes
coincides with `Lagrange.interpolate`. -/
theorem coe_hermiteJetEquiv_symm_one_eq_lagrangeInterpolate (s : Finset ι) (v : ι → K)
    (hvs : Set.InjOn v s) (r : ι → K) :
    ((hermiteJetEquiv (a := fun i : s => v i)
        (fun i j hij =>
          (sub_ne_zero.2 (mt (hvs i.2 j.2) (Subtype.ext_iff.not.mp hij))).isUnit)
        (fun _ => 1)).symm (fun i _ => r i) : K[X]) =
      Lagrange.interpolate s v r := by
  let ha : Pairwise fun i j : s => IsUnit (v i - v j) :=
    fun i j hij => (sub_ne_zero.2 (mt (hvs i.2 j.2) (Subtype.ext_iff.not.mp hij))).isUnit
  have hdeg := degree_hermiteJetEquiv_symm_lt (a := fun i : s => v i) ha (fun _ => 1)
    (fun i _ => r i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_one] at hdeg
  refine Lagrange.eq_interpolate_of_eval_eq _ hvs hdeg fun i hi => ?_
  simpa using eval_hasseDeriv_hermiteJetEquiv_symm (a := fun j : s => v j) ha (fun _ => 1)
    (fun j _ => r j) ⟨i, hi⟩ 0

/-- For `m = 1` on `s`, `hermiteJet` evaluates `p` at `v i`, agreeing componentwise with
`Lagrange.funEquivDegreeLT`. -/
theorem hermiteJet_one_apply (s : Finset ι) (v : ι → K) (hvs : Set.InjOn v s)
    (p : degreeLT K (∑ _ : s, 1)) (i : s) :
    hermiteJet (fun j : s => v j) (fun _ => 1) p i 0 =
      Lagrange.funEquivDegreeLT hvs ⟨(p : K[X]), by simpa using p.2⟩ i := by
  -- Mathlib's `Lagrange.funEquivDegreeLT` exposes `toFun f i := f.1.eval (v i)` with no simp lemma
  have h :
      Lagrange.funEquivDegreeLT hvs ⟨(p : K[X]), by simpa using p.2⟩ i = (p : K[X]).eval (v i) :=
    rfl
  rw [h, hermiteJet_apply]
  simp

end LagrangeComparison

/-! ### Invertibility of the ordinary-derivative jet map -/

section OrdinaryJet

variable [CommRing R] [Fintype ι]

/-- Over a commutative ring, the ordinary-derivative jet map `hermiteOrdinaryJet a m` is bijective
if and only if `a i - a j` is a unit for distinct nodes of nonzero multiplicity and `(k : ℕ)!` is
a unit in `R` for every `i : ι` and `k : Fin (m i)`. -/
theorem hermiteOrdinaryJet_bijective_iff (a : ι → R) (m : ι → ℕ) :
    Bijective (hermiteOrdinaryJet a m) ↔
      (∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) ∧
        ∀ i (k : Fin (m i)), IsUnit (((k : ℕ)! : R)) := by
  let diag : (∀ i, Fin (m i) → R) → (∀ i, Fin (m i) → R) :=
    fun c i k => ((k : ℕ)! : R) * c i k
  have hcomp : ⇑(hermiteOrdinaryJet a m) = diag ∘ ⇑(hermiteJet a m) := by
    ext p i k
    exact hermiteOrdinaryJet_apply_eq_factorial_mul a m p i k
  have hdiag_bij : (∀ i (k : Fin (m i)), IsUnit (((k : ℕ)! : R))) → Bijective diag := by
    intro hu
    refine ⟨fun c₁ c₂ h => ?_, fun c => ?_⟩
    · ext i k
      exact (hu i k).mul_left_cancel (congr_fun (congr_fun h i) k)
    · refine ⟨fun i k => ↑(hu i k).unit⁻¹ * c i k, ?_⟩
      ext i k
      simp [diag, ← mul_assoc]
  refine ⟨fun hbij => ?_, fun ⟨ha, hu⟩ => ?_⟩
  · have hu : ∀ i (k : Fin (m i)), IsUnit (((k : ℕ)! : R)) := by
      classical
      intro i k
      obtain ⟨p, hp⟩ := hbij.2 (Pi.single i (Pi.single k 1))
      have hpk := congr_fun (congr_fun hp i) k
      rw [hermiteOrdinaryJet_apply_eq_factorial_mul, Pi.single_eq_same, Pi.single_eq_same] at hpk
      exact isUnit_iff_exists_inv.mpr ⟨hermiteJet a m p i k, hpk⟩
    have hjet_bij : Bijective (hermiteJet a m) := by
      rw [hcomp] at hbij
      exact (Bijective.of_comp_iff' (hdiag_bij hu) _).mp hbij
    exact ⟨(hermiteJet_bijective_iff a m).mp hjet_bij, hu⟩
  · rw [hcomp]
    exact (hdiag_bij hu).comp ((hermiteJet_bijective_iff a m).mpr ha)

/-- Over a field of characteristic zero, the ordinary-derivative Hermite jet map is bijective for
injective nodes and arbitrary multiplicities. -/
theorem hermiteOrdinaryJet_bijective_of_charZero [Field K] [CharZero K]
    {a : ι → K} (ha : Injective a) (m : ι → ℕ) :
    Bijective (hermiteOrdinaryJet a m) := by
  rw [hermiteOrdinaryJet_bijective_iff]
  refine ⟨(hermiteJet_bijective_iff a m).mp (hermiteJet_bijective ha m), fun _ _ => ?_⟩
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)).isUnit

/-- Over a field of prime characteristic `p` with injective nodes, the ordinary-derivative Hermite
jet map is bijective if and only if every multiplicity satisfies `m i ≤ p` (so every jet order `k`
satisfies `k < p` and `k !` is invertible in `K`). -/
theorem hermiteOrdinaryJet_bijective_charP_iff [Field K] {p : ℕ}
    [hp : Fact (Nat.Prime p)] [CharP K p] {a : ι → K} (ha : Injective a) (m : ι → ℕ) :
    Bijective (hermiteOrdinaryJet a m) ↔ ∀ i, m i ≤ p := by
  rw [hermiteOrdinaryJet_bijective_iff]
  have ha' := (hermiteJet_bijective_iff a m).mp (hermiteJet_bijective ha m)
  refine ⟨fun ⟨_, h⟩ i => ?_, fun h => ⟨ha', fun i k => ?_⟩⟩
  · by_contra! hip
    have hu := h i ⟨p, hip⟩
    rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff K p,
      Nat.Prime.dvd_factorial hp.out] at hu
    exact hu le_rfl
  · rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff K p,
      Nat.Prime.dvd_factorial hp.out, not_le]
    exact k.2.trans_le (h i)

end OrdinaryJet

/-! ### Identification of the matrix of `hermiteJet` with `Matrix.confluentVandermonde` -/

section MatrixBridge

variable [CommRing R] {r : ℕ}

/-- In the monomial basis `degreeLT.basis R (∑ i, m i)` of `degreeLT R (∑ i, m i)` and the
lexicographic jet basis of `∀ i, Fin (m i) → R` indexed via `finSigmaFinEquiv`, the matrix of
`hermiteJet a m` is `Matrix.confluentVandermonde a m`. -/
theorem toMatrix_hermiteJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i))
        ((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv)
        (hermiteJet a m) =
      Matrix.confluentVandermonde a m := by
  ext ρ j
  rw [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply, Pi.basis_repr,
    Pi.basisFun_repr, hermiteJet_apply, hasseJet_apply, degreeLT.basis_val,
    Matrix.confluentVandermonde_apply]

/-- In the monomial basis and lexicographic jet basis, the matrix of `hermiteOrdinaryJet a m` is
the ordinary-derivative confluent Vandermonde matrix. -/
theorem toMatrix_hermiteOrdinaryJet (a : Fin r → R) (m : Fin r → ℕ) :
    LinearMap.toMatrix (degreeLT.basis R (∑ i, m i))
        ((Pi.basis fun i => Pi.basisFun R (Fin (m i))).reindex finSigmaFinEquiv)
        (hermiteOrdinaryJet a m) =
      Matrix.of fun ρ (j : Fin (∑ i, m i)) =>
        (derivative ^[(finSigmaFinEquiv.symm ρ).2] (X ^ (j : ℕ) : R[X])).eval
          (a (finSigmaFinEquiv.symm ρ).1) := by
  ext ρ j
  rw [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply, Pi.basis_repr,
    Pi.basisFun_repr, hermiteOrdinaryJet_apply, hermiteOrdinaryJetEval_apply, degreeLT.basis_val,
    Matrix.of_apply]

end MatrixBridge

/-! ### Checks -/

section Checks

/-- Single node `r`: `hermiteJetEquiv` at multiplicity `n` over any commutative ring reconstructs
the truncated Taylor expansion `∑ k : Fin n, C (c 0 k) * (X - C r) ^ k`. -/
example [CommRing R] (r : R) (n : ℕ) (c : ∀ i : Fin 1, Fin ((fun _ => n) i) → R) :
    ((hermiteJetEquiv (a := ![r]) (fun i j hij => absurd (Subsingleton.elim i j) hij)
        (fun _ => n)).symm c : R[X]) =
      ∑ k : Fin n, C (c 0 k) * (X - C r) ^ (k : ℕ) := by
  symm
  refine (eq_hermiteJetEquiv_symm_iff _ _).2 ⟨?_, fun i k => ?_⟩
  · rw [← mem_degreeLT]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mem_degreeLT, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    refine (degree_mul_le _ _).trans_lt ?_
    refine (add_le_add degree_C_le (degree_pow_le _ _)).trans_lt ?_
    rw [zero_add]
    exact (nsmul_le_nsmul_right (degree_X_sub_C_le r) _).trans_lt (by simp)
  · fin_cases i
    simpa using eval_hasseDeriv_sum_fin_C_mul_X_sub_C_pow r (c 0) k

/-- Double node at `0` with jet `(1, 0)` and simple node at `1` with value `0`: the unique
quadratic Hermite interpolant over `ℤ` is `1 - X ^ 2`. -/
example :
    ((hermiteJetEquiv (a := ![(0 : ℤ), 1])
        (by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all)
        ![2, 1]).symm
        (Fin.cases (motive := fun i => Fin (![2, 1] i) → ℤ) ![(1 : ℤ), 0]
          (Fin.cases ![(0 : ℤ)] fun i => Fin.elim0 i)) : ℤ[X]) =
      1 - X ^ 2 := by
  symm
  refine (eq_hermiteJetEquiv_symm_iff _ _).2 ⟨?_, fun i k => ?_⟩
  · refine (degree_sub_le _ _).trans_lt ?_
    simp only [degree_one, degree_X_pow, Fin.sum_univ_two]
    decide
  · fin_cases i <;> fin_cases k <;> simp [← monomial_one_right_eq_X_pow] <;> rfl

/-- Empty node family (`r = 0`): `degreeLT ℤ 0 = ⊥` and `hermiteJet` is bijective between two
trivial modules. -/
example (a : Fin 0 → ℤ) (m : Fin 0 → ℕ) : Bijective (hermiteJet a m) :=
  (hermiteJet_bijective_iff a m).mpr fun i => Fin.elim0 i

/-- Repeated node of multiplicity `0`: `![0, 0, 1]` is not injective, yet `![1, 0, 1]` satisfies
the unit-difference criterion over `ℤ` and `hermiteJet` is bijective. -/
example :
    ¬ Injective ![(0 : ℤ), 0, 1] ∧
      Bijective (hermiteJet ![(0 : ℤ), 0, 1] ![1, 0, 1]) := by
  refine ⟨fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide), ?_⟩
  rw [hermiteJet_bijective_iff]
  intro i j hij hmi hmj
  fin_cases i <;> fin_cases j <;> simp_all

private local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Characteristic `2` at `![0]`, `![3]`: `hermiteJet` is bijective over `ZMod 2`, whereas
`hermiteOrdinaryJet` is NOT bijective because `2! = 0` in `ZMod 2` (`X ^ 2` lies in its kernel). -/
example :
    Bijective (hermiteJet ![(0 : ZMod 2)] ![3]) ∧
      ¬ Bijective (hermiteOrdinaryJet ![(0 : ZMod 2)] ![3]) := by
  have hinj : Injective ![(0 : ZMod 2)] := injective_of_subsingleton _
  refine ⟨hermiteJet_bijective hinj ![3], ?_⟩
  rw [hermiteOrdinaryJet_bijective_charP_iff hinj]
  decide

/-- Characteristic `2` at `![0, 1]`, `![2, 2]`: every multiplicity satisfies `m i ≤ 2`, so even
`hermiteOrdinaryJet` is bijective over `ZMod 2`. -/
example : Bijective (hermiteOrdinaryJet ![(0 : ZMod 2), 1] ![2, 2]) := by
  have hinj : Injective ![(0 : ZMod 2), 1] := by decide
  rw [hermiteOrdinaryJet_bijective_charP_iff hinj]
  decide

end Checks

end Polynomial
