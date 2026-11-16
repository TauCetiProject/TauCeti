/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.Polynomial.Taylor
public import TauCeti.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Hermite interpolation

Given nodes `a : ι → R` and multiplicities `m : ι → ℕ`, the *Hasse jets* of a polynomial `f` are
the values `(hasseDeriv k f).eval (a i)` for `k < m i`: the first `m i` Taylor coefficients of `f`
at `a i`. Hermite interpolation says that when the nodes are pairwise distinct (over a commutative
ring: when their differences are units), these `M = ∑ i, m i` numbers can be prescribed
arbitrarily, and determine `f` uniquely among the polynomials of degree below `M`. This
generalises Lagrange interpolation (`Lagrange.funEquivDegreeLT`, every `m i = 1`) to arbitrary
multiplicities, including `0`, and to Hasse rather than ordinary derivatives, so that it holds in
every characteristic.

The kernel of the unrestricted jet map `Polynomial.hasseJet a m` on `R[X]` is the ideal generated
by `∏ i, (X - a i) ^ m i`: at one node this is Taylor's formula
(`Polynomial.X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero`), and the factors are pairwise
coprime. The map is surjective by the Chinese remainder theorem, so it identifies
`R[X] ⧸ (∏ i, (X - a i) ^ m i)` with the jet space (`Polynomial.hasseJetQuotientEquiv`), factoring
through the Chinese remainder ring isomorphism `Polynomial.hermiteQuotientEquiv` and the local
Taylor coordinates `TauCeti.taylorJetQuotientEquiv`. Since the product is monic of degree `M`, the
restriction `Polynomial.hermiteJet a m` to polynomials of degree below `M` is bijective
(`AdjoinRoot.degreeLTEquiv`).

## Main definitions

* `Polynomial.hasseJet a m`: the `R`-linear map `f ↦ ((hasseDeriv k f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteJet a m`: its restriction to `Polynomial.degreeLT R (∑ i, m i)`.
* `Polynomial.ordinaryHermiteJet a m`: the Hermite jet map built from ordinary derivatives,
  `f ↦ ((derivative^[k] f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteQuotientEquiv`: for nodes with unit differences, the Chinese remainder ring
  isomorphism `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃+* ∀ i, R[X] ⧸ ((X - C (a i)) ^ m i)`.
* `Polynomial.hasseJetQuotientEquiv`:
  `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteJetEquiv`: for nodes with unit differences, Hermite interpolation as a linear
  equivalence; its inverse sends a jet datum to its interpolation polynomial.
* `Polynomial.hermiteBasis`: the basis of `degreeLT R (∑ i, m i)` dual to the Hasse jets.

## Main results

* `Polynomial.all_jets_vanish_iff_dvd`: over a commutative ring without zero divisors, for
  injective nodes, the jets of `f` all vanish iff `∏ i, (X - C (a i)) ^ m i ∣ f`;
  `all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub` is the form over a commutative ring.
* `Polynomial.hasseJetQuotientEquiv_eq_taylorJetQuotientEquiv`: `hasseJetQuotientEquiv` is
  `hermiteQuotientEquiv` followed componentwise by `TauCeti.taylorJetQuotientEquiv`.
* `Polynomial.hermiteJet_bijective`: over a field, for injective nodes, the Hermite jet map is
  bijective; `hermiteJet_bijective_of_pairwise_isUnit_sub` is the form over a commutative ring.
* `Polynomial.eq_hermiteJetEquiv_symm_iff`, `Polynomial.existsUnique_hermite_interpolation`: the
  interpolation polynomial is the unique polynomial of degree below `∑ i, m i` with the prescribed
  jets.
* `Polynomial.hermiteJet_map`, `Polynomial.map_hermiteJetEquiv_symm`: Hermite jets and
  interpolation commute with ring homomorphisms.
* `Polynomial.ordinaryHermiteJet_bijective`,
  `Polynomial.ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub`: the same interpolation with
  ordinary derivatives, when the factorials `k !` with `k < m i` are units.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6: the Hasse derivatives as Taylor coefficients, pp. 282–283, and the multiplicity
  criterion through Hasse derivatives, Lemma 11.16, pp. 283–284.
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
    hermiteJet (fun i => ψ (a i)) m ⟨(f : R[X]).map ψ, map_mem_degreeLT ψ f.2⟩ =
      fun i k => ψ (hermiteJet a m f i k) := by
  simpa only [hermiteJet_apply] using hasseJet_map ψ a m f

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

/-- When the differences of the nodes are units, the ideal generated by `∏ i, (X - a i) ^ m i`
is the intersection of the ideals generated by its factors `(X - a i) ^ m i`. -/
theorem span_prod_X_sub_C_pow_eq_iInf :
    Ideal.span {∏ i, (X - C (a i)) ^ m i} = ⨅ i, Ideal.span {(X - C (a i)) ^ m i} :=
  (Ideal.iInf_span_singleton fun _ _ hij => (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow).symm

/-- **Chinese remainder theorem** for `∏ i, (X - a i) ^ m i`, when the differences of the nodes are
units. -/
noncomputable def hermiteQuotientEquiv :
    (R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃+*
      ((i : ι) → R[X] ⧸ Ideal.span {(X - C (a i)) ^ m i}) :=
  (Ideal.quotEquivOfEq (span_prod_X_sub_C_pow_eq_iInf ha m)).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hij =>
      (Ideal.isCoprime_span_singleton_iff _ _).2 (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow

@[simp]
theorem hermiteQuotientEquiv_mk (f : R[X]) (i : ι) :
    hermiteQuotientEquiv ha m (Ideal.Quotient.mk _ f) i = Ideal.Quotient.mk _ f := by
  rw [hermiteQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact Ideal.quotientInfRingEquivPiQuotient_mk_apply _ _ _

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

/-- The quotient-to-jet equivalence `hasseJetQuotientEquiv` is the Chinese remainder isomorphism
`hermiteQuotientEquiv` followed componentwise by the local Taylor coordinates
`TauCeti.taylorJetQuotientEquiv`. -/
theorem hasseJetQuotientEquiv_eq_taylorJetQuotientEquiv
    (x : R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) (i : ι) :
    hasseJetQuotientEquiv ha m x i =
      TauCeti.taylorJetQuotientEquiv (a i) (m i) (hermiteQuotientEquiv ha m x i) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  ext k
  simp

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

/-- Hermite interpolation with ordinary derivatives over a commutative ring: when the differences
of the nodes are units and `k !` is a unit for every order `k < m i` that occurs, the
ordinary-derivative Hermite jet map on polynomials of degree below `∑ i, m i` is bijective. -/
theorem ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    Bijective (ordinaryHermiteJet a m) := by
  let e : (∀ i, Fin (m i) → R) ≃ₗ[R] ∀ i, Fin (m i) → R :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfUnit (hm i k k.2).unit
  have h : ⇑(ordinaryHermiteJet a m) = e ∘ hermiteJet a m := by
    ext f i k
    rw [Function.comp_apply, ordinaryHermiteJet_eq_factorial_mul]
    simp [e, LinearEquiv.smulOfUnit, Units.smul_def]
  rw [h]
  exact e.bijective.comp (hermiteJet_bijective_of_pairwise_isUnit_sub ha m)

end CommRing

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

end NoZeroDivisors

section Field

variable [Field K] [Fintype ι] {a : ι → K}

/-- **Hermite interpolation** over a field: for injective nodes and arbitrary multiplicities, the
Hermite jet map on the polynomials of degree below `∑ i, m i` is bijective. -/
theorem hermiteJet_bijective (ha : Injective a) (m : ι → ℕ) : Bijective (hermiteJet a m) :=
  hermiteJet_bijective_of_pairwise_isUnit_sub
    (fun _ _ hij => (sub_ne_zero.2 (ha.ne hij)).isUnit) m

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

section Examples

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
it kills `X²`, so the unit hypothesis on the factorials is necessary. -/
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

/-- `X (X - 1) ∣ X² - X`. -/
example : (∏ i, (X - C (![(0 : ℚ), 1] i)) ^ ![1, 1] i) ∣ X ^ 2 - X := by
  rw [← all_jets_vanish_iff_dvd (by decide)]
  intro i k
  fin_cases i <;> fin_cases k <;> simp

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

end Examples

end Polynomial
