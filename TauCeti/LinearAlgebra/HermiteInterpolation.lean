/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Algebra.Polynomial.Taylor
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
`R[X] ⧸ (∏ i, (X - a i) ^ m i)` with the jet space (`Polynomial.hasseJetQuotientEquiv`); since the
product is monic of degree `M`, the restriction `Polynomial.hermiteJet a m` to polynomials of
degree below `M` is bijective (`AdjoinRoot.degreeLTEquiv`).

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
* `Polynomial.hermiteBasis_eq_of_dvd_taylor_mul_sub_one`,
  `Polynomial.hermiteBasis_eq_prod_mul_pow_mul_taylor`: each Hermite basis polynomial factors as
  `(∏ i ≠ r, (X - C (a i)) ^ m i) * (X - C (a r)) ^ s` times the Taylor shift at `-a r` of the
  inverse modulo `X ^ (m r - s)` of the local complementary product, constructed from truncated
  geometric series.
* `Polynomial.eval_iterate_derivative_bijective`,
  `Polynomial.eval_iterate_derivative_smul_hermiteBasis`: Hermite interpolation with ordinary
  derivatives when the required factorials are invertible.

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

/-- **Local Taylor-inverse formula for the Hermite basis.** If `h` has degree below `m x.1 - x.2`
and inverts the Taylor shift at `a x.1` of `∏ i ≠ x.1, (X - C (a i)) ^ m i` modulo
`X ^ (m x.1 - x.2)`, then the Hermite basis polynomial at `x` is
`(∏ i ≠ x.1, (X - C (a i)) ^ m i) * (X - C (a x.1)) ^ x.2 * taylor (-a x.1) h`. -/
theorem hermiteBasis_eq_of_dvd_taylor_mul_sub_one [DecidableEq ι] (x : Σ i, Fin (m i))
    {h : R[X]} (hdeg : h.degree < ↑(m x.1 - x.2))
    (hdvd : X ^ (m x.1 - x.2) ∣
      taylor (a x.1) (∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i) * h - 1) :
    (hermiteBasis ha m x : R[X]) =
      (∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i) * (X - C (a x.1)) ^ (x.2 : ℕ) *
        taylor (-a x.1) h := by
  nontriviality R
  rw [hermiteBasis_apply]
  symm
  set Q : R[X] := ∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i
  set f : R[X] := Q * (X - C (a x.1)) ^ (x.2 : ℕ) * taylor (-a x.1) h
  refine (eq_hermiteJetEquiv_symm_iff ha m).2 ⟨?_, fun i k ↦ ?_⟩
  · have hQ : Monic Q := monic_prod_X_sub_C_pow (univ.erase x.1) a m
    have hP : Monic (Q * (X - C (a x.1)) ^ (x.2 : ℕ)) := hQ.mul ((monic_X_sub_C _).pow _)
    have hsum : (∑ i ∈ univ.erase x.1, m i) + x.2 + (m x.1 - x.2) = ∑ i, m i := by
      rw [add_assoc, Nat.add_sub_of_le x.2.isLt.le, sum_erase_add _ _ (mem_univ x.1)]
    calc f.degree
        ≤ (Q * (X - C (a x.1)) ^ (x.2 : ℕ)).degree + (taylor (-a x.1) h).degree := degree_mul_le _ _
      _ = ↑((∑ i ∈ univ.erase x.1, m i) + x.2) + h.degree := by
          rw [degree_eq_natDegree hP.ne_zero, hQ.natDegree_mul ((monic_X_sub_C _).pow _),
            natDegree_prod_X_sub_C_pow, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C,
            mul_one, degree_taylor]
      _ < ↑((∑ i ∈ univ.erase x.1, m i) + x.2) + ↑(m x.1 - x.2) :=
          WithBot.add_lt_add_left WithBot.coe_ne_bot hdeg
      _ = ↑(∑ i, m i) := by rw [← Nat.cast_add, hsum]
  · by_cases hi : i = x.1
    · subst hi
      have hX : taylor (a x.1) (X - C (a x.1)) = X := by simp [taylor_apply]
      have htf : taylor (a x.1) f = X ^ (x.2 : ℕ) * (taylor (a x.1) Q * h) := by
        simp only [f, taylor_mul, taylor_pow, hX, taylor_taylor, add_neg_cancel, taylor_zero]
        ring
      have hdvd' : X ^ m x.1 ∣ taylor (a x.1) f - X ^ (x.2 : ℕ) := by
        conv_lhs => rw [← Nat.add_sub_of_le x.2.isLt.le, pow_add]
        rw [htf, ← mul_sub_one]
        exact mul_dvd_mul_left _ hdvd
      have hk := X_pow_dvd_iff.1 hdvd' k k.2
      rw [coeff_sub, sub_eq_zero, taylor_coeff, coeff_X_pow] at hk
      rw [hk]
      simp [Pi.single_apply, Fin.ext_iff]
    · have hdvdQ : (X - C (a i)) ^ m i ∣ f :=
        (dvd_prod_of_mem _ (mem_erase.2 ⟨hi, mem_univ i⟩)).trans
          ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
      rw [X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.1 hdvdQ k k.2, Pi.single_eq_of_ne hi,
        Pi.zero_apply]

/-- When there is only one node, the Hermite basis polynomials are the Taylor monomials
`(X - C (a x.1)) ^ x.2`. -/
theorem hermiteBasis_of_subsingleton [Subsingleton ι] (x : Σ i, Fin (m i)) :
    (hermiteBasis ha m x : R[X]) = (X - C (a x.1)) ^ (x.2 : ℕ) := by
  let : DecidableEq ι := fun _ _ ↦ isTrue (Subsingleton.elim _ _)
  have hempty : univ.erase x.1 = (∅ : Finset ι) :=
    eq_empty_of_forall_notMem fun i hi ↦ (mem_erase.1 hi).1 (Subsingleton.elim i x.1)
  have hpos : 0 < m x.1 - x.2 := Nat.sub_pos_of_lt x.2.isLt
  have hdeg : (1 : R[X]).degree < ↑(m x.1 - x.2) :=
    degree_one_le.trans_lt (Nat.cast_pos.2 hpos)
  simpa [hempty] using hermiteBasis_eq_of_dvd_taylor_mul_sub_one ha m x hdeg (by simp [hempty])

/-- **Explicit truncated-geometric-series formula for the Hermite basis.** Given inverses `v i` of
`a x.1 - a i` for `i ≠ x.1`, each shifted linear factor `X + C (a x.1 - a i)` has inverse
`∑ k < N, v i * (-v i) ^ k * X ^ k` modulo `X ^ N` where `N = m x.1 - x.2`. Truncating the product
of their `m i`-th powers below degree `N` gives the local factor of `hermiteBasis ha m x`. -/
theorem hermiteBasis_eq_prod_mul_pow_mul_taylor [DecidableEq ι] (x : Σ i, Fin (m i)) {v : ι → R}
    (hv : ∀ i, i ≠ x.1 → (a x.1 - a i) * v i = 1) :
    (hermiteBasis ha m x : R[X]) =
      (∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i) * (X - C (a x.1)) ^ (x.2 : ℕ) *
        taylor (-a x.1) (∑ d ∈ range (m x.1 - x.2), monomial d
          ((∏ i ∈ univ.erase x.1,
            (∑ k ∈ range (m x.1 - x.2), monomial k (v i * (-v i) ^ k)) ^ m i).coeff d)) := by
  set N : ℕ := m x.1 - x.2
  set q : ι → R[X] := fun i ↦ ∑ k ∈ range N, monomial k (v i * (-v i) ^ k)
  set P : R[X] := ∏ i ∈ univ.erase x.1, q i ^ m i
  set h : R[X] := ∑ d ∈ range N, monomial d (P.coeff d)
  refine hermiteBasis_eq_of_dvd_taylor_mul_sub_one ha m x ?_ ?_
  · rw [degree_lt_iff_coeff_zero _ N]
    intro k hk
    rw [finsetSum_coeff]
    exact sum_eq_zero fun d hd ↦ by simp [((mem_range.1 hd).trans_le hk).ne]
  · let π : R[X] →+* R[X] ⧸ Ideal.span ({X ^ N} : Set R[X]) := Ideal.Quotient.mk _
    suffices hπ : π (taylor (a x.1) (∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i) * h) = π 1 by
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hπ)
    have hPh : π h = π P := by
      symm
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, X_pow_dvd_iff]
      intro d hd
      rw [coeff_sub, finsetSum_coeff,
        sum_eq_single d (fun c _ hcd ↦ by simp [hcd]) (fun hd' ↦ absurd (mem_range.2 hd) hd'),
        coeff_monomial_same, sub_self]
    have hq (i : ι) (hi : i ∈ univ.erase x.1) :
        π (taylor (a x.1) (X - C (a i)) * q i) = 1 := by
      have hgeom : taylor (a x.1) (X - C (a i)) * q i = 1 - monomial N ((-v i) ^ N) := by
        have hlin : taylor (a x.1) (X - C (a i)) * C (v i) = 1 - monomial 1 (-v i) := by
          rw [taylor_apply, sub_comp, X_comp, C_comp, ← C_mul_X_pow_eq_monomial, pow_one, map_neg]
          calc (X + C (a x.1) - C (a i)) * C (v i)
              = C (v i) * X + C (a x.1 - a i) * C (v i) := by rw [map_sub]; ring
            _ = 1 - -C (v i) * X := by rw [← C_mul, hv i (mem_erase.1 hi).1, C_1]; ring
        have hsum : q i = C (v i) * ∑ k ∈ range N, monomial 1 (-v i) ^ k := by
          rw [mul_sum]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [monomial_pow, one_mul, C_mul_monomial]
        rw [hsum, ← mul_assoc, hlin, mul_neg_geom_sum, monomial_pow, one_mul]
      rw [hgeom, map_sub, map_one, ← C_mul_X_pow_eq_monomial,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (dvd_mul_left _ _)), sub_zero]
    have htprod : taylor (a x.1) (∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i) =
        ∏ i ∈ univ.erase x.1, taylor (a x.1) ((X - C (a i)) ^ m i) :=
      map_prod (taylorAlgHom (a x.1)) _ _
    rw [map_mul, hPh, htprod, ← map_mul, ← prod_mul_distrib, map_prod, map_one]
    refine prod_eq_one fun i hi ↦ ?_
    rw [taylor_pow, ← mul_pow, map_pow, hq i hi, one_pow]

/-- Scaling a Hermite basis polynomial by an inverse `u` of `(x.2)!` yields Kronecker-delta values
for the ordinary derivatives `(derivative^[j] _).eval (a i)` of orders `j < m i`. -/
theorem eval_iterate_derivative_smul_hermiteBasis [DecidableEq ι] (x : Σ i, Fin (m i)) {u : R}
    (hu : ((x.2 : ℕ)! : R) * u = 1) (i : ι) {j : ℕ} (hj : j < m i) :
    (derivative^[j] (u • (hermiteBasis ha m x : R[X]))).eval (a i) =
      if i = x.1 ∧ j = x.2 then 1 else 0 := by
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, map_smul, eval_smul, eval_smul,
    nsmul_eq_mul, smul_eq_mul]
  have hev := eval_hasseDeriv_hermiteBasis ha m x i ⟨j, hj⟩
  by_cases h : i = x.1 ∧ j = x.2
  · rcases h with ⟨rfl, rfl⟩
    have hx : (⟨x.1, ⟨x.2, hj⟩⟩ : Σ i, Fin (m i)) = x := by ext <;> rfl
    rw [hev, hx]
    simp [hu]
  · have hx : x ≠ ⟨i, ⟨j, hj⟩⟩ := fun h' ↦ h ⟨(congr_arg Sigma.fst h').symm, by subst h'; rfl⟩
    simp [hev, hx, h]

end CommRing

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

end Polynomial
