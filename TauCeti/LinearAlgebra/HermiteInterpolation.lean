/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
by `∏ i, (X - C (a i)) ^ m i`: at one node this is Taylor's formula
(`Polynomial.X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero`), and the factors are pairwise
coprime. The Chinese remainder theorem (`Polynomial.hermiteQuotientEquiv`) identifies
`R[X] ⧸ (∏ i, (X - C (a i)) ^ m i)` with `∏ i, R[X] ⧸ ((X - C (a i)) ^ m i)`, and the jet map
factors through this isomorphism followed at each node by `TauCeti.taylorJetQuotientEquiv`
(`Polynomial.hasseJet_eq_taylorJetQuotientEquiv`), giving the linear equivalence
`Polynomial.hasseJetQuotientEquiv` with the jet space. Since `∏ i, (X - C (a i)) ^ m i` is monic of
degree `M`, the restriction `Polynomial.hermiteJet a m` to polynomials of degree below `M` is
bijective (`AdjoinRoot.degreeLTEquiv`).

## Main definitions

* `Polynomial.hasseJet a m`: the `R`-linear map `f ↦ ((hasseDeriv k f).eval (a i))_{i, k < m i}`.
* `Polynomial.hermiteJet a m`: its restriction to `Polynomial.degreeLT R (∑ i, m i)`.
* `Polynomial.ordinaryHermiteJet a m`: the `R`-linear jet map built from iterated ordinary
  derivatives `(derivative^[k] f).eval (a i)`.
* `Polynomial.hermiteQuotientEquiv`: the Chinese remainder ring isomorphism
  `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃+* ∀ i, R[X] ⧸ ((X - C (a i)) ^ m i)`.
* `Polynomial.hasseJetQuotientEquiv`: the `R`-linear equivalence
  `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteJetEquiv`: for nodes with unit differences, Hermite interpolation as a linear
  equivalence; its inverse sends a jet datum to its interpolation polynomial.
* `Polynomial.hermiteBasis`: the basis of `degreeLT R (∑ i, m i)` dual to the Hasse jets.

## Main results

* `Polynomial.all_jets_vanish_iff_dvd`: over a domain, for injective nodes, the jets of `f` all
  vanish iff `∏ i, (X - C (a i)) ^ m i ∣ f`; `all_jets_vanish_iff_dvd_of_pairwise_isUnit_sub` is
  the form over a commutative ring.
* `Polynomial.hasseJet_eq_taylorJetQuotientEquiv`: the Hasse jet map factors through
  `hermiteQuotientEquiv` and `TauCeti.taylorJetQuotientEquiv`.
* `Polynomial.hermiteJet_injective`, `Polynomial.ordinaryHermiteJet_injective`: over a domain, for
  injective nodes, `hermiteJet` is injective (and `ordinaryHermiteJet` is injective when `k ! ≠ 0`
  for `k < m i`).
* `Polynomial.hermiteJet_bijective`: over a field, for injective nodes, the Hermite jet map is
  bijective; `hermiteJet_bijective_of_pairwise_isUnit_sub` is the form over a commutative ring.
* `Polynomial.eq_hermiteJetEquiv_symm_iff`, `Polynomial.existsUnique_hermite_interpolation`: the
  interpolation polynomial is the unique polynomial of degree below `∑ i, m i` with the prescribed
  jets.
* `Polynomial.hermiteJet_map`, `Polynomial.map_hermiteJetEquiv_symm`: jet evaluation and
  interpolation commute with ring homomorphisms.
* `Polynomial.ordinaryHermiteJet_eq_comp`, `Polynomial.ordinaryHermiteJet_bijective`: comparison
  and bijectivity of ordinary-derivative Hermite interpolation when the factorials `k !` with
  `k < m i` are units.

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

/-- Taking Hermite jets commutes with mapping the coefficients and nodes by a ring homomorphism. -/
theorem hermiteJet_map [Semiring S] (ψ : R →+* S) (a : ι → R) (m : ι → ℕ)
    (f : degreeLT R (∑ i, m i)) :
    hermiteJet (fun i => ψ (a i)) m ⟨(f : R[X]).map ψ, map_mem_degreeLT ψ f.2⟩ =
      fun i k => ψ (hermiteJet a m f i k) := by
  simpa only [hermiteJet_apply] using hasseJet_map ψ a m f

/-- The Hermite jet map built from ordinary derivatives: the `R`-linear map sending a polynomial `f`
of degree below `∑ i, m i` to `((derivative^[k] f).eval (a i))_{i, k < m i}`. -/
noncomputable def ordinaryHermiteJet (a : ι → R) (m : ι → ℕ) :
    degreeLT R (∑ i, m i) →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => LinearMap.pi fun k =>
    leval (a i) ∘ₗ (derivative ^ (k : ℕ)) ∘ₗ (degreeLT R (∑ i, m i)).subtype

/-- The coordinates of `ordinaryHermiteJet` are the iterated ordinary derivatives at the nodes. -/
@[simp]
theorem ordinaryHermiteJet_apply (a : ι → R) (m : ι → ℕ) (f : degreeLT R (∑ i, m i)) (i : ι)
    (k : Fin (m i)) :
    ordinaryHermiteJet a m f i k = (derivative^[k] (f : R[X])).eval (a i) := by
  simp [ordinaryHermiteJet, pow_apply_eq_iterate]

/-- The ordinary Hermite jets are the Hasse Hermite jets scaled by `k !`. -/
theorem ordinaryHermiteJet_eq_factorial_mul (a : ι → R) (m : ι → ℕ)
    (f : degreeLT R (∑ i, m i)) (i : ι) (k : Fin (m i)) :
    ordinaryHermiteJet a m f i k = ((k : ℕ) ! : R) * hermiteJet a m f i k := by
  simp [← factorial_smul_hasseDeriv]

end Semiring

section CommSemiring

variable [CommSemiring R] [Fintype ι]

/-- When `k !` is a unit for every `k < m i`, the ordinary Hermite jet map is the Hasse Hermite jet
map followed by the invertible scaling of coordinate `(i, k)` by `k !`. -/
theorem ordinaryHermiteJet_eq_comp (a : ι → R) {m : ι → ℕ}
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    ordinaryHermiteJet a m =
      (LinearEquiv.piCongrRight fun i =>
        LinearEquiv.piCongrRight fun k : Fin (m i) =>
          LinearEquiv.smulOfUnit (M := R) (hm i k k.2).unit).toLinearMap ∘ₗ
        hermiteJet a m := by
  ext f i k
  simp [← factorial_smul_hasseDeriv, LinearEquiv.smulOfUnit, Units.smul_def]

/-- When `k !` is a unit for every `k < m i`, the ordinary and Hasse Hermite jet maps have the same
kernel. -/
theorem ker_ordinaryHermiteJet (a : ι → R) {m : ι → ℕ}
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    LinearMap.ker (ordinaryHermiteJet a m) = LinearMap.ker (hermiteJet a m) := by
  ext f
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, ordinaryHermiteJet_eq_factorial_mul]
  exact forall_congr' fun i => forall_congr' fun k => (hm i k k.2).mul_right_eq_zero

/-- When `k !` is a unit for every `k < m i`, the ordinary Hermite jet map is bijective iff the
Hasse Hermite jet map is bijective. -/
theorem ordinaryHermiteJet_bijective_iff_of_isUnit (a : ι → R) {m : ι → ℕ}
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    Bijective (ordinaryHermiteJet a m) ↔ Bijective (hermiteJet a m) := by
  rw [ordinaryHermiteJet_eq_comp a hm]
  exact EquivLike.comp_bijective _
    (LinearEquiv.piCongrRight fun i =>
      LinearEquiv.piCongrRight fun k : Fin (m i) =>
        LinearEquiv.smulOfUnit (M := R) (hm i k k.2).unit)

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

/-- When the differences of the nodes are units, the ideal generated by `∏ i, (X - C (a i)) ^ m i`
is the intersection of the ideals generated by its factors. -/
theorem span_prod_X_sub_C_pow :
    Ideal.span {∏ i, (X - C (a i)) ^ m i} = ⨅ i, Ideal.span {(X - C (a i)) ^ m i} :=
  (Ideal.iInf_span_singleton fun _ _ hij =>
    (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow).symm

/-- **Chinese remainder theorem** for Hermite interpolation: when the differences of the nodes are
units, `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i)` is isomorphic as a ring to the product of the local
quotients `R[X] ⧸ ((X - C (a i)) ^ m i)`. -/
noncomputable def hermiteQuotientEquiv :
    (R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃+*
      ∀ i, R[X] ⧸ Ideal.span {(X - C (a i)) ^ m i} :=
  (Ideal.quotEquivOfEq (span_prod_X_sub_C_pow ha m)).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hij =>
      (Ideal.isCoprime_span_singleton_iff _ _).2
        (isCoprime_X_sub_C_of_isUnit_sub (ha hij)).pow

@[simp]
theorem hermiteQuotientEquiv_mk (f : R[X]) (i : ι) :
    hermiteQuotientEquiv ha m (Ideal.Quotient.mk _ f) i = Ideal.Quotient.mk _ f := by
  rw [hermiteQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact Ideal.quotientInfRingEquivPiQuotient_mk_apply _ _ _

/-- The Hasse jet map factors through the quotient by `∏ i, (X - C (a i)) ^ m i`, the Chinese
remainder isomorphism `hermiteQuotientEquiv`, and the local Taylor coordinates
`TauCeti.taylorJetQuotientEquiv`. -/
theorem hasseJet_eq_taylorJetQuotientEquiv (f : R[X]) (i : ι) :
    hasseJet a m f i =
      TauCeti.taylorJetQuotientEquiv (a i) (m i)
        (hermiteQuotientEquiv ha m (Ideal.Quotient.mk _ f) i) := by
  rw [hermiteQuotientEquiv_mk, TauCeti.taylorJetQuotientEquiv_mk]
  ext k
  simp

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

/-- On the quotient `R[X] ⧸ (∏ i, (X - C (a i)) ^ m i)`, `hasseJetQuotientEquiv` is the Chinese
remainder isomorphism `hermiteQuotientEquiv` followed at each node by
`TauCeti.taylorJetQuotientEquiv`. -/
theorem hasseJetQuotientEquiv_apply (x : R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) (i : ι) :
    hasseJetQuotientEquiv ha m x i =
      TauCeti.taylorJetQuotientEquiv (a i) (m i) (hermiteQuotientEquiv ha m x i) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa using hasseJet_eq_taylorJetQuotientEquiv ha m f i

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

/-- Every Hasse jet datum has a unique interpolating polynomial of degree below `∑ i, m i`, when
the differences of the nodes are units. -/
theorem existsUnique_hermite_interpolation_of_pairwise_isUnit_sub (c : ∀ i, Fin (m i) → R) :
    ∃! f : R[X], f.degree < ∑ i, m i ∧
      ∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = c i k :=
  ⟨(hermiteJetEquiv ha m).symm c, (eq_hermiteJetEquiv_symm_iff ha m).1 rfl,
    fun _ hf => (eq_hermiteJetEquiv_symm_iff ha m).2 hf⟩

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

/-- The Hasse jet of the Hermite basis polynomial `hermiteBasis ha m x` is the standard basis
vector at `x`. -/
@[simp]
theorem hasseJet_hermiteBasis [DecidableEq ι] (x : Σ i, Fin (m i)) :
    hasseJet a m (hermiteBasis ha m x) = Pi.single x.1 (Pi.single x.2 1) := by
  rw [hermiteBasis_apply, hasseJet_hermiteJetEquiv_symm]

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
of the nodes are units and `k !` is a unit for every order `k < m i`, `ordinaryHermiteJet a m` is
bijective. -/
theorem ordinaryHermiteJet_bijective_of_pairwise_isUnit_sub
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : R)) :
    Bijective (ordinaryHermiteJet a m) :=
  (ordinaryHermiteJet_bijective_iff_of_isUnit a hm).2
    (hermiteJet_bijective_of_pairwise_isUnit_sub ha m)

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

/-- Over a domain, for injective nodes, the Hermite jet map on the polynomials of degree below
`∑ i, m i` is injective, even when the differences of the nodes are not units. -/
theorem hermiteJet_injective (ha : Injective a) (m : ι → ℕ) : Injective (hermiteJet a m) := by
  nontriviality R
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext ?_
  have hdvd : (∏ i, (X - C (a i)) ^ m i) ∣ (f : R[X]) :=
    (all_jets_vanish_iff_dvd ha m f).1 fun i k => by
      simpa using congr_fun (congr_fun hf i) k
  refine eq_zero_of_dvd_of_degree_lt hdvd ?_
  rw [degree_eq_natDegree (monic_prod_X_sub_C_pow univ a m).ne_zero, natDegree_prod_X_sub_C_pow]
  exact mem_degreeLT.1 f.2

/-- Over a domain, for injective nodes, the ordinary-derivative Hermite jet map is injective
whenever `k ! ≠ 0` in `R` for every `k < m i` (in particular, unconditionally in characteristic
zero), even when neither node differences nor factorials are units in `R`. -/
theorem ordinaryHermiteJet_injective (ha : Injective a) {m : ι → ℕ}
    (hm : ∀ i, ∀ k < m i, (k ! : R) ≠ 0) : Injective (ordinaryHermiteJet a m) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => hermiteJet_injective ha m ?_
  ext i k
  have h := congr_fun (congr_fun hf i) k
  rw [Pi.zero_apply, Pi.zero_apply, ordinaryHermiteJet_eq_factorial_mul, mul_eq_zero] at h
  rw [map_zero, Pi.zero_apply, Pi.zero_apply]
  exact h.resolve_left (hm i k k.2)

end NoZeroDivisors

section Field

variable [Field K] [Fintype ι] {a : ι → K}

/-- **Hermite interpolation** over a field: for injective nodes and arbitrary multiplicities, the
Hermite jet map on the polynomials of degree below `∑ i, m i` is bijective. -/
theorem hermiteJet_bijective (ha : Injective a) (m : ι → ℕ) : Bijective (hermiteJet a m) :=
  hermiteJet_bijective_of_pairwise_isUnit_sub
    (fun _ _ hij => (sub_ne_zero.2 (ha.ne hij)).isUnit) m

/-- Every Hasse jet datum over a field has a unique interpolating polynomial of degree below
`∑ i, m i` when the nodes are distinct. -/
theorem existsUnique_hermite_interpolation (ha : Injective a) (m : ι → ℕ)
    (c : ∀ i, Fin (m i) → K) :
    ∃! f : K[X], f.degree < ∑ i, m i ∧
      ∀ i (k : Fin (m i)), (hasseDeriv k f).eval (a i) = c i k :=
  existsUnique_hermite_interpolation_of_pairwise_isUnit_sub
    (fun _ _ hij => (sub_ne_zero.2 (ha.ne hij)).isUnit) m c

/-- Over a field, when the nodes are distinct and every `k !` with `k < m i` is a unit, the
ordinary-derivative Hermite jet map is bijective. -/
theorem ordinaryHermiteJet_bijective (ha : Injective a) (m : ι → ℕ)
    (hm : ∀ i, ∀ k < m i, IsUnit (k ! : K)) : Bijective (ordinaryHermiteJet a m) :=
  (ordinaryHermiteJet_bijective_iff_of_isUnit a hm).2 (hermiteJet_bijective ha m)

end Field

/-! ### Checks -/

section Examples

/-- One node `c` of multiplicity `2`: `c₀ + c₁ X ↦ (c₀ + c₁ c, c₁)`. -/
example (c c₀ c₁ : ℤ) (h : C c₀ + C c₁ * X ∈ degreeLT ℤ (∑ i, ![2] i)) :
    hermiteJet ![c] ![2] ⟨_, h⟩ 0 ⟨0, by simp⟩ = c₀ + c₁ * c ∧
      hermiteJet ![c] ![2] ⟨_, h⟩ 0 ⟨1, by simp⟩ = c₁ := by
  simp only [hermiteJet_apply, hasseJet_apply]
  simp

/-- Simple nodes `0, 1`: `c₀ + c₁ X ↦ (c₀, c₀ + c₁)`, the values at the nodes. -/
example (c₀ c₁ : ℤ) (h : C c₀ + C c₁ * X ∈ degreeLT ℤ (∑ i, ![1, 1] i)) :
    hermiteJet ![0, 1] ![1, 1] ⟨_, h⟩ 0 ⟨0, by simp⟩ = c₀ ∧
      hermiteJet ![0, 1] ![1, 1] ⟨_, h⟩ 1 ⟨0, by simp⟩ = c₀ + c₁ := by
  simp only [hermiteJet_apply, hasseJet_apply]
  simp

/-- No nodes: the map from the zero space to the one-point space is bijective. -/
example : Bijective (hermiteJet (![] : Fin 0 → ℤ) ![]) :=
  hermiteJet_bijective_of_pairwise_isUnit_sub (fun i => i.elim0) _

/-- A node of multiplicity `0` contributes no coordinate, and `hermiteJet` remains bijective. -/
example : Bijective (hermiteJet ![(5 : ℚ), 0] ![0, 3]) :=
  hermiteJet_bijective (by decide) _

/-- Over `ℤ` at nodes `0` and `2` of multiplicity `3`, neither `0 - 2` nor `2 !` is a unit, yet
`ordinaryHermiteJet` is still injective because `ℤ` is a domain of characteristic zero. -/
example : Injective (ordinaryHermiteJet ![(0 : ℤ), 2] ![3, 3]) :=
  ordinaryHermiteJet_injective (by decide) fun _ _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

/-- A repeated node: `X ↦ (0, 0)`, so injectivity of the nodes is necessary. -/
example : ¬ Injective (hermiteJet ![(0 : ℤ), 0] ![1, 1]) := by
  intro h
  have hX : (X : ℤ[X]) ∈ degreeLT ℤ (∑ i, ![1, 1] i) := by
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

/-- `X² ∤ X` over `ℤ`: the jet of order `1` of `X` at `0` is `1`. -/
example : ¬ (∏ i, (X - C (![(0 : ℤ)] i)) ^ ![2] i) ∣ X := by
  rw [← all_jets_vanish_iff_dvd (injective_of_subsingleton _)]
  intro h
  simpa [hasseDeriv_one'] using h 0 ⟨1, by simp⟩

/-- `X (X - 1) ∣ X² - X` over `ℤ`. -/
example : (∏ i, (X - C (![(0 : ℤ), 1] i)) ^ ![1, 1] i) ∣ X ^ 2 - X := by
  rw [← all_jets_vanish_iff_dvd (by decide)]
  intro i k
  fin_cases i <;> fin_cases k <;> simp

/-- Worked example over `ℤ`: `1 - X²` is the unique polynomial in `ℤ[X]` of degree below `3` with
`f(0) = 1`, `f'(0) = 0` and `f(1) = 0`. -/
example (f : ℤ[X]) (hf : f ∈ degreeLT ℤ 3) (h₀ : f.eval 0 = 1) (h₁ : (derivative f).eval 0 = 0)
    (h₂ : f.eval 1 = 0) : f = 1 - X ^ 2 := by
  have hM : ∑ i, ![2, 1] i = 3 := rfl
  have hg : (1 - X ^ 2 : ℤ[X]) ∈ degreeLT ℤ (∑ i, ![2, 1] i) := by
    rw [hM, mem_degreeLT]
    compute_degree!
  refine congrArg Subtype.val (hermiteJet_injective (a := ![(0 : ℤ), 1]) (by decide) ![2, 1]
    (a₁ := ⟨f, hM ▸ hf⟩) (a₂ := ⟨_, hg⟩) ?_)
  ext i k
  rw [hermiteJet_apply, hasseJet_apply, hermiteJet_apply, hasseJet_apply]
  fin_cases i <;> fin_cases k <;> simp [h₀, h₁, h₂]

end Examples

end Polynomial
