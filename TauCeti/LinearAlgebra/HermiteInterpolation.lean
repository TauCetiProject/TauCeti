/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.Algebra.Polynomial.RingDivision
public import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Coprime.Lemmas
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Hermite polynomial interpolation and the Hasse jet map

Given nodes `a : ι → R` and multiplicities `m : ι → ℕ` over a commutative ring `R`, the Hasse jet
map `Polynomial.hermiteJetEval a m : R[X] →ₗ[R] ∀ i, Fin (m i) → R` evaluates the Hasse derivatives
`hasseDeriv k f` (`k < m i`) of a polynomial `f` at each node `a i`, and its restriction
`Polynomial.hermiteJet a m` acts on the submodule `Polynomial.degreeLT R (∑ i, m i)` of polynomials
of degree strictly below `M = ∑ i, m i`. Using Hasse derivatives rather than iterated ordinary
derivatives avoids factorial denominators and makes Hermite interpolation characteristic-free.

At a single node `r`, the truncated Taylor expansion gives an `R`-linear isomorphism
`Polynomial.quotientSpanXSubCPowEquiv r n : (R[X] ⧸ Ideal.span {(X - C r) ^ n}) ≃ₗ[R] (Fin n → R)`.
Across finitely many nodes whose pairwise differences `a i - a j` are units whenever `i ≠ j` and
`m i, m j ≠ 0` — equivalently, whose local factors `(X - C (a i)) ^ m i` are pairwise coprime —
composing the Chinese Remainder Theorem (`Ideal.quotientInfRingEquivPiQuotient`) with the local
Taylor coordinates gives the global quotient isomorphism `Polynomial.quotientSpanProdXSubCPowEquiv`
between `R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}` and `∀ i, Fin (m i) → R`. In particular,
the kernel of `hermiteJetEval a m` on all of `R[X]` is `Ideal.span {∏ i, (X - C (a i)) ^ m i}`.

Reducing modulo the monic product `∏ i, (X - C (a i)) ^ m i` identifies this quotient with
`degreeLT R (∑ i, m i)`. Over every commutative ring, `hermiteJet a m` is bijective if and only if
`a i - a j` is a unit for all `i ≠ j` with `m i, m j ≠ 0` (`Polynomial.hermiteJet_bijective_iff`),
which holds in particular for injective nodes over any field (`Polynomial.hermiteJet_bijective`).
From the resulting linear equivalence `Polynomial.hermiteEquiv` we obtain the interpolation operator
`Polynomial.hermiteInterpolate`, the dual Hasse-jet basis `Polynomial.hermiteBasis` of
`degreeLT R (∑ i, m i)`, naturality under ring homomorphisms (`Polynomial.map_hermiteInterpolate`),
agreement with `Lagrange.interpolate` and `Lagrange.funEquivDegreeLT` when all multiplicities are
`1`, the exact invertibility criterion for the ordinary-derivative jet map
`Polynomial.hermiteOrdinaryJet`, and the matrix identity `Polynomial.toMatrix_hermiteJet`
identifying the matrix of `hermiteJet a m` in the monomial and lexicographic jet bases with
`Matrix.confluentVandermonde a m`.

## Main definitions

* `Polynomial.hermiteJetEval a m`: the unrestricted Hasse jet map `R[X] →ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteJet a m`: the Hasse jet map restricted to `degreeLT R (∑ i, m i)`.
* `Polynomial.quotientSpanXSubCPowEquiv r n`: local Taylor linear equivalence
  `(R[X] ⧸ Ideal.span {(X - C r) ^ n}) ≃ₗ[R] Fin n → R`.
* `Polynomial.quotientSpanProdXSubCPowEquiv`: global jet quotient `R`-linear equivalence
  `(R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteEquiv`: the Hermite interpolation equivalence
  `degreeLT R (∑ i, m i) ≃ₗ[R] ∀ i, Fin (m i) → R`.
* `Polynomial.hermiteInterpolate`: the linear map `(∀ i, Fin (m i) → R) →ₗ[R] R[X]` sending jet
  data to its unique interpolating polynomial of degree `< ∑ i, m i`.
* `Polynomial.hermiteBasis`: the basis of `degreeLT R (∑ i, m i)` dual to the Hasse jet functionals.
* `Polynomial.hermiteOrdinaryJetEval`, `Polynomial.hermiteOrdinaryJet`: the jet maps formed with
  iterated ordinary derivatives `derivative^[k]`.

## Main results

* `Polynomial.prod_X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero`,
  `Polynomial.ker_hermiteJetEval`: `∏ i, (X - C (a i)) ^ m i` divides `f` if and only if all Hasse
  jets of order `< m i` vanish at `a i`.
* `Polynomial.hermiteJet_bijective_iff`, `Polynomial.hermiteJet_bijective`: exact unit-difference
  criterion over commutative rings, and bijectivity for injective nodes over any field.
* `Polynomial.eq_hermiteInterpolate_iff`, `Polynomial.existsUnique_mem_degreeLT_hermiteJetEval_eq`:
  existence and uniqueness of the Hermite interpolant, plus the remainder formula
  `Polynomial.hermiteInterpolate_hermiteJetEval`.
* `Polynomial.map_hermiteInterpolate`: commutation of Hermite interpolation with `Polynomial.map`,
  showing that `K`-rational nodes and jet values over an extension `L` produce a polynomial over
  `K`.
* `Polynomial.hermiteInterpolate_one_eq_lagrangeInterpolate`: for multiplicity `1`, Hermite
  interpolation coincides with `Lagrange.interpolate`.
* `Polynomial.hermiteOrdinaryJet_bijective_iff`,
  `Polynomial.hermiteOrdinaryJet_bijective_of_charZero`,
  `Polynomial.hermiteOrdinaryJet_bijective_charP_iff`: invertibility of the ordinary-derivative jet
  map via invertibility of factorials, including the sharp `m i ≤ p` threshold in characteristic
  `p`.
* `Polynomial.toMatrix_hermiteJet`: the matrix of `hermiteJet a m` in the monomial basis and
  lexicographic jet basis is `Matrix.confluentVandermonde a m`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (AMS Colloquium Publications 53, 2004),
  §11.6, Lemma 11.16, pp. 282–284.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Grundlehren 326, 2000),
  Lemma 3.24, p. 100.
-/

public section

open Finset
open scoped Nat

namespace Polynomial

/-! ### The unrestricted and degree-bounded Hasse jet maps -/

section Semiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι : Type*}

/-- The unrestricted Hasse jet map `f ↦ (fun i k => (hasseDeriv k f).eval (a i))` on `R[X]`. -/
noncomputable def hermiteJetEval (a : ι → R) (m : ι → ℕ) : R[X] →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => LinearMap.pi fun k => (leval (a i)).comp (hasseDeriv (k : ℕ))

@[simp]
theorem hermiteJetEval_apply (a : ι → R) (m : ι → ℕ) (f : R[X]) (i : ι) (k : Fin (m i)) :
    hermiteJetEval a m f i k = (hasseDeriv (k : ℕ) f).eval (a i) :=
  (rfl)

/-- Evaluating `hermiteJetEval` on a mapped polynomial `f.map ψ` at the mapped nodes `ψ ∘ a`
applies `ψ` to every jet value. -/
theorem hermiteJetEval_map (ψ : R →+* S) (a : ι → R) (m : ι → ℕ) (f : R[X]) (i : ι)
    (k : Fin (m i)) :
    hermiteJetEval (ψ ∘ a) m (f.map ψ) i k = ψ (hermiteJetEval a m f i k) := by
  simp [hasseDeriv_map]

/-- The Hermite jet map on polynomials of degree strictly below `∑ i, m i`, sending `p` to the
family of Hasse jets `(hasseDeriv k p).eval (a i)` for `i : ι` and `k : Fin (m i)`. -/
noncomputable def hermiteJet [Fintype ι] (a : ι → R) (m : ι → ℕ) :
    degreeLT R (∑ i, m i) →ₗ[R] ∀ i, Fin (m i) → R :=
  (hermiteJetEval a m).comp (degreeLT R (∑ i, m i)).subtype

@[simp]
theorem hermiteJet_apply [Fintype ι] (a : ι → R) (m : ι → ℕ) (p : degreeLT R (∑ i, m i))
    (i : ι) (k : Fin (m i)) :
    hermiteJet a m p i k = (hasseDeriv (k : ℕ) (p : R[X])).eval (a i) :=
  (rfl)

theorem hermiteJet_eq_hermiteJetEval_comp_subtype [Fintype ι] (a : ι → R) (m : ι → ℕ) :
    hermiteJet a m = (hermiteJetEval a m).comp (degreeLT R (∑ i, m i)).subtype :=
  (rfl)

/-- The unrestricted jet map formed with iterated ordinary derivatives `derivative^[k]`. -/
noncomputable def hermiteOrdinaryJetEval (a : ι → R) (m : ι → ℕ) :
    R[X] →ₗ[R] ∀ i, Fin (m i) → R :=
  LinearMap.pi fun i => LinearMap.pi fun k => (leval (a i)).comp (derivative ^ (k : ℕ))

@[simp]
theorem hermiteOrdinaryJetEval_apply (a : ι → R) (m : ι → ℕ) (f : R[X]) (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJetEval a m f i k = (derivative ^[(k : ℕ)] f).eval (a i) := by
  simp [hermiteOrdinaryJetEval, pow_apply_eq_iterate]

/-- The jet map on `degreeLT R (∑ i, m i)` formed with iterated ordinary derivatives
`derivative^[k]`. Unlike `hermiteJet`, its `(i, k)` coordinate carries a factor of `k !`. -/
noncomputable def hermiteOrdinaryJet [Fintype ι] (a : ι → R) (m : ι → ℕ) :
    degreeLT R (∑ i, m i) →ₗ[R] ∀ i, Fin (m i) → R :=
  (hermiteOrdinaryJetEval a m).comp (degreeLT R (∑ i, m i)).subtype

@[simp]
theorem hermiteOrdinaryJet_apply [Fintype ι] (a : ι → R) (m : ι → ℕ)
    (p : degreeLT R (∑ i, m i)) (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJet a m p i k = (derivative ^[(k : ℕ)] (p : R[X])).eval (a i) := by
  simp [hermiteOrdinaryJet]

/-- Each ordinary jet of order `k` is `k !` times the corresponding Hasse jet. -/
theorem hermiteOrdinaryJetEval_apply_eq_factorial_mul (a : ι → R) (m : ι → ℕ) (f : R[X])
    (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJetEval a m f i k = ((k : ℕ)! : R) * hermiteJetEval a m f i k := by
  rw [hermiteOrdinaryJetEval_apply, ← factorial_smul_hasseDeriv, LinearMap.smul_apply,
    nsmul_eq_mul, eval_mul, eval_natCast, hermiteJetEval_apply]

/-- On `degreeLT R (∑ i, m i)`, each ordinary jet of order `k` is `k !` times the corresponding
Hasse jet. -/
theorem hermiteOrdinaryJet_apply_eq_factorial_mul [Fintype ι] (a : ι → R) (m : ι → ℕ)
    (p : degreeLT R (∑ i, m i)) (i : ι) (k : Fin (m i)) :
    hermiteOrdinaryJet a m p i k = ((k : ℕ)! : R) * hermiteJet a m p i k :=
  hermiteOrdinaryJetEval_apply_eq_factorial_mul a m (p : R[X]) i k

end Semiring

/-! ### Local Taylor quotient isomorphism at a single node -/

section LocalQuotient

variable {R : Type*} [CommRing R]

private noncomputable def quotientSpanXSubCPowToFun (r : R) (n : ℕ)
    (x : R[X] ⧸ Ideal.span {(X - C r) ^ n}) : Fin n → R :=
  Quotient.liftOn' x (fun f (k : Fin n) => (hasseDeriv (k : ℕ) f).eval r) fun f g h => by
    rw [Submodule.quotientRel_def, Ideal.mem_span_singleton,
      X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero] at h
    ext k
    have hk := h k k.2
    rwa [map_sub, eval_sub, sub_eq_zero] at hk

private theorem quotientSpanXSubCPowToFun_mk (r : R) (n : ℕ) (f : R[X]) (k : Fin n) :
    quotientSpanXSubCPowToFun r n (Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) f) k =
      (hasseDeriv (k : ℕ) f).eval r :=
  (rfl)

private noncomputable def quotientSpanXSubCPowMap (r : R) (n : ℕ) :
    (R[X] ⧸ Ideal.span {(X - C r) ^ n}) →ₗ[R] Fin n → R where
  toFun := quotientSpanXSubCPowToFun r n
  map_add' x y := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hadd :
        Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) f +
          Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) g =
        Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) (f + g) :=
      (map_add (Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n})) f g).symm
    rw [hadd]
    ext k
    rw [quotientSpanXSubCPowToFun_mk, Pi.add_apply, quotientSpanXSubCPowToFun_mk,
      quotientSpanXSubCPowToFun_mk, map_add, eval_add]
  map_smul' s x := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hsmul : s • Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) f =
        Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) (s • f) :=
      (map_smul (Ideal.Quotient.mkₐ R (Ideal.span {(X - C r) ^ n})) s f).symm
    rw [hsmul]
    ext k
    simp only [quotientSpanXSubCPowToFun_mk, map_smul, eval_smul, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply]

private theorem quotientSpanXSubCPowMap_mk (r : R) (n : ℕ) (f : R[X]) (k : Fin n) :
    quotientSpanXSubCPowMap r n (Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) f) k =
      (hasseDeriv (k : ℕ) f).eval r :=
  (rfl)

private theorem quotientSpanXSubCPowMap_bijective (r : R) (n : ℕ) :
    Function.Bijective (quotientSpanXSubCPowMap r n) := by
  refine ⟨?_, fun c => ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_ker] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero]
    intro k hk
    exact congrFun hx ⟨k, hk⟩
  · refine ⟨Ideal.Quotient.mk _ (∑ k : Fin n, C (c k) * (X - C r) ^ (k : ℕ)), ?_⟩
    ext k
    rw [quotientSpanXSubCPowMap_mk, eval_hasseDeriv_sum_fin_C_mul_X_sub_C_pow]

/-- At a single node `r`, evaluating the Hasse derivatives of order `< n` at `r` descends to an
`R`-linear isomorphism `(R[X] ⧸ Ideal.span {(X - C r) ^ n}) ≃ₗ[R] (Fin n → R)`, with inverse given
by the truncated Taylor polynomial `c ↦ ∑ k : Fin n, C (c k) * (X - C r) ^ k`. -/
noncomputable def quotientSpanXSubCPowEquiv (r : R) (n : ℕ) :
    (R[X] ⧸ Ideal.span {(X - C r) ^ n}) ≃ₗ[R] Fin n → R :=
  LinearEquiv.ofBijective (quotientSpanXSubCPowMap r n) (quotientSpanXSubCPowMap_bijective r n)

@[simp]
theorem quotientSpanXSubCPowEquiv_mk (r : R) (n : ℕ) (f : R[X]) (k : Fin n) :
    quotientSpanXSubCPowEquiv r n (Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n}) f) k =
      (hasseDeriv (k : ℕ) f).eval r :=
  (rfl)

@[simp]
theorem quotientSpanXSubCPowEquiv_symm_apply (r : R) (n : ℕ) (c : Fin n → R) :
    (quotientSpanXSubCPowEquiv r n).symm c =
      Ideal.Quotient.mk (Ideal.span {(X - C r) ^ n})
        (∑ k : Fin n, C (c k) * (X - C r) ^ (k : ℕ)) := by
  apply (quotientSpanXSubCPowEquiv r n).injective
  rw [LinearEquiv.apply_symm_apply]
  ext k
  rw [quotientSpanXSubCPowEquiv_mk, eval_hasseDeriv_sum_fin_C_mul_X_sub_C_pow]

end LocalQuotient

/-! ### Multi-node kernel and Chinese Remainder Theorem quotient comparison -/

section MultiNodeQuotient

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- When `a i - a j` is a unit for distinct nodes of nonzero multiplicity, the principal ideal
generated by `∏ i, (X - C (a i)) ^ m i` is the intersection of the local ideals
`Ideal.span {(X - C (a i)) ^ m i}`. -/
theorem span_prod_X_sub_C_pow_eq_iInf {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    Ideal.span {∏ i, (X - C (a i)) ^ m i} = ⨅ i, Ideal.span {(X - C (a i)) ^ m i} := by
  have hcop :
      ((Finset.univ : Finset ι) : Set ι).Pairwise
        (Function.onFun IsCoprime fun i => Ideal.span {(X - C (a i)) ^ m i}) := by
    intro i _ j _ hij
    rw [Function.onFun_apply, Ideal.isCoprime_span_singleton_iff]
    exact (pairwise_isCoprime_X_sub_C_pow_iff a m).mpr ha hij
  rw [← Ideal.prod_span_singleton Finset.univ (fun i => (X - C (a i)) ^ m i),
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
  simp

/-- When `a i - a j` is a unit for distinct nodes of nonzero multiplicity, a polynomial `f` is
divisible by `∏ i, (X - C (a i)) ^ m i` if and only if all Hasse derivatives of order `< m i`
vanish at `a i`. -/
theorem prod_X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) :
    (∏ i, (X - C (a i)) ^ m i) ∣ f ↔
      ∀ i (k : Fin (m i)), (hasseDeriv (k : ℕ) f).eval (a i) = 0 := by
  have hcop := (pairwise_isCoprime_X_sub_C_pow_iff a m).mpr ha
  refine ⟨fun hdvd i k => ?_, fun h => ?_⟩
  · exact X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.mp
      ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hdvd) k k.2
  · refine Fintype.prod_dvd_of_coprime hcop fun i => ?_
    exact X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.mpr fun k hk => h i ⟨k, hk⟩

/-- Over a field, all Hasse jets of `f` of order `< m i` vanish at injective nodes `a i` if and
only if `∏ i, (X - C (a i)) ^ m i` divides `f`. -/
theorem prod_X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero_of_injective
    {K : Type*} [Field K] {a : ι → K} (ha : Function.Injective a) (m : ι → ℕ) (f : K[X]) :
    (∏ i, (X - C (a i)) ^ m i) ∣ f ↔
      ∀ i (k : Fin (m i)), (hasseDeriv (k : ℕ) f).eval (a i) = 0 :=
  prod_X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero
    (fun _ _ hij _ _ => (sub_ne_zero_of_ne (ha.ne hij)).isUnit) f

/-- `hermiteJetEval a m f = 0` holds if and only if `∏ i, (X - C (a i)) ^ m i` divides `f`. -/
theorem hermiteJetEval_eq_zero_iff {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) :
    hermiteJetEval a m f = 0 ↔ (∏ i, (X - C (a i)) ^ m i) ∣ f := by
  rw [prod_X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero ha]
  refine ⟨fun h i k => congrFun (congrFun h i) k, fun h => ?_⟩
  ext i k
  exact h i k

/-- The kernel of the unrestricted Hasse jet map `hermiteJetEval a m` on `R[X]` is the principal
ideal generated by `∏ i, (X - C (a i)) ^ m i`, viewed as an `R`-submodule. -/
theorem ker_hermiteJetEval {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    LinearMap.ker (hermiteJetEval a m) =
      (Ideal.span {∏ i, (X - C (a i)) ^ m i}).restrictScalars R := by
  ext f
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton,
    hermiteJetEval_eq_zero_iff ha]

/-- Reducing modulo `∏ i, (X - C (a i)) ^ m i` leaves all prescribed Hasse jets unchanged. -/
theorem hermiteJetEval_modByMonic_prod_X_sub_C_pow {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) :
    hermiteJetEval a m (f %ₘ ∏ i, (X - C (a i)) ^ m i) = hermiteJetEval a m f := by
  have hdvd : (∏ i, (X - C (a i)) ^ m i) ∣ f - f %ₘ ∏ i, (X - C (a i)) ^ m i :=
    ⟨_, sub_eq_of_eq_add' (modByMonic_add_div f _).symm⟩
  have hzero := (hermiteJetEval_eq_zero_iff ha _).mpr hdvd
  rwa [map_sub, sub_eq_zero, eq_comm] at hzero

/-- Composing the Chinese Remainder Theorem (`Ideal.quotientInfRingEquivPiQuotient`) with the local
Taylor equivalences `quotientSpanXSubCPowEquiv` gives an `R`-linear isomorphism
`(R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃ₗ[R] ∀ i, Fin (m i) → R` through which
`hermiteJetEval a m` factors. -/
noncomputable def quotientSpanProdXSubCPowEquiv {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    (R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃ₗ[R] ∀ i, Fin (m i) → R :=
  have hcop :
      Pairwise (Function.onFun IsCoprime fun i => Ideal.span {(X - C (a i)) ^ m i}) := by
    intro i j hij
    rw [Function.onFun_apply, Ideal.isCoprime_span_singleton_iff]
    exact (pairwise_isCoprime_X_sub_C_pow_iff a m).mpr ha hij
  let crtAlgEquiv :
      (R[X] ⧸ Ideal.span {∏ i, (X - C (a i)) ^ m i}) ≃ₐ[R]
        ∀ i, R[X] ⧸ Ideal.span {(X - C (a i)) ^ m i} :=
    (Ideal.quotientEquivAlgOfEq R (span_prod_X_sub_C_pow_eq_iInf ha)).trans
      { __ := Ideal.quotientInfRingEquivPiQuotient _ hcop
        commutes' := fun _ => rfl }
  crtAlgEquiv.toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun i => quotientSpanXSubCPowEquiv (a i) (m i))

@[simp]
theorem quotientSpanProdXSubCPowEquiv_mk {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) (i : ι)
    (k : Fin (m i)) :
    quotientSpanProdXSubCPowEquiv ha
        (Ideal.Quotient.mk (Ideal.span {∏ j, (X - C (a j)) ^ m j}) f) i k =
      (hasseDeriv (k : ℕ) f).eval (a i) := by
  simp only [quotientSpanProdXSubCPowEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
    LinearEquiv.piCongrRight_apply]
  exact quotientSpanXSubCPowEquiv_mk (a i) (m i) f k

/-- The unrestricted Hasse jet map `hermiteJetEval a m` is the composite of the `R`-algebra
quotient map modulo `∏ i, (X - C (a i)) ^ m i` and `quotientSpanProdXSubCPowEquiv ha`. -/
theorem quotientSpanProdXSubCPowEquiv_comp_mkₐ {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    (quotientSpanProdXSubCPowEquiv ha).toLinearMap.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {∏ i, (X - C (a i)) ^ m i})).toLinearMap =
      hermiteJetEval a m := by
  refine LinearMap.ext fun f => ?_
  ext i k
  exact quotientSpanProdXSubCPowEquiv_mk ha f i k

omit [Fintype ι] in
/-- For finitely many nodes whose differences are units whenever both multiplicities are nonzero,
the unrestricted Hasse jet map `hermiteJetEval a m` is surjective onto `∀ i, Fin (m i) → R`. -/
theorem hermiteJetEval_surjective [Finite ι] {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    Function.Surjective (hermiteJetEval a m) := by
  cases nonempty_fintype ι
  intro c
  obtain ⟨x, rfl⟩ := (quotientSpanProdXSubCPowEquiv ha).surjective c
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨f, ?_⟩
  ext i k
  exact (quotientSpanProdXSubCPowEquiv_mk ha f i k).symm

end MultiNodeQuotient

/-! ### Bijectivity of `hermiteJet`, the Hermite interpolant, and the adapted basis -/

section HermiteInterpolation

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- On `degreeLT R (∑ i, m i)`, the kernel of `hermiteJet a m` is trivial whenever `a i - a j` is
a unit for distinct nodes of nonzero multiplicity. -/
theorem ker_hermiteJet {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    LinearMap.ker (hermiteJet a m) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  ext1
  nontriviality R
  have hdvd : (∏ i, (X - C (a i)) ^ m i) ∣ (p : R[X]) :=
    (hermiteJetEval_eq_zero_iff ha (p : R[X])).mp hp
  have hmonic : (∏ i, (X - C (a i)) ^ m i).Monic :=
    monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
  have hPdeg : (∏ i, (X - C (a i)) ^ m i).natDegree = ∑ i, m i := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _]
    simp [(monic_X_sub_C _).natDegree_pow]
  have hpdeg : (p : R[X]).degree < (∏ i, (X - C (a i)) ^ m i).degree := by
    rw [← mem_degreeLT_natDegree_iff hmonic.ne_zero, hPdeg]
    exact p.2
  rw [← (modByMonic_eq_self_iff hmonic).mpr hpdeg, (modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd,
    Submodule.coe_zero]

omit [Fintype ι] in
/-- If `hermiteJetEval a m` is surjective, then `a i - a j` is a unit whenever `i ≠ j` and
`m i, m j ≠ 0`. -/
theorem isUnit_sub_of_hermiteJetEval_surjective {a : ι → R} {m : ι → ℕ}
    (hsurj : Function.Surjective (hermiteJetEval a m)) ⦃i j : ι⦄ (hij : i ≠ j)
    (hmi : m i ≠ 0) (hmj : m j ≠ 0) : IsUnit (a i - a j) := by
  classical
  obtain ⟨f, hf⟩ := hsurj fun l _ => if l = i then 1 else 0
  have hfi : f.eval (a i) = 1 := by
    have h0 := congrFun (congrFun hf i) ⟨0, Nat.pos_of_ne_zero hmi⟩
    simpa using h0
  have hfj : f.eval (a j) = 0 := by
    have h0 := congrFun (congrFun hf j) ⟨0, Nat.pos_of_ne_zero hmj⟩
    simpa [hij.symm] using h0
  have hdvd := sub_dvd_eval_sub (a i) (a j) f
  rw [hfi, hfj, sub_zero] at hdvd
  exact isUnit_of_dvd_one hdvd

/-- **Hermite interpolation over a commutative ring**: `hermiteJet a m` is bijective if and only if
`a i - a j` is a unit whenever `i ≠ j` and both `m i` and `m j` are nonzero. -/
theorem hermiteJet_bijective_iff (a : ι → R) (m : ι → ℕ) :
    Function.Bijective (hermiteJet a m) ↔
      ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  refine ⟨fun hbij i j hij hmi hmj => ?_, fun ha => ?_⟩
  · refine isUnit_sub_of_hermiteJetEval_surjective (fun c => ?_) hij hmi hmj
    obtain ⟨p, hp⟩ := hbij.2 c
    exact ⟨(p : R[X]), hp⟩
  · refine ⟨LinearMap.ker_eq_bot.mp (ker_hermiteJet ha), fun c => ?_⟩
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact ⟨0, Subsingleton.elim _ _⟩
    obtain ⟨f, hf⟩ := hermiteJetEval_surjective ha c
    set P := ∏ i, (X - C (a i)) ^ m i
    have hP : P.Monic := monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
    have hPdeg : P.natDegree = ∑ i, m i := by
      rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _]
      simp [(monic_X_sub_C _).natDegree_pow]
    exact ⟨⟨f %ₘ P, hPdeg ▸ modByMonic_mem_degreeLT hP f⟩,
      (hermiteJetEval_modByMonic_prod_X_sub_C_pow ha f).trans hf⟩

/-- **Hermite interpolation**: over any field, for injective nodes `a` and any multiplicity vector
`m`, the Hermite jet map `hermiteJet a m` on `degreeLT K (∑ i, m i)` is bijective. -/
theorem hermiteJet_bijective {K : Type*} [Field K] {a : ι → K} (ha : Function.Injective a)
    (m : ι → ℕ) : Function.Bijective (hermiteJet a m) :=
  (hermiteJet_bijective_iff a m).mpr fun _ _ hij _ _ => (sub_ne_zero_of_ne (ha.ne hij)).isUnit

/-- The `R`-linear equivalence `degreeLT R (∑ i, m i) ≃ₗ[R] ∀ i, Fin (m i) → R` given by
`hermiteJet a m` when `a i - a j` is a unit for distinct nodes of nonzero multiplicity. -/
noncomputable def hermiteEquiv {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    degreeLT R (∑ i, m i) ≃ₗ[R] ∀ i, Fin (m i) → R :=
  LinearEquiv.ofBijective (hermiteJet a m) ((hermiteJet_bijective_iff a m).mpr ha)

@[simp]
theorem hermiteEquiv_apply {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (p : degreeLT R (∑ i, m i)) :
    hermiteEquiv ha p = hermiteJet a m p :=
  (rfl)

/-- The Hermite interpolation linear map `(∀ i, Fin (m i) → R) →ₗ[R] R[X]` sending jet data `c` to
the unique polynomial in `degreeLT R (∑ i, m i)` with Hasse jets `c`. -/
noncomputable def hermiteInterpolate {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    (∀ i, Fin (m i) → R) →ₗ[R] R[X] :=
  (degreeLT R (∑ i, m i)).subtype.comp (hermiteEquiv ha).symm.toLinearMap

@[simp]
theorem coe_hermiteEquiv_symm_apply {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    ((hermiteEquiv ha).symm c : R[X]) = hermiteInterpolate ha c :=
  (rfl)

theorem hermiteInterpolate_mem_degreeLT {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    hermiteInterpolate ha c ∈ degreeLT R (∑ i, m i) :=
  ((hermiteEquiv ha).symm c).2

theorem degree_hermiteInterpolate_lt {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    (hermiteInterpolate ha c).degree < ∑ i, m i :=
  mem_degreeLT.mp (hermiteInterpolate_mem_degreeLT ha c)

@[simp]
theorem eval_hasseDeriv_hermiteInterpolate {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) (i : ι) (k : Fin (m i)) :
    (hasseDeriv (k : ℕ) (hermiteInterpolate ha c)).eval (a i) = c i k := by
  have h := congrFun (congrFun ((hermiteEquiv ha).apply_symm_apply c) i) k
  rwa [hermiteEquiv_apply, hermiteJet_apply, coe_hermiteEquiv_symm_apply] at h

@[simp]
theorem hermiteJetEval_hermiteInterpolate {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    hermiteJetEval a m (hermiteInterpolate ha c) = c := by
  ext i k
  exact eval_hasseDeriv_hermiteInterpolate ha c i k

@[simp]
theorem quotientSpanProdXSubCPowEquiv_symm_apply {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    (quotientSpanProdXSubCPowEquiv ha).symm c =
      Ideal.Quotient.mk (Ideal.span {∏ i, (X - C (a i)) ^ m i}) (hermiteInterpolate ha c) := by
  apply (quotientSpanProdXSubCPowEquiv ha).injective
  rw [LinearEquiv.apply_symm_apply]
  ext i k
  rw [quotientSpanProdXSubCPowEquiv_mk, eval_hasseDeriv_hermiteInterpolate]

/-- Characteristic property of `hermiteInterpolate`: a polynomial `f` equals
`hermiteInterpolate ha c` if and only if `f ∈ degreeLT R (∑ i, m i)` and its Hasse jets match `c`.
-/
theorem eq_hermiteInterpolate_iff {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    {f : R[X]} {c : ∀ i, Fin (m i) → R} :
    f = hermiteInterpolate ha c ↔
      f ∈ degreeLT R (∑ i, m i) ∧
        ∀ i (k : Fin (m i)), (hasseDeriv (k : ℕ) f).eval (a i) = c i k := by
  refine ⟨fun hf => ⟨hf ▸ hermiteInterpolate_mem_degreeLT ha c,
    fun i k => hf ▸ eval_hasseDeriv_hermiteInterpolate ha c i k⟩, fun ⟨hf, hjet⟩ => ?_⟩
  have heq : hermiteEquiv ha ⟨f, hf⟩ = c := by
    ext i k
    exact hjet i k
  exact congrArg Subtype.val ((hermiteEquiv ha).eq_symm_apply.mpr heq)

/-- Unique existence of the Hermite interpolating polynomial in `degreeLT R (∑ i, m i)`. -/
theorem existsUnique_mem_degreeLT_hermiteJetEval_eq {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    ∃! f : R[X], f ∈ degreeLT R (∑ i, m i) ∧ hermiteJetEval a m f = c := by
  refine ⟨hermiteInterpolate ha c,
    ⟨hermiteInterpolate_mem_degreeLT ha c, hermiteJetEval_hermiteInterpolate ha c⟩, ?_⟩
  rintro f ⟨hf, rfl⟩
  exact (eq_hermiteInterpolate_iff ha).mpr ⟨hf, fun _ _ => rfl⟩

/-- Interpolating the Hasse jets of an arbitrary polynomial `f : R[X]` computes its remainder
`f %ₘ (∏ i, (X - C (a i)) ^ m i)` modulo the product of the local factors. -/
theorem hermiteInterpolate_hermiteJetEval {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) (f : R[X]) :
    hermiteInterpolate ha (hermiteJetEval a m f) = f %ₘ ∏ i, (X - C (a i)) ^ m i := by
  nontriviality R
  symm
  rw [eq_hermiteInterpolate_iff ha]
  set P := ∏ i, (X - C (a i)) ^ m i
  have hP : P.Monic := monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
  have hPdeg : P.natDegree = ∑ i, m i := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _]
    simp [(monic_X_sub_C _).natDegree_pow]
  exact ⟨hPdeg ▸ modByMonic_mem_degreeLT hP f,
    fun i k => congrFun (congrFun (hermiteJetEval_modByMonic_prod_X_sub_C_pow ha f) i) k⟩

/-- **Naturality of Hermite interpolation under ring homomorphisms**: mapping the Hermite
interpolant along `ψ : R →+* S` produces the Hermite interpolant at the mapped nodes `ψ ∘ a` for
the mapped jet values. In particular, if nodes and jet values in an extension `L` lie in the image
of `K →+* L`, the interpolating polynomial over `L` has coefficients in `K`. -/
theorem map_hermiteInterpolate {S : Type*} [CommRing S] (ψ : R →+* S) {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    (hermiteInterpolate ha c).map ψ =
      hermiteInterpolate (a := ψ ∘ a) (m := m)
        (fun _ _ hij hmi hmj => by simpa [map_sub] using (ha hij hmi hmj).map ψ)
        (fun i k => ψ (c i k)) := by
  rw [eq_hermiteInterpolate_iff]
  refine ⟨mem_degreeLT.mpr (degree_map_le.trans_lt (degree_hermiteInterpolate_lt ha c)),
    fun i k => ?_⟩
  rw [Function.comp_apply, hasseDeriv_map, eval_map_apply, eval_hasseDeriv_hermiteInterpolate]

/-- The basis of `degreeLT R (∑ i, m i)` dual to the Hasse jet functionals
`(i, k) ↦ (hasseDeriv k ·).eval (a i)`, whose `⟨i, k⟩` vector is the unique polynomial of degree
`< ∑ i, m i` with `⟨i, k⟩` Hasse jet `1` and all other prescribed Hasse jets `0`. -/
noncomputable def hermiteBasis {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) :
    Module.Basis ((i : ι) × Fin (m i)) R (degreeLT R (∑ i, m i)) :=
  (Pi.basis fun i => Pi.basisFun R (Fin (m i))).map (hermiteEquiv ha).symm

@[simp]
theorem hermiteBasis_repr_apply {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (p : degreeLT R (∑ i, m i)) (x : (i : ι) × Fin (m i)) :
    (hermiteBasis ha).repr p x = (hasseDeriv (x.2 : ℕ) (p : R[X])).eval (a x.1) := by
  simp [hermiteBasis, Pi.basis_repr]

/-- Each adapted basis vector `hermiteBasis ha x` is the Hermite interpolant of the unit jet
supported at `x = ⟨x.1, x.2⟩`. -/
theorem coe_hermiteBasis [DecidableEq ι] {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (x : (i : ι) × Fin (m i)) :
    (hermiteBasis ha x : R[X]) = hermiteInterpolate ha (Pi.single x.1 (Pi.single x.2 1)) := by
  simp [hermiteBasis, Pi.basis_apply]

/-- Kronecker duality between `hermiteBasis` and the Hasse jet functionals. -/
theorem eval_hasseDeriv_hermiteBasis [DecidableEq ι] {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (x y : (i : ι) × Fin (m i)) :
    (hasseDeriv (y.2 : ℕ) (hermiteBasis ha x : R[X])).eval (a y.1) = if x = y then 1 else 0 := by
  rw [← hermiteBasis_repr_apply ha (hermiteBasis ha x) y, Module.Basis.repr_self,
    Finsupp.single_apply]

@[simp]
theorem eval_hasseDeriv_hermiteBasis_self {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (x : (i : ι) × Fin (m i)) :
    (hasseDeriv (x.2 : ℕ) (hermiteBasis ha x : R[X])).eval (a x.1) = 1 := by
  classical
  simp [eval_hasseDeriv_hermiteBasis]

theorem eval_hasseDeriv_hermiteBasis_of_ne {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    {x y : (i : ι) × Fin (m i)} (hxy : x ≠ y) :
    (hasseDeriv (y.2 : ℕ) (hermiteBasis ha x : R[X])).eval (a y.1) = 0 := by
  classical
  simp [eval_hasseDeriv_hermiteBasis, hxy]

/-- Every polynomial in `degreeLT R (∑ i, m i)` expands in `hermiteBasis` with its Hasse jets as
coordinates. -/
theorem sum_eval_hasseDeriv_smul_hermiteBasis {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (p : degreeLT R (∑ i, m i)) :
    (∑ x : (i : ι) × Fin (m i),
        (hasseDeriv (x.2 : ℕ) (p : R[X])).eval (a x.1) • hermiteBasis ha x) = p := by
  simpa [hermiteBasis_repr_apply] using (hermiteBasis ha).sum_repr p

/-- Explicit expansion of `hermiteInterpolate ha c` in the adapted basis `hermiteBasis ha`. -/
theorem hermiteInterpolate_eq_sum {a : ι → R} {m : ι → ℕ}
    (ha : ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j))
    (c : ∀ i, Fin (m i) → R) :
    hermiteInterpolate ha c =
      ∑ x : (i : ι) × Fin (m i), c x.1 x.2 • (hermiteBasis ha x : R[X]) := by
  have h := congrArg Subtype.val
    (sum_eval_hasseDeriv_smul_hermiteBasis ha ((hermiteEquiv ha).symm c))
  simpa [Submodule.coe_sum] using h.symm

end HermiteInterpolation

/-! ### Specialization to Lagrange interpolation for simple nodes -/

section LagrangeComparison

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- When every multiplicity is `1`, Hermite interpolation on a finite set `s` of injective nodes
coincides with `Lagrange.interpolate`. -/
theorem hermiteInterpolate_one_eq_lagrangeInterpolate (s : Finset ι) (v : ι → K)
    (hvs : Set.InjOn v s) (r : ι → K) :
    hermiteInterpolate (a := fun i : s => v i) (m := fun _ => 1)
        (fun i j hij _ _ =>
          (sub_ne_zero_of_ne (mt (hvs i.2 j.2) (Subtype.ext_iff.not.mp hij))).isUnit)
        (fun i _ => r i) =
      Lagrange.interpolate s v r := by
  let ha : ∀ ⦃i j : s⦄, i ≠ j → (1 : ℕ) ≠ 0 → (1 : ℕ) ≠ 0 → IsUnit (v i - v j) :=
    fun i j hij _ _ => (sub_ne_zero_of_ne (mt (hvs i.2 j.2) (Subtype.ext_iff.not.mp hij))).isUnit
  have hdeg := degree_hermiteInterpolate_lt (a := fun i : s => v i) (m := fun _ => 1) ha
    (fun i _ => r i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_one] at hdeg
  refine Lagrange.eq_interpolate_of_eval_eq _ hvs hdeg fun i hi => ?_
  simpa using eval_hasseDeriv_hermiteInterpolate (a := fun j : s => v j) (m := fun _ => 1) ha
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

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- Over a commutative ring, the ordinary-derivative jet map `hermiteOrdinaryJet a m` is bijective
if and only if `a i - a j` is a unit for distinct nodes of nonzero multiplicity and `(k : ℕ)!` is
a unit in `R` for every `i : ι` and `k : Fin (m i)`. -/
theorem hermiteOrdinaryJet_bijective_iff (a : ι → R) (m : ι → ℕ) :
    Function.Bijective (hermiteOrdinaryJet a m) ↔
      (∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j)) ∧
        ∀ i (k : Fin (m i)), IsUnit (((k : ℕ)! : R)) := by
  let diag : (∀ i, Fin (m i) → R) → (∀ i, Fin (m i) → R) :=
    fun c i k => ((k : ℕ)! : R) * c i k
  have hcomp : ⇑(hermiteOrdinaryJet a m) = diag ∘ ⇑(hermiteJet a m) := by
    ext p i k
    exact hermiteOrdinaryJet_apply_eq_factorial_mul a m p i k
  have hdiag_bij : (∀ i (k : Fin (m i)), IsUnit (((k : ℕ)! : R))) → Function.Bijective diag := by
    intro hu
    refine ⟨fun c₁ c₂ h => ?_, fun c => ?_⟩
    · ext i k
      exact (hu i k).mul_left_cancel (congrFun (congrFun h i) k)
    · refine ⟨fun i k => ↑(hu i k).unit⁻¹ * c i k, ?_⟩
      ext i k
      simp [diag, ← mul_assoc]
  refine ⟨fun hbij => ?_, fun ⟨ha, hu⟩ => ?_⟩
  · have hu : ∀ i (k : Fin (m i)), IsUnit (((k : ℕ)! : R)) := by
      classical
      intro i k
      obtain ⟨p, hp⟩ := hbij.2 (Pi.single i (Pi.single k 1))
      have hpk := congrFun (congrFun hp i) k
      rw [hermiteOrdinaryJet_apply_eq_factorial_mul, Pi.single_eq_same, Pi.single_eq_same] at hpk
      exact isUnit_iff_exists_inv.mpr ⟨hermiteJet a m p i k, hpk⟩
    have hjet_bij : Function.Bijective (hermiteJet a m) := by
      rw [hcomp] at hbij
      exact (Function.Bijective.of_comp_iff' (hdiag_bij hu) _).mp hbij
    exact ⟨(hermiteJet_bijective_iff a m).mp hjet_bij, hu⟩
  · rw [hcomp]
    exact (hdiag_bij hu).comp ((hermiteJet_bijective_iff a m).mpr ha)

/-- Over a field of characteristic zero, the ordinary-derivative Hermite jet map is bijective for
injective nodes and arbitrary multiplicities. -/
theorem hermiteOrdinaryJet_bijective_of_charZero {K : Type*} [Field K] [CharZero K]
    {a : ι → K} (ha : Function.Injective a) (m : ι → ℕ) :
    Function.Bijective (hermiteOrdinaryJet a m) := by
  rw [hermiteOrdinaryJet_bijective_iff]
  refine ⟨(hermiteJet_bijective_iff a m).mp (hermiteJet_bijective ha m), fun i k => ?_⟩
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)).isUnit

/-- Over a field of prime characteristic `p` with injective nodes, the ordinary-derivative Hermite
jet map is bijective if and only if every multiplicity satisfies `m i ≤ p` (so every jet order `k`
satisfies `k < p` and `k !` is invertible in `K`). -/
theorem hermiteOrdinaryJet_bijective_charP_iff {K : Type*} [Field K] {p : ℕ}
    [hp : Fact (Nat.Prime p)] [CharP K p] {a : ι → K} (ha : Function.Injective a) (m : ι → ℕ) :
    Function.Bijective (hermiteOrdinaryJet a m) ↔ ∀ i, m i ≤ p := by
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

variable {R : Type*} [CommRing R] {r : ℕ}

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
    Pi.basisFun_repr, hermiteJet_apply, degreeLT.basis_val, Matrix.confluentVandermonde_apply]

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
    Pi.basisFun_repr, hermiteOrdinaryJet_apply, degreeLT.basis_val, Matrix.of_apply]

end MatrixBridge

/-! ### Checks -/

section Checks

/-- Single node `r`: `hermiteInterpolate` at multiplicity `n` over any commutative ring
reconstructs the truncated Taylor expansion `∑ k : Fin n, C (c 0 k) * (X - C r) ^ k`. -/
example {R : Type*} [CommRing R] (r : R) (n : ℕ) (c : ∀ i : Fin 1, Fin ((fun _ => n) i) → R) :
    hermiteInterpolate (a := ![r]) (m := fun _ => n)
        (fun i j hij => absurd (Subsingleton.elim i j) hij) c =
      ∑ k : Fin n, C (c 0 k) * (X - C r) ^ (k : ℕ) := by
  symm
  rw [eq_hermiteInterpolate_iff]
  refine ⟨?_, fun i k => ?_⟩
  · refine Submodule.sum_mem _ fun k _ => ?_
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
    hermiteInterpolate (a := ![(0 : ℤ), 1]) (m := ![2, 1])
        (by
          intro i j hij _ _
          fin_cases i <;> fin_cases j <;> simp_all)
        (Fin.cases (motive := fun i => Fin (![2, 1] i) → ℤ) ![(1 : ℤ), 0]
          (Fin.cases ![(0 : ℤ)] fun i => Fin.elim0 i)) =
      1 - X ^ 2 := by
  symm
  rw [eq_hermiteInterpolate_iff]
  refine ⟨?_, fun i k => ?_⟩
  · rw [mem_degreeLT]
    refine (degree_sub_le _ _).trans_lt ?_
    simp only [degree_one, degree_X_pow, Fin.sum_univ_two]
    decide
  · fin_cases i <;> fin_cases k <;> simp [← monomial_one_right_eq_X_pow] <;> rfl

/-- Empty node family (`r = 0`): `degreeLT ℤ 0 = ⊥` and `hermiteJet` is bijective between two
trivial modules. -/
example (a : Fin 0 → ℤ) (m : Fin 0 → ℕ) : Function.Bijective (hermiteJet a m) :=
  (hermiteJet_bijective_iff a m).mpr fun i => Fin.elim0 i

/-- Repeated node of multiplicity `0`: `![0, 0, 1]` is not injective, yet `![1, 0, 1]` satisfies
the unit-difference criterion over `ℤ` and `hermiteJet` is bijective. -/
example :
    ¬ Function.Injective ![(0 : ℤ), 0, 1] ∧
      Function.Bijective (hermiteJet ![(0 : ℤ), 0, 1] ![1, 0, 1]) := by
  refine ⟨fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide), ?_⟩
  rw [hermiteJet_bijective_iff]
  intro i j hij hmi hmj
  fin_cases i <;> fin_cases j <;> simp_all

private local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Characteristic `2` at `![0]`, `![3]`: `hermiteJet` is bijective over `ZMod 2`, whereas
`hermiteOrdinaryJet` is NOT bijective because `2! = 0` in `ZMod 2` (`X ^ 2` lies in its kernel). -/
example :
    Function.Bijective (hermiteJet ![(0 : ZMod 2)] ![3]) ∧
      ¬ Function.Bijective (hermiteOrdinaryJet ![(0 : ZMod 2)] ![3]) := by
  have hinj : Function.Injective ![(0 : ZMod 2)] := Function.injective_of_subsingleton _
  refine ⟨hermiteJet_bijective hinj ![3], ?_⟩
  rw [hermiteOrdinaryJet_bijective_charP_iff hinj]
  decide

/-- Characteristic `2` at `![0, 1]`, `![2, 2]`: every multiplicity satisfies `m i ≤ 2`, so even
`hermiteOrdinaryJet` is bijective over `ZMod 2`. -/
example : Function.Bijective (hermiteOrdinaryJet ![(0 : ZMod 2), 1] ![2, 2]) := by
  have hinj : Function.Injective ![(0 : ZMod 2), 1] := by decide
  rw [hermiteOrdinaryJet_bijective_charP_iff hinj]
  decide

end Checks

end Polynomial
