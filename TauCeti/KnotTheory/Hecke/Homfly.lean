/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.KnotTheory.Hecke
public import TauCeti.KnotTheory.Hecke.Jimbo
public import TauCeti.KnotTheory.Homfly.Alexander
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

/-!
# Comparison between Hecke Markov braid traces and the HOMFLY polynomial

This file connects the normalized universal Hecke braid trace `MarkovBraid.heckeTrace` and its
Ocneanu-trace specialization to the two-variable HOMFLY polynomial `MarkovBraid.reducedHomfly`,
constructs the quadratic coefficient extension needed to choose the Markov normalization root, and
establishes regularity across both apparent zero-factor loci before evaluating specializations
there:

1. **Quadratic root extension (`heckeRootPoly`, `heckeRootUnit`,
   `heckeNormalization_adjoinRoot`)**: for any commutative ring `R` and unit stabilization
   constants `a, b : Rˣ`, adjoining a root of `X ^ 2 - b * a⁻¹` embeds `R` injectively and
   supplies an explicit unit `l` with `l ^ 2 = b * a⁻¹` and `C = (l * a)⁻¹` solving both Markov
   normalization equations.
2. **Naturality and one-dimensional characters (`MarkovBraid.map_heckeTrace_ocneanuTrace`,
   `MarkovBraid.heckeTrace_ocneanuTrace_index`, `MarkovBraid.heckeTrace_ocneanuTrace_sign`)**:
   `heckeTrace` for `ocneanuTrace` commutes with ring homomorphisms, and at `z = q` (`l = q⁻¹`) or
   `z = -q⁻¹` (`l = -q`) evaluates identically to `1` over any commutative ring (including at
   `q = ±1`).
3. **Two-variable HOMFLY comparison (`MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`)**: whenever
   `u = q - q⁻¹` is a unit and `(C, l, z)` satisfies both Markov normalization equations for a
   Markov trace `τ`, evaluating `β.reducedHomfly K` at outer variable `l⁻¹` and inner variable `u`
   equals `β.heckeTrace τ C l`.
4. **Regularity and evaluation across zero-factor specializations**:
   * **Across `l⁻¹ - l = 0` (`C = 0`, Alexander specialization)**: in `heckeUniversalRing K`
     (inverting both `q - q⁻¹` and `a - a⁻¹ = l⁻¹ - l`), the normalized Ocneanu trace equals the
     image under the injective localization map `heckeAlexanderInclusion K` of the regular element
     `MarkovBraid.heckeAlexanderRegular K` in `heckeAlexanderRegularRing K` (which inverts
     `q - q⁻¹` alone); evaluating that unique regular extension at `a = 1` (`l = 1`) and `q = s⁻¹`
     recovers `MarkovBraid.normalizedBurauAlexander s`.
   * **Across `q - q⁻¹ = 0` (`q = ±1`, classical specialization)**: whenever
     `l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))` in `LaurentPolynomial K` with `C₀ ≠ 0`, the generic HOMFLY
     specialization in `Localization.Away (C₀ * (T 1 - T (-1)))` equals the image under the
     injective localization map `heckeZeroFactorLift C₀` of `heckeTrace` over
     `Localization.Away C₀`; evaluating that unique regular extension at any `q` with
     `eval₂ φ q C₀` invertible (including `q = ±1`) yields `heckeTrace` at `q`, and
     `jimboWeight_sum_genericUnit_ne_zero` shows `C₀ = [N + 1]_q ≠ 0` over every nontrivial
     commutative ring.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Sections 5–6 and 11–12.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 3 and 6.
-/

public noncomputable section

namespace TauCeti

open BraidGroup KnotTheory LaurentPolynomial
open InfiniteTypeAHeckeAlgebra (IsMarkovTrace ocneanuTrace isMarkovTrace_ocneanuTrace)
open scoped BigOperators

/-! ### Quadratic coefficient extension for Markov normalization -/

section RootExtension

variable {R : Type*} [CommRing R]

/-- The monic quadratic polynomial `X ^ 2 - b * a⁻¹` adjoining the writhe normalization root `l`
for unit positive and negative Markov stabilization constants `a, b : Rˣ`. -/
def heckeRootPoly (a b : Rˣ) : Polynomial R :=
  Polynomial.X ^ 2 - Polynomial.C (↑(b * a⁻¹) : R)

/-- `heckeRootPoly a b` is monic. -/
theorem monic_heckeRootPoly (a b : Rˣ) : (heckeRootPoly a b).Monic :=
  Polynomial.monic_X_pow_sub_C (↑(b * a⁻¹) : R) (by decide)

/-- The canonical coefficient map `R →+* AdjoinRoot (heckeRootPoly a b)` is injective over every
commutative ring `R`. -/
theorem of_heckeRootPoly_injective (a b : Rˣ) :
    Function.Injective (AdjoinRoot.of (heckeRootPoly a b)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Function.injective_of_subsingleton _
  · have hm := monic_heckeRootPoly a b
    refine AdjoinRoot.of.injective_of_monic_of_degree_pos hm ?_
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, heckeRootPoly, Polynomial.natDegree_X_pow_sub_C]
    decide

/-- In `AdjoinRoot (heckeRootPoly a b)`, the adjoined root squares to the image of `b * a⁻¹`. -/
theorem heckeRoot_sq (a b : Rˣ) :
    AdjoinRoot.root (heckeRootPoly a b) ^ 2 =
      AdjoinRoot.of (heckeRootPoly a b) (↑(b * a⁻¹) : R) := by
  have h := AdjoinRoot.eval₂_root (heckeRootPoly a b)
  conv at h => arg 1; arg 3; rw [heckeRootPoly]
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The adjoined writhe root in `AdjoinRoot (heckeRootPoly a b)` as a unit. -/
def heckeRootUnit (a b : Rˣ) : (AdjoinRoot (heckeRootPoly a b))ˣ where
  val := AdjoinRoot.root (heckeRootPoly a b)
  inv := AdjoinRoot.root (heckeRootPoly a b) * AdjoinRoot.of (heckeRootPoly a b) (↑(a * b⁻¹) : R)
  val_inv := by
    have hmul : (b * a⁻¹) * (a * b⁻¹) = 1 := by simp [mul_left_comm]
    rw [← mul_assoc, ← sq, heckeRoot_sq, ← map_mul, ← Units.val_mul, hmul, Units.val_one, map_one]
  inv_val := by
    have hmul : (b * a⁻¹) * (a * b⁻¹) = 1 := by simp [mul_left_comm]
    calc AdjoinRoot.root (heckeRootPoly a b) *
          AdjoinRoot.of (heckeRootPoly a b) (↑(a * b⁻¹) : R) *
          AdjoinRoot.root (heckeRootPoly a b)
        = AdjoinRoot.root (heckeRootPoly a b) ^ 2 *
            AdjoinRoot.of (heckeRootPoly a b) (↑(a * b⁻¹) : R) := by ring
      _ = 1 := by rw [heckeRoot_sq, ← map_mul, ← Units.val_mul, hmul, Units.val_one, map_one]

/-- Coercing `heckeRootUnit a b` gives the adjoined root. -/
@[simp]
theorem val_heckeRootUnit (a b : Rˣ) :
    (heckeRootUnit a b : AdjoinRoot (heckeRootPoly a b)) =
      AdjoinRoot.root (heckeRootPoly a b) :=
  (rfl)

/-- `heckeRootUnit a b` squares to the mapped unit `b * a⁻¹`. -/
theorem heckeRootUnit_sq (a b : Rˣ) :
    heckeRootUnit a b ^ 2 =
      Units.map (AdjoinRoot.of (heckeRootPoly a b)).toMonoidHom (b * a⁻¹) :=
  Units.ext (heckeRoot_sq a b)

/-- **Markov normalization in the quadratic root extension.** Over `AdjoinRoot (heckeRootPoly a b)`,
`l = heckeRootUnit a b` and `C = (l * a)⁻¹` satisfy both positive and negative Markov
normalization equations for the mapped stabilization constants `a` and `b`. -/
theorem heckeNormalization_adjoinRoot (a b : Rˣ) :
    (↑((heckeRootUnit a b * Units.map (AdjoinRoot.of (heckeRootPoly a b)).toMonoidHom a)⁻¹) :
        AdjoinRoot (heckeRootPoly a b)) *
      (heckeRootUnit a b : AdjoinRoot (heckeRootPoly a b)) *
      AdjoinRoot.of (heckeRootPoly a b) a = 1 ∧
    (↑((heckeRootUnit a b * Units.map (AdjoinRoot.of (heckeRootPoly a b)).toMonoidHom a)⁻¹) :
        AdjoinRoot (heckeRootPoly a b)) *
      (↑(heckeRootUnit a b)⁻¹ : AdjoinRoot (heckeRootPoly a b)) *
      AdjoinRoot.of (heckeRootPoly a b) b = 1 := by
  have hsq : heckeRootUnit a b ^ 2 =
      Units.map (AdjoinRoot.of (heckeRootPoly a b)).toMonoidHom b *
        (Units.map (AdjoinRoot.of (heckeRootPoly a b)).toMonoidHom a)⁻¹ := by
    rw [heckeRootUnit_sq, map_mul, map_inv]
  exact heckeNormalization_of_sq_eq hsq

end RootExtension

/-! ### Naturality and one-dimensional character specializations -/

namespace MarkovBraid

/-- **Base-change naturality of the normalized Ocneanu braid trace.** Every ring homomorphism
`f : R →+* S` commutes with `heckeTrace` applied to `ocneanuTrace`. -/
theorem map_heckeTrace_ocneanuTrace {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : Rˣ) (z C : R) (l : Rˣ) (β : MarkovBraid) :
    f (β.heckeTrace (ocneanuTrace R q z) C l) =
      β.heckeTrace (ocneanuTrace S (Units.map f.toMonoidHom q) (f z))
        (f C) (Units.map f.toMonoidHom l) := by
  simp only [heckeTrace_def, map_mul, map_pow, InfiniteTypeAHeckeAlgebra.map_ocneanuTrace_braidHom]
  congr 2
  exact (Units.coe_map (f : R →* S) (l ^ _)).symm.trans
    (congrArg Units.val (map_zpow (Units.map (f : R →* S)) l _))

/-- **Index-character specialization (`z = q`, `C = 1`, `l = q⁻¹`).** Over any commutative ring `R`
and for any `q : Rˣ` (including `q = ±1`), the normalized Ocneanu trace at `(z, C, l) = (q, 1, q⁻¹)`
is identically `1`. -/
@[simp]
theorem heckeTrace_ocneanuTrace_index {R : Type*} [CommRing R] (q : Rˣ) (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R q (q : R)) 1 q⁻¹ = 1 := by
  have hpos : (1 : R) * ↑(q⁻¹ : Rˣ) * (q : R) = 1 := by
    simpa only [one_mul] using Units.inv_mul q
  have hneg : (1 : R) * ↑((q⁻¹ : Rˣ)⁻¹) * ((q : R) - ((q : R) - ↑q⁻¹)) = 1 := by
    rw [inv_inv, sub_sub_cancel, one_mul]
    exact Units.mul_inv q
  have heq := eq_heckeTrace_of_skein (isMarkovTrace_ocneanuTrace (q : R)) hpos hneg
    (F := fun _ ↦ (1 : R)) (fun _ _ _ ↦ rfl)
    (fun _ _ _ ↦ by simp) (fun _ _ ↦ by simp) rfl
  exact (congrFun heq β).symm

/-- **Sign-character specialization (`z = -q⁻¹`, `C = 1`, `l = -q`).** Over any commutative ring `R`
and for any `q : Rˣ` (including `q = ±1`), the normalized Ocneanu trace at
`(z, C, l) = (-q⁻¹, 1, -q)` is identically `1`. -/
@[simp]
theorem heckeTrace_ocneanuTrace_sign {R : Type*} [CommRing R] (q : Rˣ) (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R q (-(↑q⁻¹ : R))) 1 (-q) = 1 := by
  have hinv : (↑((-q : Rˣ)⁻¹) : R) = -(↑q⁻¹ : R) := by
    apply (Units.mul_right_inj (-q)).mp
    rw [Units.mul_inv, Units.val_neg, neg_mul_neg, Units.mul_inv]
  have hpos : (1 : R) * ↑(-q : Rˣ) * (-(↑q⁻¹ : R)) = 1 := by
    rw [Units.val_neg, one_mul, neg_mul_neg]
    exact Units.mul_inv q
  have hneg : (1 : R) * ↑((-q : Rˣ)⁻¹) * (-(↑q⁻¹ : R) - ((q : R) - ↑q⁻¹)) = 1 := by
    rw [hinv, one_mul, show -(↑q⁻¹ : R) - ((q : R) - ↑q⁻¹) = -(q : R) by ring, neg_mul_neg]
    exact Units.inv_mul q
  have heq := eq_heckeTrace_of_skein (isMarkovTrace_ocneanuTrace (-(↑q⁻¹ : R))) hpos hneg
    (F := fun _ ↦ (1 : R)) (fun _ _ _ ↦ rfl)
    (fun _ _ _ ↦ by rw [hinv, Units.val_neg]; ring)
    (fun _ _ ↦ by simp) rfl
  exact (congrFun heq β).symm

end MarkovBraid

/-! ### Comparison with the two-variable HOMFLY polynomial -/

section HomflyComparison

variable {K R : Type*} [Field K] [CommRing R]

/-- Under the Markov normalization equations `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1` with unit skein factor `u = q - q⁻¹`, the unreduced HOMFLY unknot
polynomial `(a - a⁻¹) / u` specializes at `(a, u) = (l⁻¹, q - q⁻¹)` to the unlink factor `C`. -/
theorem KnotTheory.eval₂_homflyUnknot_of_heckeNormalization (φ : K →+* R) {q u l : Rˣ} {C z : R}
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  have hCu : C * (u : R) = (↑l⁻¹ : R) - l := by
    rw [hu]
    exact heckeNormalization_mul_sub hpos hneg
  have heval : eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = ((↑l⁻¹ : R) - l) * ↑u⁻¹ := by
    simp [homflyUnknot_def, map_mul, map_sub]
  rw [heval, ← hCu, mul_assoc, Units.mul_inv, mul_one]

namespace MarkovBraid

/-- **Comparison between `reducedHomfly` and `heckeTrace`.** Whenever `u = q - q⁻¹` is a unit in `R`
and `(C, l, z)` solves the positive and negative Markov normalization equations for a Markov trace
`τ` on `InfiniteTypeAHeckeAlgebra R q`, evaluating `β.reducedHomfly K` at outer variable `l⁻¹` and
inner variable `u` recovers the normalized Hecke trace `β.heckeTrace τ C l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (φ : K →+* R) {q u l : Rˣ} {C z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) = β.heckeTrace τ C l := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) l⁻¹
  have heU : e (homflyUnknot K) = C :=
    KnotTheory.eval₂_homflyUnknot_of_heckeNormalization φ hu hpos hneg
  have heq := eq_heckeTrace_of_skein hτ hpos hneg
    (F := fun γ ↦ e (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun n c i ↦ by
      have hs := congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
      simpa only [e, one_mul, map_sub, map_mul, eval₂_T, zpow_one, zpow_neg_one, inv_inv,
        eval₂_C, hu] using hs)
    (fun n b ↦ by rw [reducedHomfly_strandIncl, map_mul, heU])
    (by simp [e])
  exact congrFun heq β

/-- Specialization of the unreduced HOMFLY polynomial `β.homfly K` at `(a, u) = (l⁻¹, q - q⁻¹)`
equals `C * β.heckeTrace τ C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace (φ : K →+* R) {q u l : Rˣ} {C z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) = C * β.heckeTrace τ C l := by
  rw [← homflyUnknot_mul_reducedHomfly, map_mul,
    KnotTheory.eval₂_homflyUnknot_of_heckeNormalization φ hu hpos hneg,
    β.eval₂_reducedHomfly_eq_heckeTrace φ hτ hu hpos hneg]

/-- Canonical specialization of `eval₂_reducedHomfly_eq_heckeTrace` to the algebraic Ocneanu trace
`ocneanuTrace R q z`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace (φ : K →+* R) {q u l : Rˣ} {C z : R}
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace (ocneanuTrace R q z) C l :=
  β.eval₂_reducedHomfly_eq_heckeTrace φ (isMarkovTrace_ocneanuTrace z) hu hpos hneg

end MarkovBraid

/-- On the quotient `Quot MarkovEquiv`, `heckeBraidInvariant` equals the descended specialization
of `reducedHomfly K` whenever `u = q - q⁻¹` is a unit. -/
theorem heckeBraidInvariant_eq_eval₂_reducedHomfly (φ : K →+* R) {q u l : Rˣ} {C z : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (x : Quot MarkovEquiv) :
    heckeBraidInvariant hτ C l hpos hneg x =
      Quot.lift (fun β : MarkovBraid ↦ eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K))
        (fun _ _ h ↦ congrArg _ (h.reducedHomfly_eq K)) x := by
  rcases Quot.exists_rep x with ⟨β, rfl⟩
  rw [heckeBraidInvariant_mk]
  exact (β.eval₂_reducedHomfly_eq_heckeTrace φ hτ hu hpos hneg).symm

end HomflyComparison

/-! ### Regularity and evaluation across zero-factor specializations -/

section ZeroFactorRegularity

/-- Over a commutative ring without zero divisors, localizing away from a divisor `x` of a nonzero
element `y` embeds injectively into the localization away from `y`. -/
private theorem away_lift_injective {A : Type*} [CommRing A] [NoZeroDivisors A] {x y : A}
    (hy : y ≠ 0) (hxy : x ∣ y) :
    Function.Injective (IsLocalization.Away.lift x
      (S := Localization.Away x) (g := algebraMap A (Localization.Away y))
      (IsLocalization.Away.isUnit_of_dvd y hxy)) := by
  let f : Localization.Away x →+* Localization.Away y :=
    IsLocalization.Away.lift x (IsLocalization.Away.isUnit_of_dvd y hxy)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, hza⟩ := IsLocalization.Away.surj x z
  have hfa : algebraMap A (Localization.Away y) a = algebraMap A (Localization.Away y) 0 := by
    have h0 := congrArg f hza
    rw [map_mul, hz, zero_mul] at h0
    rw [map_zero]
    simpa only [f, IsLocalization.Away.lift_eq] using h0.symm
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq y hfa
  rw [mul_zero] at hm
  have ha : a = 0 := (mul_eq_zero.mp hm).resolve_left (pow_ne_zero m hy)
  rw [ha, map_zero] at hza
  exact (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away x) x n).mul_right_cancel
    (hza.trans (zero_mul _).symm)

/-! #### 1. Regularity across `l⁻¹ - l = 0` (`C = 0`, Alexander specialization) -/

section AlexanderRegularity

variable (K : Type*) [Field K]

/-- The inner Hecke skein factor `q - q⁻¹` inside `K[q, q⁻¹][a, a⁻¹]`. -/
def heckeDeltaQ : LaurentPolynomial (LaurentPolynomial K) :=
  C (T 1 - T (-1))

/-- The outer writhe factor `a - a⁻¹ = l⁻¹ - l` inside `K[q, q⁻¹][a, a⁻¹]`, vanishing at the
Alexander specialization `a = 1`. -/
def heckeDeltaA : LaurentPolynomial (LaurentPolynomial K) :=
  T 1 - T (-1)

/-- The inner Hecke skein factor `heckeDeltaQ K` is nonzero. -/
theorem heckeDeltaQ_ne_zero : heckeDeltaQ K ≠ 0 := by
  intro h
  have hc : (T 1 - T (-1) : LaurentPolynomial K) = 0 := by
    simpa [heckeDeltaQ] using
      congrArg (eval₂ (RingHom.id (LaurentPolynomial K)) 1) h
  exact T_sub_T_ne_zero (by decide) hc

/-- The outer writhe factor `heckeDeltaA K` is nonzero. -/
theorem heckeDeltaA_ne_zero : heckeDeltaA K ≠ 0 := by
  rw [heckeDeltaA]
  exact T_sub_T_ne_zero (by decide)

/-- The localization `K[q, q⁻¹][a, a⁻¹][(q - q⁻¹)⁻¹]`, in which `a - a⁻¹ = l⁻¹ - l` is *not*
inverted and specialization to `a = ±1` (`C = 0`) is regular. -/
abbrev heckeAlexanderRegularRing : Type _ :=
  Localization.Away (heckeDeltaQ K)

/-- The universal localization `K[q, q⁻¹][a, a⁻¹][((q - q⁻¹)(a - a⁻¹))⁻¹]`, in which both generic
normalization denominators are units so `heckeTrace` is directly defined. -/
abbrev heckeUniversalRing : Type _ :=
  Localization.Away (heckeDeltaQ K * heckeDeltaA K)

/-- The canonical localization map from `heckeAlexanderRegularRing K` into `heckeUniversalRing K`.
Its injectivity guarantees uniqueness of regular extensions across `a - a⁻¹ = 0`. -/
def heckeAlexanderInclusion : heckeAlexanderRegularRing K →+* heckeUniversalRing K :=
  IsLocalization.Away.awayToAwayRight (heckeDeltaQ K) (heckeDeltaA K)

/-- `heckeAlexanderInclusion K` is injective, so any regular extension in
`heckeAlexanderRegularRing K` of the universal normalized Hecke trace is unique. -/
theorem heckeAlexanderInclusion_injective :
    Function.Injective (heckeAlexanderInclusion K) := by
  rw [heckeAlexanderInclusion, IsLocalization.Away.awayToAwayRight]
  exact away_lift_injective (mul_ne_zero (heckeDeltaQ_ne_zero K) (heckeDeltaA_ne_zero K))
    (dvd_mul_right _ _)

/-- The unit `q - q⁻¹` inside `heckeAlexanderRegularRing K`. -/
def heckeDeltaQUnit : (heckeAlexanderRegularRing K)ˣ where
  val := algebraMap _ (heckeAlexanderRegularRing K) (heckeDeltaQ K)
  inv := IsLocalization.Away.invSelf (heckeDeltaQ K)
  val_inv := IsLocalization.Away.mul_invSelf (heckeDeltaQ K)
  inv_val := by rw [mul_comm, IsLocalization.Away.mul_invSelf]

/-- The generic Hecke parameter `q` as a unit in `heckeUniversalRing K`. -/
def heckeUniversalQ : (heckeUniversalRing K)ˣ :=
  Units.map
    ((algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)).comp
      C).toMonoidHom
    (genericUnit K)

/-- The generic outer HOMFLY variable `a = l⁻¹` as a unit in `heckeUniversalRing K`. -/
def heckeUniversalA : (heckeUniversalRing K)ˣ :=
  Units.map
    (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)).toMonoidHom
    (genericUnit (LaurentPolynomial K))

/-- The generic unlink factor `C = (a - a⁻¹) * (q - q⁻¹)⁻¹` in `heckeUniversalRing K`. -/
def heckeUniversalC : heckeUniversalRing K :=
  algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (heckeDeltaA K) *
    ↑((Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K))⁻¹)

/-- The generic Ocneanu parameter `z = (a - a⁻¹)⁻¹ * (q - q⁻¹) * a` in `heckeUniversalRing K`. -/
def heckeUniversalZ : heckeUniversalRing K :=
  (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K) (heckeDeltaQ K) *
      IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K)) *
    ↑(Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)) *
    (heckeUniversalA K : heckeUniversalRing K)

/-- The generic parameters `(heckeUniversalC K, (heckeUniversalA K)⁻¹, heckeUniversalZ K)` satisfy
both Markov normalization equations in `heckeUniversalRing K`. -/
theorem heckeUniversalNormalization :
    heckeUniversalC K * ↑((heckeUniversalA K)⁻¹ : (heckeUniversalRing K)ˣ) *
        heckeUniversalZ K = 1 ∧
      heckeUniversalC K * ↑(((heckeUniversalA K)⁻¹ : (heckeUniversalRing K)ˣ)⁻¹) *
        (heckeUniversalZ K -
          ((heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹)) = 1 := by
  let ι := algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)
  let u_u : (heckeUniversalRing K)ˣ :=
    Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)
  let invΔa : heckeUniversalRing K :=
    ι (heckeDeltaQ K) * IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K)
  have hcomp : (heckeAlexanderInclusion K).comp
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)) = ι := by
    rw [heckeAlexanderInclusion, IsLocalization.Away.awayToAwayRight]
    exact IsLocalization.Away.lift_comp _ _
  have hΔa_inv : ι (heckeDeltaA K) * invΔa = 1 := by
    dsimp only [invΔa]
    calc ι (heckeDeltaA K) * (ι (heckeDeltaQ K) *
            IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K))
        = ι (heckeDeltaQ K * heckeDeltaA K) *
            IsLocalization.Away.invSelf (heckeDeltaQ K * heckeDeltaA K) := by
          rw [map_mul]
          ring
      _ = 1 := IsLocalization.Away.mul_invSelf _
  have hu_val : (u_u : heckeUniversalRing K) =
      (heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹ := by
    have h₁ : (u_u : heckeUniversalRing K) = ι (heckeDeltaQ K) := by
      simpa [u_u, heckeDeltaQUnit] using congrFun (congrArg DFunLike.coe hcomp) (heckeDeltaQ K)
    have h₂ : (heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹ =
        ι (heckeDeltaQ K) := by
      simp [ι, heckeUniversalQ, heckeDeltaQ, map_sub]
    exact h₁.trans h₂.symm
  have ha_sub : (heckeUniversalA K : heckeUniversalRing K) - ↑(heckeUniversalA K)⁻¹ =
      ι (heckeDeltaA K) := by
    simp [ι, heckeUniversalA, heckeDeltaA, map_sub]
  refine ⟨?_, ?_⟩
  · rw [heckeUniversalC, heckeUniversalZ]
    change (ι (heckeDeltaA K) * ↑u_u⁻¹) * ↑(heckeUniversalA K)⁻¹ *
      (invΔa * (u_u : heckeUniversalRing K) * (heckeUniversalA K : heckeUniversalRing K)) = 1
    linear_combination (↑u_u⁻¹ : heckeUniversalRing K) * (u_u : heckeUniversalRing K) *
        ↑(heckeUniversalA K)⁻¹ * (heckeUniversalA K : heckeUniversalRing K) * hΔa_inv +
      u_u.inv_mul * ↑(heckeUniversalA K)⁻¹ * (heckeUniversalA K : heckeUniversalRing K) +
      (heckeUniversalA K).inv_mul
  · rw [inv_inv, ← hu_val, heckeUniversalC, heckeUniversalZ]
    change (ι (heckeDeltaA K) * ↑u_u⁻¹) * (heckeUniversalA K : heckeUniversalRing K) *
      (invΔa * (u_u : heckeUniversalRing K) * (heckeUniversalA K : heckeUniversalRing K) -
        (u_u : heckeUniversalRing K)) = 1
    have hz_sub : invΔa * (u_u : heckeUniversalRing K) *
          (heckeUniversalA K : heckeUniversalRing K) - (u_u : heckeUniversalRing K) =
        invΔa * (u_u : heckeUniversalRing K) * ↑(heckeUniversalA K)⁻¹ := by
      linear_combination (u_u : heckeUniversalRing K) * hΔa_inv +
        invΔa * (u_u : heckeUniversalRing K) * ha_sub
    rw [hz_sub]
    linear_combination (↑u_u⁻¹ : heckeUniversalRing K) * (u_u : heckeUniversalRing K) *
        (heckeUniversalA K : heckeUniversalRing K) * ↑(heckeUniversalA K)⁻¹ * hΔa_inv +
      u_u.inv_mul * (heckeUniversalA K : heckeUniversalRing K) * ↑(heckeUniversalA K)⁻¹ +
      (heckeUniversalA K).mul_inv

/-- The regular two-variable element in `heckeAlexanderRegularRing K` extending the universal
normalized Hecke trace across `a - a⁻¹ = 0` (`l = ±1`, `C = 0`). -/
def MarkovBraid.heckeAlexanderRegular (β : MarkovBraid) : heckeAlexanderRegularRing K :=
  eval₂ (eval₂ (algebraMap K (heckeAlexanderRegularRing K)) (heckeDeltaQUnit K))
    (Units.map
      (algebraMap (LaurentPolynomial (LaurentPolynomial K))
        (heckeAlexanderRegularRing K)).toMonoidHom
      (genericUnit (LaurentPolynomial K)))
    (β.reducedHomfly K)

/-- **Regularity of the universal normalized Hecke trace across `l⁻¹ - l = 0` (`C = 0`).** Inside
`heckeUniversalRing K`, the normalized Ocneanu braid trace with generic parameters
`(heckeUniversalQ K, heckeUniversalZ K, heckeUniversalC K, (heckeUniversalA K)⁻¹)` equals the image
under the injective map `heckeAlexanderInclusion K` of `β.heckeAlexanderRegular K`. -/
theorem MarkovBraid.heckeAlexanderInclusion_heckeAlexanderRegular (β : MarkovBraid) :
    heckeAlexanderInclusion K (β.heckeAlexanderRegular K) =
      β.heckeTrace
        (ocneanuTrace (heckeUniversalRing K) (heckeUniversalQ K) (heckeUniversalZ K))
        (heckeUniversalC K) (heckeUniversalA K)⁻¹ := by
  let ι := algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeUniversalRing K)
  let u_u : (heckeUniversalRing K)ˣ :=
    Units.map (heckeAlexanderInclusion K).toMonoidHom (heckeDeltaQUnit K)
  have hcomp : (heckeAlexanderInclusion K).comp
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)) = ι := by
    rw [heckeAlexanderInclusion, IsLocalization.Away.awayToAwayRight]
    exact IsLocalization.Away.lift_comp _ _
  have hu_val : (u_u : heckeUniversalRing K) =
      (heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹ := by
    have h₁ : (u_u : heckeUniversalRing K) = ι (heckeDeltaQ K) := by
      simpa [u_u, heckeDeltaQUnit] using congrFun (congrArg DFunLike.coe hcomp) (heckeDeltaQ K)
    have h₂ : (heckeUniversalQ K : heckeUniversalRing K) - ↑(heckeUniversalQ K)⁻¹ =
        ι (heckeDeltaQ K) := by
      simp [ι, heckeUniversalQ, heckeDeltaQ, map_sub]
    exact h₁.trans h₂.symm
  obtain ⟨hpos, hneg⟩ := heckeUniversalNormalization K
  have heval : heckeAlexanderInclusion K (β.heckeAlexanderRegular K) =
      eval₂ (eval₂ (algebraMap K (heckeUniversalRing K)) u_u)
        ((heckeUniversalA K)⁻¹)⁻¹ (β.reducedHomfly K) := by
    rw [MarkovBraid.heckeAlexanderRegular, hom_eval₂, inv_inv]
    congr 2
    · refine RingHom.ext fun p ↦ ?_
      rw [RingHom.comp_apply, hom_eval₂]
      congr 2
      rw [IsScalarTower.algebraMap_eq K (LaurentPolynomial (LaurentPolynomial K))
          (heckeAlexanderRegularRing K),
        ← RingHom.comp_assoc, hcomp,
        ← IsScalarTower.algebraMap_eq K (LaurentPolynomial (LaurentPolynomial K))
          (heckeUniversalRing K)]
    · ext
      rw [Units.coe_map, Units.coe_map, heckeUniversalA, Units.coe_map]
      exact congrFun (congrArg DFunLike.coe hcomp)
        (genericUnit (LaurentPolynomial K) : LaurentPolynomial (LaurentPolynomial K))
  rw [heval]
  exact β.eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace _ hu_val hpos hneg

/-- When `u = s⁻¹ - s` is a unit in `R`, the Alexander evaluation map `q ↦ s⁻¹`, `a ↦ 1` sends
`heckeDeltaQ K` to a unit in `R`. -/
theorem isUnit_eval₂_heckeDeltaQ {R : Type*} [CommRing R] (φ : K →+* R) {s u : Rˣ}
    (hu : (u : R) = ((s⁻¹ : Rˣ) : R) - (s : R)) :
    IsUnit (eval₂ (eval₂ φ s⁻¹) 1 (heckeDeltaQ K)) := by
  have hval : eval₂ (eval₂ φ s⁻¹) 1 (heckeDeltaQ K) = (u : R) := by
    simp [heckeDeltaQ, hu]
  exact hval ▸ u.isUnit

/-- **Evaluation of the regular extension at `l = 1` (`C = 0`, Alexander specialization).** Given
any commutative ring `R`, `φ : K →+* R`, and units `s, u : Rˣ` with `u = s⁻¹ - s` (corresponding to
`q = s⁻¹` and `l = 1`, where `l⁻¹ - l = 0`), evaluating the unique regular extension
`β.heckeAlexanderRegular K` along `IsLocalization.Away.lift (heckeDeltaQ K)` recovers the
normalized Burau–Alexander invariant `β.normalizedBurauAlexander s`. -/
theorem MarkovBraid.lift_heckeAlexanderRegular_eq_normalizedBurauAlexander {R : Type*}
    [CommRing R] (φ : K →+* R) (s u : Rˣ)
    (hu : (u : R) = ((s⁻¹ : Rˣ) : R) - (s : R))
    (hg : IsUnit (eval₂ (eval₂ φ s⁻¹) 1 (heckeDeltaQ K))) (β : MarkovBraid) :
    IsLocalization.Away.lift (heckeDeltaQ K) hg (β.heckeAlexanderRegular K) =
      β.normalizedBurauAlexander s := by
  let g : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ s⁻¹) 1
  let L : heckeAlexanderRegularRing K →+* R := IsLocalization.Away.lift (heckeDeltaQ K) hg
  have hcomp : L.comp
      (algebraMap (LaurentPolynomial (LaurentPolynomial K)) (heckeAlexanderRegularRing K)) = g :=
    IsLocalization.Away.lift_comp _ _
  have hL : L (β.heckeAlexanderRegular K) = eval₂ (eval₂ φ u) 1 (β.reducedHomfly K) := by
    rw [MarkovBraid.heckeAlexanderRegular, hom_eval₂]
    congr 2
    · refine RingHom.ext fun p ↦ ?_
      rw [RingHom.comp_apply, hom_eval₂]
      congr 2
      · rw [IsScalarTower.algebraMap_eq K (LaurentPolynomial (LaurentPolynomial K))
            (heckeAlexanderRegularRing K), ← RingHom.comp_assoc, hcomp]
        refine RingHom.ext fun x ↦ ?_
        rw [RingHom.comp_apply,
          IsScalarTower.algebraMap_apply K (LaurentPolynomial K)
            (LaurentPolynomial (LaurentPolynomial K)) x,
          ← C_eq_algebraMap, ← C_eq_algebraMap]
        simp [g]
      · ext
        change L (algebraMap (LaurentPolynomial (LaurentPolynomial K))
          (heckeAlexanderRegularRing K) (heckeDeltaQ K)) = (u : R)
        rw [← RingHom.comp_apply, hcomp]
        simp [g, heckeDeltaQ, hu]
    · ext
      rw [Units.coe_map, Units.coe_map]
      simp [L]
  exact hL.trans (β.eval₂_reducedHomfly_eq_normalizedBurauAlexander φ s u hu)

end AlexanderRegularity

/-! #### 2. Regularity across `q - q⁻¹ = 0` (`q = ±1`, classical specialization) -/

section ClassicalRegularity

variable {K : Type*} [Field K]

/-- Canonical localization map from `Localization.Away C₀` (inverting `C₀` alone) into
`Localization.Away (C₀ * (T 1 - T (-1)))` (also inverting `q - q⁻¹`). -/
def heckeZeroFactorLift (C₀ : LaurentPolynomial K) :
    Localization.Away C₀ →+* Localization.Away (C₀ * (T 1 - T (-1))) :=
  IsLocalization.Away.awayToAwayRight C₀ (T 1 - T (-1))

/-- When `C₀ ≠ 0` in `LaurentPolynomial K`, `heckeZeroFactorLift C₀` is injective, so regular
extensions across `q - q⁻¹ = 0` into `Localization.Away C₀` are unique. -/
theorem heckeZeroFactorLift_injective {C₀ : LaurentPolynomial K} (hC₀ : C₀ ≠ 0) :
    Function.Injective (heckeZeroFactorLift C₀) := by
  rw [heckeZeroFactorLift, IsLocalization.Away.awayToAwayRight]
  exact away_lift_injective (mul_ne_zero hC₀ (T_sub_T_ne_zero (by decide))) (dvd_mul_right _ _)

/-- The regular Ocneanu trace parameter `C₀⁻¹ * l₀⁻¹` inside `Localization.Away C₀`. -/
def heckeZeroFactorZ (C₀ : LaurentPolynomial K) (l₀ : (LaurentPolynomial K)ˣ) :
    Localization.Away C₀ :=
  IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀ *
    algebraMap (LaurentPolynomial K) (Localization.Away C₀) (↑l₀⁻¹ : LaurentPolynomial K)

/-- The unit `T 1 - T (-1) = q - q⁻¹` inside `Localization.Away (C₀ * (T 1 - T (-1)))`. -/
def heckeZeroFactorDeltaUnit (C₀ : LaurentPolynomial K) :
    (Localization.Away (C₀ * (T 1 - T (-1))))ˣ where
  val := algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
    (T 1 - T (-1))
  inv := algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1)))) C₀ *
    IsLocalization.Away.invSelf (C₀ * (T 1 - T (-1)))
  val_inv := by
    calc algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
            (T 1 - T (-1)) *
          (algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1)))) C₀ *
            IsLocalization.Away.invSelf (C₀ * (T 1 - T (-1))))
        = algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
            (C₀ * (T 1 - T (-1))) *
            IsLocalization.Away.invSelf (C₀ * (T 1 - T (-1))) := by
          rw [map_mul]
          ring
      _ = 1 := IsLocalization.Away.mul_invSelf _
  inv_val := by
    calc algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1)))) C₀ *
          IsLocalization.Away.invSelf (C₀ * (T 1 - T (-1))) *
          algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
            (T 1 - T (-1))
        = algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
            (C₀ * (T 1 - T (-1))) *
            IsLocalization.Away.invSelf (C₀ * (T 1 - T (-1))) := by
          rw [map_mul]
          ring
      _ = 1 := IsLocalization.Away.mul_invSelf _

/-- In `Localization.Away C₀` (without inverting `q - q⁻¹`), any `l₀ : (LaurentPolynomial K)ˣ`
satisfying `l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))` solves both positive and negative Markov normalization
equations with `z = heckeZeroFactorZ C₀ l₀`. -/
theorem heckeZeroFactorNormalization {C₀ : LaurentPolynomial K} {l₀ : (LaurentPolynomial K)ˣ}
    (hl₀ : (↑l₀⁻¹ : LaurentPolynomial K) - (l₀ : LaurentPolynomial K) = C₀ * (T 1 - T (-1))) :
    algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀ *
        ↑(Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀) *
        heckeZeroFactorZ C₀ l₀ = 1 ∧
      algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀ *
        ↑((Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀)⁻¹) *
        (heckeZeroFactorZ C₀ l₀ -
          (↑(Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K)) -
            ↑(Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K))⁻¹)) = 1 := by
  let ι := algebraMap (LaurentPolynomial K) (Localization.Away C₀)
  let q₀ := Units.map ι.toMonoidHom (genericUnit K)
  let l := Units.map ι.toMonoidHom l₀
  let c := IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀
  have hc : ι C₀ * c = 1 := IsLocalization.Away.mul_invSelf C₀
  have hz_def : heckeZeroFactorZ C₀ l₀ = c * ↑l⁻¹ := by
    rw [heckeZeroFactorZ]
    rfl
  rw [hz_def]
  refine ⟨by linear_combination (l : Localization.Away C₀) * ↑l⁻¹ * hc + l.mul_inv, ?_⟩
  have hq : (q₀ : Localization.Away C₀) - ↑q₀⁻¹ = ι (T 1 - T (-1)) := by
    change ι (genericUnit K) - ι ↑(genericUnit K)⁻¹ = ι (T 1 - T (-1))
    rw [genericUnit_val, genericUnit_inv, map_sub]
  have hsub : (↑l⁻¹ : Localization.Away C₀) - (l : Localization.Away C₀) =
      ι C₀ * ((q₀ : Localization.Away C₀) - ↑q₀⁻¹) := by
    rw [hq, ← map_mul, ← hl₀, map_sub]
    rfl
  have hz : c * ↑l⁻¹ - ((q₀ : Localization.Away C₀) - ↑q₀⁻¹) =
      c * (l : Localization.Away C₀) := by
    linear_combination c * hsub + ((q₀ : Localization.Away C₀) - ↑q₀⁻¹) * hc
  rw [hz]
  linear_combination (↑l⁻¹ : Localization.Away C₀) * (l : Localization.Away C₀) * hc + l.inv_mul

/-- **Regularity across `q - q⁻¹ = 0` (`q = ±1`).** Whenever `l₀⁻¹ - l₀ = C₀ * (T 1 - T (-1))` in
`LaurentPolynomial K` with `C₀ ≠ 0`, the generic HOMFLY specialization in
`Localization.Away (C₀ * (T 1 - T (-1)))` equals the image under the injective localization map
`heckeZeroFactorLift C₀` of the regular normalized Ocneanu trace in `Localization.Away C₀`. -/
theorem MarkovBraid.heckeZeroFactorLift_heckeTrace_eq_eval₂_reducedHomfly
    {C₀ : LaurentPolynomial K} {l₀ : (LaurentPolynomial K)ˣ}
    (hl₀ : (↑l₀⁻¹ : LaurentPolynomial K) - (l₀ : LaurentPolynomial K) = C₀ * (T 1 - T (-1)))
    (β : MarkovBraid) :
    heckeZeroFactorLift C₀
        (β.heckeTrace
          (ocneanuTrace (Localization.Away C₀)
            (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K))
            (heckeZeroFactorZ C₀ l₀))
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀)
          (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀)) =
      eval₂
        (eval₂ (algebraMap K (Localization.Away (C₀ * (T 1 - T (-1)))))
          (heckeZeroFactorDeltaUnit C₀))
        (Units.map
          (algebraMap (LaurentPolynomial K)
            (Localization.Away (C₀ * (T 1 - T (-1))))).toMonoidHom l₀)⁻¹
        (β.reducedHomfly K) := by
  have hj : ∀ a : LaurentPolynomial K,
      heckeZeroFactorLift C₀ (algebraMap (LaurentPolynomial K) (Localization.Away C₀) a) =
        algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1)))) a := by
    intro a
    rw [heckeZeroFactorLift]
    exact IsLocalization.Away.awayToAwayRight_eq C₀ (T 1 - T (-1)) a
  obtain ⟨hpos₀, hneg₀⟩ := heckeZeroFactorNormalization hl₀
  let q₀ := Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
    (genericUnit K)
  let l_S₀ := Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀
  have hpos : heckeZeroFactorLift C₀
        (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
      ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom l_S₀) *
      heckeZeroFactorLift C₀ (heckeZeroFactorZ C₀ l₀) = 1 := by
    change heckeZeroFactorLift C₀
        (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
      heckeZeroFactorLift C₀ l_S₀ *
      heckeZeroFactorLift C₀ (heckeZeroFactorZ C₀ l₀) = 1
    rw [← map_mul, ← map_mul, hpos₀, map_one]
  have hneg : heckeZeroFactorLift C₀
        (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
      ↑((Units.map (heckeZeroFactorLift C₀).toMonoidHom l_S₀)⁻¹) *
      (heckeZeroFactorLift C₀ (heckeZeroFactorZ C₀ l₀) -
        (↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀) -
          ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀)⁻¹)) = 1 := by
    change heckeZeroFactorLift C₀
        (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
      heckeZeroFactorLift C₀ ↑l_S₀⁻¹ *
      (heckeZeroFactorLift C₀ (heckeZeroFactorZ C₀ l₀) -
        (heckeZeroFactorLift C₀ q₀ - heckeZeroFactorLift C₀ ↑q₀⁻¹)) = 1
    rw [← map_sub, ← map_sub, ← map_mul, ← map_mul, hneg₀, map_one]
  have hu : (heckeZeroFactorDeltaUnit C₀ : Localization.Away (C₀ * (T 1 - T (-1)))) =
      ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀) -
        ↑(Units.map (heckeZeroFactorLift C₀).toMonoidHom q₀)⁻¹ := by
    rw [heckeZeroFactorDeltaUnit]
    change algebraMap (LaurentPolynomial K) (Localization.Away (C₀ * (T 1 - T (-1))))
        (T 1 - T (-1)) =
      heckeZeroFactorLift C₀
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) (genericUnit K)) -
        heckeZeroFactorLift C₀
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) ↑(genericUnit K)⁻¹)
    rw [genericUnit_val, genericUnit_inv, hj, hj, map_sub]
  have hl_eq : Units.map (heckeZeroFactorLift C₀).toMonoidHom l_S₀ =
      Units.map
        (algebraMap (LaurentPolynomial K)
          (Localization.Away (C₀ * (T 1 - T (-1))))).toMonoidHom l₀ := by
    ext
    exact hj (l₀ : LaurentPolynomial K)
  rw [β.map_heckeTrace_ocneanuTrace (heckeZeroFactorLift C₀),
    ← β.eval₂_reducedHomfly_eq_heckeTrace_ocneanuTrace
      (algebraMap K (Localization.Away (C₀ * (T 1 - T (-1))))) hu hpos hneg,
    hl_eq]

/-- **Evaluation of the regular extension across `q - q⁻¹ = 0` (including at `q = ±1`).** For any
`φ : K →+* R`, `q : Rˣ`, and inverse `c` of `eval₂ φ q C₀`, evaluating the unique regular
extension in `Localization.Away C₀` via `IsLocalization.Away.lift C₀` produces the normalized
Ocneanu braid trace at `q`. -/
theorem MarkovBraid.lift_heckeZeroFactorRegular_eq_heckeTrace {R : Type*} [CommRing R]
    {C₀ : LaurentPolynomial K} (l₀ : (LaurentPolynomial K)ˣ)
    (φ : K →+* R) (q : Rˣ) {c : R} (hc : c * eval₂ φ q C₀ = 1)
    (hunit : IsUnit (eval₂ φ q C₀)) (β : MarkovBraid) :
    IsLocalization.Away.lift C₀ hunit
        (β.heckeTrace
          (ocneanuTrace (Localization.Away C₀)
            (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
              (genericUnit K))
            (heckeZeroFactorZ C₀ l₀))
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀)
          (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀)) =
      β.heckeTrace (ocneanuTrace R q (c * eval₂ φ q (↑l₀⁻¹ : LaurentPolynomial K)))
        (eval₂ φ q C₀) (Units.map (eval₂ φ q).toMonoidHom l₀) := by
  have hLC : IsLocalization.Away.lift C₀ hunit
      (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) = eval₂ φ q C₀ :=
    IsLocalization.Away.lift_eq C₀ hunit C₀
  have hLc : IsLocalization.Away.lift C₀ hunit
      (IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀) = c := by
    have hmul : IsLocalization.Away.lift C₀ hunit
          (algebraMap (LaurentPolynomial K) (Localization.Away C₀) C₀) *
        IsLocalization.Away.lift C₀ hunit
          (IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    rw [hLC] at hmul
    linear_combination c * hmul -
      IsLocalization.Away.lift C₀ hunit
        (IsLocalization.Away.invSelf (S := Localization.Away C₀) C₀) * hc
  have hq_eq : Units.map (IsLocalization.Away.lift C₀ hunit).toMonoidHom
      (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom
        (genericUnit K)) = q := by
    ext
    rw [Units.coe_map, Units.coe_map]
    change IsLocalization.Away.lift C₀ hunit
      (algebraMap (LaurentPolynomial K) (Localization.Away C₀) (genericUnit K)) = (q : R)
    rw [genericUnit_val, IsLocalization.Away.lift_eq, eval₂_T, zpow_one]
  have hl_eq : Units.map (IsLocalization.Away.lift C₀ hunit).toMonoidHom
      (Units.map (algebraMap (LaurentPolynomial K) (Localization.Away C₀)).toMonoidHom l₀) =
        Units.map (eval₂ φ q).toMonoidHom l₀ := by
    ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact IsLocalization.Away.lift_eq C₀ hunit (l₀ : LaurentPolynomial K)
  have hLz : IsLocalization.Away.lift C₀ hunit (heckeZeroFactorZ C₀ l₀) =
      c * eval₂ φ q (↑l₀⁻¹ : LaurentPolynomial K) := by
    rw [heckeZeroFactorZ, map_mul, hLc, IsLocalization.Away.lift_eq]
  rw [β.map_heckeTrace_ocneanuTrace (IsLocalization.Away.lift C₀ hunit),
    hLC, hLz, hq_eq, hl_eq]

/-- The positive-rank universal quantum dimension `[N + 1]_q` in `LaurentPolynomial A` is nonzero
over every nontrivial commutative ring `A`, so `heckeZeroFactorLift_injective` and
`heckeZeroFactorLift_heckeTrace_eq_eval₂_reducedHomfly` apply to all positive finite ranks. -/
theorem jimboWeight_sum_genericUnit_ne_zero (A : Type*) [CommRing A] [Nontrivial A] (N : ℕ) :
    (∑ a : Fin (N + 1), jimboWeight (genericUnit A) a) ≠ 0 := by
  intro h
  have hs := jimboWeight_sum (N := N + 1) (genericUnit A)
  have hp : (↑(genericUnit A ^ (N + 1)) : LaurentPolynomial A) = T ((N + 1 : ℕ) : ℤ) := by
    rw [← zpow_natCast, genericUnit_zpow_val]
  have hn : (↑((genericUnit A)⁻¹ ^ (N + 1)) : LaurentPolynomial A) = T (-((N + 1 : ℕ) : ℤ)) := by
    have hz : ((genericUnit A)⁻¹ ^ (N + 1) : (LaurentPolynomial A)ˣ) =
        genericUnit A ^ (-((N + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [hz, genericUnit_zpow_val]
  rw [h, mul_zero, hp, hn] at hs
  exact T_sub_T_ne_zero (by omega) hs.symm

end ClassicalRegularity

end ZeroFactorRegularity

end TauCeti
