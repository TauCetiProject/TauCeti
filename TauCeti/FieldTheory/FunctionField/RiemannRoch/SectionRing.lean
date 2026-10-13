/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Principal
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# The section ring of a divisor

Let `F / k` be an algebraic function field and `D` a divisor of `F`. Since
`L(mD) · L(nD) ⊆ L((m + n)D)`, the Riemann–Roch spaces `L(nD)`, `n ∈ ℕ`, form a graded family of
`k`-subspaces of `F`, and their direct sum `⨁ₙ L(nD)` is a graded `k`-algebra, the
**section ring** of `D`. It is realized as the subalgebra `TauCeti.Divisor.sectionRing D` of
`F[X]` of polynomials `∑ fₙ Xⁿ` with `fₙ ∈ L(nD)`, graded by the power of `X`.

Section rings of divisors are the graded rings from which projective models of a curve are built
as `Proj`. This file computes the rings of the standard affine charts `D₊(f Xⁿ)` of `Proj` of the
section ring, and which of these charts cover it. If `f Xⁿ` is homogeneous of degree `n`
with `f ∈ L(nD)` nonzero, the degree-zero fractions `g Xⁿʳ / (f Xⁿ)ʳ`, with `g ∈ L(nrD)`, are
the functions `g / fʳ`, and these are exactly the functions regular at every place `P` at which
`f` attains the bound `ord_P f ≥ -n D(P)` defining `L(nD)`, that is, every place outside the
support of the effective divisor `div f + nD`. So the homogeneous localization at `f Xⁿ` is a
holomorphy ring (`TauCeti.Divisor.sectionRingAwayEquiv`). Sections `sᵢ ∈ L(D)` without a common
base point, meaning that at every place `P` one of them has order exactly `-D(P)`, give elements
`sᵢ X` of degree one whose standard opens cover `Proj`
(`TauCeti.Divisor.irrelevant_le_radical_span_monomialDegreeOne`).

For the pole divisor `D = (x)_∞` of a nonzero `x` and the sections `1, x ∈ L(D)`, the two
holomorphy rings are the rings `𝒪_x` and `𝒪_{x⁻¹}` of functions regular wherever `x`,
respectively `x⁻¹`, is regular (`TauCeti.Divisor.coeff_poles_eq_zero_iff` and
`TauCeti.Divisor.valuation_eq_exp_coeff_poles_iff`), and `1, x` have no common base point
(`TauCeti.Divisor.irrelevant_le_radical_span_monomialDegreeOne_poles`). These are the two affine
charts from which `TauCeti.AlgebraicGeometry.twoChartModel` is glued.

## Main definitions

* `TauCeti.Divisor.sectionRing D`: the section ring `⨁ₙ L(nD)` of `D`, inside `F[X]`.
* `TauCeti.Divisor.sectionRingGrade D`: its grading, `n ↦ L(nD) Xⁿ`.
* `TauCeti.Divisor.monomialDegreeOne hs`: the element `s X` of degree one, for `s ∈ L(D)`.
* `TauCeti.Divisor.sectionRingAwayEquiv hF hf hf0`: for a nonzero homogeneous element `f Xⁿ`, the
  isomorphism from the homogeneous localization at `f Xⁿ` onto the holomorphy ring of the places
  at which `f` has valuation `exp (n D(P))`.

## Main results

* `TauCeti.Divisor.mem_holomorphyRing_iff_exists_mul_pow_mem_riemannRochSpace`: for `f ∈ L(nD)`,
  a function `z` is regular at every place `P` where `ord_P f = -n D(P)` exactly when
  `z fʳ ∈ L(nrD)` for some `r`.
* `TauCeti.Divisor.sectionRingAwayEquiv_mk`: the isomorphism sends `g Xⁿʳ / (f Xⁿ)ʳ` to `g / fʳ`.
* `TauCeti.Divisor.irrelevant_le_radical_span_monomialDegreeOne`: sections of `L(D)` without a
  common base point generate the irrelevant ideal up to radical.
* `TauCeti.Divisor.irrelevant_le_radical_span_monomialDegreeOne_poles`: for `D = (x)_∞`, the
  elements `X` and `x X` generate the irrelevant ideal up to radical.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2 (the affine charts of
  `Proj`) and Section IV.3 (embedding a curve by the sections of a divisor).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 (holomorphy rings) and Theorem 1.1.19.
-/

public section

open Polynomial HomogeneousLocalization

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-! ### The section ring and its grading -/

/-- The Riemann–Roch spaces `L(nD)` form a graded family: `1 ∈ L(0)` and
`L(mD) · L(nD) ⊆ L((m + n)D)`. -/
instance gradedMonoid_riemannRochSpace (D : Divisor k F) :
    SetLike.GradedMonoid fun n : ℕ ↦ riemannRochSpace (n • D) where
  one_mem := one_mem_riemannRochSpace_iff.mpr (by rw [zero_nsmul])
  mul_mem m n f g hf hg := by
    rw [add_nsmul]
    exact mul_mem_riemannRochSpace_add hf hg

/-- The **section ring** `⨁ₙ L(nD)` of a divisor `D`: the `k`-subalgebra of `F[X]` of polynomials
`∑ fₙ Xⁿ` with `fₙ ∈ L(nD)` for every `n`.

It is an abbreviation for `TauCeti.coeffSubalgebra` of the family `n ↦ L(nD)`, so that the
grading and its API apply to it directly. -/
noncomputable abbrev sectionRing (D : Divisor k F) : Subalgebra k F[X] :=
  coeffSubalgebra fun n : ℕ ↦ riemannRochSpace (n • D)

/-- The grading of the section ring of `D`: its degree `n` piece consists of the monomials
`f Xⁿ` with `f ∈ L(nD)`. -/
noncomputable abbrev sectionRingGrade (D : Divisor k F) : ℕ → Submodule k (sectionRing D) :=
  coeffSubalgebra.grade fun n : ℕ ↦ riemannRochSpace (n • D)

/-- The element `s X` of degree one of the section ring of `D`, for `s ∈ L(D)`. -/
noncomputable def monomialDegreeOne {D : Divisor k F} {s : F} (hs : s ∈ riemannRochSpace D) :
    sectionRing D :=
  coeffSubalgebra.monomial _ 1 s (by rwa [one_nsmul])

@[simp]
theorem coe_monomialDegreeOne {D : Divisor k F} {s : F} (hs : s ∈ riemannRochSpace D) :
    (monomialDegreeOne hs : F[X]) = Polynomial.monomial 1 s :=
  coeffSubalgebra.coe_monomial _ _ _

theorem monomialDegreeOne_mem_sectionRingGrade {D : Divisor k F} {s : F}
    (hs : s ∈ riemannRochSpace D) : monomialDegreeOne hs ∈ sectionRingGrade D 1 :=
  coeffSubalgebra.monomial_mem_grade _ _ _

/-! ### Functions regular where a section attains its bound -/

/-- **Functions regular where a section attains its bound.** Let `f ∈ L(nD)`. A function `z` is
regular at every place `P` at which `f` has valuation `exp (n D(P))`, that is,
`ord_P f = -n D(P)`, so that `f` attains the bound defining `L(nD)`, exactly when `z fʳ ∈ L(nrD)`
for some `r`: the other places are zeros of the effective divisor `div f + nD`, where a high power
of `f` absorbs the poles of `z`.

At `f = 0` the set of places is empty and both sides hold for every `z`. -/
theorem mem_holomorphyRing_iff_exists_mul_pow_mem_riemannRochSpace (hF : IsFunctionField k F)
    {D : Divisor k F} {n : ℕ} {f : F} (hf : f ∈ riemannRochSpace (n • D)) {z : F} :
    z ∈ holomorphyRing {P : Place k F | P.valuation f = WithZero.exp (n * D.coeff P)} ↔
      ∃ r : ℕ, z * f ^ r ∈ riemannRochSpace ((n * r) • D) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have hempty : {P : Place k F | P.valuation 0 = WithZero.exp (n * D.coeff P)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun P h ↦ WithZero.exp_ne_zero (h.symm.trans (map_zero _))
    rw [hempty, holomorphyRing_empty]
    exact iff_of_true Algebra.mem_top ⟨1, by simp⟩
  -- At every place, `ord_P f + n D(P) ≥ 0`, with equality exactly on the set of places.
  have hfP (P : Place k F) : 0 ≤ P.ord f + n * D.coeff P := by
    have := (mem_riemannRochSpace_iff_neg_le_ord hf0).mp hf P
    rw [WeilDivisor.coeff_nsmul] at this
    omega
  have hval (P : Place k F) :
      P.valuation f = WithZero.exp (n * D.coeff P) ↔ P.ord f = -(n * D.coeff P) := by
    rw [P.ord_eq_iff_valuation_eq_exp_neg hf0, neg_neg]
  simp only [mem_holomorphyRing_iff_forall_ord_nonneg, Set.mem_ofPred_eq, hval]
  constructor
  · intro hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨0, by simp⟩
    classical
    have hT : {P : Place k F | P.ord z < 0}.Finite := Place.finite_setOf_ord_neg hF z
    set r : ℕ := hT.toFinset.sup fun P ↦ (-P.ord z).toNat
    refine ⟨r, (mem_riemannRochSpace_iff_neg_le_ord (mul_ne_zero hz0 (pow_ne_zero r hf0))).mpr
      fun P ↦ ?_⟩
    rw [P.ord_mul hz0 (pow_ne_zero r hf0), P.ord_pow, WeilDivisor.coeff_nsmul]
    push_cast
    by_cases hPz : P.ord z < 0
    · -- `P` is a pole of `z`, hence a zero of `div f + nD`, and `r` absorbs it.
      have hpos : 1 ≤ P.ord f + n * D.coeff P := by
        by_contra h
        have := hfP P
        have := hz P (by omega)
        omega
      have hle : (-P.ord z).toNat ≤ r :=
        Finset.le_sup (f := fun P : Place k F ↦ (-P.ord z).toNat) (hT.mem_toFinset.mpr hPz)
      have h1 : ((-P.ord z).toNat : ℤ) = -P.ord z := Int.toNat_of_nonneg (by omega)
      have h2 : (r : ℤ) ≤ r * (P.ord f + n * D.coeff P) :=
        le_mul_of_one_le_right (Nat.cast_nonneg r) hpos
      linarith
    · have h2 : 0 ≤ (r : ℤ) * (P.ord f + n * D.coeff P) :=
        mul_nonneg (Nat.cast_nonneg r) (hfP P)
      linarith
  · rintro ⟨r, hr⟩ P hP
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have := (mem_riemannRochSpace_iff_neg_le_ord (mul_ne_zero hz0 (pow_ne_zero r hf0))).mp hr P
    rw [P.ord_mul hz0 (pow_ne_zero r hf0), P.ord_pow, WeilDivisor.coeff_nsmul] at this
    push_cast at this
    nlinarith

/-! ### The homogeneous localizations of the section ring -/

/-- Evaluation at `X = 1`, `∑ fₙ Xⁿ ↦ ∑ fₙ`, on the section ring. It sends a homogeneous element
`f Xⁿ` to `f`. -/
private noncomputable def evalOne (D : Divisor k F) : sectionRing D →ₐ[k] F :=
  ((Polynomial.aeval (R := F) (1 : F)).restrictScalars k).comp (sectionRing D).val

private theorem evalOne_apply (D : Divisor k F) (f : sectionRing D) :
    evalOne D f = (f : F[X]).eval 1 := by
  rw [evalOne, AlgHom.comp_apply, Subalgebra.coe_val, AlgHom.restrictScalars_apply,
    coe_aeval_eq_eval]

/-- On a homogeneous element of degree `n`, evaluation at `X = 1` is the `n`-th coefficient. -/
private theorem evalOne_of_mem {D : Divisor k F} {n : ℕ} {f : sectionRing D}
    (hf : f ∈ sectionRingGrade D n) : evalOne D f = (f : F[X]).coeff n := by
  rw [evalOne_apply, coeffSubalgebra.eval_one_of_mem_grade hf]

variable (hF : IsFunctionField k F) {D : Divisor k F} {n : ℕ} {f : sectionRing D}
  (hf : f ∈ sectionRingGrade D n) (hf0 : f ≠ 0)

include hf hf0 in
private theorem isUnit_evalOne : IsUnit (evalOne D f) := by
  rw [evalOne_of_mem hf]
  exact isUnit_iff_ne_zero.mpr ((coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade hf).not.mpr hf0)

/-- The ring homomorphism from the homogeneous localization at `f Xⁿ` to `F` sending
`g Xⁿʳ / (f Xⁿ)ʳ` to `g / fʳ`. -/
private noncomputable def awayLift : Away (sectionRingGrade D) f →ₐ[k] F where
  __ := Away.lift (sectionRingGrade D) (evalOne D).toRingHom (isUnit_evalOne hf hf0)
  commutes' c := by
    rw [RingHom.toFun_eq_coe, algebraMap_eq_comp, RingHom.comp_apply,
      ← HomogeneousLocalization.algebraMap_eq,
      Away.lift_algebraMap, SetLike.GradeZero.coe_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.commutes]

private theorem awayLift_apply (w : Away (sectionRingGrade D) f) :
    awayLift hf hf0 w =
      Away.lift (sectionRingGrade D) (evalOne D).toRingHom (isUnit_evalOne hf hf0) w := by
  rw [awayLift, AlgHom.coe_mk]

private theorem awayLift_mk (r : ℕ) (g : sectionRing D) (hg : g ∈ sectionRingGrade D (r • n)) :
    awayLift hf hf0 (Away.mk _ hf r g hg) =
      (g : F[X]).coeff (r • n) * ((f : F[X]).coeff n ^ r)⁻¹ := by
  rw [awayLift_apply, Away.lift_mk, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evalOne_of_mem hg,
    evalOne_of_mem hf]

include hF in
private theorem range_awayLift :
    (awayLift hf hf0).range =
      holomorphyRing {P : Place k F | P.valuation ((f : F[X]).coeff n) =
        WithZero.exp (n * D.coeff P)} := by
  have hfn : (f : F[X]).coeff n ∈ riemannRochSpace (n • D) := mem_coeffSubalgebra_iff.mp f.2 n
  have ha0 := (coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade hf).not.mpr hf0
  ext z
  rw [AlgHom.mem_range, mem_holomorphyRing_iff_exists_mul_pow_mem_riemannRochSpace hF hfn]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨r, g, hg, rfl⟩ := Away.mk_surjective _ hf w
    refine ⟨r, ?_⟩
    rw [awayLift_mk, inv_mul_cancel_right₀ (pow_ne_zero r ha0)]
    have hg' : (g : F[X]).coeff (r • n) ∈ riemannRochSpace ((r • n) • D) :=
      mem_coeffSubalgebra_iff.mp g.2 (r • n)
    rw [smul_eq_mul, mul_comm r n] at hg' ⊢
    exact hg'
  · rintro ⟨r, hr⟩
    have hr' : (z * (f : F[X]).coeff n ^ r) ∈ riemannRochSpace ((r • n) • D) := by
      rwa [smul_eq_mul, mul_comm r n]
    refine ⟨Away.mk _ hf r (coeffSubalgebra.monomial _ (r • n) _ hr')
      (coeffSubalgebra.monomial_mem_grade _ _ _), ?_⟩
    rw [awayLift_mk, coeffSubalgebra.coe_monomial, coeff_monomial_same,
      mul_inv_cancel_right₀ (pow_ne_zero r ha0)]

private theorem awayLift_injective : Function.Injective (awayLift hf hf0) := by
  refine (injective_iff_map_eq_zero _).mpr fun w hw ↦ ?_
  obtain ⟨r, g, hg, rfl⟩ := Away.mk_surjective _ hf w
  rw [awayLift_mk, mul_eq_zero, inv_eq_zero, or_iff_left (pow_ne_zero r
    ((coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade hf).not.mpr hf0))] at hw
  have hg0 : g = 0 := (coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade hg).mp hw
  apply val_injective
  simp [hg0, Localization.mk_zero]

/-- **The homogeneous localization of the section ring at a nonzero homogeneous element.** Let
`f Xⁿ` be a nonzero homogeneous element of degree `n` of the section ring of `D`, so
`f ∈ L(nD)`. Its homogeneous localization, the ring of fractions `g Xⁿʳ / (f Xⁿ)ʳ` with
`g ∈ L(nrD)`, is isomorphic to the holomorphy ring of the places at which `f` has valuation
`exp (n D(P))`, that is, `ord_P f = -n D(P)`; the fraction corresponds to `g / fʳ`
(`TauCeti.Divisor.sectionRingAwayEquiv_mk`).

Geometrically, the standard open `D₊(f Xⁿ)` of `Proj` of the section ring is the spectrum of the
ring of functions regular outside the support of `div f + nD`. -/
noncomputable def sectionRingAwayEquiv :
    Away (sectionRingGrade D) f ≃ₐ[k]
      holomorphyRing {P : Place k F | P.valuation ((f : F[X]).coeff n) =
        WithZero.exp (n * D.coeff P)} :=
  (AlgEquiv.ofInjective _ (awayLift_injective hf hf0)).trans
    (Subalgebra.equivOfEq _ _ (range_awayLift hF hf hf0))

/-- The isomorphism `TauCeti.Divisor.sectionRingAwayEquiv` sends the fraction
`g Xⁿʳ / (f Xⁿ)ʳ` to `g / fʳ`. -/
@[simp]
theorem sectionRingAwayEquiv_mk (r : ℕ) (g : sectionRing D)
    (hg : g ∈ sectionRingGrade D (r • n)) :
    (sectionRingAwayEquiv hF hf hf0 (Away.mk _ hf r g hg) : F) =
      (g : F[X]).coeff (r • n) * ((f : F[X]).coeff n ^ r)⁻¹ := by
  rw [sectionRingAwayEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    AlgEquiv.ofInjective_apply, awayLift_mk]

/-! ### Sections without a common base point cover `Proj` -/

/-- A homogeneous element `f Xᵐ` of positive degree has a power in the ideal generated by the
elements `sᵢ X` of degree one, when the sections `sᵢ ∈ L(D)` have no common base point.

The functions `sᵢᵐ / f` generate the unit ideal of the ring of functions regular at the places
`P` where `ord_P f = -m D(P)`: by Stichtenoth's Theorem 1.1.19 a proper ideal would lie in the
maximal ideal of such a place, but there some `sᵢ` has `ord_P sᵢ = -D(P)` and `sᵢᵐ / f` is a
unit. Clearing denominators in `1 = ∑ cᵢ sᵢᵐ / f` gives
`fʳ⁺¹ = ∑ (cᵢ fʳ) sᵢᵐ` with `cᵢ fʳ ∈ L(mrD)`. -/
private theorem pow_mem_span_monomialDegreeOne (hF : IsFunctionField k F) {D : Divisor k F}
    {ι : Type*} {s : ι → F} (hs : ∀ i, s i ∈ riemannRochSpace D)
    (hbase : ∀ P : Place k F, ∃ i, P.valuation (s i) = WithZero.exp (D.coeff P)) {m : ℕ}
    (hm : 0 < m) {y : sectionRing D} (hy : y ∈ sectionRingGrade D m) :
    ∃ r : ℕ, y ^ r ∈ Ideal.span (Set.range fun i ↦ monomialDegreeOne (hs i)) := by
  classical
  set a := (y : F[X]).coeff m
  have ha : a ∈ riemannRochSpace (m • D) := mem_coeffSubalgebra_iff.mp y.2 m
  have hy_eq : (y : F[X]) = Polynomial.monomial m a :=
    (coeffSubalgebra.mem_grade_iff_monomial_coeff.mp hy).symm
  rcases eq_or_ne a 0 with ha0 | ha0
  · refine ⟨1, ?_⟩
    rw [(coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade hy).mp ha0, pow_one]
    exact zero_mem _
  set O := holomorphyRing {P : Place k F | P.valuation a = WithZero.exp (m * D.coeff P)}
  -- The generators `sᵢᵐ / a` are regular at the places where `ord_P a = -m D(P)`.
  have hgen (i : ι) : s i ^ m / a ∈ O.toSubring := by
    refine mem_holomorphyRing_iff.mpr fun P hP ↦ ?_
    rw [Set.mem_ofPred_eq] at hP
    have hsi := mem_riemannRochSpace_iff.mp (hs i) P
    rw [Place.mem_integers_iff, map_div₀, map_pow, hP, div_le_one₀ (zero_lt_iff.mpr
      WithZero.exp_ne_zero), ← nsmul_eq_mul, WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le hsi m
  set I : Ideal O.toSubring := Ideal.span (Set.range fun i ↦ (⟨_, hgen i⟩ : O.toSubring))
  have hI : I = ⊤ := by
    by_contra hI
    -- Some generator is nonzero, since the sections have no common base point.
    have hI0 : I ≠ ⊥ := by
      obtain ⟨P⟩ := Place.nonempty hF
      obtain ⟨i, hi⟩ := hbase P
      have hsi : s i ≠ 0 := by
        rintro h
        rw [h, map_zero] at hi
        exact WithZero.exp_ne_zero hi.symm
      intro hbot
      have hmem : (⟨_, hgen i⟩ : O.toSubring) ∈ I := Ideal.subset_span ⟨i, rfl⟩
      rw [hbot, Ideal.mem_bot] at hmem
      exact div_ne_zero (pow_ne_zero m hsi) ha0 (congr_arg Subtype.val hmem)
    obtain ⟨P, hPO, hPI⟩ := Place.exists_forall_mem_integers_and_valuation_lt_one hF
      (fun c ↦ O.algebraMap_mem c) hI hI0
    have hPU : P.valuation a = WithZero.exp (m * D.coeff P) :=
      (coe_holomorphyRing_subset_integers_iff hF).mp fun z hz ↦ hPO ⟨z, hz⟩
    obtain ⟨i, hi⟩ := hbase P
    have hlt := hPI _ (Ideal.subset_span ⟨i, rfl⟩)
    rw [map_div₀, map_pow, hi, hPU, ← nsmul_eq_mul, WithZero.exp_nsmul,
      div_self (pow_ne_zero m WithZero.exp_ne_zero)] at hlt
    exact lt_irrefl _ hlt
  -- Write `1 = ∑ cᵢ sᵢᵐ / a` and clear denominators with a common power of `a`.
  have hone : (1 : O.toSubring) ∈ I := by
    rw [hI]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hone
  have hc' : ∑ i ∈ c.support, (c i : F) * (s i ^ m / a) = 1 := by
    simpa [Finsupp.sum] using congr_arg Subtype.val hc
  have hr (i : ι) : ∃ r : ℕ, (c i : F) * a ^ r ∈ riemannRochSpace ((m * r) • D) :=
    (mem_holomorphyRing_iff_exists_mul_pow_mem_riemannRochSpace hF ha).mp (c i).2
  choose r hr using hr
  set R := c.support.sup r
  have hR (i : ι) : (c i : F) * a ^ R ∈ riemannRochSpace ((m * R) • D) := by
    by_cases hi : i ∈ c.support
    · have hle : r i ≤ R := Finset.le_sup hi
      have hpow : a ^ (R - r i) ∈ riemannRochSpace (((R - r i) • m) • D) :=
        SetLike.pow_mem_graded (A := fun n : ℕ ↦ riemannRochSpace (n • D)) _ ha
      have hmul := SetLike.mul_mem_graded (A := fun n : ℕ ↦ riemannRochSpace (n • D)) (hr i) hpow
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle] at hmul
      convert hmul using 3
      rw [smul_eq_mul, ← mul_comm m, ← mul_add, Nat.add_sub_cancel' hle]
    · rw [Finsupp.notMem_support_iff.mp hi, ZeroMemClass.coe_zero, zero_mul]
      exact zero_mem _
  refine ⟨R + 1, ?_⟩
  have hsum : y ^ (R + 1) = ∑ i ∈ c.support,
      coeffSubalgebra.monomial _ (m * R) _ (hR i) * monomialDegreeOne (hs i) ^ m := by
    ext1
    simp only [SubmonoidClass.coe_pow, hy_eq, Polynomial.monomial_pow,
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, coeffSubalgebra.coe_monomial,
      coe_monomialDegreeOne, one_mul, monomial_mul_monomial, ← map_sum]
    congr 1
    rw [← mul_one (a ^ (R + 1)), ← hc', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  rw [hsum]
  refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ ?_
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) m hm

/-- **Sections without a common base point cover `Proj` of the section ring.** If the sections
`sᵢ ∈ L(D)` have no common base point, that is, at every place `P` some `sᵢ` has valuation
`exp (D(P))` (equivalently, `ord_P sᵢ = -D(P)`), then the elements `sᵢ X` of degree one generate
the irrelevant ideal of the section ring of `D` up to radical. Equivalently, the standard opens
`D₊(sᵢ X)` cover `Proj` of the section ring. -/
theorem irrelevant_le_radical_span_monomialDegreeOne (hF : IsFunctionField k F)
    {D : Divisor k F} {ι : Type*} {s : ι → F} (hs : ∀ i, s i ∈ riemannRochSpace D)
    (hbase : ∀ P : Place k F, ∃ i, P.valuation (s i) = WithZero.exp (D.coeff P)) :
    (HomogeneousIdeal.irrelevant (sectionRingGrade D)).toIdeal ≤
      (Ideal.span (Set.range fun i ↦ monomialDegreeOne (hs i))).radical := by
  classical
  intro y hy
  rw [← DirectSum.sum_support_decompose (sectionRingGrade D) y]
  refine Ideal.sum_mem _ fun m _ ↦ ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- The degree-zero component of an element of the irrelevant ideal vanishes.
    rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hy
    rw [hy]
    exact zero_mem _
  · exact pow_mem_span_monomialDegreeOne hF hs hbase hm (SetLike.coe_mem _)

/-! ### The pole divisor of a function -/

/-- **The sections `1` and `z` of the pole divisor of `z` cover `Proj` of its section ring**:
the elements `X` and `z X` of degree one generate the irrelevant ideal up to radical. -/
theorem irrelevant_le_radical_span_monomialDegreeOne_poles (hF : IsFunctionField k F) (z : Fˣ) :
    (HomogeneousIdeal.irrelevant (sectionRingGrade (poles hF z))).toIdeal ≤
      (Ideal.span {monomialDegreeOne (one_mem_riemannRochSpace_iff.mpr
          (isEffective_poles hF z).zero_le),
        monomialDegreeOne (mem_riemannRochSpace_poles hF z)}).radical := by
  have hs : ∀ i, ![1, (z : F)] i ∈ riemannRochSpace (poles hF z) := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le,
      mem_riemannRochSpace_poles hF z⟩
  have hbase (P : Place k F) :
      ∃ i, P.valuation (![1, (z : F)] i) = WithZero.exp ((poles hF z).coeff P) := by
    by_cases hP : (z : F) ∈ P.integers
    · exact ⟨0, by simp [(coeff_poles_eq_zero_iff hF z P).mpr hP]⟩
    · refine ⟨1, (valuation_eq_exp_coeff_poles_iff hF z P).mpr ?_⟩
      rw [Place.mem_integers_iff, map_inv₀]
      rw [Place.mem_integers_iff, not_le] at hP
      exact inv_le_one_of_one_le₀ hP.le
  convert irrelevant_le_radical_span_monomialDegreeOne hF hs hbase using 3
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two]
  exact or_congr eq_comm eq_comm

end Divisor

end TauCeti
