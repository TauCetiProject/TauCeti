/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Units
public import TauCeti.NumberTheory.NumberField.Quadratic.Norm
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Norm.Basic

/-!
# Units of norm `-1` and the narrow class group of a real quadratic field

Let `K = ℚ(√d)` be a quadratic number field, presented by `θ : 𝓞 K` with `minpoly ℤ θ = X² - d`
and `Algebra.adjoin ℚ {θ} = ⊤`. Forgetting positivity gives a surjection `Cl⁺(K) → Cl(K)` from the
narrow class group onto the ordinary one, and the two class groups agree exactly when that
surjection is injective. For a **real** quadratic field (`0 < d`) this file identifies when that
happens: precisely when some unit of `𝓞 K` has norm `-1`.

The mechanism is a sign count carried by the norm. Every real embedding of `K` is one fixed
embedding `φ`, or `φ` composed with quadratic conjugation `σ`
(`NumberField.realRingHom_eq_or_eq_comp_quadraticConj`), so the two signs an element `x` receives
are those of `φ x` and `φ (σ x)`, whose product is `N(x)`. Hence `N(x) > 0` says the two signs
agree, that is, `x` or `-x` is totally positive
(`NumberField.isTotallyPositive_or_isTotallyPositive_neg_of_norm_pos`), and the elements of
negative norm are exactly the ones with no totally positive associate up to sign. Since
`N(θ) = -d < 0`, multiplying by `θ` exchanges the two cases; so a *single* unit of negative norm
lets every `x : Kˣ` be scaled to a totally positive element by a unit of `𝓞 K`, which is exactly
triviality of the narrow principal class (`NumberField.NarrowClassGroup.mkPrincipal_eq_one_iff`).
Conversely, if `Cl⁺(K) → Cl(K)` is injective then the narrow class of `(θ)` is trivial, so some
`v · θ` is totally positive and therefore has positive norm `N(v) · (-d)`, forcing `N(v) = -1`.

For an *imaginary* quadratic field the norm is positive on every nonzero element
(`NumberField.norm_pos_of_radicand_neg`), so there is no unit of norm `-1`; consistently, the two
class groups already agree there for the unrelated reason that positivity is vacuous
(`NumberField.NarrowClassGroup.toClassGroup_injective`). The hypothesis `0 < d` is therefore
needed only for the direction producing a unit; the direction consuming one carries its own
positivity (`NumberField.radicand_pos_of_norm_eq_neg_one`).

A solution of the negative Pell equation `b² - d a² = -1` supplies a unit of norm `-1`
(`exists_norm_eq_neg_one_of_sq_sub_mul_sq_eq_neg_one`), which is how the hypothesis is met
concretely: for `d = 2`, `a = b = 1` gives the unit `1 + √2`.

This is the classical criterion `h⁺ = h ↔ N(ε) = -1` for the fundamental unit `ε`. It is what
transfers the narrow genus-theory `2`-rank formula `2-rank Cl⁺(K) = t - 1` to the ordinary class
group of a real quadratic field, where that rank can otherwise drop.

## Main results

* `NumberField.isTotallyPositive_or_isTotallyPositive_neg_of_norm_pos`: an element of positive
  norm is, up to sign, totally positive.
* `NumberField.radicand_pos_of_norm_eq_neg_one`: a unit of norm `-1` forces `0 < d`.
* `NumberField.exists_norm_eq_neg_one_of_sq_sub_mul_sq_eq_neg_one`: a solution of the negative
  Pell equation `b² - d a² = -1` supplies such a unit.
* `NumberField.NarrowClassGroup.toClassGroup_injective_of_norm_eq_neg_one`: a unit of norm `-1`
  makes `Cl⁺(K) → Cl(K)` injective.
* `NumberField.NarrowClassGroup.toClassGroup_injective_iff_exists_norm_eq_neg_one`: for `0 < d`
  the converse holds too.
* `NumberField.NarrowClassGroup.card_eq_card_classGroup_iff_exists_norm_eq_neg_one`: the narrow
  class number equals the class number exactly when some unit has norm `-1`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Positive norm forces a sign.** In a quadratic field the norm of `x` is the product of the
two values `φ x` and `φ (σ x)` that the real embeddings give `x`, so a positive norm says those
values have the same sign and hence that `x` or `-x` is totally positive. A positive norm also
forces `x ≠ 0`. The proof feeds `x / σ x = x² / N(x)`, a product of totally positive elements, to
`isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj`. Over a
totally complex field both alternatives hold vacuously. -/
theorem isTotallyPositive_or_isTotallyPositive_neg_of_norm_pos
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {x : K}
    (hnorm : 0 < Algebra.norm ℚ x) :
    IsTotallyPositive x ∨ IsTotallyPositive (-x) := by
  have hx : x ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis (Module.finBasis ℚ K)).mp hnorm.ne'
  refine isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
    hmin hgen ?_
  have hprod : x * quadraticConj hmin hgen x = ((Algebra.norm ℚ x : ℚ) : K) := by
    rw [← eq_ratCast (algebraMap ℚ K)]
    exact (algebraMap_norm_eq_mul_quadraticConj hmin hgen x).symm
  have hconj : quadraticConj hmin hgen x ≠ 0 := by
    simpa using hx
  have hdiv : x / quadraticConj hmin hgen x = x ^ 2 * (((Algebra.norm ℚ x : ℚ) : K))⁻¹ := by
    rw [← hprod]
    field_simp
  rw [hdiv]
  exact (isTotallyPositive_sq hx).mul (isTotallyPositive_ratCast hnorm).inv

/-- **A unit of norm `-1` only exists in the real case.** For `d < 0` the norm is positive on every
nonzero element (`norm_pos_of_radicand_neg`), and `d = 0` is excluded because the radicand is not a
square; so a unit of norm `-1` forces `0 < d`. -/
theorem radicand_pos_of_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ}
    (hu : Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1) : 0 < d := by
  have hune : ((u : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have := norm_pos_of_radicand_neg hmin hgen hd hune
    rw [hu] at this
    norm_num at this
  · -- `d = 0` makes the radicand the square `0 * 0`.
    subst hd
    exact absurd ⟨0, by norm_num⟩ (not_isSquare_radicand hmin)
  · exact hd

/-- **A solution of the negative Pell equation gives a unit of norm `-1`.** If `b² - d a² = -1`
then `b + aθ` has norm `-1`, hence is a unit of `𝓞 K` (an algebraic integer is a unit exactly when
its norm is `±1`). This is the concrete source of the hypothesis below: for `d = 2`, `a = b = 1`
gives the unit `1 + √2`. -/
theorem exists_norm_eq_neg_one_of_sq_sub_mul_sq_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {a b : ℤ} (hab : b ^ 2 - d * a ^ 2 = -1) :
    ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
  set x : 𝓞 K := (b : 𝓞 K) + (a : 𝓞 K) * θ with hxdef
  have habq : ((b : ℤ) : ℚ) ^ 2 - ((d : ℤ) : ℚ) * ((a : ℤ) : ℚ) ^ 2 = -1 := by exact_mod_cast hab
  have hnorm : Algebra.norm ℚ ((x : K)) = -1 := by
    have hval : ((x : 𝓞 K) : K)
        = (((b : ℤ) : ℚ) : K) + (((a : ℤ) : ℚ) : K) * (θ : K) := by
      rw [hxdef]
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast,
        Rat.cast_intCast]
    rw [hval, norm_add_mul_gen hmin hgen, habq]
  have hunit : IsUnit x := by
    rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, hnorm]
    norm_num
  exact ⟨hunit.unit, by rwa [IsUnit.unit_spec]⟩

/-- **A unit of norm `-1` makes some unit multiple of `θ` totally positive.** Writing the
hypothesis in the conjugation form `u σu = -1`, the companion sign lemma
`isTotallyPositive_or_neg_of_mul_ringOfIntegersQuadraticConj_eq_neg_one` puts `θu` or `-θu` on the
totally positive side, and both are `v • θ` for a unit `v`. -/
theorem exists_unit_isTotallyPositive_smul_gen_of_norm_eq_neg_one
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ}
    (hu : Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1) :
    ∃ v : (𝓞 K)ˣ, IsTotallyPositive (v • (θ : K)) := by
  have hconj : (u : 𝓞 K) * ringOfIntegersQuadraticConj hmin hgen (u : 𝓞 K) = -1 := by
    have := (norm_eq_intCast_iff_mul_ringOfIntegersQuadraticConj_eq_intCast
      (n := -1) hmin hgen (x := (u : 𝓞 K))).mp (by rw [hu]; norm_num)
    simpa using this
  rcases isTotallyPositive_or_neg_of_mul_ringOfIntegersQuadraticConj_eq_neg_one hmin hgen hconj
    with h | h
  · exact ⟨u, by simpa [Units.smul_def, Algebra.smul_def, mul_comm] using h⟩
  · exact ⟨-u, by simpa [Units.smul_def, Algebra.smul_def, mul_comm] using h⟩

/-- **A totally positive unit multiple of `θ` produces a unit of norm `-1`.** Its norm
`N(v) · N(θ) = N(v) · (-d)` is positive, so `N(v)` is negative; and the norm of a unit is `±1`. -/
theorem norm_eq_neg_one_of_isTotallyPositive_smul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) {v : (𝓞 K)ˣ}
    (hv : IsTotallyPositive (v • (θ : K))) :
    Algebra.norm ℚ (((v : 𝓞 K) : K)) = -1 := by
  have hvalue : (v : (𝓞 K)ˣ) • (θ : K) = ((v : 𝓞 K) : K) * (θ : K) := by
    simp [Units.smul_def, Algebra.smul_def]
  have hne : (v : (𝓞 K)ˣ) • (θ : K) ≠ 0 := by
    rw [hvalue]
    exact mul_ne_zero (RingOfIntegers.coe_ne_zero_iff.mpr v.ne_zero) (coe_gen_ne_zero hmin)
  have hpos := norm_pos_of_isTotallyPositive hne hv
  rw [hvalue, map_mul, norm_gen_eq_neg_radicand hmin hgen] at hpos
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rcases mul_ringOfIntegersQuadraticConj_unit_eq_one_or_neg_one hmin hgen v with h | h
  · have hone : Algebra.norm ℚ (((v : 𝓞 K) : K)) = 1 :=
      (norm_eq_intCast_iff_mul_ringOfIntegersQuadraticConj_eq_intCast (n := 1) hmin hgen).mpr
        (by simpa using h)
    rw [hone] at hpos
    nlinarith
  · exact (norm_eq_intCast_iff_mul_ringOfIntegersQuadraticConj_eq_intCast (n := -1) hmin hgen).mpr
      (by simpa using h)

/-- An element of positive norm has a totally positive multiple by `±1`. -/
private theorem exists_unit_isTotallyPositive_smul (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {y : K} (hnorm : 0 < Algebra.norm ℚ y) :
    ∃ ε : (𝓞 K)ˣ, IsTotallyPositive (ε • y) := by
  rcases isTotallyPositive_or_isTotallyPositive_neg_of_norm_pos hmin hgen hnorm with h | h
  · exact ⟨1, by simpa using h⟩
  · exact ⟨-1, by simpa [Units.smul_def, Algebra.smul_def] using h⟩

namespace NarrowClassGroup

/-- **A unit of norm `-1` makes the narrow class group the ordinary one.** Given `x : Kˣ`, its norm
`N(x)` is positive or negative. If positive, `x` or `-x` is already totally positive. If negative,
then `N(θx) = -d · N(x)` is positive, so some `ε · θx` is totally positive; multiplying it by the
totally positive `v · θ` supplied by the hypothesis gives `d · (εv) · x` totally positive, and `d`
is a positive rational. Either way a unit of `𝓞 K` scales `x` to a totally positive element, so
every principal narrow class is trivial and the kernel of `Cl⁺(K) → Cl(K)` vanishes. -/
theorem toClassGroup_injective_of_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ}
    (hu : Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1) :
    Function.Injective (toClassGroup (K := K)) := by
  have hd : 0 < d := radicand_pos_of_norm_eq_neg_one hmin hgen hu
  have hdq : (0 : ℚ) < ((d : ℤ) : ℚ) := by exact_mod_cast hd
  have hsq : (θ : K) ^ 2 = ((((d : ℤ) : ℚ)) : K) := by
    rw [coe_gen_sq_ratCast hmin, eq_ratCast]
  obtain ⟨v, hv⟩ := exists_unit_isTotallyPositive_smul_gen_of_norm_eq_neg_one hmin hgen hu
  rw [← MonoidHom.ker_eq_bot_iff, toClassGroup_ker, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨x, rfl⟩
  rw [mkPrincipal_eq_one_iff]
  have hx : (x : K) ≠ 0 := x.ne_zero
  have hnx : Algebra.norm ℚ ((x : K)) ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (Module.finBasis ℚ K)).mpr hx
  rcases hnx.lt_or_gt with hlt | hgt
  · -- Negative norm: correct it with `θ`, whose norm `-d` is negative too.
    have hypos : 0 < Algebra.norm ℚ ((θ : K) * (x : K)) := by
      rw [map_mul, norm_gen_eq_neg_radicand hmin hgen]
      nlinarith
    obtain ⟨ε, hε⟩ := exists_unit_isTotallyPositive_smul hmin hgen hypos
    refine ⟨v * ε, ?_⟩
    -- The product of the two totally positive elements is `d` times `(vε) • x`.
    have hmul : (v • (θ : K)) * (ε • ((θ : K) * (x : K)))
        = ((((d : ℤ) : ℚ)) : K) * ((v * ε : (𝓞 K)ˣ) • (x : K)) := by
      simp only [Units.smul_def, Algebra.smul_def, Units.val_mul, map_mul]
      rw [← hsq]
      ring
    have hpos : IsTotallyPositive (((((d : ℤ) : ℚ)) : K) * ((v * ε : (𝓞 K)ˣ) • (x : K))) :=
      hmul ▸ hv.mul hε
    have hfinal := (isTotallyPositive_ratCast (K := K) hdq).inv.mul hpos
    rwa [← mul_assoc, inv_mul_cancel₀ (Rat.cast_ne_zero.mpr hdq.ne'), one_mul] at hfinal
  · exact exists_unit_isTotallyPositive_smul hmin hgen hgt

/-- **The narrow and ordinary class groups of a real quadratic field agree exactly when some unit
has norm `-1`.** One direction is `toClassGroup_injective_of_norm_eq_neg_one`. For the other,
injectivity makes the narrow class of the principal ideal `(θ)` trivial, so a unit multiple of `θ`
is totally positive and `norm_eq_neg_one_of_isTotallyPositive_smul_gen` applies. -/
theorem toClassGroup_injective_iff_exists_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) :
    Function.Injective (toClassGroup (K := K)) ↔
      ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
  refine ⟨fun h => ?_, fun ⟨u, hu⟩ => toClassGroup_injective_of_norm_eq_neg_one hmin hgen hu⟩
  -- The narrow class of the principal ideal `(θ)` lies in the kernel, hence is trivial.
  have hker : mkPrincipal (Units.mk0 ((θ : K)) (coe_gen_ne_zero hmin)) = 1 :=
    h (by rw [toClassGroup_mkPrincipal, map_one])
  obtain ⟨v, hv⟩ := mkPrincipal_eq_one_iff.mp hker
  exact ⟨v, norm_eq_neg_one_of_isTotallyPositive_smul_gen hmin hgen hd (by simpa using hv)⟩

/-- **The narrow class number equals the class number exactly when some unit has norm `-1`.**
Forgetting positivity is surjective (`toClassGroup_surjective`) and `Cl⁺(K)` is finite, so equal
cardinalities are equivalent to bijectivity (`Nat.bijective_iff_surjective_and_card`) and hence to
injectivity. This is the classical criterion `h⁺ = h ↔ N(ε) = -1`. -/
theorem card_eq_card_classGroup_iff_exists_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) :
    Nat.card (NarrowClassGroup K) = Nat.card (ClassGroup (𝓞 K)) ↔
      ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
  rw [← toClassGroup_injective_iff_exists_norm_eq_neg_one hmin hgen hd]
  constructor
  · exact fun h =>
      ((Nat.bijective_iff_surjective_and_card _).mpr ⟨toClassGroup_surjective, h⟩).injective
  · exact fun h =>
      ((Nat.bijective_iff_surjective_and_card _).mp ⟨h, toClassGroup_surjective⟩).2

end NarrowClassGroup

end NumberField
