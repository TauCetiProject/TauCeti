/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Componentwise
public import TauCeti.RingTheory.NovikovSeries.Reduced
public import TauCeti.RingTheory.NovikovSeries.TotalQuotient
public import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Algebra.CharP.Two
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.Algebra.Regular.NatCast
import TauCeti.Algebra.Homology.ReidemeisterTorsion.SquareMinor

/-!
# A partially acyclic complex over the Novikov ring of `ℤ/2`

For the deck group `H = ℤ/2` and the zero period homomorphism, the Novikov ring
`Λ = Nov(ℤ, ℤ/2, 0)` is the group ring `ℤ[g]/(g² - 1)`, where `g = e^1` is the deck monomial
of the generator (`TauCeti.NovikovSeries.PartialAcyclicityExample.deck`). Its elements are the
series `a(0) + a(1) g`, and it has two characters to `ℤ`, sending `g` to `1` and to `-1`
(`TauCeti.NovikovSeries.PartialAcyclicityExample.character`). Every nonzerodivisor has nonzero
image under both, because `a (1 + s g) = (a(0) + s a(1)) (1 + s g)` for each sign `s`. So the
characters extend to the total ring of fractions, and together they identify it with `ℚ × ℚ`
(`TauCeti.NovikovSeries.PartialAcyclicityExample.fractionRingEquiv`). The total ring of fractions
is thus a product of two fields of characteristic zero, although `Λ` is not a domain:
`(1 - g) (1 + g) = 0`.

The two-term complex `Λ → Λ` with differential `1 - g` from degree `1` to degree `0`
(`TauCeti.NovikovSeries.PartialAcyclicityExample.twoTermComplex`), based by the generator in each
degree, has partially acyclic total-quotient components. Its coordinate base change along a ring
homomorphism `φ : Λ →+* K` into a field is acyclic exactly when `φ (1 - g) ≠ 0`, and its torsion is
then `φ (1 - g)⁻¹`; since `0⁻¹ = 0` in a field, the formula `τ = φ (1 - g)⁻¹` also covers the
nonacyclic case
(`TauCeti.NovikovSeries.PartialAcyclicityExample.reidemeisterTorsion_matrixBaseChange`).
The two rational components have differentials `0` and `2`, so the componentwise torsion in the
total ring of fractions has components `0` and `1/2`
(`PartialAcyclicityExample.fractionRingEquiv_componentwiseReidemeisterTorsion`).
It is neither `0` nor a unit: a single global zero convention for nonacyclic complexes would lose
the nonzero component.

## Main definitions

* `TauCeti.NovikovSeries.PartialAcyclicityExample.character`: the characters `a ↦ a(0) + s a(1)`
  of `Nov(ℤ, ℤ/2, 0)`, for a sign `s`.
* `TauCeti.NovikovSeries.PartialAcyclicityExample.fractionRingEquiv`: the total ring of fractions
  of `Nov(ℤ, ℤ/2, 0)` is `ℚ × ℚ`.
* `TauCeti.NovikovSeries.PartialAcyclicityExample.twoTermComplex`: the two-term complex with
  differential `1 - g`.

## Main results

* `TauCeti.NovikovSeries.PartialAcyclicityExample.acyclic_matrixBaseChange_iff`,
  `TauCeti.NovikovSeries.PartialAcyclicityExample.reidemeisterTorsion_matrixBaseChange`: the base
  change of the complex to a field is acyclic exactly when `1 - g` maps to a nonzero element, and
  its torsion is the inverse of that element.
* `PartialAcyclicityExample.fractionRingEquiv_componentwiseReidemeisterTorsion`: the
  componentwise torsion corresponds to `(0, 1/2)` in `ℚ × ℚ`.
* `TauCeti.NovikovSeries.PartialAcyclicityExample.componentwiseReidemeisterTorsion_ne_zero`,
  `TauCeti.NovikovSeries.PartialAcyclicityExample.not_isUnit_componentwiseReidemeisterTorsion`:
  the componentwise torsion is neither zero nor a unit.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2 (torsion in the total ring of fractions of a Novikov ring, with zero components on the
  components where the complex is not acyclic).
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §I.2 and §I.3.
-/

public section

noncomputable section

open CategoryTheory Module HomologicalComplex

namespace TauCeti.NovikovSeries.PartialAcyclicityExample

/-! ### The Novikov ring of `ℤ/2` and its characters -/

/-- The deck monomial `g = e^1` of the generator of `ℤ/2` in `Nov(ℤ, ℤ/2, 0)`. -/
def deck : NovikovSeries ℤ (ZMod 2) 0 :=
  single 1 1

/-- The deck monomial is an involution: `g² = 1`. -/
theorem deck_mul_deck : deck * deck = 1 := by
  rw [deck, single_mul_single, one_mul, CharTwo.add_self_eq_zero, single_zero_one]

@[simp]
theorem coeff_deck_zero : deck.coeff 0 = 0 :=
  coeff_single_of_ne zero_ne_one 1

@[simp]
theorem coeff_deck_one : deck.coeff 1 = 1 :=
  coeff_single_same 1 1

/-- Every element of `Nov(ℤ, ℤ/2, 0)` is `a(0) + a(1) g`. -/
theorem eq_single_zero_add_single_one (a : NovikovSeries ℤ (ZMod 2) 0) :
    a = single 0 (a.coeff 0) + single 1 (a.coeff 1) := by
  classical
  ext h
  obtain rfl | rfl : h = 0 ∨ h = 1 := by decide +revert
  all_goals simp [coeff_add]

/-- Multiplication in `Nov(ℤ, ℤ/2, 0)`, constant coefficient:
`(a * b)(0) = a(0) b(0) + a(1) b(1)`. -/
private theorem coeff_mul_zero (a b : NovikovSeries ℤ (ZMod 2) 0) :
    (a * b).coeff 0 = a.coeff 0 * b.coeff 0 + a.coeff 1 * b.coeff 1 := by
  classical
  conv_lhs => rw [eq_single_zero_add_single_one a, eq_single_zero_add_single_one b]
  simp [add_mul, mul_add, single_mul_single, CharTwo.add_self_eq_zero, coeff_add]

/-- Multiplication in `Nov(ℤ, ℤ/2, 0)`, coefficient of `g`:
`(a * b)(1) = a(0) b(1) + a(1) b(0)`. -/
private theorem coeff_mul_one (a b : NovikovSeries ℤ (ZMod 2) 0) :
    (a * b).coeff 1 = a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0 := by
  classical
  conv_lhs => rw [eq_single_zero_add_single_one a, eq_single_zero_add_single_one b]
  simp [add_mul, mul_add, single_mul_single, CharTwo.add_self_eq_zero, coeff_add]
  ring

/-- For a sign `s`, the character of `Nov(ℤ, ℤ/2, 0)` sending the deck monomial `g` to `s`:
`a ↦ a(0) + s a(1)`. -/
def character (s : ℤˣ) : NovikovSeries ℤ (ZMod 2) 0 →+* ℤ where
  toFun a := a.coeff 0 + s * a.coeff 1
  map_one' := by
    classical
    simp [← single_zero_one]
  map_mul' a b := by
    simp only [coeff_mul_zero, coeff_mul_one]
    linear_combination (-(a.coeff 1 * b.coeff 1)) * Int.units_coe_mul_self s
  map_zero' := by simp [coeff_zero]
  map_add' a b := by
    simp only [coeff_add]
    ring

@[simp]
theorem character_apply (s : ℤˣ) (a : NovikovSeries ℤ (ZMod 2) 0) :
    character s a = a.coeff 0 + s * a.coeff 1 :=
  (rfl)

theorem character_deck (s : ℤˣ) : character s deck = s := by
  simp

/-- Multiplication by `1 + s g` acts on `a` as multiplication by the scalar `a(0) + s a(1)`. -/
private theorem mul_one_add_smul_deck (s : ℤˣ) (a : NovikovSeries ℤ (ZMod 2) 0) :
    a * (1 + (s : ℤ) • deck) = character s a • (1 + (s : ℤ) • deck) := by
  classical
  ext h
  obtain rfl | rfl : h = 0 ∨ h = 1 := by decide +revert
  all_goals
    simp only [coeff_mul_zero, coeff_mul_one, coeff_add, coeff_smul, coeff_one, coeff_deck_zero,
      coeff_deck_one, character_apply, smul_eq_mul]
    simp
  · ring
  · linear_combination (-a.coeff 1) * Int.units_coe_mul_self s

/-- A nonzerodivisor of `Nov(ℤ, ℤ/2, 0)` has nonzero image under each character. -/
theorem character_ne_zero_of_mem_nonZeroDivisors (s : ℤˣ) {a : NovikovSeries ℤ (ZMod 2) 0}
    (ha : a ∈ nonZeroDivisors (NovikovSeries ℤ (ZMod 2) 0)) : character s a ≠ 0 := by
  classical
  intro h0
  have hne : (1 + (s : ℤ) • deck : NovikovSeries ℤ (ZMod 2) 0) ≠ 0 := fun h ↦ by
    have := congrArg (fun b : NovikovSeries ℤ (ZMod 2) 0 ↦ b.coeff 0) h
    simp [deck, ← single_zero_one, smul_single, coeff_add] at this
  have := mul_one_add_smul_deck s a
  rw [h0, zero_smul, mul_comm] at this
  exact hne ((mul_right_mem_nonZeroDivisors_eq_zero_iff ha).1 this)

/-- An element of `Nov(ℤ, ℤ/2, 0)` killed by both characters is zero. -/
theorem eq_zero_of_character_eq_zero {a : NovikovSeries ℤ (ZMod 2) 0} (h₁ : character 1 a = 0)
    (h₂ : character (-1) a = 0) : a = 0 := by
  rw [character_apply] at h₁ h₂
  push_cast at h₁ h₂
  rw [eq_single_zero_add_single_one a, show a.coeff 0 = 0 by omega,
    show a.coeff 1 = 0 by omega, single_zero, single_zero, add_zero]

/-! ### The total ring of fractions -/

/-- The extension of the character `character s` to the total ring of fractions, with values in
`ℚ`. -/
def fractionCharacter (s : ℤˣ) : FractionRing (NovikovSeries ℤ (ZMod 2) 0) →+* ℚ :=
  IsLocalization.lift (M := nonZeroDivisors (NovikovSeries ℤ (ZMod 2) 0))
    (g := (Int.castRingHom ℚ).comp (character s)) fun a ↦
      isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 (character_ne_zero_of_mem_nonZeroDivisors s a.2))

@[simp]
theorem fractionCharacter_algebraMap (s : ℤˣ) (a : NovikovSeries ℤ (ZMod 2) 0) :
    fractionCharacter s (algebraMap _ (FractionRing (NovikovSeries ℤ (ZMod 2) 0)) a) =
      character s a :=
  IsLocalization.lift_eq _ a

/-- The extended character on a fraction `a / d` is `character s a / character s d`. -/
theorem fractionCharacter_mk' (s : ℤˣ) (a : NovikovSeries ℤ (ZMod 2) 0)
    (d : nonZeroDivisors (NovikovSeries ℤ (ZMod 2) 0)) :
    fractionCharacter s (IsLocalization.mk' (FractionRing (NovikovSeries ℤ (ZMod 2) 0)) a d) =
      character s a / character s d := by
  rw [eq_div_iff (Int.cast_ne_zero.2 (character_ne_zero_of_mem_nonZeroDivisors s d.2)),
    ← fractionCharacter_algebraMap, ← fractionCharacter_algebraMap, ← _root_.map_mul,
    IsLocalization.mk'_spec]

private theorem fractionCharacter_injective :
    Function.Injective ((fractionCharacter 1).prod (fractionCharacter (-1))) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨⟨a, d⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (NovikovSeries ℤ (ZMod 2) 0)) x
  simp only [RingHom.prod_apply, Prod.mk_eq_zero, fractionCharacter_mk', div_eq_zero_iff,
    Int.cast_eq_zero] at hx
  rw [eq_zero_of_character_eq_zero
      (hx.1.resolve_right (character_ne_zero_of_mem_nonZeroDivisors 1 d.2))
      (hx.2.resolve_right (character_ne_zero_of_mem_nonZeroDivisors (-1) d.2))]
  exact IsLocalization.mk'_zero d

private theorem fractionCharacter_surjective :
    Function.Surjective ((fractionCharacter 1).prod (fractionCharacter (-1))) := by
  intro r
  -- With a common denominator `d`, write `r = (m / d, n / d)`; then `r` is the image of
  -- `((m + n) + (m - n) g) / 2d`.
  obtain ⟨d, m, n, hd0, hm, hn⟩ : ∃ (d : ℕ) (m n : ℤ), d ≠ 0 ∧ (m : ℚ) / d = r.1 ∧
      (n : ℚ) / d = r.2 :=
    ⟨r.1.den * r.2.den, r.1.num * r.2.den, r.2.num * r.1.den,
      Nat.mul_ne_zero r.1.den_nz r.2.den_nz, by
        push_cast
        rw [mul_div_mul_right _ _ (Nat.cast_ne_zero.2 r.2.den_nz), Rat.num_div_den], by
        push_cast
        rw [mul_comm (r.1.den : ℚ), mul_div_mul_right _ _ (Nat.cast_ne_zero.2 r.1.den_nz),
          Rat.num_div_den]⟩
  have h2d : ((2 * d : ℕ) : NovikovSeries ℤ (ZMod 2) 0) ∈ nonZeroDivisors _ :=
    natCast_mem_nonZeroDivisors (by positivity)
  have hval (s : ℤˣ) : fractionCharacter s (IsLocalization.mk' _
      (single 0 (m + n) + single 1 (m - n)) ⟨_, h2d⟩) =
        (((m + n) + s * (m - n) : ℤ) : ℚ) / (2 * d) := by
    rw [fractionCharacter_mk', _root_.map_natCast]
    simp [coeff_add]
  refine ⟨IsLocalization.mk' _ (single 0 (m + n) + single 1 (m - n)) ⟨_, h2d⟩,
    Prod.ext ?_ ?_⟩
  · simp only [RingHom.prod_apply, hval, ← hm]
    push_cast
    field_simp
    ring
  · simp only [RingHom.prod_apply, hval, ← hn]
    push_cast
    field_simp
    ring

/-- The total ring of fractions of `Nov(ℤ, ℤ/2, 0)` is `ℚ × ℚ`, through the two characters
sending the deck monomial to `1` and to `-1`. -/
def fractionRingEquiv : FractionRing (NovikovSeries ℤ (ZMod 2) 0) ≃+* ℚ × ℚ :=
  RingEquiv.ofBijective ((fractionCharacter 1).prod (fractionCharacter (-1)))
    ⟨fractionCharacter_injective, fractionCharacter_surjective⟩

@[simp]
theorem fractionRingEquiv_apply (x : FractionRing (NovikovSeries ℤ (ZMod 2) 0)) :
    fractionRingEquiv x = (fractionCharacter 1 x, fractionCharacter (-1) x) :=
  (rfl)

/-- The total ring of fractions of `Nov(ℤ, ℤ/2, 0)` is Artinian, as is that of every Novikov ring
over a domain on a finitely generated abelian group. -/
instance : IsArtinianRing (FractionRing (NovikovSeries ℤ (ZMod 2) 0)) :=
  isArtinianRing_of_isFractionRing (H := ZMod 2) ℤ 0 _

/-! ### The two-term complex with differential `1 - g` -/

/-- The ranks of the two-term complex: one generator in degrees `0` and `1`, none elsewhere. -/
def twoTermRank (i : ℤ) : ℕ :=
  if i = 0 ∨ i = 1 then 1 else 0

/-- The matrix of the differential from degree `i + 1` to degree `i`: the `1 × 1` matrix `1 - g`
for `i = 0`, and zero otherwise. -/
def twoTermMatrix (i : ℤ) :
    Matrix (Fin (twoTermRank i)) (Fin (twoTermRank (i + 1))) (NovikovSeries ℤ (ZMod 2) 0) :=
  if i = 0 then .of fun _ _ ↦ 1 - deck else 0

private theorem twoTermMatrix_mul_twoTermMatrix (i : ℤ) :
    twoTermMatrix i * twoTermMatrix (i + 1) = 0 := by
  by_cases hi : i = 0
  · subst hi
    simp [twoTermMatrix]
  · simp [twoTermMatrix, hi]

/-- The two-term complex `Λ → Λ`, with differential `1 - g` from degree `1` to degree `0`, over
`Λ = Nov(ℤ, ℤ/2, 0)`. -/
def twoTermComplex : ChainComplex (ModuleCat (NovikovSeries ℤ (ZMod 2) 0)) ℤ :=
  ChainComplex.of (fun i ↦ ModuleCat.of _ (Fin (twoTermRank i) → NovikovSeries ℤ (ZMod 2) 0))
    (fun i ↦ ModuleCat.ofHom (Matrix.toLin' (twoTermMatrix i))) fun i ↦ by
      ext1
      simp [← Matrix.toLin'_mul, twoTermMatrix_mul_twoTermMatrix]

/-- The standard basis of the two-term complex in degree `i`. -/
def twoTermBasis (i : ℤ) :
    Basis (Fin (twoTermRank i)) (NovikovSeries ℤ (ZMod 2) 0) (twoTermComplex.X i) :=
  Pi.basisFun _ (Fin (twoTermRank i))

/-- The matrices of the differentials of the two-term complex in its standard bases. -/
@[simp]
theorem toMatrix_twoTermComplex_d (i : ℤ) :
    LinearMap.toMatrix (twoTermBasis (i + 1)) (twoTermBasis i) (twoTermComplex.d (i + 1) i).hom =
      twoTermMatrix i := by
  simp only [twoTermComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  -- `twoTermBasis i` is `Pi.basisFun` by definition, and `Matrix.toLin'` is `Matrix.toLin` in
  -- the standard bases; the module structure on `twoTermComplex.X i` is that of
  -- `Fin (twoTermRank i) → Λ` only after unfolding `ModuleCat.of`, so the lemma is applied with
  -- `exact` rather than rewritten with.
  exact LinearMap.toMatrix_toLin (Pi.basisFun _ (Fin (twoTermRank (i + 1))))
    (Pi.basisFun _ (Fin (twoTermRank i))) _

private theorem finite_twoTermRank : {i | twoTermRank i ≠ 0}.Finite :=
  (Set.toFinite {0, 1}).subset fun i hi ↦ by
    by_contra h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact hi (ite_eq_right_iff.2 fun h' ↦ (h h').elim)

/-! ### Torsion of the base changes to fields -/

section Field

variable {K : Type*} [Field K] (φ : NovikovSeries ℤ (ZMod 2) 0 →+* K)

/-- The first block of the split bases for the square-minor formula: the generator in degree `0`.
-/
private abbrev minorRows (i : ℤ) : ℕ :=
  if i = 0 then 1 else 0

/-- The second block of the split bases for the square-minor formula: the generator in degree `1`.
-/
private abbrev minorCols (i : ℤ) : ℕ :=
  if i = 1 then 1 else 0

private theorem twoTermRank_eq_add (i : ℤ) : twoTermRank i = minorRows i + minorCols i := by
  simp only [twoTermRank, minorRows, minorCols]
  split_ifs <;> omega

private theorem minorCols_add_one (j : ℤ) : minorCols (j + 1) = minorRows j := by
  simp only [minorRows, minorCols]
  split_ifs <;> omega

private theorem det_torsionMinor (j : ℤ) :
    (torsionMinor (twoTermComplex.matrixBaseChangeBasis twoTermBasis φ) twoTermRank_eq_add
      minorCols_add_one j).det = if j = 0 then φ (1 - deck) else 1 := by
  split_ifs with hj
  · subst hj
    rw [Matrix.det_eq_elem_of_card_eq_one (by simp) ⟨0, by simp [minorRows]⟩, torsionMinor_apply,
      ← LinearMap.toMatrix_apply, toMatrix_matrixBaseChange_d, toMatrix_twoTermComplex_d]
    simp [twoTermMatrix]
  · exact Matrix.det_eq_one_of_card_eq_zero (by simp [hj])

private theorem det_torsionMinor_ne_zero (h : φ (1 - deck) ≠ 0) (j : ℤ) :
    (torsionMinor (twoTermComplex.matrixBaseChangeBasis twoTermBasis φ) twoTermRank_eq_add
      minorCols_add_one j).det ≠ 0 := by
  rw [det_torsionMinor]
  split_ifs
  exacts [h, one_ne_zero]

/-- The coordinate base change of the two-term complex to a field `K` along `φ` is acyclic exactly
when `φ (1 - g) ≠ 0`. -/
theorem acyclic_matrixBaseChange_iff :
    (twoTermComplex.matrixBaseChange twoTermBasis φ).Acyclic ↔ φ (1 - deck) ≠ 0 := by
  refine ⟨fun h h0 ↦ ?_, fun h ↦ acyclic_of_det_torsionMinor_ne_zero
    (c := twoTermComplex.matrixBaseChangeBasis twoTermBasis φ) (hn := twoTermRank_eq_add)
    (hpq := minorCols_add_one) (det_torsionMinor_ne_zero φ h)⟩
  · -- In degree `0` the incoming differential `φ (1 - g) = 0` and the outgoing one, to the zero
    -- space in degree `-1`, both vanish, while the term is one-dimensional.
    let D := twoTermComplex.matrixBaseChange twoTermBasis φ
    let b := twoTermComplex.matrixBaseChangeBasis twoTermBasis φ
    have (i : ℤ) : Module.Finite K (D.X i) := Module.Finite.of_basis (b i)
    have hX (i : ℤ) : finrank K (D.X i) = twoTermRank i := by
      rw [finrank_eq_card_basis (b i), Fintype.card_fin]
    have hin : (D.d (0 + 1) 0).hom = 0 := by
      rw [hom_matrixBaseChange_d, toMatrix_twoTermComplex_d]
      convert map_zero (Matrix.toLin (b (0 + 1)) (b 0))
      ext r k
      simp [twoTermMatrix, h0]
    have hout : finrank K (LinearMap.range (D.d 0 (0 - 1)).hom) = 0 :=
      Nat.eq_zero_of_le_zero ((Submodule.finrank_le _).trans (by simp [hX, twoTermRank]))
    have := (exactAt_iff_finrank_add_finrank D (ChainComplex.prev ℤ 0)
      (ChainComplex.next ℤ 0)).1 (h 0)
    rw [hin, LinearMap.range_zero, finrank_bot, hout, hX] at this
    simp [twoTermRank] at this

/-- The torsion of the coordinate base change of the two-term complex to a field `K` along `φ` is
`φ (1 - g)⁻¹`. This is the normalization `τ = a⁻¹` of a differential `a ≠ 0` from degree `1` to
degree `0`; when `φ (1 - g) = 0` the base change is not acyclic, and both sides are `0`. -/
theorem reidemeisterTorsion_matrixBaseChange :
    (twoTermComplex.matrixBaseChange twoTermBasis φ).reidemeisterTorsion
      (twoTermComplex.matrixBaseChangeBasis twoTermBasis φ) = (φ (1 - deck))⁻¹ := by
  by_cases h : φ (1 - deck) = 0
  · rw [h, inv_zero, reidemeisterTorsion_eq_zero_iff _ _ finite_twoTermRank,
      acyclic_matrixBaseChange_iff, not_not, h]
  · rw [reidemeisterTorsion_eq_finprod_det_torsionMinor (det_torsionMinor_ne_zero φ h)
        finite_twoTermRank,
      finprod_eq_single _ 0 fun j hj ↦ by simp [det_torsionMinor, hj]]
    simp [det_torsionMinor]

end Field

/-! ### The componentwise torsion in the total ring of fractions -/

/-- **Partial acyclicity.** The componentwise torsion of the two-term complex with differential
`1 - g` over `Nov(ℤ, ℤ/2, 0)`, in its total ring of fractions `ℚ × ℚ`, has components `0` and
`1/2`: the component where `g = 1` has differential `0` and is not acyclic, and the component where
`g = -1` has differential `2`. -/
theorem fractionRingEquiv_componentwiseReidemeisterTorsion :
    fractionRingEquiv (twoTermComplex.componentwiseReidemeisterTorsion twoTermBasis
      (algebraMap _ (FractionRing (NovikovSeries ℤ (ZMod 2) 0)))) = (0, 2⁻¹) := by
  have key (s : ℤˣ) :
      fractionCharacter s (twoTermComplex.componentwiseReidemeisterTorsion twoTermBasis
        (algebraMap _ (FractionRing (NovikovSeries ℤ (ZMod 2) 0)))) = ((1 - s : ℤ) : ℚ)⁻¹ := by
    rw [map_componentwiseReidemeisterTorsion,
      componentwiseReidemeisterTorsion_eq_reidemeisterTorsion_matrixBaseChange,
      reidemeisterTorsion_matrixBaseChange]
    simp
  rw [fractionRingEquiv_apply, key, key]
  norm_num

/-- The componentwise torsion of the two-term complex is nonzero: the complex is acyclic on the
component where `g = -1`. -/
theorem componentwiseReidemeisterTorsion_ne_zero :
    twoTermComplex.componentwiseReidemeisterTorsion twoTermBasis
      (algebraMap _ (FractionRing (NovikovSeries ℤ (ZMod 2) 0))) ≠ 0 := fun h ↦ by
  simpa [h] using fractionRingEquiv_componentwiseReidemeisterTorsion

/-- The componentwise torsion of the two-term complex is not a unit: the complex is not acyclic on
the component where `g = 1`. -/
theorem not_isUnit_componentwiseReidemeisterTorsion :
    ¬IsUnit (twoTermComplex.componentwiseReidemeisterTorsion twoTermBasis
      (algebraMap _ (FractionRing (NovikovSeries ℤ (ZMod 2) 0)))) := fun h ↦ by
  have := (h.map fractionRingEquiv).map (RingHom.fst ℚ ℚ)
  rw [fractionRingEquiv_componentwiseReidemeisterTorsion] at this
  simp at this

end TauCeti.NovikovSeries.PartialAcyclicityExample
