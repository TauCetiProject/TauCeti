/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Zero
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.IndexTwo.CupExact
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialGroup
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.DirectSum.Finsupp

/-!
# The mod-two cohomology algebra of a group of order two

For a discrete group of order two, cup product with its unique nonzero character is an
isomorphism in every degree. Consequently its canonical graded continuous cohomology algebra
is the polynomial algebra on that degree-one character.

The calculation uses the index-two restriction–corestriction exact sequence for the trivial
subgroup. Positive cohomology of that subgroup vanishes, and degree-zero corestriction is
multiplication by two. The resulting degreewise equivalences give the polynomial-algebra
identification, with its generator and homogeneous monomials explicitly normalized.
The forward equations involving `DirectSum.of` retain the caller's equality decision on degrees;
the algebra equivalence itself is independent of that decision.

The classical polynomial-ring calculation is A. Hatcher, *Algebraic Topology*,
Theorem 3.19, p. 220, via the classifying space `ℝP∞ = BC₂`. The formal proof here instead
uses the index-two coefficient sequence. The cup identities are from K. S. Brown,
*Cohomology of Groups*, Chapter V, §3.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory DirectSum Polynomial

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G]

private def cyclicTwoSubgroup : OpenSubgroup G :=
  ⟨⊥, isOpen_discrete _⟩

omit [IsTopologicalGroup G] in
private theorem cyclicTwoSubgroup_index (hG : Nat.card G = 2) :
    (cyclicTwoSubgroup G).toSubgroup.index = 2 :=
  Subgroup.index_bot.trans hG

/-- The nontrivial degree-one character class of a discrete group of order two. -/
def cyclicTwoCharacterClass (hG : Nat.card G = 2) : cohomF2 G 1 :=
  (cyclicTwoSubgroup G).indexTwoCharacterClass (cyclicTwoSubgroup_index G hG)

/-- The generator is the class of the continuous character with trivial kernel. -/
theorem cyclicTwoCharacterClass_eq_homClass (hG : Nat.card G = 2) :
    cyclicTwoCharacterClass G hG = ContCohomology.homClass G
      ((⊥ : Subgroup G).indexTwoCharacter (Subgroup.index_bot.trans hG))
      continuous_of_discreteTopology := by
  rw [cyclicTwoCharacterClass, OpenSubgroup.indexTwoCharacterClass_def,
    ContCohomology.homClass_def]
  -- The chosen open subgroup reduces to bottom; proof irrelevance identifies the
  -- index and continuity witnesses in the two character-class constructions.
  rfl

-- The additive map preserves the selected cohomology carriers. Flipping the integral
-- bilinear map instead selects incompatible integral scalar-action presentations.
private def cyclicTwoCupAddHom (hG : Nat.card G = 2) (n : ℕ) :
    cohomF2 G n →+ cohomF2 G (n + 1) where
  toFun x := (trivialF2TopPairing G).cup n 1 x (cyclicTwoCharacterClass G hG)
  map_zero' := by simp
  map_add' x y := by simp

private theorem cyclicTwoCor_eq_zero (hG : Nat.card G = 2) (n : ℕ)
    (x : cohomF2 (cyclicTwoSubgroup G).toSubgroup n) :
    let : Finite G := Nat.finite_of_card_ne_zero (by omega)
    let : (cyclicTwoSubgroup G).toSubgroup.FiniteIndex := ⟨by
      rw [cyclicTwoSubgroup_index G hG]; decide⟩
    trivialF2CorMap G (cyclicTwoSubgroup G).toSubgroup (cyclicTwoSubgroup G).isOpen' n x = 0 := by
  let : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let : (cyclicTwoSubgroup G).toSubgroup.FiniteIndex := ⟨by
    rw [cyclicTwoSubgroup_index G hG]; decide⟩
  dsimp only
  cases n with
  | zero =>
    obtain ⟨y, rfl⟩ := trivialF2ResMap_zero_surjective G (cyclicTwoSubgroup G).toSubgroup x
    rw [trivialF2CorMap_trivialF2ResMap, cyclicTwoSubgroup_index G hG, cohomF2.two_nsmul_eq_zero]
  | succ n =>
    have : Subsingleton (cyclicTwoSubgroup G).toSubgroup := inferInstanceAs
      (Subsingleton (⊥ : Subgroup G))
    rw [Subsingleton.elim x 0, map_zero]

/-- Cup product with the character of an order-two discrete group is bijective in every
nonnegative degree, including degree zero. -/
theorem bijective_cup_cyclicTwoCharacterClass (hG : Nat.card G = 2) (n : ℕ) :
    Function.Bijective (fun x : cohomF2 G n ↦
      (trivialF2TopPairing G).cup n 1 x (cyclicTwoCharacterClass G hG)) := by
  let : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let U := cyclicTwoSubgroup G
  have hU : U.toSubgroup.index = 2 := cyclicTwoSubgroup_index G hG
  let : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  have : Subsingleton U.toSubgroup := inferInstanceAs (Subsingleton (⊥ : Subgroup G))
  have hex := U.exact_cor_cup_of_index_two hU n
  have hsurj := U.exact_cup_res_of_index_two hU n
  constructor
  · apply (injective_iff_map_eq_zero (cyclicTwoCupAddHom G hG n)).2
    intro x hx
    obtain ⟨y, hy⟩ := (hex x).1 hx
    exact hy.symm.trans (cyclicTwoCor_eq_zero G hG n y)
  · intro y
    exact (hsurj y).1 (Subsingleton.elim _ _)

/-- Multiplication by the degree-one character, as a linear equivalence between successive
mod-two continuous cohomology groups. -/
def cyclicTwoCupLinearEquiv (hG : Nat.card G = 2) (n : ℕ) :
    cohomF2 G n ≃ₗ[ZMod 2] cohomF2 G (n + 1) :=
  LinearEquiv.ofBijective
    ((cyclicTwoCupAddHom G hG n).toZModLinearMap 2) (bijective_cup_cyclicTwoCharacterClass G hG n)

/-- The periodicity equivalence is cup product with the character. -/
theorem cyclicTwoCupLinearEquiv_apply (hG : Nat.card G = 2) (n : ℕ) (x : cohomF2 G n) :
    cyclicTwoCupLinearEquiv G hG n x =
      (trivialF2TopPairing G).cup n 1 x (cyclicTwoCharacterClass G hG) :=
  (rfl)

/-- The canonical generator in every degree, obtained by iterated cup product with the
nontrivial character, identifies that degree with `ZMod 2`. -/
def cyclicTwoCohomLinearEquiv (hG : Nat.card G = 2) :
    (n : ℕ) → ZMod 2 ≃ₗ[ZMod 2] cohomF2 G n
  | 0 => (cohomF2ZeroLinearEquiv G).symm
  | n + 1 => (cyclicTwoCohomLinearEquiv hG n).trans (cyclicTwoCupLinearEquiv G hG n)

/-- The degree-zero generator is the unit class. -/
theorem cyclicTwoCohomLinearEquiv_zero_one (hG : Nat.card G = 2) :
    cyclicTwoCohomLinearEquiv G hG 0 1 = 1 := by
  apply (cohomF2ZeroLinearEquiv G).injective
  simp [cyclicTwoCohomLinearEquiv]

/-- The generators in successive degrees differ by cup product with the character. -/
theorem cyclicTwoCohomLinearEquiv_succ (hG : Nat.card G = 2) (n : ℕ) (r : ZMod 2) :
    cyclicTwoCohomLinearEquiv G hG (n + 1) r =
      (trivialF2TopPairing G).cup n 1 (cyclicTwoCohomLinearEquiv G hG n r)
        (cyclicTwoCharacterClass G hG) :=
  (rfl)

private theorem of_cyclicTwoCohomLinearEquiv_one (hG : Nat.card G = 2) (n : ℕ) :
    DirectSum.of (cohomF2 G) n (cyclicTwoCohomLinearEquiv G hG n 1) =
      (DirectSum.of (cohomF2 G) 1 (cyclicTwoCharacterClass G hG)) ^ n := by
  induction n with
  | zero => simp [cyclicTwoCohomLinearEquiv_zero_one]
  | succ n ih => rw [pow_succ, ← ih, cohomF2.of_mul_of, cyclicTwoCohomLinearEquiv_succ]

/-- The normalized degree-one generator is the nontrivial character. -/
@[simp]
theorem cyclicTwoCohomLinearEquiv_one_one (hG : Nat.card G = 2) :
    cyclicTwoCohomLinearEquiv G hG 1 1 = cyclicTwoCharacterClass G hG := by
  apply DirectSum.of_injective 1
  simpa using of_cyclicTwoCohomLinearEquiv_one G hG 1

/-- The normalized degree-one coordinate of the nontrivial character is one. -/
@[simp]
theorem cyclicTwoCohomLinearEquiv_symm_character (hG : Nat.card G = 2) :
    (cyclicTwoCohomLinearEquiv G hG 1).symm (cyclicTwoCharacterClass G hG) = 1 := by
  apply (cyclicTwoCohomLinearEquiv G hG 1).injective
  simp only [LinearEquiv.apply_symm_apply, cyclicTwoCohomLinearEquiv_one_one]

private def cyclicTwoPolynomialLinearEquiv (hG : Nat.card G = 2) :
    (ZMod 2)[X] ≃ₗ[ZMod 2] gradedCohomF2 G :=
  (Polynomial.toFinsuppIsoLinear (ZMod 2)).trans
    ((AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).trans
      ((finsuppLEquivDirectSum (ZMod 2) (ZMod 2) ℕ).trans
        (DirectSum.congrLinearEquiv (cyclicTwoCohomLinearEquiv G hG))))

private theorem cyclicTwoPolynomialLinearEquiv_monomial (hG : Nat.card G = 2)
    (n : ℕ) (r : ZMod 2) :
    cyclicTwoPolynomialLinearEquiv G hG (monomial n r) =
      DirectSum.of (cohomF2 G) n (cyclicTwoCohomLinearEquiv G hG n r) := by
  simp [cyclicTwoPolynomialLinearEquiv, DirectSum.coe_congrLinearEquiv,
    DirectSum.lof_eq_of, Polynomial.toFinsuppIsoLinear, Polynomial.toFinsupp_monomial]

private theorem cyclicTwoPolynomialLinearEquiv_apply_component (hG : Nat.card G = 2)
    (p : (ZMod 2)[X]) (n : ℕ) :
    (cyclicTwoPolynomialLinearEquiv G hG p) n =
      cyclicTwoCohomLinearEquiv G hG n (p.coeff n) := by
  simp only [cyclicTwoPolynomialLinearEquiv, LinearEquiv.trans_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_apply, finsuppLEquivDirectSum_apply,
    AddMonoidAlgebra.coeffLinearEquiv_apply, Polynomial.toFinsuppIsoLinear_apply,
    Polynomial.toFinsupp_apply, LinearEquiv.coe_toLinearMap]

private theorem cyclicTwoPolynomialLinearEquiv_eq_aeval (hG : Nat.card G = 2)
    (p : (ZMod 2)[X]) :
    cyclicTwoPolynomialLinearEquiv G hG p =
      aeval (DirectSum.of (cohomF2 G) 1 (cyclicTwoCharacterClass G hG)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n r =>
    rw [cyclicTwoPolynomialLinearEquiv_monomial, aeval_monomial,
      ← Algebra.smul_def, ← of_cyclicTwoCohomLinearEquiv_one, ← DirectSum.of_smul,
      ← map_smul, smul_eq_mul, mul_one]

/-- The canonical graded mod-two cohomology algebra of an order-two discrete group is a
polynomial algebra, with `X` sent to its nontrivial character in degree one. -/
def cyclicTwoCohomPolynomialEquiv (hG : Nat.card G = 2) :
    (ZMod 2)[X] ≃ₐ[ZMod 2] gradedCohomF2 G :=
  AlgEquiv.ofBijective
    (aeval (DirectSum.of (cohomF2 G) 1 (cyclicTwoCharacterClass G hG)))
    (by
      have h := funext (cyclicTwoPolynomialLinearEquiv_eq_aeval G hG)
      exact h ▸ (cyclicTwoPolynomialLinearEquiv G hG).bijective)

/-- The polynomial generator is the character class in degree one. -/
@[simp]
theorem cyclicTwoCohomPolynomialEquiv_X [h : DecidableEq ℕ] (hG : Nat.card G = 2) :
    cyclicTwoCohomPolynomialEquiv G hG X =
      DirectSum.of (cohomF2 G) 1 (cyclicTwoCharacterClass G hG) := by
  cases Subsingleton.elim h Nat.decEq
  simp [cyclicTwoCohomPolynomialEquiv]

/-- A monomial is the corresponding normalized homogeneous cohomology class. -/
-- Keep this equation named so that generic inverse laws still match on monomials.
theorem cyclicTwoCohomPolynomialEquiv_monomial [h : DecidableEq ℕ]
    (hG : Nat.card G = 2) (n : ℕ) (r : ZMod 2) :
    cyclicTwoCohomPolynomialEquiv G hG (monomial n r) =
      DirectSum.of (cohomF2 G) n (cyclicTwoCohomLinearEquiv G hG n r) := by
  cases Subsingleton.elim h Nat.decEq
  exact (cyclicTwoPolynomialLinearEquiv_eq_aeval G hG _).symm.trans
    (cyclicTwoPolynomialLinearEquiv_monomial G hG n r)

/-- The inverse sends a homogeneous class to the monomial with its normalized coefficient. -/
theorem cyclicTwoCohomPolynomialEquiv_symm_of (hG : Nat.card G = 2) (n : ℕ)
    (x : cohomF2 G n) :
    (cyclicTwoCohomPolynomialEquiv G hG).symm (DirectSum.of (cohomF2 G) n x) =
      monomial n ((cyclicTwoCohomLinearEquiv G hG n).symm x) := by
  apply (cyclicTwoCohomPolynomialEquiv G hG).injective
  simp only [AlgEquiv.apply_symm_apply, cyclicTwoCohomPolynomialEquiv_monomial,
    LinearEquiv.apply_symm_apply]

/-- The inverse sends the degree-one character to the polynomial generator. -/
@[simp]
theorem cyclicTwoCohomPolynomialEquiv_symm_character (hG : Nat.card G = 2) :
    (cyclicTwoCohomPolynomialEquiv G hG).symm
      (DirectSum.of (cohomF2 G) 1 (cyclicTwoCharacterClass G hG)) = X := by
  apply (cyclicTwoCohomPolynomialEquiv G hG).injective
  simp only [AlgEquiv.apply_symm_apply, cyclicTwoCohomPolynomialEquiv_X]

/-- The coefficient of a polynomial is the coordinate of its homogeneous cohomology class. -/
theorem cyclicTwoCohomPolynomialEquiv_apply_component (hG : Nat.card G = 2)
    (p : (ZMod 2)[X]) (n : ℕ) :
    (cyclicTwoCohomPolynomialEquiv G hG p) n =
      cyclicTwoCohomLinearEquiv G hG n (p.coeff n) := by
  -- `ofBijective` retains the evaluation homomorphism as its underlying function.
  change (aeval (DirectSum.of (cohomF2 G) 1 (cyclicTwoCharacterClass G hG)) p) n = _
  rw [← cyclicTwoPolynomialLinearEquiv_eq_aeval G hG]
  exact cyclicTwoPolynomialLinearEquiv_apply_component G hG p n

/-- The inverse polynomial has the coordinates supplied by the normalized degreewise
equivalences. -/
@[simp]
theorem cyclicTwoCohomPolynomialEquiv_symm_coeff (hG : Nat.card G = 2)
    (z : gradedCohomF2 G) (n : ℕ) :
    ((cyclicTwoCohomPolynomialEquiv G hG).symm z).coeff n =
      (cyclicTwoCohomLinearEquiv G hG n).symm (z n) := by
  apply (cyclicTwoCohomLinearEquiv G hG n).injective
  rw [← cyclicTwoCohomPolynomialEquiv_apply_component]
  simp

/-- The degree-one character class of an order-two group is nonzero. -/
theorem cyclicTwoCharacterClass_ne_zero (hG : Nat.card G = 2) :
    cyclicTwoCharacterClass G hG ≠ 0 := by
  intro h
  have hx : cyclicTwoCohomPolynomialEquiv G hG X = 0 := by
    rw [cyclicTwoCohomPolynomialEquiv_X, h, map_zero]
  exact Polynomial.X_ne_zero ((cyclicTwoCohomPolynomialEquiv G hG).injective
    (hx.trans (map_zero _).symm))

end TauCeti
