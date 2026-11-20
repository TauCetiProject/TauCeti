/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Exponential
public import TauCeti.Algebra.Lie.Filtered.Action
public import TauCeti.Algebra.Lie.Graded.Completion

/-!
# Exponential automorphisms of completed filtered modules

Let a positively graded Lie algebra act on a module with a decreasing filtration starting at
the whole module. If the action raises filtration, its action on the quotient by order `k + 1`
is nilpotent of exponent at most `k + 1`. Over a rational algebra the finite exponential is
therefore a linear automorphism. Lie and module truncations intertwine these automorphisms.

An element of the degree-completed Lie algebra consequently defines a linear automorphism of
the module completion `limₖ M / F (k + 1)`. Its coordinates are the finite exponentials, and
negation gives the inverse. This supplies the exponential automorphisms underlying the
completed filtered-module actions.

The finite automorphism is `PositiveDegrees.truncatedExpLieAction`, with its truncated-series
formula `PositiveDegrees.truncatedExpLieAction_apply_eq_sum`. The completed automorphism is
`PositiveDegrees.completedExpLieAction`; `PositiveDegrees.coe_completedExpLieAction_apply` computes
its projections through the canonical quotient equivalence.

Adapted from `Mei/Algebra/Lie/Filtered/Module.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0). The completion uses the existing
`ModuleTower.quotients` and `ModuleTower.limExp` constructions.
-/

public section

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti.PositiveDegrees

open CategoryTheory Opposite

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  (F : ℕ → Submodule R M) (hF : Antitone F) (hF0 : F 0 = ⊤)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

/-- Rational scalars on the module quotients come from the coefficient algebra. -/
local instance quotientRatModule (k : ℕ) : Module ℚ (M ⧸ F (k + 1)) :=
  Module.compHom (M ⧸ F (k + 1)) (algebraMap ℚ R)

/-- Exponentiate a truncated Lie element on the matching filtered-module quotient. -/
def truncatedExpLieAction (k : ℕ) (x : d.truncatedLie ℒ k) :
    (M ⧸ F (k + 1)) ≃ₗ[R] (M ⧸ F (k + 1)) :=
  (d.truncatedLieAction ℒ F hF hF0 k x).locallyNilpotentExp
    (IsNilpotent.exists_pow_apply_eq_zero
      ⟨k + 1, d.truncatedLieAction_pow_eq_zero ℒ F hF hF0 k x⟩)

/-- The finite automorphism is the nilpotent endomorphism exponential. -/
@[simp]
theorem truncatedExpLieAction_toLinearMap (k : ℕ) (x : d.truncatedLie ℒ k) :
    (d.truncatedExpLieAction ℒ F hF hF0 k x).toLinearMap =
      IsNilpotent.exp (d.truncatedLieAction ℒ F hF hF0 k x) :=
  Module.End.locallyNilpotentExp_eq_exp _
    ⟨k + 1, d.truncatedLieAction_pow_eq_zero ℒ F hF hF0 k x⟩

/-- The finite exponential can be evaluated by its `k + 1` terms. -/
theorem truncatedExpLieAction_apply_eq_sum (k : ℕ) (x : d.truncatedLie ℒ k)
    (m : M ⧸ F (k + 1)) :
    d.truncatedExpLieAction ℒ F hF hF0 k x m =
      ∑ i ∈ Finset.range (k + 1), (i.factorial : ℚ)⁻¹ •
        (d.truncatedLieAction ℒ F hF hF0 k x ^ i) m :=
  Module.End.locallyNilpotentExp_apply_eq_sum _ _ (by
    rw [d.truncatedLieAction_pow_eq_zero ℒ F hF hF0, LinearMap.zero_apply])

/-- Negating the truncated Lie element gives the inverse module automorphism. -/
@[simp]
theorem truncatedExpLieAction_neg (k : ℕ) (x : d.truncatedLie ℒ k) :
    d.truncatedExpLieAction ℒ F hF hF0 k (-x) =
      (d.truncatedExpLieAction ℒ F hF hF0 k x).symm := by
  simp only [truncatedExpLieAction, map_neg, Module.End.locallyNilpotentExp_symm]

/-- Zero acts as the identity on every finite quotient. -/
@[simp]
theorem truncatedExpLieAction_zero (k : ℕ) :
    d.truncatedExpLieAction ℒ F hF hF0 k 0 = LinearEquiv.refl R _ := by
  apply LinearEquiv.toLinearMap_injective
  rw [truncatedExpLieAction_toLinearMap, map_zero, IsNilpotent.exp_zero]
  rfl

/-- Lie and module truncations intertwine the finite exponential automorphisms. -/
@[simp]
theorem factor_truncatedExpLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (m : M ⧸ F (l + 1)) :
    Submodule.factor (hF (Nat.add_le_add_right h 1))
        (d.truncatedExpLieAction ℒ F hF hF0 l x m) =
      d.truncatedExpLieAction ℒ F hF hF0 k (d.truncationMap ℒ h x)
        (Submodule.factor (hF (Nat.add_le_add_right h 1)) m) :=
  Module.End.map_locallyNilpotentExp _ _ _ _
    (d.factor_truncatedLieAction ℒ F hF hF0 h x) m

local notation "T" => ModuleTower.quotients (fun k ↦ F (k + 1))
  (hF.comp_monotone (monotone_id.add_const 1))

local notation "π" => LieIdeal.completionProjection
  (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- Every term of a tower over a rational algebra inherits rational scalar multiplication. -/
local instance towerRatModule (T' : ModuleTower R) : ∀ k : ℕ, Module ℚ (T'.obj (op k)) :=
  fun k ↦ Module.compHom (T'.obj (op k)) (algebraMap ℚ R)

local notation "q" => (fun k : ℕ ↦ ModuleTower.quotientsLiftEquiv
  (fun k ↦ F (k + 1)) (hF.comp_monotone (monotone_id.add_const 1)) k
  (Submodule.mkQ (F (k + 1))) (Submodule.ker_mkQ _) (Submodule.mkQ_surjective _))

/-- The completed Lie element acts on each tower term through the quotient equivalence. -/
private def completionAction (x : d.completedLie ℒ) (k : ℕ) :
    Module.End R ((T).obj (op k)) :=
  ((q) k).symm.conjRingEquiv (d.truncatedLieAction ℒ F hF hF0 k (π k x))

omit [Algebra ℚ R] in
private theorem completionAction_nilpotent (x : d.completedLie ℒ) (k : ℕ) :
    IsNilpotent (d.completionAction ℒ F hF hF0 x k) :=
  (IsNilpotent.map ⟨k + 1, d.truncatedLieAction_pow_eq_zero ℒ F hF hF0 k (π k x)⟩
    ((q) k).symm.conjRingEquiv)

omit [Algebra ℚ R] in
private theorem completionAction_compatible (x : d.completedLie ℒ) {k l : ℕ} (h : k ≤ l) :
    Function.Semiconj ((T).transitionOfLE h)
      (d.completionAction ℒ F hF hF0 x l) (d.completionAction ℒ F hF hF0 x k) := by
  have hq (m : (T).obj (op l)) : ((q) k) ((T).transitionOfLE h m) =
      Submodule.factor (hF (Nat.add_le_add_right h 1)) (((q) l) m) := by
    obtain ⟨m, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ l m
    rw [ModuleTower.transitionOfLE_quotientsπ (fun k ↦ F (k + 1))
      (hF.comp_monotone (monotone_id.add_const 1)) h m]
    rw [ModuleTower.quotientsLiftEquiv_quotientsπ, ModuleTower.quotientsLiftEquiv_quotientsπ]
    exact (Submodule.factor_mk _ m).symm
  intro m
  apply ((q) k).injective
  rw [hq]
  simp only [completionAction, LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  rw [d.factor_truncatedLieAction ℒ F hF hF0 h]
  have hx := LieIdeal.factor_completionProjection
    (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) h x
  have he : d.truncationMap ℒ h = LieIdeal.factor (d.degreeIdeal_antitone ℒ h) := by
    apply LieHom.ext
    intro y
    obtain ⟨y, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ y
    simp only [LieIdeal.mkQ_apply, truncationMap_mk, LieIdeal.factor_apply]
  rw [he, hx]
  exact congrArg (d.truncatedLieAction ℒ F hF hF0 k (π k x))
    (hq m).symm

/-- A completed Lie element exponentiates to an automorphism of the filtered-module completion. -/
def completedExpLieAction (x : d.completedLie ℒ) : (T).lim ≃ₗ[R] (T).lim :=
  (T).limExp (d.completionAction ℒ F hF hF0 x)
    (fun k ↦ (d.completionAction_nilpotent ℒ F hF hF0 x k).exists_pow_apply_eq_zero)
    (d.completionAction_compatible ℒ F hF hF0 x)

/-- Under the canonical quotient equivalence, each projection is the finite exponential. -/
@[simp]
theorem coe_completedExpLieAction_apply (x : d.completedLie ℒ) (m : (T).lim) (k : ℕ) :
    (q) k ((d.completedExpLieAction ℒ F hF hF0 x m : (T).Product) k) =
      d.truncatedExpLieAction ℒ F hF hF0 k (π k x) ((q) k ((m : (T).Product) k)) := by
  rw [completedExpLieAction, ModuleTower.coe_limExp_apply_of_isNilpotent _ _ _ _ _ _
    (d.completionAction_nilpotent ℒ F hF hF0 x k)]
  have hsem : Function.Semiconj ((q) k)
      (d.completionAction ℒ F hF hF0 x k) (d.truncatedLieAction ℒ F hF hF0 k (π k x)) := by
    intro a
    simp only [completionAction, LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
  rw [Module.End.map_exp _ (d.completionAction_nilpotent ℒ F hF hF0 x k)
    ⟨k + 1, d.truncatedLieAction_pow_eq_zero ℒ F hF hF0 k (π k x)⟩ ((q) k) hsem]
  exact (LinearMap.congr_fun
    (d.truncatedExpLieAction_toLinearMap ℒ F hF hF0 k (π k x)) _).symm

/-- The zero completed Lie element acts as the identity. -/
@[simp]
theorem completedExpLieAction_zero :
    d.completedExpLieAction ℒ F hF hF0 0 = LinearEquiv.refl R _ := by
  ext m : 1
  apply (T).lim_ext
  intro k
  apply ((q) k).injective
  simp only [ModuleTower.limπ_apply, coe_completedExpLieAction_apply, map_zero,
    truncatedExpLieAction_zero, LinearEquiv.refl_apply]

/-- Negation of a completed Lie element inverts its exponential automorphism. -/
@[simp]
theorem completedExpLieAction_neg (x : d.completedLie ℒ) :
    d.completedExpLieAction ℒ F hF hF0 (-x) =
      (d.completedExpLieAction ℒ F hF hF0 x).symm := by
  apply LinearEquiv.ext
  intro m
  apply (d.completedExpLieAction ℒ F hF hF0 x).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (T).lim_ext
  intro k
  apply ((q) k).injective
  simp only [ModuleTower.limπ_apply, coe_completedExpLieAction_apply, map_neg,
    truncatedExpLieAction_neg, LinearEquiv.apply_symm_apply]

/-- The exponential is continuous for the module completion topology. -/
theorem continuous_completedExpLieAction (x : d.completedLie ℒ) :
    Continuous (d.completedExpLieAction ℒ F hF hF0 x) :=
  (T).continuous_limExp _ _ _

end TauCeti.PositiveDegrees
