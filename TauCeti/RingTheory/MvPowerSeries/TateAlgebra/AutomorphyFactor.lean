/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeightedSubst

/-!
# Automorphy factors on Tate algebras and their slash actions

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`, and let `M` be a
monoid. A *restricted automorphy factor* for `M` on the unit Tate algebra `R⟨X₁, …, X_k⟩` is a
pair of families

* `w γ = (w γ₁, …, w γ_k)` of restricted series of Gauss norm at most one, so that `f ↦ f(w γ)`
  is an analytic self-map of the closed unit polydisc, and
* `j γ` of restricted series, the factor itself,

satisfying the identity and cocycle laws

```text
w 1 = X,    w (γ δ) = (w γ)(w δ),    j 1 = 1,    j (γ δ) = (j γ)(w δ) · j δ.
```

These laws are stated entirely inside the Tate algebra, by analytic substitution, and need no
evaluation at points: they make sense, and the construction below applies, over nonreduced or
integral coefficient rings, where a series need not be determined by its values at points.

The *slash operator* of `γ` is the weighted substitution `f ↦ f|γ = j γ · f(w γ)`
(`TauCeti.MvPowerSeries.restrictedWeightedSubstCLM`). The cocycle laws are exactly what the
composition law of weighted substitutions needs to give `f|1 = f` and `(f|γ)|δ = f|(γ δ)`, so the
slash operators form a right action of `M` on `R⟨X⟩` by continuous `R`-linear maps
(`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.slash`), each bounded by the norm of its
factor. Indexed by the automorphy factor, playing the role of the weight, these operators form a
Mathlib `SlashAction`, so lemmas stated for an arbitrary slash action apply to them.

This is the shape of the weight-`κ` actions of `GL₂`-type monoids on the coefficient modules of
overconvergent and `p`-adic families of automorphic forms, where `w γ` is a Möbius transformation
and `j γ` is built from a character evaluated on `c z + d`; the Möbius case is in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Moebius`.

## Main definitions

* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor`: an automorphy factor for `M` on the unit
  Tate algebra in `k` variables.
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.slash`: the right action
  `Mᵐᵒᵖ →* (R⟨X⟩ →L[R] R⟨X⟩)` by the slash operators `f ↦ j γ · f(w γ)`.
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.instSlashAction`: the same operators as a
  `SlashAction` indexed by the automorphy factors.
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.twist`: the twist of an automorphy factor by
  a character `χ : M →* R`, whose slash operators are scaled by `χ`
  (`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.twist_slash_apply`).
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.comp`: the pullback of an automorphy factor
  along a monoid homomorphism, whose slash action is the original one through the homomorphism
  (`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.comp_slash`).

## Main results

* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.slash_apply`: the formula for `f|γ`.
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.slash_mul_apply`: `(f|γ)|δ = f|(γ δ)`.
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.norm_slash_apply_le`: `‖f|γ‖ ≤ ‖j γ‖ ‖f‖`.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Ser. 320 (2007), 59–120, §§9–10.
* D. Jacobs, *Slopes of compact Hecke operators*, PhD thesis, Imperial College London (2003),
  §1.5.
-/

public section

open MvPowerSeries MulOpposite

namespace TauCeti.MvPowerSeries

variable (M R : Type*) [Monoid M] [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  (k : ℕ)

/-- A **restricted automorphy factor** for the monoid `M` on the unit Tate algebra `R⟨X₁, …, X_k⟩`:
substitutions `w γ` into the closed unit polydisc and factors `j γ` satisfying `w 1 = X`,
`w (γ δ) = (w γ)(w δ)`, `j 1 = 1` and the cocycle law `j (γ δ) = (j γ)(w δ) · j δ`, all stated by
analytic substitution in the Tate algebra. -/
@[ext]
structure RestrictedAutomorphyFactor where
  /-- The substitution `w γ`, a `k`-tuple of series in the closed unit ball. -/
  subst : M → Fin k → IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)
  /-- Each coordinate of `w γ` has Gauss norm at most one. -/
  norm_subst_le : ∀ γ i, ‖subst γ i‖ ≤ 1
  /-- The automorphy factor `j γ`. -/
  factor : M → IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)
  /-- The substitution of the identity is the identity: `w 1 = X`. -/
  subst_one : ∀ i, subst 1 i = ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩
  /-- The substitutions compose contravariantly: `w (γ δ) = (w γ)(w δ)`. -/
  subst_mul : ∀ γ δ i,
    subst (γ * δ) i = restrictedAnalyticSubst (subst δ) (norm_subst_le δ) (subst γ i)
  /-- The factor of the identity is one. -/
  factor_one : factor 1 = 1
  /-- **The cocycle law** `j (γ δ) = (j γ)(w δ) · j δ`. -/
  factor_mul : ∀ γ δ,
    factor (γ * δ) = restrictedAnalyticSubst (subst δ) (norm_subst_le δ) (factor γ) * factor δ

namespace RestrictedAutomorphyFactor

variable {M R k} (A : RestrictedAutomorphyFactor M R k)

variable {M' : Type*} [Monoid M']

/-- The **pullback** of a restricted automorphy factor for `M` along a monoid homomorphism
`φ : M' →* M`: the substitutions and factors of `φ γ`. Its slash action is that of `M` through
`φ`. -/
def comp (φ : M' →* M) : RestrictedAutomorphyFactor M' R k where
  subst γ := A.subst (φ γ)
  norm_subst_le γ := A.norm_subst_le (φ γ)
  factor γ := A.factor (φ γ)
  subst_one i := by rw [map_one, A.subst_one]
  subst_mul γ δ i := by rw [map_mul, A.subst_mul]
  factor_one := by rw [map_one, A.factor_one]
  factor_mul γ δ := by rw [map_mul, A.factor_mul]

@[simp]
theorem comp_subst (φ : M' →* M) (γ : M') : (A.comp φ).subst γ = A.subst (φ γ) :=
  (rfl)

@[simp]
theorem comp_factor (φ : M' →* M) (γ : M') : (A.comp φ).factor γ = A.factor (φ γ) :=
  (rfl)

/-- The **twist** of a restricted automorphy factor by a character `χ : M →* R`: the same
substitutions, with factors `χ γ · j γ`. Twisting by `γ ↦ ν (det γ)` adds the determinant
character to the weight. -/
noncomputable def twist (χ : M →* R) : RestrictedAutomorphyFactor M R k where
  subst := A.subst
  norm_subst_le := A.norm_subst_le
  factor γ := χ γ • A.factor γ
  subst_one := A.subst_one
  subst_mul := A.subst_mul
  factor_one := by rw [map_one, one_smul, A.factor_one]
  factor_mul γ δ := by
    rw [map_mul, A.factor_mul, map_smul, smul_mul_smul_comm, mul_comm (χ γ)]

@[simp]
theorem twist_subst (χ : M →* R) : (A.twist χ).subst = A.subst :=
  (rfl)

@[simp]
theorem twist_factor (χ : M →* R) (γ : M) : (A.twist χ).factor γ = χ γ • A.factor γ :=
  (rfl)

variable [NormOneClass R]

/-- The **slash action** of a restricted automorphy factor: the right action of `M` on the unit
Tate algebra by the continuous `R`-linear operators `f ↦ f|γ = j γ · f(w γ)`, written as a monoid
homomorphism out of `Mᵐᵒᵖ`, so that `(f|γ)|δ = f|(γ δ)`. -/
noncomputable def slash :
    Mᵐᵒᵖ →* ((IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) →L[R]
      IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) where
  toFun γ := restrictedWeightedSubstCLM (A.factor (unop γ)) (A.subst (unop γ))
    (A.norm_subst_le (unop γ))
  map_one' := by
    simp_rw [unop_one, A.factor_one]
    convert restrictedWeightedSubstCLM_one_X (R := R) (r := fun _ : Fin k ↦ (1 : ℝ)) using 2
    exact funext A.subst_one
  map_mul' γ δ := by
    rw [ContinuousLinearMap.mul_def, restrictedWeightedSubstCLM_comp]
    congr 1
    · rw [unop_mul, A.factor_mul, mul_comm]
    · exact funext (A.subst_mul (unop δ) (unop γ))

/-- The slash operator of `γ` is the weighted substitution `f ↦ j γ · f(w γ)`. -/
theorem slash_op (γ : M) :
    A.slash (op γ) =
      restrictedWeightedSubstCLM (A.factor γ) (A.subst γ) (A.norm_subst_le γ) :=
  (rfl)

/-- **The slash formula** `f|γ = j γ · f(w γ)`. -/
@[simp]
theorem slash_apply (γ : M) (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    A.slash (op γ) f = A.factor γ * restrictedAnalyticSubst (A.subst γ) (A.norm_subst_le γ) f := by
  rw [slash_op, restrictedWeightedSubstCLM_apply]

/-- The identity acts trivially: `f|1 = f`. -/
theorem slash_one_apply (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    A.slash (op 1) f = f := by
  rw [op_one, map_one, one_apply_eq_self]

/-- **The right action law** `(f|γ)|δ = f|(γ δ)`. -/
theorem slash_mul_apply (γ δ : M) (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    A.slash (op (γ * δ)) f = A.slash (op δ) (A.slash (op γ) f) := by
  rw [op_mul, map_mul, mul_apply_eq_comp]

/-- The slash operator of `γ` is bounded by the norm of its factor: `‖f|γ‖ ≤ ‖j γ‖ ‖f‖`. In
particular it is a contraction when `‖j γ‖ ≤ 1`. -/
theorem norm_slash_apply_le (γ : M) (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    ‖A.slash (op γ) f‖ ≤ ‖A.factor γ‖ * ‖f‖ := by
  rw [slash_op]
  exact norm_restrictedWeightedSubstCLM_apply_le _ _ _ f

/-- The slash operators of all restricted automorphy factors for `M`, as a Mathlib slash action
indexed by the automorphy factor: `f ∣[A] γ = A.slash (op γ) f`. -/
noncomputable instance instSlashAction :
    SlashAction (RestrictedAutomorphyFactor M R k) M
      (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) where
  map A γ f := A.slash (op γ) f
  zero_slash A γ := map_zero (A.slash (op γ))
  slash_one A f := A.slash_one_apply f
  slash_mul A γ δ f := A.slash_mul_apply γ δ f
  add_slash A γ f g := map_add (A.slash (op γ)) f g

@[simp]
theorem slashAction_map (γ : M) (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    SlashAction.map A γ f = A.slash (op γ) f :=
  (rfl)

/-- The slash operators of a twist are those of the original factor, scaled by the character:
`f|_{A.twist χ} γ = χ γ • f|_A γ`. -/
theorem twist_slash_apply (χ : M →* R) (γ : M)
    (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    (A.twist χ).slash (op γ) f = χ γ • A.slash (op γ) f := by
  simp

/-- The slash action of a pullback is the slash action through the homomorphism:
`f|_{A.comp φ} γ = f|_A (φ γ)`. -/
theorem comp_slash (φ : M' →* M) (γ : M') : (A.comp φ).slash (op γ) = A.slash (op (φ γ)) :=
  (rfl)

end RestrictedAutomorphyFactor

end TauCeti.MvPowerSeries
