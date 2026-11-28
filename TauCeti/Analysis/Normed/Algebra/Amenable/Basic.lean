/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Bimodule

/-!
# Amenable normed algebras

A normed algebra `A` over `𝕜` is *amenable*, in the sense of B. E. Johnson, if for every Banach
`A`-bimodule `E` in the universe of `A` every bounded derivation `D : A → E*` into the dual
bimodule is inner. Here a bimodule is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`,
with `a · x = L a x` and `x · a = R a x`, and the dual `E*` carries the dual actions of
`TauCeti.Analysis.Normed.Module.Dual.Bimodule`: the left action is `dualAction R` and the right
action is `dualAction L`. A bounded derivation is a bounded operator `D` with
`D (a * b) = a · D b + D a · b`, and it is inner when `D a = a · φ - φ · a` for some `φ ∈ E*`.
Equivalently, the first bounded Hochschild cohomology `H¹(A, E*)` vanishes for every such `E` (see
`TauCeti.Analysis.Normed.Algebra.Amenable.Cohomology`).

This file defines `TauCeti.IsAmenable` and proves basic examples (`TauCeti.isAmenable_self`,
`TauCeti.isAmenable_of_subsingleton`).

For universe-polymorphic bidual innerness and innerness on invariant bidual kernels, see
`TauCeti.Analysis.Normed.Algebra.Amenable.Bidual`; for the existence of bounded two-sided
approximate identities, see `TauCeti.Analysis.Normed.Algebra.Amenable.ApproximateUnit`; and for
Johnson's virtual and bounded approximate diagonal characterizations, see
`TauCeti.Analysis.Normed.Algebra.Amenable.Diagonal`.

## Main definitions

* `TauCeti.IsAmenable`: amenability of a normed algebra.

## Main results

* `TauCeti.isAmenable_self` and `TauCeti.isAmenable_of_subsingleton`: the base field and the zero
  algebra are amenable.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.1 and §2.2.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.8–2.9.
-/

public section

noncomputable section

universe u v

open ContinuousLinearMap

namespace TauCeti

section Amenable

variable (𝕜 : Type v) (A : Type u) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- A normed algebra `A` over `𝕜` is *amenable* if, for every Banach `A`-bimodule `E` in the
universe of `A`, every bounded derivation of `A` into the dual bimodule `E*` is inner.

The bimodule structure is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`,
`a · x = L a x` and `x · a = R a x`, which need not be unital or contractive. The dual `E*` has
left action `dualAction R` and right action `dualAction L`. A bounded derivation is a bounded
operator `D : A →L[𝕜] E*` with `D (a * b) = a · D b + D a · b`, and it is inner when
`D a = a · φ - φ · a` for some `φ ∈ E*`. -/
def IsAmenable : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (L R : A →L[𝕜] E →L[𝕜] E), (∀ a b x, L (a * b) x = L a (L b x)) →
      (∀ a b x, R (a * b) x = R b (R a x)) → (∀ a b x, L a (R b x) = R b (L a x)) →
      ∀ D : A →L[𝕜] StrongDual 𝕜 E,
        (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
          ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ

variable {𝕜 A}

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- The characteristic property of amenability: for every Banach `A`-bimodule `E` in the universe
of `A`, every bounded derivation `D : A → E*` is inner. -/
theorem isAmenable_def : IsAmenable 𝕜 A ↔
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      (L R : A →L[𝕜] E →L[𝕜] E), (∀ a b x, L (a * b) x = L a (L b x)) →
        (∀ a b x, R (a * b) x = R b (R a x)) → (∀ a b x, L a (R b x) = R b (L a x)) →
        ∀ D : A →L[𝕜] StrongDual 𝕜 E,
          (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
            ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  Iff.rfl

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable normed algebra `A`, every bounded derivation `D` of `A` into the dual `E*` of a
Banach `A`-bimodule `E` in the universe of `A` is inner: `D a = a · φ - φ · a` for some
`φ ∈ E*`, where `E*` has left action `dualAction R` and right action `dualAction L`. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction (h : IsAmenable 𝕜 A) {E : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  h E L R hL hR hLR D hD

variable (𝕜 A) in
omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- Every subsingleton normed algebra (in particular, the zero algebra) is amenable. -/
theorem isAmenable_of_subsingleton [Subsingleton A] : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ _ _ _ _ _ ↦ ⟨0, fun a ↦ by simp [Subsingleton.elim a 0]⟩

variable (𝕜) in
/-- Every nontrivially normed field is amenable over itself. -/
theorem isAmenable_self : IsAmenable 𝕜 𝕜 := by
  intro E _ _ _ L R hL hR hLR D hD
  have h1 : D 1 = dualAction R 1 (D 1) + dualAction L 1 (D 1) := by
    simpa only [mul_one] using hD 1 1
  have hRR : dualAction R 1 (dualAction R 1 (D 1)) = dualAction R 1 (D 1) := by
    rw [← dualAction_mul_apply_of_right hR, mul_one]
  have hLL : dualAction L 1 (dualAction L 1 (D 1)) = dualAction L 1 (D 1) := by
    rw [← dualAction_mul_apply_of_left hL, mul_one]
  have hRL : dualAction R 1 (dualAction L 1 (D 1)) = 0 := by
    have h := congrArg (dualAction R 1) h1
    rw [map_add, hRR] at h
    exact left_eq_add.mp h
  have hLR' : dualAction L 1 (dualAction R 1 (D 1)) = 0 := by
    rw [← dualAction_apply_dualAction_apply_comm hLR, hRL]
  refine ⟨dualAction R 1 (D 1) - dualAction L 1 (D 1), fun a ↦ ?_⟩
  have ha : a = a • (1 : 𝕜) := ((smul_eq_mul a 1).trans (mul_one a)).symm
  rw [ha, map_smul, map_smul, map_smul, smul_apply, smul_apply, ← smul_sub, map_sub, map_sub,
    hRR, hRL, hLR', hLL, sub_zero, zero_sub, sub_neg_eq_add, ← h1]

end Amenable

end TauCeti
