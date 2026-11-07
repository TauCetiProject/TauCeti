/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.RepresentationTheory.LSPath.RootOperator

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import TauCeti.RepresentationTheory.LSPath.PartialInverse

/-!
# Ambient simple-root string of piecewise-linear paths

Fix a root datum `P : RootDatum ι X Y` with a base `b : P.Base`, an additive realization
`f : X →+ V` in a vector space over a linearly ordered field `𝕜`, and height forms
`F : b.support → Module.Dual 𝕜 V` agreeing with the simple coroots on `f(X)`.

For any simple root `α_i` (`i : b.support`), the height form `F i` takes value `2` on `f α_i`
(`TauCeti.PLPath.apply_root_eq_two`). Lowering the straight simple-root path `t ↦ t • f α_i` once
under `f_i = lower (F i) (f α_i)` cuts it at the midpoint and reflects its first half, producing the
zero-weight bent path `TauCeti.PLPath.simpleRootBent` traversing `-(1/2) f α_i` followed by
`(1/2) f α_i`; lowering once more produces the opposite straight path `t ↦ -t • f α_i`, and raising
steps back through the same three-element string.

These ambient path-operator calculations depend only on `F i (f α_i) = 2` and require neither
injectivity of `f`, crystal admissibility, nor isolation of `i`.

## Main definitions

* `TauCeti.PLPath.simpleRootBent`: the zero-weight bent path `-(1/2) α_i` followed by `(1/2) α_i`
  at the middle of the `i`-th simple-root string.

## Main results

* `TauCeti.PLPath.apply_root_eq_two`: `F i (f (P.root i)) = 2` whenever `F` agrees with the simple
  coroots on `f(X)`.
* `TauCeti.PLPath.minHeight_simpleRootBent_self`: `simpleRootBent` has minimum `i`-th coroot height
  `-1`.
* `TauCeti.PLPath.lower_straight_root`, `TauCeti.PLPath.lower_simpleRootBent`,
  `TauCeti.PLPath.raise_straight_neg_root`, `TauCeti.PLPath.raise_simpleRootBent`: explicit action
  of `lower (F i) (f α_i)` and `raise (F i) (f α_i)` along `{straight α_i, simpleRootBent,
  straight (-α_i)}`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1.
-/

public section

namespace TauCeti.PLPath

open Module

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}

section Pairing

variable [Ring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- Every simple-coroot height form evaluates to `2` on its realized simple root. -/
theorem apply_root_eq_two (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) : F i (f (P.root i)) = 2 := by
  rw [hF, P.root_coroot'_eq_pairing, P.pairing_same, Int.cast_ofNat]

end Pairing

section Bent

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

variable (𝕜) in
/-- The zero-weight bent path `-(1/2) α_i` followed by `(1/2) α_i` obtained by lowering the
straight simple-root path `t ↦ t • α_i` once. -/
noncomputable def simpleRootBent (f : X →+ V) (i : b.support) : PLPath 𝕜 V :=
  straight 𝕜 (-(2 : 𝕜)⁻¹ • f (P.root i)) * straight 𝕜 ((2 : 𝕜)⁻¹ • f (P.root i))

theorem simpleRootBent_def (f : X →+ V) (i : b.support) :
    simpleRootBent 𝕜 f i =
      straight 𝕜 (-(2 : 𝕜)⁻¹ • f (P.root i)) * straight 𝕜 ((2 : 𝕜)⁻¹ • f (P.root i)) :=
  (rfl)

@[simp]
theorem endpoint_simpleRootBent (i : b.support) :
    (simpleRootBent 𝕜 f i).endpoint = 0 := by
  simp [simpleRootBent]

@[simp]
theorem reverse_simpleRootBent (i : b.support) :
    (simpleRootBent 𝕜 f i).reverse = simpleRootBent 𝕜 f i := by
  simp [simpleRootBent]

/-- The bent path `simpleRootBent` has minimum `i`-th coroot height `-1`. -/
theorem minHeight_simpleRootBent_self
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    (simpleRootBent 𝕜 f i).minHeight (F i) = -1 := by
  rw [simpleRootBent, neg_smul, minHeight_straight_neg_mul_straight]
  simp only [map_smul, smul_eq_mul, apply_root_eq_two hF i]
  norm_num

/-- Lowering the straight simple-root path `t ↦ t • α_i` gives `simpleRootBent`. -/
theorem lower_straight_root
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    lower (F i) (f (P.root i)) (straight 𝕜 (f (P.root i))) = some (simpleRootBent 𝕜 f i) := by
  have hv := apply_root_eq_two hF i
  rw [lower_straight (by linarith : (1 : 𝕜) ≤ F i (f (P.root i))), hv]
  congr 1
  have hrefl :
      preReflection (f (P.root i)) (F i) ((2 : 𝕜)⁻¹ • f (P.root i)) =
        -(2 : 𝕜)⁻¹ • f (P.root i) := by
    rw [preReflection_apply, map_smul, hv, smul_eq_mul]
    have h1 : (2 : 𝕜)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
    rw [h1, one_smul]
    module
  have hsub : (1 - (2 : 𝕜)⁻¹) = (2 : 𝕜)⁻¹ := by norm_num
  rw [hrefl, hsub, simpleRootBent]

/-- Raising `simpleRootBent` recovers `straight 𝕜 (f (P.root i))`. -/
theorem raise_simpleRootBent
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    raise (F i) (f (P.root i)) (simpleRootBent 𝕜 f i) = some (straight 𝕜 (f (P.root i))) :=
  (lower_eq_some_iff (apply_root_eq_two hF i)).mp (lower_straight_root hF i)

/-- Lowering `simpleRootBent` gives the opposite straight simple-root path `t ↦ -t • α_i`. -/
theorem lower_simpleRootBent
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    lower (F i) (f (P.root i)) (simpleRootBent 𝕜 f i) = some (straight 𝕜 (-f (P.root i))) := by
  conv_lhs => rw [← reverse_simpleRootBent (f := f) i]
  rw [lower_reverse, raise_simpleRootBent hF i, Option.map_some, reverse_straight]

/-- Raising `straight 𝕜 (-f (P.root i))` gives `simpleRootBent`. -/
theorem raise_straight_neg_root
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support) :
    raise (F i) (f (P.root i)) (straight 𝕜 (-f (P.root i))) = some (simpleRootBent 𝕜 f i) :=
  (lower_eq_some_iff (apply_root_eq_two hF i)).mp (lower_simpleRootBent hF i)

end Bent

end TauCeti.PLPath
