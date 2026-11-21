/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.Finiteness
public import TauCeti.GroupTheory.ExponentialGroup.Hom
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finite generation in groups with exponents in `ℤ[t]`

The monomials `t ^ k` generate the additive group of `ℤ[t]`, which is not finitely generated. So in
a `ℤ[t]`-group, if the powers `x ^ p` of an element `x` are pairwise distinct, the powers
`x ^ (t ^ k)` generate a subgroup isomorphic to the additive group of `ℤ[t]`, which is not finitely
generated.

## Main results

* `TauCeti.IsExponentialGroup.not_fg_closure_range_pow_X_pow`: in a `ℤ[t]`-group, the powers
  `x ^ (t ^ k)` of an element `x` whose powers `x ^ p` are pairwise distinct generate a subgroup
  that is not finitely generated.
-/

public section

open Polynomial

namespace TauCeti.IsExponentialGroup

variable {G : Type*} [Group G] [Pow G ℤ[X]] [IsExponentialGroup ℤ[X] G]

open scoped MultiplicativePow in
/-- In a `ℤ[t]`-group, if the powers `x ^ p` of an element `x` are pairwise distinct, the powers
`x ^ (t ^ k)` generate a subgroup that is not finitely generated. -/
theorem not_fg_closure_range_pow_X_pow {x : G} (hx : Function.Injective (powHom ℤ[X] x)) :
    ¬(Subgroup.closure (Set.range fun k : ℕ => x ^ (X ^ k : ℤ[X]))).FG := by
  let φ := (powHom ℤ[X] x).toMonoidHom
  have hφ : Function.Injective φ := by simpa [φ] using hx
  -- the monomials `t ^ k` generate `ℤ[t]`, so the powers `x ^ (t ^ k)` generate the range of `φ`
  have hX : AddSubgroup.closure (Set.range fun k : ℕ => (X ^ k : ℤ[X])) = ⊤ := by
    simpa [Submodule.span_int_eq_addSubgroupClosure, coe_basisMonomials,
      monomial_one_right_eq_X_pow] using congrArg Submodule.toAddSubgroup (basisMonomials ℤ).span_eq
  have hS : φ '' (Multiplicative.toAdd ⁻¹' Set.range fun k : ℕ => (X ^ k : ℤ[X])) =
      Set.range fun k : ℕ => x ^ (X ^ k : ℤ[X]) := by
    ext
    simp [φ, powHom_apply]
  have hrange : Subgroup.closure (Set.range fun k : ℕ => x ^ (X ^ k : ℤ[X])) = φ.range := by
    rw [← hS, ← MonoidHom.map_closure, ← AddSubgroup.toSubgroup_closure, hX, OrderIso.map_top,
      MonoidHom.range_eq_map]
  -- the range of `φ` is isomorphic to the additive group of `ℤ[t]`, which is not finitely generated
  rw [hrange, ← Group.fg_iff_subgroup_fg]
  intro hfg
  exact Polynomial.not_finite <| Module.Finite.iff_addGroup_fg.2 <|
    isMulFG_multiplicative_iff.1 <| (isMulFG_congr (MonoidHom.ofInjective hφ)).2 hfg

end TauCeti.IsExponentialGroup
