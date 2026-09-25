/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.ZMod

/-!
# The continuous `ZMod n`-dual of a topological group

The continuous characters of a topological group with values in the multiplicative encoding
`Multiplicative (ZMod n)` of `ZMod n` form a commutative group, written additively as the
**continuous `ZMod n`-dual** `TauCeti.continuousZModDual n G`. Scalar `n` kills the target, hence
the character group as well, so the dual is a `ZMod n`-module; for a prime `p` it is an
`𝔽_p`-vector space, the discrete companion of a compact `𝔽_p`-vector group.

When the group is itself commutative with a `ZMod p`-module structure on its additive copy — for a
prime `p`, an elementary abelian group — a continuous character of it is in particular a linear
functional on that module, so `TauCeti.continuousZModDualToDual` reads the continuous dual inside
the algebraic dual, injectively.

## Main definitions

* `TauCeti.continuousZModDual`: the group of continuous `ZMod n`-valued characters of a topological
  group, written additively; for a prime `p` it is the continuous `𝔽_p`-dual.
* `TauCeti.continuousZModDualToDual`: a continuous `ZMod p`-valued character of a commutative group
  whose additive copy is a `ZMod p`-module, read as a linear functional on that module.
-/

public section

namespace TauCeti

universe u

section ZModDual

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- The **continuous `ZMod n`-dual** of a topological group: its group of continuous characters
with values in `ZMod n`, written additively so that it is a `ZMod n`-module. For a prime `p` it is
the continuous `𝔽_p`-dual, an `𝔽_p`-vector space. -/
abbrev continuousZModDual (n : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Type u :=
  Additive (G →ₜ* Multiplicative (ZMod n))

/-- The continuous `ZMod n`-valued characters form a `ZMod n`-module: the target has exponent
dividing `n`, hence so does the character group. -/
instance instModuleContinuousZModDual : Module (ZMod n) (continuousZModDual n G) :=
  AddCommGroup.zmodModule fun x ↦ by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    ext g
    simp [ContinuousMonoidHom.pow_apply, toAdd_pow, nsmul_eq_mul]

end ZModDual

section ToDual

variable {p : ℕ} {W : Type u} [CommGroup W] [TopologicalSpace W]
  [Module (ZMod p) (Additive W)]

/-- A continuous `ZMod p`-valued character of a commutative group `W` whose additive copy is a
`ZMod p`-module, read as a linear functional on that module; for a prime `p` and an elementary
abelian `W` this is a functional on the `𝔽_p`-vector space `Additive W`. It is injective
(`TauCeti.continuousZModDualToDual_injective`), so the continuous dual is a subspace of the
algebraic dual. -/
def continuousZModDualToDual :
    continuousZModDual p W →ₗ[ZMod p] Module.Dual (ZMod p) (Additive W) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun x ↦ AddMonoidHom.toZModLinearMap p
        { toFun := fun w ↦ Multiplicative.toAdd (Additive.toMul x (Additive.toMul w))
          map_zero' := by simp
          map_add' := fun a b ↦ by simp [toMul_add] }
      map_zero' := by ext w; simp
      map_add' := fun x y ↦ by ext w; simp }

@[simp]
theorem continuousZModDualToDual_apply (x : continuousZModDual p W) (w : Additive W) :
    continuousZModDualToDual x w = Multiplicative.toAdd (Additive.toMul x (Additive.toMul w)) :=
  (rfl)

theorem continuousZModDualToDual_injective :
    Function.Injective (continuousZModDualToDual (p := p) (W := W)) := fun x y h ↦ by
  apply Additive.toMul.injective
  ext w
  have hw := congrArg (fun f ↦ f (Additive.ofMul w)) h
  simp only [continuousZModDualToDual_apply, toMul_ofMul] at hw
  exact Multiplicative.toAdd.injective hw

theorem continuousZModDualToDual_eq_zero_iff {x : continuousZModDual p W} {w : Additive W} :
    continuousZModDualToDual x w = 0 ↔ Additive.toMul w ∈ (Additive.toMul x).ker := by
  simp [MonoidHom.mem_ker]

end ToDual

end TauCeti
