/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Topology.LocallyConstant.Algebra

/-!
# Locally constant families of finitely supported functions on a finite set

Let `Y` be a finite discrete space, `T` a topological space and `R` a ring. A locally constant
family `v : T → (Y →₀ R)` pairs with an integer valued function `φ : Y → ℤ` to the locally
constant function `t ↦ ∑ y, v t y * φ y`. This pairing identifies `LocallyConstant T (Y →₀ R)`
with the `R`-module of additive maps `LocallyConstant Y ℤ →+ LocallyConstant T R`
(`TauCeti.locallyConstantFinsuppEquiv`); the inverse sends `ψ` to `t ↦ ∑ y, single y (ψ 𝟙_{y} t)`.

The identification is natural in `Y` (pushforward of finitely supported functions against
pullback of integer valued functions) and in `T` (pullback on both sides). It computes the
sections of free condensed modules on finite sets: for a finite set `Y`, the free condensed
`R`-module on `Y` has sections `LocallyConstant T (Y →₀ R)` over a compact Hausdorff space `T`,
and this equivalence rewrites them as `Hom(ℤ^Y, C(T, R))`. Passing to the limit over finite
quotients of a profinite set is how the free solid module on a profinite set is computed.

`Y` enters through `ULift Y` so that the coefficients may live in a larger universe, as they do
for condensed modules.
-/

public section

namespace TauCeti

universe u

variable (R : Type*) [Ring R] (Y : Type u) [TopologicalSpace Y] (T : Type*) [TopologicalSpace T]

/-- The pairing of a locally constant family of finitely supported functions `v : T → (Y →₀ R)`
with an integer valued locally constant function `φ` on `Y`: the locally constant function
`t ↦ ∑ y, v t y * φ y`. -/
private noncomputable def locallyConstantFinsuppPairing :
    LocallyConstant T (ULift.{u'} Y →₀ R) →ₗ[R] (LocallyConstant Y ℤ →+ LocallyConstant T R) where
  toFun v :=
    { toFun φ := LocallyConstant.mapₗ R (Finsupp.linearCombination R fun y ↦ (φ y.down : R)) v
      map_zero' := by ext; simp [Finsupp.linearCombination_apply]
      map_add' φ ψ := by ext; simp [Finsupp.linearCombination_apply, mul_add, Finsupp.sum_add] }
  map_add' v w := by ext; simp
  map_smul' r v := by ext; simp

private theorem locallyConstantFinsuppPairing_apply_apply
    (v : LocallyConstant T (ULift.{u'} Y →₀ R)) (φ : LocallyConstant Y ℤ) (t : T) :
    locallyConstantFinsuppPairing R Y T v φ t = (v t).sum fun y r ↦ r * (φ y.down : R) := by
  simp [locallyConstantFinsuppPairing, Finsupp.linearCombination_apply]

/-- Pairing against the characteristic function of a point `y` evaluates at `y`. -/
private theorem locallyConstantFinsuppPairing_charFn [DiscreteTopology Y]
    (v : LocallyConstant T (ULift.{u'} Y →₀ R)) (y : Y) (t : T) :
    locallyConstantFinsuppPairing R Y T v (LocallyConstant.charFn ℤ (isClopen_discrete {y})) t =
      v t ⟨y⟩ := by
  classical
  rw [locallyConstantFinsuppPairing_apply_apply, Finsupp.sum_eq_single ⟨y⟩
    (fun b _ hb ↦ by simp [LocallyConstant.coe_charFn, ULift.ext_iff.not.mp hb]) (by simp)]
  simp [LocallyConstant.coe_charFn]

variable [DiscreteTopology Y] [Fintype Y]

/-- For a finite discrete space `Y`, locally constant families `v : T → (Y →₀ R)` are the same as
additive maps `LocallyConstant Y ℤ →+ LocallyConstant T R`: `v` corresponds to the map sending
`φ` to `t ↦ ∑ y, v t y * φ y` (`locallyConstantFinsuppEquiv_apply_apply`). -/
noncomputable def locallyConstantFinsuppEquiv :
    LocallyConstant T (ULift.{u'} Y →₀ R) ≃ₗ[R] (LocallyConstant Y ℤ →+ LocallyConstant T R) where
  __ := locallyConstantFinsuppPairing R Y T
  invFun ψ := ∑ y : Y, (ψ (LocallyConstant.charFn ℤ (isClopen_discrete {y}))).map
    (Finsupp.single (ULift.up y))
  left_inv v := by
    classical
    ext t ⟨y⟩
    simp [LocallyConstant.finsetSum_apply, Finset.sum_apply',
      locallyConstantFinsuppPairing_charFn, Finsupp.single_apply]
  right_inv ψ := by
    ext φ t
    conv_rhs => rw [← LocallyConstant.sum_smul_charFn φ]
    simp only [map_sum, map_zsmul, LocallyConstant.finsetSum_apply, LocallyConstant.smul_apply]
    simp [locallyConstantFinsuppPairing_apply_apply, Int.cast_comm]

variable {R Y T}

@[simp]
theorem locallyConstantFinsuppEquiv_apply_apply (v : LocallyConstant T (ULift.{u'} Y →₀ R))
    (φ : LocallyConstant Y ℤ) (t : T) :
    locallyConstantFinsuppEquiv R Y T v φ t = (v t).sum fun y r ↦ r * (φ y.down : R) :=
  locallyConstantFinsuppPairing_apply_apply R Y T v φ t

theorem locallyConstantFinsuppEquiv_symm_apply (ψ : LocallyConstant Y ℤ →+ LocallyConstant T R) :
    ((locallyConstantFinsuppEquiv R Y T).symm ψ : LocallyConstant T (ULift.{u'} Y →₀ R)) =
      ∑ y : Y, (ψ (LocallyConstant.charFn ℤ (isClopen_discrete {y}))).map
        (Finsupp.single (ULift.up y)) :=
  (rfl)

/-- `locallyConstantFinsuppEquiv` is natural in `Y`: pushing a family forward along `k : Y → Y'`
corresponds to pulling integer valued functions back along `k`. -/
theorem locallyConstantFinsuppEquiv_map {Y' : Type u} [TopologicalSpace Y'] [DiscreteTopology Y']
    [Fintype Y'] (k : C(Y, Y')) (v : LocallyConstant T (ULift.{u'} Y →₀ R)) :
    locallyConstantFinsuppEquiv R Y' T (v.map (Finsupp.mapDomain (ULift.map k))) =
      (locallyConstantFinsuppEquiv R Y T v).comp (LocallyConstant.comapAddMonoidHom k) := by
  ext φ t
  simp [Finsupp.sum_mapDomain_index, add_mul, ULift.map]

/-- `locallyConstantFinsuppEquiv` is natural in `T`: it commutes with pullback along
`g : T' → T`. -/
theorem locallyConstantFinsuppEquiv_comap {T' : Type*} [TopologicalSpace T'] (g : C(T', T))
    (v : LocallyConstant T (ULift.{u'} Y →₀ R)) (φ : LocallyConstant Y ℤ) :
    locallyConstantFinsuppEquiv R Y T' (v.comap g) φ =
      (locallyConstantFinsuppEquiv R Y T v φ).comap g := by
  ext t
  simp

end TauCeti
