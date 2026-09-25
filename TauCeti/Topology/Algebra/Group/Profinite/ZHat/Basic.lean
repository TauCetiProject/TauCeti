/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Completion

/-!
# The profinite integers as a profinite group

The **profinite integers** `ℤ̂`, written `zHat`, form the profinite completion of the additive
group of `ℤ`, written multiplicatively. This file records the group-theoretic facts about `ℤ̂`
that the pro-`p` theory uses; the ring structure on `ℤ̂` is not treated here.

The generator `1 ∈ ℤ` gives the topological generator `zHat.gen`, and the universal property of
the profinite completion becomes: continuous homomorphisms from `ℤ̂` to a profinite group `P`
are exactly the elements of `P`, through the value at `zHat.gen`. Since the image of `ℤ` is
dense, `ℤ̂` is commutative. The identification of the maximal pro-`p` quotient of `ℤ̂` with the
`p`-adic integers, and of its `p`-Sylow subgroups with `ℤ_p`, is in
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.PadicInt`.

## Main definitions

* `TauCeti.zHat`: the profinite integers, as a profinite group.
* `TauCeti.zHat.ofInt`, `TauCeti.zHat.gen`: the canonical homomorphism from `ℤ` and the image
  of `1`.
* `TauCeti.zHat.lift`: the continuous homomorphism to a profinite group sending `zHat.gen` to a
  given element.

## Main results

* `TauCeti.zHat.hom_ext`, `TauCeti.zHat.existsUnique_lift`: the universal property of `ℤ̂`.
* `TauCeti.zHat.denseRange_ofInt`, and the `IsMulCommutative zHat` instance: the image of `ℤ`
  is dense, so `ℤ̂` is commutative.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.3.
-/

public section

namespace TauCeti

open CategoryTheory

universe v

/-- The **profinite integers** `ℤ̂`: the profinite completion of the additive group of `ℤ`,
written multiplicatively. This is the profinite group only; its ring structure is not treated
here. -/
noncomputable abbrev zHat : ProfiniteGrp.{0} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

namespace zHat

/-- The canonical homomorphism from `ℤ`, written multiplicatively, to the profinite integers. It
is Mathlib's unit `ProfiniteGrp.ProfiniteCompletion.eta` at `Multiplicative ℤ`, read as a plain
monoid homomorphism. -/
noncomputable def ofInt : Multiplicative ℤ →* zHat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

/-- The underlying function of `ofInt` is the unit map into the profinite completion. -/
theorem coe_ofInt :
    ⇑ofInt = ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ)) :=
  (rfl)

/-- The image of `1 ∈ ℤ` in the profinite integers: the element whose value determines a
continuous homomorphism out of `ℤ̂`, by `zHat.hom_ext`. -/
noncomputable def gen : zHat := ofInt (Multiplicative.ofAdd 1)

/-- The canonical homomorphism from `ℤ` sends `n` to the `n`-th power of the generator. -/
@[simp]
theorem ofInt_ofAdd (n : ℤ) : ofInt (Multiplicative.ofAdd n) = gen ^ n := by
  rw [gen, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]

/-- The image of `ℤ` is dense in the profinite integers. -/
theorem denseRange_ofInt : DenseRange ofInt := by
  rw [coe_ofInt]
  exact ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- The profinite integers are commutative, since the image of `ℤ` is dense. -/
instance : IsMulCommutative zHat where
  is_comm := ⟨fun x y ↦ by
    -- Multiplication by a fixed element is continuous, so it suffices to check commutation
    -- on the dense image of `ℤ`, in each variable separately.
    have h : ∀ (z : Multiplicative ℤ) (x : zHat), x * ofInt z = ofInt z * x := fun z ↦
      congrFun (denseRange_ofInt.equalizer (continuous_id.mul continuous_const)
        (continuous_const.mul continuous_id)
        (funext fun w ↦ by simp only [Function.comp, ← map_mul, mul_comm]))
    exact congrFun (denseRange_ofInt.equalizer (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const) (funext fun z ↦ h z x)) y⟩

section HomExt

variable {Q : Type v} [Monoid Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of the profinite integers into a Hausdorff topological
monoid that agree on the generator are equal. -/
@[ext]
theorem hom_ext {φ ψ : zHat →ₜ* Q} (h : φ gen = ψ gen) : φ = ψ := by
  refine ProfiniteCompletion.continuousMonoidHom_ext (Multiplicative ℤ) fun z ↦ ?_
  have hcomp : φ.toMonoidHom.comp ofInt = ψ.toMonoidHom.comp ofInt := MonoidHom.ext_mint h
  simpa [coe_ofInt] using DFunLike.congr_fun hcomp z

end HomExt

section Lift

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The continuous homomorphism from the profinite integers to a profinite group `P` sending the
generator to `a`. -/
noncomputable def lift (a : P) : zHat →ₜ* P :=
  (ProfiniteCompletion.continuousMonoidHomEquiv (Multiplicative ℤ) P).symm (zpowersHom P a)

/-- The lift of `a` sends the image of `n ∈ ℤ` to `a ^ n`. -/
@[simp]
theorem lift_ofInt (a : P) (z : Multiplicative ℤ) : lift a (ofInt z) = a ^ z.toAdd := by
  rw [lift, coe_ofInt, ProfiniteCompletion.continuousMonoidHomEquiv_symm_apply_etaFn,
    zpowersHom_apply]

/-- The lift of `a` sends the generator to `a`. -/
@[simp]
theorem lift_gen (a : P) : lift a gen = a := by
  rw [gen, lift_ofInt, toAdd_ofAdd, zpow_one]

/-- A continuous homomorphism sending the generator to `a` is the lift of `a`. -/
theorem lift_unique (a : P) (φ : zHat →ₜ* P) (hφ : φ gen = a) : φ = lift a :=
  hom_ext (by rw [hφ, lift_gen])

/-- **The universal property of the profinite integers.** For every element `a` of a profinite
group there is a unique continuous homomorphism from `ℤ̂` sending the generator to `a`. -/
theorem existsUnique_lift (a : P) : ∃! φ : zHat →ₜ* P, φ gen = a :=
  ⟨lift a, lift_gen a, fun φ hφ ↦ lift_unique a φ hφ⟩

end Lift

end zHat

end TauCeti
