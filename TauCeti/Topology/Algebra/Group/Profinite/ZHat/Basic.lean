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
group of `ℤ`, written multiplicatively. The defining copy of `ℤ` is universe-lifted so that
`zHat.{u}` can live in any universe; this does not change the completed group. This file records
the group-theoretic facts about `ℤ̂` that the pro-`p` theory uses; the ring structure on `ℤ̂` is
not treated here.

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

universe u v

/-- The **profinite integers** `ℤ̂`: the profinite completion of a universe lift of the additive
group of `ℤ`, written multiplicatively. The lift only places the completion in universe `u`.
This is the profinite group only; its ring structure is not treated here. -/
noncomputable abbrev zHat : ProfiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (ULift.{u} (Multiplicative ℤ)))

namespace zHat

/-- The canonical homomorphism from `ℤ`, written multiplicatively, to the profinite integers. It
sends `z` through `ULift.up` into the defining copy `ULift.{u} (Multiplicative ℤ)`, and then
through Mathlib's unit `ProfiniteGrp.ProfiniteCompletion.eta` at that copy, read as a plain
monoid homomorphism. -/
noncomputable def ofInt : Multiplicative ℤ →* zHat.{u} :=
  (ProfiniteGrp.ProfiniteCompletion.eta
    (GrpCat.of (ULift.{u} (Multiplicative ℤ)))).hom.comp MulEquiv.ulift.symm.toMonoidHom

/-- The underlying function of `ofInt` is `ULift.up` followed by the unit map of the profinite
completion of `ULift.{u} (Multiplicative ℤ)`. -/
theorem coe_ofInt :
    ⇑(ofInt : Multiplicative ℤ →* zHat.{u}) = fun z ↦
      ProfiniteGrp.ProfiniteCompletion.etaFn
      (GrpCat.of (ULift.{u} (Multiplicative ℤ))) (ULift.up z) :=
  (rfl)

/-- The image of `1 ∈ ℤ` in the profinite integers: the element whose value determines a
continuous homomorphism out of `ℤ̂`, by `zHat.hom_ext`. -/
noncomputable def gen : zHat.{u} :=
  (ofInt : Multiplicative ℤ →* zHat.{u}) (Multiplicative.ofAdd 1)

/-- The canonical homomorphism from `ℤ` sends `n` to the `n`-th power of the generator. -/
@[simp]
theorem ofInt_ofAdd (n : ℤ) :
    (ofInt : Multiplicative ℤ →* zHat.{u}) (Multiplicative.ofAdd n) =
      (gen : zHat.{u}) ^ n := by
  rw [gen, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]

/-- The image of `ℤ` is dense in the profinite integers. -/
theorem denseRange_ofInt : DenseRange (ofInt : Multiplicative ℤ →* zHat.{u}) := by
  rw [DenseRange, coe_ofInt, ← Function.comp_def, ULift.up_surjective.range_comp]
  exact ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- The profinite integers are commutative, since the image of `ℤ` is dense. -/
instance : IsMulCommutative zHat.{u} where
  is_comm := ⟨fun x y ↦ by
    -- Multiplication by a fixed element is continuous, so it suffices to check commutation
    -- on the dense image of `ℤ`, in each variable separately.
    have h : ∀ (z : Multiplicative ℤ) (x : zHat.{u}),
        x * (ofInt : Multiplicative ℤ →* zHat.{u}) z =
          (ofInt : Multiplicative ℤ →* zHat.{u}) z * x := fun z ↦
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
theorem hom_ext {φ ψ : zHat.{u} →ₜ* Q} (h : φ gen = ψ gen) : φ = ψ := by
  refine ProfiniteCompletion.continuousMonoidHom_ext (ULift.{u} (Multiplicative ℤ)) fun z ↦ ?_
  have hcomp : φ.toMonoidHom.comp (ofInt : Multiplicative ℤ →* zHat.{u}) =
      ψ.toMonoidHom.comp (ofInt : Multiplicative ℤ →* zHat.{u}) := MonoidHom.ext_mint h
  simpa [coe_ofInt] using DFunLike.congr_fun hcomp z.down

end HomExt

section Lift

variable {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The continuous homomorphism from the profinite integers to a profinite group `P`, in any
universe, sending the generator to `a`. -/
noncomputable def lift (a : P) : zHat.{u} →ₜ* P :=
  (ProfiniteCompletion.continuousMonoidHomEquiv (ULift.{u} (Multiplicative ℤ)) P).symm
    ((zpowersHom P a).comp MulEquiv.ulift.toMonoidHom)

/-- The lift of `a` sends the image of `n ∈ ℤ` to `a ^ n`. -/
@[simp]
theorem lift_ofInt (a : P) (z : Multiplicative ℤ) :
    (lift a : zHat.{u} →ₜ* P) (ofInt z) = a ^ z.toAdd := by
  rw [lift, coe_ofInt, ProfiniteCompletion.continuousMonoidHomEquiv_symm_apply_etaFn,
    MonoidHom.comp_apply, zpowersHom_apply]
  rfl

/-- The lift of `a` sends the generator to `a`. -/
@[simp]
theorem lift_gen (a : P) : (lift a : zHat.{u} →ₜ* P) gen = a := by
  rw [gen, lift_ofInt, toAdd_ofAdd, zpow_one]

/-- A continuous homomorphism sending the generator to `a` is the lift of `a`. -/
theorem lift_unique (a : P) (φ : zHat.{u} →ₜ* P) (hφ : φ gen = a) : φ = lift a :=
  hom_ext (by rw [hφ, lift_gen])

/-- **The universal property of the profinite integers.** For every element `a` of a profinite
group there is a unique continuous homomorphism from `ℤ̂` sending the generator to `a`. -/
theorem existsUnique_lift (a : P) : ∃! φ : zHat.{u} →ₜ* P, φ gen = a :=
  ⟨lift a, lift_gen a, fun φ hφ ↦ lift_unique a φ hφ⟩

/-- The lift of a topological generator of a profinite group is surjective. -/
theorem lift_surjective (a : P) (ha : (Subgroup.zpowers a).topologicalClosure = ⊤) :
    Function.Surjective (lift a : zHat.{u} →ₜ* P) := by
  have hdense : DenseRange (lift a) := by
    rw [denseRange_iff_closure_range]
    apply top_unique
    have hle : closure (Subgroup.zpowers a : Set P) ⊆ closure (Set.range (lift a)) :=
      closure_mono fun x hx ↦ by
        obtain ⟨n, rfl⟩ := hx
        exact ⟨(ofInt : Multiplicative ℤ →* zHat.{u}) (Multiplicative.ofAdd n), by simp⟩
    rw [← Subgroup.topologicalClosure_coe, ha, Subgroup.coe_top] at hle
    exact hle
  have hclosed : IsClosed (Set.range (lift a)) :=
    (isCompact_range (lift a).continuous).isClosed
  rw [← Set.range_eq_univ, ← hclosed.closure_eq]
  exact hdense.closure_range

/-- The lift of `a` is injective when every finite quotient of the defining copy of `ℤ` is
detected by a continuous quotient of the target carrying `a` to the canonical generator. This is
the finite-coordinate criterion used to identify a procyclic group having quotients of every
finite order with the profinite integers. -/
theorem lift_injective_of_finite_quotients (a : P)
    (hquot : ∀ H : FiniteIndexNormalSubgroup (ULift.{u} (Multiplicative ℤ)),
      letI : TopologicalSpace
        (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup) := ⊥
      ∃ q : P →ₜ* (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup),
        q a = QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1))) :
    Function.Injective (lift a : zHat.{u} →ₜ* P) := by
  intro x y hxy
  apply Subtype.ext
  funext H
  let _ : TopologicalSpace (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup) := ⊥
  let _ : DiscreteTopology (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup) := ⟨rfl⟩
  obtain ⟨q, hq⟩ := hquot H
  let c : zHat.{u} →ₜ* (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup) :=
    ⟨ProfiniteCompletion.coordinateHom _ H,
      ProfiniteCompletion.continuous_coordinateHom _ H⟩
  have hc : q.comp (lift a) = c := hom_ext <| by
    -- Expose evaluation at the generator through the bundled continuous homomorphisms.
    change q (lift a gen) = c gen
    rw [lift_gen, hq]
    -- Unfold `c` just enough to use the defining computation for a completion coordinate.
    change QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1)) =
      ProfiniteCompletion.coordinateHom _ H gen
    rw [gen, coe_ofInt, ProfiniteCompletion.coordinateHom_etaFn]
  have hxy' := congrArg q hxy
  have hcxy : c x = c y :=
    (DFunLike.congr_fun hc x).symm.trans (hxy'.trans (DFunLike.congr_fun hc y))
  rw [← ProfiniteCompletion.coordinateHom_apply _ H x,
    ← ProfiniteCompletion.coordinateHom_apply _ H y]
  exact hcxy

end Lift

end zHat

end TauCeti
