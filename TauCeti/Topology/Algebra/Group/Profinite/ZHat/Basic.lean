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
the group-theoretic facts about `ℤ̂` that the pro-`p` theory uses, together with the calculus of
`zHat.lift` (naturality, joint continuity, and its behaviour in the first argument) on which the
ring structure rests; that ring structure lives on `Additive zHat` in
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring`.

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
* `TauCeti.zHat.liftEquiv`: `lift` as an equivalence between a profinite group and the continuous
  homomorphisms from `ℤ̂` to it, with inverse evaluation at `zHat.gen`.

## Main results

* `TauCeti.zHat.hom_ext`, `TauCeti.zHat.existsUnique_lift`: the universal property of `ℤ̂`.
* `TauCeti.zHat.denseRange_ofInt`, and the `IsMulCommutative zHat` instance: the image of `ℤ`
  is dense, so `ℤ̂` is commutative.
* `TauCeti.zHat.comp_lift`, `TauCeti.zHat.continuous_lift`: the lift is natural in the target
  and jointly continuous in the element and the exponent.
* `TauCeti.zHat.lift_mul_apply`, `TauCeti.zHat.lift_zpow_apply`, `TauCeti.zHat.lift_comm`: the
  lift is multiplicative on commuting base elements and compatible with powers, and on `ℤ̂`
  itself it is symmetric.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.3.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- The **profinite integers** `ℤ̂`: the profinite completion of a universe lift of the additive
group of `ℤ`, written multiplicatively. The lift only places the completion in universe `u`.
This is the profinite group; its ring structure is put on `Additive zHat` in
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring`. -/
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

variable (P) in
/-- **The universal property of the profinite integers, bundled.** Continuous homomorphisms from
`ℤ̂` to a profinite group `P` correspond to elements of `P`, via `TauCeti.zHat.lift` and
evaluation at the generator. -/
noncomputable def liftEquiv : P ≃ (zHat.{u} →ₜ* P) where
  toFun := lift
  invFun φ := φ gen
  left_inv := lift_gen
  right_inv φ := (lift_unique _ φ rfl).symm

/-- The bundled universal property sends `a` to its lift. -/
@[simp]
theorem liftEquiv_apply (a : P) : liftEquiv.{u} P a = lift a :=
  (rfl)

/-- The inverse of the bundled universal property is evaluation at the generator. -/
@[simp]
theorem liftEquiv_symm_apply (φ : zHat.{u} →ₜ* P) : (liftEquiv P).symm φ = φ gen :=
  (rfl)

/-- The lift of the generator is the identity of the profinite integers. -/
theorem lift_gen_eq_id : (lift gen : zHat.{u} →ₜ* zHat.{u}) = ContinuousMonoidHom.id zHat.{u} :=
  (lift_unique gen _ rfl).symm

/-- The lift of the generator fixes every element. -/
@[simp]
theorem lift_gen_apply (x : zHat.{u}) : (lift gen : zHat.{u} →ₜ* zHat.{u}) x = x := by
  rw [lift_gen_eq_id, ContinuousMonoidHom.coe_id, id]

/-- The lift of `1` is the trivial homomorphism. -/
theorem lift_one : (lift (1 : P) : zHat.{u} →ₜ* P) = 1 :=
  (lift_unique 1 1 rfl).symm

/-- The lift of `1` is constant equal to `1`. -/
@[simp]
theorem lift_one_apply (x : zHat.{u}) : (lift (1 : P) : zHat.{u} →ₜ* P) x = 1 := by
  rw [lift_one, ContinuousMonoidHom.coe_one, Pi.one_apply]

section Naturality

variable {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [TotallyDisconnectedSpace Q]

/-- **Naturality of the lift.** A continuous homomorphism `f` between profinite groups carries
the lift of `a` to the lift of `f a`. -/
theorem comp_lift (f : P →ₜ* Q) (a : P) : f.comp (lift a : zHat.{u} →ₜ* P) = lift (f a) :=
  lift_unique (f a) _ (by simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, lift_gen])

/-- A continuous homomorphism between profinite groups commutes with the lift: it carries
`lift a x` to `lift (f a) x`. -/
@[simp]
theorem map_lift (f : P →ₜ* Q) (a : P) (x : zHat.{u}) : f (lift a x) = lift (f a) x := by
  rw [← comp_lift f a, ContinuousMonoidHom.coe_comp, Function.comp_apply]

end Naturality

/-- **Joint continuity of the lift**: `(a, x) ↦ lift a x` is continuous on `P × ℤ̂`. -/
theorem continuous_lift : Continuous fun q : P × zHat.{u} ↦ (lift q.1 : zHat.{u} →ₜ* P) q.2 := by
  refine continuous_iff_forall_continuous_mk.mpr fun U ↦ ?_
  -- Modulo an open normal subgroup `U` the lift of `a` only depends on the class of `a`, by
  -- naturality along the quotient map, and the finite quotient `P ⧸ U` is discrete.
  let π : P →ₜ* P ⧸ U.toSubgroup := ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  have h : (fun q : P × zHat.{u} ↦ ((lift q.1 : zHat.{u} →ₜ* P) q.2 : P ⧸ U.toSubgroup)) =
      (fun r : (P ⧸ U.toSubgroup) × zHat.{u} ↦ (lift r.1 : zHat.{u} →ₜ* P ⧸ U.toSubgroup) r.2) ∘
        Prod.map π id :=
    funext fun q ↦ map_lift π q.1 q.2
  rw [h]
  exact (continuous_prod_of_discrete_left.mpr fun c ↦ (lift c).continuous).comp
    (π.continuous.prodMap continuous_id)

/-- The lift is multiplicative on commuting base elements. -/
@[simp]
theorem lift_mul_apply (a b : P) (hab : Commute a b) (x : zHat.{u}) :
    (lift (a * b) : zHat.{u} →ₜ* P) x = lift a x * lift b x :=
  congrFun (denseRange_ofInt.equalizer (lift (a * b)).continuous
    ((lift a).continuous.mul (lift b).continuous)
    (funext fun z ↦ by simp [Function.comp, hab.mul_zpow])) x

/-- The lift of a power of the generator is that power. -/
theorem lift_gen_zpow_apply (n : ℤ) (x : zHat.{u}) :
    (lift (gen ^ n) : zHat.{u} →ₜ* zHat.{u}) x = x ^ n := by
  -- Both sides are continuous in `x` and agree on the integers, where both are `gen ^ (n * m)`.
  have h (z : Multiplicative ℤ) :
      (lift (gen ^ n) : zHat.{u} →ₜ* zHat.{u}) (ofInt z) = ofInt z ^ n := by
    rw [lift_ofInt, ← ofAdd_toAdd z, ofInt_ofAdd, toAdd_ofAdd, ← zpow_mul, ← zpow_mul, mul_comm]
  exact congrFun (denseRange_ofInt.equalizer (lift (gen ^ n)).continuous (continuous_zpow n)
    (funext h)) x

/-- The lift of a power is the power of the lift. -/
@[simp]
theorem lift_zpow_apply (a : P) (n : ℤ) (x : zHat.{u}) :
    (lift (a ^ n) : zHat.{u} →ₜ* P) x = lift a x ^ n := by
  -- Write `a ^ n` as the lift of `a` at `gen ^ n` and move the lift through by naturality.
  have h : a ^ n = lift a (gen ^ n) := by rw [map_zpow, lift_gen]
  rw [h, ← map_lift, lift_gen_zpow_apply, map_zpow]

/-- The lift on the profinite integers themselves is symmetric: `lift a b = lift b a`. This is
the commutativity of the ring product of `Additive zHat`. -/
theorem lift_comm (a b : zHat.{u}) :
    (lift a : zHat.{u} →ₜ* zHat.{u}) b = (lift b : zHat.{u} →ₜ* zHat.{u}) a := by
  -- Both sides are continuous in `a`, the left one by joint continuity, so it suffices to
  -- compare them at the integers, where both are the power `b ^ n`.
  have h (z : Multiplicative ℤ) :
      (lift (ofInt z) : zHat.{u} →ₜ* zHat.{u}) b = (lift b : zHat.{u} →ₜ* zHat.{u}) (ofInt z) := by
    rw [lift_ofInt, ← ofAdd_toAdd z, ofInt_ofAdd, lift_gen_zpow_apply, toAdd_ofAdd]
  exact congrFun (denseRange_ofInt.equalizer
    (continuous_lift.comp (continuous_id.prodMk continuous_const)) (lift b).continuous
    (funext h)) a

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
