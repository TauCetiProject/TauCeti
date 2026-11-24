/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Nonconstant maps and their reparametrization quotients

Let a group `G` act on a space `Y` by homeomorphisms. Then `G` acts on the continuous maps
`u : Y → X` by **reparametrization**, the left action `g • u = u ∘ (g⁻¹ • ·)`
(`TauCeti.NonconstantMap.smul_apply`); its orbits are those of the right action `u ↦ u ∘ (g • ·)`
by precomposition. A constant map is fixed by every element of `G`, so no action containing it can
be free or proper, and this file restricts the action to the **nonconstant** maps
(`TauCeti.NonconstantMap Y X`), with the compact-open topology.

The **unparametrized maps** `TauCeti.UnparametrizedMap G Y X` form the orbit space of this action
and the **one-marked unparametrized maps** `TauCeti.MarkedUnparametrizedMap G Y X` the orbit space
of the diagonal action `g • (u, z) = (g • u, g • z)` on pairs of a map and a point of `Y`. The
evaluation `(u, z) ↦ u z` is invariant, since `(g • u) (g • z) = u z`, so it descends to a
continuous **evaluation map** `TauCeti.MarkedUnparametrizedMap.eval` on one-marked unparametrized
maps. Forgetting the marked point gives a continuous surjection
`TauCeti.MarkedUnparametrizedMap.forget` onto unparametrized maps.

The main example is the group `PSL(2, 𝕜)` of Möbius transformations acting on the projective line
`OnePoint 𝕜`; for `𝕜 = ℂ` the two orbit spaces are the spaces of unparametrized and one-marked
continuous spheres. That action on nonconstant maps is proper, so both orbit spaces are Hausdorff
(`OnePoint.instProperSMulNonconstantMap`).

## Main definitions

* `TauCeti.NonconstantMap Y X`: the nonconstant continuous maps `Y → X`, with the
  reparametrization action of any group acting on `Y`.
* `TauCeti.UnparametrizedMap G Y X`: its orbit space.
* `TauCeti.MarkedUnparametrizedMap G Y X`: the orbit space of pairs of a nonconstant map and a
  point.
* `TauCeti.MarkedUnparametrizedMap.eval`: the evaluation `[u, z] ↦ u z`.
* `TauCeti.MarkedUnparametrizedMap.forget`: the map `[u, z] ↦ [u]`.

## Main results

* `TauCeti.NonconstantMap.instContinuousSMul`: the reparametrization action is continuous when the
  action on `Y` is, as composition is continuous for the compact-open topology.
* `TauCeti.MarkedUnparametrizedMap.continuous_eval`: the evaluation map is continuous.
* `TauCeti.MarkedUnparametrizedMap.continuous_forget`,
  `TauCeti.MarkedUnparametrizedMap.forget_surjective`: forgetting the marked point is a continuous
  surjection.
-/

public section

open Function Topology TopologicalSpace

namespace TauCeti

section Maps

variable (Y X : Type*) [TopologicalSpace Y] [TopologicalSpace X]

/-- The nonconstant continuous maps `Y → X`, with the compact-open topology. For `Y` the projective
line `OnePoint ℂ` these are the nonconstant parametrized spheres in `X`. -/
structure NonconstantMap where
  /-- The underlying continuous map of a nonconstant map. -/
  toContinuousMap : C(Y, X)
  /-- A nonconstant map takes two different values. -/
  exists_apply_ne' : ∃ z w, toContinuousMap z ≠ toContinuousMap w

namespace NonconstantMap

variable {Y X}

instance : FunLike (NonconstantMap Y X) Y X where
  coe u := u.toContinuousMap
  coe_injective := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    congr
    exact DFunLike.coe_injective h

instance : ContinuousMapClass (NonconstantMap Y X) Y X where
  map_continuous u := u.toContinuousMap.continuous

@[simp]
theorem coe_toContinuousMap (u : NonconstantMap Y X) : ⇑u.toContinuousMap = u :=
  (rfl)

@[simp]
theorem mk_apply (u : C(Y, X)) (hu : ∃ z w, u z ≠ u w) (z : Y) : mk u hu z = u z :=
  (rfl)

theorem toContinuousMap_injective :
    Injective (toContinuousMap : NonconstantMap Y X → C(Y, X)) := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩ rfl
  rfl

@[ext]
theorem ext {u v : NonconstantMap Y X} (h : ∀ z, u z = v z) : u = v :=
  DFunLike.ext _ _ h

/-- A nonconstant map takes two different values. -/
theorem exists_apply_ne (u : NonconstantMap Y X) : ∃ z w, u z ≠ u w :=
  u.exists_apply_ne'

/-- The compact-open topology on nonconstant maps, induced from all continuous maps. -/
instance : TopologicalSpace (NonconstantMap Y X) :=
  .induced toContinuousMap inferInstance

/-- The topology of the nonconstant maps is induced by the compact-open topology. -/
theorem isEmbedding_toContinuousMap :
    IsEmbedding (toContinuousMap : NonconstantMap Y X → C(Y, X)) :=
  ⟨⟨rfl⟩, toContinuousMap_injective⟩

@[fun_prop]
theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : NonconstantMap Y X → C(Y, X)) :=
  isEmbedding_toContinuousMap.continuous

instance [T2Space X] : T2Space (NonconstantMap Y X) :=
  isEmbedding_toContinuousMap.t2Space

instance [WeaklyLocallyCompactSpace Y] [SigmaCompactSpace Y] [MetrizableSpace X] :
    MetrizableSpace (NonconstantMap Y X) :=
  isEmbedding_toContinuousMap.metrizableSpace

/-- The evaluation `(u, z) ↦ u z` is jointly continuous. -/
instance [LocallyCompactPair Y X] : ContinuousEval (NonconstantMap Y X) Y X where
  continuous_eval :=
    (ContinuousEval.continuous_eval (F := C(Y, X))).comp
      (continuous_toContinuousMap.prodMap continuous_id)

variable {G : Type*} [Group G] [MulAction G Y]

section ContinuousConstSMul

variable [ContinuousConstSMul G Y]

/-- The **reparametrization action** of `G` on nonconstant maps, `g • u = u ∘ (g⁻¹ • ·)`.
Its orbits are those of the right action `u ↦ u ∘ (g • ·)` by precomposition. -/
instance : SMul G (NonconstantMap Y X) where
  smul g u := ⟨u.toContinuousMap.comp ⟨(g⁻¹ • ·), continuous_const_smul _⟩, by
    obtain ⟨z, w, h⟩ := u.exists_apply_ne
    exact ⟨g • z, g • w, by simpa using h⟩⟩

@[simp]
theorem smul_apply (g : G) (u : NonconstantMap Y X) (z : Y) : (g • u) z = u (g⁻¹ • z) :=
  (rfl)

@[simp]
theorem toContinuousMap_smul (g : G) (u : NonconstantMap Y X) :
    (g • u).toContinuousMap = u.toContinuousMap.comp ⟨(g⁻¹ • ·), continuous_const_smul _⟩ :=
  (rfl)

instance : MulAction G (NonconstantMap Y X) where
  one_smul u := ext fun z ↦ by simp
  mul_smul g h u := ext fun z ↦ by simp [mul_smul]

theorem smul_apply_smul (g : G) (u : NonconstantMap Y X) (z : Y) : (g • u) (g • z) = u z := by
  simp

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace G] [ContinuousSMul G Y]

/-- The homeomorphism `z ↦ g • z` depends continuously on `g`, as a continuous map of `Y`. -/
private theorem continuous_smulMap :
    Continuous fun g : G ↦ (⟨(g • ·), continuous_const_smul g⟩ : C(Y, Y)) :=
  (ContinuousMap.curry ⟨fun p : G × Y ↦ p.1 • p.2, continuous_smul⟩).continuous

/-- The reparametrization action is continuous when the action on `Y` is: composition of maps out
of `Y` is continuous for the compact-open topology. -/
instance instContinuousSMul [ContinuousInv G] [LocallyCompactPair Y X] :
    ContinuousSMul G (NonconstantMap Y X) where
  continuous_smul := by
    refine isEmbedding_toContinuousMap.continuous_iff.2 ?_
    exact ContinuousMap.continuous_comp'.comp
      ((continuous_smulMap.comp continuous_inv.fst').prodMk continuous_toContinuousMap.snd')

end ContinuousSMul

end NonconstantMap

end Maps

variable (G Y X : Type*) [Group G] [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
  [TopologicalSpace X]

/-- The **unparametrized maps** `Y → X`: the orbit space of the nonconstant maps under
reparametrization by `G`. -/
abbrev UnparametrizedMap : Type _ :=
  MulAction.orbitRel.Quotient G (NonconstantMap Y X)

/-- The **one-marked unparametrized maps** `Y → X`: the orbit space of pairs `(u, z)` of a
nonconstant map and a point under `g • (u, z) = (g • u, g • z)`, which identifies
`(u ∘ (g • ·), z)` with `(u, g • z)`. -/
abbrev MarkedUnparametrizedMap : Type _ :=
  MulAction.orbitRel.Quotient G (NonconstantMap Y X × Y)

namespace MarkedUnparametrizedMap

variable {G Y X}

/-- The **evaluation map** `[u, z] ↦ u z` on one-marked unparametrized maps. -/
def eval : MarkedUnparametrizedMap G Y X → X :=
  Quotient.lift (fun p ↦ p.1 p.2) <| by
    rintro _ ⟨u, z⟩ ⟨g, rfl⟩
    exact NonconstantMap.smul_apply_smul g u z

@[simp]
theorem eval_mk (u : NonconstantMap Y X) (z : Y) :
    eval (Quotient.mk _ (u, z) : MarkedUnparametrizedMap G Y X) = u z :=
  (rfl)

/-- The evaluation map is continuous. -/
@[fun_prop]
theorem continuous_eval [LocallyCompactPair Y X] :
    Continuous (eval : MarkedUnparametrizedMap G Y X → X) :=
  isQuotientMap_quotient_mk'.continuous_iff.2 <|
    ContinuousEval.continuous_eval.congr fun p : NonconstantMap Y X × Y ↦ (eval_mk p.1 p.2).symm

/-- Forgetting the marked point, `[u, z] ↦ [u]`. -/
def forget : MarkedUnparametrizedMap G Y X → UnparametrizedMap G Y X :=
  Quotient.map' Prod.fst <| by
    rintro _ ⟨u, z⟩ ⟨g, rfl⟩
    exact ⟨g, rfl⟩

@[simp]
theorem forget_mk (u : NonconstantMap Y X) (z : Y) :
    forget (Quotient.mk _ (u, z) : MarkedUnparametrizedMap G Y X) = Quotient.mk _ u :=
  (rfl)

@[fun_prop]
theorem continuous_forget : Continuous (forget : MarkedUnparametrizedMap G Y X → _) :=
  isQuotientMap_quotient_mk'.continuous_iff.2 <|
    (continuous_quotient_mk'.comp continuous_fst).congr fun p : NonconstantMap Y X × Y ↦
      (forget_mk p.1 p.2).symm

theorem forget_surjective : Surjective (forget : MarkedUnparametrizedMap G Y X → _) := by
  rintro ⟨u⟩
  obtain ⟨z, -, -⟩ := u.exists_apply_ne
  exact ⟨Quotient.mk _ (u, z), rfl⟩

end MarkedUnparametrizedMap

end TauCeti
