/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Algebra.ProperAction.Slice

import TauCeti.Topology.Covering.BalancedProduct.RightTranslation

/-!
# Clean neighbourhoods for group actions

A neighbourhood of `x` is clean if it is invariant under the stabilizer of `x` and disjoint
from its translates by elements outside that stabilizer. Proper actions of discrete groups have
arbitrarily small clean open neighbourhoods. This includes finite groups acting by continuous maps
on Hausdorff spaces, with no local compactness required.

The contracted product `MulAction.ContractedProduct` identifies `(g, u)` with
`(g * h⁻¹, h • u)` for `h` fixing `x`. For a stabilizer-invariant open neighbourhood `U`,
cleanness is equivalent to injectivity of its evaluation map into `X`. Thus clean
neighbourhoods give the set-theoretic local model for finite quotient charts, including
points with nontrivial stabilizers.

## References

* D. Hansen and C. Johansson, *Perfectoid Shimura varieties and the Calegari–Emerton conjectures*,
  arXiv:2011.03951v2, definition preceding Lemma 5.2 and Lemma 5.2, pp. 27–28.
-/

public section

open Set Topology
open scoped Pointwise

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

section Contracted

private def toBalancedProduct (x : X) (U : Set X) (p : G × U) :
    TauCeti.BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation X :=
  TauCeti.BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation p.1) p.2

variable (G) in
/-- The contracted product by the stabilizer of `x`, restricted to `G × U`.
It quotients `G × U` by equality of classes in the ambient `TauCeti.BalancedProduct`:
`(g, u)` and `(g * h⁻¹, h • u)` are identified for `h • x = x`. This also makes sense
when `U` is not stabilizer-invariant. -/
def ContractedProduct (x : X) (U : Set X) : Type _ :=
  Quotient (Setoid.ker (toBalancedProduct (G := G) x U))

namespace ContractedProduct

/-- The class of `(g, u)` in the contracted product. -/
def mk (x : X) (U : Set X) (g : G) (u : U) : ContractedProduct G x U :=
  Quotient.mk _ (g, u)

/-- Equality of representatives is the usual contracted-product relation for the stabilizer. -/
theorem mk_eq_iff_exists {x : X} {U : Set X} {g k : G} {u v : U} :
    mk x U g u = mk x U k v ↔
      ∃ h : G, h • x = x ∧ k = g * h⁻¹ ∧ (v : X) = h • (u : X) := by
  have hmk : mk x U k v = mk x U g u ↔
      toBalancedProduct x U (k, v) = toBalancedProduct x U (g, u) :=
    ⟨Quotient.exact, fun h ↦ Quotient.sound h⟩
  rw [eq_comm (a := mk x U g u), hmk]
  simp only [toBalancedProduct,
    TauCeti.BalancedProduct.mk_toRightTranslation_eq_mk_toRightTranslation_iff]
  constructor
  · rintro ⟨h, hk, hv⟩
    exact ⟨h, mem_stabilizer_iff.mp h.property, hk.symm, hv.symm⟩
  · rintro ⟨h, hx, hk, hv⟩
    exact ⟨⟨h, mem_stabilizer_iff.mpr hx⟩, hk.symm, hv.symm⟩

/-- Two representatives agree precisely when their orbit labels and evaluations agree. -/
@[simp]
theorem mk_eq_iff {x : X} {U : Set X} {g k : G} {u v : U} :
    mk x U g u = mk x U k v ↔
      g • x = k • x ∧ g • (u : X) = k • (v : X) := by
  rw [mk_eq_iff_exists]
  constructor
  · rintro ⟨h, hx, rfl, hv⟩
    have hinv : h⁻¹ • x = x := inv_smul_eq_iff.mpr hx.symm
    simp [mul_smul, hinv, hv]
  · rintro ⟨hx, huv⟩
    refine ⟨k⁻¹ * g, ?_, by simp, ?_⟩
    · simpa [mul_smul] using congrArg (fun y : X ↦ k⁻¹ • y) hx
    · simpa [mul_smul] using (congrArg (fun y : X ↦ k⁻¹ • y) huv).symm

variable (G) in
/-- Every contracted-product point has a representative. -/
theorem mk_surjective (x : X) (U : Set X) :
    Function.Surjective fun p : G × U ↦ mk x U p.1 p.2 :=
  Quotient.mk_surjective

/-- To prove a property of a contracted-product point, it suffices to prove it on
representatives. -/
@[elab_as_elim]
theorem inductionOn {x : X} {U : Set X} {motive : ContractedProduct G x U → Prop}
    (q : ContractedProduct G x U) (h : ∀ g u, motive (mk x U g u)) : motive q :=
  Quotient.inductionOn q fun p ↦ h p.1 p.2

/-- A function of representatives descends to the contracted product if it respects equality
of orbit labels and evaluations. -/
def lift {x : X} {U : Set X} {Y : Sort*} (f : G → U → Y)
    (hf : ∀ (g : G) (u : U) (k : G) (v : U),
      g • x = k • x → g • (u : X) = k • (v : X) → f g u = f k v) :
    ContractedProduct G x U → Y :=
  Quotient.lift (fun p ↦ f p.1 p.2) fun p q h ↦
    have heq : mk x U p.1 p.2 = mk x U q.1 q.2 := Quotient.sound h
    let ⟨hx, huv⟩ := mk_eq_iff.mp heq
    hf _ _ _ _ hx huv

/-- The descended function agrees with the original function on representatives. -/
@[simp]
theorem lift_mk {x : X} {U : Set X} {Y : Sort*} (f : G → U → Y)
    (hf : ∀ (g : G) (u : U) (k : G) (v : U),
      g • x = k • x → g • (u : X) = k • (v : X) → f g u = f k v)
    (g : G) (u : U) : lift f hf (mk x U g u) = f g u := (rfl)

variable (G) in
/-- The map from the contracted product to the ambient space, sending `[g, u]` to `g • u`. -/
def eval (x : X) (U : Set X) : ContractedProduct G x U → X :=
  lift (fun g u ↦ g • (u : X)) fun _ _ _ _ _ huv ↦ huv

/-- Evaluation on a representative of the contracted product. -/
@[simp]
theorem eval_mk (x : X) (U : Set X) (g : G) (u : U) :
    eval G x U (mk x U g u) = g • (u : X) := (rfl)

variable (G) in
/-- The image of the evaluation map is the saturation of `U`. -/
theorem range_eval (x : X) (U : Set X) :
    range (eval G x U) = ⋃ g : G, g • U := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨⟨g, u⟩, rfl⟩ := mk_surjective G x U q
    exact mem_iUnion.mpr ⟨g, ⟨u, u.property, rfl⟩⟩
  · intro hy
    obtain ⟨g, u, hu, rfl⟩ := mem_iUnion.mp hy
    exact ⟨mk x U g ⟨u, hu⟩, eval_mk x U g ⟨u, hu⟩⟩

variable (G) in
/-- Evaluation is injective exactly when elements moving a point of `U` back into `U` fix the
distinguished point. No openness or invariance of `U` is needed. -/
theorem eval_injective_iff (x : X) (U : Set X) :
    Function.Injective (eval G x U) ↔
      ∀ (g : G) (u : X), u ∈ U → g • u ∈ U → g • x = x := by
  constructor
  · intro hinj g u hu hgu
    have heq := hinj (a₁ := mk x U g ⟨u, hu⟩)
      (a₂ := mk x U 1 ⟨g • u, hgu⟩) (by simp)
    simpa using (mk_eq_iff.mp heq).1
  · intro h p q hpq
    obtain ⟨⟨g, u⟩, rfl⟩ := mk_surjective G x U p
    obtain ⟨⟨k, v⟩, rfl⟩ := mk_surjective G x U q
    simp only [eval_mk] at hpq
    apply mk_eq_iff.mpr
    refine ⟨?_, hpq⟩
    have huv : (k⁻¹ * g) • (u : X) = v := by
      simpa [mul_smul] using congrArg (fun z : X ↦ k⁻¹ • z) hpq
    have hx := h (k⁻¹ * g) u u.property (huv ▸ v.property)
    simpa [mul_smul] using congrArg (fun z : X ↦ k • z) hx

end ContractedProduct

end Contracted

section Topology

variable [TopologicalSpace X] {x : X} {U V : Set X}

/-- A clean open neighbourhood of `x` is stabilizer-invariant and disjoint from the translates
by elements not fixing `x`. For right actions, use the left action of the opposite group. -/
structure IsClean (G : Type*) {X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    (x : X) (U : Set X) : Prop where
  /-- The neighbourhood is open. -/
  isOpen : IsOpen U
  /-- The distinguished point lies in the neighbourhood. -/
  mem : x ∈ U
  /-- Elements of the stabilizer preserve the neighbourhood. -/
  smul_eq : ∀ g : G, g • x = x → g • U = U
  /-- The other translates are disjoint from the neighbourhood. -/
  disjoint_smul : ∀ g : G, g • x ≠ x → Disjoint U (g • U)

/-- The empty set is not a clean neighbourhood of any point. -/
@[simp]
theorem not_isClean_empty (x : X) : ¬ IsClean G x ∅ := fun h ↦ h.mem

/-- A clean neighbourhood cannot contain both `u` and `g • u` unless `g` fixes `x`. -/
theorem IsClean.smul_eq_of_mem (hU : IsClean G x U) {g : G} {u : X}
    (hu : u ∈ U) (hgu : g • u ∈ U) : g • x = x := by
  by_contra hg
  exact Set.disjoint_left.mp (hU.disjoint_smul g hg) hgu ⟨u, hu, rfl⟩

/-- Cleanness is equivalent to stabilizer-invariance and injectivity of the
contracted-product evaluation map, for an open neighbourhood of the distinguished point. -/
theorem isClean_iff_eval_injective (hU : IsOpen U) (hx : x ∈ U) :
    IsClean G x U ↔ (∀ g : G, g • x = x → g • U = U) ∧
      Function.Injective (ContractedProduct.eval G x U) := by
  rw [ContractedProduct.eval_injective_iff]
  refine ⟨fun h ↦ ⟨h.smul_eq, fun _ _ hu hgu ↦ h.smul_eq_of_mem hu hgu⟩, ?_⟩
  rintro ⟨hstable, h⟩
  refine ⟨hU, hx, hstable, fun g hg ↦ Set.disjoint_left.mpr ?_⟩
  rintro y hy ⟨u, hu, rfl⟩
  exact hg (h g u hu hy)

/-- Intersecting two clean neighbourhoods of the same point gives a clean neighbourhood. -/
theorem IsClean.inter (hU : IsClean G x U) (hV : IsClean G x V) :
    IsClean G x (U ∩ V) where
  isOpen := hU.isOpen.inter hV.isOpen
  mem := ⟨hU.mem, hV.mem⟩
  smul_eq g hg := by rw [smul_set_inter, hU.smul_eq g hg, hV.smul_eq g hg]
  disjoint_smul g hg := (hU.disjoint_smul g hg).mono inter_subset_left
    (smul_set_mono inter_subset_left)

/-- For an action fixing every point, clean sets are exactly open neighbourhoods. -/
theorem isClean_iff_of_forall_smul_eq_self (h : ∀ (g : G) (y : X), g • y = y) :
    IsClean G x U ↔ IsOpen U ∧ x ∈ U := by
  refine ⟨fun hU ↦ ⟨hU.isOpen, hU.mem⟩, fun hU ↦ ⟨hU.1, hU.2, ?_, ?_⟩⟩
  · intro g _
    exact Set.ext fun y ↦ by simp [mem_smul_set_iff_inv_smul_mem, h]
  · intro g hg
    exact (hg (h g x)).elim

/-- An open singleton is clean, even if the stabilizer is nontrivial. In particular this
applies to every singleton in a discrete space. -/
theorem isClean_singleton (x : X) (hx : IsOpen ({x} : Set X)) : IsClean G x {x} where
  isOpen := hx
  mem := mem_singleton x
  smul_eq g hg := by simp [hg]
  disjoint_smul g hg := by simpa [disjoint_singleton_left] using hg.symm

variable (G) in
/-- For a proper action of a discrete group, every neighbourhood of a point contains
a clean open neighbourhood of that point. -/
theorem _root_.ProperSMul.exists_isClean [TopologicalSpace G] [DiscreteTopology G]
    [ProperSMul G X] (x : X) (hV : V ∈ 𝓝 x) : ∃ U ⊆ V, IsClean G x U := by
  obtain ⟨U, hU, hxU, hUV, hslice⟩ := ProperSMul.exists_slice G x hV
  refine ⟨U, hUV, (isClean_iff_eval_injective hU hxU).mpr ⟨?_, ?_⟩⟩
  · intro g hg
    exact SetLike.units_smul U (toUnits ⟨g, mem_stabilizer_iff.mpr hg⟩)
  · exact (ContractedProduct.eval_injective_iff G x U).mpr fun g u hu hgu ↦
      mem_stabilizer_iff.mp (hslice g u hu hgu)

variable (G) in
/-- A finite group acting by continuous maps on a Hausdorff space has arbitrarily small clean
open neighbourhoods. Local compactness and freeness are not required. -/
theorem exists_isClean [Finite G] [ContinuousConstSMul G X] [T2Space X] (x : X)
    (V : Set X) (hV : V ∈ 𝓝 x) : ∃ U ⊆ V, IsClean G x U := by
  -- Give the finite group the discrete topology to use the proper-action result.
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  let : ProperSMul G X := TauCeti.properSMul_of_compactSpace G X
  exact ProperSMul.exists_isClean G x hV

end Topology

end MulAction

/-! The degenerate and finite-orbit cases distinguish the contracted product from either
`G × U` (which retains the stabilizer) or the saturation of `U` (which can lose orbit labels). -/

open MulAction

-- An empty input gives no contracted-product points.
example (G X : Type*) [Group G] [MulAction G X] (x : X) :
    IsEmpty (ContractedProduct G x (∅ : Set X)) :=
  ⟨fun q ↦ q.inductionOn fun _ u ↦ u.property⟩

-- For a trivial action, evaluation is injective and its image is exactly the input set.
example {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ (g : G) (y : X), g • y = y) (x : X) (U : Set X) :
    Function.Injective (ContractedProduct.eval G x U) :=
  (ContractedProduct.eval_injective_iff G x U).mpr fun g _ _ _ ↦ h g x

example {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ (g : G) (y : X), g • y = y) (x : X) (U : Set X) :
    range (ContractedProduct.eval G x U) = U := by
  rw [ContractedProduct.range_eval]
  have hs (g : G) : g • U = U := by
    ext y
    simp [mem_smul_set_iff_inv_smul_mem, h]
  simp only [hs]
  exact iUnion_const U

-- A singleton maps injectively onto its orbit, without requiring a trivial stabilizer.
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Function.Injective (ContractedProduct.eval G x {x}) := by
  rw [ContractedProduct.eval_injective_iff]
  intro g u hu hgu
  simpa only [mem_singleton_iff.mp hu, mem_singleton_iff] using hgu

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    range (ContractedProduct.eval G x {x}) = orbit G x := by
  ext y
  simp [ContractedProduct.range_eval, mem_orbit_iff]

-- A clean singleton for a nontrivial finite action, and the obstruction on its whole orbit.
example : IsClean (Equiv.Perm Bool) false {false} :=
  isClean_singleton false (isOpen_discrete _)

example : ¬ IsClean (Equiv.Perm Bool) false Set.univ := by
  intro h
  have := h.smul_eq_of_mem (g := Equiv.swap false true) (mem_univ false) (mem_univ true)
  simp at this

-- The transposition moves the singleton chart to the other point.
example : ContractedProduct.eval (Equiv.Perm Bool) false {false}
    (ContractedProduct.mk false {false} (Equiv.swap false true) ⟨false, rfl⟩) = true := by
  simp

-- A whole two-point orbit has two different orbit labels with the same evaluation.
example : ¬ Function.Injective
    (ContractedProduct.eval (Equiv.Perm Bool) false Set.univ) := by
  rw [ContractedProduct.eval_injective_iff]
  intro h
  have := h (Equiv.swap false true) false (mem_univ _) (mem_univ _)
  simp at this
