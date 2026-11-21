/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Algebra.ProperAction.Slice

/-!
# Clean neighbourhoods for group actions

A neighbourhood of `x` is clean if it is invariant under the stabilizer of `x` and disjoint
from its translates by elements outside that stabilizer. Finite group actions on Hausdorff
spaces have arbitrarily small clean open neighbourhoods; no local compactness is needed.

The contracted product `MulAction.cleanContracted` identifies `(g, u)` with
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

/-- The contracted product by the stabilizer of `x`, restricted to `G × U`.
The relation is equality of `(g • x, g • u)`: equivalently, `(g, u)` and
`(g * h⁻¹, h • u)` are identified for `h • x = x`. This definition also makes sense
when `U` is not stabilizer-invariant, by restricting the orbit relation. -/
def cleanContracted (x : X) (U : Set X) :=
  Quotient (Setoid.ker fun p : G × U ↦ (p.1 • x, p.1 • (p.2 : X)))

/-- The class of `(g, u)` in the contracted product. -/
def cleanContractedMk (x : X) (U : Set X) (g : G) (u : U) : cleanContracted (G := G) x U :=
  Quotient.mk _ (g, u)

/-- Two representatives agree precisely when their orbit labels and evaluations agree. -/
@[simp]
theorem cleanContractedMk_eq_iff {x : X} {U : Set X} {g k : G} {u v : U} :
    cleanContractedMk x U g u = cleanContractedMk x U k v ↔
      g • x = k • x ∧ g • (u : X) = k • (v : X) := by
  exact ⟨fun h ↦ Prod.mk.inj (Quotient.exact h),
    fun h ↦ Quotient.sound (Prod.ext h.1 h.2)⟩

/-- Equality of representatives is the usual contracted-product relation for the stabilizer.
In particular the two coordinates of the defining kernel impose no additional identifications. -/
theorem cleanContractedMk_eq_iff_exists {x : X} {U : Set X} {g k : G} {u v : U} :
    cleanContractedMk x U g u = cleanContractedMk x U k v ↔
      ∃ h : G, h • x = x ∧ k = g * h⁻¹ ∧ (v : X) = h • (u : X) := by
  rw [cleanContractedMk_eq_iff]
  constructor
  · rintro ⟨hx, huv⟩
    refine ⟨k⁻¹ * g, ?_, by simp, ?_⟩
    · simpa [mul_smul] using congrArg (fun y : X ↦ k⁻¹ • y) hx
    · simpa [mul_smul] using (congrArg (fun y : X ↦ k⁻¹ • y) huv).symm
  · rintro ⟨h, hx, rfl, hv⟩
    have hinv : h⁻¹ • x = x := inv_smul_eq_iff.mpr hx.symm
    simp [mul_smul, hinv, hv]

/-- Every contracted-product point has a representative. -/
theorem cleanContractedMk_surjective (x : X) (U : Set X) :
    Function.Surjective fun p : G × U ↦ cleanContractedMk x U p.1 p.2 :=
  Quotient.mk_surjective

/-- The map from the contracted product to the ambient space, sending `[g, u]` to `g • u`. -/
def cleanContractedMap (x : X) (U : Set X) : cleanContracted (G := G) x U → X :=
  Quotient.lift (fun p ↦ p.1 • (p.2 : X)) (fun _ _ h ↦ congrArg Prod.snd h)

/-- Evaluation on a representative of the contracted product. -/
@[simp]
theorem cleanContractedMap_mk (x : X) (U : Set X) (g : G) (u : U) :
    cleanContractedMap x U (cleanContractedMk x U g u) = g • (u : X) := (rfl)

/-- The image of the contracted product is the saturation of `U`. -/
theorem range_cleanContractedMap (x : X) (U : Set X) :
    range (cleanContractedMap (G := G) x U) = ⋃ g : G, g • U := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨⟨g, u⟩, rfl⟩ := cleanContractedMk_surjective x U q
    exact mem_iUnion.mpr ⟨g, ⟨u, u.2, rfl⟩⟩
  · intro hy
    obtain ⟨g, u, hu, rfl⟩ := mem_iUnion.mp hy
    exact ⟨cleanContractedMk x U g ⟨u, hu⟩, cleanContractedMap_mk x U g ⟨u, hu⟩⟩

/-- The contracted-product map is injective exactly when elements moving a point of `U`
back into `U` fix the distinguished point. No openness or invariance of `U` is needed. -/
theorem injective_cleanContractedMap_iff (x : X) (U : Set X) :
    Function.Injective (cleanContractedMap (G := G) x U) ↔
      ∀ (g : G) (u : X), u ∈ U → g • u ∈ U → g • x = x := by
  constructor
  · intro hinj g u hu hgu
    have heq := hinj (a₁ := cleanContractedMk x U g ⟨u, hu⟩)
      (a₂ := cleanContractedMk x U 1 ⟨g • u, hgu⟩) (by simp)
    simpa using (cleanContractedMk_eq_iff.mp heq).1
  · intro h p q hpq
    obtain ⟨⟨g, u⟩, rfl⟩ := cleanContractedMk_surjective x U p
    obtain ⟨⟨k, v⟩, rfl⟩ := cleanContractedMk_surjective x U q
    simp only [cleanContractedMap_mk] at hpq
    apply cleanContractedMk_eq_iff.mpr
    refine ⟨?_, hpq⟩
    have huv : (k⁻¹ * g) • (u : X) = v := by
      simpa [mul_smul] using congrArg (fun z : X ↦ k⁻¹ • z) hpq
    have hx := h (k⁻¹ * g) u u.2 (huv ▸ v.2)
    simpa [mul_smul] using congrArg (fun z : X ↦ k • z) hx

end Contracted

section Topology

variable [TopologicalSpace X] {x : X} {U V : Set X}

/-- A clean open neighbourhood of `x` is stabilizer-invariant and disjoint from the translates
by elements not fixing `x`. For right actions, use the left action of the opposite group. -/
structure IsGClean (G : Type*) {X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
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
theorem not_isGClean_empty (x : X) : ¬ IsGClean G x ∅ := fun h ↦ h.mem

/-- A clean neighbourhood cannot contain both `u` and `g • u` unless `g` fixes `x`. -/
theorem IsGClean.smul_eq_of_mem (hU : IsGClean G x U) {g : G} {u : X}
    (hu : u ∈ U) (hgu : g • u ∈ U) : g • x = x := by
  by_contra hg
  exact Set.disjoint_left.mp (hU.disjoint_smul g hg) hgu ⟨u, hu, rfl⟩

/-- Cleanness is equivalent to stabilizer-invariance and injectivity of the
contracted-product map, for an open neighbourhood of the distinguished point. -/
theorem isGClean_iff_injective (hU : IsOpen U) (hx : x ∈ U) :
    IsGClean G x U ↔ (∀ g : G, g • x = x → g • U = U) ∧
      Function.Injective (cleanContractedMap (G := G) x U) := by
  rw [injective_cleanContractedMap_iff]
  refine ⟨fun h ↦ ⟨h.smul_eq, fun _ _ hu hgu ↦ h.smul_eq_of_mem hu hgu⟩, ?_⟩
  rintro ⟨hstable, h⟩
  refine ⟨hU, hx, hstable, fun g hg ↦ Set.disjoint_left.mpr ?_⟩
  rintro y hy ⟨u, hu, rfl⟩
  exact hg (h g u hu hy)

/-- Intersecting two clean neighbourhoods of the same point gives a clean neighbourhood. -/
theorem IsGClean.inter (hU : IsGClean G x U) (hV : IsGClean G x V) :
    IsGClean G x (U ∩ V) where
  isOpen := hU.isOpen.inter hV.isOpen
  mem := ⟨hU.mem, hV.mem⟩
  smul_eq g hg := by rw [smul_set_inter, hU.smul_eq g hg, hV.smul_eq g hg]
  disjoint_smul g hg := (hU.disjoint_smul g hg).mono inter_subset_left
    (smul_set_mono inter_subset_left)

/-- For an action fixing every point, clean sets are exactly open neighbourhoods. -/
theorem isGClean_iff_of_forall_smul_eq_self (h : ∀ (g : G) (y : X), g • y = y) :
    IsGClean G x U ↔ IsOpen U ∧ x ∈ U := by
  refine ⟨fun hU ↦ ⟨hU.isOpen, hU.mem⟩, fun hU ↦ ⟨hU.1, hU.2, ?_, ?_⟩⟩
  · intro g _
    exact Set.ext fun y ↦ by simp [mem_smul_set_iff_inv_smul_mem, h]
  · intro g hg
    exact (hg (h g x)).elim

/-- An open singleton is clean, even if the stabilizer is nontrivial. In particular this
applies to every singleton in a discrete space. -/
theorem isGClean_singleton (x : X) (hx : IsOpen ({x} : Set X)) : IsGClean G x {x} where
  isOpen := hx
  mem := mem_singleton x
  smul_eq g hg := by simp [hg]
  disjoint_smul g hg := by simpa [disjoint_singleton_left] using hg.symm

/-- A finite group acting continuously on a Hausdorff space has arbitrarily small clean
open neighbourhoods. Local compactness and freeness are not required. -/
theorem exists_isGClean [Finite G] [ContinuousConstSMul G X] [T2Space X] (x : X)
    (V : Set X) (hV : V ∈ 𝓝 x) : ∃ U ⊆ V, IsGClean G x U := by
  -- Give the finite group the discrete topology to use the existing proper-action slice theorem.
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  let : ProperSMul G X := TauCeti.properSMul_of_compactSpace G X
  obtain ⟨U, hU, hxU, hUV, hslice⟩ := ProperSMul.exists_slice G x hV
  refine ⟨U, hUV, hU, hxU, ?_, ?_⟩
  · intro g hg
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact U.smul_mem ⟨g, hg⟩ hu
    · intro hy
      exact ⟨g⁻¹ • y, U.smul_mem ⟨g⁻¹, (stabilizer G x).inv_mem hg⟩ hy,
        smul_inv_smul g y⟩
  · intro g hg
    refine Set.disjoint_left.mpr ?_
    rintro y hy ⟨u, hu, rfl⟩
    exact hg (hslice g u hu hy)

end Topology

end MulAction

/-! The degenerate and finite-orbit cases distinguish the contracted product from either
`G × U` (which retains the stabilizer) or the saturation of `U` (which can lose orbit labels). -/

open MulAction

-- An empty input gives no contracted-product points.
example (G X : Type*) [Group G] [MulAction G X] (x : X) :
    IsEmpty (cleanContracted (G := G) x (∅ : Set X)) := by
  refine ⟨fun q ↦ ?_⟩
  obtain ⟨⟨_, u⟩, _⟩ := cleanContractedMk_surjective x ∅ q
  exact u.2

-- For a trivial action, evaluation is injective and its image is exactly the input set.
example {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ (g : G) (y : X), g • y = y) (x : X) (U : Set X) :
    Function.Injective (cleanContractedMap (G := G) x U) :=
  (injective_cleanContractedMap_iff x U).mpr fun g _ _ _ ↦ h g x

example {G X : Type*} [Group G] [MulAction G X]
    (h : ∀ (g : G) (y : X), g • y = y) (x : X) (U : Set X) :
    range (cleanContractedMap (G := G) x U) = U := by
  rw [range_cleanContractedMap]
  have hs (g : G) : g • U = U := by
    ext y
    simp [mem_smul_set_iff_inv_smul_mem, h]
  simp only [hs]
  exact iUnion_const U

-- A singleton maps injectively onto its orbit, without requiring a trivial stabilizer.
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Function.Injective (cleanContractedMap (G := G) x {x}) := by
  rw [injective_cleanContractedMap_iff]
  intro g u hu hgu
  simpa only [mem_singleton_iff.mp hu, mem_singleton_iff] using hgu

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    range (cleanContractedMap (G := G) x {x}) = orbit G x := by
  ext y
  simp [range_cleanContractedMap, mem_orbit_iff]

-- A clean singleton for a nontrivial finite action, and the obstruction on its whole orbit.
example : IsGClean (Equiv.Perm Bool) false {false} :=
  isGClean_singleton false (isOpen_discrete _)

example : ¬ IsGClean (Equiv.Perm Bool) false Set.univ := by
  intro h
  have := h.smul_eq_of_mem (g := Equiv.swap false true) (mem_univ false) (mem_univ true)
  simp at this

-- The transposition moves the singleton chart to the other point.
example : cleanContractedMap false {false}
    (cleanContractedMk false {false} (Equiv.swap false true) ⟨false, rfl⟩) = true := by
  simp

-- A whole two-point orbit has two different orbit labels with the same evaluation.
example : ¬ Function.Injective
    (cleanContractedMap (G := Equiv.Perm Bool) false Set.univ) := by
  rw [injective_cleanContractedMap_iff]
  intro h
  have := h (Equiv.swap false true) false (mem_univ _) (mem_univ _)
  simp at this
