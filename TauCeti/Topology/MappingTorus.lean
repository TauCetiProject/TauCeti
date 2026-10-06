/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Constructions
public import Mathlib.GroupTheory.GroupAction.Defs
public import TauCeti.Topology.Instances.AddCircle.Defs
import TauCeti.Topology.Homeomorph.Semiconj

/-!
# Mapping tori and fibering over the circle

For a homeomorphism `φ : F ≃ₜ F`, the mapping torus identifies `(φ x, t + 1)` with
`(x, t)`. The quotient model below is deliberately topological: manifold charts and
the local-triviality theorem are separate geometric input. `MappingTorusPresentation`
stores the fibre and monodromy, while `FibersOverCircle` asserts that such a presentation
exists.

The quotient projection to `UnitAddCircle` records the circle coordinate of each orbit.
The map `MappingTorus.incl` includes the fibre at height zero.  Moving once around the cylinder
gives `MappingTorus.monodromyHomotopy`, a homotopy from this inclusion after the monodromy to the
inclusion itself.

A continuous map `g : F → G` intertwining monodromies `φ` and `ψ` induces
`MappingTorus.map φ ψ g h : C(MappingTorus φ, MappingTorus ψ)`, acting on cylinder representatives
by `g` in the fibre coordinate and the identity in the height coordinate. These induced maps lie
over the circle (`MappingTorus.proj_comp_map`), restrict to `g` on the fibres at height zero
(`MappingTorus.map_comp_incl`), and are functorial (`MappingTorus.map_id`,
`MappingTorus.map_comp`). They are the maps needed to state naturality of constructions on mapping
tori under commuting squares of monodromies.

The construction follows the standard mapping-torus model, e.g. Hatcher,
*Algebraic Topology*, Section 2.2.
-/

universe u

public section

open Topology

namespace TauCeti

variable {F : Type*} [TopologicalSpace F]

namespace MappingTorus

/-- The integer action translating the real coordinate and applying monodromy. -/
def vadd (φ : F ≃ₜ F) (n : ℤ) (p : F × ℝ) : F × ℝ :=
  ((φ ^ n) p.1, p.2 + n)

/-- The additive action whose orbits form the mapping torus. -/
@[instance_reducible]
def action (φ : F ≃ₜ F) : AddAction ℤ (F × ℝ) where
  vadd := vadd φ
  zero_vadd p := by
    -- Unfold the action field to expose the concrete `vadd` operation.
    change vadd φ 0 p = p
    dsimp [vadd]
    simp
  add_vadd m n p := by
    -- Unfold the action field to expose the concrete `vadd` operation.
    change vadd φ (m + n) p = vadd φ m (vadd φ n p)
    dsimp [vadd]
    apply Prod.ext
    · rw [zpow_add, Homeomorph.mul_apply]
    · push_cast
      ring_nf

end MappingTorus

/-- The topological mapping torus of a self-homeomorphism. -/
abbrev MappingTorus (φ : F ≃ₜ F) :=
  @AddAction.orbitRel.Quotient ℤ (F × ℝ) inferInstance (MappingTorus.action φ)

namespace MappingTorus

/-- The quotient map from the cylinder used to construct the mapping torus. -/
def mk (φ : F ≃ₜ F) (x : F) (t : ℝ) : MappingTorus φ :=
  @Quotient.mk'' (F × ℝ)
    (@AddAction.orbitRel ℤ (F × ℝ) inferInstance (MappingTorus.action φ)) (x, t)

/-- The quotient identifies (φ ^ n) x at height t + n with x at height t. -/
@[simp]
theorem mk_vadd (φ : F ≃ₜ F) (n : ℤ) (x : F) (t : ℝ) :
    mk φ ((φ ^ n) x) (t + n) = mk φ x t := by
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  unfold mk
  apply Quotient.sound
  exact AddAction.orbitRel_apply.mpr ⟨n, rfl⟩

/-- Two cylinder points represent the same mapping-torus point exactly when they differ
by an integer translate in the monodromy orbit and the corresponding height translate. -/
theorem mk_eq_iff (φ : F ≃ₜ F) {x y : F} {t s : ℝ} :
    mk φ x t = mk φ y s ↔ ∃ n : ℤ, (φ ^ n) y = x ∧ s + n = t := by
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  unfold mk
  rw [Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · exact congrArg Prod.fst hn
    · exact congrArg Prod.snd hn
  · rintro ⟨n, hxy, hts⟩
    exact ⟨n, Prod.ext hxy hts⟩

/-- Every point of a mapping torus is represented by a point of the cylinder. -/
theorem mk_surjective (φ : F ≃ₜ F) : Function.Surjective fun p : F × ℝ ↦ mk φ p.1 p.2 :=
  Quotient.mk''_surjective

/-- The quotient map from the cylinder to the mapping torus is continuous. -/
theorem continuous_mk (φ : F ≃ₜ F) : Continuous fun p : F × ℝ ↦ mk φ p.1 p.2 :=
  continuous_quotient_mk'

/-- The canonical inclusion of the fibre at height zero into its mapping torus. -/
def incl (φ : F ≃ₜ F) : C(F, MappingTorus φ) :=
  ⟨fun x ↦ mk φ x 0, (continuous_mk φ).comp (continuous_id.prodMk continuous_const)⟩

/-- The fibre inclusion sends a point to its class at height zero. -/
@[simp]
lemma incl_apply (φ : F ≃ₜ F) (x : F) : incl φ x = mk φ x 0 := (rfl)

/-- Going once around the mapping torus gives a homotopy from the fibre inclusion after
monodromy to the fibre inclusion itself. -/
def monodromyHomotopy (φ : F ≃ₜ F) :
    ((incl φ).comp ⟨φ, φ.continuous⟩).Homotopy (incl φ) where
  toFun p := mk φ (φ p.2) p.1
  continuous_toFun := (continuous_mk φ).comp
    ((φ.continuous.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst))
  map_zero_left x := rfl
  map_one_left x := by
    simpa using mk_vadd φ 1 x 0

/-- The canonical monodromy homotopy moves linearly in the cylinder coordinate. -/
@[simp]
lemma monodromyHomotopy_apply (φ : F ≃ₜ F) (t : unitInterval) (x : F) :
    monodromyHomotopy φ (t, x) = mk φ (φ x) t := (rfl)

section Map

variable {G : Type*} [TopologicalSpace G]

/-- A continuous map intertwining two monodromies induces a map of their mapping tori. -/
def map (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (g : C(F, G)) (h : Function.Semiconj g φ ψ) :
    C(MappingTorus φ, MappingTorus ψ) :=
  letI : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  { toFun := Quotient.lift (fun p : F × ℝ ↦ mk ψ (g p.1) p.2) fun a b hab ↦ by
      obtain ⟨n, rfl⟩ := AddAction.mem_orbit_iff.mp hab
      -- The action orbit witness must be unfolded to expose its two coordinates.
      change mk ψ (g ((φ ^ n) b.1)) (b.2 + n) = mk ψ (g b.1) b.2
      rw [h.homeomorph_zpow_right n]
      exact mk_vadd ψ n (g b.1) b.2
    continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr <|
      (continuous_mk ψ).comp ((g.continuous.comp continuous_fst).prodMk continuous_snd) }

/-- The map induced between mapping tori acts on cylinder representatives by the original map. -/
@[simp]
lemma map_mk (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (g : C(F, G)) (h : Function.Semiconj g φ ψ)
    (x : F) (t : ℝ) : map φ ψ g h (mk φ x t) = mk ψ (g x) t := (rfl)

/-- A map of mapping tori restricts on the fibre to the map intertwining the monodromies. -/
@[simp]
lemma map_comp_incl (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (g : C(F, G))
    (h : Function.Semiconj g φ ψ) :
    (map φ ψ g h).comp (incl φ) = (incl ψ).comp g := by
  ext x
  simp

/-- The map of a mapping torus induced by the identity map is the identity. -/
@[simp]
lemma map_id (φ : F ≃ₜ F) :
    map φ φ (ContinuousMap.id F) (by intro x; rfl) =
      ContinuousMap.id (MappingTorus φ) := by
  ext z
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  simp

/-- Maps of mapping tori respect composition of maps intertwining the monodromies. -/
@[simp]
lemma map_comp {H : Type*} [TopologicalSpace H] (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (χ : H ≃ₜ H)
    (g : C(F, G)) (k : C(G, H)) (hg : Function.Semiconj g φ ψ)
    (hk : Function.Semiconj k ψ χ) :
    (map ψ χ k hk).comp (map φ ψ g hg) = map φ χ (k.comp g) (hg.trans hk) := by
  ext z
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  simp

end Map

/-- The canonical projection of a mapping torus to the circle. -/
def proj (φ : F ≃ₜ F) : MappingTorus φ → UnitAddCircle :=
  letI := MappingTorus.action φ
  Quotient.lift (fun z : F × ℝ ↦ (z.2 : UnitAddCircle)) (by
    intro a b h
    obtain ⟨n, rfl⟩ := AddAction.mem_orbit_iff.mp h
    -- The action orbit witness must be unfolded to expose its real coordinate.
    change ((b.2 + (n : ℝ) : ℝ) : UnitAddCircle) = (b.2 : UnitAddCircle)
    rw [AddCircle.coe_add]
    simp)

@[simp]
theorem proj_mk (φ : F ≃ₜ F) (x : F) (t : ℝ) :
    proj φ (mk φ x t) = (t : UnitAddCircle) := by
  unfold proj mk
  apply Quotient.lift_mk

/-- The canonical projection from a mapping torus to the additive circle is continuous. -/
theorem continuous_proj (φ : F ≃ₜ F) : Continuous (proj φ) := by
  unfold proj
  let _ : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  simpa using
    ((isQuotientMap_quotient_mk' (s := AddAction.orbitRel ℤ (F × ℝ))).continuous_iff.mpr
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))

/-- The projection from the mapping torus of a nonempty space onto the circle is surjective. -/
theorem proj_surjective [Nonempty F] (φ : F ≃ₜ F) : Function.Surjective (proj φ) := by
  intro θ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact ⟨mk φ (Classical.arbitrary F) t, proj_mk φ _ t⟩

section Map

variable {G : Type*} [TopologicalSpace G]

/-- A map of mapping tori preserves the projection to the circle. -/
@[simp]
lemma proj_comp_map (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (g : C(F, G))
    (h : Function.Semiconj g φ ψ) :
    (⟨proj ψ, continuous_proj ψ⟩ : C(MappingTorus ψ, UnitAddCircle)).comp
        (map φ ψ g h) =
      (⟨proj φ, continuous_proj φ⟩ : C(MappingTorus φ, UnitAddCircle)) := by
  ext z
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  simp

end Map

end MappingTorus

/-- A mapping-torus presentation of a topological space, including its fibre and monodromy. -/
structure MappingTorusPresentation (M : Type u) [TopologicalSpace M] where
  /-- The fibre type. -/
  Fiber : Type u
  /-- The fibre is nonempty. -/
  nonemptyFiber : Nonempty Fiber
  /-- The topology carried by the fibre. -/
  fiberTopology : TopologicalSpace Fiber
  /-- The monodromy homeomorphism around the circle. -/
  monodromy : @Homeomorph Fiber Fiber fiberTopology fiberTopology
  /-- A homeomorphism from the presented space to the mapping torus. -/
  equivalence : @Homeomorph M (@MappingTorus Fiber fiberTopology monodromy)
      (by infer_instance) instTopologicalSpaceQuotient

/-- A space fibres over the circle when it is homeomorphic to a mapping torus. -/
def FibersOverCircle (M : Type u) [TopologicalSpace M] : Prop :=
  Nonempty (MappingTorusPresentation M)

/-- The mapping torus has its canonical presentation. -/
def MappingTorus.presentation [Nonempty F] (φ : F ≃ₜ F) :
    MappingTorusPresentation (MappingTorus φ) where
  Fiber := F
  nonemptyFiber := inferInstance
  fiberTopology := inferInstance
  monodromy := φ
  equivalence := Homeomorph.refl _

/-- The mapping torus carries its canonical fibering-over-the-circle presentation. -/
theorem fibersOverCircle_mappingTorus [Nonempty F] (φ : F ≃ₜ F) :
    FibersOverCircle (MappingTorus φ) :=
  ⟨MappingTorus.presentation φ⟩

/-- A homeomorphism transports a fibering-over-the-circle presentation. -/
theorem _root_.Homeomorph.fibersOverCircle {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (h : M ≃ₜ N) (hN : FibersOverCircle N) : FibersOverCircle M := by
  obtain ⟨p⟩ := hN
  let _ := p.fiberTopology
  let e : N ≃ₜ @MappingTorus p.Fiber p.fiberTopology p.monodromy := p.equivalence
  refine ⟨{ Fiber := p.Fiber
            nonemptyFiber := p.nonemptyFiber
            fiberTopology := p.fiberTopology
            monodromy := p.monodromy
            equivalence := ?_ }⟩
  exact h.trans e

/-- A space that fibers over the circle is infinite, since it maps onto the circle. -/
theorem FibersOverCircle.infinite {M : Type u} [TopologicalSpace M] (h : FibersOverCircle M) :
    Infinite M := by
  obtain ⟨p⟩ := h
  let _ := p.fiberTopology
  have := p.nonemptyFiber
  exact .of_surjective _ ((MappingTorus.proj_surjective p.monodromy).comp p.equivalence.surjective)

end TauCeti
