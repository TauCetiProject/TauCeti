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
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Mapping tori and fibering over the circle

For a homeomorphism `φ : F ≃ₜ F`, the mapping torus identifies `(φ x, t + 1)` with
`(x, t)`. The quotient model below is deliberately topological: manifold charts are separate
geometric input. Local product charts for the circle projection are constructed in
`TauCeti.Topology.MappingTorus.LocalProduct`. `MappingTorusPresentation`
stores the fibre and monodromy, while `FibersOverCircle` asserts that such a presentation
exists.

Functions on the cylinder `F × ℝ` invariant under the integer action descend to the mapping torus
through `MappingTorus.lift`, its universal property as a quotient.

The quotient projection to `UnitAddCircle` records the circle coordinate of each orbit; the fibre
over `0` is `MappingTorus.fiber`, the image of the inclusion `MappingTorus.incl`.
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

/-- The defining integer action applies monodromy and translates the height. -/
@[simp] theorem action_vadd (φ : F ≃ₜ F) (n : ℤ) (p : F × ℝ) :
    letI := action φ
    n +ᵥ p = ((φ ^ n) p.1, p.2 + n) := (rfl)

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

/-- The cylinder quotient defining a mapping torus is an open map. -/
theorem isOpenMap_mk (φ : F ≃ₜ F) :
    IsOpenMap (fun p : F × ℝ => mk φ p.1 p.2) := by
  let _ := action φ
  have : ContinuousConstVAdd ℤ (F × ℝ) := ⟨fun n => by
    simp only [action_vadd]
    exact ((φ ^ n).continuous.comp continuous_fst).prodMk
      (continuous_snd.add continuous_const)⟩
  -- The cylinder map wraps the orbit quotient's `mk'` with a pair of projections.
  convert (isOpenMap_quotient_mk'_add (Γ := ℤ) (T := F × ℝ)) using 1
  funext p
  rfl

/-- **The universal property of the mapping torus.** A function on the cylinder `F × ℝ` which is
invariant under the integer action, `f ((φ ^ n) x, t + n) = f (x, t)`, descends to the mapping
torus. -/
def lift {β : Sort*} (φ : F ≃ₜ F) (f : F × ℝ → β)
    (hf : ∀ (n : ℤ) (x : F) (t : ℝ), f ((φ ^ n) x, t + n) = f (x, t)) : MappingTorus φ → β :=
  letI : AddAction ℤ (F × ℝ) := MappingTorus.action φ
  Quotient.lift f fun a b hab ↦ by
    obtain ⟨n, rfl⟩ := AddAction.mem_orbit_iff.mp hab
    exact hf n b.1 b.2

@[simp]
lemma lift_mk {β : Sort*} (φ : F ≃ₜ F) (f : F × ℝ → β)
    (hf : ∀ (n : ℤ) (x : F) (t : ℝ), f ((φ ^ n) x, t + n) = f (x, t)) (x : F) (t : ℝ) :
    lift φ f hf (mk φ x t) = f (x, t) := (rfl)

/-- A continuous function on the cylinder descends to a continuous function on the mapping
torus. -/
theorem continuous_lift {β : Type*} [TopologicalSpace β] (φ : F ≃ₜ F) {f : F × ℝ → β}
    (hf : ∀ (n : ℤ) (x : F) (t : ℝ), f ((φ ^ n) x, t + n) = f (x, t)) (hc : Continuous f) :
    Continuous (lift φ f hf) :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr hc

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

/-- A map of mapping tori carries the canonical cylinder homotopy to the canonical cylinder
homotopy of the image point. -/
-- Rewrite before simplification unfolds the homotopy track to a cylinder representative.
@[simp↓]
lemma map_monodromyHomotopy (φ : F ≃ₜ F) (ψ : G ≃ₜ G) (g : C(F, G))
    (h : Function.Semiconj g φ ψ) (t : unitInterval) (x : F) :
    map φ ψ g h (monodromyHomotopy φ (t, x)) =
      monodromyHomotopy ψ (t, g x) := by
  simpa using congrArg (fun y ↦ mk ψ y (t : ℝ)) (h x)

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

/-- The fibre of a mapping torus over `0` in the circle. It is the image of the fibre inclusion
`MappingTorus.incl` (`MappingTorus.range_incl`). -/
def fiber (φ : F ≃ₜ F) : Set (MappingTorus φ) := proj φ ⁻¹' {0}

@[simp]
lemma mem_fiber_iff (φ : F ≃ₜ F) {z : MappingTorus φ} : z ∈ fiber φ ↔ proj φ z = 0 := Iff.rfl

/-- The fibre over `0` is closed. -/
theorem isClosed_fiber (φ : F ≃ₜ F) : IsClosed (fiber φ) :=
  isClosed_singleton.preimage (continuous_proj φ)

/-- The fibre inclusion lands in the fibre over `0`. -/
lemma incl_mem_fiber (φ : F ≃ₜ F) (x : F) : incl φ x ∈ fiber φ := by
  simp

/-- The fibre over `0` is exactly the image of the fibre inclusion. -/
@[simp]
theorem range_incl (φ : F ≃ₜ F) : Set.range (incl φ) = fiber φ := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 (incl_mem_fiber φ)) fun z hz ↦ ?_
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).1 ((proj_mk φ x t).symm.trans hz)
  refine ⟨(φ ^ (-n)) x, (mk_eq_iff φ).2 ⟨-n, rfl, ?_⟩⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  push_cast
  linarith

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
