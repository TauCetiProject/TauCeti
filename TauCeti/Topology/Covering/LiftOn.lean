/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Topology.SeparatedMap

/-!
# Lifting maps continuous on a set through covering maps

Let `p : E → X` be a covering map and `f : A → X` a map continuous on a set `s ⊆ A` which, as a
subspace, is simply connected and locally path-connected. By the lifting criterion
(`IsCoveringMap.existsUnique_continuousMap_lifts`), `f` lifts on `s` through `p`, through any
prescribed point over the value of `f` at a base point `a ∈ s`
(`IsCoveringMap.exists_continuousOn_lift`).

Fix such lifts `g y`, one through each point `y` of the fibre of `p` over `f a`. Their images on
`s` are pairwise disjoint as soon as `f` is injective on `s`
(`IsCoveringMap.pairwise_disjoint_image_lift`), and their union is the preimage under `p` of
`f '' s` (`IsCoveringMap.preimage_image_eq_iUnion_image_lift`). So `p ⁻¹' (f '' s)` splits into
one copy of `s` for each sheet of the covering.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3, Proposition 1.33 (the lifting criterion) and Proposition 1.34 (unique lifting).
-/

public section

open Function Set

namespace IsCoveringMap

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  {p : E → X} {f : A → X} {s : Set A} {a : A}

/-- A map continuous on a simply connected, locally path-connected set lifts on that set through a
covering map `p`, through any prescribed point `e` over its value at a point `a` of the set. -/
theorem exists_continuousOn_lift (hp : IsCoveringMap p) [SimplyConnectedSpace s]
    [LocallyPathConnectedSpace s] (hf : ContinuousOn f s) (ha : a ∈ s) {e : E}
    (he : p e = f a) :
    ∃ g : A → E, ContinuousOn g s ∧ g a = e ∧ EqOn (p ∘ g) f s := by
  classical
  -- Lift `f`, restricted to `s`, through `p`, then extend the lift by `e` outside `s`.
  obtain ⟨G, ⟨hG₀, hG⟩, -⟩ := hp.existsUnique_continuousMap_lifts
    ⟨s.domRestrict f, hf.domRestrict⟩ ⟨a, ha⟩ e he
  refine ⟨fun x ↦ if hx : x ∈ s then G ⟨x, hx⟩ else e, ?_, by simp [ha, hG₀],
    fun x hx ↦ by simpa [hx] using congrFun hG ⟨x, hx⟩⟩
  rw [continuousOn_iff_continuous_domRestrict]
  convert G.continuous using 1
  ext ⟨x, hx⟩
  simp [hx]

/-- The lifts through a covering map `p` of a map `f` injective on a preconnected set `s`, through
the points `y` of the fibre of `p` over `f a` for some `a ∈ s`, each continuous on `s` and taking
the value `y` at `a`, have pairwise disjoint images on `s`. -/
theorem pairwise_disjoint_image_lift (hp : IsCoveringMap p) (hs : IsPreconnected s)
    (hinj : InjOn f s) (ha : a ∈ s) {g : p ⁻¹' {f a} → A → E} (hg : ∀ y, ContinuousOn (g y) s)
    (hg₀ : ∀ y, g y a = y) (hgp : ∀ y, EqOn (p ∘ g y) f s) :
    Pairwise fun y y' ↦ Disjoint (g y '' s) (g y' '' s) :=
  fun y y' hyy' ↦ hp.isSeparatedMap.disjoint_image_of_eqOn_comp
    hp.isLocalHomeomorph.isLocallyInjective hs hinj (hg y) (hg y') (hgp y) (hgp y') ha
    (by rwa [hg₀, hg₀, Ne, ← Subtype.ext_iff])

/-- **The preimage of the image of a set is covered by its lifts.** For a covering map `p` and a map
`f` continuous on a simply connected, locally path-connected set `s`, the lifts of `f` through the
points `y` of the fibre over `f a` for some `a ∈ s`, each continuous on `s` and taking the value `y`
at `a`, have images on `s` whose union is the preimage under `p` of `f '' s`. -/
theorem preimage_image_eq_iUnion_image_lift (hp : IsCoveringMap p) [SimplyConnectedSpace s]
    [LocallyPathConnectedSpace s] (hf : ContinuousOn f s) (ha : a ∈ s)
    {g : p ⁻¹' {f a} → A → E} (hg : ∀ y, ContinuousOn (g y) s) (hg₀ : ∀ y, g y a = y)
    (hgp : ∀ y, EqOn (p ∘ g y) f s) :
    p ⁻¹' (f '' s) = ⋃ y, g y '' s := by
  refine Subset.antisymm ?_ (iUnion_subset fun y ↦ ?_)
  · rintro z ⟨x, hx, hxz⟩
    -- Lift `f` through `z` at `x`; this lift passes at `a` through a point `y` of the fibre, so it
    -- is the lift `g y`, which therefore takes the value `z` at `x`.
    obtain ⟨χ, hχ, hχx, hχp⟩ := hp.exists_continuousOn_lift hf hx hxz.symm
    have hy : χ a ∈ p ⁻¹' {f a} := hχp ha
    have hEq := hp.eqOn_of_comp_eqOn (isPreconnected_iff_preconnectedSpace.2 inferInstance)
      (hg ⟨χ a, hy⟩) hχ ((hgp _).trans hχp.symm) ha (hg₀ _)
    exact mem_iUnion.2 ⟨⟨χ a, hy⟩, x, hx, (hEq hx).trans hχx⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hgp y hx).symm⟩

end IsCoveringMap
