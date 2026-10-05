/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# Maps of coefficient modules on finite normal layers

A `G`-equivariant map `φ : A → A'` between the coefficient modules of two formations on `G`
carries every level `A^U` into the level `A'^U`. On a finite normal layer `V ◁ U` it therefore
induces a map `A^V → A'^V` of the coefficient modules of the layer, equivariant for the Galois
group `U ⧸ V`; this is `NormalLayer.repMap`, through which a map of formations acts on the
cohomology `L.H F n` of the layer.

Taking `V`-invariants is only left exact. A short exact sequence `0 → A → A' → A'' → 0` of
coefficient modules gives a short exact sequence `0 → A^V → A'^V → A''^V → 0` on the layer exactly
when every `V`-invariant element of `A''` lifts to a `V`-invariant element of `A'`, which is
`NormalLayer.shortExact_repMap`. For the sequence `0 → (Kˢ)ˣ → I_{Kˢ} → C_{Kˢ} → 0` of a number
field this lifting is Hilbert 90 for the top subgroup, and the resulting sequence
`0 → Lˣ → I_L → C_L → 0` is the source of the long exact sequence relating the cohomology of the
multiplicative, idele and idele-class formations of a layer.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.repMap`: the map of layer coefficient modules induced by
  an equivariant map of coefficient modules.

## Main statements

* `TauCeti.ClassFieldTheory.Formation.map_mem_level`: an equivariant map preserves levels.
* `TauCeti.ClassFieldTheory.NormalLayer.shortExact_repMap`: a short exact sequence of
  coefficient modules stays short exact on a layer once invariants of the top subgroup lift.
-/

public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F F' F'' : Formation G}

/-- **An equivariant map of coefficient modules preserves levels**: it carries an element fixed by
`U` to an element fixed by `U`. -/
theorem Formation.map_mem_level (φ : F.toRep ⟶ F'.toRep) {U : OpenSubgroup G} {x : F.toRep.V}
    (hx : x ∈ F.level U) : φ.hom x ∈ F'.level U :=
  F'.mem_level.2 fun u hu ↦ by rw [← Rep.hom_comm_apply φ, F.mem_level.1 hx u hu]

namespace NormalLayer

variable (L : NormalLayer G)

/-- **The map of layer coefficient modules induced by a map of coefficient modules**: an
equivariant map `A → A'` restricts to a map `A^V → A'^V` of top levels, equivariant for the Galois
group of the layer. Composing with `groupCohomology.map` or `groupCohomology.functor` makes a map
of formations act on the cohomology of the layer. -/
def repMap (φ : F.toRep ⟶ F'.toRep) : L.rep F ⟶ L.rep F' :=
  Rep.ofHom
    { toLinearMap := φ.hom.toLinearMap.restrict fun _ hx ↦ Formation.map_mem_level φ hx
      isIntertwining' := fun γ ↦ by
        induction γ using QuotientGroup.induction_on with
        | H u =>
          ext x
          exact Rep.hom_comm_apply φ (u : G) (x : F.toRep.V) }

/-- `repMap φ` applies `φ` to an element of the top level. -/
@[simp]
theorem repMap_hom_apply_coe (φ : F.toRep ⟶ F'.toRep) (x : F.level L.top) :
    (dsimp% only ((L.repMap φ).hom x : F'.toRep.V)) = φ.hom x :=
  (rfl)

/-- `repMap` is functorial: it carries a composite to the composite. -/
theorem repMap_comp (φ : F.toRep ⟶ F'.toRep) (ψ : F'.toRep ⟶ F''.toRep) :
    L.repMap (φ ≫ ψ) = L.repMap φ ≫ L.repMap ψ :=
  (rfl)

/-- `repMap` carries the identity to the identity. -/
@[simp]
theorem repMap_id : L.repMap (𝟙 F.toRep) = 𝟙 (L.rep F) :=
  (rfl)

/-- The maps of layer coefficient modules induced by an exact pair of coefficient maps compose to
zero. -/
theorem repMap_comp_eq_zero {φ : F.toRep ⟶ F'.toRep} {ψ : F'.toRep ⟶ F''.toRep}
    (hφψ : Function.Exact φ.hom ψ.hom) : L.repMap φ ≫ L.repMap ψ = 0 := by
  ext x
  exact hφψ.apply_apply_eq_zero x.1

/-- **A short exact sequence of coefficient modules stays short exact on a layer** `V ◁ U` once
every `V`-invariant element of the third module lifts to a `V`-invariant element of the second.
Injectivity and exactness in the middle pass to the top levels unconditionally; the lifting
hypothesis is exactly the surjectivity of `A'^V → A''^V`, which in general is obstructed by
`H¹(V, A)`. -/
theorem shortExact_repMap {φ : F.toRep ⟶ F'.toRep} {ψ : F'.toRep ⟶ F''.toRep}
    (hφ : Function.Injective φ.hom) (hφψ : Function.Exact φ.hom ψ.hom)
    (hψ : ∀ y ∈ F''.level L.top, ∃ x ∈ F'.level L.top, ψ.hom x = y) :
    (ShortComplex.mk (L.repMap φ) (L.repMap ψ) (L.repMap_comp_eq_zero hφψ)).ShortExact where
  exact := (forget₂ (Rep ℤ L.Gal) (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun (x : F'.level L.top) hx ↦ by
      -- An element of `A'^V` killed by `ψ` comes from `A`, and from `A^V` because `φ` is
      -- injective and equivariant.
      have hx' : ψ.hom (x : F'.toRep.V) = 0 := congrArg Subtype.val hx
      obtain ⟨a, ha⟩ := (hφψ (x : F'.toRep.V)).1 hx'
      have hmem : a ∈ F.level L.top := F.mem_level.2 fun v hv ↦ hφ <| by
        rw [Rep.hom_comm_apply φ, ha, F'.mem_level.1 x.2 v hv]
      exact ⟨⟨a, hmem⟩, Subtype.ext ha⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h ↦ Subtype.ext (hφ (congrArg Subtype.val h))
  epi_g := (Rep.epi_iff_surjective _).2 fun y ↦ by
    obtain ⟨x, hx, hxy⟩ := hψ y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end NormalLayer

end TauCeti.ClassFieldTheory
