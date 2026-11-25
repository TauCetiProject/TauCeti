/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.RepresentationTheory.Admissible
public import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# Isotypic components of a representation

For representations `ρ` on `V` and `σ` on `W` of a monoid `G`, the `σ`-isotypic component `V(σ)`
of `ρ` is the sum of the images of the `G`-equivariant maps from `σ` to `ρ`. It is stable under
`G`. For irreducible `σ` it is Mathlib's `isotypicComponent` of the simple `k[G]`-module
`σ.asModule` in `ρ.asModule`, and evaluating `Hom_G(σ, ρ)` at a nonzero vector of `W` embeds it
into `V(σ)`. This bounds the multiplicity of `σ` in `ρ` by the dimension of `V(σ)`, so a
representation with finite-dimensional isotypic components has finite multiplicities. For a
`(𝔤, K)`-module `M` (`TauCeti/RepresentationTheory/GKModule/Basic.lean`), the isotypic components
of `M.ρ` are `K`-stable but not `𝔤`-stable in general, since `𝔤` moves `K`-types.

## Main definitions

* `Representation.isotypicComponent ρ σ`: the `σ`-isotypic component of `ρ`.
* `Representation.isotypicComponentSubrep ρ σ`: the isotypic component as a subrepresentation.
* `Representation.evalIntertwiningMap ρ σ w`: evaluation of `Hom_G(σ, ρ)` at `w`, with values in
  the isotypic component.

## Main statements

* `Representation.mem_isotypicComponent_iff`: for irreducible `σ`, the isotypic component is
  Mathlib's `isotypicComponent` of the simple `k[G]`-module `σ.asModule`.
* `Representation.evalIntertwiningMap_injective`: for irreducible `σ` and `w ≠ 0`, evaluation at
  `w` embeds `Hom_G(σ, ρ)` into the isotypic component `V(σ)`.
* `Representation.multiplicity_le_rank_isotypicComponent`: for irreducible `σ`, the multiplicity
  of `σ` is at most the dimension of the isotypic component.
* `Representation.hasFiniteMultiplicities_of_finiteDimensional_isotypicComponent`: a
  representation whose isotypic components are finite-dimensional has finite multiplicities.

## References

* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), §3.3.
-/

public section

namespace Representation

variable {k G V W : Type*} [Monoid G]

section CommSemiring

variable [CommSemiring k] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k G W)

/-- The **`σ`-isotypic component** `V(σ)` of a representation `ρ`: the sum of the images of the
`G`-equivariant linear maps from `σ` to `ρ`. For irreducible `σ` it is the sum of the
subrepresentations isomorphic to `σ` (`Representation.mem_isotypicComponent_iff`). It is stable
under `G` (`Representation.isotypicComponentSubrep`). -/
def isotypicComponent : Submodule k V :=
  ⨆ f : IntertwiningMap σ ρ, LinearMap.range f.toLinearMap

/-- The isotypic component is the supremum of the ranges of the `G`-equivariant maps from `σ`. -/
theorem isotypicComponent_def :
    ρ.isotypicComponent σ = ⨆ f : IntertwiningMap σ ρ, LinearMap.range f.toLinearMap :=
  (rfl)

/-- The isotypic component is the least submodule containing the ranges of all `G`-equivariant
maps from `σ`. -/
theorem isotypicComponent_le_iff {P : Submodule k V} :
    ρ.isotypicComponent σ ≤ P ↔ ∀ f : IntertwiningMap σ ρ, LinearMap.range f.toLinearMap ≤ P := by
  rw [isotypicComponent_def, iSup_le_iff]

variable {ρ σ}

theorem range_le_isotypicComponent (f : IntertwiningMap σ ρ) :
    LinearMap.range f.toLinearMap ≤ ρ.isotypicComponent σ :=
  (ρ.isotypicComponent_le_iff σ).1 le_rfl f

theorem apply_mem_isotypicComponent (f : IntertwiningMap σ ρ) (w : W) :
    f w ∈ ρ.isotypicComponent σ :=
  range_le_isotypicComponent f ⟨w, rfl⟩

/-- The isotypic component is stable under `G`. -/
theorem apply_mem_isotypicComponent_of_mem (g : G) {v : V} (hv : v ∈ ρ.isotypicComponent σ) :
    ρ g v ∈ ρ.isotypicComponent σ := by
  refine Submodule.iSup_induction _ (motive := fun v ↦ ρ g v ∈ ρ.isotypicComponent σ) hv ?_ ?_ ?_
  · rintro f _ ⟨w, rfl⟩
    rw [IntertwiningMap.toLinearMap_apply, ← f.isIntertwining]
    exact apply_mem_isotypicComponent f _
  · simp
  · intro v v' hv hv'
    simpa using add_mem hv hv'

variable (ρ σ)

/-- The isotypic component as a subrepresentation. -/
def isotypicComponentSubrep : Subrepresentation ρ where
  toSubmodule := ρ.isotypicComponent σ
  apply_mem_toSubmodule g _ hv := apply_mem_isotypicComponent_of_mem g hv

@[simp]
theorem mem_isotypicComponentSubrep {v : V} :
    v ∈ ρ.isotypicComponentSubrep σ ↔ v ∈ ρ.isotypicComponent σ :=
  Iff.rfl

/-- Evaluation of `G`-equivariant maps `σ → ρ` at a vector `w`, which lands in the isotypic
component `V(σ)`. -/
def evalIntertwiningMap (w : W) : IntertwiningMap σ ρ →ₗ[k] ρ.isotypicComponent σ where
  toFun f := ⟨f w, apply_mem_isotypicComponent f w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalIntertwiningMap_apply_coe (w : W) (f : IntertwiningMap σ ρ) :
    (ρ.evalIntertwiningMap σ w f : V) = f w :=
  (rfl)

end CommSemiring

section Field

variable [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

open scoped MonoidAlgebra in
/-- For irreducible `σ`, the isotypic component is Mathlib's `isotypicComponent` of the simple
`k[G]`-module `σ.asModule` in `ρ.asModule`, read on `V` through `Representation.asModuleEquiv`. -/
theorem mem_isotypicComponent_iff [σ.IsIrreducible] {v : V} :
    v ∈ ρ.isotypicComponent σ ↔
      ρ.asModuleEquiv.symm v ∈ _root_.isotypicComponent k[G] ρ.asModule σ.asModule := by
  constructor
  · intro hv
    refine Submodule.iSup_induction _
      (motive := fun v ↦ ρ.asModuleEquiv.symm v ∈ _root_.isotypicComponent k[G] _ _) hv ?_ ?_ ?_
    · rintro f _ ⟨w, rfl⟩
      exact (IntertwiningMap.equivLinearMapAsModule σ ρ f).apply_mem_isotypicComponent
        (σ.asModuleEquiv.symm w)
    · simp
    · intro v v' hv hv'
      simpa using add_mem hv hv'
  · intro hv
    rw [_root_.isotypicComponent, sSup_eq_iSup'] at hv
    rw [← ρ.asModuleEquiv.apply_symm_apply v]
    refine Submodule.iSup_induction _
      (motive := fun x ↦ ρ.asModuleEquiv x ∈ ρ.isotypicComponent σ) hv ?_ ?_ ?_
    · rintro ⟨m, ⟨e⟩⟩ x hx
      let f := (IntertwiningMap.equivLinearMapAsModule σ ρ).symm (m.subtype ∘ₗ e.symm.toLinearMap)
      have : ρ.asModuleEquiv x = f (σ.asModuleEquiv (e ⟨x, hx⟩)) := by
        -- Mathlib has no apply lemmas for `IntertwiningMap.equivLinearMapAsModule`, whose maps
        -- have the same underlying functions on the type synonyms `asModule`, nor for
        -- `Representation.asModuleEquiv`, which is the identity; so `f` is unfolded by `change`.
        change _ = ρ.asModuleEquiv (m.subtype (e.symm (e ⟨x, hx⟩)))
        rw [LinearEquiv.symm_apply_apply]
        rfl
      rw [this]
      exact apply_mem_isotypicComponent f _
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy

/-- For irreducible `σ`, evaluation at a nonzero vector is injective on `Hom_G(σ, ρ)`: a nonzero
equivariant map from an irreducible representation is injective. -/
theorem evalIntertwiningMap_injective [σ.IsIrreducible] {w : W} (hw : w ≠ 0) :
    Function.Injective (ρ.evalIntertwiningMap σ w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  rcases IsIrreducible.injective_or_eq_zero f with hinj | h0
  · exact absurd (hinj (by simpa using congrArg Subtype.val hf)) hw
  · exact h0

/-- For irreducible `σ`, a finite-dimensional isotypic component `V(σ)` makes `Hom_G(σ, ρ)`
finite-dimensional. -/
theorem finiteDimensional_intertwiningMap_of_finiteDimensional_isotypicComponent
    [σ.IsIrreducible] [FiniteDimensional k (ρ.isotypicComponent σ)] :
    FiniteDimensional k (IntertwiningMap σ ρ) := by
  have := Representation.IsIrreducible.nontrivial (ρ := σ) inferInstance
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact Module.Finite.of_injective _ (evalIntertwiningMap_injective (ρ := ρ) hw)

/-- For irreducible `σ`, the multiplicity of `σ` in `ρ` is at most the dimension of the isotypic
component. -/
theorem multiplicity_le_rank_isotypicComponent [σ.IsIrreducible] :
    ρ.multiplicity σ ≤ (Module.rank k (ρ.isotypicComponent σ)).toENat := by
  have := Representation.IsIrreducible.nontrivial (ρ := σ) inferInstance
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h := OrderHomClass.mono Cardinal.toENat
    (LinearMap.lift_rank_le_of_injective _ (evalIntertwiningMap_injective (ρ := ρ) (σ := σ) hw))
  rwa [Cardinal.toENat_lift, Cardinal.toENat_lift, ← multiplicity_def] at h

/-- A representation whose isotypic components are finite-dimensional has finite
multiplicities. -/
theorem hasFiniteMultiplicities_of_finiteDimensional_isotypicComponent
    (h : ∀ U : Subrepresentation ρ, U.toRepresentation.IsIrreducible →
      FiniteDimensional k (ρ.isotypicComponent U.toRepresentation)) :
    ρ.HasFiniteMultiplicities :=
  ρ.hasFiniteMultiplicities_iff.2 fun U hU ↦
    have := h U hU
    finiteDimensional_intertwiningMap_of_finiteDimensional_isotypicComponent
      (σ := U.toRepresentation)

end Field

end Representation
