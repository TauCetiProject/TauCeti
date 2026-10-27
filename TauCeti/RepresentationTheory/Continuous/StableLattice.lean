/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Lattice
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep

/-!
# Stable lattices for compact groups

Let `E` be a field with a valuative topology (for instance a nonarchimedean local field), with
valuation ring `𝒪[E]`, and let `V` be a finite-dimensional `E`-vector space with its module
topology. A representation `ρ` of a compact group `Γ` on `V` whose orbit maps `g ↦ ρ g x` are
continuous preserves a lattice: every lattice `L` is contained in a `Γ`-stable lattice. Indeed
`L` is open, so the elements `h` with `ρ h L ⊆ L` form a neighbourhood of `1`, and by compactness
the sum of the translates `ρ g L` is the finite sum over finitely many `g`. In particular every
jointly continuous representation of a compact group (`TauCeti.ContinuousRep`) has a stable
lattice, which is the starting point for integral models of `ℓ`-adic Galois representations.

Over a nonarchimedean local field this gives the classical criterion: a subgroup `K` of
`GL(V) = V ≃ₗ[E] V` stabilizes a lattice exactly when its closure is compact. The converse
direction uses that the stabilizer of a lattice is compact
(`Submodule.IsLattice.isCompact_stabilizer`).

## Main results

* `Representation.exists_le_stable_lattice`: a representation of a compact group with
  continuous orbit maps stabilizes a lattice containing any given lattice.
* `Representation.exists_stable_lattice`, `TauCeti.ContinuousRep.exists_stable_lattice`: such a
  representation, in particular a jointly continuous one, has a stable lattice.
* `Subgroup.isCompact_closure_iff_exists_stable_lattice`: a subgroup of `V ≃ₗ[E] V` has compact
  closure if and only if it stabilizes a lattice.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, paragraph after
  Proposition 2.6.
* K. A. Ribet, *Galois representations attached to eigenforms with Nebentypus*, §2.
-/

public section

open Module ValuativeRel Set Submodule
open scoped Pointwise

section ValuativeTopology

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V]

namespace Representation

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]

/-- **Stable lattices for compact groups.** A representation of a compact group whose orbit
maps are continuous stabilizes a lattice containing any given lattice `L`. -/
theorem exists_le_stable_lattice (ρ : Representation E Γ V)
    (hρ : ∀ x, Continuous fun g => ρ g x) (L : Submodule 𝒪[E] V) [IsLattice E L] :
    ∃ L' : Submodule 𝒪[E] V, L ≤ L' ∧ IsLattice E L' ∧ ∀ g, ∀ x ∈ L', ρ g x ∈ L' := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
  let r : Γ → V →ₗ[𝒪[E]] V := fun g => (ρ g).restrictScalars 𝒪[E]
  have hr (g h : Γ) : r (g * h) = (r g).comp (r h) := LinearMap.ext fun x => by simp [r]
  obtain ⟨s, hs⟩ := IsLattice.fg (A := E) (M := L)
  -- `ρ h` maps `L` into `ρ g L` for `h` in the open neighbourhood `W g` of `g`.
  let W : Γ → Set Γ := fun g => ⋂ v ∈ s, (fun h => ρ g⁻¹ (ρ h v)) ⁻¹' L
  have hWo (g : Γ) : IsOpen (W g) := isOpen_biInter_finset fun v _ =>
    (IsLattice.isOpen L).preimage ((IsModuleTopology.continuous_of_linearMap (ρ g⁻¹)).comp (hρ v))
  have hWm (g : Γ) : g ∈ W g := mem_iInter₂.mpr fun v hv => by
    simpa [← Module.End.mul_apply, ← map_mul] using hs ▸ subset_span hv
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover W hWo fun g _ => mem_iUnion.mpr ⟨g, hWm g⟩
  have hle (h : Γ) : L.map (r h) ≤ ⨆ g ∈ t, L.map (r g) := by
    obtain ⟨g, hg, hh⟩ := mem_iUnion₂.mp (ht (mem_univ h))
    have hL : L.map (r (g⁻¹ * h)) ≤ L := by
      have := (map_span_le (r (g⁻¹ * h)) s L).mpr fun v hv => by
        simpa [r] using mem_iInter₂.mp hh v hv
      rwa [hs] at this
    calc L.map (r h) = (L.map (r (g⁻¹ * h))).map (r g) := by
          rw [← map_comp, ← hr, mul_inv_cancel_left]
      _ ≤ L.map (r g) := map_mono hL
      _ ≤ ⨆ g ∈ t, L.map (r g) := le_iSup₂_of_le g hg le_rfl
  let L' := ⨆ h, L.map (r h)
  have hr1 : r 1 = LinearMap.id := LinearMap.ext fun x => by simp [r]
  have hLL' : L ≤ L' := le_iSup_of_le 1 (by rw [hr1, map_id])
  have hfg : L'.FG := by
    rw [show L' = ⨆ g ∈ t, L.map (r g) from
      le_antisymm (iSup_le hle) (iSup₂_le fun g _ => le_iSup_of_le g le_rfl)]
    exact fg_biSup t _ fun g _ => IsLattice.fg.map (r g)
  refine ⟨L', hLL', IsLattice.of_le_of_isLattice_of_fg E hLL' hfg, fun g x hx => ?_⟩
  have hL' : L' ≤ L'.comap (r g) := iSup_le fun h => by
    rw [← map_le_iff_le_comap, ← map_comp, ← hr]
    exact le_iSup_of_le (g * h) le_rfl
  exact hL' hx

/-- **A representation of a compact group with continuous orbit maps stabilizes a lattice.** -/
theorem exists_stable_lattice [FiniteDimensional E V] (ρ : Representation E Γ V)
    (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ L : Submodule 𝒪[E] V, IsLattice E L ∧ ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
  have := isLattice_span (R := 𝒪[E]) (finite_range (Module.finBasis E V))
    (Module.finBasis E V).span_eq
  obtain ⟨L, -, hL⟩ := ρ.exists_le_stable_lattice hρ (span 𝒪[E] (range (Module.finBasis E V)))
  exact ⟨L, hL⟩

end Representation

namespace TauCeti.ContinuousRep

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]

/-- **A jointly continuous representation of a compact group has a stable lattice.** -/
theorem exists_stable_lattice [FiniteDimensional E V] (ρ : ContinuousRep Γ E V) :
    ∃ L : Submodule 𝒪[E] V, IsLattice E L ∧ ∀ g, ∀ x ∈ L, ρ g x ∈ L :=
  ρ.toRepresentation.exists_stable_lattice ρ.continuous_orbit

end TauCeti.ContinuousRep

end ValuativeTopology

namespace Subgroup

variable {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]

/-- **A subgroup of `GL(V)` stabilizes a lattice if and only if its closure is compact.** Here
`V` is a finite-dimensional vector space over a nonarchimedean local field `E`, and `GL(V)` is
the group `V ≃ₗ[E] V` of linear automorphisms with its natural topology. -/
theorem isCompact_closure_iff_exists_stable_lattice (K : Subgroup (V ≃ₗ[E] V)) :
    IsCompact (_root_.closure (K : Set (V ≃ₗ[E] V))) ↔
      ∃ L : Submodule 𝒪[E] V, IsLattice E L ∧ ∀ k ∈ K, ∀ x ∈ L, k x ∈ L := by
  constructor
  · intro hK
    have : ContinuousAdd V := IsModuleTopology.toContinuousAdd E V
    let H := K.topologicalClosure
    have : CompactSpace H := isCompact_iff_compactSpace.mp (by simpa [H] using hK)
    let ρ : Representation E H V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      H.subtype
    have hρ (x : V) : Continuous fun g : H => ρ g x :=
      (IsModuleTopology.continuous_of_linearMap
        (LinearMap.applyₗ x : Module.End E V →ₗ[E] V)).comp
        (TauCeti.continuous_linearEquiv_toLinearMap.comp continuous_subtype_val)
    obtain ⟨L, hL, hρL⟩ := ρ.exists_stable_lattice hρ
    exact ⟨L, hL, fun k hk => hρL ⟨k, K.le_topologicalClosure hk⟩⟩
  · rintro ⟨L, hL, hKL⟩
    have hS := IsLattice.isCompact_stabilizer L
    have hKS : (K : Set (V ≃ₗ[E] V)) ⊆ MulAction.stabilizer (V ≃ₗ[E] V) (L : Set V) :=
      fun k hk => TauCeti.mem_stabilizer_set_iff_mapsTo.mpr
        ⟨fun x => hKL k hk x, fun x => hKL k⁻¹ (K.inv_mem hk) x⟩
    exact hS.of_isClosed_subset isClosed_closure (closure_minimal hKS hS.isClosed)

end Subgroup
