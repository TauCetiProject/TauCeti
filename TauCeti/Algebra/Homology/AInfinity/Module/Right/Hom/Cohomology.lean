/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Components

/-!
# Cohomology and quasi-isomorphisms of right A-infinity modules

The linear part of a morphism of right `A∞` modules commutes with the unary operations.  It
therefore sends cycles to cycles and boundaries to boundaries, inducing a linear map on module
cohomology.  These induced maps preserve identities and composition.

A module morphism is a quasi-isomorphism when its induced map on cohomology is bijective.  The
functorial laws immediately give identity, composition, and both two-out-of-three implications.
This is the invariant inverted in the derived category of `A∞` modules.

## Main definitions

* `TauCeti.AInfinityRightModuleHom.cohomologyMap`: the map induced by the linear part.
* `TauCeti.AInfinityRightModuleHom.IsQuasiIso`: bijectivity of the induced cohomology map.
* `TauCeti.AInfinityRightModuleHom.IsQuasiIso.cohomologyLinearEquiv`: the resulting linear
  equivalence on cohomology.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4.1--4.2.
-/

public section

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-- The linear part of a module morphism commutes with the unary module differentials. -/
theorem differential_comp_linearPart (f : AInfinityRightModuleHom MM NN) :
    NN.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ MM.differential := by
  ext x
  simp only [LinearMap.comp_apply, AInfinityRightModule.differential_apply]
  exact (f.linearPart_m_one x _ _).symm

/-- The linear part of a module morphism carries cycles to cycles. -/
theorem linearPart_mem_cycles (f : AInfinityRightModuleHom MM NN) {x : M}
    (hx : x ∈ MM.cycles) : f.linearPart x ∈ NN.cycles := by
  rw [AInfinityRightModule.mem_cycles] at hx ⊢
  calc
    NN.differential (f.linearPart x) = f.linearPart (MM.differential x) :=
      LinearMap.congr_fun f.differential_comp_linearPart x
    _ = 0 := by rw [hx, map_zero]

/-- The linear part of a module morphism carries boundaries to boundaries. -/
theorem linearPart_mem_boundaries (f : AInfinityRightModuleHom MM NN) {x : M}
    (hx : x ∈ MM.boundaries) : f.linearPart x ∈ NN.boundaries := by
  rw [AInfinityRightModule.mem_boundaries] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨f.linearPart y, LinearMap.congr_fun f.differential_comp_linearPart y⟩

/-- The linear part of a module morphism, restricted to unary cycles. -/
noncomputable def cyclesMap (f : AInfinityRightModuleHom MM NN) : MM.cycles →ₗ[R] NN.cycles :=
  f.linearPart.restrict fun _ hx ↦ f.linearPart_mem_cycles hx

/-- The underlying element of the image of a cycle is its image under the linear part. -/
@[simp]
theorem coe_cyclesMap (f : AInfinityRightModuleHom MM NN) (x : MM.cycles) :
    (f.cyclesMap x : N) = f.linearPart x := (rfl)

private theorem boundariesInCycles_le_comap (f : AInfinityRightModuleHom MM NN) :
    MM.boundariesInCycles ≤ NN.boundariesInCycles.comap f.cyclesMap := by
  intro x hx
  rw [Submodule.mem_comap, AInfinityRightModule.mem_boundariesInCycles, coe_cyclesMap]
  exact f.linearPart_mem_boundaries ((MM.mem_boundariesInCycles).1 hx)

/-- The linear map on cohomology induced by the linear part of a module morphism. -/
noncomputable def cohomologyMap (f : AInfinityRightModuleHom MM NN) :
    MM.Cohomology →ₗ[R] NN.Cohomology :=
  Submodule.mapQ MM.boundariesInCycles NN.boundariesInCycles f.cyclesMap
    f.boundariesInCycles_le_comap

/-- The induced map sends the class of a cycle to the class of its image under the linear part. -/
@[simp]
theorem cohomologyMap_cohomologyClass (f : AInfinityRightModuleHom MM NN) {x : M}
    (hx : x ∈ MM.cycles) :
    f.cohomologyMap (MM.cohomologyClass hx) =
      NN.cohomologyClass (f.linearPart_mem_cycles hx) := by
  rw [AInfinityRightModule.cohomologyClass_eq_mk, cohomologyMap, Submodule.mapQ_apply,
    AInfinityRightModule.cohomologyClass_eq_mk]
  rfl

/-- Passage to module cohomology sends the identity morphism to the identity map. -/
@[simp]
theorem cohomologyMap_id (MM : AInfinityRightModule AA M) :
    (AInfinityRightModuleHom.id MM).cohomologyMap = LinearMap.id := by
  apply LinearMap.ext
  intro c
  obtain ⟨x, hx, rfl⟩ := MM.exists_cohomologyClass_eq c
  rw [cohomologyMap_cohomologyClass, LinearMap.id_apply]
  congr 1
  simp only [linearPart_id, LinearMap.id_apply]

/-- Passage to module cohomology preserves composition. -/
@[simp]
theorem cohomologyMap_comp (g : AInfinityRightModuleHom NN PP)
    (f : AInfinityRightModuleHom MM NN) :
    (g.comp f).cohomologyMap = g.cohomologyMap ∘ₗ f.cohomologyMap := by
  apply LinearMap.ext
  intro c
  obtain ⟨x, hx, rfl⟩ := MM.exists_cohomologyClass_eq c
  rw [cohomologyMap_cohomologyClass, LinearMap.comp_apply, cohomologyMap_cohomologyClass,
    cohomologyMap_cohomologyClass]
  congr 1
  simp only [linearPart_comp, LinearMap.comp_apply]

/-- A morphism of right `A∞` modules is a quasi-isomorphism when its linear part induces a
bijection on cohomology. -/
def IsQuasiIso (f : AInfinityRightModuleHom MM NN) : Prop :=
  Function.Bijective f.cohomologyMap

/-- A module morphism is a quasi-isomorphism exactly when its induced cohomology map is
bijective. -/
theorem isQuasiIso_def (f : AInfinityRightModuleHom MM NN) :
    f.IsQuasiIso ↔ Function.Bijective f.cohomologyMap := Iff.rfl

/-- The identity morphism of a right `A∞` module is a quasi-isomorphism. -/
@[simp]
theorem isQuasiIso_id (MM : AInfinityRightModule AA M) :
    (AInfinityRightModuleHom.id MM).IsQuasiIso := by
  rw [IsQuasiIso, cohomologyMap_id]
  exact Function.bijective_id

/-- Quasi-isomorphisms of right `A∞` modules are closed under composition. -/
theorem IsQuasiIso.comp {g : AInfinityRightModuleHom NN PP}
    {f : AInfinityRightModuleHom MM NN} (hg : g.IsQuasiIso) (hf : f.IsQuasiIso) :
    (g.comp f).IsQuasiIso := by
  rw [isQuasiIso_def] at hg hf ⊢
  rw [cohomologyMap_comp]
  rw [LinearMap.coe_comp]
  exact Function.Bijective.comp hg hf

/-- Two out of three: if `f` and `g ∘ f` are quasi-isomorphisms, then so is `g`. -/
theorem IsQuasiIso.of_precomp {g : AInfinityRightModuleHom NN PP}
    {f : AInfinityRightModuleHom MM NN} (hf : f.IsQuasiIso) (hgf : (g.comp f).IsQuasiIso) :
    g.IsQuasiIso := by
  rw [isQuasiIso_def] at hf hgf ⊢
  rw [cohomologyMap_comp] at hgf
  rw [LinearMap.coe_comp] at hgf
  exact (Function.Bijective.of_comp_iff _ hf).1 hgf

/-- Two out of three: if `g` and `g ∘ f` are quasi-isomorphisms, then so is `f`. -/
theorem IsQuasiIso.of_postcomp {g : AInfinityRightModuleHom NN PP}
    {f : AInfinityRightModuleHom MM NN} (hg : g.IsQuasiIso) (hgf : (g.comp f).IsQuasiIso) :
    f.IsQuasiIso := by
  rw [isQuasiIso_def] at hg hgf ⊢
  rw [cohomologyMap_comp] at hgf
  rw [LinearMap.coe_comp] at hgf
  exact (Function.Bijective.of_comp_iff' hg _).1 hgf

namespace IsQuasiIso

/-- The map induced on cohomology by a quasi-isomorphism, as a linear equivalence. -/
noncomputable def cohomologyLinearEquiv {f : AInfinityRightModuleHom MM NN}
    (hf : f.IsQuasiIso) : MM.Cohomology ≃ₗ[R] NN.Cohomology :=
  LinearEquiv.ofBijective f.cohomologyMap ((isQuasiIso_def f).1 hf)

/-- The cohomology equivalence of a quasi-isomorphism agrees with its induced map. -/
@[simp]
theorem cohomologyLinearEquiv_apply {f : AInfinityRightModuleHom MM NN}
    (hf : f.IsQuasiIso) (c : MM.Cohomology) :
    hf.cohomologyLinearEquiv c = f.cohomologyMap c :=
  LinearEquiv.ofBijective_apply _ c

end IsQuasiIso

end AInfinityRightModuleHom

end TauCeti
