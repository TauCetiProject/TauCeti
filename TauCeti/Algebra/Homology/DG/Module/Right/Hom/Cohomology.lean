/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.HomComplex

/-!
# Functorial cohomology of differential graded right modules

A morphism of DG right modules over `A` induces a right `H(A)`-linear map on cohomology.
The map is computed on cycle representatives and respects identities, composition, and addition.
Consequently cohomology defines an additive functor from DG right modules to right modules over
`H(A)`. This is the cohomology invariant used when inverting quasi-isomorphisms of DG modules.

Homotopic DG module maps induce the same map on cohomology. Here a homotopy is an ordinary
right-module linear map of degree minus one with `f - g = d s + s d`, in agreement with the
existing right-module Hom complex. The equality criterion on cycles also applies without choosing
such a homotopy.

The functor exposes its object construction so its values have the advertised cohomology
carriers.

The construction uses Mathlib's `Submodule.mapQ` for descent to the quotient and the existing
right `H(A)`-action on module cohomology.

## References

* B. Keller, *Deriving DG categories*, Section 2.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  {hM : IsDGRightModule h ℳ dM} {hN : IsDGRightModule h 𝒩 dN}
  {hP : IsDGRightModule h ℳP dP}

/-- A DG module map restricts to a right-linear map over the algebra of cycles. -/
def cyclesMap (f : DGRightModuleHom hM hN) : hM.cycles →ₗ[(h.cycles)ᵐᵒᵖ] hN.cycles where
  toFun z := ⟨f z, by simp [hN.mem_cycles, f.map_d, hM.mem_cycles.mp z.2]⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' a z := Subtype.ext (f.toLinearMap.map_smul (op (a.unop : A)) z)

@[simp]
theorem cyclesMap_apply_coe (f : DGRightModuleHom hM hN) (z : hM.cycles) :
    (f.cyclesMap z : N) = f (z : M) := (rfl)

/-- Restriction to cycles preserves identity morphisms. -/
@[simp]
theorem cyclesMap_id : (DGRightModuleHom.id hM).cyclesMap = LinearMap.id := by
  ext z
  simp only [cyclesMap_apply_coe, LinearMap.id_apply, id_apply]

/-- Restriction to cycles preserves composition. -/
@[simp]
theorem cyclesMap_comp (g : DGRightModuleHom hN hP) (f : DGRightModuleHom hM hN) :
    (g.comp f).cyclesMap = g.cyclesMap.comp f.cyclesMap := by
  ext z
  simp only [cyclesMap_apply_coe, LinearMap.comp_apply, comp_apply]

/-- Restriction to cycles preserves addition. -/
@[simp]
theorem cyclesMap_add (f g : DGRightModuleHom hM hN) :
    (f + g).cyclesMap = f.cyclesMap + g.cyclesMap := by
  ext z
  simp only [cyclesMap_apply_coe, LinearMap.add_apply, Submodule.coe_add, add_apply]

/-- A DG module map sends boundaries to boundaries. -/
theorem cyclesMap_mem_boundaries (f : DGRightModuleHom hM hN) {z : hM.cycles}
    (hz : z ∈ hM.boundaries) : f.cyclesMap z ∈ hN.boundaries := by
  obtain ⟨x, hx⟩ := hM.mem_boundaries.mp hz
  exact hN.mem_boundaries.mpr ⟨f x, by simp [hx, cyclesMap_apply_coe]⟩

/-- The map on cohomology, initially linear over the opposite algebra of cycles. -/
private noncomputable def cohomologyCyclesMap (f : DGRightModuleHom hM hN) :
    hM.Cohomology →ₗ[(h.cycles)ᵐᵒᵖ] hN.Cohomology :=
  hM.boundaries.mapQ hN.boundaries f.cyclesMap (fun _ hz ↦ f.cyclesMap_mem_boundaries hz)

/-- A DG module morphism induces a right-linear map over the cohomology algebra. -/
noncomputable def cohomologyMap (f : DGRightModuleHom hM hN) :
    hM.Cohomology →ₗ[(h.Cohomology)ᵐᵒᵖ] hN.Cohomology where
  toFun := f.cohomologyCyclesMap
  map_add' := map_add _
  map_smul' a x := by
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective a.unop
    simp only [RingHom.id_apply]
    rw [← op_unop a, ← hz, hM.op_quotientMk_smul, hN.op_quotientMk_smul]
    exact f.cohomologyCyclesMap.map_smul (op z) x

/-- Cohomology maps send the class of a cycle to the class of its image. -/
@[simp]
theorem cohomologyMap_mk (f : DGRightModuleHom hM hN) (z : hM.cycles) :
    f.cohomologyMap (Submodule.Quotient.mk z) = Submodule.Quotient.mk (f.cyclesMap z) :=
  (rfl)

/-- Taking cohomology preserves the identity module map. -/
@[simp]
theorem cohomologyMap_id : (DGRightModuleHom.id hM).cohomologyMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [cohomologyMap_mk, LinearMap.id_apply]
  simp only [cyclesMap_id, LinearMap.id_apply]

/-- Taking cohomology preserves composition of module maps. -/
@[simp]
theorem cohomologyMap_comp (g : DGRightModuleHom hN hP) (f : DGRightModuleHom hM hN) :
    (g.comp f).cohomologyMap = g.cohomologyMap.comp f.cohomologyMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [LinearMap.comp_apply, cohomologyMap_mk, cyclesMap_comp]

/-- Taking cohomology preserves addition of module maps. -/
@[simp]
theorem cohomologyMap_add (f g : DGRightModuleHom hM hN) :
    (f + g).cohomologyMap = f.cohomologyMap + g.cohomologyMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [LinearMap.add_apply, cohomologyMap_mk, cyclesMap_add,
    Submodule.Quotient.mk_add]

/-- Two DG module maps induce the same cohomology map exactly when their difference sends
all cycles to boundaries. -/
@[simp]
theorem cohomologyMap_eq_iff (f g : DGRightModuleHom hM hN) :
    f.cohomologyMap = g.cohomologyMap ↔
      ∀ z : hM.cycles, f (z : M) - g (z : M) ∈ LinearMap.range dN := by
  constructor
  · intro hfg z
    have hz := LinearMap.congr_fun hfg (Submodule.Quotient.mk z)
    rw [cohomologyMap_mk, cohomologyMap_mk, Submodule.Quotient.eq] at hz
    exact hN.mem_boundaries.mp hz
  · intro hfg
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [cohomologyMap_mk, cohomologyMap_mk, Submodule.Quotient.eq]
    exact hN.mem_boundaries.mpr (hfg z)

/-- Homotopic DG module maps induce equal right `H(A)`-linear maps on cohomology. -/
theorem cohomologyMap_eq_of_homotopy (f g : DGRightModuleHom hM hN)
    (s : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := 𝒩) (-1))
    (hs : ∀ x : M, f x - g x = dN (s.1 x) + s.1 (dM x)) :
    f.cohomologyMap = g.cohomologyMap := by
  apply (cohomologyMap_eq_iff f g).mpr
  intro z
  refine ⟨s.1 z, ?_⟩
  simp [hs, hM.mem_cycles.mp z.2]

end DGRightModuleHom

namespace DGRightModuleCat

/-- Cohomology as a functor to right modules over the cohomology algebra. -/
@[expose]
noncomputable def cohomologyFunctor :
    DGRightModuleCat.{uR, uA, uM} h ⥤ ModuleCat.{uM} (h.Cohomology)ᵐᵒᵖ where
  obj M := ModuleCat.of _ M.isDGRightModule.Cohomology
  map f := ModuleCat.ofHom f.cohomologyMap
  map_id M := by
    apply ModuleCat.hom_ext
    exact DGRightModuleHom.cohomologyMap_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact DGRightModuleHom.cohomologyMap_comp g f

/-- The cohomology functor takes a DG module to its cohomology right module. -/
@[simp]
theorem cohomologyFunctor_obj (M : DGRightModuleCat.{uR, uA, uM} h) :
    (cohomologyFunctor (h := h)).obj M = ModuleCat.of _ M.isDGRightModule.Cohomology :=
  (rfl)

@[simp]
theorem cohomologyFunctor_map_hom {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) :
    ((cohomologyFunctor (h := h)).map f).hom = f.cohomologyMap := (rfl)

/-- Cohomology of DG right modules preserves addition of morphisms. -/
instance : (cohomologyFunctor.{uR, uA, uM} (h := h)).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    exact DGRightModuleHom.cohomologyMap_add f g

end DGRightModuleCat

end TauCeti
