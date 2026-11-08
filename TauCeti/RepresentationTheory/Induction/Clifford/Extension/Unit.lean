/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Reconstruction
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basis
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Recovering multiplicities from Clifford reconstruction

For a simple normal-subgroup representation `A`, the map sending `m` to the
intertwiner `x ↦ m ⊗ x` identifies a multiplicity module with the intertwiner
space of its reconstructed representation. The tensor is balanced over the full
endomorphism division algebra, not just the ground field. Multiplicity modules
and inertia quotients may be infinite.

This is the ground-field-linear unit comparison needed to invert reconstruction.
It is canonical, although the proof uses a right-commutant basis. A nonzero vector
of `A` detects which coordinate endomorphisms vanish, so every intertwiner uses
only finitely many basis coordinates.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
* `Module.Basis.balancedTensorProductEquiv` supplies tensor coordinates.
-/

public noncomputable section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  {M : Type w} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "E" => BalancedTensorProduct k (End A) M V
local notation "ρ" => MonoidHom.comp (cliffordReconstructionRepresentation A s hs U)
  (Subgroup.inclusion (le_inertia A))

attribute [local instance] endModule

private local instance : IsScalarTower k (End A) V := (F).endModule_isScalarTower A

/-- The canonical multiplicity map sends `m` to the normal-subgroup intertwiner
`x ↦ m ⊗ x` in the reconstructed representation. -/
def cliffordReconstructionUnit : M →ₗ[k] Representation.IntertwiningMap (V).ρ ρ where
  toFun m :=
    { toLinearMap := BalancedTensorProduct.mk k (End A) m
      isIntertwining' := fun n => by
        ext x
        simp only [LinearMap.comp_apply, BalancedTensorProduct.mk_apply]
        symm
        -- The native tensor formula uses the FDRep carrier, rather than its Rep view.
        erw [MonoidHom.comp_apply, cliffordReconstructionRepresentation_inclusion_tmul]
        rw [FDRep.forget₂_ρ]
        rfl }
  map_add' m m' := by
    ext x
    simp [BalancedTensorProduct.mk_apply]
  map_smul' r m := by
    ext x
    simp [BalancedTensorProduct.mk_apply]

/-- The unit comparison evaluates to the pure balanced tensor. -/
@[simp]
theorem cliffordReconstructionUnit_apply (m : M) (x : V) :
    cliffordReconstructionUnit A s hs U m x =
      BalancedTensorProduct.tmul k (End A) (N := V) m x := by
  simp [cliffordReconstructionUnit, BalancedTensorProduct.mk_apply]

section Coordinates

variable {ι : Type*} (b : Module.Basis ι (End A)ᵐᵒᵖ M)

local notation "e" => b.balancedTensorProductEquiv (k := k) (N := V)

private theorem unit_coordinates_action (n : N) (z : E) :
    e (ρ n z) = Finsupp.mapRange ((V).ρ n) (map_zero _) (e z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht m x =>
    ext i
    have hn : ρ n (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
        BalancedTensorProduct.tmul k (End A) (N := V) m ((V).ρ n x) := by
      -- As in the unit construction, bridge the FDRep and Rep carrier views.
      erw [MonoidHom.comp_apply, cliffordReconstructionRepresentation_inclusion_tmul]
      rw [FDRep.forget₂_ρ]
      rfl
    rw [hn]
    simp only [Module.Basis.balancedTensorProductEquiv_tmul_apply, Finsupp.mapRange_apply]
    simp only [(F).endModule_smul, Functor.comp_map, Rep.forget₂_moduleCat_map,
      ModuleCat.hom_ofHom]
    exact (((R).map (unop (b.repr m i)).asHom).hom.isIntertwining _ _ n x)
  | ha x y hx hy =>
    ext i
    simpa only [map_add, Finsupp.mapRange_apply, Finsupp.add_apply] using
      congrArg (fun z => z i) (congrArg₂ (· + ·) hx hy)

private def unitCoordinate (f : Representation.IntertwiningMap (V).ρ ρ) (i : ι) : End A :=
  End.of (forget₂HomLinearEquiv A A ((Rep.homLinearEquiv V V).symm
    { toLinearMap := (Finsupp.lapply i).comp ((e).toLinearMap.comp f.toLinearMap)
      isIntertwining' := fun n => by
        ext x
        have h := congrArg (fun z => e z i) (f.isIntertwining _ _ n x)
        simpa only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
          unit_coordinates_action, Finsupp.mapRange_apply,
          Representation.IntertwiningMap.coe_toLinearMap] using h }))

private theorem unitCoordinate_apply (f : Representation.IntertwiningMap (V).ρ ρ)
    (i : ι) (x : V) :
    ((F).map (unitCoordinate A s hs U b f i).asHom).hom x = e (f x) i := by
  simp [unitCoordinate, Functor.comp_map, forget₂_map_forget₂HomLinearEquiv,
    Rep.homLinearEquiv]

include b in
private theorem unit_injective_of_basis :
    Function.Injective (cliffordReconstructionUnit A s hs U) := by
  intro m m' h
  apply b.repr.injective
  ext i
  apply unop_injective
  apply End.ext
  apply (R).map_injective
  ext x
  have hx := congrArg (fun f : Representation.IntertwiningMap (V).ρ ρ => e (f x) i) h
  simpa only [cliffordReconstructionUnit_apply,
    Module.Basis.balancedTensorProductEquiv_tmul_apply, (F).endModule_smul,
    Functor.comp_map, Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom] using hx

variable [Simple A]

include b in
private theorem unit_surjective_of_basis :
    Function.Surjective (cliffordReconstructionUnit A s hs U) := by
  classical
  have : Nontrivial V := by
    have h := isIrreducible_of_simple A
    rw [← FDRep.forget₂_ρ] at h
    exact h.nontrivial
  intro f
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let t := (e (f x)).support
  let d := unitCoordinate A s hs U b f
  have hd (i : ι) (hi : i ∉ t) : d i = 0 := by
    have hz : (d i) • x = 0 := by
      rw [(F).endModule_smul, unitCoordinate_apply]
      exact Finsupp.notMem_support_iff.mp hi
    exact (smul_eq_zero.mp hz).resolve_right hx
  let m := ∑ i ∈ t, op (d i) • b i
  have hm (i : ι) : b.repr m i = op (d i) := by
    simp only [m, map_sum, map_smul, Module.Basis.repr_self]
    by_cases hi : i ∈ t
    · simp [Finsupp.single_apply, hi]
    · simp [Finsupp.single_apply, hi, hd i hi]
  refine ⟨m, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  apply (e).injective
  ext i
  simp only [Representation.IntertwiningMap.coe_toLinearMap]
  rw [cliffordReconstructionUnit_apply,
    Module.Basis.balancedTensorProductEquiv_tmul_apply, hm, unop_op,
    (F).endModule_smul, unitCoordinate_apply]

end Coordinates

variable [Simple A]

/-- Reconstructing from a multiplicity module and then taking normal-subgroup
multiplicities recovers the original ground-field vector space, even for infinite modules. -/
theorem cliffordReconstructionUnit_bijective :
    Function.Bijective (cliffordReconstructionUnit A s hs U) :=
  ⟨unit_injective_of_basis A s hs U (Module.Free.chooseBasis _ _),
    unit_surjective_of_basis A s hs U (Module.Free.chooseBasis _ _)⟩

/-- The canonical ground-field-linear unit comparison for Clifford reconstruction. -/
def cliffordReconstructionUnitEquiv :
    M ≃ₗ[k] Representation.IntertwiningMap (V).ρ ρ :=
  LinearEquiv.ofBijective (cliffordReconstructionUnit A s hs U)
    (cliffordReconstructionUnit_bijective A s hs U)

/-- The unit equivalence sends a multiplicity vector to tensoring with that vector. -/
@[simp]
theorem cliffordReconstructionUnitEquiv_apply (m : M) :
    cliffordReconstructionUnitEquiv A s hs U m =
      cliffordReconstructionUnit A s hs U m := (rfl)

/-- The inverse unit equivalence recovers a vector from its tensoring intertwiner. -/
@[simp]
theorem cliffordReconstructionUnitEquiv_symm_unit (m : M) :
    (cliffordReconstructionUnitEquiv A s hs U).symm
      (cliffordReconstructionUnit A s hs U m) = m :=
  (cliffordReconstructionUnitEquiv A s hs U).symm_apply_apply m

end FDRep
