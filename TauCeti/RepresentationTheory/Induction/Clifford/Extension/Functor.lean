/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Reconstruction

/-!
# Functorial Clifford reconstruction

A map of opposite-coefficient, inverse-factor Clifford crossed-product modules induces
an inertia intertwiner on balanced tensors by `m ⊗ x ↦ f(m) ⊗ x`. This makes
reconstruction a ground-field-linear functor from all modules over the multiplicity
algebra to representations of the inertia group. Neither the inertia quotient nor the
multiplicity module needs to be finite, and the full commutant is retained.

The unbundled map also accepts coefficient-linear maps intertwining the semilinear
operators. Its equivariance uses the kernel and section decomposition of the canonical
Clifford extension. This is the morphism construction for the isotypic correspondence;
no essential-surjectivity or inverse-functor assertion is made here. The object assignment
uses `FDRep.cliffordReconstructionRepresentation`; morphisms use `BalancedTensorProduct.map`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension
open scoped ModuleCat.Algebra

universe u v w w'

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)

local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "C" => cliffordCrossedSystem A s hs
local notation "B" => CrossedSystem.Algebra (CrossedSystem.opInv (C))

attribute [local instance] endModule

section Maps

variable {M : Type w} {M' : Type w'}
  [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module (End A)ᵐᵒᵖ M']
  [IsScalarTower k (End A)ᵐᵒᵖ M']
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)
  (U' : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M')
  (f : M →ₗ[k] M')
  (hd : ∀ (d : (End A)ᵐᵒᵖ) m, f (d • m) = d • f m)
  (hq : ∀ q m, f (U.operator q m) = U'.operator q (f m))

include hd hq in
private theorem reconstructionMultiplicity_naturality (c : Carrier A) (m : M) :
    f (cliffordReconstructionMultiplicityRepresentation A s hs U c m) =
      cliffordReconstructionMultiplicityRepresentation A s hs U' c (f m) := by
  obtain ⟨d, hc⟩ := s.exists_eq_inl_mul_section c
  rw [hc]
  simp only [groupExtension_inl, map_mul, mul_apply_eq_comp,
    cliffordReconstructionMultiplicityRepresentation_section,
    cliffordReconstructionMultiplicityRepresentation_inl]
  rw [hd, hq]

/-- A coefficient-linear map intertwining the semilinear operators reconstructs to an
inertia intertwiner, acting on the multiplicity factor of the balanced tensor. -/
noncomputable def cliffordReconstructionMap :
    Representation.IntertwiningMap (cliffordReconstructionRepresentation A s hs U)
      (cliffordReconstructionRepresentation A s hs U') where
  toLinearMap := BalancedTensorProduct.map f LinearMap.id (fun d m => hd (op d) m)
    (fun _ _ => rfl)
  isIntertwining' t := by
    obtain ⟨p, rfl⟩ := projection_surjective A t
    apply BalancedTensorProduct.hom_ext
    intro m x
    simp only [LinearMap.comp_apply, BalancedTensorProduct.map_tmul,
      cliffordReconstructionRepresentation_projection_tmul, LinearMap.id_apply]
    erw [BalancedTensorProduct.map_tmul]
    -- The projection formula unfolds the quotient carrier of the Clifford extension;
    -- `erw` transports its named naturality equation across that carrier view.
    erw [reconstructionMultiplicity_naturality A s hs U U' f hd hq]
    rfl

/-- The underlying function of reconstruction is the balanced-tensor map on the
multiplicity factor. The native tensor-map lemmas compute its values. -/
@[simp]
theorem coe_cliffordReconstructionMap :
    ⇑(cliffordReconstructionMap A s hs U U' f hd hq) =
      ⇑(BalancedTensorProduct.map f (LinearMap.id : V →ₗ[k] V)
        (fun d m => hd (op d) m) (fun _ _ => rfl)) := (rfl)

end Maps

/-- The right-commutant action on a multiplicity-algebra module, obtained by restriction
along the noncentral coefficient inclusion. Install it locally when using tensor coordinates. -/
noncomputable abbrev cliffordReconstructionCoefficients (M : ModuleCat.{w} B) :
    Module (End A)ᵐᵒᵖ M :=
  Module.compHom M (CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs).opInv).toRingHom

attribute [local instance] cliffordReconstructionCoefficients

/-- Restricting the coefficients acts by their inclusion in the multiplicity algebra. -/
theorem cliffordReconstructionCoefficients_smul (M : ModuleCat.{w} B)
    (d : (End A)ᵐᵒᵖ) (m : M) :
    d • m = CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs).opInv d • m := rfl

/-- The restricted commutant action is compatible with the module's ground-field action. -/
theorem cliffordReconstructionCoefficientTower (M : ModuleCat.{w} B) :
    IsScalarTower k (End A)ᵐᵒᵖ M :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    rw [cliffordReconstructionCoefficients_smul, AlgHom.commutes, algebraMap_smul]

attribute [local instance] cliffordReconstructionCoefficientTower

/-- Read the semilinear operators of a multiplicity-algebra module from its basis action. -/
noncomputable def cliffordReconstructionSemilinearAction (M : ModuleCat.{w} B) :
    CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M :=
  CrossedSystem.SemilinearAction.ofAlgHom (Algebra.lsmul k k M) (fun _ => rfl)

/-- The recovered semilinear operator is multiplication by its crossed-product basis element. -/
@[simp]
theorem cliffordReconstructionSemilinearAction_apply (M : ModuleCat.{w} B)
    (q : Quotient A) (m : M) :
    (cliffordReconstructionSemilinearAction A s hs M).operator q m =
      CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs).opInv q • m := by
  -- Restriction along the coefficient inclusion is the same scalar action;
  -- `erw` identifies the two bundled module views in `ofAlgHom`.
  unfold cliffordReconstructionSemilinearAction
  erw [CrossedSystem.SemilinearAction.ofAlgHom_operator]
  rfl

/-- Reconstruct inertia representations from arbitrary modules over the actual
opposite-commutant, inverse-factor multiplicity algebra. This abbreviation preserves
the balanced-tensor carriers needed to state the action and morphism formulas. -/
noncomputable abbrev cliffordReconstructionFunctor :
    ModuleCat.{w} B ⥤ Rep.{max u w} k (inertia A) where
  obj M := Rep.of (cliffordReconstructionRepresentation A s hs
    (cliffordReconstructionSemilinearAction A s hs M))
  map {M M'} f := Rep.ofHom (cliffordReconstructionMap A s hs
    (cliffordReconstructionSemilinearAction A s hs M)
    (cliffordReconstructionSemilinearAction A s hs M')
    (f.hom.restrictScalars k)
    (fun d m => by
      simp only [LinearMap.restrictScalars_apply, cliffordReconstructionCoefficients_smul]
      exact f.hom.map_smul (CrossedSystem.Algebra.inc
        (cliffordCrossedSystem A s hs).opInv d) m)
    (fun q m => by
      simpa only [LinearMap.restrictScalars_apply,
        cliffordReconstructionSemilinearAction_apply] using
        f.hom.map_smul (CrossedSystem.Algebra.basis
          (cliffordCrossedSystem A s hs).opInv q) m))
  map_id M := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply BalancedTensorProduct.hom_ext
    intro m x
    simp [coe_cliffordReconstructionMap]
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply BalancedTensorProduct.hom_ext
    intro m x
    dsimp only [Rep.hom_comp, Rep.hom_ofHom]
    simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
    simp [coe_cliffordReconstructionMap]

/-- If an implementer's extension class is written as a kernel unit times a section
value, its action first applies the corresponding crossed-product basis operator and
then inverse right multiplication by the kernel unit. -/
theorem cliffordReconstructionFunctor_obj_projection_tmul (M : ModuleCat.{w} B)
    (p : implementers A) (d : (End A)ˣ) (q : Quotient A)
    (hp : (QuotientGroup.mk p : Carrier A) = inl A d * s q) (m : M) (x : V) :
    letI := cliffordReconstructionCoefficients A s hs M
    ((cliffordReconstructionFunctor A s hs).obj M).ρ (projection A p)
        (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V)
        (CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs).opInv
          (op (↑d⁻¹ : End A)) •
            (CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs).opInv q • m))
        (p.1.2 x) := by
  dsimp only [cliffordReconstructionFunctor, Rep.of_ρ]
  erw [cliffordReconstructionRepresentation_projection_tmul, hp, map_mul,
    mul_apply_eq_comp, cliffordReconstructionMultiplicityRepresentation_section,
    cliffordReconstructionMultiplicityRepresentation_inl]
  rw [cliffordReconstructionSemilinearAction_apply, cliffordReconstructionCoefficients_smul]

instance : (cliffordReconstructionFunctor.{u, v, w} A s hs).Additive where
  map_add {X Y} f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply BalancedTensorProduct.hom_ext
    intro m x
    simp only [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap,
      LinearMap.add_apply]
    dsimp only [cliffordReconstructionFunctor, Rep.hom_ofHom]
    simp [coe_cliffordReconstructionMap, BalancedTensorProduct.add_tmul]

instance : (cliffordReconstructionFunctor.{u, v, w} A s hs).Linear k where
  map_smul {X Y} f r := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply BalancedTensorProduct.hom_ext
    intro m x
    simp only [Rep.smul_hom, Representation.IntertwiningMap.toLinearMap_smul,
      LinearMap.smul_apply]
    dsimp only [cliffordReconstructionFunctor, Rep.hom_ofHom]
    simp [coe_cliffordReconstructionMap, BalancedTensorProduct.smul_tmul]

end FDRep
