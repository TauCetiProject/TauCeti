/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Module
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Evaluation

/-!
# Recovering intertwiners from Clifford multiplicities

For an inertia representation whose restriction to the normal subgroup is semisimple
and isotypic of type `A`, postcomposition identifies its intertwiners with the maps
of its crossed-product multiplicity module. The target representation is arbitrary.
Thus the multiplicity functor is fully faithful on semisimple isotypic representations,
including over nonsplitting fields and for infinite inertia quotients.

The inverse sends a multiplicity map `h` to the map determined by
`f(x) ↦ h(f)(x)`. Balanced evaluation constructs this map: coefficient linearity
makes it balanced over the full commutant, while the crossed-product operators
supply inertia equivariance. No identification of the commutant with scalars is used.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension
open scoped MonoidAlgebra

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)

local notation "res" => Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))
local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "C" => cliffordMultiplicityFunctor A s hs

attribute [local instance] endModule

-- Select the concrete action stored in the functor's bundled objects.
private noncomputable local instance multiplicityModule (W : FDRep k (inertia A)) :
    Module (CrossedSystem.Algebra (cliffordCrossedSystem A s hs).opInv)
      (A ⟶ (res).obj W) :=
  (cliffordMultiplicitySemilinearAction A s hs W).module

private theorem multiplicityMap_smul {W W' : FDRep k (inertia A)}
    (h : (C).obj W ⟶ (C).obj W') (d : (End A)ᵐᵒᵖ)
    (f : A ⟶ (res).obj W) : h.hom (d • f) = d • h.hom f := by
  simpa only [CrossedSystem.SemilinearAction.module_inc_smul] using
    h.hom.map_smul (CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs).opInv d) f

private theorem multiplicityMap_operator {W W' : FDRep k (inertia A)}
    (h : (C).obj W ⟶ (C).obj W') (c : Carrier A)
    (f : A ⟶ (res).obj W) :
    h.hom (cliffordMultiplicityRepresentation A W c f) =
      cliffordMultiplicityRepresentation A W' c (h.hom f) := by
  have hsection (q : Quotient A) (f : A ⟶ (res).obj W) :
      h.hom (cliffordMultiplicityRepresentation A W (s q) f) =
        cliffordMultiplicityRepresentation A W' (s q) (h.hom f) := by
    simpa only [CrossedSystem.SemilinearAction.module_basis_smul,
      cliffordMultiplicitySemilinearAction_operator] using
      h.hom.map_smul (CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs).opInv q) f
  have hker : c * (s (rightHom A c))⁻¹ ∈ (inl A).range := by
    rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp [← groupExtension_rightHom, GroupExtension.Section.rightHom_section]
  obtain ⟨d, hd⟩ := hker
  have hc : c = inl A d * s (rightHom A c) := by
    rw [hd]
    group
  rw [hc]
  simp only [map_mul, mul_apply_eq_comp]
  rw [inl_apply, cliffordMultiplicityRepresentation_mk_kernelLift,
    cliffordMultiplicityRepresentation_mk_kernelLift, multiplicityMap_smul, hsection]

private noncomputable def multiplicityTensorMap {W W' : FDRep k (inertia A)}
    (h : (C).obj W ⟶ (C).obj W') :
    Representation.IntertwiningMap (cliffordTensorRepresentation A W)
      (cliffordTensorRepresentation A W') := by
  letI := (cliffordMultiplicitySemilinearAction A s hs W).isScalarTower
  letI := (cliffordMultiplicitySemilinearAction A s hs W').isScalarTower
  exact
    { toLinearMap := BalancedTensorProduct.map (h.hom.restrictScalars k) LinearMap.id
        (fun d f => multiplicityMap_smul A s hs h (op d) f) (fun _ _ => rfl)
      isIntertwining' := fun t => by
        obtain ⟨p, rfl⟩ := projection_surjective A t
        apply BalancedTensorProduct.hom_ext
        intro f x
        erw [LinearMap.comp_apply, cliffordTensorRepresentation_projection_tmul,
          BalancedTensorProduct.map_tmul, LinearMap.comp_apply, BalancedTensorProduct.map_tmul,
          cliffordTensorRepresentation_projection_tmul]
        exact congrArg (fun g => BalancedTensorProduct.tmul k (End A) (N := V) g (p.1.2 x))
          (multiplicityMap_operator A s hs h (QuotientGroup.mk p) f) }

private theorem multiplicityTensorMap_tmul {W W' : FDRep k (inertia A)}
    (h : (C).obj W ⟶ (C).obj W') (f : A ⟶ (res).obj W) (x : V) :
    multiplicityTensorMap A s hs h (BalancedTensorProduct.tmul k (End A) (N := V) f x) =
      BalancedTensorProduct.tmul k (End A) (N := V) (h.hom f) x := by
  exact BalancedTensorProduct.map_tmul _ _ _ _ f x

variable {W W' : FDRep k (inertia A)}
  [IsSemisimpleModule k[N] (Representation.asModule (FDRep.ρ
    ((Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W)))]
  (hW : IsIsotypicOfType k[N] (Representation.asModule (FDRep.ρ
    ((Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W)))
    (Representation.asModule A.ρ))

/-- Recover an inertia intertwiner from a crossed-product multiplicity map by
balanced evaluation. Only the source must have semisimple isotypic restriction. -/
noncomputable def cliffordMultiplicityPreimage (h : (C).obj W ⟶ (C).obj W') : W ⟶ W' := by
  let e := cliffordBalancedEvaluationEquiv A W hW
  let f := (cliffordBalancedEvaluation A W').comp
    ((multiplicityTensorMap A s hs h).comp e.symm.toIntertwiningMap)
  exact
    { hom := FGModuleCat.ofHom f.toLinearMap
      comm := fun t => by
        apply FGModuleCat.hom_ext
        exact f.isIntertwining' t }

/-- The recovered intertwiner is characterized on every value of a multiplicity. -/
@[simp]
theorem cliffordMultiplicityPreimage_apply (h : (C).obj W ⟶ (C).obj W')
    (f : A ⟶ (res).obj W) (x : A) :
    (cliffordMultiplicityPreimage A s hs hW h).hom.hom.hom (f.hom.hom.hom x) =
      (h.hom f).hom.hom.hom x := by
  -- Unbundle the action morphism constructed from the composite linear map.
  change cliffordBalancedEvaluation A W'
    (multiplicityTensorMap A s hs h
      ((cliffordBalancedEvaluationEquiv A W hW).symm (f.hom.hom.hom x))) = _
  erw [cliffordBalancedEvaluationEquiv_symm_apply_map, multiplicityTensorMap_tmul,
    cliffordBalancedEvaluation_tmul]

/-- Postcomposition by the recovered intertwiner is the original multiplicity map. -/
@[simp]
theorem cliffordMultiplicityFunctor_map_preimage (h : (C).obj W ⟶ (C).obj W') :
    (C).map (cliffordMultiplicityPreimage A s hs hW h) = h := by
  apply ModuleCat.hom_ext
  ext f x
  simp only [cliffordMultiplicityFunctor, ModuleCat.hom_ofHom,
    CrossedSystem.SemilinearAction.linearMap_apply, Linear.rightComp_apply]
  exact cliffordMultiplicityPreimage_apply A s hs hW h f x

include hW in
/-- Intertwiners with semisimple isotypic source are determined by postcomposition
on the multiplicity module, and every crossed-product module map arises this way. -/
theorem cliffordMultiplicityFunctor_map_bijective :
    Function.Bijective ((C).map : (W ⟶ W') → ((C).obj W ⟶ (C).obj W')) := by
  constructor
  · intro f g hfg
    have heval := (cliffordBalancedEvaluationEquiv A W hW).surjective
    ext y
    obtain ⟨z, rfl⟩ := heval y
    have hz : ∀ z, f.hom.hom.hom (cliffordBalancedEvaluation A W z) =
        g.hom.hom.hom (cliffordBalancedEvaluation A W z) := by
      intro z
      induction z using BalancedTensorProduct.induction_on with
      | ht a x =>
        rw [cliffordBalancedEvaluation_tmul]
        have hh : ((C).map f).hom a = ((C).map g).hom a :=
          congrArg (fun h : (C).obj W ⟶ (C).obj W' => h.hom a) hfg
        simp only [cliffordMultiplicityFunctor, ModuleCat.hom_ofHom,
          CrossedSystem.SemilinearAction.linearMap_apply, Linear.rightComp_apply] at hh
        exact congrArg (fun h => h.hom.hom.hom x) hh
      | ha a b ha hb => simp [ha, hb]
    simpa only [Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap, cliffordBalancedEvaluationEquiv_apply] using hz z
  · intro h
    exact ⟨cliffordMultiplicityPreimage A s hs hW h,
      cliffordMultiplicityFunctor_map_preimage A s hs hW h⟩

/-- Intertwiners are exactly the maps of crossed-product multiplicity modules when
the source has semisimple isotypic restriction to the normal subgroup. -/
noncomputable def cliffordMultiplicityHomEquiv :
    (W ⟶ W') ≃ ((C).obj W ⟶ (C).obj W') :=
  Equiv.ofBijective (C).map (cliffordMultiplicityFunctor_map_bijective A s hs hW)

/-- The Hom correspondence is postcomposition on multiplicities. -/
@[simp]
theorem cliffordMultiplicityHomEquiv_apply (g : W ⟶ W') :
    cliffordMultiplicityHomEquiv A s hs hW g = (C).map g := (rfl)

/-- The inverse Hom correspondence is the balanced-evaluation reconstruction. -/
@[simp]
theorem cliffordMultiplicityHomEquiv_symm_apply (h : (C).obj W ⟶ (C).obj W') :
    (cliffordMultiplicityHomEquiv A s hs hW).symm h =
      cliffordMultiplicityPreimage A s hs hW h := by
  apply (cliffordMultiplicityHomEquiv A s hs hW).injective
  rw [Equiv.apply_symm_apply, cliffordMultiplicityHomEquiv_apply,
    cliffordMultiplicityFunctor_map_preimage]

end FDRep
