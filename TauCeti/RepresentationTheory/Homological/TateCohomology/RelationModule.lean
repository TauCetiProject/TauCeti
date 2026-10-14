/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
import TauCeti.RepresentationTheory.Homological.TateCohomology.Augmentation
import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective

/-!
# Tate cohomology of the relation module

Let `G` be a group, `k` a commutative ring and `g : ι → G` a family of elements indexed by a
finite type which generates `G`. Lyndon's sequence `0 → R → k[G]^ι → I_G → 0`, where `R` is the
relation module `TauCeti.MonoidAlgebra.relationModule k G g` and `I_G` the augmentation ideal, and
the augmentation sequence `0 → I_G → k[G] → k → 0` both have a free middle term, which has no Tate
cohomology on any finite subgroup. Their connecting homomorphisms therefore compose to an
isomorphism `H-hat^n(S, k) ≅ H-hat^(n+2)(S, R)` for every finite subgroup `S` of `G` and every
`n : ℤ`.

In particular `H-hat^3(S, R) ≅ H¹(S, k) = Hom(S, k)` vanishes when `k` has no additive torsion,
and `H-hat^2(S, R) ≅ H-hat^0(S, k) = k ⧸ #S k`. These are the degree-two and degree-three inputs
of Tate's isomorphism criterion for a map from the relation module to a module with the same
low-degree cohomology, such as the completed multiplicative group of a local field.

## Main statements

* `TauCeti.TateCohomology.isZero_tateCohomology_three_res_relationModule`: `H-hat^3(S, R) = 0`
  when `k` has no additive torsion.
* `TauCeti.TateCohomology.natCard_tateCohomology_two_res_relationModule`: `H-hat^2(S, R)` has as
  many elements as `k ⧸ #S k`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (5.6.6) and the
  proof of (7.4.2).
* K. W. Gruenberg, *Relation modules of finite groups*, CBMS Regional Conference Series in
  Mathematics 25 (1976), Chapter 2.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti.TateCohomology

open _root_.Rep

variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} [Fintype ι] {g : ι → G}

/-- The inclusion `I_G → k[G]` of the augmentation ideal, as a morphism from the representation
attached to the `k[G]`-module `I_G` to the left regular representation. -/
private def augmentationKerToLeftRegular :
    ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
      (RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G))) ⟶ leftRegular k G :=
  ConcreteCategory.ofHom
  { toFun x := ((RestrictScalars.addEquiv k (MonoidAlgebra k G) _ x :
      RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G)) : MonoidAlgebra k G)
    map_add' _ _ := rfl
    map_smul' r x := (congrArg Subtype.val
      (RestrictScalars.addEquiv_map_smul k (MonoidAlgebra k G)
        (RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G)) r x)).trans
      (Algebra.smul_def r _).symm
    -- Both actions are left multiplication by `single h 1`; the closing `rfl`s identify the
    -- representations `ofModule I_G` and `ofMulAction k G G` with the actions of the objects
    -- `ofModuleMonoidAlgebra.obj I_G` and `leftRegular k G`, which are these by definition.
    isIntertwining' h := LinearMap.ext fun x ↦
      (congrArg (fun y ↦ ((RestrictScalars.addEquiv k (MonoidAlgebra k G) _ y :
          RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G)) : MonoidAlgebra k G))
        ((Representation.ofModule_asAlgebraHom_apply_apply
          (RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G)) (MonoidAlgebra.single h 1)
            x).symm.trans
          (by rw [Representation.asAlgebraHom_single_one]; rfl))).symm.trans
      ((Representation.asAlgebraHom_ofMulAction_smul_eq_mul _ _).symm.trans
        (by rw [Representation.asAlgebraHom_single_one]; rfl)) }

/-- The representation attached to the augmentation ideal of `k[G]`, the last term of Lyndon's
sequence, is the augmentation ideal `Rep.augmentationIdeal k G`, the categorical kernel of the
augmentation: the inclusion `I_G → k[G]` lifts to an isomorphism onto that kernel. -/
private def augmentationKerIso :
    ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
      (RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G))) ≅ augmentationIdeal k G :=
  let l := KernelFork.IsLimit.lift' (augmentationιIsKernel k G) augmentationKerToLeftRegular (by
    ext x
    exact (augmentation_hom_apply k G _).trans
      (RestrictScalars.addEquiv k (MonoidAlgebra k G) _ x).2)
  have : Mono augmentationKerToLeftRegular := (Rep.mono_iff_injective _).2 fun x y h ↦
    (RestrictScalars.addEquiv k (MonoidAlgebra k G) _).injective (Subtype.ext h)
  have : Mono l.1 := mono_of_mono_fac l.2
  have hy (y : augmentationIdeal k G) :
      (augmentationι k G).hom y ∈ RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G) := by
    rw [RingHom.mem_ker, ← augmentation_hom_apply, ← ConcreteCategory.comp_apply,
      augmentationι_comp_augmentation]
    rfl
  have : Epi l.1 := (Rep.epi_iff_surjective _).2 fun y ↦
    ⟨(RestrictScalars.addEquiv k (MonoidAlgebra k G)
      (RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G))).symm ⟨_, hy y⟩,
      TauCeti.AugmentationIdeal.augmentationι_injective k G <|
        (ConcreteCategory.comp_apply l.1 (augmentationι k G) _).symm.trans
          (ConcreteCategory.congr_hom l.2 _)⟩
  have : IsIso l.1 := isIso_of_mono_of_epi _
  asIso l.1

variable (g) in
/-- The map `k[G]^ι → I_G`, `e_i ↦ g_i - 1`, whose kernel is the relation module. -/
private def relationModuleToKer :
    (ι → MonoidAlgebra k G) →ₗ[MonoidAlgebra k G]
      RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G) :=
  (Fintype.linearCombination (MonoidAlgebra k G)
    fun i ↦ MonoidAlgebra.single (g i) (1 : k) - 1).codRestrict _ fun c ↦
      TauCeti.MonoidAlgebra.range_linearCombination_le_ker_augmentation g ⟨c, rfl⟩

private theorem exact_relationModuleToKer :
    Function.Exact (TauCeti.MonoidAlgebra.relationModule k G g).subtype
      (relationModuleToKer g) := by
  have h := (relationModuleToKer (k := k) g).exact_subtype_ker_map
  rwa [relationModuleToKer, LinearMap.ker_codRestrict,
    ← TauCeti.MonoidAlgebra.relationModule_def] at h

variable (k g) in
/-- Lyndon's sequence `0 → R → k[G]^ι → I_G → 0` of `k[G]`-modules. -/
private def relationModuleShortComplex : ShortComplex (ModuleCat.{u} (MonoidAlgebra k G)) :=
  ModuleCat.shortComplexOfCompEqZero (TauCeti.MonoidAlgebra.relationModule k G g).subtype
    (relationModuleToKer g) exact_relationModuleToKer.linearMap_comp_eq_zero

private theorem relationModuleShortComplex_shortExact (hg : Subgroup.closure (Set.range g) = ⊤) :
    (relationModuleShortComplex k g).ShortExact := by
  refine ModuleCat.shortComplex_shortExact (relationModuleShortComplex k g)
    exact_relationModuleToKer (TauCeti.MonoidAlgebra.relationModule k G g).injective_subtype ?_
  rintro ⟨x, hx⟩
  rw [← TauCeti.MonoidAlgebra.range_linearCombination_eq_ker_augmentation hg] at hx
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c, rfl⟩

variable (k) in
/-- **The double dimension shift of the relation module**: for a family `g` generating `G` and a
finite subgroup `S`, `H-hat^n(S, k) ≅ H-hat^(n+2)(S, R)`, where `R` is the relation module of
`g`. It is the augmentation dimension shift `augmentationδIso`, carried to the last term `I_G` of
Lyndon's sequence `0 → R → k[G]^ι → I_G → 0`, followed by the connecting homomorphism of that
sequence. -/
private def relationModuleShiftIso (hg : Subgroup.closure (Set.range g) = ⊤) (S : Subgroup G)
    [Fintype S] (n : ℤ) :
    tateCohomology (res S.subtype (trivial k G k)) n ≅
      tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
        (TauCeti.MonoidAlgebra.relationModule k G g)))) (n + 1 + 1) :=
  augmentationδIso k S n ≪≫
    (tateCohomologyFunctor (n + 1)).mapIso
      ((resFunctor S.subtype).mapIso augmentationKerIso.symm) ≪≫
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact ((shortExact_res S.subtype).2
      ((relationModuleShortComplex_shortExact hg).map_of_exact ofModuleMonoidAlgebra))).δIso
      (n + 1) (n + 1 + 1) rfl
      (isZero_res_ofModuleMonoidAlgebra_obj (.of _ (ι → MonoidAlgebra k G)) S _)
      (isZero_res_ofModuleMonoidAlgebra_obj (.of _ (ι → MonoidAlgebra k G)) S _)

variable (k) in
/-- **`H-hat^3(S, R) = 0`** for the relation module `R` of a family generating `G`, a finite
subgroup `S` and a coefficient ring `k` without additive torsion: it is `H¹(S, k) = Hom(S, k)`. -/
theorem isZero_tateCohomology_three_res_relationModule [IsAddTorsionFree k]
    (hg : Subgroup.closure (Set.range g) = ⊤) (S : Subgroup G) [Fintype S] :
    IsZero (tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of
      (MonoidAlgebra k G) (TauCeti.MonoidAlgebra.relationModule k G g)))) 3) :=
  have : (res S.subtype (trivial k G k)).IsTrivial := ⟨fun _ ↦ rfl⟩
  ((TauCeti.groupCohomology.isZero_H1_of_isTrivial (res S.subtype (trivial k G k))).of_iso
    ((_root_.TateCohomology.isoGroupCohomology 1).app _)).of_iso
    (relationModuleShiftIso k hg S 1).symm

variable (k) in
/-- **`H-hat^2(S, R) ≅ k ⧸ #S k`** for the relation module `R` of a family generating `G` and a
finite subgroup `S`, as a count of elements: it is `H-hat^0(S, k)`. -/
theorem natCard_tateCohomology_two_res_relationModule (hg : Subgroup.closure (Set.range g) = ⊤)
    (S : Subgroup G) [Fintype S] :
    Nat.card (tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of
      (MonoidAlgebra k G) (TauCeti.MonoidAlgebra.relationModule k G g)))) 2) =
      Nat.card (k ⧸ Ideal.span {(Nat.card S : k)}) :=
  -- The restriction to `S` of the trivial representation of `G` is the trivial representation
  -- of `S`, the source of `H0LinearEquivTrivial k S`.
  (Nat.card_congr (relationModuleShiftIso k hg S 0).toLinearEquiv.toEquiv).symm.trans
    (Nat.card_congr (H0LinearEquivTrivial k S).toEquiv)

end TauCeti.TateCohomology
