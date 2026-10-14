/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
import TauCeti.RepresentationTheory.Homological.Augmentation
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective
import TauCeti.RepresentationTheory.Rep.TensorShortExact

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

/-- The augmentation sequence `0 → I_G → k[G] → k → 0`, with `I_G` the representation attached to
the augmentation ideal of `k[G]`, the last term of Lyndon's sequence. (`Rep.augmentationSES` has
the categorical kernel of the augmentation as its first term instead.) -/
private def augmentationKerSES : ShortComplex (Rep k G) :=
  ShortComplex.mk augmentationKerToLeftRegular (augmentation k G) (by
    ext x
    exact (augmentation_hom_apply k G _).trans
      (RestrictScalars.addEquiv k (MonoidAlgebra k G) _ x).2)

private theorem augmentationKerSES_shortExact :
    (augmentationKerSES (k := k) (G := G)).ShortExact := by
  refine .mk' ((exact_iff_function_exact _).2 fun y ↦ ?_)
    ((Rep.mono_iff_injective _).2 fun x y h ↦ ?_) (augmentation_epi k G)
  · refine ⟨fun hy ↦ ⟨(RestrictScalars.addEquiv k (MonoidAlgebra k G) _).symm
      ⟨y, (augmentation_hom_apply k G y).symm.trans hy⟩, rfl⟩, ?_⟩
    rintro ⟨x, rfl⟩
    exact (augmentation_hom_apply k G _).trans
      (RestrictScalars.addEquiv k (MonoidAlgebra k G) _ x).2
  · exact (RestrictScalars.addEquiv k (MonoidAlgebra k G) _).injective (Subtype.ext h)

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
      (relationModuleToKer g) := fun c ↦ by
  rw [Submodule.coe_subtype, Subtype.range_coe_subtype, Set.mem_ofPred_eq,
    TauCeti.MonoidAlgebra.relationModule_def, LinearMap.mem_ker, ← Subtype.coe_inj]
  -- `relationModuleToKer g` is the restriction of the linear combination to its codomain.
  rfl

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
`g`. It is the composite of the connecting homomorphisms of the augmentation sequence
`0 → I_G → k[G] → k → 0` and of Lyndon's sequence `0 → R → k[G]^ι → I_G → 0`. -/
private def relationModuleShiftIso (hg : Subgroup.closure (Set.range g) = ⊤) (S : Subgroup G)
    [Fintype S] (n : ℤ) :
    tateCohomology (res S.subtype (trivial k G k)) n ≅
      tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
        (TauCeti.MonoidAlgebra.relationModule k G g)))) (n + 1 + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact
      ((shortExact_res S.subtype).2 augmentationKerSES_shortExact)).δIso n (n + 1) rfl
      (isZero_res_leftRegular S n) (isZero_res_leftRegular S (n + 1)) ≪≫
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
