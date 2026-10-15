/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Augmentation
import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective.Basic

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

* `TauCeti.TateCohomology.relationModuleShiftIso`: the double dimension-shift isomorphism
  `H-hat^n(S, k) ≅ H-hat^(n+2)(S, R)`.
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
/-- The connecting homomorphism of Lyndon's sequence for a family `g` generating `G`, restricted
to a finite subgroup `S`. -/
def relationModuleδ (hg : Subgroup.closure (Set.range g) = ⊤) (S : Subgroup G)
    [Fintype S] (n : ℤ) :
    tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
      (RingHom.ker (TauCeti.MonoidAlgebra.augmentation k G))))) n ⟶
      tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
        (TauCeti.MonoidAlgebra.relationModule k G g)))) (n + 1) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact ((shortExact_res S.subtype).2
    ((relationModuleShortComplex_shortExact hg).map_of_exact ofModuleMonoidAlgebra))).δ
    n (n + 1) rfl

/-- The connecting homomorphism of Lyndon's sequence is an isomorphism because its middle term is
free. -/
noncomputable instance relationModuleδ_isIso (hg : Subgroup.closure (Set.range g) = ⊤)
    (S : Subgroup G) [Fintype S] (n : ℤ) : IsIso (relationModuleδ k hg S n) :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact ((shortExact_res S.subtype).2
    ((relationModuleShortComplex_shortExact hg).map_of_exact ofModuleMonoidAlgebra))).isIso_δ
    n (n + 1) rfl
    (isZero_res_ofModuleMonoidAlgebra_obj (.of _ (ι → MonoidAlgebra k G)) S _)
    (isZero_res_ofModuleMonoidAlgebra_obj (.of _ (ι → MonoidAlgebra k G)) S _)

variable (k) in
/-- **The double dimension shift of the relation module**: for a family `g` generating `G` and a
finite subgroup `S`, `H-hat^n(S, k) ≅ H-hat^(n+2)(S, R)`, where `R` is the relation module of
`g`. It is the augmentation dimension shift `augmentationδIso`, carried to the last term `I_G` of
Lyndon's sequence `0 → R → k[G]^ι → I_G → 0`, followed by the connecting homomorphism of that
sequence. -/
def relationModuleShiftIso (hg : Subgroup.closure (Set.range g) = ⊤) (S : Subgroup G)
    [Fintype S] (n : ℤ) :
    tateCohomology (res S.subtype (trivial k G k)) n ≅
      tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra k G)
        (TauCeti.MonoidAlgebra.relationModule k G g)))) (n + 1 + 1) :=
  augmentationδIso k S n ≪≫
    (tateCohomologyFunctor (n + 1)).mapIso
      ((resFunctor S.subtype).mapIso (augmentationKerIso k G).symm) ≪≫
    asIso (relationModuleδ k hg S (n + 1))

/-- The double dimension shift is the connecting map of the augmentation sequence, transported
across the comparison between the two augmentation ideals, followed by the connecting map of
Lyndon's sequence. -/
@[simp]
theorem relationModuleShiftIso_hom (hg : Subgroup.closure (Set.range g) = ⊤)
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    (relationModuleShiftIso k hg S n).hom =
      @_root_.TateCohomology.δ k S _ _ _ _
          (augmentationSES_res_shortExact k G S.subtype) n ≫
        (tateCohomologyFunctor (n + 1)).map
          ((resFunctor S.subtype).map (augmentationKerIso k G).inv) ≫
        (asIso (relationModuleδ k hg S (n + 1))).hom := by
  rw [relationModuleShiftIso, Iso.trans_hom, Iso.trans_hom, augmentationδIso_hom,
    Functor.mapIso_hom, Functor.mapIso_hom, Iso.symm_hom]
  rfl

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
