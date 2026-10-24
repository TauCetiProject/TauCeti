/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# The reduced Mayer–Vietoris connecting morphism

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`. The Mayer–Vietoris
connecting morphism `Hₖ₊₁(X) ⟶ Hₖ(U ∩ V)` lands in the reduced homology of `U ∩ V`: in degree
zero, it is killed by the map to `H₀(U)`, which commutes with the augmentations. The resulting
morphism `TopCat.reducedMayerVietorisδ` is natural in maps of covered spaces. It is an epimorphism
as soon as the reduced homology of `U` and of `V` vanishes in degree `k`, and an isomorphism as soon
as it vanishes in degrees `k` and `k + 1`, in particular when `U` and `V` are contractible.

This is the form in which the Mayer–Vietoris sequence computes the homology of a sphere from its
cover by the complements of two antipodal points.

Coefficients are an object `R` of an abelian category with coproducts.

## Main definitions and results

* `TopCat.reducedMayerVietorisδ`: the connecting morphism `Hₖ₊₁(X) ⟶ H_redₖ(U ∩ V)`.
* `TopCat.reducedMayerVietorisδ_comp_ι`: it lifts the Mayer–Vietoris connecting morphism.
* `TopCat.reducedMayerVietorisδ_naturality`: naturality in maps of covered spaces.
* `TopCat.epi_reducedMayerVietorisδ`: it is an epimorphism when `U` and `V` have vanishing
  reduced homology in its target degree.
* `TopCat.isIso_reducedMayerVietorisδ`: it is an isomorphism when `U` and `V` have vanishing
  reduced homology in the two adjacent degrees; `TopCat.isIso_reducedMayerVietorisδ_of_contractible`
  specializes this to contractible `U` and `V`.
* `TopCat.eq_zero_of_comp_reducedSingularHomologyFunctor_map_inclusion`: for open subsets `A`
  and `B` of a space with `H_redₖ₊₁(A ∪ B) = 0`, a class of `A ∩ B` in degree `k` vanishing in
  `A` and in `B` is zero, by exactness of the Mayer–Vietoris sequence at `Hₖ(A ∩ B)`.
* `TopCat.reducedMayerVietorisIsoOfIsZero`: for open subsets `A` and `B` of a space with vanishing
  reduced homology in degrees `k` and `k + 1`, the isomorphism `H_redₖ₊₁(A ∪ B) ≅ H_redₖ(A ∩ B)`.
* `TauCeti.bijective_singularHomologyMap_inclusion_prod_neg`: for an open cover `X = U ∪ V` with
  `Hₙ₊₁(X) = Hₙ₊₂(X) = 0`, the map `(i_U, -i_V)` on `Hₙ₊₁` is bijective.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the reduced Mayer–Vietoris sequence.
* `TopPair.reducedSingularHomologyδ` for the connecting morphism in relative singular homology.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- The Mayer–Vietoris connecting morphism `Hₖ₊₁(X) ⟶ Hₖ(U ∩ V)`, with its target written as the
singular homology of `U ∩ V`, the form in which reduced homology is defined. -/
private abbrev δ (k : ℕ) :
    (toSSet.obj X).homology R (k + 1) ⟶ ((singularHomologyFunctor C k).obj R).obj (of ↥(U ∩ V)) :=
  mayerVietorisδ R hU hV hUV (k + 1) k

/-- The Mayer–Vietoris connecting morphism followed by the map induced by `U ∩ V ⊆ U` vanishes,
since that map is the first component of the next map of the sequence. -/
private lemma δ_comp_homologyMap_inclusion (k : ℕ) :
    δ R hU hV hUV k ≫ ((singularHomologyFunctor C k).obj R).map
      (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))) = 0 := by
  have := mayerVietorisδ_toBiprod R hU hV hUV (k + 1) k =≫ biprod.fst
  rwa [Category.assoc, SSet.mayerVietorisToBiprod_fst, zero_comp] at this

/-- The Mayer–Vietoris connecting morphism into degree zero followed by the augmentation of
`U ∩ V` vanishes, since the augmentation of `U ∩ V` factors through `H₀(U)`. -/
private lemma δ_comp_singularHomology₀ε :
    δ R hU hV hUV 0 ≫ (of ↥(U ∩ V)).singularHomology₀ε R = 0 := by
  rw [← singularHomologyMap_singularHomology₀ε R
    (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))),
    reassoc_of% δ_comp_homologyMap_inclusion R hU hV hUV 0, zero_comp]

/-- The Mayer–Vietoris connecting morphism `Hₖ₊₁(X) ⟶ H_redₖ(U ∩ V)` of an open cover of `X` by `U`
and `V`, into the reduced singular homology of the intersection. It lifts the Mayer–Vietoris
connecting morphism through the inclusion of reduced into ordinary homology
(`TopCat.reducedMayerVietorisδ_comp_ι`). -/
def reducedMayerVietorisδ : (k : ℕ) →
    (toSSet.obj X).homology R (k + 1) ⟶ (reducedSingularHomologyFunctor R k).obj (of ↥(U ∩ V))
  | 0 => kernel.lift _ (δ R hU hV hUV 0) (δ_comp_singularHomology₀ε R hU hV hUV) ≫
      eqToHom (reducedSingularHomologyFunctor_zero_obj R _).symm
  | k + 1 => δ R hU hV hUV (k + 1) ≫ (reducedSingularHomologySuccIso R k).inv.app _

/-- The reduced Mayer–Vietoris connecting morphism followed by the inclusion of reduced into
ordinary homology is the Mayer–Vietoris connecting morphism. -/
@[reassoc (attr := simp)]
lemma reducedMayerVietorisδ_comp_ι (k : ℕ) :
    reducedMayerVietorisδ R hU hV hUV k ≫ (reducedSingularHomologyι R k).app (of ↥(U ∩ V)) =
      mayerVietorisδ R hU hV hUV (k + 1) k := by
  cases k with
  | zero => simp [reducedMayerVietorisδ]
  | succ k => simp [reducedMayerVietorisδ, ← reducedSingularHomologySuccIso_hom]

/-- **The reduced Mayer–Vietoris connecting morphism is an epimorphism when both open sets are
acyclic in its target degree**: if the reduced homology of `U` and of `V` vanishes in degree `k`,
then `Hₖ₊₁(X) ⟶ H_redₖ(U ∩ V)` is an epimorphism. -/
theorem epi_reducedMayerVietorisδ {k : ℕ}
    (hU₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of U)))
    (hV₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of V))) :
    Epi (reducedMayerVietorisδ R hU hV hUV k) := by
  -- Exactness at `Hₖ(U ∩ V)` identifies the image of the connecting morphism with the cycles of
  -- the map to `Hₖ(U) ⊞ Hₖ(V)`. The inclusion of reduced homology lands in these cycles, as the
  -- reduced homology of `U` and of `V` vanishes, and it is then an isomorphism onto them.
  let S := ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R hU hV hUV (k + 1) k)
  -- The inclusion of reduced homology, with its target written as the homology of the singular
  -- simplicial set, the form in which the Mayer–Vietoris sequence is stated.
  let ι : (reducedSingularHomologyFunctor R k).obj (of ↥(U ∩ V)) ⟶ S.X₂ :=
    (reducedSingularHomologyι R k).app (of ↥(U ∩ V))
  have hι : ι ≫ S.g = 0 := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, SSet.mayerVietorisToBiprod_fst, zero_comp]
      exact ((reducedSingularHomologyι R k).naturality _).symm.trans
        ((hU₀.eq_of_tgt _ 0 =≫ _).trans zero_comp)
    · rw [Category.assoc, SSet.mayerVietorisToBiprod_snd, Preadditive.comp_neg, zero_comp,
        neg_eq_zero]
      exact ((reducedSingularHomologyι R k).naturality _).symm.trans
        ((hV₀.eq_of_tgt _ 0 =≫ _).trans zero_comp)
  have : Mono ι := inferInstanceAs (Mono ((reducedSingularHomologyι R k).app _))
  have : Mono (S.liftCycles ι hι) := mono_of_mono_fac (S.liftCycles_i ι hι)
  have hδ : reducedMayerVietorisδ R hU hV hUV k ≫ S.liftCycles ι hι = S.toCycles := by
    rw [← cancel_mono S.iCycles, Category.assoc, S.liftCycles_i, S.toCycles_i]
    exact reducedMayerVietorisδ_comp_ι R hU hV hUV k
  have : Epi S.toCycles := (mayerVietoris_exact₁ R hU hV hUV (k + 1) k).epi_toCycles
  have : Epi (S.liftCycles ι hι) := epi_of_epi_fac hδ
  have : IsIso (S.liftCycles ι hι) := isIso_of_mono_of_epi _
  rw [← Category.comp_id (reducedMayerVietorisδ R hU hV hUV k),
    ← IsIso.hom_inv_id (S.liftCycles ι hι), ← Category.assoc, hδ]
  infer_instance

/-- **The reduced Mayer–Vietoris connecting morphism is an isomorphism when both open sets are
acyclic in the adjacent degrees**: if the reduced homology of `U` and of `V` vanishes in degrees
`k` and `k + 1`, then `Hₖ₊₁(X) ⟶ H_redₖ(U ∩ V)` is an isomorphism. -/
theorem isIso_reducedMayerVietorisδ {k : ℕ}
    (hU₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of U)))
    (hV₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of V)))
    (hU₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of U)))
    (hV₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of V))) :
    IsIso (reducedMayerVietorisδ R hU hV hUV k) := by
  -- Exactness at `Hₖ₊₁(X)` makes the Mayer–Vietoris connecting morphism a monomorphism, since
  -- `Hₖ₊₁(U) ⊞ Hₖ₊₁(V)` vanishes; the reduced connecting morphism is a factor of it.
  have hB : IsZero ((toSSet.obj (of U)).homology R (k + 1) ⊞
      (toSSet.obj (of V)).homology R (k + 1)) :=
    (biprod_isZero_iff _ _).2 ⟨hU₁.of_iso ((reducedSingularHomologySuccIso R k).app _).symm,
      hV₁.of_iso ((reducedSingularHomologySuccIso R k).app _).symm⟩
  have : Mono (δ R hU hV hUV k) :=
    (mayerVietoris_exact₃ R hU hV hUV (k + 1) k).mono_g (hB.eq_of_src _ _)
  have : Mono (reducedMayerVietorisδ R hU hV hUV k) :=
    mono_of_mono_fac (reducedMayerVietorisδ_comp_ι R hU hV hUV k)
  have := epi_reducedMayerVietorisδ R hU hV hUV hU₀ hV₀
  exact isIso_of_mono_of_epi _

/-- The reduced Mayer–Vietoris connecting morphism of an open cover by two contractible sets is an
isomorphism in every degree. -/
instance isIso_reducedMayerVietorisδ_of_contractible [ContractibleSpace U] [ContractibleSpace V]
    (k : ℕ) : IsIso (reducedMayerVietorisδ R hU hV hUV k) :=
  isIso_reducedMayerVietorisδ R hU hV hUV
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R (of U) (k + 1))
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R (of V) (k + 1))
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R (of U) k)
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R (of V) k)

variable {Y : TopCat.{w}} {U' V' : Set Y} (hU' : IsOpen U') (hV' : IsOpen V')
  (hUV' : U' ∪ V' = Set.univ) (f : X ⟶ Y) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- **Naturality of the reduced Mayer–Vietoris connecting morphism.** A map `f : X ⟶ Y` carrying
`U` into `U'` and `V` into `V'` commutes with the reduced connecting morphisms, where
`U ∩ V ⟶ U' ∩ V'` is the restriction of `f`. -/
@[reassoc]
lemma reducedMayerVietorisδ_naturality (k : ℕ) :
    reducedMayerVietorisδ R hU hV hUV k ≫
        (reducedSingularHomologyFunctor R k).map (ofHom ⟨(hfU.inter_inter hfV).restrict,
          f.hom.continuous.restrict (hfU.inter_inter hfV)⟩) =
      SSet.homologyMap (toSSet.map f) R (k + 1) ≫ reducedMayerVietorisδ R hU' hV' hUV' k := by
  rw [← cancel_mono ((reducedSingularHomologyι R k).app (of ↥(U' ∩ V'))), Category.assoc,
    (reducedSingularHomologyι R k).naturality, reducedMayerVietorisδ_comp_ι_assoc,
    Category.assoc, reducedMayerVietorisδ_comp_ι]
  exact mayerVietorisδ_naturality R hU hV hUV hU' hV' hUV' f hfU hfV (k + 1) k

open Set Topology in
/-- **Injectivity in the Mayer–Vietoris sequence.** Let `A` and `B` be open subsets of a space,
and suppose that the reduced homology of `A ∪ B` vanishes in degree `k + 1`. Then a (generalized)
reduced homology class of `A ∩ B` in degree `k` that vanishes both in `A` and in `B` is zero.

The intersection and the union are allowed to be given by any sets `D` and `E` equal to them. -/
theorem eq_zero_of_comp_reducedSingularHomologyFunctor_map_inclusion {Y : TopCat.{w}}
    {A B D E : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hDA : D ⊆ A) (hDB : D ⊆ B)
    (hD : A ∩ B ⊆ D) (hE : A ∪ B = E) {k : ℕ}
    (hk : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of E)))
    {P : C} (x : P ⟶ (reducedSingularHomologyFunctor R k).obj (of D))
    (hxA : x ≫ (reducedSingularHomologyFunctor R k).map (ofHom (ContinuousMap.inclusion hDA)) = 0)
    (hxB : x ≫ (reducedSingularHomologyFunctor R k).map (ofHom (ContinuousMap.inclusion hDB)) = 0) :
    x = 0 := by
  obtain rfl : D = A ∩ B := (subset_inter hDA hDB).antisymm hD
  subst hE
  -- The Mayer–Vietoris sequence is stated for an open cover of a space, here `A ∪ B`, by the
  -- preimages `U` and `V` of `A` and `B`; these are homeomorphic to `A` and `B` over `Y`.
  let U : Set (of ↥(A ∪ B)) := Subtype.val ⁻¹' A
  let V : Set (of ↥(A ∪ B)) := Subtype.val ⁻¹' B
  have hU : IsOpen U := hA.preimage continuous_subtype_val
  have hV : IsOpen V := hB.preimage continuous_subtype_val
  have hUV : U ∪ V = univ := eq_univ_of_forall fun y ↦ y.2
  let eU : ↥U ≃ₜ ↥A := IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (subset_union_left.trans Subtype.range_coe.symm.subset)
  let eV : ↥V ≃ₜ ↥B := IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (subset_union_right.trans Subtype.range_coe.symm.subset)
  let eUV : ↥(U ∩ V) ≃ₜ ↥(A ∩ B) := IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (inter_subset_left.trans (subset_union_left.trans Subtype.range_coe.symm.subset))
  let iU : of ↥U ≅ of ↥A := isoOfHomeo eU
  let iV : of ↥V ≅ of ↥B := isoOfHomeo eV
  let iUV : of ↥(U ∩ V) ≅ of ↥(A ∩ B) := isoOfHomeo eUV
  have sqU : ofHom (ContinuousMap.inclusion (inter_subset_left (s := U) (t := V))) ≫ iU.hom =
      iUV.hom ≫ ofHom (ContinuousMap.inclusion hDA) := by
    ext x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    dsimp only [iU, iUV]
    rw [isoOfHomeo_hom, isoOfHomeo_hom]
    simp only [ConcreteCategory.hom_ofHom, ContinuousMap.coe_ofClass,
      IsEmbedding.homeomorphOfSubsetRange_apply_coe, ContinuousMap.inclusion_apply_coe, U, V, eU]
    -- `U ∩ V` is `Subtype.val ⁻¹' (A ∩ B)` by `Set.preimage_inter`, which holds by definition.
    exact (IsEmbedding.homeomorphOfSubsetRange_apply_coe (s := A ∩ B) _ _ x).symm
  have sqV : ofHom (ContinuousMap.inclusion (inter_subset_right (s := U) (t := V))) ≫ iV.hom =
      iUV.hom ≫ ofHom (ContinuousMap.inclusion hDB) := by
    ext x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    dsimp only [iV, iUV]
    rw [isoOfHomeo_hom, isoOfHomeo_hom]
    simp only [ConcreteCategory.hom_ofHom, ContinuousMap.coe_ofClass,
      IsEmbedding.homeomorphOfSubsetRange_apply_coe, ContinuousMap.inclusion_apply_coe, U, V, eV]
    -- `U ∩ V` is `Subtype.val ⁻¹' (A ∩ B)` by `Set.preimage_inter`, which holds by definition.
    exact (IsEmbedding.homeomorphOfSubsetRange_apply_coe (s := A ∩ B) _ _ x).symm
  -- Transport the class to `U ∩ V`.
  obtain ⟨x, rfl⟩ : ∃ x' : P ⟶ (reducedSingularHomologyFunctor R k).obj (of ↥(U ∩ V)),
      x = x' ≫ (reducedSingularHomologyFunctor R k).map iUV.hom :=
    ⟨x ≫ (reducedSingularHomologyFunctor R k).map iUV.inv, by
      rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.comp_id]⟩
  have hxU : x ≫ (reducedSingularHomologyFunctor R k).map
      (ofHom (ContinuousMap.inclusion (inter_subset_left (s := U) (t := V)))) = 0 := by
    rw [← cancel_mono ((reducedSingularHomologyFunctor R k).map iU.hom), Category.assoc,
      ← Functor.map_comp, sqU, Functor.map_comp, ← Category.assoc, hxA, zero_comp]
  have hxV : x ≫ (reducedSingularHomologyFunctor R k).map
      (ofHom (ContinuousMap.inclusion (inter_subset_right (s := U) (t := V)))) = 0 := by
    rw [← cancel_mono ((reducedSingularHomologyFunctor R k).map iV.hom), Category.assoc,
      ← Functor.map_comp, sqV, Functor.map_comp, ← Category.assoc, hxB, zero_comp]
  -- Exactness at `Hₖ(U ∩ V)`: the connecting morphism starts at `Hₖ₊₁(A ∪ B) = 0`, so the map to
  -- `Hₖ(U) ⊞ Hₖ(V)` is a monomorphism, and so is its composite with the inclusion of reduced
  -- homology.
  have hmono := (mayerVietoris_exact₁ R hU hV hUV (k + 1) k).mono_g
    ((hk.of_iso ((reducedSingularHomologySuccIso R k).app _).symm).eq_of_src _ _)
  -- The inclusion of reduced homology, with its target written as the homology of the singular
  -- simplicial set, the form in which the Mayer–Vietoris sequence is stated.
  let ι : (reducedSingularHomologyFunctor R k).obj (of ↥(U ∩ V)) ⟶
      (toSSet.obj (of ↥(U ∩ V))).homology R k :=
    (reducedSingularHomologyι R k).app (of ↥(U ∩ V))
  have hx : (x ≫ ι) ≫ SSet.mayerVietorisToBiprod R
        (toSSet.map (ofHom (ContinuousMap.inclusion (inter_subset_left (s := U) (t := V)))))
        (toSSet.map (ofHom (ContinuousMap.inclusion (inter_subset_right (s := U) (t := V))))) k =
      0 := by
    refine biprod.hom_ext _ _ ?_ ?_
    · simp only [Category.assoc, SSet.mayerVietorisToBiprod_fst, zero_comp]
      exact (x ≫= ((reducedSingularHomologyι R k).naturality _).symm).trans
        (((reassoc_of% hxU) _).trans zero_comp)
    · simp only [Category.assoc, SSet.mayerVietorisToBiprod_snd, Preadditive.comp_neg, zero_comp,
        neg_eq_zero]
      exact (x ≫= ((reducedSingularHomologyι R k).naturality _).symm).trans
        (((reassoc_of% hxV) _).trans zero_comp)
  have : Mono ι := inferInstanceAs (Mono ((reducedSingularHomologyι R k).app _))
  have : Mono (SSet.mayerVietorisToBiprod R
      (toSSet.map (ofHom (ContinuousMap.inclusion (inter_subset_left (s := U) (t := V)))))
      (toSSet.map (ofHom (ContinuousMap.inclusion (inter_subset_right (s := U) (t := V))))) k) :=
    hmono
  have hx0 : x = 0 := by
    rw [← cancel_mono ι, zero_comp, ← cancel_mono (SSet.mayerVietorisToBiprod R
      (toSSet.map (ofHom (ContinuousMap.inclusion (inter_subset_left (s := U) (t := V)))))
      (toSSet.map (ofHom (ContinuousMap.inclusion (inter_subset_right (s := U) (t := V))))) k),
      hx, zero_comp]
  rw [hx0, zero_comp]

open Set Topology in
/-- **The reduced Mayer–Vietoris isomorphism of two acyclic open sets.** Let `A` and `B` be open
subsets of a space, and suppose that the reduced homology of `A` and of `B` vanishes in degrees `k`
and `k + 1`. Then the reduced Mayer–Vietoris connecting morphism of the cover of `A ∪ B` by `A`
and `B` (`TopCat.reducedMayerVietorisδ`) is an isomorphism `H_redₖ₊₁(A ∪ B) ≅ H_redₖ(A ∩ B)`.

The intersection and the union are allowed to be given by any sets `D` and `E` equal to them. -/
def reducedMayerVietorisIsoOfIsZero {Y : TopCat.{w}} {A B D E : Set Y} (hA : IsOpen A)
    (hB : IsOpen B) (hD : A ∩ B = D) (hE : A ∪ B = E) {k : ℕ}
    (hA₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of A)))
    (hB₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of B)))
    (hA₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of A)))
    (hB₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of B))) :
    (reducedSingularHomologyFunctor R (k + 1)).obj (of E) ≅
      (reducedSingularHomologyFunctor R k).obj (of D) :=
  -- The Mayer–Vietoris sequence is stated for an open cover of a space, here `E`, by the
  -- preimages `A'` and `B'` of `A` and `B`; these are homeomorphic to `A` and `B` over `Y`.
  have hAE : A ⊆ range (Subtype.val : E → Y) := hE ▸ subset_union_left.trans Subtype.range_coe.ge
  have hBE : B ⊆ range (Subtype.val : E → Y) := hE ▸ subset_union_right.trans Subtype.range_coe.ge
  let A' : Set (of ↥E) := Subtype.val ⁻¹' A
  let B' : Set (of ↥E) := Subtype.val ⁻¹' B
  have hA' : IsOpen A' := hA.preimage continuous_subtype_val
  have hB' : IsOpen B' := hB.preimage continuous_subtype_val
  have hAB' : A' ∪ B' = univ := eq_univ_of_forall fun y ↦ (hE ▸ y.2 : (y : Y) ∈ A ∪ B)
  let iA : of ↥A' ≅ of ↥A := isoOfHomeo (IsEmbedding.subtypeVal.homeomorphOfSubsetRange hAE)
  let iB : of ↥B' ≅ of ↥B := isoOfHomeo (IsEmbedding.subtypeVal.homeomorphOfSubsetRange hBE)
  -- `A' ∩ B'` is `Subtype.val ⁻¹' (A ∩ B)` by `Set.preimage_inter`, which holds by definition.
  let iAB : of ↥(A' ∩ B') ≅ of ↥D := isoOfHomeo
    ((IsEmbedding.subtypeVal.homeomorphOfSubsetRange (inter_subset_left.trans hAE)).trans
      (Homeomorph.setCongr hD))
  -- `TopCat.isIso_reducedMayerVietorisδ` is a theorem with hypotheses rather than an instance, so
  -- it is supplied to `asIso` explicitly.
  (reducedSingularHomologySuccIso R k).app (of ↥E) ≪≫
    @asIso _ _ _ _ (reducedMayerVietorisδ R hA' hB' hAB' k)
      (isIso_reducedMayerVietorisδ R hA' hB' hAB'
        (hA₁.of_iso ((reducedSingularHomologyFunctor R (k + 1)).mapIso iA))
        (hB₁.of_iso ((reducedSingularHomologyFunctor R (k + 1)).mapIso iB))
        (hA₀.of_iso ((reducedSingularHomologyFunctor R k).mapIso iA))
        (hB₀.of_iso ((reducedSingularHomologyFunctor R k).mapIso iB))) ≪≫
    (reducedSingularHomologyFunctor R k).mapIso iAB

end TopCat

namespace TauCeti

open Set Function
open ContinuousMap (singularHomologyMap)

/-- For an open cover `X = U ∪ V` of a space whose reduced homology vanishes in degrees `n + 1`
and `n + 2`, the map `Hₙ₊₁(U ∩ V) → Hₙ₊₁(U) × Hₙ₊₁(V)` given by the first inclusion and the
negative of the second is bijective. -/
theorem bijective_singularHomologyMap_inclusion_prod_neg {k : Type w} [Ring k] {n : ℕ}
    {X : Type w} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ)
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of k k) (n + 1)).obj (TopCat.of X)))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of k k) (n + 2)).obj (TopCat.of X))) :
    Bijective fun x ↦
      (singularHomologyMap k (n + 1) (ContinuousMap.inclusion (inter_subset_left (t := V))) x,
        -singularHomologyMap k (n + 1)
          (ContinuousMap.inclusion (inter_subset_right (s := U))) x) := by
  rw [reducedSingularHomologyFunctor_succ] at h₁ h₂
  have hiso := TopCat.isIso_mayerVietorisToBiprod_of_isZero (X := TopCat.of X)
    (ModuleCat.of k k) hU hV hUV (n + 1) h₂ h₁
  set M := SSet.mayerVietorisToBiprod (ModuleCat.of k k)
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_left (t := V)))))
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_right (s := U)))))
      (n + 1)
  -- Read the biproduct `Hₙ₊₁(U) ⊞ Hₙ₊₁(V)` as the product module, where elements have
  -- coordinates.
  set P := M ≫ (ModuleCat.biprodIsoProd _ _).hom
  have hP : Bijective P.hom := ConcreteCategory.bijective_of_isIso P
  have hfst : ∀ x, (P.hom x).1 = singularHomologyMap k (n + 1)
      (ContinuousMap.inclusion (inter_subset_left (t := V))) x := fun x ↦ by
    have hc : P ≫ (ModuleCat.biprodIsoProd _ _).inv ≫ biprod.fst = SSet.homologyMap
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_left (t := V)))))
        (ModuleCat.of k k) (n + 1) := by
      simp only [P, M, Category.assoc, Iso.hom_inv_id_assoc, SSet.mayerVietorisToBiprod_fst]
    rw [ModuleCat.biprodIsoProd_inv_comp_fst] at hc
    exact congr($(hc).hom x)
  have hsnd : ∀ x, (P.hom x).2 = -singularHomologyMap k (n + 1)
      (ContinuousMap.inclusion (inter_subset_right (s := U))) x := fun x ↦ by
    have hc : P ≫ (ModuleCat.biprodIsoProd _ _).inv ≫ biprod.snd = -SSet.homologyMap
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_right (s := U)))))
        (ModuleCat.of k k) (n + 1) := by
      simp only [P, M, Category.assoc, Iso.hom_inv_id_assoc, SSet.mayerVietorisToBiprod_snd]
    rw [ModuleCat.biprodIsoProd_inv_comp_snd] at hc
    exact congr($(hc).hom x)
  have hP_eq : ⇑P.hom = fun x ↦
      (singularHomologyMap k (n + 1) (ContinuousMap.inclusion (inter_subset_left (t := V))) x,
        -singularHomologyMap k (n + 1)
          (ContinuousMap.inclusion (inter_subset_right (s := U))) x) := by
    funext x
    exact Prod.ext (hfst x) (hsnd x)
  rwa [hP_eq] at hP

end TauCeti
