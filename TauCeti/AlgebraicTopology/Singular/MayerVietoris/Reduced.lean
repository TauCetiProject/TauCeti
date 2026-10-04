/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# The reduced Mayer–Vietoris connecting morphism

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`. The Mayer–Vietoris
connecting morphism `Hₖ₊₁(X) ⟶ Hₖ(U ∩ V)` lands in the reduced homology of `U ∩ V`: in degree
zero, it is killed by the map to `H₀(U)`, which commutes with the augmentations. The resulting
morphism `TopCat.reducedMayerVietorisδ` is natural in maps of covered spaces, and it is an
isomorphism as soon as the reduced homology of `U` and of `V` vanishes in degrees `k` and `k + 1`,
in particular when `U` and `V` are contractible.

This is the form in which the Mayer–Vietoris sequence computes the homology of a sphere from its
cover by the complements of two antipodal points.

Coefficients are an object `R` of an abelian category with coproducts.

## Main definitions and results

* `TopCat.reducedMayerVietorisδ`: the connecting morphism `Hₖ₊₁(X) ⟶ H_redₖ(U ∩ V)`.
* `TopCat.reducedMayerVietorisδ_comp_ι`: it lifts the Mayer–Vietoris connecting morphism.
* `TopCat.reducedMayerVietorisδ_naturality`: naturality in maps of covered spaces.
* `TopCat.isIso_reducedMayerVietorisδ`: it is an isomorphism when `U` and `V` have vanishing
  reduced homology in the two adjacent degrees; `TopCat.isIso_reducedMayerVietorisδ_of_contractible`
  specializes this to contractible `U` and `V`.
* `TopCat.eq_zero_of_comp_reducedSingularHomologyFunctor_map_inclusion`: for open subsets `A`
  and `B` of a space with `H_redₖ₊₁(A ∪ B) = 0`, a class of `A ∩ B` in degree `k` vanishing in
  `A` and in `B` is zero, by exactness of the Mayer–Vietoris sequence at `Hₖ(A ∩ B)`.

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

/-- **The reduced Mayer–Vietoris connecting morphism is an isomorphism when both open sets are
acyclic in the adjacent degrees**: if the reduced homology of `U` and of `V` vanishes in degrees
`k` and `k + 1`, then `Hₖ₊₁(X) ⟶ H_redₖ(U ∩ V)` is an isomorphism. -/
theorem isIso_reducedMayerVietorisδ {k : ℕ}
    (hU₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of U)))
    (hV₁ : IsZero ((reducedSingularHomologyFunctor R (k + 1)).obj (of V)))
    (hU₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of U)))
    (hV₀ : IsZero ((reducedSingularHomologyFunctor R k).obj (of V))) :
    IsIso (reducedMayerVietorisδ R hU hV hUV k) := by
  -- Exactness at `Hₖ₊₁(X)` makes the connecting morphism a monomorphism, since
  -- `Hₖ₊₁(U) ⊞ Hₖ₊₁(V)` vanishes; exactness at `Hₖ(U ∩ V)` then exhibits it as a kernel of the
  -- map to `Hₖ(U) ⊞ Hₖ(V)`, through which the inclusion of reduced homology factors.
  have hB : IsZero ((toSSet.obj (of U)).homology R (k + 1) ⊞
      (toSSet.obj (of V)).homology R (k + 1)) :=
    (biprod_isZero_iff _ _).2 ⟨hU₁.of_iso ((reducedSingularHomologySuccIso R k).app _).symm,
      hV₁.of_iso ((reducedSingularHomologySuccIso R k).app _).symm⟩
  have hmono : Mono (δ R hU hV hUV k) :=
    (mayerVietoris_exact₃ R hU hV hUV (k + 1) k).mono_g (hB.eq_of_src _ _)
  -- The inclusion of reduced homology, with its target written as the homology of the singular
  -- simplicial set, the form in which the Mayer–Vietoris sequence is stated.
  let ι : (reducedSingularHomologyFunctor R k).obj (of ↥(U ∩ V)) ⟶
      (toSSet.obj (of ↥(U ∩ V))).homology R k :=
    (reducedSingularHomologyι R k).app (of ↥(U ∩ V))
  have hι : ι ≫ SSet.mayerVietorisToBiprod R
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))) k = 0 := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, SSet.mayerVietorisToBiprod_fst, zero_comp]
      exact ((reducedSingularHomologyι R k).naturality _).symm.trans
        ((hU₀.eq_of_tgt _ 0 =≫ _).trans zero_comp)
    · rw [Category.assoc, SSet.mayerVietorisToBiprod_snd, Preadditive.comp_neg, zero_comp,
        neg_eq_zero]
      exact ((reducedSingularHomologyι R k).naturality _).symm.trans
        ((hV₀.eq_of_tgt _ 0 =≫ _).trans zero_comp)
  have hS := mayerVietoris_exact₁ R hU hV hUV (k + 1) k
  have : Mono (ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R hU hV hUV (k + 1) k)).f := hmono
  obtain ⟨m, hm⟩ := KernelFork.IsLimit.lift' hS.fIsKernel _ hι
  -- The inclusion of the kernel fork `KernelFork.ofι δ _` is `δ`, by definition.
  replace hm : m ≫ mayerVietorisδ R hU hV hUV (k + 1) k = ι := hm
  refine ⟨m, ?_, ?_⟩
  · rw [← cancel_mono (δ R hU hV hUV k), Category.assoc]
    exact (reducedMayerVietorisδ R hU hV hUV k ≫= hm).trans
      ((reducedMayerVietorisδ_comp_ι R hU hV hUV k).trans (Category.id_comp _).symm)
  · rw [← cancel_mono ((reducedSingularHomologyι R k).app (of ↥(U ∩ V))), Category.assoc]
    exact (m ≫= reducedMayerVietorisδ_comp_ι R hU hV hUV k).trans
      (hm.trans (Category.id_comp _).symm)

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
    simp only [ConcreteCategory.hom_ofHom, ContinuousMap.coe_coe,
      IsEmbedding.homeomorphOfSubsetRange_apply_coe, ContinuousMap.inclusion_apply_coe, U, V, eU]
    -- `U ∩ V` is `Subtype.val ⁻¹' (A ∩ B)` by `Set.preimage_inter`, which holds by definition.
    exact (IsEmbedding.homeomorphOfSubsetRange_apply_coe (s := A ∩ B) _ _ x).symm
  have sqV : ofHom (ContinuousMap.inclusion (inter_subset_right (s := U) (t := V))) ≫ iV.hom =
      iUV.hom ≫ ofHom (ContinuousMap.inclusion hDB) := by
    ext x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    dsimp only [iV, iUV]
    rw [isoOfHomeo_hom, isoOfHomeo_hom]
    simp only [ConcreteCategory.hom_ofHom, ContinuousMap.coe_coe,
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

end TopCat
