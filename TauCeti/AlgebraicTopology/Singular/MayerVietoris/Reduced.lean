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

end TopCat
