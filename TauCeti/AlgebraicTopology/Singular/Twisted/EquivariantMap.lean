/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.GroupHomology
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.EquivariantMap

/-!
# Change of groups in twisted homology of quotient covers

An equivariant map `f : E ⟶ F` along a group homomorphism `φ : G →* H`, lying over
`b : B ⟶ C`, and a compatible coefficient map `ξ : A ⟶ Rep.res φ D` induce a map on
twisted chains of the bases. It sends the class of `a ⊗ e` in the summand of a simplex `σ`
to the class of `ξ a ⊗ f e` in the summand of `b ∘ σ`.

The identification of twisted chains with tensor coinvariants of chains of the total spaces
commutes with this map. If the total spaces are contractible, the existing identification with
Mathlib's group homology therefore carries the geometric map to `groupHomology.map φ ξ`.
No injectivity or surjectivity assumption on `φ` is needed.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.8.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.

The algebraic comparison is `MonoidHom.groupHomologyIso_inv_naturality`; the geometric
comparison is `IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.TopCat TauCeti.LocalCoefficientSystem Simplicial

universe u

namespace IsQuotientCoveringMap

variable {E B F C : TopCat.{u}} {p : E ⟶ B} {q : F ⟶ C}
  {G H : Type u} [Group G] [Group H] [MulAction G E] [MulAction H F]
  (hG : IsQuotientCoveringMap p G) (hH : IsQuotientCoveringMap q H)
  (k : Type u) [CommRing k] {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)
  {A : Rep.{u} k G} {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D)

/-- The twisted chain map induced by an equivariant map of quotient covers and a compatible
coefficient map: change coefficients to the pulled-back target system, then push forward. -/
def associatedTwistedChainMap :
    twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) ⟶
      twistedChainComplex.{u, u, u} (hH.associatedLocalSystem k D) :=
  twistedChainComplexCoefficientMap (hG.associatedLocalSystemMapOver k hH f hf b hb ξ) ≫
    twistedChainComplexMap b (hH.associatedLocalSystem k D)

/-- The induced twisted chain map is coefficient change followed by pushforward along `b`. -/
theorem associatedTwistedChainMap_def :
    hG.associatedTwistedChainMap hH k f hf b hb ξ =
      twistedChainComplexCoefficientMap (hG.associatedLocalSystemMapOver k hH f hf b hb ξ) ≫
        twistedChainComplexMap b (hH.associatedLocalSystem k D) :=
  (rfl)

/-- A summand of the twisted chain map sends `⟦a ⊗ e⟧` to `⟦ξ a ⊗ f e⟧` over the image
simplex. -/
@[simp↓]
theorem associatedTwistedChainMap_f_ι_mk_single (n : ℕ) (σ : (TopCat.toSSet.obj B) _⦋n⦌)
    (a : A) (e : p ⁻¹' {(initialVertex σ).as}) (r : k) :
    ((hG.associatedTwistedChainMap hH k f hf b hb ξ).f n).hom
        ((ιTwistedChainComplex (hG.associatedLocalSystem k A) n σ).hom
          (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj (initialVertex σ)) a
            (Finsupp.single e r))) =
      (ιTwistedChainComplex (hH.associatedLocalSystem k D) n
        ((TopCat.toSSet.map b).app _ σ)).hom
          (Rep.coinvariantsTensorMk D ((hH.permutationRepFunctor k).obj
            (initialVertex ((TopCat.toSSet.map b).app _ σ))) (ξ.hom a)
            (Finsupp.single ((CommSq.mk hb.symm).fiberMap (initialVertex σ).as e) r)) := by
  let η := hG.associatedLocalSystemMapOver k hH f hf b hb ξ
  let L := hH.associatedLocalSystem k D
  let v := Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj (initialVertex σ)) a
    (Finsupp.single e r)
  -- Term mode keeps the equal initial-vertex fibres identified across pullback and pushforward.
  exact (congrArg (((twistedChainComplexMap b L).f n).hom)
      (twistedChainComplexCoefficientMap_f_ι_apply η n σ v)).trans
    ((congrArg (fun t ↦ t.hom ((η.app (initialVertex σ)).hom v))
      (ιTwistedChainComplex_twistedChainComplexMap_f b L n σ)).trans
        (congrArg (ιTwistedChainComplex L n ((TopCat.toSSet.map b).app _ σ)).hom
          (hG.associatedLocalSystemMapOver_app_mk_single k hH f hf b hb ξ _ a e r)))

/-- Tensor classes at sheets depend only on the simplex and the underlying sheet, not on the
proof of membership in the fibre. -/
private theorem ι_mk_single_congr {n : ℕ} {σ τ : (TopCat.toSSet.obj C) _⦋n⦌}
    (h : σ = τ) (a : D) (e : q ⁻¹' {(initialVertex σ).as})
    (e' : q ⁻¹' {(initialVertex τ).as}) (he : (e : F) = e') (r : k) :
    (ιTwistedChainComplex (hH.associatedLocalSystem k D) n σ).hom
        (Rep.coinvariantsTensorMk D ((hH.permutationRepFunctor k).obj (initialVertex σ)) a
          (Finsupp.single e r)) =
      (ιTwistedChainComplex (hH.associatedLocalSystem k D) n τ).hom
        (Rep.coinvariantsTensorMk D ((hH.permutationRepFunctor k).obj (initialVertex τ)) a
          (Finsupp.single e' r)) := by
  subst τ
  obtain rfl : e = e' := Subtype.ext he
  rfl

/-- The comparison of twisted chains with tensor coinvariants is natural for equivariant maps
along arbitrary group homomorphisms and compatible coefficient maps. -/
@[reassoc]
theorem coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality_over :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    φ.coinvariantsTensorChainMap ξ (singularChainsRepResMap k f hf) ≫
        (hH.coinvariantsTensorSingularChainsRepIsoTwisted k D).hom =
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom ≫
        hG.associatedTwistedChainMap hH k f hf b hb ξ := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ Rep.coinvariantsTensor_hom_ext
    (LinearMap.ext fun a ↦ singularChains_linearMap_ext fun τ ↦ ?_)
  -- The left route maps the coefficient and the lifted simplex before descending;
  -- the right route descends first, then maps the coefficient and initial sheet.
  have hpush := (singularChainsRepResMap_f_hom_apply k f hf n (simplexChain τ 1)).trans
    (singularChains_map_f_simplexChain f τ 1)
  have hleft := (congrArg ((hH.coinvariantsTensorSingularChainsRepIsoTwisted k D).hom.f n).hom
    ((φ.coinvariantsTensorChainMap_f_mk ξ (singularChainsRepResMap k f hf) n a
      (simplexChain τ 1)).trans
      (congrArg (Rep.coinvariantsTensorMk D _ (ξ.hom a)) hpush))).trans
        (hH.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk k n (ξ.hom a)
          ((TopCat.toSSet.map f).app _ τ))
  have hright := (congrArg ((hG.associatedTwistedChainMap hH k f hf b hb ξ).f n).hom
    (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk k n a τ)).trans
      (hG.associatedTwistedChainMap_f_ι_mk_single hH k f hf b hb ξ n
        ((TopCat.toSSet.map p).app _ τ) a (initialSheet τ) 1)
  have hσ : (TopCat.toSSet.map q).app _ ((TopCat.toSSet.map f).app _ τ) =
      (TopCat.toSSet.map b).app _ ((TopCat.toSSet.map p).app _ τ) := by
    simpa only [Functor.map_comp, NatTrans.comp_app, types_comp_apply] using
      (congrArg (fun t : E ⟶ C ↦ (TopCat.toSSet.map t).app _ τ) hb).symm
  exact hleft.trans ((ι_mk_single_congr hH k hσ (ξ.hom a) _ _
    (CommSq.fiberMap_apply_coe (CommSq.mk hb.symm) _ (initialSheet τ)).symm 1).trans
      hright.symm)

/-- On a contractible free cover, change of groups in twisted homology agrees with Mathlib's
change-of-group map in group homology. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_hom_naturality_over
    [ContractibleSpace E] [ContractibleSpace F] (n : ℕ) :
    HomologicalComplex.homologyMap (hG.associatedTwistedChainMap hH k f hf b hb ξ) n ≫
        (hH.twistedHomologyIsoGroupHomology k D n).hom =
      (hG.twistedHomologyIsoGroupHomology k A n).hom ≫ groupHomology.map φ ξ n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  let := Classical.decEq G
  let := Classical.decEq H
  have hchain : hG.associatedTwistedChainMap hH k f hf b hb ξ ≫
      (hH.coinvariantsTensorSingularChainsRepIsoTwisted k D).inv =
        (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).inv ≫
          φ.coinvariantsTensorChainMap ξ (singularChainsRepResMap k f hf) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality_over hH k f hf b hb ξ,
      Iso.inv_hom_id_assoc]
  rw [twistedHomologyIsoGroupHomology_hom_eq, twistedHomologyIsoGroupHomology_hom_eq]
  -- The resolution complexes are the equivariant singular chains up to unfolding.
  calc
    _ = HomologicalComplex.homologyMap
          ((hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).inv ≫
            φ.coinvariantsTensorChainMap ξ (singularChainsRepResMap k f hf)) n ≫
          (groupHomologyIso D n (singularChainsResolution k F H)).inv :=
      (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans
        (congrArg (fun t ↦ HomologicalComplex.homologyMap t n ≫ _) hchain)
    _ = _ := (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).trans
      ((congrArg (_ ≫ ·) (φ.groupHomologyIso_inv_naturality ξ
        (singularChainsResolution k E G) (singularChainsResolution k F H)
        (singularChainsRepResMap k f hf)
        (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n)).trans
          (Category.assoc _ _ _).symm)

/-- The inverse comparison of group homology with twisted homology on a contractible free cover
is natural for equivariant maps and compatible coefficient maps. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_inv_naturality_over
    [ContractibleSpace E] [ContractibleSpace F] (n : ℕ) :
    groupHomology.map φ ξ n ≫ (hH.twistedHomologyIsoGroupHomology k D n).inv =
      (hG.twistedHomologyIsoGroupHomology k A n).inv ≫
        HomologicalComplex.homologyMap (hG.associatedTwistedChainMap hH k f hf b hb ξ) n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.twistedHomologyIsoGroupHomology_hom_naturality_over hH k f hf b hb ξ n,
    Iso.inv_hom_id_assoc]

end IsQuotientCoveringMap
