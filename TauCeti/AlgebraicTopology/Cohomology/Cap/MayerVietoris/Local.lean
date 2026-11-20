/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Support
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic

/-! # The signed support-local cap connecting square -/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex MonoidalCategory Simplicial Topology TopologicalSpace

namespace TauCeti
namespace CapMayerVietoris

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] MonoidalPreadditive.monoidalLinearInt

/-- Chain lifts with the same boundary determine a cycle in the union term. -/
private lemma exists_twoLiftCycle {X₁ X₂ X₃ X₄ : SSet.{0}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : CommSq t l r b) (L A : ModuleCat.{0} ℤ) (q : ℕ)
    (w : A ⟶ (X₁.chainComplex L).X q)
    (u : A ⟶ (X₂.chainComplex L).X (q + 1))
    (v : A ⟶ (X₃.chainComplex L).X (q + 1))
    (hu : u ≫ (X₂.chainComplex L).d (q + 1) q = w ≫ (SSet.chainComplexMap t L).f q)
    (hv : v ≫ (X₃.chainComplex L).d (q + 1) q = w ≫ (SSet.chainComplexMap l L).f q) :
    ∃ z : A ⟶ (X₄.chainComplex L).cycles (q + 1),
      u ≫ (SSet.chainComplexMap r L).f (q + 1) -
        v ≫ (SSet.chainComplexMap b L).f (q + 1) = z ≫ (X₄.chainComplex L).iCycles (q + 1) := by
  let x := u ≫ (SSet.chainComplexMap r L).f (q + 1) -
    v ≫ (SSet.chainComplexMap b L).f (q + 1)
  have hx : x ≫ (X₄.chainComplex L).d (q + 1) q = 0 := by
    dsimp only [x]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc,
      HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm,
      ← Category.assoc, ← Category.assoc, hu, hv]
    apply sub_eq_zero.mpr
    have hs := congrArg (fun f ↦ (SSet.chainComplexMap f L).f q) sq.w
    simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at hs
    simpa only [Category.assoc] using congrArg (w ≫ ·) hs
  exact ⟨(X₄.chainComplex L).liftCycles x q (ChainComplex.next_nat_succ q) hx,
    ((X₄.chainComplex L).liftCycles_i x q (ChainComplex.next_nat_succ q) hx).symm⟩

/-- Two chain lifts with a common boundary compute the native Mayer–Vietoris connecting map. -/
private lemma delta_from_two_lifts {X₁ X₂ X₃ X₄ : SSet.{0}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b) [Mono t] (L A : ModuleCat.{0} ℤ) (q : ℕ)
    (z : A ⟶ (X₄.chainComplex L).cycles (q + 1))
    (w : A ⟶ (X₁.chainComplex L).cycles q)
    (u : A ⟶ (X₂.chainComplex L).X (q + 1))
    (v : A ⟶ (X₃.chainComplex L).X (q + 1))
    (huv : u ≫ (SSet.chainComplexMap r L).f (q + 1) -
        v ≫ (SSet.chainComplexMap b L).f (q + 1) = z ≫ (X₄.chainComplex L).iCycles (q + 1))
    (hu : u ≫ (X₂.chainComplex L).d (q + 1) q =
      w ≫ (X₁.chainComplex L).iCycles q ≫ (SSet.chainComplexMap t L).f q)
    (hv : v ≫ (X₃.chainComplex L).d (q + 1) q =
      w ≫ (X₁.chainComplex L).iCycles q ≫ (SSet.chainComplexMap l L).f q) :
    z ≫ (X₄.chainComplex L).homologyπ (q + 1) ≫ SSet.mayerVietorisδ L sq (q + 1) q rfl =
      w ≫ (X₁.chainComplex L).homologyπ q := by
  let C := (sq.map ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj L)).shortComplex
  let x₂ : A ⟶ C.X₂.X (q + 1) :=
    u ≫ (biprod.inl : X₂.chainComplex L ⟶ X₂.chainComplex L ⊞ X₃.chainComplex L).f (q + 1) -
      v ≫ (biprod.inr : X₃.chainComplex L ⟶ X₂.chainComplex L ⊞ X₃.chainComplex L).f (q + 1)
  have hx₂ : x₂ ≫ C.g.f (q + 1) = z ≫ (X₄.chainComplex L).iCycles (q + 1) := by
    change (u ≫ _ - v ≫ _) ≫ (biprod.desc
      (SSet.chainComplexMap r L) (SSet.chainComplexMap b L)).f (q + 1) = _
    simpa only [Preadditive.sub_comp, Category.assoc,
      biprod_inl_desc_f, biprod_inr_desc_f] using huv
  have hx₁ : w ≫ (X₁.chainComplex L).iCycles q ≫ C.f.f q =
      x₂ ≫ C.X₂.d (q + 1) q := by
    change w ≫ _ ≫ (biprod.lift (SSet.chainComplexMap t L)
        (-SSet.chainComplexMap l L)).f q =
      (u ≫ (biprod.inl : X₂.chainComplex L ⟶ X₂.chainComplex L ⊞ X₃.chainComplex L).f (q + 1) -
        v ≫ (biprod.inr : X₃.chainComplex L ⟶ X₂.chainComplex L ⊞ X₃.chainComplex L).f (q + 1)) ≫
          (X₂.chainComplex L ⊞ X₃.chainComplex L).d (q + 1) q
    apply HomologicalComplex.biprodX_ext_to
    · simp only [Category.assoc, biprod_lift_fst_f, Preadditive.sub_comp,
        ← HomologicalComplex.Hom.comm, HomologicalComplex.biprod_inl_fst_f_assoc,
        HomologicalComplex.biprod_inr_fst_f_assoc, zero_comp, comp_zero, sub_zero]
      exact hu.symm
    · simp only [Category.assoc, biprod_lift_snd_f, HomologicalComplex.neg_f_apply,
        Preadditive.comp_neg, Preadditive.sub_comp, ← HomologicalComplex.Hom.comm,
        HomologicalComplex.biprod_inl_snd_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
        zero_comp, comp_zero, zero_sub]
      exact congrArg Neg.neg hv.symm
  ext x
  have he := (SSet.shortExact_mayerVietorisShortComplex L sq).moduleCat_δ_homologyπ
    (q + 1) q rfl (z x) (x₂ x)
    (ConcreteCategory.congr_hom hx₂ x) (w x) (ConcreteCategory.congr_hom hx₁ x)
  change (SSet.mayerVietorisδ L sq (q + 1) q rfl).hom
      ((X₄.chainComplex L).homologyπ (q + 1) (z x)) =
    (X₁.chainComplex L).homologyπ q (w x)
  rw [SSet.mayerVietorisδ_def L sq (q + 1) q rfl]
  exact he


variable {X : TopCat.{0}} (L : ModuleCat.{0} ℤ)

private lemma small_chain_inclusion {ι : Type} (L : ModuleCat.{0} ℤ)
    (F : ι → Set X) {A : Set X} {i : ι} (hA : A ⊆ F i) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSmallSingularSubcomplex F hA) L).f n ≫
      (SSet.chainComplexMap (X.smallSingularSubcomplex F).ι L).f n =
      (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal A))) L).f n := by
  have hc := congrArg (fun f ↦ (SSet.chainComplexMap f L).f n)
    (TopCat.toSmallSingularSubcomplex_ι F hA)
  simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using hc

lemma signed_cap_boundary_on_cycles (S : (TopCat.toSSet.obj X).Subcomplex) (U V A B C D : Opens X)
    (hUV : U ⊔ V = ⊤) (hCA : C ≤ A) (hCB : C ≤ B) (hAD : A ≤ D) (hBD : B ≤ D)
    (hSU : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (hSV : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ V ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ B)
    (hSW : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ (U ⊓ V : Opens X) ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ D)
    (p q n : ℕ) (h : p + q = n)
    (φ : ((TopPair.ofSubset (A : Set X)).singularChainComplex ℤₘ).X p ⟶ L)
    (ψ : ((TopPair.ofSubset (B : Set X)).singularChainComplex ℤₘ).X p ⟶ L)
    (α : ((TopPair.ofSubset (C : Set X)).singularCochainComplex ℤₘ ℤ L).cycles p)
    (ζ : ((TopPair.ofSubset (D : Set X)).singularCochainComplex ℤₘ ℤ L).cycles (p + 1))
    (hφ : ((TopPair.ofSubset (A : Set X)).singularChainComplex ℤₘ).d (p + 1) p ≫ φ =
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAD) ℤₘ).f (p + 1) ≫
        ((TopPair.ofSubset (D : Set X)).singularCochainComplex ℤₘ ℤ L).iCycles (p + 1) ζ)
    (hψ : ((TopPair.ofSubset (B : Set X)).singularChainComplex ℤₘ).d (p + 1) p ≫ ψ =
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hBD) ℤₘ).f (p + 1) ≫
        ((TopPair.ofSubset (D : Set X)).singularCochainComplex ℤₘ ℤ L).iCycles (p + 1) ζ)
    (hα : (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCA) ℤₘ).f p ≫ φ -
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCB) ℤₘ).f p ≫ ψ =
        ((TopPair.ofSubset (C : Set X)).singularCochainComplex ℤₘ ℤ L).iCycles p α) :
    HomologicalComplex.cyclesMap
        (SSetPair.chainComplexMap
          ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrictι S) ℤₘ) (n + 1) ≫
      ChainComplex.capCycles ℤ
        ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
        ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p (q + 1) (n + 1) (by omega) α ≫
        ((TopCat.toSSet.obj X).chainComplex L).homologyπ (q + 1) ≫
        TopCat.mayerVietorisδ L U.isOpen V.isOpen
          (congrArg (fun W : Opens X ↦ (W : Set X)) hUV) (q + 1) q rfl =
    ((-1 : ℤ) ^ (p + 1)) •
      (HomologicalComplex.cyclesMap
          (SSetPair.chainComplexMap (changeSupport S (hCA.trans hAD)) ℤₘ) (n + 1) ≫
        capIntoCycles L S (U ⊓ V) D hSW (p + 1) q (n + 1) (by omega) ζ ≫
        ((TopCat.toSSet.obj ((Opens.toTopCat X).obj (U ⊓ V))).chainComplex L).homologyπ q) := by
  let R := ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrict S).chainComplex ℤₘ
  let CW := (TopCat.toSSet.obj ((Opens.toTopCat X).obj (U ⊓ V))).chainComplex L
  let qD := SSetPair.chainComplexMap (changeSupport S (hCA.trans hAD)) ℤₘ
  let a := R.iCycles (n + 1) ≫
    (SSetPair.chainComplexMap (changeSupport S hCA) ℤₘ).f (n + 1) ≫
      relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ
  let b := R.iCycles (n + 1) ≫
    (SSetPair.chainComplexMap (changeSupport S hCB) ℤₘ).f (n + 1) ≫
      relativeCapInto L S V B p (q + 1) (n + 1) (by omega) ψ
  let w := HomologicalComplex.cyclesMap qD (n + 1) ≫
    capIntoCycles L S (U ⊓ V) D hSW (p + 1) q (n + 1) (by omega) ζ
  let sq := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (U : Set X) (V : Set X)
  have ha := localized_boundary_cycles L S U (U ⊓ V) A D C inf_le_left hCA hAD hSU hSW
    p q n h φ ζ hφ
  have hb := localized_boundary_cycles L S V (U ⊓ V) B D C inf_le_right hCB hBD hSV hSW
    p q n h ψ ζ hψ
  obtain ⟨z, hz⟩ := exists_twoLiftCycle sq.toCommSq L (R.cycles (n + 1)) q
    (((( -1 : ℤ) ^ (p + 1)) • w) ≫ CW.iCycles q) a b ha hb
  have hd := delta_from_two_lifts sq L (R.cycles (n + 1)) q z
    (((-1 : ℤ) ^ (p + 1)) • w) a b hz ha hb
  have hzM : z ≫ HomologicalComplex.cyclesMap
        (SSet.chainComplexMap (X.smallSingularSubcomplex ![(U : Set X), (V : Set X)]).ι L)
        (q + 1) =
      HomologicalComplex.cyclesMap
        (SSetPair.chainComplexMap
          ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrictι S) ℤₘ) (n + 1) ≫
        ChainComplex.capCycles ℤ
          ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom)
          p (q + 1) (n + 1) (by omega) α := by
    rw [← cancel_mono (((TopCat.toSSet.obj X).chainComplex L).iCycles (q + 1))]
    conv_lhs =>
      erw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, ← hz,
        Preadditive.sub_comp, Category.assoc a, Category.assoc b,
        small_chain_inclusion, small_chain_inclusion]
    have hcapi := ChainComplex.capCycles_i (k := ℤ)
      ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
      ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p (q + 1) (n + 1) (by omega) α
    conv_rhs => erw [Category.assoc, hcapi, HomologicalComplex.cyclesMap_i_assoc]
    have he := congrArg (R.iCycles (n + 1) ≫ ·)
      (localized_cap_sub L S U V A B C hCA hCB hSU hSV p (q + 1) (n + 1) (by omega) φ ψ _ hα)
    simp only [Preadditive.comp_sub] at he
    convert he using 1; rfl
  erw [← Category.assoc, ← hzM, Category.assoc,
    ← HomologicalComplex.homologyπ_naturality_assoc,
    TopCat.homologyMap_ι_comp_mayerVietorisδ L U.isOpen V.isOpen
      (congrArg (fun W : Opens X ↦ (W : Set X)) hUV) (q + 1) q rfl, hd]
  exact Preadditive.zsmul_comp _ _ _

end CapMayerVietoris
end TauCeti
