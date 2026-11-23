/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Support
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic

/-! # The signed support-local cap connecting square

Capping native relative small cycles with a cocycle `α` and applying the connecting map gives
`(-1)^(p+1)` times the localized cap with `ζ`, the common coboundary of lifts differing by `α`.
-/

public noncomputable section

open CategoryTheory Limits HomologicalComplex MonoidalCategory Simplicial Topology TopologicalSpace

namespace TauCeti
namespace CapMayerVietoris

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {X : TopCat.{0}} (L : ModuleCat.{0} ℤ)
  (S : (TopCat.toSSet.obj X).Subcomplex) (U V W A B C : Opens X)

open _root_.TopCat TopPair

-- These local notations expand to the original native chains, relative chains and cochains.
local notation "C[" U "]" => SSet.chainComplex
  (CategoryTheory.Functor.obj TopCat.toSSet (CategoryTheory.Functor.obj (Opens.toTopCat X) U)) L
local notation "Q[" A "]" => TopPair.singularChainComplex (TopPair.ofSubset (A : Set X)) ℤₘ
local notation "Q⁎[" A "]" => TopPair.singularCochainComplex (TopPair.ofSubset (A : Set X)) ℤₘ ℤ L
local notation "R[" A "]" =>
  SSetPair.chainComplex
    (SSetPair.restrict (CategoryTheory.Functor.obj TopPair.toSSetPair
      (TopPair.ofSubset (A : Set X))) S) ℤₘ

private lemma localized_cap_ambient (hCA : C ≤ A)
    (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    (SSetPair.chainComplexMap (restrictSubsetMap S hCA) ℤₘ).f n ≫
        relativeCapInto L S U A p q n h φ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q =
      (SSetPair.chainComplexMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrictι S) ℤₘ).f n ≫
      ChainComplex.capChain ℤ ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h
          ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCA) ℤₘ).f p ≫ φ) := by
  have hi := congrArg (fun f ↦ f.f n)
    (chainComplexMap_restrictSubsetMap_comp_restrictι (R := ℤₘ) S hCA)
  simp only [HomologicalComplex.comp_f] at hi
  erw [relativeCapInto_inclusion L S U A p q n h (hS n) φ,
    ← Category.assoc, hi, Category.assoc]
  have hn := TopPair.capChain_naturality (TopPair.ofSubsetMap (𝟙 X) hCA)
    ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h φ
  erw [TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id,
    SSet.chainComplexMap_id, Category.comp_id] at hn
  exact congrArg ((SSetPair.chainComplexMap
    ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrictι S) ℤₘ).f n ≫ ·) hn

/-- The difference of the two localized cap chains is the ambient cap of their difference. -/
private lemma restrictSubsetMap_relativeCapInto_sub_eq_capChain (hCA : C ≤ A) (hCB : C ≤ B)
    (hSU : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (hSV : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ V ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ B)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L)
    (ψ : Q[B].X p ⟶ L)
    (θ : Q[C].X p ⟶ L)
    (hθ : (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCA) ℤₘ).f p ≫ φ -
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCB) ℤₘ).f p ≫ ψ = θ) :
    (SSetPair.chainComplexMap (restrictSubsetMap S hCA) ℤₘ).f n ≫
        relativeCapInto L S U A p q n h φ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q -
      (SSetPair.chainComplexMap (restrictSubsetMap S hCB) ℤₘ).f n ≫
        relativeCapInto L S V B p q n h ψ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' V)) L).f q =
    (SSetPair.chainComplexMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrictι S) ℤₘ).f n ≫
      ChainComplex.capChain ℤ ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
        ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h θ := by
  erw [localized_cap_ambient L S U A C hCA hSU p q n h φ,
    localized_cap_ambient L S V B C hCB hSV p q n h ψ, ← Preadditive.comp_sub]
  have hm := (ChainComplex.capChain ℤ
    ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h).map_sub
    ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCA) ℤₘ).f p ≫ φ)
    ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCB) ℤₘ).f p ≫ ψ)
  erw [← hm, hθ]

/-- The localized cap boundary has sign `(-1)^(p+1)` on native cycles. -/
private lemma relativeCapInto_comp_d_eq_zsmul_relativeCapInto
    (hWU : W ≤ U) (hCA : C ≤ A) (hAB : A ≤ B)
    (hSU : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (hSW : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ W ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ B)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L)
    (ζ : Q[B].X (p + 1) ⟶ L)
    (hφ : Q[A].d (p + 1) p ≫ φ =
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).f (p + 1) ≫ ζ) :
    R[C].iCycles (n + 1) ≫
      (SSetPair.chainComplexMap (restrictSubsetMap S hCA) ℤₘ).f (n + 1) ≫
        relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫
          C[U].d (q + 1) q =
      ((-1 : ℤ) ^ (p + 1)) •
        (R[C].iCycles (n + 1) ≫
          (SSetPair.chainComplexMap (restrictSubsetMap S (hCA.trans hAB)) ℤₘ).f (n + 1) ≫
          relativeCapInto L S W B (p + 1) q (n + 1) (by omega) ζ ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hWU))) L).f q) := by
  have hb := relativeCapInto_cycles_comp_d L S U A hSU p q n h φ
  have hm := relativeCapInto_comp_chainComplexMap_homOfLE L S W U B hWU
    (p + 1) q (n + 1) (by omega) (hSW (n + 1)) ζ
  have hc := chainComplexMap_restrictSubsetMap_comp (R := ℤₘ) S hCA hAB
  erw [← HomologicalComplex.cyclesMap_i_assoc, hb, Preadditive.comp_zsmul, hφ,
    ← restrictSubsetMap_relativeCapInto L S U A B hAB (p + 1) q (n + 1) (by omega) ζ]
  congr 1
  erw [HomologicalComplex.cyclesMap_i_assoc]
  erw [← Category.assoc
    ((SSetPair.chainComplexMap (restrictSubsetMap S hCA) ℤₘ).f (n + 1)),
    ← HomologicalComplex.comp_f, hc, hm]

/-- The signed localized boundary, with its target expressed as native cycles. -/
private lemma relativeCapInto_comp_d_eq_zsmul_capIntoCycles
    (hWU : W ≤ U) (hCA : C ≤ A) (hAB : A ≤ B)
    (hSU : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (hSW : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ W ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ B)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L)
    (ζ : Q⁎[B].cycles (p + 1))
    (hφ : Q[A].d (p + 1) p ≫ φ =
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).f (p + 1) ≫
        Q⁎[B].iCycles (p + 1) ζ) :
    R[C].iCycles (n + 1) ≫
      (SSetPair.chainComplexMap (restrictSubsetMap S hCA) ℤₘ).f (n + 1) ≫
        relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫ C[U].d (q + 1) q =
      (((-1 : ℤ) ^ (p + 1)) •
        (HomologicalComplex.cyclesMap
            (SSetPair.chainComplexMap (restrictSubsetMap S (hCA.trans hAB)) ℤₘ) (n + 1) ≫
          capIntoCycles L S W B hSW (p + 1) q (n + 1) (by omega) ζ)) ≫
        C[W].iCycles q ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hWU))) L).f q := by
  conv_rhs =>
    erw [Preadditive.zsmul_comp]
    simp only [Category.assoc]
    erw [capIntoCycles_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
  exact relativeCapInto_comp_d_eq_zsmul_relativeCapInto L S U W A B C
    hWU hCA hAB hSU hSW p q n h φ _ hφ

variable {S U V W A B C}

/-- On native relative small cycles, cap with `α` followed by Mayer–Vietoris δ is
`(-1)^(p+1)` times the cap with `ζ` in the original intersection, for lifts whose difference is `α`.
-/
lemma capCycles_homologyπ_mayerVietorisδ (S : (TopCat.toSSet.obj X).Subcomplex)
    (U V A B C D : Opens X)
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
          (SSetPair.chainComplexMap (restrictSubsetMap S (hCA.trans hAD)) ℤₘ) (n + 1) ≫
        capIntoCycles L S (U ⊓ V) D hSW (p + 1) q (n + 1) (by omega) ζ ≫
        ((TopCat.toSSet.obj ((Opens.toTopCat X).obj (U ⊓ V))).chainComplex L).homologyπ q) := by
  let R := ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrict S).chainComplex ℤₘ
  let CW := (TopCat.toSSet.obj ((Opens.toTopCat X).obj (U ⊓ V))).chainComplex L
  let a := R.iCycles (n + 1) ≫
    (SSetPair.chainComplexMap (restrictSubsetMap S hCA) ℤₘ).f (n + 1) ≫
      relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ
  let b := R.iCycles (n + 1) ≫
    (SSetPair.chainComplexMap (restrictSubsetMap S hCB) ℤₘ).f (n + 1) ≫
      relativeCapInto L S V B p (q + 1) (n + 1) (by omega) ψ
  let w := cyclesMap (SSetPair.chainComplexMap (restrictSubsetMap S (hCA.trans hAD)) ℤₘ) (n + 1) ≫
    capIntoCycles L S (U ⊓ V) D hSW (p + 1) q (n + 1) (by omega) ζ
  let sq := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (U : Set X) (V : Set X)
  have ha := relativeCapInto_comp_d_eq_zsmul_capIntoCycles L S U (U ⊓ V) A D C
    inf_le_left hCA hAD hSU hSW p q n h φ ζ hφ
  have hb := relativeCapInto_comp_d_eq_zsmul_capIntoCycles L S V (U ⊓ V) B D C
    inf_le_right hCB hBD hSV hSW p q n h ψ ζ hψ
  obtain ⟨z, hz⟩ := SSet.exists_cycle_of_chain_lifts L sq.toCommSq q
    (((( -1 : ℤ) ^ (p + 1)) • w) ≫ CW.iCycles q) a b ha hb
  have hd := SSet.homologyπ_mayerVietorisδ_of_chain_lifts L sq q z
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
        chainComplexMap_f_toSmallSingularSubcomplex_ι,
        chainComplexMap_f_toSmallSingularSubcomplex_ι]
    have hcapi := ChainComplex.capCycles_i (k := ℤ)
      ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
      ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p (q + 1) (n + 1) (by omega) α
    conv_rhs => erw [Category.assoc, hcapi, HomologicalComplex.cyclesMap_i_assoc]
    have he := congrArg (R.iCycles (n + 1) ≫ ·)
      (restrictSubsetMap_relativeCapInto_sub_eq_capChain L S U V A B C
        hCA hCB hSU hSV p (q + 1) (n + 1) (by omega) φ ψ _ hα)
    simp only [Preadditive.comp_sub] at he
    -- The native cap abbreviation and relative-chain object are the same literal composites.
    convert he using 1; rfl
  erw [← Category.assoc, ← hzM, Category.assoc,
    ← HomologicalComplex.homologyπ_naturality_assoc,
    TopCat.homologyMap_ι_comp_mayerVietorisδ L U.isOpen V.isOpen
      (congrArg (fun W : Opens X ↦ (W : Set X)) hUV) (q + 1) q rfl, hd]
  exact Preadditive.zsmul_comp _ _ _

end CapMayerVietoris
end TauCeti
