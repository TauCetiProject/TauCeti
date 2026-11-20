/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-! # Support-local cap products on native relative chains

`relativeCapInto`, `capIntoCycles` and `capIntoHomology` localize the cap product in an open
subspace. Their support-change and boundary laws use the native relative small-chain quotient.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial Topology TopologicalSpace

namespace TauCeti
namespace CapMayerVietoris

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {X : TopCat.{0}} (L : ModuleCat.{0} ℤ)
  (S : (TopCat.toSSet.obj X).Subcomplex) (U V W A B C : Opens X)

-- These local notations expand to the original native chains, relative chains and cochains.
local notation "C[" U "]" => SSet.chainComplex
  (CategoryTheory.Functor.obj TopCat.toSSet (CategoryTheory.Functor.obj (Opens.toTopCat X) U)) L
local notation "Q[" A "]" => TopPair.singularChainComplex (TopPair.ofSubset (A : Set X)) ℤₘ
local notation "Q⁎[" A "]" => TopPair.singularCochainComplex (TopPair.ofSubset (A : Set X)) ℤₘ ℤ L
local notation "R[" A "]" =>
  SSetPair.chainComplex
    (SSetPair.restrict (CategoryTheory.Functor.obj TopPair.toSSetPair
      (TopPair.ofSubset (A : Set X))) S) ℤₘ

private def cap (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L) :
    ((TopCat.toSSet.obj X).chainComplex ℤₘ).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex L).X q :=
  ChainComplex.capChain ℤ (X.alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h φ

/-- Capping subordinate chains in an open subspace, with zero for unsupported simplices. -/
def capInto (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L) :
    ((S : SSet).chainComplex ℤₘ).X n ⟶
      C[U].X q :=
  by
  classical
  exact (S.toSSet.isColimitChainComplexXCofan ℤₘ n).desc
    (Cofan.mk _ fun σ ↦
    if hσ : Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U then
      (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).ιChainComplex
          (TopCat.toSSetObjCodRestrict σ.val hσ) ≫
        cap L p q n h
          ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) ℤₘ).f p ≫ φ)
    else 0)

private lemma cap_naturality {Y : TopCat.{0}} (f : X ⟶ Y)
    (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj Y).chainComplex ℤₘ).X p ⟶ L) :
    cap L p q n h
        ((SSet.chainComplexMap (TopCat.toSSet.map f) ℤₘ).f p ≫ φ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) L).f q =
      (SSet.chainComplexMap (TopCat.toSSet.map f) ℤₘ).f n ≫ cap L p q n h φ := by
  exact ChainComplex.capChain_naturality _ _ _ _ _ _ _ _
    (TopCat.alexanderWhitneyDiagonal_naturality f (ρ_ ℤₘ).inv)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map f) (ρ_ L).hom).symm p q n h φ

private lemma ι_capInto (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L)
    (σ : (S : SSet) _⦋n⦌) :
    S.toSSet.ιChainComplex σ ≫ capInto L S U p q n h φ =
      letI := Classical.propDecidable (Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U)
      if hσ : Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U then
        (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).ιChainComplex
            (TopCat.toSSetObjCodRestrict σ.val hσ) ≫
          cap L p q n h
            ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) ℤₘ).f p ≫ φ)
      else 0 := by
  classical
  exact (S.toSSet.isColimitChainComplexXCofan ℤₘ n).fac _ ⟨σ⟩

/-- A cap chain supported in an open subspace has its actual inclusion into ambient chains. -/
private lemma capInto_inclusion (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L)
    (hφ : ∀ (σ : (S : SSet) _⦋n⦌),
      ¬ Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U → (TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ.val) ≫
            φ = 0) :
    capInto L S U p q n h φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q =
      (SSet.chainComplexMap S.ι ℤₘ).f n ≫ cap L p q n h φ := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_capInto]
  split_ifs with hσ
  · rw [Category.assoc, cap_naturality, ← Category.assoc, SSet.ι_chainComplexMap_f,
      TopCat.toSSet_map_inclusion'_toSSetObjCodRestrict]
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    rfl
  · rw [zero_comp, ← Category.assoc, SSet.ι_chainComplexMap_f]
    rw [cap, TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal]
    have he : S.ι.app _ σ = σ.val := rfl
    rw [he, hφ σ hσ]
    simp

private lemma relative_simplex_zero {p : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋p⦌)
    (hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
        ((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p = 0 := by
  have hτ := TopCat.toSSet_map_inclusion'_toSSetObjCodRestrict σ hσ
  -- The source of the relative quotient is the ambient singular set after `toSSetPair` unfolds.
  erw [← hτ, ← SSet.ι_chainComplexMap_f, Category.assoc, ← HomologicalComplex.comp_f]
  have hz := TopPair.chainComplexMap_comp_singularChainComplexπ (TopPair.ofSubset (A : Set X)) ℤₘ
  change (TopCat.toSSet.obj ((Opens.toTopCat X).obj A)).ιChainComplex _ ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' A)) ℤₘ ≫ _).f p = 0
  erw [hz]
  exact comp_zero

private lemma face_range_subset (A : Set X) {m n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A)
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).map f.op σ)) ⊆ A := by
  rintro _ ⟨z, rfl⟩
  rw [TopCat.toSSetObjEquiv_naturality_apply]
  exact hσ ⟨_, rfl⟩

private lemma capInto_inclusion_relative (p q n : ℕ) (h : p + q = n)
    (hS : ∀ (σ : (S : SSet) _⦋n⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (φ : Q[A].X p ⟶ L) :
    capInto L S U p q n h
        (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q =
      (SSet.chainComplexMap S.ι ℤₘ).f n ≫
        cap L p q n h
          (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ) := by
  apply capInto_inclusion
  intro σ hσ
  obtain hA := (hS σ).resolve_left hσ
  -- The quotient source is definitionally the ambient singular chains, through `toSSetPair`.
  erw [← Category.assoc, relative_simplex_zero A _ (face_range_subset _ _ hA _), zero_comp]

private lemma cap_zero (p q n : ℕ) (h : p + q = n) :
    cap (X := X) L p q n h 0 = 0 :=
  (ChainComplex.capChain ℤ (X.alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h).map_zero

private lemma capInto_zero_of_front (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L)
    (σ : S.toSSet _⦋n⦌)
    (hφ : (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ.val) ≫
          φ = 0) :
    S.toSSet.ιChainComplex σ ≫ capInto L S U p q n h φ = 0 := by
  classical
  rw [ι_capInto]
  split_ifs with hσ
  · have : Mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q) :=
      inferInstanceAs (Mono ((SSet.chainComplexMap
        (TopPair.toSSetPair.obj (TopPair.ofSubset (U : Set X))).hom L).f q))
    apply (cancel_mono
      ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q)).1
    rw [Category.assoc, cap_naturality, ← Category.assoc, SSet.ι_chainComplexMap_f,
      TopCat.toSSet_map_inclusion'_toSSetObjCodRestrict, cap,
      TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal, hφ]
    simp
  · rfl

private lemma relative_capInto_zero (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    (SSet.chainComplexMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).hom ℤₘ).f n ≫
      capInto L S U p q n h
        (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ) = 0 := by
  apply SSet.chainComplex_hom_ext
  intro τ
  erw [← Category.assoc, SSet.ι_chainComplexMap_f]
  apply capInto_zero_of_front
  have hA := (TopPair.mem_range_restrict_hom_app_iff (TopPair.ofSubset (A : Set X)) S
    (((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).hom.app _ τ)).1
    ⟨τ, rfl⟩
  rw [TopPair.range_ofSubset_map] at hA
  erw [← Category.assoc, relative_simplex_zero A _ (face_range_subset _ _ hA _), zero_comp]

/-- The support-local cap on the original relative small chains. -/
def relativeCapInto (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    R[A].X n ⟶
      C[U].X q :=
  (SSetPair.isColimitCokernelCoforkChainComplexX
      ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S) ℤₘ n).desc
    (CokernelCofork.ofπ
      (capInto L S U p q n h
        (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ))
      (relative_capInto_zero L S U A p q n h φ))

@[reassoc]
private lemma π_relativeCapInto (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).chainComplexπ
        ℤₘ).f n) ≫ relativeCapInto L S U A p q n h φ =
      capInto L S U p q n h
        (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ) := by
  exact (SSetPair.isColimitCokernelCoforkChainComplexX
    ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S) ℤₘ n).fac
      (CokernelCofork.ofπ _ (relative_capInto_zero L S U A p q n h φ))
      WalkingParallelPair.one

private lemma relativeCapInto_inclusion (p q n : ℕ) (h : p + q = n)
    (hS : ∀ (σ : (S : SSet) _⦋n⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (φ : Q[A].X p ⟶ L) :
    relativeCapInto L S U A p q n h φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q =
      (SSetPair.chainComplexMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ).f n ≫
        ChainComplex.capChain ℤ
          ((TopPair.ofSubset (A : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h φ := by
  let P := TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))
  erw [← cancel_epi (((P.restrict S).chainComplexπ ℤₘ).f n)]
  erw [← Category.assoc, π_relativeCapInto, capInto_inclusion_relative L S U A p q n h hS]
  have hπ := SSetPair.chainComplexπ_naturality ℤₘ (P.restrictι S)
  have hc := TopPair.singularChainComplexπ_capChain_alexanderWhitneyDiagonal
    (TopPair.ofSubset (A : Set X)) ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h φ
  have hπn := congrArg (fun f ↦ f.f n) hπ
  simp only [HomologicalComplex.comp_f] at hπn
  erw [← Category.assoc, ← hπn, Category.assoc]
  have hr := SSetPair.restrictι_right P S
  erw [hr]
  -- The quotient and its restricted ambient object reduce through the native pair functors.
  change (SSet.chainComplexMap S.ι ℤₘ).f n ≫
      cap L p q n h
        (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ) = _
  convert congrArg ((SSet.chainComplexMap S.ι ℤₘ).f n ≫ ·)
    hc.symm using 1
  rfl

section Subordinate

variable (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
  Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨ Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
  (p q n : ℕ) (h : p + q = n)

include hS

private lemma relativeCapInto_comp_d (φ : Q[A].X p ⟶ L) :
    relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫
        C[U].d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        (R[A].d (n + 1) n ≫ relativeCapInto L S U A p q n h φ -
          relativeCapInto L S U A (p + 1) q (n + 1) (by omega)
            (Q[A].d (p + 1) p ≫ φ)) := by
  have : Mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q) :=
    inferInstanceAs (Mono ((SSet.chainComplexMap
      (TopPair.toSSetPair.obj (TopPair.ofSubset (U : Set X))).hom L).f q))
  have htop := relativeCapInto_inclusion L S U A p (q + 1) (n + 1)
    (by omega) (hS (n + 1)) φ
  have hlow := relativeCapInto_inclusion L S U A p q n h (hS n) φ
  have hder := relativeCapInto_inclusion L S U A (p + 1) q (n + 1)
    (by omega) (hS (n + 1))
    (Q[A].d (p + 1) p ≫ φ)
  have hb := ChainComplex.capChain_comp_d (k := ℤ)
    ((TopPair.ofSubset (A : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h φ
  rw [← cancel_mono
    ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q)]
  erw [Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc, htop]
  erw [Preadditive.zsmul_comp, Preadditive.sub_comp]
  simp only [Category.assoc]
  erw [hlow, hder, hb, Preadditive.comp_zsmul, Preadditive.comp_sub]
  congr 2
  erw [← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc]

private lemma relativeCapInto_cycles_comp_d (φ : Q[A].X p ⟶ L) :
    R[A].iCycles (n + 1) ≫
      relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫
        C[U].d (q + 1) q =
      ((-1 : ℤ) ^ (p + 1)) •
        (R[A].iCycles (n + 1) ≫
          relativeCapInto L S U A (p + 1) q (n + 1) (by omega)
            (Q[A].d (p + 1) p ≫ φ)) := by
  erw [relativeCapInto_comp_d L S U A hS p q n h φ,
    Preadditive.comp_zsmul, Preadditive.comp_sub, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp, zero_sub]
  simp [pow_succ]

omit hS in
private lemma capInto_zero (p q n : ℕ) (h : p + q = n) : capInto L S U p q n h 0 = 0 := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_capInto]
  split_ifs <;> simp only [comp_zero, cap_zero]

omit hS in
private lemma relativeCapInto_zero
    (p q n : ℕ) (h : p + q = n) : relativeCapInto L S U A p q n h 0 = 0 := by
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).chainComplexπ
      ℤₘ).f n), π_relativeCapInto, comp_zero, comp_zero, capInto_zero]
  rfl

/-- The support-local cap with a cocycle sends native cycles to cycles. -/
def capIntoCycles (φ : Q⁎[A].cycles p) :
    R[A].cycles n ⟶
      C[U].cycles q :=
  C[U].liftCycles
    (R[A].iCycles n ≫
      relativeCapInto L S U A p q n h
        (Q⁎[A].iCycles p φ))
    ((ComplexShape.down ℕ).next q) rfl (by
      cases q with
      | zero => rw [HomologicalComplex.shape _ _ _ (by simp), comp_zero]
      | succ q =>
        obtain rfl : n = p + q + 1 := by omega
        rw [ChainComplex.next_nat_succ]
        erw [relativeCapInto_cycles_comp_d L S U A hS p q (p + q) rfl,
          ChainComplex.d_comp_linearYonedaObj_iCycles,
          relativeCapInto_zero, comp_zero, smul_zero])

@[reassoc]
lemma capIntoCycles_i (φ : Q⁎[A].cycles p) :
    capIntoCycles L S U A hS p q n h φ ≫
        C[U].iCycles q =
      R[A].iCycles n ≫
        relativeCapInto L S U A p q n h
          (Q⁎[A].iCycles p φ) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

private lemma relativeCapInto_comp_d_of_cycles (φ : Q⁎[A].cycles p) :
    relativeCapInto L S U A p (q + 1) (n + 1) (by omega)
        (Q⁎[A].iCycles p φ) ≫
        C[U].d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        (R[A].d (n + 1) n ≫
          relativeCapInto L S U A p q n h
            (Q⁎[A].iCycles p φ)) := by
  have hc := relativeCapInto_comp_d L S U A hS p q n h
    (Q⁎[A].iCycles p φ)
  have hd : Q[A].d (p + 1) p ≫
      Q⁎[A].iCycles p φ =
      (0 : Q[A].X (p + 1) ⟶ L) :=
    ChainComplex.d_comp_linearYonedaObj_iCycles p (p + 1) φ
  have hz := relativeCapInto_zero L S U A (p + 1) q (n + 1) (by omega)
  have hcapzero := (congrArg (relativeCapInto L S U A (p + 1) q (n + 1)
    (by omega)) hd).trans hz
  simpa only [hcapzero, sub_zero] using hc

private lemma toCycles_capIntoCycles (φ : Q⁎[A].cycles p) :
    R[A].toCycles (n + 1) n ≫
        capIntoCycles L S U A hS p q n h φ =
      (((-1 : ℤ) ^ p) • relativeCapInto L S U A p (q + 1) (n + 1) (by omega)
        (Q⁎[A].iCycles p φ)) ≫
            C[U].toCycles (q + 1) q := by
  erw [← cancel_mono
    (C[U].iCycles q)]
  erw [Category.assoc, capIntoCycles_i, HomologicalComplex.toCycles_i_assoc,
    Category.assoc, HomologicalComplex.toCycles_i, Preadditive.zsmul_comp,
    relativeCapInto_comp_d_of_cycles L S U A hS p q n h φ]
  simp [smul_smul, ← mul_pow]

/-- The cap with a cocycle descends to the native homology quotient. -/
def capIntoHomology (φ : Q⁎[A].cycles p) :
    R[A].homology n ⟶
      C[U].homology q :=
  (CokernelCofork.IsColimit.desc'
    (R[A].homologyIsCokernel (n + 1) n (by simp))
    (capIntoCycles L S U A hS p q n h φ ≫
      C[U].homologyπ q)
    (by rw [← Category.assoc, toCycles_capIntoCycles, Category.assoc,
        HomologicalComplex.toCycles_comp_homologyπ, comp_zero])).1

@[reassoc]
lemma homologyπ_capIntoHomology (φ : Q⁎[A].cycles p) :
    R[A].homologyπ n ≫ capIntoHomology L S U A hS p q n h φ =
      capIntoCycles L S U A hS p q n h φ ≫
        C[U].homologyπ q :=
  (CokernelCofork.IsColimit.desc'
    (R[A].homologyIsCokernel (n + 1) n (by simp)) _ _).2

end Subordinate

private lemma relativeCap_naturality {P P' : TopPair.{0}} (f : P ⟶ P')
    (p q n : ℕ) (h : p + q = n)
    (φ : (P'.singularChainComplex ℤₘ).X p ⟶ L) :
    (TopPair.singularChainComplexMap f ℤₘ).f n ≫
        ChainComplex.capChain ℤ (P'.alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj P'.fst).chainComplexPairing (ρ_ L).hom) p q n h φ =
      ChainComplex.capChain ℤ (P.alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ L).hom) p q n h
          ((TopPair.singularChainComplexMap f ℤₘ).f p ≫ φ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) L).f q :=
  (ChainComplex.capChain_naturality _ _ _ _ _ _ _ _
    (TopPair.alexanderWhitneyDiagonal_naturality f (ρ_ ℤₘ).inv)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map (TopPair.Hom.fst f))
      (ρ_ L).hom).symm p q n h φ).symm

/-- The original subspace paired with the inverse image of the relative subset. -/
abbrev sourcePair : TopPair.{0} :=
  TopPair.ofSubset (Opens.inclusion' U ⁻¹' (A : Set X))

/-- The map of original relative pairs induced by the open inclusion. -/
def inclusionPairMap :
    sourcePair U A ⟶ TopPair.ofSubset (A : Set X) :=
  TopPair.ofSubsetMap (Opens.inclusion' U) (fun _ hx ↦ hx)

/-- The actual pair map is induced by the original open inclusion. -/
lemma inclusionPairMap_def :
    inclusionPairMap U A = TopPair.ofSubsetMap (Opens.inclusion' U) (fun _ hx ↦ hx) := by
  rfl

/-- The ambient component of the native pair map is the open inclusion. -/
@[simp]
lemma inclusionPairMap_fst :
    TopPair.Hom.fst (inclusionPairMap U A) = Opens.inclusion' U := by
  erw [inclusionPairMap, TopPair.ofSubsetMap_fst]

section Subspace

variable (T : (TopPair.toSSetPair.obj (sourcePair U A)).right.Subcomplex)
  (hT : T ≤ S.preimage (TopPair.toSSetPair.map (inclusionPairMap U A)).right)
  (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
    Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨ Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
  (p q n : ℕ) (h : p + q = n)

include hT hS

private lemma capInto_subspace_chains (φ : Q[A].X p ⟶ L) :
    (SSetPair.chainComplexMap
        (SSetPair.restrictMap (TopPair.toSSetPair.map (inclusionPairMap U A)) hT)
        ℤₘ).f n ≫ relativeCapInto L S U A p q n h φ =
      (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T) ℤₘ).f n ≫
        ChainComplex.capChain ℤ ((sourcePair U A).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplexPairing (ρ_ L).hom) p q n h
          ((TopPair.singularChainComplexMap (inclusionPairMap U A) ℤₘ).f p ≫ φ) := by
  have : Mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q) :=
    inferInstanceAs (Mono ((SSet.chainComplexMap
      (TopPair.toSSetPair.obj (TopPair.ofSubset (U : Set X))).hom L).f q))
  rw [← cancel_mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q)]
  simp only [Category.assoc]
  erw [relativeCapInto_inclusion L S U A p q n h (hS n) φ]
  have hc := congrArg (fun f ↦ (SSetPair.chainComplexMap f ℤₘ).f n)
    (SSetPair.restrictMap_comp_restrictι (TopPair.toSSetPair.map (inclusionPairMap U A)) hT)
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at hc
  erw [← Category.assoc, hc, Category.assoc, relativeCap_naturality]
  erw [inclusionPairMap, TopPair.ofSubsetMap_fst]
  rfl

private lemma capInto_subspace_cycles (φ : Q⁎[A].cycles p) :
    HomologicalComplex.cyclesMap (SSetPair.chainComplexMap
        (SSetPair.restrictMap (TopPair.toSSetPair.map (inclusionPairMap U A)) hT)
        ℤₘ) n ≫ capIntoCycles L S U A hS p q n h φ =
      HomologicalComplex.cyclesMap
        (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T) ℤₘ) n ≫
        ChainComplex.capCycles ℤ ((sourcePair U A).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplexPairing (ρ_ L).hom) p q n h
          (HomologicalComplex.cyclesMap
            (TopPair.singularCochainComplexMap (inclusionPairMap U A)) p φ) := by
  rw [← cancel_mono
    (C[U].iCycles q)]
  have hleft := capIntoCycles_i L S U A hS p q n h φ
  have hright := ChainComplex.capCycles_i (k := ℤ)
    ((sourcePair U A).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
    ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplexPairing (ρ_ L).hom)
    p q n h (HomologicalComplex.cyclesMap
      (TopPair.singularCochainComplexMap (inclusionPairMap U A)) p φ)
  have hφ := ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply
    (k := ℤ) (TopPair.singularChainComplexMap (inclusionPairMap U A) ℤₘ) p φ
  erw [Category.assoc, hleft, HomologicalComplex.cyclesMap_i_assoc,
    Category.assoc, hright, HomologicalComplex.cyclesMap_i_assoc, hφ]
  erw [capInto_subspace_chains L S U A T hT hS p q n h]

private lemma capInto_subspace_homology (φ : Q⁎[A].cycles p) :
    HomologicalComplex.homologyMap (SSetPair.chainComplexMap
        (SSetPair.restrictMap (TopPair.toSSetPair.map (inclusionPairMap U A)) hT)
        ℤₘ) n ≫ capIntoHomology L S U A hS p q n h φ =
      HomologicalComplex.homologyMap
        (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T) ℤₘ) n ≫
        (sourcePair U A).singularCap ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h
          (((sourcePair U A).singularCochainComplex ℤₘ ℤ L).homologyπ p
            (HomologicalComplex.cyclesMap
              (TopPair.singularCochainComplexMap (inclusionPairMap U A)) p φ)) := by
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj (sourcePair U A)).restrict T).chainComplex ℤₘ).homologyπ n)]
  have hc := capInto_subspace_cycles L S U A T hT hS p q n h φ
  have hr := TopPair.singularCap_homologyπ (sourcePair U A) ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h
    (HomologicalComplex.cyclesMap (TopPair.singularCochainComplexMap (inclusionPairMap U A)) p φ)
  have hl := homologyπ_capIntoHomology L S U A hS p q n h φ
  have hnl := HomologicalComplex.homologyπ_naturality
    (SSetPair.chainComplexMap
      (SSetPair.restrictMap (TopPair.toSSetPair.map (inclusionPairMap U A)) hT) ℤₘ) n
  have hnr := HomologicalComplex.homologyπ_naturality
    (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T) ℤₘ) n
  conv_lhs => erw [← Category.assoc, hnl, Category.assoc, hl]
  conv_rhs => erw [← Category.assoc, hnr, Category.assoc, hr]
  have hc' := congrArg
    (· ≫ C[U].homologyπ q) hc
  simp only [Category.assoc] at hc'
  convert hc' using 1
  rfl

/-- Relative excision identifies the localized cap with the cap in the original subspace. -/
lemma capIntoHomology_of_subspace
    [Mono (SSetPair.homologyMap
      ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ n)]
    [IsIso (SSetPair.homologyMap
      ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T) ℤₘ n)]
    (φ : Q⁎[A].cycles p)
    (z : R[A].homology n)
    (y : ((sourcePair U A).singularChainComplex ℤₘ).homology n)
    (hz : SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ n z =
      TopPair.singularHomologyMap (inclusionPairMap U A) ℤₘ n y) :
    capIntoHomology L S U A hS p q n h φ z =
      ((sourcePair U A).singularCap ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h
        (((sourcePair U A).singularCochainComplex ℤₘ ℤ L).homologyπ p
          (HomologicalComplex.cyclesMap
            (TopPair.singularCochainComplexMap (inclusionPairMap U A)) p φ))).hom y := by
  let j := SSetPair.homologyMap
    ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T) ℤₘ n
  obtain ⟨y', hy'⟩ := (ConcreteCategory.bijective_of_isIso j).surjective y
  have hz' : SSetPair.homologyMap
      (SSetPair.restrictMap (TopPair.toSSetPair.map (inclusionPairMap U A)) hT) ℤₘ n y' = z := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ n)
    rw [hz, ← ConcreteCategory.comp_apply, ← SSetPair.homologyMap_comp]
    erw [SSetPair.restrictMap_comp_restrictι, SSetPair.homologyMap_comp,
      ConcreteCategory.comp_apply]
    exact congrArg (TopPair.singularHomologyMap (inclusionPairMap U A) ℤₘ n) hy'
  rw [← hz']
  have hc := ConcreteCategory.congr_hom
    (capInto_subspace_homology L S U A T hT hS p q n h φ) y'
  have hy'' : HomologicalComplex.homologyMap
      (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (sourcePair U A)).restrictι T)
        ℤₘ) n y' = y := hy'
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hy''] at hc
  exact hc

end Subspace

private lemma subsetMap_right {A B : Set X} (hAB : A ⊆ B) :
    (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) hAB)).right =
      𝟙 (TopCat.toSSet.obj X) := by
  erw [TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst]
  exact CategoryTheory.Functor.map_id _ _

private lemma chains_id (S : SSet.{0}) (R : ModuleCat.{0} ℤ) :
    SSet.chainComplexMap (𝟙 S) R = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

private lemma chains_comp {A B C : SSet.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (R : ModuleCat.{0} ℤ) :
    SSet.chainComplexMap f R ≫ SSet.chainComplexMap g R = SSet.chainComplexMap (f ≫ g) R :=
  (CategoryTheory.Functor.map_comp _ _ _).symm

/-- Enlarging the relative subset induces a map of the native restricted pairs. -/
def changeSupport
    {A B : Set X} (hAB : A ⊆ B) :
    (TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrict S ⟶
      (TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrict S :=
  SSetPair.restrictMap (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) hAB)) (by
    erw [subsetMap_right, SSet.Subcomplex.preimage_id]
    exact le_refl S)

private lemma changeSupport_right
    {A B : Set X} (hAB : A ⊆ B) : (changeSupport S hAB).right = 𝟙 S.toSSet := by
  ext i σ
  apply Subtype.ext
  erw [changeSupport, SSetPair.restrictMap_right_app_coe]
  erw [subsetMap_right]
  rfl

private lemma π_changeSupport
    {A B : Set X} (hAB : A ⊆ B) :
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrict S).chainComplexπ ℤₘ ≫
      SSetPair.chainComplexMap (changeSupport S hAB) ℤₘ =
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrict S).chainComplexπ ℤₘ := by
  erw [← SSetPair.chainComplexπ_naturality, changeSupport_right, chains_id, Category.id_comp]

private lemma relativeCapInto_changeSupport (hAB : A ≤ B)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[B].X p ⟶ L) :
    (SSetPair.chainComplexMap (changeSupport S hAB) ℤₘ).f n ≫
        relativeCapInto L S U B p q n h φ =
      relativeCapInto L S U A p q n h
        ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).f p ≫ φ) := by
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).chainComplexπ ℤₘ).f n)]
  have hn := congrArg (fun f ↦ f.f n) (π_changeSupport S hAB)
  simp only [HomologicalComplex.comp_f] at hn
  erw [← Category.assoc, hn, π_relativeCapInto, π_relativeCapInto]
  have hp0 : (TopPair.ofSubset (A : Set X)).singularChainComplexπ
      ℤₘ ≫ TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ =
      (TopPair.ofSubset (B : Set X)).singularChainComplexπ ℤₘ := by
    have hn := SSetPair.chainComplexπ_naturality ℤₘ
      (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) hAB))
    erw [subsetMap_right, chains_id, Category.id_comp] at hn
    exact hn.symm
  have hp := congrArg (fun f ↦ f.f p) hp0
  simp only [HomologicalComplex.comp_f] at hp
  erw [← Category.assoc, hp]

/-- Support change commutes with the original relative-chain inclusion. -/
lemma changeSupport_inclusion
    {A B : Set X} (hAB : A ⊆ B) :
    SSetPair.chainComplexMap (changeSupport S hAB) ℤₘ ≫
      SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrictι S) ℤₘ =
    SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrictι S) ℤₘ ≫
      TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ := by
  have hc : changeSupport S hAB ≫ (TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrictι S =
      (TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrictι S ≫
        TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) hAB) :=
    SSetPair.restrictMap_comp_restrictι _ _
  have h := congrArg (fun f ↦ SSetPair.chainComplexMap f ℤₘ) hc
  simpa only [CategoryTheory.Functor.map_comp] using h

private lemma relativeCap_id_naturality {A B : Set X} (hAB : A ⊆ B)
    (p q n : ℕ) (h : p + q = n)
    (φ : ((TopPair.ofSubset B).singularChainComplex ℤₘ).X p ⟶ L) :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).f n ≫
        ChainComplex.capChain ℤ ((TopPair.ofSubset B).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h φ =
      ChainComplex.capChain ℤ ((TopPair.ofSubset A).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h
          ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).f p ≫ φ) := by
  have hc := relativeCap_naturality L (TopPair.ofSubsetMap (𝟙 X) hAB) p q n h φ
  erw [TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id, chains_id,
    Category.comp_id] at hc
  exact hc

private lemma localized_cap_ambient (hCA : C ≤ A)
    (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    (SSetPair.chainComplexMap (changeSupport S hCA) ℤₘ).f n ≫
        relativeCapInto L S U A p q n h φ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q =
      (SSetPair.chainComplexMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set X))).restrictι S) ℤₘ).f n ≫
      ChainComplex.capChain ℤ ((TopPair.ofSubset (C : Set X)).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h
          ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hCA) ℤₘ).f p ≫ φ) := by
  have hi := congrArg (fun f ↦ f.f n) (changeSupport_inclusion S hCA)
  simp only [HomologicalComplex.comp_f] at hi
  erw [relativeCapInto_inclusion L S U A p q n h (hS n) φ,
    ← Category.assoc, hi, Category.assoc, relativeCap_id_naturality]

/-- The difference of the two localized cap chains is the ambient cap of their difference. -/
lemma localized_cap_sub (hCA : C ≤ A) (hCB : C ≤ B)
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
    (SSetPair.chainComplexMap (changeSupport S hCA) ℤₘ).f n ≫
        relativeCapInto L S U A p q n h φ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q -
      (SSetPair.chainComplexMap (changeSupport S hCB) ℤₘ).f n ≫
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

private lemma changeSupport_comp
    {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C) :
    SSetPair.chainComplexMap (changeSupport S hAB) ℤₘ ≫
      SSetPair.chainComplexMap (changeSupport S hBC) ℤₘ =
      SSetPair.chainComplexMap (changeSupport S (hAB.trans hBC)) ℤₘ := by
  apply HomologicalComplex.Hom.ext
  funext n
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrict S).chainComplexπ ℤₘ).f n)]
  have hab := congrArg (fun f ↦ f.f n) (π_changeSupport S hAB)
  have hbc := congrArg (fun f ↦ f.f n) (π_changeSupport S hBC)
  have hac := congrArg (fun f ↦ f.f n) (π_changeSupport S (hAB.trans hBC))
  simp only [HomologicalComplex.comp_f] at hab hbc hac ⊢
  erw [← Category.assoc, hab, hbc, hac]

private lemma relativeCapInto_open_mono (hUV : U ≤ V)
    (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    relativeCapInto L S U A p q n h φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hUV))) L).f q =
      relativeCapInto L S V A p q n h φ := by
  have : Mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' V)) L).f q) :=
    inferInstanceAs (Mono ((SSet.chainComplexMap
      (TopPair.toSSetPair.obj (TopPair.ofSubset (V : Set X))).hom L).f q))
  rw [← cancel_mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' V)) L).f q)]
  have hi : (Opens.toTopCat X).map (homOfLE hUV) ≫ Opens.inclusion' V = Opens.inclusion' U := by rfl
  have hv : ∀ m (σ : (S : SSet) _⦋m⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ V ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A :=
    fun m σ ↦ (hS m σ).imp (fun hs ↦ hs.trans hUV) id
  erw [Category.assoc, ← HomologicalComplex.comp_f,
    chains_comp, ← CategoryTheory.Functor.map_comp, hi,
    relativeCapInto_inclusion L S U A p q n h (hS n) φ,
    relativeCapInto_inclusion L S V A p q n h (hv n) φ]

/-- The localized cap boundary has sign `(-1)^(p+1)` on native cycles. -/
lemma localized_boundary (hWU : W ≤ U) (hCA : C ≤ A) (hAB : A ≤ B)
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
      (SSetPair.chainComplexMap (changeSupport S hCA) ℤₘ).f (n + 1) ≫
        relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫
          C[U].d (q + 1) q =
      ((-1 : ℤ) ^ (p + 1)) •
        (R[C].iCycles (n + 1) ≫
          (SSetPair.chainComplexMap (changeSupport S (hCA.trans hAB)) ℤₘ).f (n + 1) ≫
          relativeCapInto L S W B (p + 1) q (n + 1) (by omega) ζ ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hWU))) L).f q) := by
  have hb := relativeCapInto_cycles_comp_d L S U A hSU p q n h φ
  have hm := relativeCapInto_open_mono L S W U B hWU hSW
    (p + 1) q (n + 1) (by omega) ζ
  have hc := changeSupport_comp S hCA hAB
  erw [← HomologicalComplex.cyclesMap_i_assoc, hb, Preadditive.comp_zsmul, hφ,
    ← relativeCapInto_changeSupport L S U A B hAB (p + 1) q (n + 1) (by omega) ζ]
  congr 1
  erw [HomologicalComplex.cyclesMap_i_assoc]
  erw [← Category.assoc
    ((SSetPair.chainComplexMap (changeSupport S hCA) ℤₘ).f (n + 1)),
    ← HomologicalComplex.comp_f, hc, hm]

/-- The signed localized boundary, with its target expressed as native cycles. -/
lemma localized_boundary_cycles (hWU : W ≤ U) (hCA : C ≤ A) (hAB : A ≤ B)
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
      (SSetPair.chainComplexMap (changeSupport S hCA) ℤₘ).f (n + 1) ≫
        relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫ C[U].d (q + 1) q =
      (((-1 : ℤ) ^ (p + 1)) •
        (HomologicalComplex.cyclesMap
            (SSetPair.chainComplexMap (changeSupport S (hCA.trans hAB)) ℤₘ) (n + 1) ≫
          capIntoCycles L S W B hSW (p + 1) q (n + 1) (by omega) ζ)) ≫
        C[W].iCycles q ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hWU))) L).f q := by
  conv_rhs =>
    erw [Preadditive.zsmul_comp]
    simp only [Category.assoc]
    erw [capIntoCycles_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
  exact localized_boundary L S U W A B C hWU hCA hAB hSU hSW p q n h φ _ hφ


end CapMayerVietoris
end TauCeti
