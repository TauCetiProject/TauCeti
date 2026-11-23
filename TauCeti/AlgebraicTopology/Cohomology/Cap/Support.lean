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

public noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial Topology TopologicalSpace

namespace TopCat

open TauCeti TopPair

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {X : TopCat.{0}} (L : ModuleCat.{0} ℤ)
  (S : (TopCat.toSSet.obj X).Subcomplex) (U V W A B C : Opens X)

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

/-- Evaluation on a simplex characterizes the support-local cap. -/
lemma ι_capInto (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L)
    (σ : (S : SSet) _⦋n⦌) :
    S.toSSet.ιChainComplex σ ≫ capInto L S U p q n h φ =
      letI := Classical.propDecidable (Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U)
      if hσ : Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U then
        (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).ιChainComplex
            (TopCat.toSSetObjCodRestrict σ.val hσ) ≫
          ChainComplex.capChain ℤ
            (((Opens.toTopCat X).obj U).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
            ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplexPairing (ρ_ L).hom) p q n h
            ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) ℤₘ).f p ≫ φ)
      else 0 := by
  classical
  exact (S.toSSet.isColimitChainComplexXCofan ℤₘ n).fac _ ⟨σ⟩

/-- A cap chain supported in an open subspace has its actual inclusion into ambient chains. -/
lemma capInto_inclusion (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L)
    (hφ : ∀ (σ : (S : SSet) _⦋n⦌),
      ¬ Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U → (TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ.val) ≫
            φ = 0) :
    capInto L S U p q n h φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q =
      (SSet.chainComplexMap S.ι ℤₘ).f n ≫
        ChainComplex.capChain ℤ (X.alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ L).hom) p q n h φ := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_capInto]
  split_ifs with hσ
  · erw [Category.assoc, cap_naturality, ← Category.assoc, SSet.ι_chainComplexMap_f,
      TopCat.toSSet_map_inclusion'_toSSetObjCodRestrict]
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    -- Subcomplex inclusion evaluates a subtype simplex to its underlying ambient simplex.
    rfl
  · rw [zero_comp, ← Category.assoc, SSet.ι_chainComplexMap_f]
    rw [TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal]
    have he : S.ι.app _ σ = σ.val := rfl
    rw [he, hφ σ hσ]
    simp

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
  erw [← Category.assoc, TopPair.ιChainComplex_comp_singularChainComplexπ_eq_zero
    (TopPair.ofSubset (A : Set X)) ℤₘ _ (by
      rw [TopPair.range_ofSubset_map]
      exact TopCat.range_toSSetObjEquiv_map_subset _ _ hA _), zero_comp]

/-- The support-local cap vanishes on a simplex whose front `p`-face is killed by the cochain. -/
lemma ι_capInto_eq_zero_of_front (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj X).chainComplex ℤₘ).X p ⟶ L)
    (σ : S.toSSet _⦋n⦌)
    (hφ : (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ.val) ≫
          φ = 0) :
    S.toSSet.ιChainComplex σ ≫ capInto L S U p q n h φ = 0 := by
  classical
  rw [ι_capInto]
  split_ifs with hσ
  · apply (cancel_mono
      ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q)).1
    erw [Category.assoc, cap_naturality, ← Category.assoc, SSet.ι_chainComplexMap_f,
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
  apply ι_capInto_eq_zero_of_front
  have hA := (TopPair.mem_range_restrict_hom_app_iff (TopPair.ofSubset (A : Set X)) S
    (((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).hom.app _ τ)).1
    ⟨τ, rfl⟩
  rw [TopPair.range_ofSubset_map] at hA
  erw [← Category.assoc, TopPair.ιChainComplex_comp_singularChainComplexπ_eq_zero
    (TopPair.ofSubset (A : Set X)) ℤₘ _ (by
      rw [TopPair.range_ofSubset_map]
      exact TopCat.range_toSSetObjEquiv_map_subset _ _ hA _), zero_comp]

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

/-- The native quotient map characterizes the support-local relative cap. -/
@[reassoc (attr := simp)]
lemma π_relativeCapInto (p q n : ℕ) (h : p + q = n)
    (φ : Q[A].X p ⟶ L) :
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).chainComplexπ
        ℤₘ).f n) ≫ relativeCapInto L S U A p q n h φ =
      capInto L S U p q n h
        (((TopPair.ofSubset (A : Set X)).singularChainComplexπ ℤₘ).f p ≫ φ) := by
  exact (SSetPair.isColimitCokernelCoforkChainComplexX
    ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S) ℤₘ n).fac
      (CokernelCofork.ofπ _ (relative_capInto_zero L S U A p q n h φ))
      WalkingParallelPair.one

/-- Inclusion of a support-local relative cap is the original ambient cap. -/
lemma relativeCapInto_inclusion (p q n : ℕ) (h : p + q = n)
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

/-- Enlarging the output open set preserves the support-local relative cap in that set. -/
@[reassoc]
lemma relativeCapInto_comp_chainComplexMap_homOfLE (hUV : U ≤ V) (p q n : ℕ) (h : p + q = n)
    (hS : ∀ (σ : (S : SSet) _⦋n⦌),
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
        Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
    (φ : Q[A].X p ⟶ L) :
    relativeCapInto L S U A p q n h φ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE hUV))) L).f q =
      relativeCapInto L S V A p q n h φ := by
  rw [← cancel_mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' V)) L).f q)]
  have hi := Opens.toTopCat_map_comp_inclusion' (homOfLE hUV)
  erw [Category.assoc, ← HomologicalComplex.comp_f,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hi,
    relativeCapInto_inclusion L S U A p q n h hS φ,
    relativeCapInto_inclusion L S V A p q n h (fun σ ↦ (hS σ).imp (fun hs ↦ hs.trans hUV) id) φ]

variable (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
  Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨ Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
  (p q n : ℕ) (h : p + q = n)

include hS

/-- The boundary of a relative localized cap satisfies the signed cap differential formula. -/
@[reassoc]
lemma relativeCapInto_comp_d (φ : Q[A].X p ⟶ L) :
    relativeCapInto L S U A p (q + 1) (n + 1) (by omega) φ ≫
        C[U].d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        (R[A].d (n + 1) n ≫ relativeCapInto L S U A p q n h φ -
          relativeCapInto L S U A (p + 1) q (n + 1) (by omega)
            (Q[A].d (p + 1) p ≫ φ)) := by
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

/-- On relative cycles, the boundary of a localized cap is the signed cap of the coboundary. -/
lemma relativeCapInto_cycles_comp_d (φ : Q[A].X p ⟶ L) :
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
/-- Capping with the zero cochain gives zero. -/
@[simp]
lemma capInto_zero (p q n : ℕ) (h : p + q = n) : capInto L S U p q n h 0 = 0 := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_capInto]
  split_ifs <;> simp only [map_zero, comp_zero]

omit hS in
/-- The relative support-local cap with the zero cochain is zero. -/
@[simp]
lemma relativeCapInto_zero
    (p q n : ℕ) (h : p + q = n) : relativeCapInto L S U A p q n h 0 = 0 := by
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).chainComplexπ
      ℤₘ).f n), π_relativeCapInto, comp_zero, comp_zero, capInto_zero]
  -- The quotient functor and native ambient chain object have the same zero morphism.
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

@[reassoc (attr := simp)]
lemma capIntoCycles_i (φ : Q⁎[A].cycles p) :
    capIntoCycles L S U A hS p q n h φ ≫
        C[U].iCycles q =
      R[A].iCycles n ≫
        relativeCapInto L S U A p q n h
          (Q⁎[A].iCycles p φ) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- For a cocycle, the cap boundary is `(-1)^p` times the localized cap of the boundary. -/
@[reassoc]
lemma relativeCapInto_comp_d_of_cycles (φ : Q⁎[A].cycles p) :
    relativeCapInto L S U A p (q + 1) (n + 1) (by omega)
        (Q⁎[A].iCycles p φ) ≫
        C[U].d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        (R[A].d (n + 1) n ≫
          relativeCapInto L S U A p q n h
            (Q⁎[A].iCycles p φ)) := by
  have hc := relativeCapInto_comp_d L S U A hS p q n h
    (Q⁎[A].iCycles p φ)
  erw [ChainComplex.d_comp_linearYonedaObj_iCycles p (p + 1) φ,
    relativeCapInto_zero L S U A (p + 1) q (n + 1) (by omega), sub_zero] at hc
  exact hc

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
        HomologicalComplex.toCycles_comp_homologyπ, comp_zero])).val

@[reassoc (attr := simp)]
lemma homologyπ_capIntoHomology (φ : Q⁎[A].cycles p) :
    R[A].homologyπ n ≫ capIntoHomology L S U A hS p q n h φ =
      capIntoCycles L S U A hS p q n h φ ≫
        C[U].homologyπ q :=
  (CokernelCofork.IsColimit.desc'
    (R[A].homologyIsCokernel (n + 1) n (by simp)) _ _).property

end Subordinate

section Subspace

local notation "P[" U "," A "]" => openSubspacePair U A

variable (T : (TopPair.toSSetPair.obj P[U,A]).right.Subcomplex)
  (hT : T ≤ S.preimage (TopPair.toSSetPair.map (openSubspaceInclusion U A)).right)
  (hS : ∀ m (σ : (S : SSet) _⦋m⦌),
    Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨ Set.range (X.toSSetObjEquiv _ σ.val) ⊆ A)
  (p q n : ℕ) (h : p + q = n)

include hT hS

private lemma capInto_subspace_chains (φ : Q[A].X p ⟶ L) :
    (SSetPair.chainComplexMap
        (SSetPair.restrictMap (TopPair.toSSetPair.map (openSubspaceInclusion U A)) hT)
        ℤₘ).f n ≫ relativeCapInto L S U A p q n h φ =
      (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj P[U,A]).restrictι T) ℤₘ).f n ≫
        ChainComplex.capChain ℤ (P[U,A].alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplexPairing (ρ_ L).hom) p q n h
          ((TopPair.singularChainComplexMap (openSubspaceInclusion U A) ℤₘ).f p ≫ φ) := by
  rw [← cancel_mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) L).f q)]
  simp only [Category.assoc]
  erw [relativeCapInto_inclusion L S U A p q n h (hS n) φ]
  have hc := congrArg (fun f ↦ (SSetPair.chainComplexMap f ℤₘ).f n)
    (SSetPair.restrictMap_comp_restrictι (TopPair.toSSetPair.map (openSubspaceInclusion U A)) hT)
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at hc
  erw [← Category.assoc, hc, Category.assoc, TopPair.capChain_naturality]
  -- The pair map and the open inclusion have identical ambient singular-set components.
  erw [openSubspaceInclusion, TopPair.ofSubsetMap_fst]
  rfl

private lemma capInto_subspace_cycles (φ : Q⁎[A].cycles p) :
    HomologicalComplex.cyclesMap (SSetPair.chainComplexMap
        (SSetPair.restrictMap (TopPair.toSSetPair.map (openSubspaceInclusion U A)) hT)
        ℤₘ) n ≫ capIntoCycles L S U A hS p q n h φ =
      HomologicalComplex.cyclesMap
        (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj P[U,A]).restrictι T) ℤₘ) n ≫
        ChainComplex.capCycles ℤ (P[U,A].alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).chainComplexPairing (ρ_ L).hom) p q n h
          (HomologicalComplex.cyclesMap
            (TopPair.singularCochainComplexMap (openSubspaceInclusion U A)) p φ) := by
  rw [← cancel_mono (C[U].iCycles q)]
  erw [Category.assoc, capIntoCycles_i L S U A hS p q n h φ,
    HomologicalComplex.cyclesMap_i_assoc, Category.assoc,
    ChainComplex.capCycles_i (k := ℤ) (p := p) (q := q) (n := n),
    HomologicalComplex.cyclesMap_i_assoc,
    ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply (k := ℤ),
    capInto_subspace_chains L S U A T hT hS p q n h]

private lemma capInto_subspace_homology (φ : Q⁎[A].cycles p) :
    HomologicalComplex.homologyMap (SSetPair.chainComplexMap
        (SSetPair.restrictMap (TopPair.toSSetPair.map (openSubspaceInclusion U A)) hT)
        ℤₘ) n ≫ capIntoHomology L S U A hS p q n h φ =
      HomologicalComplex.homologyMap
        (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj P[U,A]).restrictι T) ℤₘ) n ≫
        P[U,A].singularCap ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h
          ((P[U,A].singularCochainComplex ℤₘ ℤ L).homologyπ p (HomologicalComplex.cyclesMap
              (TopPair.singularCochainComplexMap (openSubspaceInclusion U A)) p φ)) := by
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj P[U,A]).restrict T).chainComplex ℤₘ).homologyπ n)]
  have hc := capInto_subspace_cycles L S U A T hT hS p q n h φ
  conv_lhs =>
    erw [HomologicalComplex.homologyπ_naturality_assoc,
      homologyπ_capIntoHomology L S U A hS p q n h φ]
  conv_rhs =>
    erw [HomologicalComplex.homologyπ_naturality_assoc,
      TopPair.singularCap_homologyπ P[U,A] ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h]
  have hc' := congrArg (· ≫ C[U].homologyπ q) hc
  simp only [Category.assoc] at hc'
  -- Pair homology is homology of its native relative chain complex.
  convert hc' using 1
  rfl

/-- Relative excision identifies the localized cap with the cap in the original subspace. -/
lemma capIntoHomology_apply_eq_singularCap
    [Mono (SSetPair.homologyMap
      ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ n)]
    [IsIso (SSetPair.homologyMap
      ((TopPair.toSSetPair.obj P[U,A]).restrictι T) ℤₘ n)]
    (φ : Q⁎[A].cycles p)
    (z : R[A].homology n)
    (y : (P[U,A].singularChainComplex ℤₘ).homology n)
    (hz : SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ n z =
      TopPair.singularHomologyMap (openSubspaceInclusion U A) ℤₘ n y) :
    capIntoHomology L S U A hS p q n h φ z =
      (P[U,A].singularCap ℤ (ρ_ ℤₘ).inv (ρ_ L).hom p q n h
        ((P[U,A].singularCochainComplex ℤₘ ℤ L).homologyπ p
          (HomologicalComplex.cyclesMap
            (TopPair.singularCochainComplexMap (openSubspaceInclusion U A)) p φ))).hom y := by
  let j := SSetPair.homologyMap
    ((TopPair.toSSetPair.obj P[U,A]).restrictι T) ℤₘ n
  obtain ⟨y', hy'⟩ := (ConcreteCategory.bijective_of_isIso j).surjective y
  have hz' : SSetPair.homologyMap
      (SSetPair.restrictMap
        (TopPair.toSSetPair.map (openSubspaceInclusion U A)) hT) ℤₘ n y' = z := by
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrictι S) ℤₘ n)
    rw [hz, ← ConcreteCategory.comp_apply, ← SSetPair.homologyMap_comp]
    erw [SSetPair.restrictMap_comp_restrictι, SSetPair.homologyMap_comp,
      ConcreteCategory.comp_apply]
    exact congrArg (TopPair.singularHomologyMap (openSubspaceInclusion U A) ℤₘ n) hy'
  rw [← hz']
  have hc := ConcreteCategory.congr_hom
    (capInto_subspace_homology L S U A T hT hS p q n h φ) y'
  have hy'' : HomologicalComplex.homologyMap
      (SSetPair.chainComplexMap ((TopPair.toSSetPair.obj P[U,A]).restrictι T)
        ℤₘ) n y' = y := hy'
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hy''] at hc
  exact hc

end Subspace

/-- Support-local cap chains commute with support restriction. -/
lemma restrictSubsetMap_relativeCapInto (hAB : A ≤ B)
    (p q n : ℕ) (h : p + q = n)
    (φ : Q[B].X p ⟶ L) :
    (SSetPair.chainComplexMap (restrictSubsetMap S hAB) ℤₘ).f n ≫
        relativeCapInto L S U B p q n h φ =
      relativeCapInto L S U A p q n h
        ((TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).f p ≫ φ) := by
  erw [← cancel_epi
    ((((TopPair.toSSetPair.obj (TopPair.ofSubset (A : Set X))).restrict S).chainComplexπ ℤₘ).f n)]
  have hn := congrArg (fun f ↦ f.f n) (chainComplexπ_restrictSubsetMap (R := ℤₘ) S hAB)
  simp only [HomologicalComplex.comp_f] at hn
  erw [← Category.assoc, hn, π_relativeCapInto, π_relativeCapInto]
  have hp0 := (TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (𝟙 X) hAB) ℤₘ).symm
  erw [TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id,
    SSet.chainComplexMap_id, Category.id_comp] at hp0
  have hp := congrArg (fun f ↦ f.f p) hp0
  simp only [HomologicalComplex.comp_f] at hp
  erw [← Category.assoc, hp]

end TopCat
