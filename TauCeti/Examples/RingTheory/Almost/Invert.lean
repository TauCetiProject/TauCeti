/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.SingleHomology
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal
import TauCeti.RingTheory.Almost.Invert
import TauCeti.RingTheory.Almost.ValuationRing
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Examples of inverting an ideal element on almost modules and algebras

These examples test `TauCeti.Almost.invert`, `TauCeti.Almost.Algebra.invert`, and the exactness
results after inverting `ϖ ∈ m`:

* inverting `0 ∈ m` sends every almost module to zero and every almost algebra to a subsingleton
  algebra, whereas inverting `2` on `classical ℤ` kills the `2`-torsion summand of
  `ℤ × (ℤ ⧸ (2))` while keeping the product nonzero, and distinguishes `𝟙` from the coordinate swap
  on `(ℤ × ℤ)^a`;
* inverting a unit `ϖ ∈ m` (forcing `S = classical V`) makes `Almost.invert` an equivalence of
  categories compatible with `Almost.Module.elements`, and preserves `A_*` on almost algebras;
* for `ϖ ∈ m`, `Almost.Algebra.invert S ϖ` is naturally isomorphic to
  `(Almost.invert S hϖ).mapCommMon ⋙ ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor` and
  identifies `(R^a)_*[1/ϖ]` with `R[1/ϖ]`;
* for `S = ofValuationRing h` on a valuation domain with non-finitely-generated maximal ideal `m`
  and `ϖ ∈ m`, `(V ⧸ (ϖ))^a` is nonzero while `Almost.invert` kills it, so `Almost.invert` is not
  faithful; moreover, the non-exact short complex `m ⟶ V ⟶ 0` has almost zero homology and becomes
  exact after inverting `ϖ`;
* for `V = 𝓞_ℂ_[p]` and `ϖ = p`, `Almost.invert` is not faithful, `Localization.Away p` is
  canonically `𝓞_ℂ_[p]`-isomorphic to `ℂ_[p]`, base-changing to `ℂ_[p]` gives equivalences for
  almost modules and algebras, and the single-term complex with `ResidueField 𝓞_ℂ_[p]` in degree
  `0` is not exact at `0`, has almost zero homology in every degree, and becomes acyclic after
  inverting `p`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §5.2.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Exercise 4.1.9.
-/

open CategoryTheory Limits IsLocalRing TauCeti.Almost TauCeti.Almost.BasicSetup
open scoped MonObj NNReal

universe u

/-! ### General module computations and degenerate cases -/

section ModuleGeneral

variable {V : Type u} [CommRing V] (S : BasicSetup V)

-- Inverting `0 ∈ m` sends every almost module to zero.
example (M : TauCeti.Almost.Module S) : IsZero ((invert S S.ideal.zero_mem).obj M) :=
  isZero_invert_obj_zero S M

-- Inverting `ϖ ∈ m` kills `(V ⧸ (ϖ))^a`.
example {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj (ModuleCat.of V (V ⧸ Ideal.span {ϖ})))) :=
  isZero_invert_toAlmost_quotient_span_singleton S hϖ

-- Inverting `ϖ ∈ m` sends `V^a` to the free rank-one module over `Localization.Away ϖ`.
noncomputable example {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    (invert S hϖ).obj ((Module.toAlmost S).obj (ModuleCat.of V V)) ≅
      ModuleCat.of (Localization.Away ϖ) (Localization.Away ϖ) :=
  invertToAlmostRingIso S hϖ

-- Precomposing `invert` with `Module.toAlmost` recovers `ModuleCat.localizedModuleFunctor`
-- and `ModuleCat.extendScalars`.
noncomputable example {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Module.toAlmost S ⋙ invert S hϖ ≅
      ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ) :=
  toAlmostCompInvertIso S hϖ

noncomputable example {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Module.toAlmost S ⋙ invert S hϖ ≅
      ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)) :=
  toAlmostCompInvertExtendScalarsIso S hϖ

-- If `ϖ ∈ m` is a unit, `invert` is an equivalence and recovers `Module.elements` upon
-- restricting scalars back to `V`.
example {ϖ : V} (hϖ : ϖ ∈ S.ideal) (hu : IsUnit ϖ) : (invert S hϖ).IsEquivalence :=
  isEquivalence_invert_of_isUnit S hϖ hu

noncomputable example {ϖ : V} (hϖ : ϖ ∈ S.ideal) (hu : IsUnit ϖ) :
    invert S hϖ ⋙ ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ)) ≅
      Module.elements S :=
  invertCompRestrictScalarsIsoElementsOfIsUnit S hϖ hu

-- On `classical ℤ` at `2`, `ℤ × (ℤ ⧸ (2))` has nonzero `2`-torsion, yet remains nonzero after
-- inverting `2` because its `ℤ` summand survives localization.
example : ¬ IsZero ((invert (classical ℤ) (ϖ := (2 : ℤ)) (by simp)).obj
    ((Module.toAlmost (classical ℤ)).obj
      (ModuleCat.of ℤ (ℤ × (ℤ ⧸ Ideal.span {(2 : ℤ)}))))) := by
  intro hzero
  let M := ModuleCat.of ℤ (ℤ × (ℤ ⧸ Ideal.span {(2 : ℤ)}))
  have hzero' : IsZero (ModuleCat.of (Localization.Away (2 : ℤ))
      (LocalizedModule.Away (2 : ℤ) M)) :=
    hzero.of_iso (invertToAlmostObjIso (classical ℤ) (ϖ := (2 : ℤ)) (by simp) M).symm
  have hsub : Subsingleton (LocalizedModule.Away (2 : ℤ) M) :=
    ⟨fun x y ↦ ModuleCat.hom_ext_iff.mp (hzero'.eq_of_tgt
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x))
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y))) |> fun h ↦ by
        simpa using LinearMap.congr_fun h 1⟩
  obtain ⟨s, ⟨n, rfl⟩, hs⟩ := LocalizedModule.subsingleton_iff.mp hsub ((1 : ℤ), 0)
  have h1 : (2 : ℤ) ^ n = 0 := by
    have hfst := congrArg Prod.fst hs
    dsimp at hfst
    rwa [Prod.smul_fst, smul_eq_mul, mul_one] at hfst
  exact pow_ne_zero n two_ne_zero h1

end ModuleGeneral

/-! ### Valuation rings: non-faithfulness and almost exactness becoming exact -/

section ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (h : ¬ (maximalIdeal V).FG)

-- For `S = ofValuationRing h` and `ϖ ∈ m`, `(V ⧸ (ϖ))^a` is nonzero in `Almost.Module S`,
-- yet `invert` sends it to zero, so `invert` is not faithful.
example {ϖ : V} (hϖ : ϖ ∈ maximalIdeal V) :
    ¬ IsZero ((Module.toAlmost (ofValuationRing h)).obj
      (ModuleCat.of V (V ⧸ Ideal.span {ϖ}))) := by
  rw [Module.isZero_toAlmost_obj_iff, ofValuationRing_isAlmostZero_quotient_span_singleton_iff]
  exact (mem_maximalIdeal ϖ).mp hϖ

example {ϖ : V} (hϖ : ϖ ∈ (ofValuationRing h).ideal) :
    ¬ (invert (ofValuationRing h) hϖ).Faithful := by
  refine not_faithful_invert_of_not_isAlmostZero_quotient (ofValuationRing h) hϖ ?_
  rw [ofValuationRing_isAlmostZero_quotient_span_singleton_iff]
  exact (mem_maximalIdeal ϖ).mp (by rwa [ofValuationRing_ideal] at hϖ)

-- The short complex `m ⟶ V ⟶ 0` is not exact in `ModuleCat V` (since `m ≠ V`), has almost zero
-- homology, and becomes honestly exact after inverting any `ϖ ∈ m`.
example {ϖ : V} (hϖ : ϖ ∈ (ofValuationRing h).ideal) :
    let C : ShortComplex (ModuleCat.{u} V) := ShortComplex.mk
      (ModuleCat.ofHom (ofValuationRing h).ideal.subtype)
      (0 : ModuleCat.of V V ⟶ ModuleCat.of V PUnit.{u + 1})
      Limits.comp_zero
    ¬ C.Exact ∧ (ofValuationRing h).IsAlmostZero C.homology ∧
      (C.map (ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ))).Exact ∧
      (C.map (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)))).Exact := by
  intro C
  have hnot_exact : ¬ C.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro hex
    apply (maximalIdeal.isMaximal V).ne_top
    rw [eq_top_iff]
    intro x _
    obtain ⟨m, hm⟩ := hex x rfl
    exact hm ▸ (ofValuationRing_ideal h ▸ m.property)
  have halmost_exact : (C.map (Module.toAlmost (ofValuationRing h))).Exact := by
    have : IsIso ((C.map (Module.toAlmost (ofValuationRing h))).f) :=
      (Module.isIso_toAlmost_map_iff _ _).mpr (ofValuationRing h).isAlmostIso_subtype
    exact ((C.map (Module.toAlmost (ofValuationRing h))).exact_iff_epi
      (by rw [ShortComplex.map_g, Functor.map_zero])).mpr inferInstance
  have hhom : (ofValuationRing h).IsAlmostZero C.homology :=
    (Module.exact_map_toAlmost_iff (ofValuationRing h) C).mp halmost_exact
  exact ⟨hnot_exact, hhom,
    exact_localizedModuleFunctor_of_isAlmostZero_homology (ofValuationRing h) hϖ hhom,
    exact_extendScalars_away_of_isAlmostZero_homology (ofValuationRing h) hϖ hhom⟩

end ValuationRing

/-! ### The integers of `ℂ_p` at `ϖ = p` -/

section PadicComplex

open scoped NNReal

variable (p : ℕ) [Fact p.Prime]

-- On `𝓞_ℂ_[p]`, inverting `p ∈ m` is not faithful.
example : ∃ hp : (p : 𝓞_ℂ_[p]) ∈
      (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)).ideal,
    ¬ (invert (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)) hp).Faithful := by
  have hp_max : (p : 𝓞_ℂ_[p]) ∈ maximalIdeal 𝓞_ℂ_[p] :=
    TauCeti.PadicComplexInt.natCast_mem_maximalIdeal p
  refine ⟨by rwa [ofValuationRing_ideal], ?_⟩
  refine not_faithful_invert_of_not_isAlmostZero_quotient _ _ ?_
  rw [ofValuationRing_isAlmostZero_quotient_span_singleton_iff]
  exact (mem_maximalIdeal _).mp hp_max

-- Inverting `p` in the open subring `𝓞_ℂ_[p]` recovers `ℂ_[p]`, so
-- `Localization.Away (p : 𝓞_ℂ_[p])` is `𝓞_ℂ_[p]`-isomorphic to `ℂ_[p]` and base-changing the
-- setup of `𝓞_ℂ_[p]` to `ℂ_[p]` yields equivalences for modules and algebras.
noncomputable example :
    let S := ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)
    PProd (IsLocalization.Away (p : 𝓞_ℂ_[p]) ℂ_[p])
      ((Localization.Away (p : 𝓞_ℂ_[p]) ≃ₐ[𝓞_ℂ_[p]] ℂ_[p]) ×
        (ModuleCat.{0} ℂ_[p] ≌ TauCeti.Almost.Module (S.baseChange ℂ_[p])) ×
        (CommAlgCat.{0} ℂ_[p] ≌ TauCeti.Almost.Algebra (S.baseChange ℂ_[p]))) := by
  let hfg := TauCeti.PadicComplexInt.not_fg_maximalIdeal p
  let S := ofValuationRing hfg
  have hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal :=
    (ofValuationRing_ideal hfg).symm ▸ TauCeti.PadicComplexInt.natCast_mem_maximalIdeal p
  have : IsLocalization.Away (p : 𝓞_ℂ_[p]) ℂ_[p] :=
    Subring.isLocalizationAway_of_isOpen (𝓞_ℂ_[p]).toSubring
      (Valued.isOpen_valuationSubring ℂ_[p]) (p : 𝓞_ℂ_[p])
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using PadicComplex.norm_p_lt_one p))
      (IsUnit.mk0 _ (by simpa using (Fact.out : p.Prime).ne_zero))
  exact ⟨‹_›,
    IsLocalization.algEquiv (Submonoid.powers (p : 𝓞_ℂ_[p]))
      (Localization.Away (p : 𝓞_ℂ_[p])) ℂ_[p],
    Module.toAlmostBaseChangeAwayEquiv S ℂ_[p] hp,
    Algebra.toAlmostBaseChangeAwayEquiv S ℂ_[p] hp⟩

-- A single-term complex concentrated in degree `0` with `ResidueField 𝓞_ℂ_[p]` is not exact at
-- `0` in `ModuleCat 𝓞_ℂ_[p]`, has almost zero homology in every degree, and becomes acyclic
-- after inverting `p`.
example :
    let S := ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)
    let K := (HomologicalComplex.single (ModuleCat 𝓞_ℂ_[p]) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of 𝓞_ℂ_[p] (ResidueField 𝓞_ℂ_[p]))
    ¬ K.ExactAt 0 ∧
    (∀ i : ℤ, S.IsAlmostZero (K.homology i)) ∧
    (((ModuleCat.localizedModuleFunctor
      (Submonoid.powers (p : 𝓞_ℂ_[p]))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ∧
    (((ModuleCat.extendScalars
      (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic := by
  let hfg := TauCeti.PadicComplexInt.not_fg_maximalIdeal p
  let S := ofValuationRing hfg
  let A := ModuleCat.of 𝓞_ℂ_[p] (ResidueField 𝓞_ℂ_[p])
  let K := (HomologicalComplex.single (ModuleCat 𝓞_ℂ_[p]) (ComplexShape.up ℤ) 0).obj A
  have hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal :=
    (ofValuationRing_ideal hfg).symm ▸ TauCeti.PadicComplexInt.natCast_mem_maximalIdeal p
  have hNotExact : ¬ K.ExactAt 0 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 A).isZero_iff,
      ModuleCat.isZero_of_iff_subsingleton]
    exact not_subsingleton (ResidueField 𝓞_ℂ_[p])
  have hAlmost : ∀ i : ℤ, S.IsAlmostZero (K.homology i) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        A).symm.toLinearEquiv.isAlmostZero_iff S).mp (ofValuationRing_isAlmostZero_residueField hfg)
    · have hzero : IsZero (K.homology i) :=
        HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 A i hi
      have : Subsingleton (K.homology i) := ModuleCat.subsingleton_of_isZero hzero
      exact S.isAlmostZero_of_subsingleton
  exact ⟨hNotExact, hAlmost,
    acyclic_localizedModuleFunctor_of_isAlmostZero_homology S hp hAlmost,
    acyclic_extendScalars_away_of_isAlmostZero_homology S hp hAlmost⟩

end PadicComplex

/-! ### Inverting an element on almost algebras -/

section Algebra

variable {V : Type u} [CommRing V] (S : BasicSetup V)

-- Inverting `0` sends every almost algebra to a subsingleton algebra.
example (A : Algebra S) : Subsingleton ((Algebra.invert S 0).obj A) :=
  Algebra.subsingleton_invert_obj_zero S A

-- Inverting a unit preserves the algebra of almost elements `A_*`.
noncomputable example {ϖ : V} (A : Algebra S) (hu : IsUnit ϖ) :
    (Algebra.elements S).obj A ≃ₐ[V] (Algebra.invert S ϖ).obj A :=
  Algebra.invertObjAlgEquivOfIsUnit S A hu

-- On `classical ℤ` at the unit `1`, inverting `1` on `ℤ^a` yields a nontrivial algebra.
example : Nontrivial ((Algebra.invert (classical ℤ) 1).obj
    ((Algebra.toAlmost (classical ℤ)).obj (CommAlgCat.of ℤ ℤ))) := by
  have hbij : Function.Bijective
      ((Algebra.adj (classical ℤ)).unit.app (CommAlgCat.of ℤ ℤ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have : Nontrivial ((𝟭 (CommAlgCat ℤ)).obj (CommAlgCat.of ℤ ℤ)) :=
    inferInstanceAs (Nontrivial ℤ)
  have : Nontrivial ((Algebra.elements (classical ℤ)).obj
      ((Algebra.toAlmost (classical ℤ)).obj (CommAlgCat.of ℤ ℤ))) :=
    hbij.injective.nontrivial
  exact (Algebra.invertObjAlgEquivOfIsUnit (classical ℤ) _ isUnit_one).symm.toEquiv.nontrivial

-- Any almost algebra `(V ⧸ (ϖ ^ n))^a` killed by a power of `ϖ` becomes zero after inverting `ϖ`.
example (ϖ : V) (n : ℕ) :
    Subsingleton ((Algebra.invert S ϖ).obj
      ((Algebra.toAlmost S).obj (CommAlgCat.of V (V ⧸ Ideal.span {ϖ ^ n})))) := by
  refine Algebra.subsingleton_invert_obj_of_pow_smul_one_eq_zero S (ϖ := ϖ) (n := n) ?_
  let f := (Algebra.adj S).unit.app (CommAlgCat.of V (V ⧸ Ideal.span {ϖ ^ n}))
  have h1 : (1 : (Algebra.elements S).obj
      ((Algebra.toAlmost S).obj (CommAlgCat.of V (V ⧸ Ideal.span {ϖ ^ n})))) = f.hom 1 :=
    (map_one f.hom).symm
  rw [h1, ← map_smul]
  have hzero : ϖ ^ n • (1 : V ⧸ Ideal.span {ϖ ^ n}) = 0 := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [hzero, map_zero]

-- For `ϖ ∈ m`, `Algebra.subsingleton_invert_toAlmost_obj_iff` characterizes vanishing directly,
-- `Algebra.invertToAlmostObjEquiv` identifies canonical numerators of `(R^a)_*[1/ϖ]` and `R[1/ϖ]`,
-- and `Algebra.invert S ϖ` is naturally isomorphic to
-- `(Almost.invert S hϖ).mapCommMon ⋙ ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor`.
example {ϖ : V} (hϖ : ϖ ∈ S.ideal) (n : ℕ) :
    Subsingleton ((Algebra.invert S ϖ).obj ((Algebra.toAlmost S).obj
      (CommAlgCat.of V (V ⧸ Ideal.span {ϖ ^ (n + 1)})))) :=
  (Algebra.subsingleton_invert_toAlmost_obj_iff S hϖ _).mpr
    ⟨n + 1, (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)⟩

example {ϖ : V} (hϖ : ϖ ∈ S.ideal) (R : CommAlgCat.{u} V) (r : R) :
    (Algebra.invertToAlmostObjEquiv S hϖ R).symm
      (algebraMap R (Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ))) r) =
      algebraMap ((Algebra.elements S).obj ((Algebra.toAlmost S).obj R))
        ((Algebra.invert S ϖ).obj ((Algebra.toAlmost S).obj R))
        (((Algebra.adj S).unit.app R).hom r) := by
  simp

noncomputable example {ϖ : V} (hϖ : ϖ ∈ S.ideal) : (invert S hϖ).Braided := inferInstance

example {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Nonempty (Algebra.invert S ϖ ≅
      (invert S hϖ).mapCommMon ⋙ ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor) :=
  ⟨Algebra.invertIsoMapCommMon S hϖ⟩

-- After inverting `2`, `Algebra.invert (classical ℤ) 2` still distinguishes the identity of
-- `(ℤ × ℤ)^a` from the coordinate swap `(x, y) ↦ (y, x)`.
example :
    let R := CommAlgCat.of ℤ (ℤ × ℤ)
    let A := (Algebra.toAlmost (classical ℤ)).obj R
    let swap : R ⟶ R := CommAlgCat.ofHom ((AlgHom.snd ℤ ℤ ℤ).prod (AlgHom.fst ℤ ℤ ℤ))
    (Algebra.invert (classical ℤ) (2 : ℤ)).map (𝟙 A) ≠
      (Algebra.invert (classical ℤ) (2 : ℤ)).map ((Algebra.toAlmost (classical ℤ)).map swap) := by
  intro R A swap h
  let u : R ⟶ (Algebra.elements (classical ℤ)).obj A := (Algebra.adj (classical ℤ)).unit.app R
  have hswap : (Algebra.elements (classical ℤ)).map ((Algebra.toAlmost (classical ℤ)).map swap)
      (u.hom (1, 0)) = u.hom (0, 1) :=
    (ConcreteCategory.congr_hom ((Algebra.adj (classical ℤ)).unit.naturality swap) (1, 0)).symm
  have heval := ConcreteCategory.congr_hom h
    (algebraMap ((Algebra.elements (classical ℤ)).obj A)
      ((Algebra.invert (classical ℤ) (2 : ℤ)).obj A) (u.hom (1, 0)))
  rw [(Algebra.invert (classical ℤ) (2 : ℤ)).map_id, ConcreteCategory.id_apply,
    Algebra.invert_map_hom_algebraMap, hswap] at heval
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ)))
    ((Algebra.invert (classical ℤ) (2 : ℤ)).obj A)).mp heval
  have hinj : Function.Injective u :=
    ((ConcreteCategory.isIso_iff_bijective u).mp inferInstance).injective
  have hmap (z : ℤ × ℤ) :
      algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ) ^ n * u.hom z =
        u.hom (algebraMap ℤ (ℤ × ℤ) ((2 : ℤ) ^ n) * z) := by
    rw [← map_pow, ← u.hom.commutes ((2 : ℤ) ^ n), ← map_mul]
  have hc' : algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ) ^ n * u.hom (1, 0) =
      algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ) ^ n * u.hom (0, 1) := hc
  rw [hmap, hmap] at hc'
  have hpow : (2 : ℤ) ^ n = 0 := by simpa using congrArg Prod.fst (hinj hc')
  exact pow_ne_zero n (by decide) hpow

end Algebra
