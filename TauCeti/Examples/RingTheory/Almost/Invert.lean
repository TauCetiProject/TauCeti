/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Homology.SingleHomology
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal
import TauCeti.RingTheory.Almost.Invert
import TauCeti.RingTheory.Almost.ValuationRing

/-!
# Examples of inverting scalars on almost modules and algebras

These examples test `TauCeti.Almost.invert` and `TauCeti.Almost.Algebra.invert`:

* **Degenerate (`ϖ = 0`)**: `0 ∈ S.ideal` for every setup `S`, and inverting `0` sends every almost
  module and almost algebra to `0`;
* **Torsion versus non-torsion**: `(V ⧸ (ϖ))^a` and `(V ⧸ (ϖ^{n+1}))^a` vanish after inverting
  `ϖ ∈ S.ideal`, whereas on `((ℤ ⧸ 2ℤ) × ℤ)^a` over `(ℤ, ℤ)` inverting `2` kills the `2`-torsion
  factor while keeping the non-torsion factor nonzero;
* **Base ring and compatibility**: `V^a` goes to the free rank-one module `V[1/ϖ]`, `toAlmost ⋙
  invert` agrees both with `ModuleCat.localizedModuleFunctor` and with `ModuleCat.extendScalars`,
  and `Algebra.invert` agrees with `(Almost.invert).mapCommMon` and distinguishes `𝟙` from the
  coordinate swap on `(ℤ × ℤ)^a` after inverting `2`;
* **Unit scalars**: when `IsUnit ϖ`, `invert` is an equivalence identifying along restriction of
  scalars with `Almost.Module.elements`, and `Algebra.invertObjEquivElementsOfIsUnit` recovers the
  algebra of almost elements `A_*`;
* **Valuation ring `𝓞_ℂ_[p]` (`ϖ = p`)**:
  - `ℂ_[p]` is a localization of `𝓞_ℂ_[p]` away from `p`, so base-changing the setup of `𝓞_ℂ_[p]`
    to `ℂ_[p]` identifies almost `ℂ_[p]`-modules and algebras with honest `ℂ_[p]`-modules and
    algebras, and inverting `p` sends `(𝓞_ℂ_[p])^a` to `ℂ_[p]`;
  - `(𝓞_ℂ_[p] ⧸ (p))^a` is **nonzero** in `Almost.Module S`, yet `invert` at `p` sends it to `0`,
    so `invert` is **not faithful** (Bhatt, Exercise 4.1.9);
  - the single-term complex with `ResidueField 𝓞_ℂ_[p]` in degree `0` is **not** exact at `0` in
    `ModuleCat 𝓞_ℂ_[p]`, has almost zero homology in every degree, and becomes acyclic after
    inverting `p`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §5.2, Corollary
  5.2.15.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Exercise 4.1.9.
* P. Scholze, J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 8, Proposition 8.2.8.
-/

open CategoryTheory Limits IsLocalRing TauCeti.Almost TauCeti.Almost.BasicSetup
open scoped MonObj NNReal

/-! ### Degenerate case: inverting `0 ∈ m` -/

section ZeroScalar

variable {V : Type*} [CommRing V] (S : BasicSetup V)

-- `0 ∈ S.ideal` always holds, and `invert` at `0` sends every almost module to `0`.
example (M : TauCeti.Almost.Module S) : IsZero ((invert S S.ideal.zero_mem).obj M) :=
  isZero_invert_zero_obj S S.ideal.zero_mem M

-- Inverting `0` sends every almost algebra to the zero algebra.
example (A : TauCeti.Almost.Algebra S) : Subsingleton ((Algebra.invert S (0 : V)).obj A) :=
  inferInstance

end ZeroScalar

/-! ### Quotients, torsion, and base ring -/

section GeneralSetup

variable {V : Type*} [CommRing V] (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal)

-- Inverting `ϖ ∈ m` kills `(V ⧸ (ϖ))^a`.
example : IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj
    (ModuleCat.of V (V ⧸ Ideal.span {ϖ})))) := by
  rw [isZero_invert_toAlmost_obj_iff]
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right a _ (Ideal.subset_span rfl))

-- An algebra killed by a power of `ϖ ∈ m` becomes zero after `Algebra.invert`.
example (n : ℕ) : Subsingleton ((Algebra.invert S ϖ).obj ((Algebra.toAlmost S).obj
    (CommAlgCat.of V (V ⧸ Ideal.span {ϖ ^ (n + 1)})))) :=
  (Algebra.subsingleton_invert_toAlmost_obj_iff S hϖ _).mpr
    ⟨n + 1, (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)⟩

-- Inverting `ϖ ∈ m` sends `V^a` to the free rank-one module `Localization.Away ϖ`.
example : Nonempty ((invert S hϖ).obj ((Module.toAlmost S).obj (ModuleCat.of V V)) ≅
    ModuleCat.of (Localization.Away ϖ) (Localization.Away ϖ)) :=
  ⟨invertToAlmostRingIso S hϖ⟩

-- Compatibility of `toAlmost ⋙ invert` with Mathlib's `localizedModuleFunctor` and `extendScalars`.
example : Nonempty (Module.toAlmost S ⋙ invert S hϖ ≅
    ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ)) :=
  ⟨toAlmostCompInvertIso S hϖ⟩

example : Nonempty (Module.toAlmost S ⋙ invert S hϖ ≅
    ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))) :=
  ⟨toAlmostCompInvertIsoExtendScalars S hϖ⟩

-- `invert S hϖ` is braided monoidal, and its induced functor on `CommMon` agrees with
-- `Algebra.invert S ϖ`.
noncomputable example : (invert S hϖ).Braided := inferInstance

example : Nonempty (Algebra.invert S ϖ ≅
    (invert S hϖ).mapCommMon ⋙ ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor) :=
  ⟨Algebra.invertIsoMapCommMon S hϖ⟩

end GeneralSetup

/-! ### Detecting non-torsion summands and morphism actions over `(ℤ, ℤ)` -/

section ClassicalInt

-- `(ℤ ⧸ 2ℤ) × ℤ` has nonzero `2`-torsion, yet inverting `2` still produces a nonzero module
-- because the `ℤ` factor is `2`-torsion-free.
example :
    have h2mem : (2 : ℤ) ∈ (classical ℤ).ideal := by simp [classical_ideal]
    (∃ x : (ℤ ⧸ Ideal.span {(2 : ℤ)}) × ℤ, x ≠ 0 ∧ (2 : ℤ) • x = 0) ∧
    ¬ IsZero ((invert (classical ℤ) h2mem).obj ((Module.toAlmost (classical ℤ)).obj
      (ModuleCat.of ℤ ((ℤ ⧸ Ideal.span {(2 : ℤ)}) × ℤ)))) := by
  refine ⟨⟨(Ideal.Quotient.mk _ 1, 0), ?_, ?_⟩, ?_⟩
  · intro h
    have h1 : (1 : ℤ) ∈ Ideal.span {(2 : ℤ)} :=
      (Ideal.Quotient.eq_zero_iff_mem).mp (congrArg Prod.fst h)
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp h1
    omega
  · refine Prod.ext ?_ (by simp)
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (by simp)
  · rw [isZero_invert_toAlmost_obj_iff]
    intro h
    obtain ⟨n, hn⟩ := h (0, 1)
    have h2 : (2 : ℤ) ^ n • (1 : ℤ) = 0 := congrArg Prod.snd hn
    rw [smul_eq_mul, mul_one] at h2
    exact pow_ne_zero n (by decide) h2

-- After inverting `2`, `Algebra.invert` still distinguishes the identity of `(ℤ × ℤ)^a` from the
-- coordinate swap `(x, y) ↦ (y, x)`.
example :
    let R := CommAlgCat.of ℤ (ℤ × ℤ)
    let A := (Algebra.toAlmost (classical ℤ)).obj R
    let swap : R ⟶ R := CommAlgCat.ofHom ((AlgHom.snd ℤ ℤ ℤ).prod (AlgHom.fst ℤ ℤ ℤ))
    (Algebra.invert (classical ℤ) (2 : ℤ)).map (𝟙 A) ≠
      (Algebra.invert (classical ℤ) (2 : ℤ)).map ((Algebra.toAlmost (classical ℤ)).map swap) := by
  intro R A swap h
  let u : R ⟶ (Algebra.elements (classical ℤ)).obj A := (Algebra.adj (classical ℤ)).unit.app R
  have hswap : (Algebra.elements (classical ℤ)).map ((Algebra.toAlmost (classical ℤ)).map swap)
      (u (1, 0)) = u (0, 1) :=
    (ConcreteCategory.congr_hom ((Algebra.adj (classical ℤ)).unit.naturality swap) (1, 0)).symm
  have heval := ConcreteCategory.congr_hom h
    (algebraMap ((Algebra.elements (classical ℤ)).obj A)
      ((Algebra.invert (classical ℤ) (2 : ℤ)).obj A) (u (1, 0)))
  rw [(Algebra.invert (classical ℤ) (2 : ℤ)).map_id, ConcreteCategory.id_apply,
    Algebra.invert_map_algebraMap, hswap] at heval
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ)))
    ((Algebra.invert (classical ℤ) (2 : ℤ)).obj A)).mp heval
  have hinj : Function.Injective u :=
    ((ConcreteCategory.isIso_iff_bijective u).mp inferInstance).1
  have hmap (z : ℤ × ℤ) :
      algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ) ^ n * u z =
        u (algebraMap ℤ (ℤ × ℤ) ((2 : ℤ) ^ n) * z) := by
    rw [← map_pow, ← u.hom.commutes ((2 : ℤ) ^ n), ← map_mul]
  have hc' : algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ) ^ n * u (1, 0) =
      algebraMap ℤ ((Algebra.elements (classical ℤ)).obj A) (2 : ℤ) ^ n * u (0, 1) := hc
  rw [hmap, hmap] at hc'
  have hpow : (2 : ℤ) ^ n = 0 := by simpa using congrArg Prod.fst (hinj hc')
  exact pow_ne_zero n (by decide) hpow

end ClassicalInt

/-! ### Degenerate case: inverting a unit scalar -/

section UnitScalar

variable {V : Type*} [CommRing V] (S : BasicSetup V) {ϖ : V}

-- When `ϖ ∈ S.ideal` is a unit of `V`, `invert S hϖ` is an equivalence and identifies along
-- restriction of scalars with `Almost.Module.elements S`.
example (hϖ : ϖ ∈ S.ideal) (hu : IsUnit ϖ) :
    (invert S hϖ).IsEquivalence ∧
      Nonempty (invert S hϖ ⋙ ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ)) ≅
        Module.elements S) :=
  ⟨isEquivalence_invert_of_isUnit S hϖ hu, ⟨invertCompRestrictScalarsIsoElements S hϖ hu⟩⟩

-- Inverting a unit scalar preserves the algebra of almost elements `A_*`.
example (hu : IsUnit ϖ) (A : TauCeti.Almost.Algebra S) (x : (Algebra.elements S).obj A) :
    Algebra.invertObjEquivElementsOfIsUnit S hu A
      (algebraMap ((Algebra.elements S).obj A) ((Algebra.invert S ϖ).obj A) x) = x :=
  Algebra.invertObjEquivElementsOfIsUnit_algebraMap S hu A x

end UnitScalar

/-! ### Non-classical valuation ring `𝓞_ℂ_[p]`, non-faithfulness, and almost-exact complexes -/

section PadicComplex

variable (p : ℕ) [Fact p.Prime]

-- `ℂ_[p]` is a localization of `𝓞_ℂ_[p]` away from `p`, so base-changing the setup of `𝓞_ℂ_[p]`
-- to `ℂ_[p]` yields equivalences of categories for both modules and algebras, and inverting `p`
-- sends `(𝓞_ℂ_[p])^a` to a module isomorphic over `𝓞_ℂ_[p]` to `ℂ_[p]`.
example :
    let S := ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)
    ∃ hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal,
      IsLocalization.Away (p : 𝓞_ℂ_[p]) ℂ_[p] ∧
      Nonempty (ModuleCat.{0} ℂ_[p] ≌ TauCeti.Almost.Module (S.baseChange ℂ_[p])) ∧
      Nonempty (CommAlgCat.{0} ℂ_[p] ≌ TauCeti.Almost.Algebra (S.baseChange ℂ_[p])) ∧
      Nonempty (((ModuleCat.restrictScalars
        (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])))).obj
          ((invert S hp).obj ((Module.toAlmost S).obj (ModuleCat.of 𝓞_ℂ_[p] 𝓞_ℂ_[p])))) ≃ₗ[𝓞_ℂ_[p]]
        ℂ_[p]) := by
  let S := ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)
  have hp1 : (1 : ℝ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ≥0) < p := zero_lt_one.trans hp1
  have hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal := by
    rw [ofValuationRing_ideal]
    have hpv : Valued.v ((p : 𝓞_ℂ_[p]) : ℂ_[p]) < 1 := by
      rw [SubringClass.coe_natCast, PadicComplex.valuation_p]
      exact (div_lt_one hp0).mpr hp1
    exact (Valuation.mem_maximalIdeal_iff (v := (PadicComplex.valued p).v)).mpr hpv
  have hLoc : IsLocalization.Away (p : 𝓞_ℂ_[p]) ℂ_[p] := by
    rw [IsLocalization.Away, isLocalization_iff]
    have hpne : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    refine ⟨?_, ?_, fun {x y} hxy ↦ ⟨1, by simp [Subtype.ext hxy]⟩⟩
    · rintro ⟨_, n, rfl⟩
      rw [map_pow]
      exact IsUnit.pow n (isUnit_iff_ne_zero.mpr (by simpa using hpne))
    · intro z
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Valued.v z) hp1
      have hmem : z * (p : ℂ_[p]) ^ n ∈ 𝓞_ℂ_[p] := by
        rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, map_mul, map_pow,
          PadicComplex.valuation_p, one_div, inv_pow, ← div_eq_mul_inv]
        exact (div_le_one (pow_pos hp0 n)).mpr hn.le
      exact ⟨(⟨z * (p : ℂ_[p]) ^ n, hmem⟩,
        ⟨(p : 𝓞_ℂ_[p]) ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩), by simp⟩
  refine ⟨hp, hLoc, ⟨Module.baseChangeAwayEquiv S ℂ_[p] hp⟩,
    ⟨Algebra.baseChangeAwayEquiv S ℂ_[p] hp⟩, ?_⟩
  let e₁ := (((ModuleCat.restrictScalars
      (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])))).mapIso
        (invertToAlmostRingIso S hp)) ≪≫
    ModuleCat.restrictScalarsAlgebraMapIso
      (Localization.Away (p : 𝓞_ℂ_[p]))).toLinearEquiv
  let e₂ : Localization.Away (p : 𝓞_ℂ_[p]) ≃ₗ[𝓞_ℂ_[p]] ℂ_[p] :=
    (IsLocalization.algEquiv (Submonoid.powers (p : 𝓞_ℂ_[p]))
      (Localization.Away (p : 𝓞_ℂ_[p])) ℂ_[p]).toLinearEquiv
  exact ⟨e₁.trans e₂⟩

-- Non-faithfulness of `invert` (Bhatt, Exercise 4.1.9): `(𝓞_ℂ_[p] ⧸ (p))^a` is nonzero in
-- `Almost.Module S`, yet `invert` at `p` sends it to `0`, so `invert` is not faithful.
example :
    let S := ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)
    let Q := (Module.toAlmost S).obj
      (ModuleCat.of 𝓞_ℂ_[p] (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p])}))
    ∃ hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal,
      ¬ IsZero Q ∧ IsZero ((invert S hp).obj Q) ∧ ¬ (invert S hp).Faithful := by
  let hfg := TauCeti.PadicComplexInt.not_fg_maximalIdeal p
  let S := ofValuationRing hfg
  let Q := (Module.toAlmost S).obj
    (ModuleCat.of 𝓞_ℂ_[p] (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p])}))
  have hpMax : (p : 𝓞_ℂ_[p]) ∈ maximalIdeal 𝓞_ℂ_[p] := by
    have hp1 : (1 : ℝ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpv : Valued.v ((p : 𝓞_ℂ_[p]) : ℂ_[p]) < 1 := by
      rw [SubringClass.coe_natCast, PadicComplex.valuation_p]
      exact (div_lt_one (zero_lt_one.trans hp1)).mpr hp1
    exact (Valuation.mem_maximalIdeal_iff (v := (PadicComplex.valued p).v)).mpr hpv
  have hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal := (ofValuationRing_ideal hfg).symm ▸ hpMax
  have hQ : ¬ IsZero Q := by
    rw [Module.isZero_toAlmost_obj_iff, ofValuationRing_isAlmostZero_quotient_span_singleton_iff]
    exact (mem_maximalIdeal _).mp hpMax
  have hInvQ : IsZero ((invert S hp).obj Q) := by
    rw [isZero_invert_toAlmost_obj_iff]
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨1, by
      rw [pow_one]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right a _ (Ideal.subset_span rfl))⟩
  refine ⟨hp, hQ, hInvQ, fun hF ↦ hQ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  apply hF.map_injective
  exact hInvQ.eq_of_src _ _

-- A single-term complex concentrated in degree `0` with `ResidueField 𝓞_ℂ_[p]` is NOT exact at `0`
-- in `ModuleCat 𝓞_ℂ_[p]`, has almost zero homology in every degree, and becomes acyclic after
-- inverting `p`.
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
  have hp : (p : 𝓞_ℂ_[p]) ∈ S.ideal := by
    rw [ofValuationRing_ideal]
    have hp1 : (1 : ℝ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpv : Valued.v ((p : 𝓞_ℂ_[p]) : ℂ_[p]) < 1 := by
      rw [SubringClass.coe_natCast, PadicComplex.valuation_p]
      exact (div_lt_one (zero_lt_one.trans hp1)).mpr hp1
    exact (Valuation.mem_maximalIdeal_iff (v := (PadicComplex.valued p).v)).mpr hpv
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
  exact ⟨hNotExact, hAlmost, IsAlmostZero.acyclic_localizedModuleFunctor hAlmost hp,
    IsAlmostZero.acyclic_extendScalars hAlmost hp⟩

end PadicComplex
