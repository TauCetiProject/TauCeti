/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.Etale.AdjoinRoot
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.LocalRing.Localization
import TauCeti.RingTheory.RegularLocalRing.Normal
import TauCeti.RingTheory.RegularLocalRing.OfQuotient
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.Unramified.RootExtraction

/-!
# Standard tamely ramified covers

For a commutative ring `A`, an element `f` and an exponent `e`, the *standard tamely ramified
cover* of `Spec A` along `f` is `Spec A[x]/(x^e − f)` (Stacks, Example 58.31.4 (0EYF)). Stacks
assumes `A` Noetherian, `f` a nonzerodivisor with `A/fA` reduced and `e ≥ 1` invertible in `A`;
the algebra itself is defined without these hypotheses, and each statement carries the ones it
uses. This file defines the cover and proves that it is free of rank `e` and étale away from `f`
when `e` is invertible there. For `e ≥ 1` the root `x` is a nonzerodivisor when `f` is, with
quotient `A ⧸ (f)`. So `V(x)` has the same underlying closed set as the preimage of `V(f)`,
although the scheme-theoretic preimage is `V(x^e)`. The file also defines the shape of the
conclusions of Stacks, Lemmas 58.31.5 (0EYG) and 58.31.6 (0EYH).

If `e ≥ 1`, `f` is a nonzerodivisor and `A/(f)` is reduced, the cover is the integral closure
of `A` in its localization away from `f`. If moreover `A` is Noetherian and `A/(f)` is regular,
the cover is regular at every prime containing the image of `f`. These properties of the local
models in Stacks, Lemma 58.31.6 (0EYH), do not require `e` to be invertible. They follow from
`IsIntegrallyClosedIn.of_isLocalization_of_le_powers` and
`IsRegularLocalRing.localization_of_isRegularRing_quotient` (Stacks 00NU).

Over a local ring `A` with `f` in the maximal ideal, the cover is itself local, since every
maximal ideal lies over the maximal ideal of `A` and contains the root. So when `A` is moreover
Noetherian, `f` is a nonzerodivisor and `A/(f)` is regular, the cover is a regular local ring,
hence a normal domain, again for every `e ≥ 1`. This is the regularity of the root algebra
`A[x]/(x^e - f)` used in the proof of Stacks, Lemma 58.31.5 (0EYG), where `A` is a strictly
henselian regular local ring and `f` a local equation of the divisor. The cover has the same
residue field as `A`; to use the residue-field API, first install
`standardTameCover_isLocalRing` as a local instance.

## Main definitions

* `TauCeti.standardTameCover A f e`: the algebra `A[x]/(x^e − f)`, as `AdjoinRoot (X ^ e - C f)`.
* `TauCeti.IsFiniteProductOfStandardTameCovers A C f`: `C` is `A`-isomorphic to a finite product
  of standard tamely ramified covers along `f` with exponents invertible in `A`.
* `TauCeti.standardTameCoverQuotientSpanRootAlgEquiv`: for `e ≥ 1`, the quotient of the cover by
  the root is `A ⧸ (f)`.
* `TauCeti.standardTameCoverAwayAlgEquiv`: the localization of the cover at `f` is the standard
  cover of `A_f` along the image of `f`.

## Main results

* `TauCeti.standardTameCover_free`: for `e ≥ 1` the cover is free of rank `e`.
* `TauCeti.isFiniteProductOfStandardTameCovers_iff`: unfolding of the predicate.
* `TauCeti.IsFiniteProductOfStandardTameCovers.of_algEquiv`: transport along `A`-algebra
  isomorphisms.
* `TauCeti.isFiniteProductOfStandardTameCovers_standardTameCover`: a single standard cover with
  invertible exponent is a finite product of standard covers.
* `TauCeti.standardTameCover_root_mem_nonZeroDivisors_iff`: for `e ≥ 1`, the root is a
  nonzerodivisor iff `f` is.
* `TauCeti.standardTameCover_etale`: if `f` and `e` are units, the cover is étale; it is a
  standard étale algebra by `Polynomial.Monic.isStandardEtale_adjoinRoot`.
* `TauCeti.standardTameCover_etale_away`: if `e` is invertible in `A_f`, the cover is étale over
  `A_f` after inverting `f`.
* `TauCeti.standardTameCover_etale_away_iff`: for `e ≥ 1`, étaleness away from `f` is equivalent
  to invertibility of `e` in `A_f`. The converse uses the exponent criterion
  `TauCeti.isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C` from
  `TauCeti.RingTheory.Unramified.RootExtraction`.
* `TauCeti.standardTameCover_isIntegralClosure`: if `f` is a nonzerodivisor and `A/(f)` is
  reduced, the cover for `e ≥ 1` is the integral closure of `A` in its localization away from `f`.
* `TauCeti.standardTameCover_isRegularLocalRing_localization`: if `A` is Noetherian, `f` is a
  nonzerodivisor and `A/(f)` is regular, the cover for `e ≥ 1` is regular at primes over `(f)`.
* `TauCeti.standardTameCover_isLocalRing`: over a local ring with `f` in the maximal ideal, the
  cover for `e ≥ 1` is local.
* `TauCeti.standardTameCover_isRegularLocalRing`, `TauCeti.standardTameCover_isIntegrallyClosed`:
  over a Noetherian local ring with `f ∈ 𝔪` a nonzerodivisor and `A/(f)` regular, the cover for
  `e ≥ 1` is a regular local ring, and so integrally closed.

## References

* [Stacks Project, Example 58.31.4](https://stacks.math.columbia.edu/tag/0EYF).
* [Stacks Project, Lemma 58.31.5](https://stacks.math.columbia.edu/tag/0EYG).
* [Stacks Project, Lemma 58.31.6](https://stacks.math.columbia.edu/tag/0EYH).
* [Stacks Project, Lemma 10.157.5](https://stacks.math.columbia.edu/tag/0567).
* [Stacks Project, Lemma 10.106.7](https://stacks.math.columbia.edu/tag/00NU).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0): `standardTameCover_free` is
  `Pcf.Kummer.finrank_adjoinRoot_kummerPoly` (`lean/Pcf/Kummer.lean`), there for a unit constant
  term.
-/

public section

universe u v w

open Polynomial TensorProduct IsLocalRing

namespace TauCeti

variable (A : Type u) [CommRing A]

/-- The standard tamely ramified cover `A[x]/(x^e − f)`. Stacks, Example 58.31.4 (0EYF). The
algebra is defined without the example's hypotheses; statements carry the ones they use. -/
@[stacks 0EYF "the algebra A[x]/(x^e − f)"]
abbrev standardTameCover (f : A) (e : ℕ) : Type u :=
  AdjoinRoot (X ^ e - C f)

/-- For `e ≥ 1` the standard cover is free of rank `e`: the "finite locally free" assertion of
Stacks, Example 58.31.4 (0EYF). -/
@[stacks 0EYF "finite locally free"]
theorem standardTameCover_free [Nontrivial A] (f : A) (e : ℕ) (he : 1 ≤ e) :
    Module.Free A (standardTameCover A f e) ∧ Module.finrank A (standardTameCover A f e) = e := by
  have hmonic : (X ^ e - C f).Monic := monic_X_pow_sub_C f (Nat.one_le_iff_ne_zero.mp he)
  refine ⟨hmonic.free_adjoinRoot, ?_⟩
  rw [(AdjoinRoot.powerBasis' hmonic).finrank, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]

variable {A}

variable (A) in
/-- `C` is `A`-isomorphic to a finite product of standard tamely ramified covers along `f` with
exponents invertible in `A`. No tag: it is the shape of the conclusions of Stacks, Lemmas 58.31.5
(0EYG) and 58.31.6 (0EYH). -/
def IsFiniteProductOfStandardTameCovers (C : Type v) [CommRing C] [Algebra A C]
    (f : A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ), (∀ i, 1 ≤ e i) ∧ (∀ i, IsUnit (e i : A)) ∧
    Nonempty (C ≃ₐ[A] ∀ i, standardTameCover A f (e i))

/-- Characterization of finite products of standard tame covers by their indexed family. -/
theorem isFiniteProductOfStandardTameCovers_iff {C : Type v} [CommRing C] [Algebra A C] (f : A) :
    IsFiniteProductOfStandardTameCovers A C f ↔
      ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ), (∀ i, 1 ≤ e i) ∧
        (∀ i, IsUnit (e i : A)) ∧ Nonempty (C ≃ₐ[A] ∀ i, standardTameCover A f (e i)) :=
  Iff.rfl

/-- Being a finite product of standard covers is invariant under `A`-algebra isomorphisms. -/
theorem IsFiniteProductOfStandardTameCovers.of_algEquiv {C : Type v} {C' : Type w} [CommRing C]
    [Algebra A C] [CommRing C'] [Algebra A C'] {f : A}
    (h : IsFiniteProductOfStandardTameCovers A C f) (φ : C ≃ₐ[A] C') :
    IsFiniteProductOfStandardTameCovers A C' f := by
  obtain ⟨ι, _, e, he, heu, ⟨ψ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff f).mp h
  exact (isFiniteProductOfStandardTameCovers_iff f).mpr
    ⟨ι, inferInstance, e, he, heu, ⟨φ.symm.trans ψ⟩⟩

/-- A single standard cover whose exponent `e ≥ 1` is invertible in `A` is a finite product of
standard covers, indexed by a point. -/
theorem isFiniteProductOfStandardTameCovers_standardTameCover (f : A) {e : ℕ} (he : 1 ≤ e)
    (heu : IsUnit (e : A)) :
    IsFiniteProductOfStandardTameCovers A (standardTameCover A f e) f :=
  (isFiniteProductOfStandardTameCovers_iff f).mpr
    ⟨Unit, inferInstance, fun _ ↦ e, fun _ ↦ he, fun _ ↦ heu,
      ⟨(AlgEquiv.funUnique A Unit (standardTameCover A f e)).symm⟩⟩

/-- For `e ≥ 1` the root `x` of the standard cover is a nonzerodivisor if and only if `f` is a
nonzerodivisor of `A`. -/
theorem standardTameCover_root_mem_nonZeroDivisors_iff {f : A} {e : ℕ} (he : e ≠ 0) :
    AdjoinRoot.root (X ^ e - C f) ∈ nonZeroDivisors (standardTameCover A f e) ↔
      f ∈ nonZeroDivisors A := by
  have hmonic : (X ^ e - C f).Monic := monic_X_pow_sub_C f he
  have := hmonic.free_adjoinRoot
  constructor
  · intro h
    nontriviality A
    refine mem_nonZeroDivisors_of_injective (AdjoinRoot.of.injective_of_monic_of_degree_pos
      hmonic (by rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero he)]; exact_mod_cast
        Nat.pos_of_ne_zero he)) ?_
    rw [← AdjoinRoot.root_X_pow_sub_C_pow]
    exact pow_mem h e
  · intro hf
    have hreg : IsSMulRegular (standardTameCover A f e) f :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hf
    refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ hreg (?_ : f • y = f • 0)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero he
    rw [smul_zero, Algebra.smul_def, AdjoinRoot.algebraMap_eq,
      ← AdjoinRoot.root_X_pow_sub_C_pow (k + 1) f, pow_succ (AdjoinRoot.root _), mul_assoc,
      mul_comm _ y, hy, mul_zero]

/-- For `e ≥ 1` the quotient of the standard cover `A[x]/(x^e − f)` by the root `x` is
`A ⧸ (f)`. Thus `V(x)` has the same underlying closed set as the preimage of `V(f)`; the
scheme-theoretic preimage is `V(x^e)`. -/
noncomputable def standardTameCoverQuotientSpanRootAlgEquiv (f : A) {e : ℕ} (he : e ≠ 0) :
    (standardTameCover A f e ⧸ Ideal.span {AdjoinRoot.root (X ^ e - C f)}) ≃ₐ[A]
      A ⧸ Ideal.span {f} :=
  have hφ : (X ^ e - C f).eval₂
      (Ideal.Quotient.mkₐ A (Ideal.span {f}) : A →+* A ⧸ Ideal.span {f}) 0 = 0 := by
    simp [zero_pow he]
  let φ := AdjoinRoot.liftAlgHom _ (Ideal.Quotient.mkₐ A (Ideal.span {f})) 0 hφ
  let F := Ideal.Quotient.liftₐ _ φ fun a ha ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [φ]
  let G := Ideal.Quotient.liftₐ (Ideal.span {f})
    ((Ideal.Quotient.mkₐ A _).comp (Algebra.ofId A (standardTameCover A f e))) fun a ha ↦ by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero he
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
        Algebra.ofId_apply, map_mul, AdjoinRoot.algebraMap_eq,
        ← AdjoinRoot.root_X_pow_sub_C_pow (k + 1) f, pow_succ (AdjoinRoot.root _)]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  AlgEquiv.ofAlgHom F G
    (Ideal.Quotient.algHom_ext A (Subsingleton.elim _ _))
    (Ideal.Quotient.algHom_ext A (AdjoinRoot.algHom_ext (by simp [F, G, φ])))

/-- The isomorphism `A[x]/(x^e − f, x) ≃ A ⧸ (f)` is the identity on the image of `A`. -/
@[simp]
theorem standardTameCoverQuotientSpanRootAlgEquiv_mk_of (f : A) {e : ℕ} (he : e ≠ 0) (a : A) :
    standardTameCoverQuotientSpanRootAlgEquiv f he (Ideal.Quotient.mk _ (AdjoinRoot.of _ a)) =
      Ideal.Quotient.mk _ a := by
  rw [← AdjoinRoot.algebraMap_eq, Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes,
    Ideal.Quotient.algebraMap_eq]

/-- The inverse of `A[x]/(x^e − f, x) ≃ A ⧸ (f)` sends the class of `a` to the class of `a`. -/
@[simp]
theorem standardTameCoverQuotientSpanRootAlgEquiv_symm_mk (f : A) {e : ℕ} (he : e ≠ 0) (a : A) :
    (standardTameCoverQuotientSpanRootAlgEquiv f he).symm (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (AdjoinRoot.of _ a) := by
  rw [← Ideal.Quotient.algebraMap_eq, AlgEquiv.commutes, ← Ideal.Quotient.mk_algebraMap,
    AdjoinRoot.algebraMap_eq]

/-- If `f` and `e` are units of `A`, the standard cover `A[x]/(x^e − f)` is étale over `A`. -/
theorem standardTameCover_etale {f : A} {e : ℕ} (hf : IsUnit f) (he : IsUnit (e : A)) :
    Algebra.Etale A (standardTameCover A f e) := by
  have hmonic : (X ^ e - C f).Monic := by
    rcases eq_or_ne e 0 with rfl | he₀
    · have : Subsingleton A := subsingleton_of_zero_eq_one (by simpa using he)
      exact monic_of_subsingleton _
    · exact monic_X_pow_sub_C _ he₀
  have := hmonic.isStandardEtale_adjoinRoot (separable_X_pow_sub_C_unit hf.unit he)
  infer_instance

section Away

variable (f : A) (e : ℕ) (Af Cf : Type*) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af]
  [CommRing Cf] [Algebra (standardTameCover A f e) Cf]
  [IsLocalization.Away (algebraMap A (standardTameCover A f e) f) Cf] [Algebra A Cf]
  [IsScalarTower A (standardTameCover A f e) Cf] [Algebra Af Cf] [IsScalarTower A Af Cf]

/-- Localizing the standard cover `A[x]/(x^e − f)` away from `f` gives the standard cover of
`A_f` along the image of `f`. It composes the base change of `AdjoinRoot`
(`AdjoinRoot.algebraTensorAlgEquiv`) with the pushout square of the localization. -/
noncomputable def standardTameCoverAwayAlgEquiv :
    standardTameCover Af (algebraMap A Af f) e ≃ₐ[Af] Cf :=
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (standardTameCover A f e) (.powers f)) Cf := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have := (Algebra.isPushout_of_isLocalization (.powers f) Af (standardTameCover A f e) Cf).symm
  (AdjoinRoot.mapAlgEquiv AlgEquiv.refl _ _ (.of_eq (by simp))).trans <|
    (AdjoinRoot.algebraTensorAlgEquiv Af (X ^ e - C f)).symm.trans
      (Algebra.IsPushout.equiv A Af _ Cf)

/-- The isomorphism `A_f[x]/(x^e − f) ≃ A[x]/(x^e − f)_f` sends the root to the root. -/
@[simp]
theorem standardTameCoverAwayAlgEquiv_root :
    standardTameCoverAwayAlgEquiv f e Af Cf (AdjoinRoot.root _) =
      algebraMap (standardTameCover A f e) Cf (AdjoinRoot.root _) := by
  rw [standardTameCoverAwayAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root, AdjoinRoot.algebraTensorAlgEquiv_symm_root,
    Algebra.IsPushout.equiv_tmul, map_one, one_mul]

variable {e} in
include f in
/-- The standard cover `A[x]/(x^e − f)` is étale away from `f` as soon as `e` is invertible there:
if `e` is a unit of `A_f`, the localization of the cover at `f` is étale over `A_f`. This holds in
particular when `e` is invertible in `A`, as in Stacks. -/
@[stacks 0EYF "étale over D(f)"]
theorem standardTameCover_etale_away (he : IsUnit (e : Af)) : Algebra.Etale Af Cf :=
  have := standardTameCover_etale (IsLocalization.Away.algebraMap_isUnit (S := Af) f) he
  Algebra.Etale.of_equiv (standardTameCoverAwayAlgEquiv f e Af Cf)

variable {e} in
include f in
/-- A positive-degree root cover is étale off the divisor exactly when its exponent is
invertible off the divisor. This applies to arbitrary models of the two localizations. -/
theorem standardTameCover_etale_away_iff (he : e ≠ 0) :
    Algebra.Etale Af Cf ↔ IsUnit (e : Af) := by
  constructor
  · intro h
    have := Algebra.Etale.of_equiv (standardTameCoverAwayAlgEquiv f e Af Cf).symm
    exact isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C (algebraMap A Af f) he
  · exact standardTameCover_etale_away f Af Cf

end Away

variable {f : A} {e : ℕ}

/-- If `f` is a nonzerodivisor and `A/(f)` is reduced, the root algebra `A[x]/(x^e - f)`
for `e > 0` is the integral closure of `A` in its localization away from `f`.
No invertibility assumption on `e` or Noetherianity assumption on `A` is needed. -/
theorem standardTameCover_isIntegralClosure (hf : f ∈ nonZeroDivisors A) (he : e ≠ 0)
    [IsReduced (A ⧸ Ideal.span {f})] (Cf : Type*) [CommRing Cf]
    [Algebra (standardTameCover A f e) Cf]
    [IsLocalization.Away (algebraMap A (standardTameCover A f e) f) Cf]
    [Algebra A Cf] [IsScalarTower A (standardTameCover A f e) Cf] :
    IsIntegralClosure (standardTameCover A f e) A Cf := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have : IsReduced
      (standardTameCover A f e ⧸ Ideal.span {AdjoinRoot.root (X ^ e - C f)}) :=
    isReduced_of_injective (standardTameCoverQuotientSpanRootAlgEquiv f he)
      (standardTameCoverQuotientSpanRootAlgEquiv f he).injective
  have : IsIntegrallyClosedIn (standardTameCover A f e) Cf :=
    .of_isLocalization_of_le_powers
      ((standardTameCover_root_mem_nonZeroDivisors_iff he).mpr hf)
      (Submonoid.powers (algebraMap A (standardTameCover A f e) f))
      (Submonoid.powers_le.mpr (by
        rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.root_X_pow_sub_C_pow]
        exact Submonoid.pow_mem _ (Submonoid.mem_powers _) e))
  exact IsIntegralClosure.of_isIntegrallyClosedIn

/-- If `A` is Noetherian, `f` is a nonzerodivisor and `A/(f)` is regular, then
`A[x]/(x^e - f)` is regular at every prime over the divisor `(f)`, for every `e > 0`.
In particular, this applies even when the residue characteristic divides `e`. -/
theorem standardTameCover_isRegularLocalRing_localization [IsNoetherianRing A]
    (hf : f ∈ nonZeroDivisors A) (he : e ≠ 0) [IsRegularRing (A ⧸ Ideal.span {f})]
    (P : Ideal (standardTameCover A f e)) [P.IsPrime]
    (hfP : algebraMap A (standardTameCover A f e) f ∈ P) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have := IsNoetherianRing.of_finite A (standardTameCover A f e)
  have : IsRegularRing
      (standardTameCover A f e ⧸ Ideal.span {AdjoinRoot.root (X ^ e - C f)}) :=
    .of_ringEquiv (standardTameCoverQuotientSpanRootAlgEquiv f he).symm.toRingEquiv
  apply IsRegularLocalRing.localization_of_isRegularRing_quotient
    ((standardTameCover_root_mem_nonZeroDivisors_iff he).mpr hf) P
  apply Ideal.IsPrime.mem_of_pow_mem inferInstance e
  rwa [AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]

section IsLocalRing

variable [IsLocalRing A]

/-- Over a local ring `A`, if `f` lies in the maximal ideal and `e > 0`, the cover
`A[x]/(x^e - f)` is a local ring. -/
theorem standardTameCover_isLocalRing (hf : f ∈ IsLocalRing.maximalIdeal A) (he : e ≠ 0) :
    IsLocalRing (standardTameCover A f e) := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  -- `χ` is the composite `A[x]/(x^e - f) → A ⧸ (f) → κ_A`; its kernel is the maximal ideal.
  let φ : standardTameCover A f e →ₐ[A] A ⧸ Ideal.span {f} :=
    (standardTameCoverQuotientSpanRootAlgEquiv f he).toAlgHom.comp (Ideal.Quotient.mkₐ A _)
  have hφ : Function.Surjective φ :=
    (standardTameCoverQuotientSpanRootAlgEquiv f he).surjective.comp
      (Ideal.Quotient.mkₐ_surjective A _)
  have hf' : ∀ a ∈ Ideal.span {f}, IsLocalRing.residue A a = 0 := fun a ha ↦
    (IsLocalRing.residue_eq_zero_iff a).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hf ha)
  let χ := (Ideal.Quotient.lift _ (IsLocalRing.residue A) hf').comp φ.toRingHom
  have hK : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ <|
    (Ideal.Quotient.lift_surjective_of_surjective _ hf' IsLocalRing.residue_surjective).comp hφ
  refine IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker χ, hK, fun M hM ↦ (hK.eq_of_le hM.ne_top ?_).symm⟩
  -- Every maximal ideal `M` lies over `𝔪_A`, so it contains `x` and the image of `𝔪_A`.
  have hcomap : M.under A = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  have hroot : AdjoinRoot.root (X ^ e - C f) ∈ M := by
    refine hM.isPrime.mem_of_pow_mem e ?_
    rwa [AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq, ← Ideal.mem_comap,
      ← Ideal.under_def, hcomap]
  intro x hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ x)
  have haM : algebraMap A _ a ∈ M := by
    rw [← Ideal.mem_comap, ← Ideal.under_def, hcomap, ← IsLocalRing.residue_eq_zero_iff]
    simpa [χ, ← ha] using hx
  have hxa : x - algebraMap A _ a ∈ Ideal.span {AdjoinRoot.root (X ^ e - C f)} := by
    have : φ (x - algebraMap A _ a) = 0 := by
      rw [map_sub, AlgHom.commutes, ← ha, Ideal.Quotient.algebraMap_eq, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← (standardTameCoverQuotientSpanRootAlgEquiv f he).map_eq_zero_iff]
    simpa [φ] using this
  simpa using M.add_mem ((Ideal.span_singleton_le_iff_mem M).mpr hroot hxa) haM

section ResidueField

variable [IsLocalRing (standardTameCover A f e)]

/-- The root of a positive-degree cover along an element of the maximal ideal vanishes in
its residue field. -/
@[simp]
theorem standardTameCover_residue_root (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    residue (standardTameCover A f e) (AdjoinRoot.root (X ^ e - C f)) = 0 := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have hcomap : (maximalIdeal (standardTameCover A f e)).under A = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal inferInstance
  rw [residue_eq_zero_iff]
  apply Ideal.IsPrime.mem_of_pow_mem inferInstance e
  rw [AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]
  rwa [← Ideal.mem_comap, ← Ideal.under_def, hcomap]

/-- The residue field of a positive-degree root cover along the maximal ideal is canonically
isomorphic to that of the base. The root reduces to zero, and constants reduce as in `A`. -/
noncomputable def standardTameCoverResidueFieldEquiv (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    ResidueField (standardTameCover A f e) ≃+* ResidueField A := by
  let φ : standardTameCover A f e →+* ResidueField A :=
    AdjoinRoot.lift (residue A) 0 (by simp [he, (residue_eq_zero_iff f).mpr hf])
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact ⟨AdjoinRoot.of _ a, by simp [φ]⟩
  have hker : RingHom.ker φ = maximalIdeal (standardTameCover A f e) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)

/-- The residue-field identification of a root cover preserves the residues of constants. -/
@[simp]
theorem standardTameCoverResidueFieldEquiv_residue_of (hf : f ∈ maximalIdeal A) (he : e ≠ 0)
    (a : A) :
    standardTameCoverResidueFieldEquiv hf he
      (residue (standardTameCover A f e) (AdjoinRoot.of _ a)) = residue A a := by
  unfold standardTameCoverResidueFieldEquiv
  -- `erw` identifies the residue-field wrapper with the quotient used by the two comparisons.
  erw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, AdjoinRoot.lift_of]

/-- In the inverse residue-field identification, a constant is sent to the same constant. -/
@[simp]
theorem standardTameCoverResidueFieldEquiv_symm_residue (hf : f ∈ maximalIdeal A) (he : e ≠ 0)
    (a : A) :
    (standardTameCoverResidueFieldEquiv hf he).symm (residue A a) =
      residue (standardTameCover A f e) (AdjoinRoot.of _ a) := by
  apply (standardTameCoverResidueFieldEquiv hf he).injective
  simp

/-- A root cover along the maximal ideal has separably closed residue field whenever the
base does. This does not require the exponent to be invertible. -/
theorem standardTameCover_isSepClosed_residueField [IsSepClosed (ResidueField A)]
    (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    IsSepClosed (ResidueField (standardTameCover A f e)) :=
  IsSepClosed.of_ringEquiv (standardTameCoverResidueFieldEquiv hf he).symm

end ResidueField

/-- If `A` is a Noetherian local ring, `f ∈ 𝔪_A` is a nonzerodivisor and `A ⧸ (f)` is regular,
then `A[x]/(x^e - f)` is a regular local ring for every `e > 0`, whether or not `e` is invertible
in `A`. In particular it is a domain and a regular ring. -/
theorem standardTameCover_isRegularLocalRing [IsNoetherianRing A]
    (hf : f ∈ IsLocalRing.maximalIdeal A) (hf₀ : f ∈ nonZeroDivisors A) (he : e ≠ 0)
    [IsRegularRing (A ⧸ Ideal.span {f})] :
    IsRegularLocalRing (standardTameCover A f e) := by
  have := standardTameCover_isLocalRing hf he
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have hfm : algebraMap A (standardTameCover A f e) f ∈ IsLocalRing.maximalIdeal _ := by
    rwa [← Ideal.mem_comap, ← Ideal.under_def,
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A (IsLocalRing.maximalIdeal _))]
  have := standardTameCover_isRegularLocalRing_localization hf₀ he _ hfm
  exact .of_ringEquiv
    (IsLocalRing.algEquivLocalizationAtMaximalIdeal A (standardTameCover A f e)).symm.toRingEquiv

/-- If `A` is a Noetherian local ring, `f ∈ 𝔪_A` is a nonzerodivisor and `A ⧸ (f)` is regular,
then `A[x]/(x^e - f)` is integrally closed for every `e > 0`: it is a regular local ring, hence
normal (Stacks, Lemma 10.157.5 (0567)). -/
theorem standardTameCover_isIntegrallyClosed [IsNoetherianRing A]
    (hf : f ∈ IsLocalRing.maximalIdeal A) (hf₀ : f ∈ nonZeroDivisors A) (he : e ≠ 0)
    [IsRegularRing (A ⧸ Ideal.span {f})] :
    IsIntegrallyClosed (standardTameCover A f e) :=
  have := standardTameCover_isRegularLocalRing hf hf₀ he
  inferInstance

end IsLocalRing

end TauCeti
