/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.Homology.ModuleCat.KInjective
public import TauCeti.CategoryTheory.ObjectProperty.Orthogonal
public import TauCeti.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Localization.Away.MayerVietoris
public import TauCeti.RingTheory.Localization.Away.Presentation
public import TauCeti.RingTheory.Polynomial.Ideal

/-!
# Derived completeness with respect to an ideal

Let `A` be a commutative ring and `I` an ideal of `A`. An object `M` of the derived category
`D(A)` of `A`-modules is *derived `I`-complete* (`TauCeti.derivedComplete`) if
`Hom_{D(A)}(A[1/f], M[n]) = 0` for every `f ∈ I` and every `n : ℤ`, that is, if
`RHom_A(A[1/f], M) = 0` for every `f ∈ I` (Stacks, Tag 091S). This is a homotopical condition and
not a separatedness condition: for instance it holds for every `A`-module annihilated by a power
of `I`, placed in any degree (`TauCeti.derivedComplete_singleFunctor_of_pow_le_annihilator`). The
derived `I`-complete objects form a triangulated subcategory, the right orthogonal of the shifts
of the localizations `A[1/f]`, `f ∈ I`.

The elements `f` with `RHom_A(A[1/f], M) = 0` form a radical ideal of `A`
(`TauCeti.derivedCompleteIdeal`, Stacks, Tag 091Q), and `M` is derived `I`-complete exactly when
`I` is contained in it (`TauCeti.derivedComplete_iff_le`). Consequently derived `I`-completeness
can be tested on any set of generators of `I` (`TauCeti.derivedComplete_span_iff`) and depends
only on the radical of `I` (`TauCeti.derivedComplete_radical_iff`); in particular no finiteness of
`I` is needed for these statements.

For an `A`-module `N` placed in a single degree, derived `I`-completeness in `D(A)` is the
telescope criterion `TauCeti.IsDerivedComplete I N` for modules
(`TauCeti.derivedComplete_singleFunctor_iff`, Stacks, Tag 091P). Indeed `A[1/f]` has the free
resolution `0 → A[X] → A[X] → A[1/f] → 0` (`TauCeti.awayPresentation`), with first map
multiplication by `f X - 1`, so all `Extⁿ_A(A[1/f], N)` vanish exactly when the telescope map
`(xₙ) ↦ (xₙ - f • xₙ₊₁)` on `ℕ → N` is bijective
(`TauCeti.forall_subsingleton_ext_localizationAway_iff`). In particular every
`I`-adically complete module, placed in any degree, is derived `I`-complete
(`TauCeti.derivedComplete_singleFunctor_of_isAdicComplete`).

## Main definitions and results

* `TauCeti.derivedComplete I`: the derived `I`-complete objects of `D(A)`, a triangulated
  subcategory.
* `TauCeti.derivedCompleteIdeal M`: the radical ideal of `f` with `RHom_A(A[1/f], M) = 0`.
* `TauCeti.derivedComplete_iff_le`: `M` is derived `I`-complete iff `I ≤ derivedCompleteIdeal M`.
* `TauCeti.derivedComplete_span_iff`: derived completeness can be tested on generators.
* `TauCeti.derivedComplete_radical_iff`: derived completeness depends only on the radical.
* `TauCeti.derivedComplete_singleFunctor_iff`: a module placed in one degree is derived
  `I`-complete iff it is a derived `I`-complete module.

## Implementation notes

The proof that these elements form an ideal uses two short exact sequences of `A`-modules:

* for `c, f ∈ A`, with `S = A[1/f]` and `c` also denoting its image in `S`,
  `0 → S[X] → S[X] → A[1/(fc)] → 0`, where the first map is multiplication by `cX - 1`; the
  polynomial ring `S[X]` is a direct sum of copies of `S`, which is handled by the passage of
  orthogonality to coproducts (`DerivedCategory.singleFunctor_hom_eq_zero_of_isColimit`), and
  this shows that `f` in the ideal implies `cf` in the ideal;
* for `f, g ∈ A`, with `h = f + g` and `B = A[1/h]`, the Mayer–Vietoris sequence
  `0 → B → B[1/f] × B[1/g] → B[1/(fg)] → 0` (`IsLocalization.Away.mayerVietoris_exact`), exact
  since `f` and `g` generate the unit ideal of `B`, which shows that `f` and `g` in the ideal
  imply `f + g` in the ideal.

## References

* [Stacks Project, Section 15.93, *Derived completion*](https://stacks.math.columbia.edu/tag/091N),
  Lemma 15.93.1 (Tag 091P), Lemma 15.93.2 (Tag 091Q) and Definition 15.93.4 (Tag 091S).
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory Polynomial

universe w w' u

namespace TauCeti

variable {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- An object `M` of the derived category of `A`-modules is **derived `I`-complete** if every map
from `A[1/f]` placed in degree zero to every shift `M⟦n⟧` vanishes, for every `f ∈ I`, that is,
`RHom_A(A[1/f], M) = 0` for every `f ∈ I` (Stacks, Tag 091S). It is defined as the right
orthogonal of the shifts of these localizations, a triangulated subcategory. -/
def derivedComplete (I : Ideal A) : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  ((ObjectProperty.ofObj fun f : I ↦
    (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away (f : A)))).shiftClosure
      ℤ).rightOrthogonal

instance (I : Ideal A) : (derivedComplete (A := A) I).IsTriangulated := by
  dsimp only [derivedComplete]
  infer_instance

instance (I : Ideal A) : (derivedComplete (A := A) I).IsClosedUnderIsomorphisms := by
  dsimp only [derivedComplete]
  infer_instance

/-! ### The ideal of elements with vanishing derived Hom -/

/-- The objects with no nonzero map to any shift of `M`. -/
private abbrev Orth (M : DerivedCategory (ModuleCat.{u} A)) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  ((ObjectProperty.singleton M).shiftClosure ℤ).leftOrthogonal

variable (A) in
/-- The `A`-module `X` placed in degree zero. -/
private abbrev deg0 (X : Type u) [AddCommGroup X] [Module A X] :
    DerivedCategory (ModuleCat.{u} A) :=
  (singleFunctor (ModuleCat.{u} A) 0).obj (.of A X)

variable {M : DerivedCategory (ModuleCat.{u} A)}

private lemma Orth.of_linearEquiv {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (e : X ≃ₗ[A] Y) (h : Orth M (deg0 A X)) : Orth M (deg0 A Y) :=
  ObjectProperty.prop_of_iso _ ((singleFunctor (ModuleCat.{u} A) 0).mapIso e.toModuleIso) h

private lemma Orth.of_subsingleton (X : Type u) [AddCommGroup X] [Module A X] [Subsingleton X] :
    Orth M (deg0 A X) := fun _ _ _ ↦
  ((singleFunctor (ModuleCat.{u} A) 0).map_isZero
    (ModuleCat.isZero_of_subsingleton _)).eq_of_src _ _

section ShortExact

variable {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
  [AddCommGroup X₃] [Module A X₃] {f : X₁ →ₗ[A] X₂} {g : X₂ →ₗ[A] X₃}
  (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
include hf hfg hg

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
private lemma shortExact :
    (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ hfg hf hg

private lemma Orth.of_shortExact₁ (h₂ : Orth M (deg0 A X₂)) (h₃ : Orth M (deg0 A X₃)) :
    Orth M (deg0 A X₁) :=
  ObjectProperty.ext_of_isTriangulatedClosed₁ _ _
    (shortExact hf hfg hg).singleTriangle_distinguished h₂ h₃

private lemma Orth.of_shortExact₂ (h₁ : Orth M (deg0 A X₁)) (h₃ : Orth M (deg0 A X₃)) :
    Orth M (deg0 A X₂) :=
  ObjectProperty.ext_of_isTriangulatedClosed₂ _ _
    (shortExact hf hfg hg).singleTriangle_distinguished h₁ h₃

private lemma Orth.of_shortExact₃ (h₁ : Orth M (deg0 A X₁)) (h₂ : Orth M (deg0 A X₂)) :
    Orth M (deg0 A X₃) :=
  ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (shortExact hf hfg hg).singleTriangle_distinguished h₁ h₂

end ShortExact

private lemma Orth.prod {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (hX : Orth M (deg0 A X)) (hY : Orth M (deg0 A Y)) : Orth M (deg0 A (X × Y)) :=
  Orth.of_shortExact₂ LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective hX hY

private lemma Orth.finsupp {X ι : Type u} [AddCommGroup X] [Module A X]
    (h : Orth M (deg0 A X)) : Orth M (deg0 A (ι →₀ X)) := by
  have h' := (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1 h
  exact (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 fun n ↦
    singleFunctor_hom_eq_zero_of_isColimit (ModuleCat.finsuppCoconeIsColimit A X ι) fun _ ↦ h' n

/-- If `RHom(A[1/f], M) = 0` then `RHom(A[1/(cf)], M) = 0`, through the short exact sequence
`0 → S[X] → S[X] → A[1/(fc)] → 0`, with `S = A[1/f]` and first map multiplication by
`cX - 1`. -/
private lemma Orth.away_mul {f : A} (c : A) (hf : Orth M (deg0 A (Localization.Away f))) :
    Orth M (deg0 A (Localization.Away (c * f))) := by
  let S := Localization.Away f
  let q : S[X] := C (algebraMap A S c) * X - 1
  have hpoly : Orth M (deg0 A S[X]) :=
    (Orth.finsupp (ι := ULift ℕ) hf).of_linearEquiv ((Finsupp.domLCongr Equiv.ulift).trans
      ((Polynomial.basisMonomials S).repr.restrictScalars A).symm)
  have hquot : Orth M (deg0 A (S[X] ⧸ Ideal.span {q})) :=
    Orth.of_shortExact₃ (mulLeft_C_mul_X_sub_one_injective A (algebraMap A S c))
      (Ideal.exact_mulLeft_mkₐ_span_singleton q) (Ideal.Quotient.mkₐ_surjective A _) hpoly hpoly
  -- The quotient `S[X] ⧸ (cX - 1)` is the localization of `A` away from `f * c`.
  have : IsLocalization.Away (f * c) (AdjoinRoot q) :=
    have := IsLocalization.adjoin_inv (algebraMap A S c)
    IsLocalization.Away.mul' S (AdjoinRoot q) f c
  rw [mul_comm]
  exact hquot.of_linearEquiv
    (IsLocalization.algEquiv (Submonoid.powers (f * c)) (AdjoinRoot q)
      (Localization.Away (f * c))).toLinearEquiv

/-- If `RHom(A[1/f], M) = 0` and `RHom(A[1/g], M) = 0`, then `RHom(A[1/(f + g)], M) = 0`, through
the Mayer–Vietoris sequence of `B = A[1/(f + g)]`, in which `f` and `g` are coprime. -/
private lemma Orth.away_add {f g : A} (hf : Orth M (deg0 A (Localization.Away f)))
    (hg : Orth M (deg0 A (Localization.Away g))) : Orth M (deg0 A (Localization.Away (f + g))) := by
  let B := Localization.Away (f + g)
  have huv : IsCoprime (algebraMap A B f) (algebraMap A B g) :=
    ⟨IsLocalization.Away.invSelf (f + g), IsLocalization.Away.invSelf (f + g), by
      rw [← mul_add, ← map_add, mul_comm, IsLocalization.Away.mul_invSelf]⟩
  have : IsLocalization.Away (algebraMap A B f * algebraMap A B g)
      (Localization.Away (algebraMap A B (f * g))) := by
    rw [← map_mul]
    infer_instance
  let Bu := Localization.Away (algebraMap A B f)
  let Bv := Localization.Away (algebraMap A B g)
  let Buv := Localization.Away (algebraMap A B (f * g))
  have hu : IsUnit (algebraMap B Buv (algebraMap A B f)) := isUnit_of_mul_isUnit_left
    (y := algebraMap B Buv (algebraMap A B g)) (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Buv) (algebraMap A B (f * g)))
  have hv : IsUnit (algebraMap B Buv (algebraMap A B g)) := isUnit_of_mul_isUnit_right
    (x := algebraMap B Buv (algebraMap A B f)) (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Buv) (algebraMap A B (f * g)))
  let ρu : Bu →ₐ[A] Buv :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom A B Buv) _ hu
  let ρv : Bv →ₐ[A] Buv :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom A B Buv) _ hv
  have hρu (b : B) : ρu (algebraMap B Bu b) = algebraMap B Buv b :=
    IsLocalization.Away.lift_eq _ hu b
  have hρv (b : B) : ρv (algebraMap B Bv b) = algebraMap B Buv b :=
    IsLocalization.Away.lift_eq _ hv b
  let ι : B →ₗ[A] Bu × Bv :=
    (IsScalarTower.toAlgHom A B Bu).toLinearMap.prod (IsScalarTower.toAlgHom A B Bv).toLinearMap
  let δ : Bu × Bv →ₗ[A] Buv :=
    ρu.toLinearMap ∘ₗ LinearMap.fst A Bu Bv - ρv.toLinearMap ∘ₗ LinearMap.snd A Bu Bv
  have hι : Function.Injective ι :=
    IsLocalization.Away.mayerVietoris_injective (Bu := Bu) (Bv := Bv) huv
  have hιδ : Function.Exact ι δ :=
    IsLocalization.Away.mayerVietoris_exact (ρu := ρu.toRingHom) (ρv := ρv.toRingHom) huv hρu hρv
  have hδ : Function.Surjective δ :=
    IsLocalization.Away.mayerVietoris_surjective (ρu := ρu.toRingHom) (ρv := ρv.toRingHom) huv
      hρu hρv
  -- Each localization of `B` is a localization of `A` away from a multiple of `f` or of `g`.
  have e (x : A) : Localization.Away ((f + g) * x) ≃ₗ[A] Localization.Away (algebraMap A B x) :=
    (IsLocalization.algEquiv (Submonoid.powers ((f + g) * x)) _ _).toLinearEquiv
  have hfg := Orth.away_mul ((f + g) * g) hf
  have hfg_eq : (f + g) * g * f = (f + g) * (f * g) := by ring
  rw [hfg_eq] at hfg
  exact Orth.of_shortExact₁ hι hιδ hδ
    (((Orth.away_mul (f + g) hf).of_linearEquiv (e f)).prod
      ((Orth.away_mul (f + g) hg).of_linearEquiv (e g)))
    (hfg.of_linearEquiv (e (f * g)))

/-- The elements `f` of `A` such that every map from `A[1/f]`, placed in degree zero, to every
shift of `M` vanishes, that is, such that `RHom_A(A[1/f], M) = 0`. They form a radical ideal
(`TauCeti.isRadical_derivedCompleteIdeal`; Stacks, Tag 091Q), and `M` is derived `I`-complete
exactly when `I` is contained in it (`TauCeti.derivedComplete_iff_le`). -/
def derivedCompleteIdeal (M : DerivedCategory (ModuleCat.{u} A)) : Ideal A where
  carrier := {f | ∀ (n : ℤ)
    (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧), φ = 0}
  zero_mem' := by
    have : Subsingleton (Localization.Away (0 : A)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : A))
        (S := Localization.Away (0 : A)) ⟨1, pow_one _⟩
    exact (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
      (Orth.of_subsingleton _)
  add_mem' {f g} hf hg := (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
    (Orth.away_add ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hf)
      ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hg))
  smul_mem' c f hf := (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
    (Orth.away_mul c ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hf))

/-- `f` lies in `derivedCompleteIdeal M` if and only if every map from `A[1/f]`, placed in degree
zero, to every shift of `M` vanishes. -/
theorem mem_derivedCompleteIdeal {f : A} :
    f ∈ derivedCompleteIdeal M ↔ ∀ (n : ℤ)
      (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧), φ = 0 :=
  Iff.rfl

/-- The ideal of `f` with `RHom_A(A[1/f], M) = 0` is radical (Stacks, Tag 091Q): `A[1/gⁿ]` is
`A[1/g]` for `n > 0`. -/
theorem isRadical_derivedCompleteIdeal (M : DerivedCategory (ModuleCat.{u} A)) :
    (derivedCompleteIdeal M).IsRadical := by
  rintro g ⟨n, hn⟩
  cases n with
  | zero =>
    rw [pow_zero] at hn
    rw [(derivedCompleteIdeal M).eq_top_of_isUnit_mem hn isUnit_one]
    exact Submodule.mem_top
  | succ n =>
    have : IsLocalization.Away (g ^ (n + 1)) (Localization.Away g) := by
      rw [pow_succ]
      exact IsLocalization.Away.mul_of_isUnit' _ _
        (by simpa using IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away g) g n)
    exact (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
      (Orth.of_linearEquiv (IsLocalization.algEquiv (Submonoid.powers (g ^ (n + 1)))
        (Localization.Away (g ^ (n + 1))) (Localization.Away g)).toLinearEquiv
        ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hn))

/-- `M` is derived `I`-complete if and only if `I` is contained in the ideal of `f` with
`RHom_A(A[1/f], M) = 0`. -/
theorem derivedComplete_iff_le {I : Ideal A} :
    derivedComplete I M ↔ I ≤ derivedCompleteIdeal M := by
  rw [derivedComplete, ObjectProperty.rightOrthogonal_shiftClosure_iff]
  constructor
  · intro h f hf
    exact h _ (ObjectProperty.ofObj_apply (fun g : I ↦
      (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away (g : A)))) ⟨f, hf⟩)
  · rintro h _ ⟨⟨f, hf⟩⟩
    exact h hf

/-- `M` is derived `I`-complete if and only if every map from `A[1/f]`, placed in degree zero, to
every shift of `M` vanishes, for every `f ∈ I`. -/
theorem derivedComplete_iff {I : Ideal A} :
    derivedComplete I M ↔ ∀ f ∈ I, ∀ (n : ℤ)
      (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧), φ = 0 :=
  derivedComplete_iff_le

/-- Derived completeness can be tested on generators (Stacks, Lemma 15.93.1): `M` is derived
complete with respect to the ideal generated by `s` if and only if `RHom_A(A[1/f], M) = 0` for every
`f ∈ s`. -/
theorem derivedComplete_span_iff (s : Set A) :
    derivedComplete (Ideal.span s) M ↔ ∀ f ∈ s, ∀ (n : ℤ)
      (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧),
        φ = 0 := by
  rw [derivedComplete_iff_le, Ideal.span_le]
  rfl

/-- Derived completeness only depends on the radical of the ideal. -/
@[simp]
theorem derivedComplete_radical_iff {I : Ideal A} :
    derivedComplete I.radical M ↔ derivedComplete I M := by
  rw [derivedComplete_iff_le, derivedComplete_iff_le,
    (isRadical_derivedCompleteIdeal M).radical_le_iff]

/-- Ideals with the same radical have the same derived complete objects. -/
theorem derivedComplete_eq_of_radical_eq {I J : Ideal A} (h : I.radical = J.radical) :
    derivedComplete (A := A) I = derivedComplete J := by
  ext M
  rw [← derivedComplete_radical_iff, h, derivedComplete_radical_iff]

/-- A larger ideal has fewer derived complete objects. -/
theorem derivedComplete_antitone : Antitone (derivedComplete (A := A)) :=
  fun _ _ h _ hM ↦ derivedComplete_iff_le.2 (h.trans (derivedComplete_iff_le.1 hM))

/-- Every object is derived complete with respect to the zero ideal. -/
@[simp]
theorem derivedComplete_bot (M : DerivedCategory (ModuleCat.{u} A)) : derivedComplete ⊥ M :=
  derivedComplete_iff_le.2 bot_le

/-! ### Modules placed in one degree -/

section Module

open Abelian

variable (f : A)

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- Under `Hom_A(A[X], N) ≃ (ℕ → N)`, `φ ↦ (φ(Xⁿ))ₙ`, restriction along multiplication by
`f X - 1` is minus the telescope map. -/
private lemma bijective_mulLeft_comp_iff (N : ModuleCat.{u} A) :
    Function.Bijective (fun φ : ModuleCat.of A A[X] ⟶ N ↦
      ModuleCat.ofHom (LinearMap.mulLeft A (C f * X - 1 : A[X])) ≫ φ) ↔
      Function.Bijective (telescope N f) := by
  let Φ : (ℕ → N) → (ModuleCat.of A A[X] ⟶ N) :=
    fun c ↦ ModuleCat.ofHom ((Polynomial.basisMonomials A).constr A c)
  have hΦ : Function.Bijective Φ :=
    (ModuleCat.homEquiv (M := ModuleCat.of A A[X]) (N := N)).symm.bijective.comp
      ((Polynomial.basisMonomials A).constr A).bijective
  have hcomm : (fun φ : ModuleCat.of A A[X] ⟶ N ↦
      ModuleCat.ofHom (LinearMap.mulLeft A (C f * X - 1 : A[X])) ≫ φ) ∘
      (Φ ∘ Neg.neg) = Φ ∘ telescope N f := by
    funext c
    refine ModuleCat.hom_ext ((Polynomial.basisMonomials A).ext fun n ↦ ?_)
    have h : (C f * X - 1 : A[X]) * monomial n 1 = f • monomial (n + 1) 1 - monomial n 1 := by
      simp [sub_mul, mul_assoc, X_mul_monomial, C_mul_monomial, smul_monomial]
    have hb (c : ℕ → N) (i : ℕ) : (Polynomial.basisMonomials A).constr A c (monomial i 1) = c i :=
      by simpa using (Polynomial.basisMonomials A).constr_basis A c i
    simp only [Φ, Function.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg, Polynomial.coe_basisMonomials]
    rw [h, map_sub, map_smul]
    simp [hb, neg_add_eq_sub]
  rw [← Function.Bijective.of_comp_iff _ (hΦ.comp neg_involutive.bijective), hcomm,
    Function.Bijective.of_comp_iff' hΦ]

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- For `f : A` and an `A`-module `N`, every `Extⁿ_A(A[1/f], N)` vanishes exactly when the
telescope map `(xₙ) ↦ (xₙ - f • xₙ₊₁)` on `ℕ → N` is bijective (Stacks, Tag 091P). -/
theorem forall_subsingleton_ext_localizationAway_iff [HasExt.{w'} (ModuleCat.{u} A)]
    (N : ModuleCat.{u} A) :
    (∀ n, Subsingleton (Ext.{w'} (ModuleCat.of A (Localization.Away f)) N n)) ↔
      Function.Bijective (telescope N f) := by
  have h := (awayPresentation_shortExact f).forall_subsingleton_ext_X₃_iff_bijective N
  rw [awayPresentation_X₃, awayPresentation_f] at h
  rw [h, ← bijective_mulLeft_comp_iff f N]
  -- Identify the first two terms of `awayPresentation f` with `A[X]`, removing the `eqToHom`s.
  generalize awayPresentation_X₁ f = h₁, awayPresentation_X₂ f = h₂
  generalize (awayPresentation f).X₁ = X₁ at h₁ ⊢
  generalize (awayPresentation f).X₂ = X₂ at h₂ ⊢
  subst h₁ h₂
  simp

end Module

/-- An `A`-module `N`, placed in any degree, is derived `I`-complete in `D(A)` if and only if it
is a derived `I`-complete module, that is, if and only if for every `f ∈ I` the telescope map
`(xₙ) ↦ (xₙ - f • xₙ₊₁)` on `ℕ → N` is bijective (Stacks, Lemma 15.93.1, Tag 091P). -/
theorem derivedComplete_singleFunctor_iff {I : Ideal A} {N : ModuleCat.{u} A} {m : ℤ} :
    derivedComplete I ((singleFunctor (ModuleCat.{u} A) m).obj N) ↔ IsDerivedComplete I N := by
  have := hasExt_of_hasDerivedCategory (C := ModuleCat.{u} A)
  rw [← (derivedComplete I).prop_iff_of_iso
      (((singleFunctors (ModuleCat.{u} A)).shiftIso (-m) m 0 (by simp)).app N),
    Functor.comp_obj, ObjectProperty.prop_shift_iff_of_isStableUnderShift (P := derivedComplete I),
    derivedComplete_iff, isDerivedComplete_iff]
  refine forall₂_congr fun f _ ↦ ?_
  rw [← forall_subsingleton_ext_localizationAway_iff]
  refine ⟨fun h n ↦ ⟨fun x y ↦ Abelian.Ext.ext ((h n x.hom).trans (h n y.hom).symm)⟩,
    fun h n φ ↦ ?_⟩
  obtain hn | hn := lt_or_ge n 0
  · -- Negative shifts: `N[0]⟦n⟧` lies in degrees `≥ -n > 0`, while `A[1/f][0]` lies in degree `0`.
    have := TStructure.t.isGE_shift ((singleFunctor (ModuleCat.{u} A) 0).obj N) 0 n (-n)
    exact TStructure.t.zero φ 0 (-n)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [← Abelian.Ext.homEquiv.apply_symm_apply φ, (h k).elim (Abelian.Ext.homEquiv.symm φ) 0]
    exact Abelian.Ext.zero_hom _ _ _

/-- An `I`-adically complete `A`-module, placed in any degree, is derived `I`-complete. -/
theorem derivedComplete_singleFunctor_of_isAdicComplete {I : Ideal A} {N : ModuleCat.{u} A}
    [IsAdicComplete I N] {m : ℤ} : derivedComplete I ((singleFunctor (ModuleCat.{u} A) m).obj N) :=
  derivedComplete_singleFunctor_iff.2 IsDerivedComplete.of_isAdicComplete

/-- An `A`-module annihilated by a power of `I`, placed in any degree, is derived `I`-complete. -/
theorem derivedComplete_singleFunctor_of_pow_le_annihilator {I : Ideal A} {N : ModuleCat.{u} A}
    {k : ℕ} (hN : I ^ k ≤ Module.annihilator A N) (m : ℤ) :
    derivedComplete I ((singleFunctor (ModuleCat.{u} A) m).obj N) :=
  derivedComplete_singleFunctor_iff.2 <| IsDerivedComplete.of_pow_smul_eq_bot <| by
    rwa [← Submodule.le_annihilator_iff, Submodule.annihilator_top]

end TauCeti
