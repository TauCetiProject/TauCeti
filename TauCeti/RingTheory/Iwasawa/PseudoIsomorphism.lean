/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.PseudoNull
public import Mathlib.RingTheory.Localization.Module

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.PowerSeries.Ideal
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.LinearAlgebra.Isomorphisms
import TauCeti.NumberTheory.Padics.PowerSeriesIdeal
import TauCeti.RingTheory.Finiteness.Finsupp
import TauCeti.RingTheory.Localization.Module
import TauCeti.RingTheory.Support

/-!
# Pseudo-isomorphisms

A linear map `f : M → N` of modules over a commutative ring `A` is a *pseudo-isomorphism* if its
kernel and cokernel are pseudo-null. The structure theory of finitely generated modules over a
noetherian normal domain, and in particular of Iwasawa modules over `Λ = O⟦T⟧`, classifies modules
up to pseudo-isomorphism: a finitely generated `Λ`-module admits a pseudo-isomorphism to an
elementary module, and the characteristic ideal and the invariants `μ` and `λ` are invariant under
pseudo-isomorphism.

Over a noetherian ring a map of finitely generated modules is a pseudo-isomorphism exactly when it
becomes an isomorphism after localizing at every prime of height at most one. This local
criterion drives the rest of the file: pseudo-isomorphisms compose, multiplication by an element
lying in no prime of height at most one of the support is a pseudo-isomorphism, and a
pseudo-isomorphism onto a finitely generated torsion module can be reversed. The last statement
fails for modules that are not torsion: over `ℤ_p⟦T⟧` the inclusion of the maximal ideal is a
pseudo-isomorphism, while no pseudo-isomorphism goes the other way (Neukirch–Schmidt–Wingberg,
Chapter V, §3, Exercise 1).

## Main definitions

* `TauCeti.Iwasawa.IsPseudoIsomorphism f`: the kernel and the cokernel of `f` are pseudo-null.

## Main results

* `TauCeti.Iwasawa.isPseudoIsomorphism_iff_bijective_localizedModule_map`: the local criterion,
  over a noetherian ring and for finitely generated modules.
* `TauCeti.Iwasawa.IsPseudoIsomorphism.comp`: over a noetherian ring, composites of
  pseudo-isomorphisms are pseudo-isomorphisms.
* `TauCeti.Iwasawa.IsPseudoIsomorphism.finite_iff`: over a noetherian ring, the source of a
  pseudo-isomorphism is finitely generated iff its target is.
* `TauCeti.Iwasawa.isPseudoIsomorphism_lsmul`: multiplication by `a` on a finitely generated
  module `M` is a pseudo-isomorphism if `a` lies in no prime of height at most one in the support
  of `M`.
* `TauCeti.Iwasawa.IsPseudoIsomorphism.exists_reverse`: over a noetherian ring, a
  pseudo-isomorphism `M → N` onto a finitely generated torsion module gives a pseudo-isomorphism
  `N → M`.
* `TauCeti.Iwasawa.isPseudoIsomorphism_iff_bijective`: over a ring of dimension at most one, such
  as a Dedekind domain, pseudo-isomorphisms are the isomorphisms.
* `TauCeti.Iwasawa.isPseudoIsomorphism_iff_finite`: over a noetherian local ring of dimension two
  with finite residue field, such as `O⟦T⟧`, a pseudo-isomorphism is a map with finite kernel and
  cokernel.

The examples at the end of the file are over `Λ = ℤ_p⟦T⟧`. The first checks the multiplication
criterion: multiplication by `p` on `Λ ⧸ (T) ≅ ℤ_p` is a pseudo-isomorphism, although it is not
surjective. The second shows that the relation is not symmetric on modules that are not torsion:
the inclusion of the maximal ideal `𝔪` is a pseudo-isomorphism, but no map `Λ → 𝔪` is one.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (5.1.5)–(5.1.7).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §13.1.
-/

public section

namespace TauCeti.Iwasawa

variable {A : Type*} [CommRing A] {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
  [Module A N] [AddCommGroup P] [Module A P]

/-- A linear map `f : M → N` is a *pseudo-isomorphism* if its kernel and its cokernel
`N ⧸ range f` are pseudo-null. -/
structure IsPseudoIsomorphism (f : M →ₗ[A] N) : Prop where
  /-- The kernel of a pseudo-isomorphism is pseudo-null. -/
  isPseudoNull_ker : IsPseudoNull A (LinearMap.ker f)
  /-- The cokernel of a pseudo-isomorphism is pseudo-null. -/
  isPseudoNull_coker : IsPseudoNull A (N ⧸ LinearMap.range f)

namespace IsPseudoIsomorphism

/-- A bijective linear map is a pseudo-isomorphism. -/
theorem of_bijective {f : M →ₗ[A] N} (hf : Function.Bijective f) : IsPseudoIsomorphism f where
  isPseudoNull_ker := by
    have := Submodule.subsingleton_iff_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hf.1)
    exact .of_subsingleton
  isPseudoNull_coker := by
    have := Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hf.2)
    exact .of_subsingleton

/-- A pseudo-isomorphism becomes bijective after localizing at a prime of height at most one. -/
theorem bijective_localizedModule_map {f : M →ₗ[A] N} (hf : IsPseudoIsomorphism f)
    (𝔭 : PrimeSpectrum A) (h𝔭 : 𝔭.asIdeal.height ≤ 1) :
    Function.Bijective (LocalizedModule.map 𝔭.asIdeal.primeCompl f) :=
  ⟨(LinearMap.localizedMap_injective_iff_subsingleton_localized_ker _ f).mpr
      (hf.isPseudoNull_ker.subsingleton_localizedModule 𝔭 h𝔭),
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ f).mpr
      (hf.isPseudoNull_coker.subsingleton_localizedModule 𝔭 h𝔭)⟩

/-- Over a noetherian ring, a map of finitely generated modules that becomes bijective after
localizing at every prime of height at most one is a pseudo-isomorphism. -/
theorem of_bijective_localizedModule_map [IsNoetherianRing A] [Module.Finite A M]
    [Module.Finite A N] {f : M →ₗ[A] N}
    (h : ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height ≤ 1 →
      Function.Bijective (LocalizedModule.map 𝔭.asIdeal.primeCompl f)) :
    IsPseudoIsomorphism f where
  isPseudoNull_ker := ⟨inferInstance, fun 𝔭 h𝔭 ↦
    (LinearMap.localizedMap_injective_iff_subsingleton_localized_ker _ f).mp (h 𝔭 h𝔭).1⟩
  isPseudoNull_coker := ⟨inferInstance, fun 𝔭 h𝔭 ↦
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ f).mp (h 𝔭 h𝔭).2⟩

/-- Over a noetherian ring, the source of a pseudo-isomorphism is finitely generated iff its target
is. -/
theorem finite_iff [IsNoetherianRing A] {f : M →ₗ[A] N} (hf : IsPseudoIsomorphism f) :
    Module.Finite A M ↔ Module.Finite A N := by
  have := hf.isPseudoNull_ker.finite
  have := hf.isPseudoNull_coker.finite
  refine ⟨fun _ ↦ .of_submodule_quotient (LinearMap.range f), fun _ ↦ ?_⟩
  -- `M` is an extension of the submodule `range f` of `N` by `ker f`.
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq]
    exact Module.Finite.iff_fg.mp inferInstance

end IsPseudoIsomorphism

/-- The local criterion: over a noetherian ring, a map of finitely generated modules is a
pseudo-isomorphism iff it becomes bijective after localizing at every prime of height at most
one. -/
theorem isPseudoIsomorphism_iff_bijective_localizedModule_map [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N] {f : M →ₗ[A] N} :
    IsPseudoIsomorphism f ↔ ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height ≤ 1 →
      Function.Bijective (LocalizedModule.map 𝔭.asIdeal.primeCompl f) :=
  ⟨fun hf ↦ hf.bijective_localizedModule_map, .of_bijective_localizedModule_map⟩

/-- Over a noetherian ring, a composite of pseudo-isomorphisms is a pseudo-isomorphism. -/
theorem IsPseudoIsomorphism.comp [IsNoetherianRing A] {f : M →ₗ[A] N} {g : N →ₗ[A] P}
    (hg : IsPseudoIsomorphism g) (hf : IsPseudoIsomorphism f) : IsPseudoIsomorphism (g ∘ₗ f) := by
  have := hf.isPseudoNull_ker.finite
  have := hf.isPseudoNull_coker.finite
  have := hg.isPseudoNull_ker.finite
  have := hg.isPseudoNull_coker.finite
  have hloc (𝔭 : PrimeSpectrum A) (h𝔭 : 𝔭.asIdeal.height ≤ 1) :
      Function.Bijective (LocalizedModule.map 𝔭.asIdeal.primeCompl (g ∘ₗ f)) := by
    rw [LocalizedModule.map_comp, LinearMap.coe_comp]
    exact (hg.bijective_localizedModule_map 𝔭 h𝔭).comp (hf.bijective_localizedModule_map 𝔭 h𝔭)
  refine ⟨⟨.ker_comp f g, fun 𝔭 h𝔭 ↦ ?_⟩, ⟨.quotient_range_comp f g, fun 𝔭 h𝔭 ↦ ?_⟩⟩
  · exact (LinearMap.localizedMap_injective_iff_subsingleton_localized_ker _ _).mp (hloc 𝔭 h𝔭).1
  · exact (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ _).mp
      (hloc 𝔭 h𝔭).2

/-- The multiplication criterion: over a noetherian ring, multiplication by `a` on a finitely
generated module `M` is a pseudo-isomorphism if `a` lies in no prime of height at most one in the
support of `M`. -/
theorem isPseudoIsomorphism_lsmul [IsNoetherianRing A] [Module.Finite A M] (a : A)
    (ha : ∀ 𝔭 ∈ Module.support A M, 𝔭.asIdeal.height ≤ 1 → a ∉ 𝔭.asIdeal) :
    IsPseudoIsomorphism (LinearMap.lsmul A M a) := by
  refine .of_bijective_localizedModule_map fun 𝔭 h𝔭 ↦ ?_
  by_cases hmem : 𝔭 ∈ Module.support A M
  · exact LocalizedModule.bijective_map_lsmul M (ha 𝔭 hmem h𝔭)
  · have := Module.notMem_support_iff.mp hmem
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

/-- Prime avoidance for a pseudo-isomorphism `f : M → N` onto a finitely generated torsion module
over a noetherian ring: some `γ` kills `ker f` and `coker f` and lies in no prime of height at most
one in the support of `N`. -/
theorem IsPseudoIsomorphism.exists_mem_annihilator_notMem [IsNoetherianRing A] [Module.Finite A N]
    (hN : Module.IsTorsion A N) {f : M →ₗ[A] N} (hf : IsPseudoIsomorphism f) :
    ∃ γ ∈ Module.annihilator A (LinearMap.ker f),
      γ ∈ Module.annihilator A (N ⧸ LinearMap.range f) ∧
        ∀ 𝔭 ∈ Module.support A N, 𝔭.asIdeal.height ≤ 1 → γ ∉ 𝔭.asIdeal := by
  have := hf.isPseudoNull_ker.finite
  have := hf.isPseudoNull_coker.finite
  -- None of the finitely many primes of height at most one in the support of `N` contains either
  -- annihilator, so none contains their intersection.
  suffices ∃ γ ∈ Module.annihilator A (LinearMap.ker f) ⊓
      Module.annihilator A (N ⧸ LinearMap.range f),
      ∀ 𝔭 ∈ {𝔭 ∈ Module.support A N | 𝔭.asIdeal.height ≤ 1}, γ ∉ 𝔭.asIdeal by
    obtain ⟨γ, hγJ, hγ⟩ := this
    exact ⟨γ, (Submodule.mem_inf.mp hγJ).1, (Submodule.mem_inf.mp hγJ).2,
      fun 𝔭 hmem h𝔭 ↦ hγ 𝔭 ⟨hmem, h𝔭⟩⟩
  by_contra! h
  obtain ⟨_, ⟨𝔭, ⟨-, hht⟩, rfl⟩, hJ⟩ :=
    (Ideal.subset_union_prime_finite (f := id)
      (hN.finite_setOf_mem_support_height_le_one.image PrimeSpectrum.asIdeal) ⊥ ⊥
      fun _ ⟨𝔭, _, h⟩ _ _ ↦ h ▸ 𝔭.isPrime).mp fun x hx ↦ by simpa using h x hx
  rcases 𝔭.isPrime.inf_le.mp hJ with hJ | hJ
  · exact (hf.isPseudoNull_ker.one_lt_height
      (Module.mem_support_iff_of_finite.mpr hJ)).not_ge hht
  · exact (hf.isPseudoNull_coker.one_lt_height
      (Module.mem_support_iff_of_finite.mpr hJ)).not_ge hht

/-- Over a noetherian ring, a pseudo-isomorphism `M → N` onto a finitely generated torsion module
can be reversed: there is a pseudo-isomorphism `N → M`. Without the torsion hypothesis the
statement fails: the inclusion of the maximal ideal of `ℤ_p⟦T⟧` is a pseudo-isomorphism, but there
is none in the other direction. -/
theorem IsPseudoIsomorphism.exists_reverse [IsNoetherianRing A] [Module.Finite A N]
    (hN : Module.IsTorsion A N) {f : M →ₗ[A] N} (hf : IsPseudoIsomorphism f) :
    ∃ g : N →ₗ[A] M, IsPseudoIsomorphism g := by
  have := hf.finite_iff.mpr ‹Module.Finite A N›
  obtain ⟨γ, hker, hcoker, hγ⟩ := hf.exists_mem_annihilator_notMem hN
  obtain ⟨g, hgf⟩ := f.exists_comp_eq_lsmul_of_mem_annihilator hker hcoker
  refine ⟨g, .of_bijective_localizedModule_map fun 𝔭 h𝔭 ↦ ?_⟩
  have hfloc := hf.bijective_localizedModule_map 𝔭 h𝔭
  by_cases hmem : 𝔭 ∈ Module.support A N
  · -- Here `γ` is a unit, and `g` is `γ²` times the inverse of `f`.
    have hγ𝔭 : γ * γ ∈ 𝔭.asIdeal.primeCompl :=
      Submonoid.mul_mem _ (hγ 𝔭 hmem h𝔭) (hγ 𝔭 hmem h𝔭)
    have := LocalizedModule.bijective_map_lsmul M hγ𝔭
    rw [← hgf, LocalizedModule.map_comp, LinearMap.coe_comp] at this
    exact (Function.Bijective.of_comp_iff _ hfloc).mp this
  · -- Here `N` vanishes, and so does `M`.
    have := Module.notMem_support_iff.mp hmem
    have : Subsingleton (LocalizedModule 𝔭.asIdeal.primeCompl M) := hfloc.1.subsingleton
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

/-- Over a ring of Krull dimension at most one, such as a Dedekind domain, the pseudo-isomorphisms
are the bijective linear maps. -/
theorem isPseudoIsomorphism_iff_bijective [Ring.KrullDimLE 1 A] {f : M →ₗ[A] N} :
    IsPseudoIsomorphism f ↔ Function.Bijective f := by
  refine ⟨fun hf ↦ ⟨?_, ?_⟩, .of_bijective⟩
  · rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
      ← isPseudoNull_iff_subsingleton (A := A)]
    exact hf.isPseudoNull_ker
  · rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff,
      ← isPseudoNull_iff_subsingleton (A := A)]
    exact hf.isPseudoNull_coker

/-- Over a noetherian local ring of dimension two with finite residue field, for example the
Iwasawa algebra `O⟦T⟧` of a complete discrete valuation ring `O` with finite residue field, a map
is a pseudo-isomorphism iff its kernel and cokernel are finite. -/
theorem isPseudoIsomorphism_iff_finite [IsLocalRing A] [IsNoetherianRing A]
    [Finite (IsLocalRing.ResidueField A)] (hdim : ringKrullDim A = 2) {f : M →ₗ[A] N} :
    IsPseudoIsomorphism f ↔ Finite (LinearMap.ker f) ∧ Finite (N ⧸ LinearMap.range f) := by
  -- A pseudo-null module is finitely generated, and so is a finite one.
  refine ⟨fun hf ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · have := hf.1.finite
    have := hf.2.finite
    exact ⟨(isPseudoNull_iff_finite hdim).mp hf.1, (isPseudoNull_iff_finite hdim).mp hf.2⟩
  · have : Module.Finite A (LinearMap.ker f) := .of_finite
    have : Module.Finite A (N ⧸ LinearMap.range f) := .of_finite
    exact ⟨(isPseudoNull_iff_finite hdim).mpr h₁, (isPseudoNull_iff_finite hdim).mpr h₂⟩

open PowerSeries in
-- Over `Λ = ℤ_p⟦T⟧`, multiplication by `p` on `Λ ⧸ (T) ≅ ℤ_p` is a pseudo-isomorphism, although
-- its cokernel `𝔽_p` is nonzero: the support of `Λ ⧸ (T)` contains no height-one prime through
-- `p`, since a prime containing `p` and `T` has height two.
example (p : ℕ) [Fact p.Prime] :
    IsPseudoIsomorphism
        (LinearMap.lsmul ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {(X : ℤ_[p]⟦X⟧)}) (C (p : ℤ_[p]))) ∧
      ¬ Function.Surjective
        (LinearMap.lsmul ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {(X : ℤ_[p]⟦X⟧)}) (C (p : ℤ_[p]))) := by
  refine ⟨isPseudoIsomorphism_lsmul _ fun 𝔭 h𝔭 hht hp ↦ ?_, fun h ↦ ?_⟩
  · rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient,
      Ideal.span_singleton_le_iff_mem] at h𝔭
    exact (PadicInt.one_lt_height_of_C_p_mem_of_X_mem hp h𝔭).not_ge hht
  · -- The constant coefficient of an element of `p • (Λ ⧸ (T))` is divisible by `p`.
    obtain ⟨y, hy⟩ := h (Ideal.Quotient.mk _ 1)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.lsmul_apply, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul,
      Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    have := congrArg constantCoeff hz
    simp only [map_sub, map_mul, constantCoeff_C, map_one, constantCoeff_X, zero_mul] at this
    exact (PadicInt.irreducible_p (p := p)).not_isUnit
      (.of_mul_eq_one (constantCoeff y) (by linear_combination this))

open PowerSeries IsLocalRing in
-- Over `Λ = ℤ_p⟦T⟧`, the inclusion of the maximal ideal `𝔪 = (p, T)` is a pseudo-isomorphism,
-- but no linear map `Λ → 𝔪` is one, so the torsion hypothesis of
-- `IsPseudoIsomorphism.exists_reverse` cannot be dropped. A map `Λ → 𝔪` is multiplication by
-- some `m ∈ 𝔪`; for `m = 0` its kernel `Λ` is not torsion, and otherwise, by Krull's principal
-- ideal theorem, a prime of height one minimal over `(m)` lies in the support of its cokernel.
example (p : ℕ) [Fact p.Prime] :
    IsPseudoIsomorphism (maximalIdeal ℤ_[p]⟦X⟧).subtype ∧
      ∀ g : ℤ_[p]⟦X⟧ →ₗ[ℤ_[p]⟦X⟧] maximalIdeal ℤ_[p]⟦X⟧, ¬ IsPseudoIsomorphism g := by
  -- A prime containing the maximal ideal `(p, X)` has height two.
  have hp : C (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p]⟦X⟧ := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_C]
    exact PadicInt.irreducible_p.not_isUnit
  have hX : X ∈ maximalIdeal ℤ_[p]⟦X⟧ := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X]
    exact not_isUnit_zero
  have hm (𝔭 : Ideal ℤ_[p]⟦X⟧) [𝔭.IsPrime] (h : maximalIdeal ℤ_[p]⟦X⟧ ≤ 𝔭) : 1 < 𝔭.height :=
    PadicInt.one_lt_height_of_C_p_mem_of_X_mem (h hp) (h hX)
  refine ⟨⟨?_, ?_⟩, fun g hg ↦ ?_⟩
  · rw [Submodule.ker_subtype]
    exact .of_subsingleton
  · rw [Submodule.range_subtype, isPseudoNull_quotient_iff]
    exact fun 𝔭 h𝔭 ↦ hm 𝔭.asIdeal h𝔭
  -- A linear map `g : Λ → 𝔪` is multiplication by `m = g 1`.
  set m : ℤ_[p]⟦X⟧ := (g 1 : ℤ_[p]⟦X⟧)
  have hg' (y : ℤ_[p]⟦X⟧) : (g y : ℤ_[p]⟦X⟧) = y * m := by
    simpa using congrArg Subtype.val (g.map_smul y 1)
  by_cases hm0 : m = 0
  · -- If `m = 0` then `ker g = Λ` is not torsion.
    obtain ⟨⟨s, hs⟩, hs1⟩ := hg.isPseudoNull_ker.isTorsion (x := ⟨1, Subtype.ext hm0⟩)
    exact nonZeroDivisors.ne_zero hs (by simpa using congrArg Subtype.val hs1)
  · -- Otherwise a height-one prime `𝔭` minimal over `(m)` lies in the support of `coker g`.
    have hmu : Ideal.span {m} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal _).mp (g 1).2
    obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes hmu
    have := h𝔭.1.1
    have hht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔭
    obtain ⟨x, hx𝔪, hx𝔭⟩ : ∃ x ∈ maximalIdeal ℤ_[p]⟦X⟧, x ∉ 𝔭 := by
      by_contra! h
      exact (hm 𝔭 h).not_ge hht
    refine (hg.isPseudoNull_coker.one_lt_height (𝔭 := ⟨𝔭, this⟩)
      (Module.mem_support_iff_of_finite.mpr fun r hr ↦ ?_)).not_ge hht
    obtain ⟨y, hy⟩ : r • (⟨x, hx𝔪⟩ : maximalIdeal ℤ_[p]⟦X⟧) ∈ LinearMap.range g := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact Module.mem_annihilator.mp hr _
    have hrx : r * x ∈ 𝔭 := by
      have := congrArg Subtype.val hy
      rw [hg'] at this
      simp only [Submodule.coe_smul, smul_eq_mul] at this
      exact this ▸ Ideal.mul_mem_left _ y (h𝔭.1.2 (Ideal.mem_span_singleton_self m))
    exact (h𝔭.1.1.mem_or_mem hrx).resolve_right hx𝔭

end TauCeti.Iwasawa

end
