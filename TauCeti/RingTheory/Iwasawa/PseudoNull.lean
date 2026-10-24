/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Support

import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.LocalRing.Quotient
import TauCeti.NumberTheory.Padics.PowerSeriesIdeal
import TauCeti.RingTheory.Finiteness.Cardinality
import TauCeti.RingTheory.Ideal.Height

/-!
# Pseudo-null modules

A module `M` over a commutative ring `A` is *pseudo-null* if it is finitely generated and its
localization `M_𝔭` vanishes at every prime `𝔭` of height at most one; equivalently, every prime in
the support of `M` has height at least two. Pseudo-null modules are the modules that the structure
theory of finitely generated modules over a noetherian normal domain ignores: that theory
classifies modules up to maps with pseudo-null kernel and cokernel (pseudo-isomorphisms), and the
characteristic ideal of a torsion module only sees its localizations at height-one primes.

Over the Iwasawa algebra `Λ = O⟦T⟧` of a complete discrete valuation ring `O` with finite residue
field, a two-dimensional noetherian local ring, the pseudo-null modules are exactly the finite
ones (`isPseudoNull_iff_finite`). The statement is proved for any noetherian local ring of Krull
dimension two with finite residue field.

## Main definitions

* `TauCeti.Iwasawa.IsPseudoNull A M`: `M` is finitely generated and `M_𝔭 = 0` for every prime
  `𝔭` of `A` of height at most one.

## Main results

* `TauCeti.Iwasawa.isPseudoNull_iff_support`: `M` is pseudo-null iff it is finitely generated and
  every prime of its support has height at least two.
* `TauCeti.Iwasawa.isPseudoNull_iff_annihilator`: the annihilator criterion, every prime
  containing `ann_A M` has height at least two; for a quotient `A ⧸ I` this is
  `TauCeti.Iwasawa.isPseudoNull_quotient_iff`.
* `TauCeti.Iwasawa.IsPseudoNull.isTorsion`: over a domain, pseudo-null modules are torsion.
* `TauCeti.Iwasawa.isPseudoNull_iff_subsingleton`: over a ring of dimension at most one, such as a
  Dedekind domain, only the zero module is pseudo-null.
* `TauCeti.Iwasawa.IsPseudoNull.of_injective`, `TauCeti.Iwasawa.IsPseudoNull.of_surjective` and
  `TauCeti.Iwasawa.IsPseudoNull.of_exact`: over a noetherian ring, submodules, quotients and
  extensions of pseudo-null modules are pseudo-null.
* `TauCeti.Iwasawa.isPseudoNull_iff_finite`: over a noetherian local ring of dimension two with
  finite residue field, a finitely generated module is pseudo-null iff it is finite.

The examples at the end of the file check the definition over `Λ = ℤ_p⟦T⟧`: the module
`Λ ⧸ (p, T) = 𝔽_p` is pseudo-null, while `Λ ⧸ (p)` is not, because its support contains the
height-one prime `(p)`; and over `ℤ_p` itself, `𝔽_p` is not pseudo-null.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (5.1.4) with Remarks 1–4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §13.1.
-/

public section

namespace TauCeti.Iwasawa

open IsLocalRing

variable (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]

/-- A module `M` over a commutative ring `A` is *pseudo-null* if it is finitely generated and its
localization at every prime of height at most one vanishes. -/
structure IsPseudoNull : Prop where
  /-- A pseudo-null module is finitely generated. -/
  finite : Module.Finite A M
  /-- The localization of a pseudo-null module at a prime of height at most one vanishes. -/
  subsingleton_localizedModule (𝔭 : PrimeSpectrum A) (h𝔭 : 𝔭.asIdeal.height ≤ 1) :
    Subsingleton (LocalizedModule 𝔭.asIdeal.primeCompl M)

variable {A M}

/-- A module is pseudo-null iff it is finitely generated and every prime in its support has
height at least two. -/
theorem isPseudoNull_iff_support :
    IsPseudoNull A M ↔
      Module.Finite A M ∧ ∀ 𝔭 ∈ Module.support A M, 1 < 𝔭.asIdeal.height := by
  refine ⟨fun h ↦ ⟨h.finite, fun 𝔭 h𝔭 ↦ ?_⟩, fun h ↦ ⟨h.1, fun 𝔭 h𝔭 ↦ ?_⟩⟩
  · by_contra hlt
    exact Module.notMem_support_iff.mpr (h.subsingleton_localizedModule 𝔭 (not_lt.mp hlt)) h𝔭
  · exact Module.notMem_support_iff.mp fun hmem ↦ (h.2 𝔭 hmem).not_ge h𝔭

/-- Every prime in the support of a pseudo-null module has height at least two. -/
theorem IsPseudoNull.one_lt_height (h : IsPseudoNull A M) {𝔭 : PrimeSpectrum A}
    (h𝔭 : 𝔭 ∈ Module.support A M) : 1 < 𝔭.asIdeal.height :=
  (isPseudoNull_iff_support.mp h).2 𝔭 h𝔭

/-- The annihilator criterion: a finitely generated module is pseudo-null iff every prime
containing its annihilator has height at least two. -/
theorem isPseudoNull_iff_annihilator [Module.Finite A M] :
    IsPseudoNull A M ↔
      ∀ 𝔭 : PrimeSpectrum A, Module.annihilator A M ≤ 𝔭.asIdeal → 1 < 𝔭.asIdeal.height := by
  simp [isPseudoNull_iff_support, Module.mem_support_iff_of_finite, ‹Module.Finite A M›]

/-- The quotient `A ⧸ I` is pseudo-null iff every prime containing `I` has height at least two. -/
theorem isPseudoNull_quotient_iff (I : Ideal A) :
    IsPseudoNull A (A ⧸ I) ↔ ∀ 𝔭 : PrimeSpectrum A, I ≤ 𝔭.asIdeal → 1 < 𝔭.asIdeal.height := by
  rw [isPseudoNull_iff_annihilator, Ideal.annihilator_quotient]

/-- The zero module is pseudo-null. -/
theorem IsPseudoNull.of_subsingleton [Subsingleton M] : IsPseudoNull A M :=
  isPseudoNull_iff_support.mpr ⟨inferInstance, by simp [Module.support_eq_empty]⟩

/-- Over a domain, a pseudo-null module is torsion: its localization at the height-zero prime `⊥`
vanishes. -/
theorem IsPseudoNull.isTorsion [IsDomain A] (h : IsPseudoNull A M) : Module.IsTorsion A M := by
  intro m
  have hbot : ((⊥ : PrimeSpectrum A).asIdeal).height ≤ 1 := by
    simp [PrimeSpectrum.asIdeal_bot, Ideal.height_bot]
  obtain ⟨r, hr, hrm⟩ :=
    Module.notMem_support_iff'.mp
      (Module.notMem_support_iff.mpr (h.subsingleton_localizedModule ⊥ hbot)) m
  exact ⟨⟨r, mem_nonZeroDivisors_of_ne_zero (by simpa using hr)⟩, hrm⟩

/-- Over a ring of Krull dimension at most one, such as a Dedekind domain, only the zero module is
pseudo-null. -/
theorem isPseudoNull_iff_subsingleton [Ring.KrullDimLE 1 A] :
    IsPseudoNull A M ↔ Subsingleton M := by
  refine ⟨fun h ↦ Module.support_eq_empty_iff (R := A).mp ?_, fun _ ↦ .of_subsingleton (A := A)⟩
  refine Set.eq_empty_of_forall_notMem fun 𝔭 h𝔭 ↦ (h.one_lt_height h𝔭).not_ge ?_
  have := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔭.asIdeal)
  have hdim : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp inferInstance
  exact_mod_cast this.trans hdim

/-- A submodule of a pseudo-null module over a noetherian ring is pseudo-null. -/
theorem IsPseudoNull.of_injective [IsNoetherianRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (h : IsPseudoNull A N) (f : M →ₗ[A] N) (hf : Function.Injective f) : IsPseudoNull A M := by
  have := h.finite
  have : Module.Finite A M := .of_injective f hf
  exact isPseudoNull_iff_support.mpr
    ⟨this, fun 𝔭 h𝔭 ↦ h.one_lt_height (Module.support_subset_of_injective f hf h𝔭)⟩

/-- A quotient of a pseudo-null module is pseudo-null. -/
theorem IsPseudoNull.of_surjective {N : Type*} [AddCommGroup N] [Module A N]
    (h : IsPseudoNull A M) (f : M →ₗ[A] N) (hf : Function.Surjective f) : IsPseudoNull A N := by
  have := h.finite
  exact isPseudoNull_iff_support.mpr
    ⟨.of_surjective f hf, fun 𝔭 h𝔭 ↦ h.one_lt_height (Module.support_subset_of_surjective f hf h𝔭)⟩

/-- An extension of pseudo-null modules is pseudo-null. -/
theorem IsPseudoNull.of_exact {N P : Type*} [AddCommGroup N] [Module A N] [AddCommGroup P]
    [Module A P] {f : M →ₗ[A] N} {g : N →ₗ[A] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hM : IsPseudoNull A M)
    (hP : IsPseudoNull A P) : IsPseudoNull A N := by
  have := hM.finite
  have := hP.finite
  refine isPseudoNull_iff_support.mpr ⟨.of_exact hfg hg, fun 𝔭 h𝔭 ↦ ?_⟩
  rw [Module.support_of_exact hfg hf hg] at h𝔭
  exact h𝔭.elim hM.one_lt_height hP.one_lt_height

/-- In a short exact sequence over a noetherian ring, the middle term is pseudo-null iff both
outer terms are. -/
theorem isPseudoNull_iff_of_exact [IsNoetherianRing A] {N P : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] {f : M →ₗ[A] N} {g : N →ₗ[A] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    IsPseudoNull A N ↔ IsPseudoNull A M ∧ IsPseudoNull A P :=
  ⟨fun h ↦ ⟨h.of_injective f hf, h.of_surjective g hg⟩,
    fun h ↦ h.1.of_exact hfg hf hg h.2⟩

section Local

variable [IsLocalRing A]

/-- Over a noetherian local ring of dimension two with finite residue field, for example the
Iwasawa algebra `O⟦T⟧` of a complete discrete valuation ring `O` with finite residue field, a
finitely generated module is pseudo-null iff it is finite. -/
theorem isPseudoNull_iff_finite [IsNoetherianRing A] [Finite (ResidueField A)]
    (hdim : ringKrullDim A = 2) [Module.Finite A M] : IsPseudoNull A M ↔ Finite M := by
  -- In dimension two the maximal ideal is the only prime of height at least two.
  have key (𝔭 : Ideal A) [𝔭.IsPrime] : 1 < 𝔭.height ↔ 𝔭 = maximalIdeal A :=
    Ideal.lt_height_iff_eq_maximalIdeal (n := 1) hdim
  -- Both sides say that the annihilator contains a power of the maximal ideal.
  rw [isPseudoNull_iff_annihilator,
    Module.finite_iff_finite_quotient_annihilator (A := A), finite_quotient_iff]
  refine ⟨fun h ↦ Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _),
    fun ⟨n, hn⟩ 𝔭 h𝔭 ↦ ?_⟩
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hJ, hJp⟩ ↦ ?_
    rw [(key J).mp (h ⟨J, hJp⟩ hJ)]
  · rw [key]
    exact le_antisymm (le_maximalIdeal Ideal.IsPrime.ne_top')
      (Ideal.IsPrime.le_of_pow_le (hn.trans h𝔭))

end Local

open PowerSeries in
-- Over `Λ = ℤ_p⟦T⟧`, `Λ ⧸ (p, T) = 𝔽_p` is pseudo-null, since every prime containing `(p, T)`
-- lies above the chain `⊥ < (p)`, while `Λ ⧸ (p)` is not, since its support contains the
-- height-one prime `(p)`, the kernel of the reduction `ℤ_p⟦T⟧ → 𝔽_p⟦T⟧`.
example (p : ℕ) [Fact p.Prime] :
    IsPseudoNull ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C (p : ℤ_[p]), X}) ∧
      ¬ IsPseudoNull ℤ_[p]⟦X⟧ (ℤ_[p]⟦X⟧ ⧸ Ideal.span {C (p : ℤ_[p])}) := by
  refine ⟨(isPseudoNull_quotient_iff _).mpr fun 𝔮 h𝔮 ↦ ?_, fun h ↦ ?_⟩
  · exact PadicInt.one_lt_height_of_C_p_mem_of_X_mem (h𝔮 (Ideal.subset_span (by simp)))
      (h𝔮 (Ideal.subset_span (by simp)))
  · exact ((isPseudoNull_quotient_iff _).mp h ⟨_, PadicInt.isPrime_span_C_p⟩ le_rfl).ne'
      PadicInt.height_span_C_p

-- Over the discrete valuation ring `ℤ_p`, of dimension one, `ℤ_p ⧸ (p) = 𝔽_p` is not pseudo-null.
example (p : ℕ) [Fact p.Prime] : ¬ IsPseudoNull ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  rw [isPseudoNull_iff_subsingleton, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]
  exact PadicInt.irreducible_p.not_isUnit

end TauCeti.Iwasawa

end
