/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Flat.Localization
public import TauCeti.LinearAlgebra.FreeModule.Filtration

/-!
# The free locus over a reduced ring, and of a filtered module

Every module over a reduced ring is free at each minimal prime. For a finitely presented
module, Mathlib's openness of the free locus therefore gives an open neighbourhood of the
minimal primes where it is locally free.

A module with an exhaustive increasing filtration is free at every prime where all the
subquotients of the filtration are free.

The rank of `R^k` at every prime is `k`, with no nontriviality hypothesis on `R`: a ring with a
prime ideal is nontrivial. No finiteness is assumed, so this applies to modules
that are not finitely generated over the base, as in the proof of generic freeness in
`TauCeti.RingTheory.Spectrum.Prime.GenericFreeness`.

## Main declarations

* `Module.mem_freeLocus_of_mem_minimalPrimes`: over a reduced ring, every module is free at the
  minimal primes.
* `Module.iInter_freeLocus_subquotient_subset_freeLocus`: a filtered module is free wherever all
  subquotients of the filtration are.
* `Module.rankAtStalk_fin_fun`: the free module `R^k` has rank `k` at every prime.

## References

* The Stacks Project, Tags 051R and 051Z, for generic freeness.
-/

public section

namespace Module

section Reduced

variable {R : Type*} (M : Type*) [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]

/-- Over a reduced ring, every module is free at each minimal prime, where the localization of
the ring is a field. -/
theorem mem_freeLocus_of_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    ⟨p, hp.1.1⟩ ∈ freeLocus R M := by
  have := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  let : Field (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact Module.Free.of_divisionRing _ _

variable (R) [Nontrivial R]

/-- A module over a nonzero reduced ring has nonempty free locus. -/
theorem freeLocus_nonempty : (freeLocus R M).Nonempty := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) bot_ne_top
  exact ⟨_, mem_freeLocus_of_mem_minimalPrimes M hp⟩

end Reduced

section Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module is free at every prime at which all subquotients `N (j + 1) ⧸ N j` of an exhaustive
increasing filtration `⊥ = N 0 ≤ N 1 ≤ ⋯` are free.

No finiteness is assumed, so this applies to filtrations of modules that are not finitely
generated over the base ring. -/
theorem iInter_freeLocus_subquotient_subset_freeLocus (N : ℕ → Submodule R M)
    (hN : Monotone N) (h0 : N 0 = ⊥) (htop : ⨆ j, N j = ⊤) :
    ⋂ j, freeLocus R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))) ⊆ freeLocus R M := by
  intro p hp
  rw [Set.mem_iInter] at hp
  let S := p.asIdeal.primeCompl
  let Rp := Localization.AtPrime p.asIdeal
  let L : ℕ → Submodule Rp (LocalizedModule S M) := fun j ↦ (N j).localized S
  have hL : Monotone L := fun _ _ hij ↦
    (Submodule.localized'gi Rp S (LocalizedModule.mkLinearMap S M)).gc.monotone_l (hN hij)
  refine Module.Free.of_filtration L hL (by simp [L, h0])
    (by simp only [L]; rw [← Submodule.localized'_iSup, htop, Submodule.localized'_top])
    fun j ↦ ?_
  -- Localize the subquotient through the localization of `N (j + 1)`.
  let g := (N (j + 1)).toLocalized' Rp S (LocalizedModule.mkLinearMap S M)
  let W := (N j).submoduleOf (N (j + 1))
  have hcoe (m : N (j + 1)) (s : S) :
      ((IsLocalizedModule.mk' g m s : L (j + 1)) : LocalizedModule S M) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) (m : M) s := by
    rw [eq_comm, IsLocalizedModule.mk'_eq_iff, ← Submodule.coe_smul_of_tower,
      IsLocalizedModule.mk'_cancel', Submodule.toLocalized'_apply_coe]
  have heq : W.localized' Rp S g = (L j).submoduleOf (L (j + 1)) := by
    ext x
    rw [Submodule.mem_localized']
    constructor
    · rintro ⟨m, hm, s, rfl⟩
      exact ⟨m, hm, s, (hcoe m s).symm⟩
    · rintro ⟨m, hm, s, hx⟩
      exact ⟨⟨m, hN j.le_succ hm⟩, hm, s, Subtype.ext ((hcoe _ s).trans hx)⟩
  have hfree : Module.Free Rp (L (j + 1) ⧸ W.localized' Rp S g) :=
    (mem_freeLocus_of_isLocalization p Rp _ (W.toLocalizedQuotient' Rp S g)).mp (hp j)
  exact Module.Free.of_equiv (Submodule.quotEquivOfEq _ _ heq)

end Filtration

/-- The free module `R^k` has rank `k` at every prime of `R`. -/
theorem rankAtStalk_fin_fun {R : Type*} [CommRing R] (k : ℕ) (p : PrimeSpectrum R) :
    rankAtStalk (R := R) (Fin k → R) p = k := by
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩
  simp

end Module

namespace PrimeSpectrum

open Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If a base prime belongs to the free locus of an algebra, that algebra is flat
over the base after localizing at any prime above it. -/
theorem flat_localization_of_comap_mem_freeLocus (q : PrimeSpectrum S)
    (hq : q.comap (algebraMap R S) ∈ freeLocus R S) :
    Flat R (Localization.AtPrime q.asIdeal) := by
  let p := q.comap (algebraMap R S)
  let U := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  let B := Localization U
  have hU : U ≤ q.asIdeal.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let : Algebra B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ U q.asIdeal.primeCompl hU
  have : IsScalarTower S B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ U q.asIdeal.primeCompl hU
  have : IsScalarTower R B (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq R S B, ← RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq S B (Localization.AtPrime q.asIdeal),
        ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)])
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl S) := hq
  have : Flat R (Localization.AtPrime p.asIdeal) :=
    IsLocalization.flat _ p.asIdeal.primeCompl
  have : Flat R (LocalizedModule p.asIdeal.primeCompl S) :=
    Flat.trans R (Localization.AtPrime p.asIdeal) _
  have : Flat R B := Flat.of_linearEquiv
    (IsLocalizedModule.iso p.asIdeal.primeCompl (IsScalarTower.toAlgHom R S B).toLinearMap).symm
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap S B))
      (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le B _ U q.asIdeal.primeCompl hU
  have : Flat B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.flat _ (q.asIdeal.primeCompl.map (algebraMap S B))
  exact Flat.trans R B _

end PrimeSpectrum
