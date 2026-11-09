/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup
public import TauCeti.LinearAlgebra.Determinant.ConstantRank
public import TauCeti.RingTheory.Flat.Rank

/-!
# Invertible modules are the finite projective modules of rank one

A module `M` over a commutative ring `R` is invertible (`Module.Invertible R M`) exactly when it
is finite projective and its rank `Module.rankAtStalk M` is constantly one, that is, when it
becomes free of rank one after localizing at every prime.

An invertible module is finite projective (Mathlib), and localizes to an invertible, hence free,
module over each local ring `R_𝔭`, so its rank is one. Conversely, on a finite projective module
of rank one every endomorphism is multiplication by its determinant
(`LinearMap.eq_projectiveDet_smul_id`), so `R ≃ Module.End R M`. Composing with
`dualTensorHomEquiv : Dual R M ⊗[R] M ≃ End R M` gives `Dual R M ⊗[R] M ≃ R`, which makes `M`
invertible.

## Main results

* `Module.Invertible.rankAtStalk_eq_one`: an invertible module has rank one at every prime.
* `Module.Invertible.of_rankAtStalk_eq_one`: a finite projective module of rank one at every prime
  is invertible.
* `Module.invertible_iff_rankAtStalk_eq_one`: the resulting characterization.
* `Module.Invertible.rankAtStalk_eq_rankAtStalk_algebra`: over a finite flat `R`-algebra `S`, an
  invertible `S`-module has the same rank over `R` as `S`.

## References

* The Stacks Project, Algebra, Section *Picard groups of rings* (Tag 0AFW), where invertible
  modules are characterized as the finite locally free modules of rank one.
-/

public section

open Module

namespace Module.Invertible

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An invertible module has rank one at every prime: its localization is an invertible module
over a local ring, hence free of rank one. -/
theorem rankAtStalk_eq_one [Module.Invertible R M] (p : PrimeSpectrum R) :
    rankAtStalk M p = 1 := by
  rw [rankAtStalk]
  exact Module.Invertible.finrank_eq_one ..

/-- A finite projective module whose rank is one at every prime is invertible. -/
theorem of_rankAtStalk_eq_one [Module.Finite R M] [Module.Projective R M]
    (h : ∀ p, rankAtStalk (R := R) M p = 1) : Module.Invertible R M := by
  have hsmul (c : R) : LinearMap.lsmul R M c = c • LinearMap.id := by ext; simp
  have hbij : Function.Bijective (LinearMap.lsmul R M) := by
    refine ⟨fun c c' hc ↦ ?_, fun f ↦ ⟨LinearMap.projectiveDet f, ?_⟩⟩
    · rw [hsmul, hsmul] at hc
      simpa [LinearMap.projectiveDet_smul_id h] using congr(LinearMap.projectiveDet $hc)
    · rw [hsmul, ← LinearMap.eq_projectiveDet_smul_id h]
  exact .right (dualTensorHomEquiv R M M ≪≫ₗ (LinearEquiv.ofBijective _ hbij).symm)

/-- Over a finite flat `R`-algebra `S`, an invertible `S`-module has the same rank over `R` as `S`
at every prime of `R`. -/
theorem rankAtStalk_eq_rankAtStalk_algebra {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] [Module S M] [IsScalarTower R S M]
    [Module.Invertible S M] (p : PrimeSpectrum R) :
    rankAtStalk (R := R) M p = rankAtStalk (R := R) S p := by
  rw [TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq (A := S) rankAtStalk_eq_one, one_mul]

end Module.Invertible

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module is invertible if and only if it is finite projective of rank one at every prime. -/
theorem invertible_iff_rankAtStalk_eq_one :
    Module.Invertible R M ↔
      Module.Finite R M ∧ Module.Projective R M ∧ ∀ p, rankAtStalk (R := R) M p = 1 :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance, Module.Invertible.rankAtStalk_eq_one⟩,
    fun ⟨_, _, h⟩ ↦ .of_rankAtStalk_eq_one h⟩

end Module
