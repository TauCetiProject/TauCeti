/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Projective.Trans
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.RingTheory.PicardGroup.RankOne

/-!
# The top exterior power of a finite projective module is invertible

Let `M` be a finite flat module over a commutative ring `R`. Exterior powers commute with base
change (`TauCeti.exteriorPower.equivBaseChange`), so at a prime `𝔭` the rank of `⋀[R]^n M` is the
binomial coefficient `(rank_𝔭 M).choose n`. If `M` is moreover projective, so is every
`⋀[R]^n M` (`exteriorPower.instProjective`).

If `M` is finite projective of constant rank `d`, its top exterior power `⋀[R]^d M`, the
determinant of `M`, is therefore an invertible module, and an endomorphism `f` of `M` acts on it
by its determinant: `⋀^d f = projectiveDet f • id`. This is the determinant used for norms of
invertible modules along finite projective algebras.

## Main results

* `exteriorPower.rankAtStalk_eq_choose`: the rank of `⋀[R]^n M` at a prime.
* `exteriorPower.invertible_of_rankAtStalk_eq`: the top exterior power of a finite projective
  module of constant rank is invertible.
* `exteriorPower.invertible_of_invertible_of_rankAtStalk_eq`: the same holds for an invertible
  module over a finite projective algebra of constant rank.
* `exteriorPower.map_eq_projectiveDet_smul_id`: an endomorphism acts on the top exterior power by
  multiplication by its determinant.

## References

* O. Goldman, *Determinants in projective modules*, Nagoya Math. J. 18 (1961), 27–36.
-/

public section

open Module TensorProduct

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The rank of the `n`th exterior power of a finite flat module at a prime `𝔭` is the binomial
coefficient `(rank_𝔭 M).choose n`. -/
theorem rankAtStalk_eq_choose [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (p : PrimeSpectrum R) :
    rankAtStalk (⋀[R]^n M) p = (rankAtStalk M p).choose n := by
  let A := Localization.AtPrime p.asIdeal
  have : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  rw [rankAtStalk_eq_finrank_tensorProduct, rankAtStalk_eq_finrank_tensorProduct,
    ← (TauCeti.exteriorPower.equivBaseChange A n).finrank_eq, finrank_eq]

/-- The top exterior power `⋀[R]^d M` of a finite projective module `M` of constant rank `d` is an
invertible module. -/
theorem invertible_of_rankAtStalk_eq [Module.Finite R M] [Module.Projective R M] {d : ℕ}
    (hd : ∀ p, rankAtStalk (R := R) M p = d) : Module.Invertible R (⋀[R]^d M) :=
  .of_rankAtStalk_eq_one fun p ↦ by rw [rankAtStalk_eq_choose, hd, Nat.choose_self]

/-- Let `S` be a finite projective `R`-algebra of constant rank `d`. The top exterior power
`⋀[R]^d M` of an invertible `S`-module `M`, viewed as an `R`-module, is an invertible `R`-module. -/
theorem invertible_of_invertible_of_rankAtStalk_eq {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S] [Module S M] [IsScalarTower R S M]
    [Module.Invertible S M] {d : ℕ} (hd : ∀ p, rankAtStalk (R := R) S p = d) :
    Module.Invertible R (⋀[R]^d M) :=
  have : Module.Finite R M := .trans S M
  have : Module.Projective R M := .trans (S := S)
  invertible_of_rankAtStalk_eq fun p ↦ by
    rw [Module.Invertible.rankAtStalk_eq_rankAtStalk_algebra (S := S), hd]

/-- An endomorphism `f` of a finite projective module of constant rank `d` acts on the top exterior
power `⋀[R]^d M` by multiplication by its determinant `LinearMap.projectiveDet f`. -/
theorem map_eq_projectiveDet_smul_id [Module.Finite R M] [Module.Projective R M] {d : ℕ}
    (hd : ∀ p, rankAtStalk (R := R) M p = d) (f : Module.End R M) :
    map d f = LinearMap.projectiveDet f • LinearMap.id := by
  refine LinearMap.ext fun x ↦ Module.eq_of_localization_maximal
    (fun P _ ↦ Localization.AtPrime P ⊗[R] ⋀[R]^d M)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) _ 1) _ _ fun P _ ↦ ?_
  let A := Localization.AtPrime P
  have : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have hfin : finrank A (A ⊗[R] M) = d := by
    rw [← rankAtStalk_eq_finrank_tensorProduct (M := M) ⟨P, inferInstance⟩, hd]
  -- Over the local ring `A`, the module `A ⊗[R] M` is free of rank `d`, where the claim is the
  -- free case `LinearMap.map_exteriorPower_finrank_eq_det_smul`, transported to `A ⊗[R] ⋀^d M`.
  let e := TauCeti.exteriorPower.equivBaseChange (R := R) (M := M) A d
  obtain ⟨y, hy⟩ := e.surjective (1 ⊗ₜ[R] x)
  have key := LinearMap.map_exteriorPower_finrank_eq_det_smul (f.baseChange A)
  subst hfin
  have h := congr(e ($key y))
  rw [TauCeti.exteriorPower.equivBaseChange_map, hy, ← LinearMap.projectiveDet_eq_det,
    LinearMap.projectiveDet_baseChange, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    hy] at h
  simpa [TensorProduct.smul_tmul', Algebra.smul_def] using h

end exteriorPower
