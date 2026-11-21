/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Algebra homomorphisms of local algebras

Over any commutative semiring `k`, every `k`-algebra augmentation `R →ₐ[k] k` of a local
`k`-algebra `R` (not assumed commutative) reflects units (`AlgHom.isLocalHom_to_ring`), so whenever
a `k`-algebra `S` admits a `k`-algebra augmentation `S →ₐ[k] k`, every `k`-algebra homomorphism
`R →ₐ[k] S` out of `R` automatically reflects units (`AlgHom.isLocalHom_of_algHom`). When `k` is a
field, `R` admits at most one `k`-algebra homomorphism `R →ₐ[k] k`
(`AlgHom.subsingleton_of_isLocalRing`), and every `k`-algebra homomorphism `R →ₐ[k] S` commutes with
any augmentations on `R` and `S` (`AlgHom.comp_eq_of_isLocalRing`).

In the commutative case, over a commutative ring `k` (for instance whenever `R` admits a
`k`-algebra augmentation `R →ₐ[k] k`, via `AlgHom.surjective_algebraMap_residueField`), for local
`k`-algebras `R` and `S` with `S` separated for its maximal ideal and
`algebraMap k (ResidueField R)` surjective, a `k`-algebra homomorphism `ψ : R →ₐ[k] S` agreeing on a
generating set of `maximalIdeal R` with a local `k`-algebra homomorphism `φ : R →ₐ[k] S` equals `φ`
(`AlgHom.ext_of_span_eq_maximalIdeal`), deduced from the general adic uniqueness result
`AlgHom.ext_of_isHausdorff` in `TauCeti.RingTheory.AdicCompletion.AlgHom`, even when `R` is not
finitely generated as a `k`-algebra (as for rings of analytic germs or formal power series).

## Main results

* `AlgHom.isLocalHom_to_ring`: any `k`-algebra augmentation `R →ₐ[k] k` of a local `k`-algebra over
  a commutative semiring `k` reflects units.
* `AlgHom.isLocalHom_of_algHom`: any `φ : R →ₐ[k] S` from a local `k`-algebra into a `k`-algebra
  admitting `S →ₐ[k] k` reflects units.
* `AlgHom.subsingleton_of_isLocalRing`: `R →ₐ[k] k` is a subsingleton for a local `k`-algebra `R`
  over a field `k`.
* `AlgHom.surjective_algebraMap_residueField`: if a commutative local `k`-algebra `R` over a
  commutative ring `k` admits `R →ₐ[k] k`, then `algebraMap k (ResidueField R)` is surjective.
* `AlgHom.ext_of_span_eq_maximalIdeal`: uniqueness of `k`-algebra homomorphisms of local rings into
  maximal-ideal-separated targets from agreement on generators of the maximal ideal.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
-/

public section

namespace AlgHom

section Augmentation

/-- Over any commutative semiring `k`, every `k`-algebra augmentation `R →ₐ[k] k` of a local ring
`R` (not assumed commutative) reflects units. -/
instance isLocalHom_to_ring {k R : Type*} [CommSemiring k] [Ring R] [IsLocalRing R] [Algebra k R]
    (ε : R →ₐ[k] k) : IsLocalHom ε where
  map_nonunit r hr := by
    have : Nontrivial k := (algebraMap k R).domain_nontrivial
    by_contra hnr
    have hker : ¬ IsUnit (algebraMap k R (ε r) - r) := fun hu ↦ by
      have h0 : algebraMap k R (ε (algebraMap k R (ε r) - r)) = 0 := by
        have h : algebraMap k R (ε (algebraMap k R (ε r) - r)) + algebraMap k R (ε r) =
            algebraMap k R (ε r) := by
          rw [← map_add, ← map_add, sub_add_cancel, ε.commutes]
          rfl
        simpa using congrArg (· - algebraMap k R (ε r)) h
      have hε : ε (algebraMap k R (ε r) - r) = 0 :=
        (ε.commutes _).symm.trans ((congrArg ε h0).trans (map_zero ε))
      exact not_isUnit_zero (hε ▸ hu.map ε)
    have hsum : IsUnit ((algebraMap k R (ε r) - r) + r) := by
      rw [sub_add_cancel]
      exact hr.map (algebraMap k R)
    exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).elim hker hnr

/-- Over a field `k`, a local `k`-algebra `R` (not assumed commutative) admits at most one
`k`-algebra homomorphism `R →ₐ[k] k`. -/
instance subsingleton_of_isLocalRing {k R : Type*} [Field k] [Ring R] [IsLocalRing R]
    [Algebra k R] : Subsingleton (R →ₐ[k] k) where
  allEq φ ψ := ext fun r ↦ by
    have hx : ¬ IsUnit (r - algebraMap k R (ψ r)) := fun hu ↦ by
      have hu0 : IsUnit (0 : k) := by simpa [ψ.commutes] using hu.map ψ
      exact not_isUnit_zero hu0
    have hφx : ¬ IsUnit (φ (r - algebraMap k R (ψ r))) := fun hu ↦
      hx (isUnit_of_map_unit φ _ hu)
    by_contra hne
    exact hφx (IsUnit.mk0 _ (by simpa [φ.commutes, sub_eq_zero] using hne))

/-- Any `k`-algebra homomorphism out of a local `k`-algebra over a field `k` commutes with
`k`-algebra augmentations on source and target. -/
theorem comp_eq_of_isLocalRing {k R S : Type*} [Field k] [Ring R] [IsLocalRing R] [Semiring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (εR : R →ₐ[k] k) (εS : S →ₐ[k] k) :
    εS.comp φ = εR :=
  Subsingleton.elim _ _

/-- Pointwise form of `AlgHom.comp_eq_of_isLocalRing`: a `k`-algebra homomorphism out of a local
`k`-algebra over a field `k` preserves augmentation values. -/
theorem comp_apply_of_isLocalRing {k R S : Type*} [Field k] [Ring R] [IsLocalRing R]
    [Semiring S] [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (εR : R →ₐ[k] k) (εS : S →ₐ[k] k)
    (r : R) : εS (φ r) = εR r :=
  AlgHom.congr_fun (φ.comp_eq_of_isLocalRing εR εS) r

/-- Over any commutative semiring `k`, any `k`-algebra homomorphism `R →ₐ[k] S` out of a local
`k`-algebra `R` into a `k`-algebra `S` admitting a `k`-algebra augmentation `S →ₐ[k] k` reflects
units. -/
theorem isLocalHom_of_algHom {k R S : Type*} [CommSemiring k] [Ring R] [IsLocalRing R] [Semiring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (εS : S →ₐ[k] k) : IsLocalHom φ := by
  have : IsLocalHom (εS.toRingHom.comp φ.toRingHom) := ⟨IsLocalHom.map_nonunit (f := εS.comp φ)⟩
  exact ⟨(isLocalHom_of_comp φ.toRingHom εS.toRingHom).map_nonunit⟩

/-- If a commutative local `k`-algebra `R` over a commutative ring `k` admits a `k`-algebra
augmentation `R →ₐ[k] k`, then `k` surjects onto `ResidueField R`. -/
theorem surjective_algebraMap_residueField {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] (ε : R →ₐ[k] k) :
    Function.Surjective (algebraMap k (IsLocalRing.ResidueField R)) := by
  have : Nontrivial k := (algebraMap k R).domain_nontrivial
  intro a
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
  refine ⟨ε r, ?_⟩
  rw [IsScalarTower.algebraMap_apply k R (IsLocalRing.ResidueField R),
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact not_isUnit_zero (by simpa [ε.commutes] using hu.map ε : IsUnit (0 : k))

end Augmentation

section AdicUniqueness

/-- **Uniqueness of `k`-algebra homomorphisms of local rings from maximal-ideal generators.** Let
`R` and `S` be commutative local `k`-algebras such that `algebraMap k (ResidueField R)` is
surjective and `S` is separated (`IsHausdorff`) with respect to its maximal ideal. If `G` generates
`maximalIdeal R` and `φ, ψ : R →ₐ[k] S` agree on `G` with `φ` local (no locality assumption on `ψ`
is needed), then `φ = ψ`. -/
theorem ext_of_span_eq_maximalIdeal {k R S : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra k R] [Algebra k S]
    [IsHausdorff (IsLocalRing.maximalIdeal S) S] {φ ψ : R →ₐ[k] S} [IsLocalHom φ]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField R)))
    {G : Set R} (hG_span : Ideal.span G = IsLocalRing.maximalIdeal R)
    (hG : Set.EqOn φ ψ G) :
    φ = ψ := by
  have : IsLocalHom φ.toRingHom := ⟨IsLocalHom.map_nonunit (f := φ)⟩
  refine ext_of_isHausdorff (IsLocalRing.maximalIdeal S) (fun r ↦ ?_) (fun g hg ↦ ?_) hG
  · obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R r)
    refine ⟨c, hG_span.symm ▸ (IsLocalRing.residue_eq_zero_iff _).1 ?_⟩
    rw [map_sub, ← hc, IsScalarTower.algebraMap_apply k R (IsLocalRing.ResidueField R),
      IsLocalRing.ResidueField.algebraMap_eq, sub_self]
  · exact map_nonunit φ.toRingHom g (hG_span ▸ Ideal.subset_span hg)

end AdicUniqueness

end AlgHom
