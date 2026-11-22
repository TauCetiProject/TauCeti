/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Algebra homomorphisms of local algebras

Over any commutative semiring `k`, every `k`-algebra augmentation `R →ₐ[k] k` of a local
`k`-algebra `R` (not assumed commutative) reflects units (`AlgHom.isLocalHom_to_ring`), so whenever
a `k`-algebra `S` admits a `k`-algebra augmentation `S →ₐ[k] k`, every `k`-algebra homomorphism
`R →ₐ[k] S` out of `R` automatically reflects units (`AlgHom.isLocalHom_of_augmentation`). When
`k` is a field, `R` admits at most one `k`-algebra homomorphism `R →ₐ[k] k`
(`AlgHom.subsingleton_of_isLocalRing`), and every `k`-algebra homomorphism `R →ₐ[k] S` commutes with
any augmentations on `R` and `S` (`AlgHom.comp_eq_of_isLocalRing`).

In the commutative case over a commutative ring `k`, `TauCeti.residue_algebraMap` identifies the
residue of a scalar `algebraMap k R c` with its image in `IsLocalRing.ResidueField R`, and
whenever `R` admits a `k`-algebra augmentation `R →ₐ[k] k`, `algebraMap k (ResidueField R)` is
surjective (`AlgHom.surjective_algebraMap_residueField`).

## Main results

* `AlgHom.isLocalHom_to_ring`: any `k`-algebra augmentation `R →ₐ[k] k` of a local `k`-algebra over
  a commutative semiring `k` reflects units.
* `AlgHom.isLocalHom_of_augmentation`: any `φ : R →ₐ[k] S` from a local `k`-algebra into a
  `k`-algebra admitting `S →ₐ[k] k` reflects units.
* `AlgHom.subsingleton_of_isLocalRing`: `R →ₐ[k] k` is a subsingleton for a local `k`-algebra `R`
  over a field `k`.
* `TauCeti.residue_algebraMap`: the residue of `algebraMap k R c` equals
  `algebraMap k (IsLocalRing.ResidueField R) c`.
* `AlgHom.surjective_algebraMap_residueField`: if a commutative local `k`-algebra `R` over a
  commutative ring `k` admits `R →ₐ[k] k`, then `algebraMap k (ResidueField R)` is surjective.

## References

* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
-/

public section

namespace TauCeti

/-- The residue of a scalar `algebraMap k R c` in a commutative local `k`-algebra `R` equals the
image of `c` in `IsLocalRing.ResidueField R`. -/
theorem residue_algebraMap {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] (c : k) :
    IsLocalRing.residue R (algebraMap k R c) =
      algebraMap k (IsLocalRing.ResidueField R) c := by
  rw [IsScalarTower.algebraMap_apply k R (IsLocalRing.ResidueField R),
    IsLocalRing.ResidueField.algebraMap_eq]

end TauCeti

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
theorem isLocalHom_of_augmentation {k R S : Type*} [CommSemiring k] [Ring R] [IsLocalRing R]
    [Semiring S] [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (εS : S →ₐ[k] k) :
    IsLocalHom φ := by
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
  rw [← TauCeti.residue_algebraMap, ← sub_eq_zero, ← map_sub]
  by_contra hne
  have hu := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne).map ε
  simp [ε.commutes] at hu

end Augmentation

end AlgHom
