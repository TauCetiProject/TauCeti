/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
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

We also record an elementary adic uniqueness principle for `k`-algebra homomorphisms into an
adically separated commutative ring (`IsHausdorff J S`): if `G` generates a left ideal modulo which
every element of `R` is represented by a scalar in `k`, then two `k`-algebra homomorphisms
`φ, ψ : R →ₐ[k] S` that agree on `G` and map `G` into `J` are congruent modulo every power `J ^ n`
(`AlgHom.sub_mem_pow_of_eqOn`), and hence equal when `IsHausdorff J S` holds
(`AlgHom.ext_of_isHausdorff`), without assuming `R` is commutative. Specializing to commutative
local `k`-algebras `R` and `S` where `algebraMap k (ResidueField R)` is surjective and `S` is
separated (`IsHausdorff`) with respect to its maximal ideal yields uniqueness of `φ, ψ : R →ₐ[k] S`
from agreement on any generating set of `maximalIdeal R`, provided one of the homomorphisms (`φ`) is
local (`AlgHom.ext_of_span_eq_maximalIdeal`), even when `R` is not finitely generated as a
`k`-algebra (as for rings of analytic germs or formal power series).

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
* `AlgHom.sub_mem_pow_of_eqOn`, `AlgHom.ext_of_isHausdorff`: adic congruences to every order and
  (under `IsHausdorff J S`) uniqueness of `k`-algebra homomorphisms into a commutative ring `S`
  from agreement on a set `G` mapped into `J` and generating an ideal modulo which every element is
  represented by a scalar.
* `AlgHom.ext_of_span_eq_maximalIdeal`: specialization to commutative local `k`-algebras, giving
  uniqueness from agreement on generators of `maximalIdeal R` when `algebraMap k (ResidueField R)`
  is surjective, `S` is maximal-ideal separated (`IsHausdorff`), and `φ` is a local homomorphism.

## References

* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
* N. Bourbaki, *Commutative Algebra*, Chapter III, §2 (for `I`-adic congruences and uniqueness of
  homomorphisms into adically separated targets) and §3 (for the local-ring specialization and
  maximal-ideal generators).
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
      -- `k` is only a `CommSemiring`, so cancel `+ algebraMap k R (ε r)` in the `Ring` `R`.
      have h0 : algebraMap k R (ε (algebraMap k R (ε r) - r)) = 0 :=
        add_right_cancel (b := algebraMap k R (ε r)) <| by
          rw [zero_add, ← map_add, ← map_add, sub_add_cancel, ε.commutes,
            Algebra.algebraMap_self_apply]
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

section AdicUniqueness

/-- **Adic congruences from generators modulo which every element is a scalar.** Suppose `G`
generates an ideal modulo which every element of `R` is represented by a scalar in `k`, and
`φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into an ideal `J` of `S`. Then `φ r - ψ r ∈ J ^ n`
for every `n : ℕ` and `r : R`. -/
theorem sub_mem_pow_of_eqOn {k R S : Type*} [CommSemiring k] [Ring R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} {J : Ideal S}
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    ∀ (n : ℕ) (r : R), φ r - ψ r ∈ J ^ n
  | 0, _ => by simp
  | n + 1, r => by
    have hψJ : Ideal.span G ≤ J.comap ψ.toRingHom :=
      Ideal.span_le.2 fun g hg ↦ Ideal.mem_comap.2 (hG hg ▸ hGJ g hg)
    obtain ⟨c, hc⟩ := haug r
    have hrc : φ r - ψ r = φ (r - algebraMap k R c) - ψ (r - algebraMap k R c) := by simp
    rw [hrc]
    refine Submodule.span_induction (p := fun x _ ↦ φ x - ψ x ∈ J ^ (n + 1))
      (fun g hg ↦ by simp [hG hg]) (by simp)
      (fun x y _ _ hx hy ↦ by simpa only [map_add, sub_add_sub_comm] using add_mem hx hy)
      (fun a x hx ihx ↦ ?_) hc
    have hsplit : φ (a • x) - ψ (a • x) = φ a * (φ x - ψ x) + (φ a - ψ a) * ψ x := by
      simp only [smul_eq_mul, map_mul, mul_sub, sub_mul, sub_add_sub_cancel]
    rw [hsplit]
    exact add_mem (Ideal.mul_mem_left _ (φ a) ihx)
      (pow_succ J n ▸ Ideal.mul_mem_mul (sub_mem_pow_of_eqOn haug hGJ hG n a) (hψJ hx))

/-- **Uniqueness of `k`-algebra homomorphisms into an adically separated ring.** Suppose `G`
generates an ideal modulo which every element of `R` is represented by a scalar in `k`, and `S` is
`IsHausdorff J S` for an ideal `J` of `S`. If `φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into
`J`, then `φ = ψ`. -/
theorem ext_of_isHausdorff {k R S : Type*} [CommSemiring k] [Ring R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} (J : Ideal S) [IsHausdorff J S]
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    φ = ψ :=
  AlgHom.coe_fn_injective <| IsHausdorff.funext' J fun n r ↦
    Ideal.Quotient.eq.2 (sub_mem_pow_of_eqOn haug hGJ hG n r)

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
    rw [map_sub, TauCeti.residue_algebraMap, hc, sub_self]
  · exact map_nonunit φ.toRingHom g (hG_span ▸ Ideal.subset_span hg)

end AdicUniqueness

end AlgHom
