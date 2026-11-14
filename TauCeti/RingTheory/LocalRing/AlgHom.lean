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

Over a field `k`, a local `k`-algebra `R` (not assumed commutative) admits at most one `k`-algebra
homomorphism `R →ₐ[k] k` (`AlgHom.subsingleton_of_isLocalRing`), and every such augmentation is
surjective and reflects units (`AlgHom.isLocalHom_self`). Consequently, whenever a `k`-algebra `S`
admits a `k`-algebra augmentation `S →ₐ[k] k`, every `k`-algebra homomorphism `R →ₐ[k] S` out of a
local `k`-algebra automatically reflects units (`AlgHom.isLocalHom_of_algHom`) and commutes with
any augmentation on `R` (`AlgHom.comp_eq_of_isLocalRing`).

In the commutative case, over an arbitrary commutative base ring `k`, let `G` be a subset of `R`
such that every element of `R` differs from a scalar in `k` by an element of `Ideal.span G`. If two
`k`-algebra homomorphisms `φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into an ideal `J` of `S`,
then `φ r - ψ r ∈ J ^ n` for every `n : ℕ` (`AlgHom.sub_mem_pow_of_eqOn`). When `S` is separated
for the `J`-adic topology (`IsHausdorff J S`), it follows that `φ = ψ`
(`AlgHom.ext_of_isHausdorff`). For local `k`-algebras `R` and `S` with `S` separated for its
maximal ideal and `algebraMap k (ResidueField R)` surjective, a `k`-algebra homomorphism
`ψ : R →ₐ[k] S` agreeing on a generating set of `maximalIdeal R` with a local `k`-algebra
homomorphism `φ : R →ₐ[k] S` equals `φ` (`AlgHom.ext_of_span_eq_maximalIdeal`), even when `R` is
not finitely generated as a `k`-algebra (as for rings of analytic germs or formal power series).

## Main results

* `AlgHom.isLocalHom_self`: any `k`-algebra augmentation `R →ₐ[k] k` of a local `k`-algebra over a
  field `k` reflects units.
* `AlgHom.subsingleton_of_isLocalRing`: `R →ₐ[k] k` is a subsingleton for a local `k`-algebra `R`
  over a field `k`.
* `AlgHom.isLocalHom_of_algHom`: any `φ : R →ₐ[k] S` from a local `k`-algebra over a field `k` into
  a `k`-algebra admitting `S →ₐ[k] k` reflects units.
* `AlgHom.sub_mem_pow_of_eqOn`: adic congruences to every order between two `k`-algebra
  homomorphisms agreeing on generators of an augmentation ideal.
* `AlgHom.ext_of_isHausdorff`, `AlgHom.ext_of_span_eq_maximalIdeal`: uniqueness of `k`-algebra
  homomorphisms into adically separated targets from agreement on generators.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
-/

public section

namespace AlgHom

section Augmentation

/-- Every `k`-algebra homomorphism `R →ₐ[k] k` to the base semiring is surjective. -/
theorem surjective_self {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R]
    (ε : R →ₐ[k] k) : Function.Surjective ε :=
  fun c ↦ ⟨algebraMap k R c, ε.commutes c⟩

/-- Over a field `k`, every `k`-algebra augmentation `R →ₐ[k] k` of a local ring `R` (not assumed
commutative) reflects units. -/
instance isLocalHom_self {k R : Type*} [Field k] [Ring R] [IsLocalRing R] [Algebra k R]
    (ε : R →ₐ[k] k) : IsLocalHom ε where
  map_nonunit r hr := by
    by_contra hnr
    have hker : ¬ IsUnit (algebraMap k R (ε r) - r) := fun hu ↦ by
      have hu0 : IsUnit (0 : k) := by simpa [ε.commutes] using hu.map ε
      exact not_isUnit_zero hu0
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
theorem apply_comp_eq_of_isLocalRing {k R S : Type*} [Field k] [Ring R] [IsLocalRing R]
    [Semiring S] [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (εR : R →ₐ[k] k) (εS : S →ₐ[k] k)
    (r : R) : εS (φ r) = εR r :=
  AlgHom.congr_fun (φ.comp_eq_of_isLocalRing εR εS) r

/-- Over a field `k`, any `k`-algebra homomorphism `R →ₐ[k] S` out of a local `k`-algebra `R` into
a `k`-algebra `S` admitting a `k`-algebra augmentation `S →ₐ[k] k` reflects units. -/
theorem isLocalHom_of_algHom {k R S : Type*} [Field k] [Ring R] [IsLocalRing R] [Semiring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (εS : S →ₐ[k] k) : IsLocalHom φ := by
  have : IsLocalHom (εS.toRingHom.comp φ.toRingHom) := ⟨IsLocalHom.map_nonunit (f := εS.comp φ)⟩
  exact ⟨(isLocalHom_of_comp φ.toRingHom εS.toRingHom).map_nonunit⟩

/-- Over a field `k`, the kernel of any `k`-algebra augmentation `R →ₐ[k] k` of a commutative local
`k`-algebra is the maximal ideal of `R`. -/
theorem ker_eq_maximalIdeal {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    (ε : R →ₐ[k] k) : RingHom.ker ε = IsLocalRing.maximalIdeal R :=
  IsLocalRing.ker_eq_maximalIdeal ε.toRingHom ε.surjective_self

/-- If a commutative local `k`-algebra `R` over a field `k` admits a `k`-algebra augmentation
`R →ₐ[k] k`, then `k` surjects onto `ResidueField R`. -/
theorem surjective_algebraMap_residueField {k R : Type*} [Field k] [CommRing R] [IsLocalRing R]
    [Algebra k R] (ε : R →ₐ[k] k) :
    Function.Surjective (algebraMap k (IsLocalRing.ResidueField R)) := by
  intro a
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
  refine ⟨ε r, ?_⟩
  rw [IsScalarTower.algebraMap_apply k R (IsLocalRing.ResidueField R),
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ← ε.ker_eq_maximalIdeal]
  simp [RingHom.mem_ker]

end Augmentation

section AdicUniqueness

/-- **Adic congruences from generators of an augmentation ideal.** Suppose every element of `R` is
congruent to a scalar in `k` modulo `Ideal.span G`, and `φ, ψ : R →ₐ[k] S` agree on `G` and map `G`
into an ideal `J` of `S`. Then `φ r - ψ r ∈ J ^ n` for every `n : ℕ` and `r : R`. -/
theorem sub_mem_pow_of_eqOn {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
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
      simp only [smul_eq_mul, map_mul]
      ring
    rw [hsplit]
    exact add_mem (Ideal.mul_mem_left _ (φ a) ihx)
      (pow_succ J n ▸ Ideal.mul_mem_mul (sub_mem_pow_of_eqOn haug hGJ hG n a) (hψJ hx))

/-- **Uniqueness of `k`-algebra homomorphisms into an adically separated ring.** Suppose every
element of `R` is congruent to a scalar in `k` modulo `Ideal.span G`, and `S` is `IsHausdorff J S`
for an ideal `J` of `S`. If `φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into `J`, then `φ = ψ`. -/
theorem ext_of_isHausdorff {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} (J : Ideal S) [IsHausdorff J S]
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    φ = ψ :=
  ext fun r ↦ sub_eq_zero.1 <| IsHausdorff.haus ‹_› (φ r - ψ r) fun n ↦ by
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using sub_mem_pow_of_eqOn haug hGJ hG n r

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
