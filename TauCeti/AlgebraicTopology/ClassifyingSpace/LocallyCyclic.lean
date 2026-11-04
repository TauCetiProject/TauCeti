/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torus
public import TauCeti.RepresentationTheory.Homological.GroupHomology.DirectedUnion
import Mathlib.Algebra.CharP.Algebra

/-!
# Classifying spaces of torsion-free locally cyclic groups

A group `G` is *locally cyclic* when any two of its elements lie in a common cyclic subgroup, so
that `G` is the directed union of its cyclic subgroups. The torsion-free locally cyclic groups are
the subgroups of `ℚ`, such as `ℤ[1/2]`.

The homology of a torsion-free locally cyclic group with trivial coefficients in any commutative
ring vanishes in every degree `n ≥ 2`
(`TauCeti.isZero_groupHomology_of_forall_exists_mem_zpowers`). A nontrivial cyclic subgroup is
infinite cyclic, so its homology is that of the circle and vanishes in degrees `n ≥ 2`
(`TauCeti.isZero_groupHomology_of_isCyclic`), and group homology has compact supports along the
directed union of the cyclic subgroups (`groupHomology.isZero_of_directed`).

In degree one, `H₁(G; k) = Gᵃᵇ ⊗ k`. When every element of `G` is a square and `2 = 0` in `k`,
every element of `Gᵃᵇ` is twice another, so `H₁(G; k) = 0`
(`TauCeti.subsingleton_groupHomology_one_of_forall_exists_sq`).

Through the identification of the homology of Milnor's classifying space with group homology, the
reduced homology of `BG = K(G, 1)` with coefficients in a ring of characteristic two vanishes when
`G` is torsion-free, locally cyclic and two-divisible
(`TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_exists_sq`). For
`ℤ[1/2] = ⋃ᵣ 2⁻ʳℤ` this is the vanishing of the reduced homology of `K(ℤ[1/2], 1)` with
coefficients in `𝔽₂`
(`TauCeti.subsingleton_classifyingSpace_localizationAway_two_singularHomology`): the homology of
`K(ℤ[1/2], 1)` is the colimit of the homology of circles along maps of degree two. This is the
case `A = ℤ[1/2]` of the vanishing of the mod-two homology of `K(A, 1)` for a uniquely
two-divisible abelian group `A`, the input to the proof that the homotopy groups of a simply
connected space with vanishing reduced mod-two homology are uniquely two-divisible.

## Main results

* `TauCeti.isZero_groupHomology_of_isCyclic`: the homology of a torsion-free cyclic group vanishes
  in degrees `n ≥ 2`.
* `TauCeti.isZero_groupHomology_of_forall_exists_mem_zpowers`: the homology of a torsion-free
  locally cyclic group vanishes in degrees `n ≥ 2`.
* `TauCeti.subsingleton_groupHomology_one_of_forall_exists_sq`: `H₁(G; k) = 0` when every element
  of `G` is a square and `2 = 0` in `k`.
* `TauCeti.subsingleton_classifyingSpace_singularHomology_of_forall_exists_sq`:
  the reduced homology of `BG` with coefficients in `k` vanishes for a torsion-free, locally
  cyclic, two-divisible group `G` and `2 = 0` in `k`.
* `TauCeti.subsingleton_classifyingSpace_localizationAway_two_singularHomology`:
  the reduced homology of `K(ℤ[1/2], 1)` with coefficients in `k` vanishes when `2 = 0` in `k`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, on `K(G, 1)`
  spaces, and Section 3.F, on homology of direct limits.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
-/

public section

noncomputable section

open CategoryTheory Limits TensorProduct

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] {G : Type u} [Group G]

/-- **The homology of a torsion-free cyclic group vanishes above degree one**, with trivial
coefficients in any commutative ring: such a group is trivial or infinite cyclic, and an infinite
cyclic group has the homology of the circle. -/
theorem isZero_groupHomology_of_isCyclic [IsCyclic G] [IsMulTorsionFree G] {n : ℕ}
    (hn : 2 ≤ n) : IsZero (groupHomology (Rep.trivial k G k) n) := by
  have key : ∀ {ι : Type u} [Finite ι] (e : G ≃* (ι → Multiplicative ℤ)), Nat.card ι < n →
      IsZero (groupHomology (Rep.trivial k G k) n) := fun e hι ↦
    (isZero_groupHomology_pi_multiplicative_int k hι).of_iso
      (groupHomology.mapIso e (LinearEquiv.refl k k) (fun _ ↦ rfl) n)
  rcases finite_or_infinite G with hG | hG
  · -- a finite torsion-free group is trivial, the group `ℤ⁰`
    have : Unique G := ⟨⟨1⟩, fun g ↦ (isOfFinOrder_iff_eq_one g).1 (isOfFinOrder_of_finite g)⟩
    exact key (ι := PEmpty.{u + 1}) MulEquiv.ofUnique (by simp; omega)
  · exact key (ι := PUnit.{u + 1})
      (intCyclicMulEquiv.symm.trans (MulEquiv.funUnique PUnit _).symm) (by simp; omega)

/-- **The homology of a torsion-free locally cyclic group vanishes above degree one**, with trivial
coefficients in any commutative ring. Here `G` is locally cyclic: any two elements lie in a common
cyclic subgroup. Such a group is the directed union of its cyclic subgroups, whose homology
vanishes above degree one. -/
theorem isZero_groupHomology_of_forall_exists_mem_zpowers [IsMulTorsionFree G]
    (h : ∀ x y : G, ∃ g, x ∈ Subgroup.zpowers g ∧ y ∈ Subgroup.zpowers g) {n : ℕ}
    (hn : 2 ≤ n) : IsZero (groupHomology (Rep.trivial k G k) n) := by
  refine groupHomology.isZero_of_directed (H := fun g : G ↦ Subgroup.zpowers g)
    (fun x y ↦ ?_) (fun g ↦ ⟨g, Subgroup.mem_zpowers g⟩) fun g ↦ ?_
  · obtain ⟨g, hx, hy⟩ := h x y
    exact ⟨g, Subgroup.zpowers_le.2 hx, Subgroup.zpowers_le.2 hy⟩
  · -- the restriction of the trivial representation is the trivial representation
    exact isZero_groupHomology_of_isCyclic k hn

/-- **The first homology of a two-divisible group vanishes in characteristic two.** If every element
of `G` is a square and `2 = 0` in `k`, then `H₁(G; k) = Gᵃᵇ ⊗ k` vanishes: every element of the
abelianization is twice another, and twice every element of `k` is zero. -/
theorem subsingleton_groupHomology_one_of_forall_exists_sq (hk : (2 : k) = 0)
    (h : ∀ g : G, ∃ x, x ^ 2 = g) : Subsingleton (groupHomology (Rep.trivial k G k) 1) := by
  suffices Subsingleton (Additive (Abelianization G) ⊗[ℤ] k) by
    exact (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial k G k)).injective.subsingleton
  refine ⟨fun s t ↦ ?_⟩
  suffices ∀ s : Additive (Abelianization G) ⊗[ℤ] k, s = 0 by rw [this s, this t]
  intro s
  induction s using TensorProduct.inductionOn with
  | add s t hs ht => rw [hs, ht, add_zero]
  | tmul a b =>
    -- `a` is the class of a square `x ^ 2`, so `a ⊗ b = x ⊗ 2b = 0`
    -- `Abelianization.of` is the quotient map, so it is surjective
    obtain ⟨g, hg⟩ : ∃ g, Abelianization.of g = Additive.toMul a :=
      QuotientGroup.mk_surjective _
    obtain ⟨x, rfl⟩ := h g
    have ha : a = Additive.ofMul (Abelianization.of x) + Additive.ofMul (Abelianization.of x) := by
      rw [← ofMul_mul, ← map_mul, ← pow_two, hg, ofMul_toMul]
    rw [ha, TensorProduct.add_tmul, ← TensorProduct.tmul_add, ← two_mul, hk, zero_mul,
      TensorProduct.tmul_zero]

/-- **The reduced homology of `K(G, 1)` vanishes in characteristic two for a torsion-free,
locally cyclic, two-divisible group `G`.** If `G` is torsion-free, any two elements of `G` lie in a
common cyclic subgroup, every element of `G` is a square, and `2 = 0` in `k`, then
`Hₙ₊₁(BG; k) = 0` for every `n`. -/
theorem subsingleton_classifyingSpace_singularHomology_of_forall_exists_sq [IsMulTorsionFree G]
    (hk : (2 : k) = 0)
    (hcyc : ∀ x y : G, ∃ g, x ∈ Subgroup.zpowers g ∧ y ∈ Subgroup.zpowers g)
    (hsq : ∀ g : G, ∃ x, x ^ 2 = g) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)) := by
  have : Subsingleton (groupHomology (Rep.trivial k G k) (n + 1)) := by
    rcases n with _ | n
    · exact subsingleton_groupHomology_one_of_forall_exists_sq k hk hsq
    · exact ModuleCat.subsingleton_of_isZero
        (isZero_groupHomology_of_forall_exists_mem_zpowers k hcyc (by omega))
  exact (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv.toEquiv
    |>.subsingleton

/-- **The reduced homology of `K(ℤ[1/2], 1)` vanishes in characteristic two**: for
`ℤ[1/2] = Localization.Away 2` and a commutative ring `k` with `2 = 0`, such as `𝔽₂`,
`Hₙ₊₁(K(ℤ[1/2], 1); k) = 0` for every `n`, where `K(ℤ[1/2], 1) = B(Multiplicative ℤ[1/2])`. -/
theorem subsingleton_classifyingSpace_localizationAway_two_singularHomology (k : Type)
    [CommRing k] (hk : (2 : k) = 0) (n : ℕ) :
    Subsingleton (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative (Localization.Away (2 : ℤ)))))).homology
        (n + 1)) := by
  -- `ℤ[1/2]` is a domain of characteristic zero, hence torsion-free
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors (two_ne_zero (α := ℤ))
  have := IsLocalization.isDomain_localization (M := Submonoid.powers (2 : ℤ)) hle
  have := charZero_of_injective_algebraMap
    (IsLocalization.injective (Localization.Away (2 : ℤ)) hle)
  have h2 : (2 : Localization.Away (2 : ℤ)) * IsLocalization.Away.invSelf (2 : ℤ) = 1 := by
    simpa using IsLocalization.Away.mul_invSelf (S := Localization.Away (2 : ℤ)) (2 : ℤ)
  refine subsingleton_classifyingSpace_singularHomology_of_forall_exists_sq k hk
    (fun x y ↦ ?_) (fun g ↦ ?_) n
  · -- `x = a / 2ᵖ` and `y = b / 2^q` are integer multiples of `u = 1 / 2^(p + q)`
    obtain ⟨p, a, ha⟩ := IsLocalization.Away.surj (2 : ℤ) x.toAdd
    obtain ⟨q, b, hb⟩ := IsLocalization.Away.surj (2 : ℤ) y.toAdd
    simp only [map_ofNat, eq_intCast] at ha hb
    set u : Localization.Away (2 : ℤ) := IsLocalization.Away.invSelf (2 : ℤ) ^ (p + q)
    have hu : (2 : Localization.Away (2 : ℤ)) ^ (p + q) * u = 1 := by rw [← mul_pow, h2, one_pow]
    refine ⟨Multiplicative.ofAdd u, Subgroup.mem_zpowers_iff.2 ⟨a * 2 ^ q, ?_⟩,
      Subgroup.mem_zpowers_iff.2 ⟨b * 2 ^ p, ?_⟩⟩
    · apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul]
      push_cast
      linear_combination (-(2 ^ q * u)) * ha + x.toAdd * hu
    · apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul]
      push_cast
      linear_combination (-(2 ^ p * u)) * hb + y.toAdd * hu
  · -- `g = (g / 2) ^ 2`
    refine ⟨Multiplicative.ofAdd (IsLocalization.Away.invSelf (2 : ℤ) * g.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, h2, one_mul]

end TauCeti
