/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Prime-order characters trivial on a finite-index subgroup

If a prime `p` divides the finite index of a subgroup `D` of a commutative group `G`, then the
finite abelian quotient `Q = G ⧸ D` has an element of order `p` by Cauchy's theorem. Consequently
the `p`-th power endomorphism of `Q` is not injective and hence not surjective, so `Q ⧸ Q ^ p` is
a nontrivial `ZMod p`-vector space. Pulling back a nonzero coordinate functional on `Q ⧸ Q ^ p`
yields a nontrivial homomorphism `G →* Multiplicative (ZMod p)` vanishing on `D`, and composing
with the embedding into any group `M` having an element of order `p` yields a nontrivial
`p`-torsion homomorphism `G →* M` vanishing on `D`.

## Main results

* `Subgroup.exists_monoidHom_zmod_of_prime_dvd_index`: nontrivial `χ : G →* Multiplicative (ZMod p)`
  vanishing on `D`.
* `Subgroup.exists_monoidHom_of_prime_dvd_index`: nontrivial `p`-torsion `χ : G →* M` vanishing on
  `D` whenever `M` has an element of order `p`.

## Provenance

Adapted from grh-lean
(https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/GaloisRep/LocalGlobal/IwahoriCompatibility.lean`
(`New.exists_char_trivial_of_prime_dvd_index`).
-/

public section

namespace Subgroup

/-- If a prime `p` divides the finite index of a subgroup `D` of a commutative group `G`, then
there exist a homomorphism `χ : G →* Multiplicative (ZMod p)` and an element `x₀ : G` such that
`χ x₀ ≠ 1` and `χ y = 1` for all `y ∈ D`. -/
theorem exists_monoidHom_zmod_of_prime_dvd_index {G : Type*} [CommGroup G] (D : Subgroup G)
    [D.FiniteIndex] {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ D.index) :
    ∃ (χ : G →* Multiplicative (ZMod p)) (x₀ : G), χ x₀ ≠ 1 ∧ ∀ y ∈ D, χ y = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (G ⧸ D) := finite_quotient_of_finiteIndex
  have hcard : p ∣ Nat.card (G ⧸ D) := by rwa [← index_eq_card]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hcard
  set φ : (G ⧸ D) →* (G ⧸ D) := powMonoidHom p
  have hnot_inj : ¬Function.Injective φ := fun hinj ↦ by
    have ha1 : a = 1 := hinj (by simp [φ, powMonoidHom_apply, ← ha, pow_orderOf_eq_one])
    rw [ha1, orderOf_one] at ha
    exact hp.ne_one ha.symm
  have hnot_surj : ¬Function.Surjective φ := fun hsurj ↦
    hnot_inj (Finite.injective_iff_surjective.mpr hsurj)
  obtain ⟨q₀, hq₀⟩ := not_forall.mp hnot_surj
  set Q := (G ⧸ D) ⧸ φ.range
  have hkill : ∀ v : Additive Q, p • v = 0 := by
    intro v
    induction v using Additive.rec with | ofMul u =>
    induction u using QuotientGroup.induction_on with | H c =>
    have hmem : c ^ p ∈ φ.range := ⟨c, rfl⟩
    rw [← ofMul_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff (c ^ p)).mpr hmem,
      ofMul_one]
  let : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hkill
  have hv₀ : Additive.ofMul (QuotientGroup.mk q₀ : Q) ≠ 0 := fun h0 ↦
    hq₀ ((QuotientGroup.eq_one_iff q₀).mp (Additive.ofMul.injective h0))
  let b := Module.Basis.ofVectorSpace (ZMod p) (Additive Q)
  obtain ⟨i, hi⟩ :
      ∃ i, (b.coord i).toAddMonoidHom (Additive.ofMul (QuotientGroup.mk q₀ : Q)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₀ (b.ext_elem fun i ↦ by simpa [Module.Basis.coord_apply] using h i)
  let χ : G →* Multiplicative (ZMod p) :=
    (b.coord i).toAddMonoidHom.toMultiplicativeRight.comp
      ((QuotientGroup.mk' φ.range).comp (QuotientGroup.mk' D))
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective D q₀
  refine ⟨χ, x₀, ?_, fun y hy ↦ ?_⟩
  · simpa [χ, QuotientGroup.mk'_apply] using hi
  · dsimp only [χ]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy, QuotientGroup.mk_one, map_one]

/-- If a prime `p` divides the finite index of a subgroup `D` of a commutative group `G` and
`z : M` is an element of order `p` in a group `M`, then there exist a homomorphism `χ : G →* M`
and an element `x₀ : G` such that `χ x₀ ≠ 1`, `χ y ^ p = 1` for all `y : G`, and `χ y = 1` for
all `y ∈ D`. -/
theorem exists_monoidHom_of_prime_dvd_index {G M : Type*} [CommGroup G] [Group M]
    (D : Subgroup G) [D.FiniteIndex] {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ D.index) {z : M}
    (hz : orderOf z = p) :
    ∃ (χ : G →* M) (x₀ : G), χ x₀ ≠ 1 ∧ (∀ y : G, χ y ^ p = 1) ∧ ∀ y ∈ D, χ y = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, x₀, hx₀, hD⟩ := exists_monoidHom_zmod_of_prime_dvd_index D hp hp_dvd
  have hpow_val (a : Multiplicative (ZMod p)) :
      Multiplicative.ofAdd (1 : ZMod p) ^ (Multiplicative.toAdd a).val = a := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  have hgen (a : Multiplicative (ZMod p)) :
      a ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod p)) :=
    Subgroup.mem_zpowers_iff.mpr ⟨(Multiplicative.toAdd a).val, by rw [zpow_natCast, hpow_val]⟩
  have hord : orderOf z ∣ orderOf (Multiplicative.ofAdd (1 : ZMod p)) := by
    rw [hz, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  let ι : Multiplicative (ZMod p) →* M := monoidHomOfForallMemZpowers hgen hord
  have hι_inj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : z ^ (Multiplicative.toAdd a).val = 1 := by
      rw [← monoidHomOfForallMemZpowers_apply_gen hgen hord, ← map_pow, hpow_val]; exact ha
    have hdvd : p ∣ (Multiplicative.toAdd a).val := by
      simpa [hz] using orderOf_dvd_of_pow_eq_one ha'
    have hval0 : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    exact Multiplicative.toAdd.injective (by
      rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd a), hval0, Nat.cast_zero, toAdd_one])
  refine ⟨ι.comp φ, x₀, fun h ↦ hx₀ (hι_inj (by simpa using h)), fun y ↦ ?_, fun y hy ↦ by
    simp [hD y hy]⟩
  rw [MonoidHom.comp_apply, ← map_pow]
  have hp1 : φ y ^ p = 1 := by
    rw [← ofAdd_toAdd (φ y), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  rw [hp1, map_one]

end Subgroup
