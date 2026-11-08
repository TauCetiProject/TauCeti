/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Bounded representatives for cyclic extensions

If `x` normalizes a subgroup `H` and `x^m ∈ H` for `m > 0`, every element of
`H ⊔ zpowers x` is `h * x^k` with `h ∈ H` and `0 ≤ k < m`.
Thus adjoining `x` to a finite subgroup multiplies its order by at most `m`.
Neither the ambient group nor `x` is assumed finite, and the representatives need not
be distinct. This is the individual extension step in power-conjugate order bounds.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Membership after adjoining a normalizing element is characterized by bounded expressions
`h * x^k`, provided its positive `m`-th power belongs to `H`. -/
theorem mem_sup_zpowers_iff_exists_mul_pow (H : Subgroup G) {x : G} {m : ℕ}
    (hm : 0 < m) (hx : x ∈ normalizer H) (hpow : x ^ m ∈ H) {g : G} :
    g ∈ H ⊔ zpowers x ↔ ∃ h : H, ∃ k : Fin m, (h : G) * x ^ (k : ℕ) = g := by
  constructor
  · intro hg
    obtain ⟨h, hh, _, ⟨z, rfl⟩, rfl⟩ :=
      (mem_sup_of_right_le_normalizer_left (zpowers_le.mpr hx)).mp hg
    have hr0 : 0 ≤ z % (m : ℤ) := Int.emod_nonneg _ (by omega)
    have hrlt : z % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
    let k : Fin m := ⟨(z % (m : ℤ)).toNat, by omega⟩
    refine ⟨⟨h * (x ^ m) ^ (z / (m : ℤ)), H.mul_mem hh (H.zpow_mem hpow _)⟩, k, ?_⟩
    have hk : (k : ℤ) = z % (m : ℤ) := by simp [k, Int.toNat_of_nonneg hr0]
    simp only [mul_assoc]
    congr 1
    rw [← zpow_natCast x m, ← zpow_mul, ← zpow_natCast x (k : ℕ), ← zpow_add]
    congr 1
    rw [hk]
    exact Int.mul_ediv_add_emod z (m : ℤ)
  · rintro ⟨h, k, rfl⟩
    exact mul_mem (mem_sup_left h.property) (mem_sup_right (pow_mem (mem_zpowers x) _))

-- One finite surjection supplies both public conclusions below.
private theorem cyclic_extension_bound (H : Subgroup G) [Finite H] {x : G} {m : ℕ}
    (hm : 0 < m) (hx : x ∈ normalizer H) (hpow : x ^ m ∈ H) :
    Finite (H ⊔ zpowers x : Subgroup G) ∧
      Nat.card (H ⊔ zpowers x : Subgroup G) ≤ Nat.card H * m := by
  let f : H × Fin m → (H ⊔ zpowers x : Subgroup G) := fun p ↦
    ⟨(p.1 : G) * x ^ (p.2 : ℕ),
      (H.mem_sup_zpowers_iff_exists_mul_pow hm hx hpow).mpr ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨h, k, hk⟩ := (H.mem_sup_zpowers_iff_exists_mul_pow hm hx hpow).mp g.property
    exact ⟨(h, k), Subtype.ext hk⟩
  have := Finite.of_surjective f hf
  exact ⟨this, by simpa only [Nat.card_prod, Nat.card_fin] using
    Nat.card_le_card_of_surjective f hf⟩

/-- Adjoining a normalizing element with a positive power in a finite subgroup is finite. -/
theorem finite_sup_zpowers (H : Subgroup G) [Finite H] {x : G} {m : ℕ}
    (hm : 0 < m) (hx : x ∈ normalizer H) (hpow : x ^ m ∈ H) :
    Finite (H ⊔ zpowers x : Subgroup G) :=
  (cyclic_extension_bound H hm hx hpow).1

/-- Adjoining a normalizing element with a certified `m`-th power in a finite subgroup `H`
gives a subgroup of order at most `|H| * m`. The power bound need not be exact. -/
theorem card_sup_zpowers_le (H : Subgroup G) [Finite H] {x : G} {m : ℕ}
    (hm : 0 < m) (hx : x ∈ normalizer H) (hpow : x ^ m ∈ H) :
    Nat.card (H ⊔ zpowers x : Subgroup G) ≤ Nat.card H * m :=
  (cyclic_extension_bound H hm hx hpow).2

end Subgroup
