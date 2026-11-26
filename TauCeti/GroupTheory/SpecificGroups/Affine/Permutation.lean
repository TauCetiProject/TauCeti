/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.GroupTheory.SpecificGroups.Affine.Primitive
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The affine group as a permutation group

The affine group `TauCeti.AffineGroup F` of a ring `F` acts faithfully on `F` by
`x ↦ b + a x`, so it is isomorphic to its image `(MulAction.toPermHom (AffineGroup F) F).range`
in the permutations of `F`. This file describes that image and its position inside
`Equiv.Perm F`.

* A permutation of `F` lies in the image exactly when it has the form `x ↦ a x + b`; for a
  permutation of this form `a` is automatically a unit.
* For a finite division ring the image is all of `Equiv.Perm F` exactly when `F` has at most
  three elements; in particular the affine group of `𝔽₃` is the full symmetric group.
* When `F` has no zero divisors and a unit other than `1`, the centralizer of the image in
  `Equiv.Perm F` is trivial. Hence the affine group has trivial centre, and an automorphism of
  the form `x ↦ h x h⁻¹` fixes no surjection onto the affine group unless `h = 1`.
* For a prime `p`, the image of the affine group of `ZMod p` is its own normalizer in
  `Equiv.Perm (ZMod p)`. Consequently two surjections from a group onto the affine group of
  `ZMod p` are conjugate under all permutations of `ZMod p` exactly when they are conjugate
  under the affine group itself.

The last two facts say that a transitive permutation representation of a group with image
`AGL(1, p)` determines its surjection onto `AGL(1, p)` up to a unique inner automorphism; this is
how Lawrence and Venkatesh count covers of a curve with monodromy group `AGL(1, p)`.

## Main results

* `TauCeti.AffineGroup.mem_range_toPermHom_iff`: the affine permutations are the maps
  `x ↦ a x + b`.
* `TauCeti.AffineGroup.range_toPermHom_eq_top_iff`: the affine permutations exhaust
  `Equiv.Perm F` iff `|F| ≤ 3`.
* `TauCeti.AffineGroup.centralizer_range_toPermHom_eq_bot`,
  `TauCeti.AffineGroup.center_eq_bot`: the affine group is centre-free and has trivial
  centralizer among all permutations.
* `TauCeti.AffineGroup.normalizer_range_toPermHom_zmod`: `AGL(1, p)` is self-normalizing in
  `Sym(𝔽_p)`.
* `TauCeti.AffineGroup.exists_perm_conj_iff_exists_conj`: conjugacy of surjections onto
  `AGL(1, p)` under `Sym(𝔽_p)` and under `AGL(1, p)` agree.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*,
  Invent. Math. 221 (2020), §2.6 and §8.2.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, §3.3 and §7.7.
-/

public section

open Equiv MulAction

namespace TauCeti

namespace AffineGroup

section Ring

variable {F : Type*} [Ring F]

/-- **The affine permutations of a ring.** A permutation of `F` comes from the affine group
exactly when it has the form `x ↦ a x + b`. No condition on `a` is needed: bijectivity of such a
map forces `a` to be a unit. -/
theorem mem_range_toPermHom_iff {σ : Perm F} :
    σ ∈ (toPermHom (AffineGroup F) F).range ↔ ∃ a b : F, ∀ x, σ x = a * x + b := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.right, g.left.toAdd, fun x ↦ by simp [smul_def, add_comm]⟩
  · rintro ⟨a, b, hσ⟩
    -- Surjectivity of `σ` gives a right inverse `c` of `a`, and injectivity makes it two-sided.
    obtain ⟨c, hc⟩ := σ.surjective (1 + b)
    have hac : a * c = 1 := add_right_cancel ((hσ c).symm.trans hc)
    have hca : c * a = 1 := by
      have h : σ (c * a) = σ 1 := by rw [hσ, hσ, ← mul_assoc, hac, one_mul, mul_one]
      exact σ.injective h
    refine ⟨⟨Multiplicative.ofAdd b, ⟨a, c, hac, hca⟩⟩, Equiv.ext fun x ↦ ?_⟩
    simp [smul_def, hσ, add_comm]

end Ring

/-- If `n (n - 1) = n!` then `n ≤ 3`: for `n = m + 2` the factorial is `(m + 2) (m + 1) m!`, so
`m! = 1`, which forces `m ≤ 1`. -/
private theorem le_three_of_mul_sub_one_eq_factorial {n : ℕ} (h : n * (n - 1) = n.factorial) :
    n ≤ 3 := by
  by_contra! h4
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.factorial_succ, Nat.factorial_succ, ← mul_assoc, show m + 2 - 1 = m + 1 by omega] at h
  have hm : m.factorial = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega))
      (h.symm.trans (mul_one _).symm)
  have h2 : Nat.factorial 2 ≤ m.factorial := Nat.factorial_le (by omega)
  rw [hm, Nat.factorial_two] at h2
  omega

section DivisionRing

variable {F : Type*} [DivisionRing F] [Finite F]

/-- **When the affine group is the full symmetric group.** For a finite division ring `F` the
affine permutations, of which there are `|F| (|F| - 1)`, exhaust the `|F|!` permutations of `F`
exactly when `|F| ≤ 3`. -/
theorem range_toPermHom_eq_top_iff :
    (toPermHom (AffineGroup F) F).range = ⊤ ↔ Nat.card F ≤ 3 := by
  have hcard := natCard_range_toPermHom (F := F)
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  constructor
  · intro htop
    rw [htop, Subgroup.card_top, Nat.card_perm] at hcard
    exact le_three_of_mul_sub_one_eq_factorial hcard.symm
  · intro h3
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, Nat.card_perm]
    interval_cases Nat.card F <;> rfl

/-- The affine group of `𝔽₃` is the full symmetric group of `𝔽₃`. -/
theorem range_toPermHom_zmod_three_eq_top :
    (toPermHom (AffineGroup (ZMod 3)) (ZMod 3)).range = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (range_toPermHom_eq_top_iff (F := ZMod 3)).2 (by rw [Nat.card_zmod])

end DivisionRing

section NoZeroDivisors

variable {F : Type*} [Ring F] [NoZeroDivisors F] [Nontrivial Fˣ]

/-- **The affine group has trivial centralizer in the symmetric group.** If `F` has no zero
divisors and a unit other than `1`, the only permutation of `F` commuting with every affine map is
the identity: commuting with the translations makes it a translation, and commuting with a
dilation `x ↦ u x` with `u ≠ 1` makes that translation trivial. -/
theorem centralizer_range_toPermHom_eq_bot :
    Subgroup.centralizer ((toPermHom (AffineGroup F) F).range : Set (Perm F)) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc
  have hcomm (g : AffineGroup F) (x : F) : g • c x = c (g • x) := by
    simpa using congrArg (· x) (hc (toPermHom (AffineGroup F) F g) ⟨g, rfl⟩)
  -- Commuting with the translation by `t` gives `c t = t + c 0`.
  have htrans (t : F) : c t = t + c 0 := by
    simpa [smul_def] using (hcomm (SemidirectProduct.inl (Multiplicative.ofAdd t)) 0).symm
  -- Commuting with the dilation by `u ≠ 1` gives `u (c 0) = c 0`, so `c 0 = 0`.
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  have hdil : (u : F) * c 0 = c 0 := by simpa [smul_def] using hcomm (SemidirectProduct.inr u) 0
  have h0 : c 0 = 0 := by
    have h : ((u : F) - 1) * c 0 = 0 := by rw [sub_mul, one_mul, hdil, sub_self]
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 fun h ↦ hu (Units.ext h))
  rw [Subgroup.mem_bot]
  exact Equiv.ext fun t ↦ by rw [htrans, h0, add_zero, Perm.one_apply]

/-- **The affine group is centre-free** when `F` has no zero divisors and a unit other than `1`. -/
theorem center_eq_bot : Subgroup.center (AffineGroup F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  have hmem : toPermHom (AffineGroup F) F g ∈
      Subgroup.centralizer ((toPermHom (AffineGroup F) F).range : Set (Perm F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  rw [centralizer_range_toPermHom_eq_bot, Subgroup.mem_bot,
    ← map_one (toPermHom (AffineGroup F) F)] at hmem
  exact Subgroup.mem_bot.2 (toPerm_injective (β := F) hmem)

/-- **A surjection onto the affine group has trivial stabilizer under conjugation**: if
conjugation by `h` fixes a surjection `φ : Γ →* AffineGroup F`, then `h = 1`. -/
theorem eq_one_of_forall_mul_mul_inv_eq {Γ : Type*} [Group Γ] {φ : Γ →* AffineGroup F}
    (hφ : Function.Surjective φ) {h : AffineGroup F} (hh : ∀ γ, h * φ γ * h⁻¹ = φ γ) : h = 1 := by
  rw [← Subgroup.mem_bot, ← center_eq_bot, Subgroup.mem_center_iff]
  intro g
  obtain ⟨γ, rfl⟩ := hφ g
  exact (mul_inv_eq_iff_eq_mul.1 (hh γ)).symm

end NoZeroDivisors

section ZMod

variable {p : ℕ} [Fact p.Prime]

/-- **A permutation of `𝔽_p` conjugating the unit translation into the affine group is affine.**
If `s τ s⁻¹` is affine for the translation `τ : x ↦ x + 1`, then `s τ s⁻¹` has no fixed point, so
it is a translation `x ↦ x + c`; then `s (x + 1) = s x + c` for every `x`, and since `𝔽_p` is
generated by `1` this forces `s x = c x + s 0`. -/
theorem mem_range_toPermHom_zmod_of_mul_mul_inv_mem {s : Perm (ZMod p)}
    (hs : s * toPermHom (AffineGroup (ZMod p)) (ZMod p)
        (SemidirectProduct.inl (Multiplicative.ofAdd 1)) * s⁻¹ ∈
      (toPermHom (AffineGroup (ZMod p)) (ZMod p)).range) :
    s ∈ (toPermHom (AffineGroup (ZMod p)) (ZMod p)).range := by
  obtain ⟨g, hg⟩ := hs
  -- `s (x + 1) = g • s x` for every `x`.
  have hstep (x : ZMod p) : s (x + 1) = g.left.toAdd + (g.right : ZMod p) * s x := by
    have := congrArg (· (s x)) hg
    simp only [toPermHom_apply, toPerm_apply, smul_def, Perm.mul_apply,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, toAdd_ofAdd, Units.val_one,
      one_mul] at this
    simpa [add_comm] using this.symm
  -- The linear part of `g` is `1`: otherwise `g` would fix the point `s z` for some `z`, and then
  -- `s (z + 1) = s z`, which is impossible.
  have hg1 : (g.right : ZMod p) = 1 := by
    by_contra hne
    have hne' : (1 : ZMod p) - g.right ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    obtain ⟨w, hw⟩ := hne'.isUnit.exists_left_inv
    set y := g.left.toAdd * w
    have hfix : g.left.toAdd + (g.right : ZMod p) * y = y := by
      linear_combination (-g.left.toAdd) * hw
    have h := hstep (s⁻¹ y)
    rw [Perm.coe_inv, Equiv.apply_symm_apply, hfix] at h
    have h' : s (s.symm y + 1) = s (s.symm y) := by rw [h, Equiv.apply_symm_apply]
    exact one_ne_zero (add_eq_left.1 (s.injective h'))
  -- Hence `s n = n c + s 0` for every natural number `n`, and every element of `ZMod p` is one.
  have hnat (n : ℕ) : s n = g.left.toAdd * n + s 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hstep, hg1, one_mul, ih]; ring
  rw [mem_range_toPermHom_iff]
  exact ⟨g.left.toAdd, s 0, fun x ↦ by rw [← ZMod.natCast_zmod_val x, hnat]⟩

/-- **`AGL(1, p)` is self-normalizing in `Sym(𝔽_p)`.** -/
theorem normalizer_range_toPermHom_zmod :
    Subgroup.normalizer ((toPermHom (AffineGroup (ZMod p)) (ZMod p)).range : Set (Perm (ZMod p))) =
      (toPermHom (AffineGroup (ZMod p)) (ZMod p)).range := by
  refine le_antisymm (fun s hs ↦ mem_range_toPermHom_zmod_of_mul_mul_inv_mem ?_)
    Subgroup.le_normalizer
  exact (Subgroup.mem_normalizer_iff.1 hs _).1 ⟨_, rfl⟩

/-- **Conjugacy of surjections onto `AGL(1, p)`.** Let `φ ψ : Γ →* AffineGroup (ZMod p)` with `φ`
surjective. The permutation representations they induce on `𝔽_p` are conjugate by a
permutation of `𝔽_p` exactly when `φ` and `ψ` are conjugate by an element of the affine group. -/
theorem exists_perm_conj_iff_exists_conj {Γ : Type*} [Group Γ]
    {φ ψ : Γ →* AffineGroup (ZMod p)} (hφ : Function.Surjective φ) :
    (∃ s : Perm (ZMod p), ∀ γ, toPermHom _ _ (ψ γ) = s * toPermHom _ _ (φ γ) * s⁻¹) ↔
      ∃ h : AffineGroup (ZMod p), ∀ γ, ψ γ = h * φ γ * h⁻¹ := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨γ₀, hγ₀⟩ := hφ (SemidirectProduct.inl (Multiplicative.ofAdd 1))
    obtain ⟨h, rfl⟩ := mem_range_toPermHom_zmod_of_mul_mul_inv_mem (s := s)
      (by rw [← hγ₀, ← hs]; exact ⟨_, rfl⟩)
    refine ⟨h, fun γ ↦ toPerm_injective (β := ZMod p) ?_⟩
    have hγ := hs γ
    rw [← map_inv, ← map_mul, ← map_mul] at hγ
    exact hγ
  · rintro ⟨h, hh⟩
    exact ⟨toPermHom _ _ h, fun γ ↦ by rw [hh, map_mul, map_mul, map_inv]⟩

end ZMod

end AffineGroup

end TauCeti
