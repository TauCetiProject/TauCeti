/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Algebra.Group.Subgroup.Centralizer
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Projection

/-!
# The Brauer projection and the relative trace on `S₃`

Examples in the group algebra of the symmetric group `S₃ = Equiv.Perm (Fin 3)`. The first ones
show that each hypothesis of the multiplicativity of the Brauer projection on invariants
(`TauCeti.brauerProjection_mul`) is needed; the last ones compute relative traces
(`TauCeti.relTrace`). Throughout, `r` is the `3`-cycle `finRotate 3`, `s` is the transposition
`Equiv.swap 0 1` and `P = ⟨s⟩` has order `2`, so that `s r s = r²` and `C_{S₃}(P) = P`.

* Over `𝔽₂`, `x = r + r²` is `P`-invariant with `x² = x`, and `Br_P(x²) = 0 = Br_P(x)²`.
* Invariance is needed: `Br_P(r r²) = Br_P(1) = 1`, but `Br_P(r) Br_P(r²) = 0`.
* Characteristic `p` is needed: over `ℚ`, `Br_P(x²) = 2` but `Br_P(x)² = 0`. And `P` must be a
  `p`-group: over `𝔽₂` with `P = ⟨r⟩ ≅ C₃` and `t` the sum of the three transpositions, `t` is
  `⟨r⟩`-invariant, `Br_{⟨r⟩}(t) = 0`, but `Br_{⟨r⟩}(t²)` has coefficient `1` at the identity.
* Over `𝔽₂`, `Tr_1^P(r) = r + r²`, which is `P`-invariant although `r` is not;
  `Tr_1^P(1) = |P| • 1 = 0`; and `Tr_P^P` is the identity of `𝔽₂[S₃]^P`.
-/

public section

namespace TauCeti.Examples.BrauerProjectionS3

open MonoidAlgebra

/-- The `3`-cycle `r = (0 1 2)` of `S₃`. -/
abbrev r : Equiv.Perm (Fin 3) := finRotate 3

/-- The transposition `s = (0 1)` of `S₃`. -/
abbrev s : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The subgroup `P = ⟨s⟩` of order `2`. -/
abbrev P : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers s

section Coefficients

variable (R : Type) [CommRing R]

/-- The element `x = r + r²` of `R[S₃]`. -/
noncomputable abbrev x : MonoidAlgebra R (Equiv.Perm (Fin 3)) := single r 1 + single (r * r) 1

/-- `x = r + r²` is invariant under conjugation by `P`. -/
theorem x_mem_conjInvariants : x R ∈ conjInvariants R P := by
  refine mem_conjInvariants_zpowers_iff.2 ?_
  simp only [of_apply, mul_add, add_mul, single_mul_single, mul_one]
  rw [show s * r = r * r * s by decide, show s * (r * r) = r * s by decide, add_comm]

/-- `r` and `r²` are not in the centralizer of `P`. -/
private theorem r_notMem : r ∉ Subgroup.centralizer (P : Set (Equiv.Perm (Fin 3))) :=
  mt Subgroup.mem_centralizer_zpowers_iff.1 (by decide)

private theorem r_sq_notMem : r * r ∉ Subgroup.centralizer (P : Set (Equiv.Perm (Fin 3))) :=
  mt Subgroup.mem_centralizer_zpowers_iff.1 (by decide)

/-- `Br_P(x) = 0`, since neither `r` nor `r²` centralizes `P`. -/
theorem brauerProjection_x : brauerProjection P (x R) = 0 := by
  rw [map_add, brauerProjection_single_of_notMem _ r_notMem,
    brauerProjection_single_of_notMem _ r_sq_notMem, add_zero]

/-- `x² = 2 + x`. -/
theorem x_mul_x : x R * x R = single 1 2 + x R := by
  simp only [x, mul_add, add_mul, single_mul_single, mul_one,
    show r * (r * r) = 1 by decide, show r * r * r = 1 by decide,
    show r * r * (r * r) = r by decide]
  rw [show (2 : R) = 1 + 1 by norm_num, single_add]
  abel

end Coefficients

/-- Over `𝔽₂`, `x = r + r²` is idempotent. -/
example : x (ZMod 2) * x (ZMod 2) = x (ZMod 2) := by
  rw [x_mul_x, show (2 : ZMod 2) = 0 by decide, single_zero, zero_add]

/-- **Check.** Over `𝔽₂`, `Br_P(x²) = 0 = Br_P(x)²`, as `brauerProjection_mul` predicts for the
`P`-invariant `x`. -/
example : brauerProjection P (x (ZMod 2) * x (ZMod 2)) = 0 ∧
    brauerProjection P (x (ZMod 2)) * brauerProjection P (x (ZMod 2)) = 0 := by
  rw [x_mul_x, show (2 : ZMod 2) = 0 by decide, single_zero, zero_add, brauerProjection_x,
    zero_mul]
  exact ⟨rfl, rfl⟩

/-- **Check: invariance is needed.** For `r` and `r²`, which are not `P`-invariant,
`Br_P(r r²) = Br_P(1) = 1` but `Br_P(r) Br_P(r²) = 0`. -/
example : brauerProjection P (single r (1 : ZMod 2) * single (r * r) 1) = 1 ∧
    brauerProjection P (single r (1 : ZMod 2)) * brauerProjection P (single (r * r) 1) = 0 := by
  rw [single_mul_single, show r * (r * r) = 1 by decide, mul_one, ← one_def,
    brauerProjection_one, brauerProjection_single_of_notMem _ r_notMem, zero_mul]
  exact ⟨rfl, rfl⟩

/-- **Check: characteristic `p` is needed.** Over `ℚ`, `Br_P(x²) = 2` but `Br_P(x)² = 0`. -/
example : brauerProjection P (x ℚ * x ℚ) = single 1 2 ∧
    brauerProjection P (x ℚ) * brauerProjection P (x ℚ) = 0 := by
  rw [x_mul_x, map_add, brauerProjection_x, add_zero, zero_mul,
    ← OneMemClass.coe_one (Subgroup.centralizer (P : Set (Equiv.Perm (Fin 3)))),
    brauerProjection_single_coe]
  exact ⟨rfl, rfl⟩

/-- The subgroup `⟨r⟩ ≅ C₃`, which is not a `2`-group. -/
abbrev C3 : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.zpowers r

/-- The sum `t` of the three transpositions of `S₃`. -/
noncomputable abbrev t : MonoidAlgebra (ZMod 2) (Equiv.Perm (Fin 3)) :=
  single (Equiv.swap 0 1) 1 + single (Equiv.swap 0 2) 1 + single (Equiv.swap 1 2) 1

/-- `t` is invariant under conjugation by `⟨r⟩`. -/
theorem t_mem_conjInvariants : t ∈ conjInvariants (ZMod 2) C3 := by
  refine mem_conjInvariants_zpowers_iff.2 ?_
  simp only [of_apply, mul_add, add_mul, single_mul_single, mul_one]
  rw [show r * Equiv.swap 0 1 = Equiv.swap 1 2 * r by decide,
    show r * Equiv.swap 0 2 = Equiv.swap 0 1 * r by decide,
    show r * Equiv.swap 1 2 = Equiv.swap 0 2 * r by decide]
  abel

/-- **Check: `P` must be a `p`-group.** Over `𝔽₂`, the `C₃`-invariant sum `t` of the
transpositions has `Br_{C₃}(t) = 0`, while `Br_{C₃}(t²)` has coefficient `1` at the identity: it
is `1 + r + r²`. -/
example : brauerProjection C3 t = 0 ∧ (brauerProjection C3 (t * t)).coeff 1 = 1 := by
  refine ⟨?_, ?_⟩
  · have h (g : Equiv.Perm (Fin 3)) (hg : g * r ≠ r * g) :=
      brauerProjection_single_of_notMem C3 (mt Subgroup.mem_centralizer_zpowers_iff.1 hg)
        (1 : ZMod 2)
    rw [map_add, map_add, h (Equiv.swap 0 1) (by decide), h (Equiv.swap 0 2) (by decide),
      h (Equiv.swap 1 2) (by decide), add_zero, add_zero]
  · rw [coeff_brauerProjection, OneMemClass.coe_one]
    simp only [t, mul_add, add_mul, single_mul_single, mul_one, coeff_add, coeff_single,
      Finsupp.add_apply, Finsupp.single_apply]
    decide

/-! ### The relative trace -/

/-- Every element of `P` is `1` or `s`. -/
private theorem s_zpow (k : ℤ) : s ^ k = 1 ∨ s ^ k = s := by
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, show s ^ (2 : ℤ) = 1 by decide, one_zpow]
  · right
    rw [zpow_add, zpow_mul, show s ^ (2 : ℤ) = 1 by decide, one_zpow, one_mul, zpow_one]

/-- The transversal `{1, s}` of the trivial subgroup in `P`. -/
private def transversal : Bool → P
  | false => 1
  | true => ⟨s, Subgroup.mem_zpowers s⟩

private theorem bijective_transversal :
    Function.Bijective fun i ↦ (transversal i : P ⧸ (⊥ : Subgroup _).subgroupOf P) := by
  refine ⟨fun i j hij ↦ ?_, fun q ↦ ?_⟩
  · rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot, inv_mul_eq_one] at hij
    revert hij
    cases i <;> cases j <;> decide
  · obtain ⟨⟨g, k, rfl⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rcases s_zpow k with h | h
    · exact ⟨false, congr_arg _ (Subtype.ext h.symm)⟩
    · exact ⟨true, congr_arg _ (Subtype.ext h.symm)⟩

/-- **Check.** Over `𝔽₂`, `Tr_1^P(r) = r + r²`. -/
example : (relTrace (ZMod 2) ⊥ P (conjInvariantsBotEquiv (ZMod 2) (single r 1)) :
    MonoidAlgebra (ZMod 2) (Equiv.Perm (Fin 3))) = x (ZMod 2) := by
  rw [relTrace_apply_eq_sum_of_bijective transversal bijective_transversal]
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, transversal, coe_conjInvariantsBotEquiv, conjRepresentation_single,
    Finset.sum_singleton, OneMemClass.coe_one, one_mul, inv_one, mul_one,
    show s * r * s⁻¹ = r * r by decide]
  exact add_comm _ _

/-- `r` is not `P`-invariant, whereas `Tr_1^P(r) = r + r²` is (`x_mem_conjInvariants`). -/
example : single r (1 : ZMod 2) ∉ conjInvariants (ZMod 2) P := by
  rw [mem_conjInvariants_iff]
  intro h
  have := h s (Subgroup.mem_zpowers s)
  rw [conjRepresentation_single, show s * r * s⁻¹ = r * r by decide] at this
  have := congr_arg (fun y : MonoidAlgebra (ZMod 2) (Equiv.Perm (Fin 3)) ↦ y.coeff r) this
  simp only [coeff_single, Finsupp.single_apply] at this
  revert this
  decide

/-- **Check.** Over `𝔽₂`, `Tr_1^P(1) = |P| • 1 = 0`. -/
example : relTrace (ZMod 2) ⊥ P 1 = 0 := by
  ext1
  have hs : orderOf s = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [relTrace_apply_of_mem (by simp), ← Nat.cast_smul_eq_nsmul (ZMod 2)]
  simp [Fintype.card_zpowers, hs, show (2 : ZMod 2) = 0 by decide]

/-- **Check.** `Tr_P^P` is the identity of `𝔽₂[S₃]^P`. -/
example (a : conjInvariants (ZMod 2) P) : relTrace (ZMod 2) P P a = a :=
  relTrace_self a

end TauCeti.Examples.BrauerProjectionS3
