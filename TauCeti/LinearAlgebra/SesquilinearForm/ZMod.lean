/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import TauCeti.Algebra.Module.ZMod.Annihilator

/-!
# Orthogonal complements in finite pairings over `ℤ/n`

For a pairing `B : M × N → ℤ/n` identifying `N` with the dual of `M`, the orthogonal
complement of a submodule `S` has `Nat.card` equal to that of `M / S`. Consequently
`Nat.card S * Nat.card S⊥ = Nat.card M`, without assuming finiteness. When `M` is finite,
an orthogonal submodule is the entire annihilator precisely when its order has this value.
For a perfect pairing of finite modules, taking orthogonal complements twice recovers the
original submodule, with the flipped pairing on the second step.

These cardinality criteria apply to local duality pairings, where orthogonality of
local conditions and their orders are established separately. No freeness or
primality of the modulus is required. We use Mathlib's `Submodule.orthogonalBilin`,
reinterpreting the pairing as a biadditive map to apply the subgroup-annihilator count in
`TauCeti.Algebra.Module.ZMod.Annihilator`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2–3.
-/

public section

namespace LinearMap

variable {n : ℕ} [NeZero n] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod n) M] [Module (ZMod n) N] [Finite M]
  (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n)

omit [Finite M] in
/-- A pairing over `ℤ/n` with bijective right adjoint has left and right modules of
equal order. -/
theorem natCard_eq_of_bijective_flip_zmod (hB : Function.Bijective B.flip) :
    Nat.card N = Nat.card M :=
  (Nat.card_congr (LinearEquiv.ofBijective B.flip hB).toEquiv).trans
    (AddEquiv.refl (ZMod n)).natCard_linearMap_zmod

/-- The right module of a pairing over `ℤ/n` with bijective right adjoint is finite
if the left module is finite. -/
theorem finite_of_bijective_flip_zmod (hB : Function.Bijective B.flip) : Finite N := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_eq_of_bijective_flip_zmod B hB]
  exact (Nat.card_pos (α := M)).ne'

end LinearMap

namespace Submodule

variable {n : ℕ} [NeZero n] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod n) M] [Module (ZMod n) N] [Finite M]
  (S : Submodule (ZMod n) M) (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n)

omit [Finite M] in
/-- The orthogonal complement has `Nat.card` equal to that of the quotient if the right
adjoint of the pairing is bijective. Neither module need be finite. -/
theorem natCard_orthogonalBilin_zmod (hB : Function.Bijective B.flip) :
    Nat.card (S.orthogonalBilin B) = Nat.card (M ⧸ S) := by
  let e := (AddMonoidHom.toZModLinearMapEquiv n).symm.toAddMonoidHom.comp
    B.flip.toAddMonoidHom
  have he : Function.Bijective e :=
    (AddMonoidHom.toZModLinearMapEquiv n).symm.bijective.comp hB
  have hker : (e.compl₂ S.toAddSubgroup.subtype).ker =
      (S.orthogonalBilin B).toAddSubgroup := by
    ext y
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.ext_iff, AddMonoidHom.compl₂_apply,
      AddMonoidHom.zero_apply, Subtype.forall, mem_toAddSubgroup, mem_orthogonalBilin]
    -- Forgetting linearity and flipping the pairing preserve its pointwise values.
    rfl
  have h := e.natCard_ker_compl₂_subtype_eq_index_zmod he
    (ZModModule.char_nsmul_eq_zero n) S.toAddSubgroup
  rw [hker] at h
  -- Submodules and their additive subgroups have the same carrier and quotient types.
  exact h

omit [Finite M] in
/-- The `Nat.card`s of a submodule and its orthogonal complement multiply to the `Nat.card`
of the left module if the right adjoint is bijective. Neither module need be finite. -/
theorem natCard_mul_natCard_orthogonalBilin_zmod (hB : Function.Bijective B.flip) :
    Nat.card S * Nat.card (S.orthogonalBilin B) = Nat.card M := by
  rw [S.natCard_orthogonalBilin_zmod B hB]
  exact S.card_eq_card_quotient_mul_card.symm

/-- An orthogonal submodule is the entire annihilator exactly when the product of
its order with that of the left submodule is the ambient order. -/
theorem eq_orthogonalBilin_iff_natCard_mul_eq_zmod (hB : Function.Bijective B.flip)
    (T : Submodule (ZMod n) N) (hT : T ≤ S.orthogonalBilin B) :
    T = S.orthogonalBilin B ↔ Nat.card S * Nat.card T = Nat.card M := by
  have : Finite N := B.finite_of_bijective_flip_zmod hB
  constructor
  · rintro rfl
    exact S.natCard_mul_natCard_orthogonalBilin_zmod B hB
  · intro hcard
    apply toAddSubgroup_injective
    apply AddSubgroup.eq_of_le_of_card_ge ((toAddSubgroup_le _ _).2 hT)
    have h := S.natCard_mul_natCard_orthogonalBilin_zmod B hB
    -- A submodule and its underlying additive subgroup have the same carrier type.
    exact (Nat.mul_left_cancel (Nat.card_pos (α := S)) (hcard.trans h.symm)).ge

/-- Under a perfect pairing of finite `ℤ/n`-modules, the double orthogonal complement
is the original submodule. The pairing is flipped on the second step. -/
@[simp]
theorem orthogonalBilin_flip_orthogonalBilin_zmod [B.IsPerfPair] :
    (S.orthogonalBilin B).orthogonalBilin B.flip = S := by
  have hB := LinearMap.IsPerfPair.bijective_right B
  have : Finite N := B.finite_of_bijective_flip_zmod hB
  symm
  apply ((S.orthogonalBilin B).eq_orthogonalBilin_iff_natCard_mul_eq_zmod B.flip
    (LinearMap.IsPerfPair.bijective_right B.flip) S le_orthogonalBilin_flip_orthogonalBilin).2
  rw [mul_comm, S.natCard_mul_natCard_orthogonalBilin_zmod B hB,
    B.natCard_eq_of_bijective_flip_zmod hB]

end Submodule
