/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import TauCeti.Algebra.Module.ZMod.Dual

/-!
# Orthogonal complements in finite pairings over `ℤ/n`

For a pairing `B : M × N → ℤ/n` identifying `N` with the dual of a finite `M`, the
orthogonal complement of a submodule `S` has the order of `M / S`. Consequently
`|S| |S⊥| = |M|`: an orthogonal subgroup is the entire annihilator precisely when its
order has this value. For a perfect pairing, taking orthogonal complements twice
recovers the original submodule, with the flipped pairing on the second step.

These cardinality criteria apply to local duality pairings, where orthogonality of
local conditions and their orders are established separately. No freeness or
primality of the modulus is required. We use Mathlib's `Submodule.orthogonalBilin`
and `Submodule.dualQuotEquivDualAnnihilator`, together with the finite `ℤ/n`-dual count in
`TauCeti.Algebra.Module.ZMod.Dual`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2–3.
-/

public section

namespace Submodule

variable {n : ℕ} [NeZero n] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod n) M] [Module (ZMod n) N] [Finite M]
  (S : Submodule (ZMod n) M) (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n)

/-- The orthogonal complement has the order of the quotient if the right adjoint of
the pairing is bijective. Only the left module is assumed finite. -/
theorem natCard_orthogonalBilin_zmod (hB : Function.Bijective B.flip) :
    Nat.card (S.orthogonalBilin B) = Nat.card (M ⧸ S) := by
  have : Finite (M ⧸ S) := Finite.of_surjective S.mkQ S.mkQ_surjective
  let e := LinearEquiv.ofBijective B.flip hB
  rw [← S.comap_dualAnnihilator_eq_orthogonalBilin B]
  exact (Nat.card_congr (e.ofSubmodule' S.dualAnnihilator).toEquiv).trans <|
    (Nat.card_congr S.dualQuotEquivDualAnnihilator.toEquiv).symm.trans <|
      (AddEquiv.refl (ZMod n)).natCard_linearMap_zmod

/-- The orders of a submodule and its orthogonal complement multiply to the order
of the left module if the right adjoint is bijective. -/
theorem natCard_mul_natCard_orthogonalBilin_zmod (hB : Function.Bijective B.flip) :
    Nat.card S * Nat.card (S.orthogonalBilin B) = Nat.card M := by
  rw [S.natCard_orthogonalBilin_zmod B hB, mul_comm]
  exact S.toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup.symm

/-- An orthogonal submodule is the entire annihilator exactly when the product of
its order with that of the left submodule is the ambient order. -/
theorem eq_orthogonalBilin_iff_natCard_mul_eq_zmod (hB : Function.Bijective B.flip)
    (T : Submodule (ZMod n) N) (hT : T ≤ S.orthogonalBilin B) :
    T = S.orthogonalBilin B ↔ Nat.card S * Nat.card T = Nat.card M := by
  have : Finite (Module.Dual (ZMod n) M) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite N := Finite.of_equiv (Module.Dual (ZMod n) M)
    (LinearEquiv.ofBijective B.flip hB).symm.toEquiv
  constructor
  · rintro rfl
    exact S.natCard_mul_natCard_orthogonalBilin_zmod B hB
  · intro hcard
    apply toAddSubgroup_injective
    apply AddSubgroup.eq_of_le_of_card_ge hT
    have h := S.natCard_mul_natCard_orthogonalBilin_zmod B hB
    exact (Nat.mul_left_cancel (Nat.card_pos (α := S)) (hcard.trans h.symm)).ge

/-- Under a perfect pairing of finite `ℤ/n`-modules, the double orthogonal complement
is the original submodule. The pairing is flipped on the second step. -/
@[simp]
theorem orthogonalBilin_flip_orthogonalBilin_zmod [B.IsPerfPair] :
    (S.orthogonalBilin B).orthogonalBilin B.flip = S := by
  have hB := LinearMap.IsPerfPair.bijective_right B
  have hB' := LinearMap.IsPerfPair.bijective_left B
  have : Finite (Module.Dual (ZMod n) M) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite N := Finite.of_equiv (Module.Dual (ZMod n) M)
    (LinearEquiv.ofBijective B.flip hB).symm.toEquiv
  have hMN : Nat.card M = Nat.card N := by
    rw [Nat.card_congr (LinearEquiv.ofBijective B.flip hB).toEquiv,
      (AddEquiv.refl (ZMod n)).natCard_linearMap_zmod]
  symm
  apply ((S.orthogonalBilin B).eq_orthogonalBilin_iff_natCard_mul_eq_zmod B.flip
    (by simpa using hB') S le_orthogonalBilin_flip_orthogonalBilin).2
  rw [mul_comm, S.natCard_mul_natCard_orthogonalBilin_zmod B hB, hMN]

end Submodule
