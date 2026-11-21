/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Dual
public import Mathlib.GroupTheory.Index

/-!
# Annihilators in biadditive pairings into `ℤ/n`

Let `n ≠ 0`, let `N` be an additive commutative group killed by `n`, and suppose the left
adjoint `e : M →+ N →+ ZMod n` is bijective. The annihilator of a subgroup `H ≤ N` is the
kernel of the restricted pairing `e.compl₂ H.subtype`. Its `Nat.card` equals the index of
`H`, and `Nat.card (e.compl₂ H.subtype).ker * Nat.card H = Nat.card M`. Neither identity
requires finiteness. The first gives zero on both sides when `H` has infinite index; the
second gives zero on both sides whenever `N` (and hence `M`) is infinite.

When `N` is finite, an arbitrary subgroup `U ≤ M` equals this annihilator if and only if
it is orthogonal to `H` and `Nat.card U * Nat.card H = Nat.card M`. This counting criterion
upgrades orthogonality and order computations to equality of local conditions under finite
Tate pairings. It works for composite `n`, without choosing module structures or bases.
Bijectivity of the left adjoint is not asserted to be two-sided perfection for infinite `N`.

The proofs use Mathlib's identification of the kernel of character restriction with the
characters of the quotient, and `TauCeti.natCard_addMonoidHom_zmod` for their order. For finite `N`,
`AddMonoidHom.bijective_flip_zmod` and
`AddMonoidHom.ker_flip_compl₂_subtype_ker_compl₂_subtype_zmod` give perfection of the flipped
pairing and the double-annihilator identity, with companions for pairings valued in an arbitrary
group `C ≃+ ZMod n`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §2, for the application to local
  conditions under Tate duality.
-/

public section

namespace AddMonoidHom

variable {n : ℕ} [NeZero n] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (e : M →+ N →+ ZMod n)

/-- If `n ≠ 0`, `N` is killed by `n`, and the left adjoint `e` is bijective, the
annihilator of `H` has `Nat.card` equal to `[N : H]`. No finiteness is required. -/
theorem natCard_ker_compl₂_subtype_eq_index_zmod (he : Function.Bijective e)
    (hN : ∀ y : N, n • y = 0) (H : AddSubgroup N) :
    Nat.card (e.compl₂ H.subtype).ker = H.index := by
  let E := Equiv.ofBijective e he
  have hmem (x : M) : x ∈ (e.compl₂ H.subtype).ker ↔
      E x ∈ (domRestrictHom H (ZMod n)).ker := by
    simp only [mem_ker, AddMonoidHom.ext_iff, compl₂_apply, domRestrictHom_apply,
      domRestrict_apply, E, Equiv.ofBijective_apply, AddSubgroup.subtype_apply]
  rw [Nat.card_congr (Equiv.subtypeEquiv E hmem),
    Nat.card_congr (domRestrictHomKerEquiv (ZMod n) H).toEquiv,
    TauCeti.natCard_addMonoidHom_zmod]
  · rfl
  · intro y
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective H y
    rw [← map_nsmul, hN, map_zero]

/-- If `n ≠ 0`, `N` is killed by `n`, and the left adjoint `e` is bijective, the product
of the `Nat.card`s of the annihilator and `H` equals `Nat.card M`. No finiteness is required. -/
theorem natCard_ker_compl₂_subtype_mul_natCard_zmod (he : Function.Bijective e)
    (hN : ∀ y : N, n • y = 0) (H : AddSubgroup N) :
    Nat.card (e.compl₂ H.subtype).ker * Nat.card H = Nat.card M := by
  rw [e.natCard_ker_compl₂_subtype_eq_index_zmod he hN, H.index_mul_card,
    Nat.card_congr (Equiv.ofBijective e he), TauCeti.natCard_addMonoidHom_zmod hN]

/-- For finite `N` killed by `n ≠ 0` and bijective left adjoint `e`, a subgroup `U ≤ M`
equals the annihilator of `H` if and only if `U` is orthogonal to `H` and
`Nat.card U * Nat.card H = Nat.card M`. -/
theorem eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod [Finite N]
    (he : Function.Bijective e) (hN : ∀ y : N, n • y = 0) (U : AddSubgroup M) (H : AddSubgroup N) :
    U = (e.compl₂ H.subtype).ker ↔
      (∀ x ∈ U, ∀ y ∈ H, e x y = 0) ∧ Nat.card U * Nat.card H = Nat.card M := by
  have : Finite (N →+ ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite M := Finite.of_injective e he.1
  have hle : U ≤ (e.compl₂ H.subtype).ker ↔ ∀ x ∈ U, ∀ y ∈ H, e x y = 0 := by
    simp only [IsConcreteLE.le_iff, mem_ker, AddMonoidHom.ext_iff, compl₂_apply, zero_apply,
      Subtype.forall, AddSubgroup.subtype_apply]
  constructor
  · intro h
    exact ⟨hle.mp h.le, h ▸ e.natCard_ker_compl₂_subtype_mul_natCard_zmod he hN H⟩
  · rintro ⟨horth, hcard⟩
    apply AddSubgroup.eq_of_le_of_card_ge (hle.mpr horth)
    have h := e.natCard_ker_compl₂_subtype_mul_natCard_zmod he hN H
    exact (Nat.mul_right_cancel Nat.card_pos (h.trans hcard.symm)).le

/-- For finite `N` killed by `n ≠ 0`, if the left adjoint `e : M →+ N →+ ZMod n` is bijective,
then the right adjoint `e.flip : N →+ M →+ ZMod n` is also bijective. -/
theorem bijective_flip_zmod [Finite N] (he : Function.Bijective e) (hN : ∀ y : N, n • y = 0) :
    Function.Bijective e.flip := by
  obtain ⟨hsep, hrep⟩ := TauCeti.forall_eq_zero_and_exists_eq_of_bijective_flip hN e.flip he
  refine ⟨(injective_iff_map_eq_zero e.flip).2 fun y hy ↦ hsep y fun x ↦ DFunLike.congr_fun hy x,
    fun φ ↦ ?_⟩
  obtain ⟨y, hy⟩ := hrep φ
  exact ⟨y, AddMonoidHom.ext hy⟩

/-- **Double-annihilator theorem for finite `ℤ/n`-pairings.** For finite `N` killed by `n ≠ 0` and
bijective left adjoint `e : M →+ N →+ ZMod n`, the annihilator under `e.flip` of the annihilator of
`H ≤ N` is `H` itself. -/
@[simp]
theorem ker_flip_compl₂_subtype_ker_compl₂_subtype_zmod [Finite N] (he : Function.Bijective e)
    (hN : ∀ y : N, n • y = 0) (H : AddSubgroup N) :
    (e.flip.compl₂ (e.compl₂ H.subtype).ker.subtype).ker = H := by
  have : Finite (N →+ ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite M := Finite.of_injective e he.1
  have hM : ∀ x : M, n • x = 0 := fun x ↦ he.1 <| by
    ext y
    rw [map_nsmul, map_zero, nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, zero_apply]
  have ⟨horth, hcard⟩ :=
    (e.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod he hN _ H).mp rfl
  symm
  refine (e.flip.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
    (e.bijective_flip_zmod he hN) hM H _).mpr ⟨fun y hy x hx ↦ horth x hx y hy, ?_⟩
  rw [mul_comm, hcard, Nat.card_congr (Equiv.ofBijective e he),
    TauCeti.natCard_addMonoidHom_zmod hN]

/-- Transport of `eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod` to a pairing
`d : M →+ N →+ C` valued in a group `C` equipped with `eC : C ≃+ ZMod n`. -/
theorem eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_of_addEquiv_zmod
    {C : Type*} [AddCommGroup C] [Finite N] (d : M →+ N →+ C) (eC : C ≃+ ZMod n)
    (hd : Function.Bijective d) (hN : ∀ y : N, n • y = 0) (U : AddSubgroup M) (H : AddSubgroup N) :
    U = (d.compl₂ H.subtype).ker ↔
      (∀ x ∈ U, ∀ y ∈ H, d x y = 0) ∧ Nat.card U * Nat.card H = Nat.card M := by
  let e : M →+ N →+ ZMod n := eC.addMonoidHomCongrRight.toAddMonoidHom.comp d
  have he : Function.Bijective e := eC.addMonoidHomCongrRight.bijective.comp hd
  have hker : (e.compl₂ H.subtype).ker = (d.compl₂ H.subtype).ker := by
    ext x
    simp [e, AddMonoidHom.ext_iff]
  rw [← hker, e.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod he hN]
  simp [e]

/-- Double-annihilator theorem for a finite pairing `d : M →+ N →+ C` valued in `C ≃+ ZMod n`. -/
theorem ker_flip_compl₂_subtype_ker_compl₂_subtype_of_addEquiv_zmod
    {C : Type*} [AddCommGroup C] [Finite N] (d : M →+ N →+ C) (eC : C ≃+ ZMod n)
    (hd : Function.Bijective d) (hN : ∀ y : N, n • y = 0) (H : AddSubgroup N) :
    (d.flip.compl₂ (d.compl₂ H.subtype).ker.subtype).ker = H := by
  let e : M →+ N →+ ZMod n := eC.addMonoidHomCongrRight.toAddMonoidHom.comp d
  have he : Function.Bijective e := eC.addMonoidHomCongrRight.bijective.comp hd
  have hker : (e.compl₂ H.subtype).ker = (d.compl₂ H.subtype).ker := by
    ext x
    simp [e, AddMonoidHom.ext_iff]
  have hker' : (e.flip.compl₂ (d.compl₂ H.subtype).ker.subtype).ker =
      (d.flip.compl₂ (d.compl₂ H.subtype).ker.subtype).ker := by
    ext y
    simp [e, AddMonoidHom.ext_iff]
  rw [← hker', ← hker, e.ker_flip_compl₂_subtype_ker_compl₂_subtype_zmod he hN]

end AddMonoidHom
