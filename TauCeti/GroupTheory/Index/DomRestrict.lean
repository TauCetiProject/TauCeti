/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Restricting homomorphisms to subgroups of finite index

Let `H` be a subgroup of a commutative group `G`, and let `A` be a commutative group. Every
element `g` of `G` has its power `g ^ [G : H]` in `H`. When raising to the power `[G : H]` is a
bijection of `A`, a homomorphism `G →* A` is therefore determined by its restriction to `H`, and
every homomorphism `H →* A` extends: restriction `(G →* A) → (H →* A)` is a bijection
(`MonoidHom.domRestrictHom_bijective_of_bijective_pow`). For `A = ℤ/n` this applies as soon as
`[G : H]` is prime to `n` (`AddMonoidHom.domRestrictHom_zmod_bijective_of_coprime`).

For a prime `p`, a nonzero homomorphism `χ : G → ℤ/p` from any group `G` has kernel of index `p`,
so for `H` of index `p` it vanishes on `H` exactly when its kernel is `H`
(`AddMonoidHom.domRestrict_eq_zero_iff_of_index_eq`). For `p = 2` a homomorphism is determined
by its kernel (`AddMonoidHom.eq_of_ker_eq_zmod_two`), so restriction to a subgroup of index two
kills exactly two homomorphisms `G → ℤ/2`: zero and the one with kernel `H`.

With `G = H₁(C; ℤ)` of a torus `C`, the homomorphisms `G → ℤ/2` are the real flat sign lines on
`C`. A finite connected cover of `C` is again a torus, and its `H₁` maps isomorphically onto a
subgroup `H` of finite index, so the homomorphisms `H → ℤ/2` are the sign lines of the cover.
These statements then describe the pullback of sign lines along such covers: covers of odd degree
pull them back bijectively, and the double cover defined by a sign line `ι` trivializes exactly
`0` and `ι`. When `G` has rank two, the other two sign lines `χ` and `χ + ι` are exactly those
not trivialized, and they have the same pullback
(`TauCeti.setOf_domRestrict_ker_ne_zero_eq_of_finrank_eq_two`).

## Main results

* `MonoidHom.domRestrictHom_bijective_of_bijective_pow`,
  `AddMonoidHom.domRestrictHom_bijective_of_bijective_nsmul`: restriction to `H` is bijective
  when raising to the power `[G : H]` is bijective on the target.
* `AddMonoidHom.domRestrictHom_zmod_bijective_of_coprime`: restriction of homomorphisms to `ℤ/n`
  is bijective when `[G : H]` is prime to `n`.
* `AddMonoidHom.domRestrict_ker_add_self`: adding `ι` does not change restrictions to `ker ι`.
* `AddMonoidHom.index_ker_zmod`: a nonzero homomorphism to `ℤ/p` has kernel of index `p`.
* `AddMonoidHom.domRestrict_eq_zero_iff_of_index_eq`: for `H` of index `p`, a homomorphism to
  `ℤ/p` vanishes on `H` iff it is zero or has kernel `H`.
* `AddMonoidHom.eq_of_ker_eq_zmod_two`: homomorphisms to `ℤ/2` with equal kernels are equal.
* `AddMonoidHom.domRestrict_ker_eq_zero_iff_zmod_two`: the homomorphisms to `ℤ/2` vanishing on the
  kernel of a nonzero `ι` are `0` and `ι`.
* `TauCeti.setOf_domRestrict_ker_ne_zero_eq_of_finrank_eq_two`: on a lattice of rank two, the
  homomorphisms to `ℤ/2` not vanishing on the kernel of a nonzero `ι` are `χ` and `χ + ι`.
-/

public section

namespace MonoidHom

variable {G A : Type*} [CommGroup G] [CommGroup A]

/-- If raising to the power `[G : H]` is a bijection of the commutative group `A`, then
restriction of homomorphisms `G →* A` to the subgroup `H` is a bijection. -/
@[to_additive /-- If multiplication by `[G : H]` is a bijection of the commutative group `A`, then
restriction of homomorphisms `G →+ A` to the subgroup `H` is a bijection. -/]
theorem domRestrictHom_bijective_of_bijective_pow (H : Subgroup G)
    (hA : Function.Bijective (powMonoidHom (α := A) H.index)) :
    Function.Bijective (domRestrictHom H A) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun χ hχ ↦ ?_, fun ψ ↦ ?_⟩
  · ext g
    apply hA.1
    have := DFunLike.congr_fun hχ ⟨_, H.pow_index_mem g⟩
    simpa [map_pow] using this
  · let e := MulEquiv.ofBijective (powMonoidHom (α := A) H.index) hA
    refine ⟨(e.symm : A →* A).comp
      (ψ.comp ((powMonoidHom H.index).codRestrict H fun g ↦ by simpa using H.pow_index_mem g)), ?_⟩
    ext h
    refine e.symm_apply_eq.2 ?_
    simp only [e, MulEquiv.ofBijective_apply, powMonoidHom_apply, ← map_pow]
    exact congrArg ψ (Subtype.ext (by simp))

end MonoidHom

namespace AddMonoidHom

section Comm

variable {G : Type*} [AddCommGroup G]

/-- If the index of `H` is prime to `n`, restriction of homomorphisms `G →+ ℤ/n` to `H` is a
bijection. -/
theorem domRestrictHom_zmod_bijective_of_coprime {n : ℕ} (H : AddSubgroup G)
    (h : H.index.Coprime n) : Function.Bijective (domRestrictHom H (ZMod n)) := by
  refine domRestrictHom_bijective_of_bijective_nsmul H ?_
  have : (nsmulAddMonoidHom (α := ZMod n) H.index : ZMod n → ZMod n) =
      ((ZMod.unitOfCoprime _ h : ZMod n) * ·) := by
    ext a
    simp [nsmul_eq_mul]
  rw [this]
  exact (Units.mulLeft _).bijective

end Comm

variable {G : Type*} [AddGroup G]

/-- Adding a homomorphism `ι` does not change the restriction of a homomorphism to the kernel of
`ι`. -/
@[simp]
theorem domRestrict_ker_add_self {A : Type*} [AddCommGroup A] (χ ι : G →+ A) :
    (χ + ι).domRestrict ι.ker = χ.domRestrict ι.ker := by
  ext x
  simp [mem_ker.1 x.property]

/-- A nonzero homomorphism to `ℤ/p`, for a prime `p`, has kernel of index `p`. -/
theorem index_ker_zmod {p : ℕ} [Fact p.Prime] {χ : G →+ ZMod p} (hχ : χ ≠ 0) :
    χ.ker.index = p := by
  rw [AddSubgroup.index_ker]
  have hdvd : Nat.card χ.range ∣ p := by
    simpa using χ.range.card_addSubgroup_dvd_card
  refine ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd).resolve_left fun h ↦ hχ ?_
  exact range_eq_bot_iff.1 (AddSubgroup.card_eq_one.1 h)

/-- For a subgroup `H` of prime index `p`, a homomorphism to `ℤ/p` vanishes on `H` if and only if
it is zero or its kernel is `H`. -/
theorem domRestrict_eq_zero_iff_of_index_eq {p : ℕ} [Fact p.Prime] {H : AddSubgroup G}
    (hH : H.index = p) {χ : G →+ ZMod p} : χ.domRestrict H = 0 ↔ χ = 0 ∨ χ.ker = H := by
  have hle : χ.domRestrict H = 0 ↔ H ≤ χ.ker := by
    simp [IsConcreteLE.le_iff]
  rw [hle]
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hχ ↦ le_antisymm ?_ h, ?_⟩
  · have hmul := AddSubgroup.relIndex_mul_index h
    rw [index_ker_zmod hχ, hH] at hmul
    exact AddSubgroup.relIndex_eq_one.1
      (Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos (by rw [hmul, one_mul]))
  · rintro (rfl | h)
    · simp
    · exact h.ge

/-- Two homomorphisms to `ℤ/2` with the same kernel are equal. -/
theorem eq_of_ker_eq_zmod_two {χ ψ : G →+ ZMod 2} (h : χ.ker = ψ.ker) : χ = ψ := by
  ext g
  have hg : χ g = 0 ↔ ψ g = 0 := by simpa using SetLike.ext_iff.1 h g
  revert hg
  generalize χ g = a
  generalize ψ g = b
  revert a b
  decide

/-- The homomorphisms to `ℤ/2` that vanish on the kernel of a nonzero homomorphism `ι : G → ℤ/2`
are `0` and `ι`. -/
theorem domRestrict_ker_eq_zero_iff_zmod_two {ι χ : G →+ ZMod 2} (hι : ι ≠ 0) :
    χ.domRestrict ι.ker = 0 ↔ χ = 0 ∨ χ = ι := by
  rw [domRestrict_eq_zero_iff_of_index_eq (index_ker_zmod hι)]
  exact or_congr_right ⟨eq_of_ker_eq_zmod_two, fun h ↦ h ▸ rfl⟩

end AddMonoidHom

namespace TauCeti

open Module

variable {Λ : Type*} [AddCommGroup Λ]

/-- **Pullback to the double cover.** On a lattice of rank two, let `ι` be a nonzero homomorphism
to `ℤ/2` and `χ` one that does not vanish on `ker ι`. Then the homomorphisms to `ℤ/2` that do not
vanish on `ker ι` are exactly `χ` and `χ + ι`, which have the same restriction to `ker ι` by
`AddMonoidHom.domRestrict_ker_add_self`. -/
theorem setOf_domRestrict_ker_ne_zero_eq_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (h : finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ : χ.domRestrict ι.ker ≠ 0) :
    {ψ : Λ →+ ZMod 2 | ψ.domRestrict ι.ker ≠ 0} = {χ, χ + ι} := by
  obtain ⟨hχ₀, hχι⟩ : χ ≠ 0 ∧ χ ≠ ι := by
    simpa [not_or] using (AddMonoidHom.domRestrict_ker_eq_zero_iff_zmod_two hι).not.1 hχ
  have := nodup_addMonoidHom_zmod_two hι hχ₀ hχι
  ext ψ
  rcases addMonoidHom_zmod_two_eq_zero_or_eq_or_eq_or_eq_add_of_finrank_eq_two h hι hχ₀ hχι ψ
    with rfl | rfl | rfl | rfl <;>
    simp_all [AddMonoidHom.domRestrict_ker_eq_zero_iff_zmod_two hι,
      eq_comm (a := (0 : Λ →+ ZMod 2))]

end TauCeti
