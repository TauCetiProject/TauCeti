/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.VirtualCharacter
import Mathlib.GroupTheory.IndexNormal

/-!
# Pairing with induction from a normal subgroup

For a normal subgroup `N`, the restriction of an induced class function pairs with a class
function on `N` as a sum over the cosets. If the second class function is invariant under
ambient conjugation, every term in that sum is the same. In particular, the pairing for virtual
characters is an integer multiple of the index. At prime index this makes the induced
constituents of a virtual character contribute zero modulo the index to the pairing on `N`.

The coset sum is the normal-subgroup case of Mackey's formula (Serre, *Linear Representations
of Finite Groups*, Chapter 7, §3).
-/

public section

namespace TauCeti

namespace ClassFunction

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal]

variable {k : Type*} [Semifield k] [Fintype N]

/-- Pairing the restriction of an induced class function with another class function on a
normal subgroup gives a sum of pairings against conjugates of the inducing function. -/
theorem characterPairing_res_ind_eq_sum [N.FiniteIndex] (f y : ClassFunction k N) :
    characterPairing (comap N.subtype (N.indClassFunction f)) y =
      letI := Fintype.ofFinite (G ⧸ N)
      ∑ q : G ⧸ N, characterPairing
        (comap (MulAut.conjNormal (H := N) q.out⁻¹).toMonoidHom f) y := by
  classical
  let := Fintype.ofFinite (G ⧸ N)
  have hres : comap N.subtype (N.indClassFunction f) =
      ∑ q : G ⧸ N, comap (MulAut.conjNormal (H := N) q.out⁻¹).toMonoidHom f := by
    apply Subtype.ext
    funext n
    simp only [comap_apply, Subgroup.indClassFunction_apply, Subgroup.indClassFun_apply,
      Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro q _
    have hnq : q.out⁻¹ * (n : G) * q.out ∈ N :=
      (inferInstance : N.Normal).conj_mem' n n.property q.out
    rw [Subgroup.coe_subtype, dite_eq_left hnq]
    exact congrArg f.val (Subtype.ext (by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, inv_inv]))
  -- Use bilinearity in the first variable, with the second variable fixed.
  simp only [hres, map_sum, LinearMap.sum_apply]

/-- If `y` is invariant under ambient conjugation, restriction after induction multiplies its
pairing with `f` by the subgroup index. No invertibility of the index is needed. -/
theorem characterPairing_res_ind_eq_index_mul [N.FiniteIndex] (f y : ClassFunction k N)
    (hy : ∀ (g : G) (n : N), y.val (MulAut.conjNormal g n) = y.val n) :
    characterPairing (comap N.subtype (N.indClassFunction f)) y =
      (N.index : k) * characterPairing f y := by
  let := Fintype.ofFinite (G ⧸ N)
  rw [characterPairing_res_ind_eq_sum]
  have hfix (g : G) : comap (MulAut.conjNormal (H := N) g).toMonoidHom y = y :=
    Subtype.ext (funext fun n ↦ (comap_apply _ _ _).trans (hy g n))
  calc
    _ = ∑ _q : G ⧸ N, characterPairing f y := by
      apply Finset.sum_congr rfl
      intro q _
      let e := MulAut.conjNormal (H := N) q.out⁻¹
      calc
        _ = characterPairing (comap e.toMonoidHom f) (comap e.toMonoidHom y) :=
          congrArg _ (hfix q.out⁻¹).symm
        _ = _ := characterPairing_comap_mulEquiv e f y
    _ = _ := by simp [Subgroup.index, Nat.card_eq_fintype_card, nsmul_eq_mul]

end ClassFunction

open ClassFunction

/-- In prime index, the pairing on `N` of a restricted induced virtual character with an
`x`-stable virtual character is an integer multiple of the index, where `x` is any element
outside `N`. -/
theorem exists_characterPairing_res_ind_eq_index_mul_intCast {G k : Type*} [Group G] [Field k]
    {N : Subgroup G} [N.Normal] [Fintype N] (hp : N.index.Prime) {x : G} (hx : x ∉ N)
    {f y : ClassFunction k N} (hf : f.val ∈ virtualCharacters k N)
    (hy : y.val ∈ virtualCharacters k N) (hyx : ∀ n : N, y.val (MulAut.conjNormal x n) = y.val n) :
    letI : N.FiniteIndex := ⟨hp.ne_zero⟩
    ∃ m : ℤ, characterPairing (comap N.subtype (N.indClassFunction f)) y = (N.index : k) * m := by
  let : N.FiniteIndex := ⟨hp.ne_zero⟩
  obtain ⟨m, hm⟩ := exists_characterPairing_eq_intCast hf hy
  refine ⟨m, ?_⟩
  rw [characterPairing_res_ind_eq_index_mul f y
    (apply_conjNormal_eq_of_isCoatom y (N.isCoatom_of_index_prime hp) hx hyx), hm]

end TauCeti
