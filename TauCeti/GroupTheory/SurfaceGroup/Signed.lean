/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SurfaceGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.SurfaceGroup.Boundary

/-!
# Surface groups of either orientability and their peripheral subgroups

The surface groups `S⁺(g, m)` and `S⁻(g, m)` of `TauCeti.GroupTheory.SurfaceGroup.Basic` are
collected into one family `TauCeti.SurfaceGroup.Signed o g m`, indexed by the orientability
`o : Bool`, so that a surface can be recorded by the triple `(o, g, m)`. A subgroup of `S±(g, m)`
is *peripheral* when it is trivial or contained in a conjugate of a boundary subgroup `⟨pⱼ⟩`.

The fundamental group of a compact surface of negative Euler characteristic is not abelian; in
particular the whole group is not peripheral. The peripheral elements `pⱼ` are nontrivial except
on the disc.

## Main definitions

* `TauCeti.SurfaceGroup.Signed o g m`: the surface group `S⁺(g, m)` when `o = true` and `S⁻(g, m)`
  when `o = false`, with its peripheral elements `TauCeti.SurfaceGroup.Signed.peripheral` and the
  Euler characteristic `TauCeti.SurfaceGroup.Signed.eulerChar`.
* `TauCeti.SurfaceGroup.Signed.IsPeripheral`: trivial subgroups and subgroups of conjugates of
  the boundary subgroups.

## Main results

* `TauCeti.SurfaceGroup.Orientable.not_isMulCommutative_of_eulerChar_neg`,
  `TauCeti.SurfaceGroup.Nonorientable.not_isMulCommutative` and
  `TauCeti.SurfaceGroup.Signed.not_isMulCommutative_of_eulerChar_neg`: surface groups of negative
  Euler characteristic are not abelian.
* `TauCeti.SurfaceGroup.Signed.not_isPeripheral_top`: the whole group of a surface of negative
  Euler characteristic is not peripheral.
* `TauCeti.SurfaceGroup.Signed.peripheral_ne_one`: the peripheral elements are nontrivial unless
  the surface is a disc, in particular when the Euler characteristic is negative
  (`TauCeti.SurfaceGroup.Signed.peripheral_ne_one_of_eulerChar_neg`).

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1 and
  Definition 5.13 (boundary subgroups and extended boundary subgroups).
-/

public section

open Subgroup

namespace TauCeti

namespace SurfaceGroup

/-! ### Non-commutativity

Each statement is proved by a homomorphism to the symmetric group `Perm (Fin 3)`, given by the
universal property of the presentation.
-/

section Maps

open Equiv

namespace Orientable

variable {g m : ℕ}

/-- The orientable surface group of a surface of negative Euler characteristic is not
abelian. -/
theorem not_isMulCommutative_of_eulerChar_neg (h : eulerChar g m < 0) :
    ¬IsMulCommutative (Orientable g m) := by
  intro _
  have hne : (swap 0 1 * swap 1 2 : Perm (Fin 3)) ≠ swap 1 2 * swap 0 1 := by decide
  rw [eulerChar_def] at h
  rcases g with _ | _ | g
  · -- `p₁ ↦ (01)`, `p₂ ↦ (12)`, `p₃ ↦ ((01)(12))⁻¹`
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by lia⟩
    have hw : orientableWord Fin.elim0 Fin.elim0
        (Fin.cons (swap 0 1) (Fin.cons (swap 1 2) (Fin.cons (swap 0 1 * swap 1 2)⁻¹ 1)) :
          Fin (m + 3) → Perm (Fin 3)) = 1 := by
      simp [orientableWord_def, List.ofFn_succ, mul_assoc]
    have := congrArg (lift _ _ _ hw) (mul_comm' (peripheral 0 (m + 3) 0) (peripheral 0 (m + 3) 1))
    exact hne (by simpa using this)
  · -- `a₁ ↦ (01)`, `b₁ ↦ (12)`, `p₁ ↦ [(01), (12)]⁻¹`
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
    have hw : orientableWord (fun _ : Fin 1 => swap 0 1) (fun _ => swap 1 2)
        (Fin.cons (swap 0 1 * swap 1 2 * swap 0 1 * swap 1 2)⁻¹ 1 :
          Fin (m + 1) → Perm (Fin 3)) = 1 := by
      simp [orientableWord_def, List.ofFn_succ, mul_assoc]
    have := congrArg (lift _ _ _ hw) (mul_comm' (a 1 (m + 1) 0) (b 1 (m + 1) 0))
    exact hne (by simpa using this)
  · -- `a₁ ↦ (01)`, `a₂ ↦ (12)`
    have hw : orientableWord (Fin.cons (swap 0 1) (Fin.cons (swap 1 2) 1) :
        Fin (g + 2) → Perm (Fin 3)) 1 (1 : Fin m → Perm (Fin 3)) = 1 := by
      simp [orientableWord_def, Pi.one_def]
    have := congrArg (lift _ _ _ hw) (mul_comm' (a (g + 2) m 0) (a (g + 2) m 1))
    exact hne (by simpa using this)

end Orientable

namespace Nonorientable

variable {g m : ℕ}

/-- The nonorientable surface group `S⁻(g, m)` is not abelian when the surface has negative
Euler characteristic or genus at least two. -/
theorem not_isMulCommutative (h : 2 ≤ g ∨ eulerChar g m < 0) :
    ¬IsMulCommutative (Nonorientable g m) := by
  intro _
  have hne : (swap 0 1 * swap 1 2 : Perm (Fin 3)) ≠ swap 1 2 * swap 0 1 := by decide
  rw [eulerChar_def] at h
  rcases g with _ | _ | g
  · -- `p₁ ↦ (01)`, `p₂ ↦ (12)`, `p₃ ↦ ((01)(12))⁻¹`
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by lia⟩
    have hw : nonorientableWord Fin.elim0
        (Fin.cons (swap 0 1) (Fin.cons (swap 1 2) (Fin.cons (swap 0 1 * swap 1 2)⁻¹ 1)) :
          Fin (m + 3) → Perm (Fin 3)) = 1 := by
      simp [nonorientableWord_def, List.ofFn_succ]
    have := congrArg (lift _ _ hw) (mul_comm' (peripheral 0 (m + 3) 0) (peripheral 0 (m + 3) 1))
    exact hne (by simpa using this)
  · -- `c₁ ↦ (01)`, `p₁ ↦ (12)`, `p₂ ↦ (12)`
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by lia⟩
    have hw : nonorientableWord (fun _ : Fin 1 => swap 0 1)
        (Fin.cons (swap 1 2) (Fin.cons (swap 1 2) 1) : Fin (m + 2) → Perm (Fin 3)) = 1 := by
      simp [nonorientableWord_def, List.ofFn_succ, Pi.one_def, pow_two]
    have := congrArg (lift _ _ hw) (mul_comm' (c 1 (m + 2) 0) (peripheral 1 (m + 2) 0))
    exact hne (by simpa using this)
  · -- `c₁ ↦ (01)`, `c₂ ↦ (12)`
    have hw : nonorientableWord (Fin.cons (swap 0 1) (Fin.cons (swap 1 2) 1) :
        Fin (g + 2) → Perm (Fin 3)) (1 : Fin m → Perm (Fin 3)) = 1 := by
      simp [nonorientableWord_def, List.ofFn_succ, Pi.one_def, pow_two]
    have := congrArg (lift _ _ hw) (mul_comm' (c (g + 2) m 0) (c (g + 2) m 1))
    exact hne (by simpa using this)

end Nonorientable

end Maps

/-! ### The family of surface groups -/

/-- The surface group `S⁺(g, m)` when `o = true` and `S⁻(g, m)` when `o = false`. A
nonorientable surface has genus at least one; for `g = 0` both presentations give the group of
the sphere with `m` holes. The body is exposed so that `Signed true g m` and
`Signed false g m` are the groups `Orientable g m` and `Nonorientable g m` themselves. -/
@[expose] def Signed : Bool → ℕ → ℕ → Type
  | true, g, m => Orientable g m
  | false, g, m => Nonorientable g m

namespace Signed

/-- The group structure of `S±(g, m)`: that of `S⁺(g, m)` or of `S⁻(g, m)`, according as `o` is
`true` or `false`. -/
instance : ∀ (o : Bool) (g m : ℕ), Group (Signed o g m)
  | true, g, m => inferInstanceAs (Group (Orientable g m))
  | false, g, m => inferInstanceAs (Group (Nonorientable g m))

/-- The peripheral (boundary) element `pⱼ` of `S±(g, m)`. -/
def peripheral : (o : Bool) → (g m : ℕ) → Fin m → Signed o g m
  | true, g, m, j => Orientable.peripheral g m j
  | false, g, m, j => Nonorientable.peripheral g m j

@[simp]
theorem peripheral_true (g m : ℕ) (j : Fin m) :
    peripheral true g m j = Orientable.peripheral g m j := (rfl)

@[simp]
theorem peripheral_false (g m : ℕ) (j : Fin m) :
    peripheral false g m j = Nonorientable.peripheral g m j := (rfl)

/-- The Euler characteristic of the surface of `S±(g, m)`: `2 - 2g - m` or `2 - g - m`. -/
def eulerChar : Bool → ℕ → ℕ → ℤ
  | true, g, m => Orientable.eulerChar g m
  | false, g, m => Nonorientable.eulerChar g m

@[simp]
theorem eulerChar_true (g m : ℕ) : eulerChar true g m = Orientable.eulerChar g m := (rfl)

@[simp]
theorem eulerChar_false (g m : ℕ) : eulerChar false g m = Nonorientable.eulerChar g m := (rfl)

variable {o : Bool} {g m : ℕ}

/-- The Euler characteristic of `S±(g, m)` is `2 - 2g - m` or `2 - g - m`, according as the
surface is orientable or not. -/
theorem eulerChar_def : eulerChar o g m = 2 - (if o then 2 else 1) * g - m := by
  cases o <;> simp [Orientable.eulerChar_def, Nonorientable.eulerChar_def]

/-- The fundamental group of a compact surface of negative Euler characteristic is not
abelian. -/
theorem not_isMulCommutative_of_eulerChar_neg (h : eulerChar o g m < 0) :
    ¬IsMulCommutative (Signed o g m) := by
  cases o
  · exact Nonorientable.not_isMulCommutative (.inr h)
  · exact Orientable.not_isMulCommutative_of_eulerChar_neg h

/-- The peripheral elements of `S±(g, m)` are nontrivial unless the surface is the disc. -/
theorem peripheral_ne_one (h : g ≠ 0 ∨ m ≠ 1) (j : Fin m) : peripheral o g m j ≠ 1 := by
  intro hj
  cases o
  · rw [peripheral_false] at hj
    exact Nonorientable.not_isOfFinOrder_peripheral h j (hj ▸ IsOfFinOrder.one)
  · rw [peripheral_true] at hj
    exact Orientable.not_isOfFinOrder_peripheral h j (hj ▸ IsOfFinOrder.one)

/-- The peripheral elements of a surface group of negative Euler characteristic are
nontrivial. -/
theorem peripheral_ne_one_of_eulerChar_neg (h : eulerChar o g m < 0) (j : Fin m) :
    peripheral o g m j ≠ 1 :=
  peripheral_ne_one (by rw [eulerChar_def] at h; split_ifs at h <;> lia) j

/-! ### Peripheral subgroups -/

/-- A subgroup of `S±(g, m)` is peripheral when it is trivial or contained in a conjugate of a
boundary subgroup `⟨pⱼ⟩`. -/
def IsPeripheral (K : Subgroup (Signed o g m)) : Prop :=
  K = ⊥ ∨ ∃ (j : Fin m) (s : Signed o g m),
    K ≤ (zpowers (peripheral o g m j)).map (MulAut.conj s).toMonoidHom

theorem isPeripheral_iff {K : Subgroup (Signed o g m)} :
    IsPeripheral K ↔ K = ⊥ ∨ ∃ (j : Fin m) (s : Signed o g m),
      K ≤ (zpowers (peripheral o g m j)).map (MulAut.conj s).toMonoidHom := Iff.rfl

@[simp]
theorem isPeripheral_bot : IsPeripheral (⊥ : Subgroup (Signed o g m)) := .inl rfl

/-- The boundary subgroup `⟨pⱼ⟩` is peripheral. -/
@[simp]
theorem isPeripheral_zpowers_peripheral (j : Fin m) :
    IsPeripheral (zpowers (peripheral o g m j)) := .inr ⟨j, 1, by simp⟩

/-- The boundary subgroup `⟨pⱼ⟩` of `S⁺(g, m)` is peripheral. -/
@[simp]
theorem isPeripheral_zpowers_orientable_peripheral (j : Fin m) :
    IsPeripheral (o := true) (zpowers (Orientable.peripheral g m j)) :=
  isPeripheral_zpowers_peripheral j

/-- The boundary subgroup `⟨pⱼ⟩` of `S⁻(g, m)` is peripheral. -/
@[simp]
theorem isPeripheral_zpowers_nonorientable_peripheral (j : Fin m) :
    IsPeripheral (o := false) (zpowers (Nonorientable.peripheral g m j)) :=
  isPeripheral_zpowers_peripheral j

/-- Without boundary, only the trivial subgroup is peripheral. -/
@[simp]
theorem isPeripheral_zero_iff {K : Subgroup (Signed o g 0)} : IsPeripheral K ↔ K = ⊥ := by
  simp [isPeripheral_iff]

/-- Subgroups of peripheral subgroups are peripheral. -/
theorem IsPeripheral.mono {K L : Subgroup (Signed o g m)} (hK : IsPeripheral K) (hLK : L ≤ K) :
    IsPeripheral L := by
  rcases hK with rfl | ⟨j, s, hK⟩
  · exact .inl (le_bot_iff.mp hLK)
  · exact .inr ⟨j, s, hLK.trans hK⟩

/-- Conjugates of peripheral subgroups are peripheral. -/
theorem IsPeripheral.map_conj {K : Subgroup (Signed o g m)} (hK : IsPeripheral K)
    (s : Signed o g m) : IsPeripheral (K.map (MulAut.conj s).toMonoidHom) := by
  rcases hK with rfl | ⟨j, t, hK⟩
  · exact .inl (map_bot _)
  · exact .inr ⟨j, s * t, map_conj_map_conj _ t s ▸ map_mono hK⟩

/-- A conjugate of a subgroup is peripheral exactly when the subgroup is. -/
@[simp]
theorem isPeripheral_map_conj_iff {K : Subgroup (Signed o g m)} {s : Signed o g m} :
    IsPeripheral (K.map (MulAut.conj s : Signed o g m →* Signed o g m)) ↔ IsPeripheral K := by
  refine ⟨fun hK => ?_, fun hK => hK.map_conj s⟩
  rw [← MulEquiv.toMonoidHom_eq_coe] at hK
  have := hK.map_conj s⁻¹
  rw [map_conj_map_conj, inv_mul_cancel] at this
  simpa [MulAut.one_def] using this

/-- Peripheral subgroups are abelian. -/
theorem IsPeripheral.isMulCommutative {K : Subgroup (Signed o g m)} (hK : IsPeripheral K) :
    IsMulCommutative K := by
  rcases hK with rfl | ⟨j, s, hK⟩
  · exact .of_setLike_mul_comm fun a ha b hb => by simp_all
  · exact .of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hK ha) (hK hb)

/-- The whole fundamental group of a compact surface of negative Euler characteristic is not
peripheral. -/
theorem not_isPeripheral_top (h : eulerChar o g m < 0) :
    ¬IsPeripheral (⊤ : Subgroup (Signed o g m)) := fun hp =>
  have := hp.isMulCommutative
  not_isMulCommutative_of_eulerChar_neg h topEquiv.surjective.isMulCommutative

end Signed

end SurfaceGroup

end TauCeti
