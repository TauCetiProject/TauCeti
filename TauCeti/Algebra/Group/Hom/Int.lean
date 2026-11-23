/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Integer characters with comparable kernels

If the kernel of an integer-valued character is contained in the kernel of another,
some nonzero integer multiple of the latter is a multiple of the former. Equal kernels
therefore give equal nonzero integer multiples. These facts compare integral normals without
choosing a basis or extending scalars to a field.

If a vector lies outside the common kernel of two characters, any character vanishing
on that kernel and at the vector also vanishes on the kernel of their contraction.

## Attribution

The two kernel comparison theorems are adapted from
`Mei/Algebra/Group/Hom/Int.lean` in Mei at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Algebra/Group/Hom/Int.lean

The contraction lemma is adapted from the same file at commit
`bf3986029ff4d3eb4025d4067489511b0724374e`.
-/

public section

namespace AddMonoidHom

variable {A : Type*} [AddGroup A]

private theorem pivot_mem_ker_iff (f g : A →+ ℤ) (v x : A) :
    f v • x - f x • v ∈ g.ker ↔ f v * g x = g v * f x := by
  rw [AddMonoidHom.sub_mem_ker_iff, map_zsmul, map_zsmul, Int.zsmul_eq_mul,
    Int.zsmul_eq_mul, mul_comm (f x) (g v)]

/-- If the kernel of an integer character is contained in that of another,
then a nonzero integer multiple of the latter is a multiple of the former.
Either character is allowed to be zero. -/
theorem exists_ne_zero_zsmul_eq_of_ker_le (f g : A →+ ℤ)
    (hker : f.ker ≤ g.ker) :
    ∃ c d : ℤ, c ≠ 0 ∧ c • g = d • f := by
  by_cases hf : f = 0
  · refine ⟨1, 0, Int.one_ne_zero, ?_⟩
    have hg : g = 0 := AddMonoidHom.ker_eq_top_iff.mp (top_unique (by simpa [hf] using hker))
    simp [hg]
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  refine ⟨f a, g a, ha, ?_⟩
  ext x
  have hx : f a • x - f x • a ∈ f.ker := (pivot_mem_ker_iff f f a x).mpr rfl
  simpa only [zsmul_apply, Int.zsmul_eq_mul] using (pivot_mem_ker_iff f g a x).mp (hker hx)

/-- Integer characters with the same kernel have equal nonzero integer multiples. -/
theorem exists_ne_zero_zsmul_eq_of_ker_eq (f g : A →+ ℤ)
    (hker : f.ker = g.ker) :
    ∃ c e : ℤ, c ≠ 0 ∧ e ≠ 0 ∧ c • f = e • g := by
  by_cases hf : f = 0
  · have hg : g = 0 := AddMonoidHom.ker_eq_top_iff.mp (by rw [← hker, hf]; simp)
    exact ⟨1, 1, Int.one_ne_zero, Int.one_ne_zero, by simp [hf, hg]⟩
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  have hga : g a ≠ 0 := by
    intro h
    have hm : a ∈ f.ker := hker ▸ AddMonoidHom.mem_ker.mpr h
    exact ha (AddMonoidHom.mem_ker.mp hm)
  obtain ⟨c, d, hc, hcd⟩ := f.exists_ne_zero_zsmul_eq_of_ker_le g hker.le
  have hd : d ≠ 0 := by
    intro hd
    have hv : c * g a = 0 := by simpa [hd] using DFunLike.congr_fun hcd a
    exact hga ((Int.mul_eq_zero.mp hv).resolve_left hc)
  exact ⟨d, c, hd, hc, hcd.symm⟩

/-- A character vanishing on the common kernel of two characters and at a vector
outside it also vanishes on the kernel of their contraction at that vector. -/
theorem ker_zsmul_sub_zsmul_le_of_inf_ker_le (f g m : A →+ ℤ) (v : A)
    (hv : v ∉ f.ker ⊓ g.ker) (hm : f.ker ⊓ g.ker ≤ m.ker) (hmv : m v = 0) :
    (f v • g - g v • f).ker ≤ m.ker := by
  have step (f g : A →+ ℤ) (hf : f v ≠ 0) (hm : f.ker ⊓ g.ker ≤ m.ker) :
      (f v • g - g v • f).ker ≤ m.ker := by
    intro x hx
    have hx' : f v * g x = g v * f x := by
      simpa only [mem_ker, sub_apply, zsmul_apply, Int.zsmul_eq_mul, sub_eq_zero] using hx
    have hz : f v • x - f x • v ∈ f.ker ⊓ g.ker :=
      AddSubgroup.mem_inf.mpr
        ⟨(pivot_mem_ker_iff f f v x).mpr rfl, (pivot_mem_ker_iff f g v x).mpr hx'⟩
    have hprod : f v * m x = 0 := by
      simpa [hmv] using AddMonoidHom.mem_ker.mp (hm hz)
    exact AddMonoidHom.mem_ker.mpr ((Int.mul_eq_zero.mp hprod).resolve_left hf)
  by_cases hf : f v = 0
  · have hg : g v ≠ 0 := fun hg =>
      hv (AddSubgroup.mem_inf.mpr ⟨AddMonoidHom.mem_ker.mpr hf, AddMonoidHom.mem_ker.mpr hg⟩)
    intro x hx
    apply step g f hg (by simpa only [inf_comm] using hm)
    rw [← neg_sub, mem_ker, neg_apply, neg_eq_zero]
    exact mem_ker.mp hx
  · exact step f g hf hm

end AddMonoidHom
