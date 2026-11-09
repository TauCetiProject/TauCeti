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

If the kernel of a nonzero integer-valued character is contained in the kernel of another,
some nonzero integer multiple of the latter is a multiple of the former. Equal kernels
therefore give equal nonzero integer multiples. These facts compare integral normals without
choosing a basis or extending scalars to a field.

## Attribution

The two kernel comparison theorems are adapted from
`Mei/Algebra/Group/Hom/Int.lean` in Mei at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Algebra/Group/Hom/Int.lean
-/

public section

namespace AddMonoidHom

variable {A : Type*} [AddGroup A]

/-- If the kernel of an integer character is contained in that of another,
then a nonzero integer multiple of the latter is a multiple of the former.
The second character is allowed to be zero. -/
theorem exists_ne_zero_zsmul_eq_of_ker_le (f g : A →+ ℤ) (hf : f ≠ 0)
    (hker : f.ker ≤ g.ker) :
    ∃ c d : ℤ, c ≠ 0 ∧ c • g = d • f := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  refine ⟨f a, g a, ha, ?_⟩
  ext x
  have hx : f a • x - f x • a ∈ f.ker := by
    simp [AddMonoidHom.mem_ker, mul_comm]
  have hg := AddMonoidHom.mem_ker.mp (hker hx)
  simpa only [map_sub, map_zsmul, AddMonoidHom.zsmul_apply, Int.zsmul_eq_mul,
    sub_eq_zero, mul_comm (f x)] using hg

/-- Nonzero integer characters with the same kernel have equal nonzero integer multiples. -/
theorem exists_ne_zero_zsmul_eq_of_ker_eq (f g : A →+ ℤ) (hf : f ≠ 0)
    (hker : f.ker = g.ker) :
    ∃ c e : ℤ, c ≠ 0 ∧ e ≠ 0 ∧ c • f = e • g := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hf
  have hga : g a ≠ 0 := by
    intro h
    have hm : a ∈ f.ker := hker ▸ AddMonoidHom.mem_ker.mpr h
    exact ha (AddMonoidHom.mem_ker.mp hm)
  obtain ⟨c, d, hc, hcd⟩ := f.exists_ne_zero_zsmul_eq_of_ker_le g hf hker.le
  have hd : d ≠ 0 := by
    intro hd
    have hv : c * g a = 0 := by simpa [hd] using DFunLike.congr_fun hcd a
    exact hga ((Int.mul_eq_zero.mp hv).resolve_left hc)
  exact ⟨d, c, hd, hc, hcd.symm⟩

end AddMonoidHom
