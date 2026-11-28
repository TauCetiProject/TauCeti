/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Periods of class functions

The right-translation stabilizer of a class function is normal. Its quotient is the smallest
quotient group on which the function can be read: a class function comes by pullback along a
surjective homomorphism precisely when the kernel consists of periods.
-/

public section

namespace TauCeti.ClassFunction

variable {k G H : Type*} [Semiring k] [Group G] [Group H]

/-- The periods of a class function form a normal subgroup. -/
instance instNormalRightTranslationStabilizer (f : ClassFunction k G) :
    (rightTranslationStabilizer f.val).Normal where
  conj_mem n hn g := by
    apply mem_rightTranslationStabilizer.mpr
    intro x
    calc f.val (x * (g * n * g⁻¹)) = f.val ((g⁻¹ * x * g) * n) := by
          simpa only [mul_assoc] using apply_mul_comm f (x * g * n) g⁻¹
      _ = f.val (g⁻¹ * x * g) := mem_rightTranslationStabilizer.mp hn _
      _ = f.val x := by simpa using apply_conj f g⁻¹ x

/-- Descent of class functions along a surjective homomorphism is equivalent to periodicity
under its kernel. -/
theorem mem_range_comap_iff (f : ClassFunction k G) {π : G →* H} (hπ : Function.Surjective π) :
    f ∈ LinearMap.range (comap π) ↔ π.ker ≤ rightTranslationStabilizer f.val := by
  constructor
  · rintro ⟨a, rfl⟩ n hn
    exact mem_rightTranslationStabilizer.mpr fun x ↦ by simp [MonoidHom.mem_ker.mp hn]
  · intro h
    obtain ⟨a, ha⟩ := (Function.factorsThrough_iff (f := ⇑π) f.val).mp fun x y hxy ↦ by
      have hmem : x⁻¹ * y ∈ π.ker := by simp [MonoidHom.mem_ker, hxy]
      simpa using (mem_rightTranslationStabilizer.mp (h hmem) x).symm
    have heval (x : G) : a (π x) = f.val x := congrFun ha.symm x
    refine ⟨⟨a, mem_iff.mpr (hπ.forall.mpr fun x ↦ hπ.forall.mpr fun y ↦ ?_)⟩, ?_⟩
    · rw [← map_inv, ← map_mul, ← map_mul, heval, heval, apply_conj]
    · exact Subtype.ext (funext fun x ↦ (comap_apply ..).trans (heval x))

/-- If a class function and its left translate by `c` have constant sum, the image of `c`
is central in the quotient by its periods. -/
theorem mk_mem_center_quotient_rightTranslationStabilizer [IsLeftCancelAdd k]
    (f : ClassFunction k G) {c : G} (h : ∀ x, f.val x + f.val (c * x) = f.val 1 + f.val c) :
    (c : G ⧸ rightTranslationStabilizer f.val) ∈ Subgroup.center _ := by
  have hswap (t g : G) : f.val (t * (g * c)) = f.val (t * (c * g)) := by
    apply add_left_cancel (a := f.val (t * g))
    calc f.val (t * g) + f.val (t * (g * c)) = f.val 1 + f.val c := by
           rw [← mul_assoc, apply_mul_comm f (t * g) c, h]
      _ = f.val (t * g) + f.val (t * (c * g)) := by
           rw [← h (g * t), apply_mul_comm f g t,
             ← mul_assoc c g t, apply_mul_comm f (c * g) t]
  refine Subgroup.mem_center_iff.mpr (QuotientGroup.mk_surjective.forall.mpr fun g ↦ ?_)
  apply QuotientGroup.eq.mpr
  exact mem_rightTranslationStabilizer.mpr fun x ↦ by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      (hswap (x * (g * c)⁻¹) g).symm

end TauCeti.ClassFunction
