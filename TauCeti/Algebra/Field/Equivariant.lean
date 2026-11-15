/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Equivariant additive maps from division rings to fields

Let `a` and `b` be families of units in a division ring and a field, indexed by the same type.
If `a` is surjective, a nonzero additive map intertwining the corresponding scalar
multiplications is a scalar multiple of a unique field homomorphism. The scalar is its value
at one, and the field homomorphism carries `a` to `b`.

This is the scalar-rigidity argument for maps between root subgroups normalized by a split
torus: the pinning equation gives equivariance, and a nontrivial root character over an
algebraically closed field is surjective. No continuity or algebraicity of the additive map
is assumed.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
-/

public section

namespace AddMonoidHom

variable {K L T : Type*} [DivisionRing K] [Field L]

/-- A nonzero additive map intertwining two scalar families, with surjective source family,
is its value at one times a unique field homomorphism. That homomorphism intertwines the two
families. The source may be a division ring, the target need not be algebraically closed,
and no multiplicativity of the scalar families is assumed. -/
theorem existsUnique_ringHom_of_equivariant (f : K →+ L) {a : T → Kˣ} {b : T → Lˣ}
    (ha : Function.Surjective a) (hf : f ≠ 0)
    (heq : ∀ t x, f ((a t : K) * x) = (b t : L) * f x) :
    ∃! g : K →+* L, (∀ x, f x = f 1 * g x) ∧ ∀ t, g (a t : K) = (b t : L) := by
  have hf1 : f 1 ≠ 0 := by
    intro h
    apply hf
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨t, ht⟩ := ha (Units.mk0 x hx)
      have hx' := heq t 1
      simpa [ht, h] using hx'
  have hmul (x y : K) : f (x * y) * f 1 = f x * f y := by
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨t, ht⟩ := ha (Units.mk0 x hx)
      have hxy : f (x * y) = (b t : L) * f y := by simpa [ht] using heq t y
      have hx1 : f x = (b t : L) * f 1 := by simpa [ht] using heq t 1
      rw [hxy, hx1]
      ac_rfl
  let g : K →+* L :=
    { toFun := fun x => f x / f 1
      map_zero' := by simp
      map_one' := div_self hf1
      map_add' := fun x y => by simp [add_div]
      map_mul' := fun x y => by
        rw [div_mul_div_comm]
        apply (div_eq_div_iff hf1 (mul_ne_zero hf1 hf1)).2
        rw [← mul_assoc, hmul] }
  have hfg (x : K) : f x = f 1 * g x := by
    exact (mul_div_cancel₀ (f x) hf1).symm
  refine ⟨g, ⟨hfg, fun t => ?_⟩, fun g' hg' => ?_⟩
  · apply mul_left_cancel₀ hf1
    rw [← hfg]
    simpa [mul_comm] using heq t 1
  · ext x
    exact mul_left_cancel₀ hf1 ((hg'.1 x).symm.trans (hfg x))

end AddMonoidHom
