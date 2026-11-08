/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.Prod

/-!
# Ideal-power torsion in a module of compatible pairs

For maps `f : M →ₗ[R] P` and `g : N →ₗ[R] P`, the kernel of `f.coprod (-g)` is the
module of pairs whose images agree. If `M` has no `I`-power torsion and `g` kills the
`I`-power torsion of `N`, projection to `N` identifies the torsion of this kernel with
that of `N`. In particular the latter hypothesis holds when `P` has no `I`-power torsion.

In formal glueing, `M` is the module of sections on the complementary open, `N` is the
prescribed module on the formal neighbourhood, and `P` consists of sections on their
overlap. The torsion identification is the input to injectivity of the scalar-extension
comparison from the compatible-pairs module. It does not assert that comparison is
surjective or that arbitrary glueing data have been reconstructed.

## References

* Stacks Project, Proposition 15.91.16 (05ER), the compatible-pairs construction.
-/

public section

namespace Ideal

variable {R M N P : Type*} [CommRing R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Projection from the module of compatible pairs identifies its `I`-power torsion with
that of the second factor, provided the first factor has no `I`-power torsion and the
second map kills `I`-power torsion. No finiteness assumption on the ideal or modules is needed. -/
theorem primaryComponent_map_snd_ker_coprod_bijective (I : Ideal R)
    (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (hM : I.primaryComponent M = ⊥) (hg : I.primaryComponent N ≤ LinearMap.ker g) :
    Function.Bijective (primaryComponent.map I
      ((LinearMap.snd R M N).comp (LinearMap.ker (f.coprod (-g))).subtype)) := by
  let K := LinearMap.ker (f.coprod (-g))
  have hfst (x : I.primaryComponent K) : (x.val.val).1 = 0 := by
    have hx := I.primaryComponent_map_mem ((LinearMap.fst R M N).comp K.subtype) x
    simpa only [hM, Submodule.mem_bot, LinearMap.comp_apply, LinearMap.fst_apply,
      Submodule.subtype_apply] using hx
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext ((hfst x).trans (hfst y).symm)
    exact congrArg Subtype.val hxy
  · intro y
    have hy : g y.val = 0 := hg y.property
    have hpair : (0, y.val) ∈ K := by
      simp [K, LinearMap.mem_ker, hy]
    have ht : (0, y.val) ∈ I.primaryComponent (M × N) :=
      I.primaryComponent_map_mem (LinearMap.inr R M N) y
    have hkt : (⟨(0, y.val), hpair⟩ : K) ∈ I.primaryComponent K := by
      rw [← I.primaryComponent_comap_subtype K]
      exact ht
    exact ⟨⟨⟨(0, y.val), hpair⟩, hkt⟩, Subtype.ext (by simp)⟩

end Ideal
