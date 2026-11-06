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

For linear maps `f : M → P` and `g : N → P`, the kernel of `f.coprod (-g)` is the
module of pairs `(m, n)` with `f m = g n`. If `M` and `P` have no `I`-power torsion,
projection onto `N` identifies its `I`-power torsion with that of `N`.

In formal module gluing, `M` is the module of sections on the complementary open,
`N` is the prescribed module on the formal neighbourhood, and `P` is the module
of sections on their overlap. The sections modules have no torsion supported on
the omitted closed subset. The theorem recovers the entire torsion of `N` inside
the compatible-pairs module.

We use Mathlib's existing kernel and `Ideal.primaryComponent.map`, rather than
introducing a separate carrier or torsion map.

## References

* The Stacks Project, Proposition 15.91.16 (Tag 05ER), the compatible-pairs
  construction and its torsion comparison.
-/

public section

namespace Ideal

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Projection from the module of compatible pairs onto its second factor is a
bijection on `I`-power torsion if the first factor and the overlap have no
`I`-power torsion. In particular, every torsion element of the second factor
has a unique compatible torsion lift, with first coordinate zero. -/
theorem primaryComponent_map_snd_ker_coprod_bijective (I : Ideal R)
    (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (hM : I.primaryComponent M = ⊥) (hP : I.primaryComponent P = ⊥) :
    Function.Bijective (Ideal.primaryComponent.map I
      ((LinearMap.snd R M N).comp (LinearMap.ker (f.coprod (-g))).subtype)) := by
  let K := LinearMap.ker (f.coprod (-g))
  let π : K →ₗ[R] N := (LinearMap.snd R M N).comp K.subtype
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun n ↦ ?_⟩
  · -- A torsion pair has first coordinate zero, so the second coordinate determines it.
    have hfst := I.primaryComponent_map_mem
      ((LinearMap.fst R M N).comp K.subtype) x
    rw [hM, Submodule.mem_bot] at hfst
    have hsnd : π x = 0 := by simpa [π] using congrArg Subtype.val hx
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hfst hsnd
  · -- Torsion vanishes on the overlap, so `(0, n)` is compatible.
    have hgn := I.primaryComponent_map_mem g n
    rw [hP, Submodule.mem_bot] at hgn
    let k : K := ⟨(0, n), by simp [K, hgn]⟩
    have hk : k ∈ I.primaryComponent K := by
      rw [← I.primaryComponent_comap_subtype K]
      exact I.primaryComponent_map_mem (LinearMap.inr R M N) n
    exact ⟨⟨k, hk⟩, Subtype.ext (by simp [k])⟩

end Ideal
