/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair

/-!
# Proper homomorphisms with finite kernel

A proper homomorphism of group schemes is finite if its scheme-theoretic kernel is finite
over the base. The kernel pair identifies with the product of the kernel and the source.
In particular, over a point in the image, a fibre is covered by the fibre of the second
projection of this product at any chosen point above it.

## References

* J. S. Milne, *Abelian Varieties*, §8, Proposition 8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace CategoryTheory.Grp

/-- A proper homomorphism of group schemes is finite exactly when its scheme-theoretic kernel
is finite over the base. -/
theorem isFinite_iff_isFinite_kernel {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
    [IsProper f.hom.hom.left] : IsFinite f.hom.hom.left ↔ IsFinite (kernel f).X.hom := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  let i : (kernel f).X ⟶ G.X := (kernel.ι f).hom.hom
  let q := snd (kernel f).X G.X
  let p := (fst (kernel f).X G.X ≫ i) * q
  have h : IsPullback p.left q.left f.hom.hom.left f.hom.hom.left :=
    (TauCeti.isPullback_mul_of_isPullback_one f.hom.hom i
      (TauCeti.GroupScheme.isPullback_kernel_hom f)).map (Over.forget S)
  have hq : IsFinite q.left := by
    dsimp only [q, Over.snd_left]
    infer_instance
  have : LocallyQuasiFinite f.hom.hom.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    by_cases hy : y ∈ Set.range f.hom.hom.left
    · obtain ⟨x, rfl⟩ := hy
      have hpreimage := Scheme.image_preimage_eq_of_isPullback h.flip {x}
      rw [Set.image_singleton] at hpreimage
      rw [← hpreimage]
      exact (q.left.finite_preimage_singleton x).image p.left
    · simp [Set.preimage_singleton_eq_empty.mpr hy]
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end CategoryTheory.Grp
