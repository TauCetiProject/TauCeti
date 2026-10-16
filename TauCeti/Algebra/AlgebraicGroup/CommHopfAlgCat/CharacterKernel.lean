/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# The common kernel of algebraic characters

The common kernel of all characters of an affine group is a normal closed subgroup scheme.
Its defining Hopf ideal is the kernel ideal of the canonical evaluation morphism from the
character group algebra. A point lies in this subgroup precisely when every character has
value one. The construction retains scheme-theoretic information over arbitrary base rings.

The formal construction uses `MonoidAlgebra.liftGroupLikeBialgHom` and
`TauCeti.CommHopfAlgCat.kernelHopfIdeal`.

## References

* A. Borel, *Linear Algebraic Groups*, §10.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 16.
-/

public section

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{max u v} R)

/-- The defining Hopf ideal of the intersection of the kernels of all algebraic characters. -/
noncomputable def characterKernelIdeal : HopfIdeal R H :=
  kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom
    (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)))

/-- The character kernel is the kernel of the evaluation morphism from the character group
algebra. -/
theorem characterKernelIdeal_def :
    characterKernelIdeal H = kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom
      (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H))) := (rfl)

/-- The common kernel of characters is a normal closed subgroup scheme. -/
theorem isNormal_characterKernelIdeal : (characterKernelIdeal H).IsNormal := by
  rw [characterKernelIdeal_def]
  exact isNormal_kernelHopfIdeal _

/-- Every character restricts to one on the character kernel. -/
@[simp]
theorem sub_one_mem_characterKernelIdeal (x : GroupLike R H) :
    (x : H) - 1 ∈ characterKernelIdeal H := by
  rw [characterKernelIdeal_def]
  have h := mem_kernelHopfIdeal_of_mem_augmentation
    (_root_.CommHopfAlgCat.ofHom
      (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)))
    (x := MonoidAlgebra.single x (1 : R) - 1) (by simp)
  simpa [map_sub, MonoidAlgebra.liftGroupLikeBialgHom_single] using h

/-- A coordinate map kills the character-kernel ideal exactly when all characters evaluate to
one. In particular this characterizes membership of points in the common kernel. -/
theorem characterKernelIdeal_toIdeal_le_ker_iff
    {A : Type w} [Ring A] [Algebra R A] (f : H →ₐ[R] A) :
    (characterKernelIdeal H).toIdeal ≤ RingHom.ker f.toRingHom ↔
      ∀ x : GroupLike R H, f x = 1 := by
  constructor
  · intro h x
    have hx := h (sub_one_mem_characterKernelIdeal H x)
    simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      map_sub, map_one, sub_eq_zero] using hx
  · intro h
    rw [characterKernelIdeal_def, kernelHopfIdeal_toIdeal_le_ker_iff]
    apply MonoidAlgebra.algHom_ext
    · intro x
      simpa [MonoidAlgebra.liftGroupLikeBialgHom_single] using h x
    · exact Subsingleton.elim _ _

/-- A closed subgroup lies in the common kernel of characters precisely when every character
restricts to one on it. -/
theorem characterKernelIdeal_le_iff (I : HopfIdeal R H) :
    characterKernelIdeal H ≤ I ↔ ∀ x : GroupLike R H, (x : H) - 1 ∈ I := by
  rw [← HopfIdeal.toIdeal_le_toIdeal,
    ← mkQuotient_ker H I, characterKernelIdeal_toIdeal_le_ker_iff]
  apply forall_congr'
  intro x
  simpa only [map_sub, map_one, sub_eq_zero, BialgHom.coe_toAlgHom] using
    (mkQuotient_eq_zero_iff H I ((x : H) - 1))

end CommHopfAlgCat
