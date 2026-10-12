/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products of submodules as intersections

Let `P ≤ M` and `Q ≤ N` be submodules. Inside `M ⊗[R] N` the image of `P ⊗[R] Q` is always
contained in both the image of `M ⊗[R] Q` and the image of `P ⊗[R] N`. Over a field the three
images satisfy

```text
P ⊗ Q = (M ⊗ Q) ∩ (P ⊗ N),
```

and the same holds over any commutative ring as soon as `M ⧸ P` is flat. This is the step that
upgrades a submodule of a coalgebra whose comultiplication lands in both one-sided tensor
products to a subcoalgebra.

## Main results

* `Submodule.range_map_subtype_subtype`: the image of `P ⊗[R] Q` in `M ⊗[R] N` is the
  intersection of the images of `M ⊗[R] Q` and `P ⊗[R] N`, when `M ⧸ P` is flat.

## References

* [N. Bourbaki, *Algebra I, Chapters 1-3*][bourbaki1989], Chapter II, §3, n°7, for the
  corresponding statement for vector spaces.
-/

public section

open TensorProduct LinearMap

namespace Submodule

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If `M ⧸ P` is flat, the image of `P ⊗[R] Q` in `M ⊗[R] N` is the intersection of the images
of `M ⊗[R] Q` and `P ⊗[R] N`. Over a field this holds for all submodules `P` and `Q`. -/
theorem range_map_subtype_subtype (P : Submodule R M) (Q : Submodule R N)
    [Module.Flat R (M ⧸ P)] :
    range (TensorProduct.map P.subtype Q.subtype) =
      range (Q.subtype.lTensor M) ⊓ range (P.subtype.rTensor N) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [← lTensor_comp_rTensor]
    exact range_comp_le_range _ _
  · rw [← rTensor_comp_lTensor]
    exact range_comp_le_range _ _
  rintro x ⟨⟨y, rfl⟩, hx⟩
  -- `x` dies in `(M ⧸ P) ⊗ N`, hence so does the image of `y` in `(M ⧸ P) ⊗ Q`; by flatness
  -- the latter image already vanishes, so `y` comes from `P ⊗ Q`.
  have hPN : Function.Exact (P.subtype.rTensor N) (P.mkQ.rTensor N) :=
    rTensor_exact N (exact_subtype_mkQ P) P.mkQ_surjective
  have hPQ : Function.Exact (P.subtype.rTensor Q) (P.mkQ.rTensor Q) :=
    rTensor_exact Q (exact_subtype_mkQ P) P.mkQ_surjective
  have hzero : Q.subtype.lTensor (M ⧸ P) (P.mkQ.rTensor Q y) = 0 := by
    have hcomm := LinearMap.congr_fun
      ((lTensor_comp_rTensor (f := P.mkQ) (g := Q.subtype)).trans
        (rTensor_comp_lTensor (f := P.mkQ) (g := Q.subtype)).symm) y
    rw [comp_apply, comp_apply] at hcomm
    rw [hcomm]
    exact (hPN _).mpr (mem_range.mp hx)
  obtain ⟨z, rfl⟩ := (hPQ y).mp
    (Module.Flat.lTensor_preserves_injective_linearMap Q.subtype Q.injective_subtype
      (hzero.trans (map_zero _).symm))
  exact ⟨z, by rw [← lTensor_comp_rTensor, comp_apply]⟩

end Submodule
