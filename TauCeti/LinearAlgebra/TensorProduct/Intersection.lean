/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor products of submodules as intersections

Let `P ≤ M` and `Q ≤ N` be submodules. Inside `M ⊗[R] N` the image of `P ⊗[R] Q` is always
contained in both the image of `M ⊗[R] Q` and the image of `P ⊗[R] N`. Over a field the three
images satisfy

```text
P ⊗ Q = (M ⊗ Q) ∩ (P ⊗ N),
```

and the same holds over any commutative ring as soon as `M ⧸ P` is flat, or more generally
whenever `(M ⧸ P) ⊗[R] Q → (M ⧸ P) ⊗[R] N` is injective. This is the step that upgrades a
submodule of a coalgebra whose comultiplication lands in both one-sided tensor products to a
subcoalgebra.

## Main results

* `Submodule.range_map_subtype_subtype`: the image of `P ⊗[R] Q` in `M ⊗[R] N` is the
  intersection of the images of `M ⊗[R] Q` and `P ⊗[R] N`, when `(M ⧸ P) ⊗[R] Q → (M ⧸ P) ⊗[R] N`
  is injective, for instance when `M ⧸ P` is flat.

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

/-- If `(M ⧸ P) ⊗[R] Q → (M ⧸ P) ⊗[R] N` is injective, the image of `P ⊗[R] Q` in `M ⊗[R] N` is
the intersection of the images of `M ⊗[R] Q` and `P ⊗[R] N`. The injectivity holds for instance
when `M ⧸ P` is flat (so for all submodules over a field), or when `Q` is a direct summand of `N`.
-/
theorem range_map_subtype_subtype (P : Submodule R M) (Q : Submodule R N)
    (hPQ : Function.Injective (Q.subtype.lTensor (M ⧸ P))) :
    range (TensorProduct.map P.subtype Q.subtype) =
      range (Q.subtype.lTensor M) ⊓ range (P.subtype.rTensor N) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [← lTensor_comp_rTensor]
    exact range_comp_le_range _ _
  · rw [← rTensor_comp_lTensor]
    exact range_comp_le_range _ _
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  -- The image of `y` dies in `(M ⧸ P) ⊗ N`, hence by injectivity already in `(M ⧸ P) ⊗ Q`, so
  -- `y` comes from `P ⊗ Q` by right exactness.
  have hzero : Q.subtype.lTensor (M ⧸ P) (P.mkQ.rTensor Q y) = 0 := by
    rw [LinearMap.lTensor_rTensor_comm]
    exact (rTensor_exact N (exact_subtype_mkQ P) P.mkQ_surjective _).mpr hy
  obtain ⟨z, rfl⟩ := (rTensor_exact Q (exact_subtype_mkQ P) P.mkQ_surjective y).mp
    ((map_eq_zero_iff _ hPQ).mp hzero)
  exact ⟨z, by rw [← lTensor_comp_rTensor, comp_apply]⟩

end Submodule
