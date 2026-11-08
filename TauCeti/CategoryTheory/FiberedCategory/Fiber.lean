/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Isomorphisms in fibers

The inclusion of a fiber reflects isomorphisms: an inverse to a vertical isomorphism
is again vertical. This lets invertibility be checked in the ambient category while
retaining the specified base object. The inverse uses Mathlib's `IsHomLift` API.

Adapted from `Mei/CategoryTheory/FiberedCategory/Fiber.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

namespace CategoryTheory.Functor.Fiber

variable {C D : Type*} [Category* C] [Category* D] {p : C ⥤ D} {d : D}

/-- The inclusion of a fiber reflects isomorphisms. -/
instance : (fiberInclusion : Fiber p d ⥤ C).ReflectsIsomorphisms where
  reflects {a b} f hf := by
    have : IsIso f.val := hf
    have : p.IsHomLift (𝟙 d) f.val := f.property
    exact ⟨⟨⟨CategoryTheory.inv f.val, inferInstance⟩,
      Subtype.ext (IsIso.hom_inv_id f.val), Subtype.ext (IsIso.inv_hom_id f.val)⟩⟩

end CategoryTheory.Functor.Fiber
