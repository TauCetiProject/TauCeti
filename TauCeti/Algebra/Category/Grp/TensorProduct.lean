/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Morphisms out of a tensor product of abelian groups

Two morphisms of `AddCommGrpCat` out of the tensor product `A ⊗[ℤ] B` of abelian groups agree if
they agree on pure tensors (`AddCommGrpCat.tensor_hom_ext`).

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Hodge/CupProduct.lean` (declaration `New.Variety.addCommGrp_tensor_hom_ext`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The lemma is adapted from this declaration.
-/

public section

open TensorProduct

universe w

namespace AddCommGrpCat

/-- Two homomorphisms out of a tensor product of abelian groups agree if they agree on pure
tensors. -/
lemma tensor_hom_ext {A B X : AddCommGrpCat.{w}} {f g : AddCommGrpCat.of (A ⊗[ℤ] B) ⟶ X}
    (h : ∀ (a : A) (b : B), f (a ⊗ₜ b) = g (a ⊗ₜ b)) : f = g :=
  AddCommGrpCat.hom_ext (AddMonoidHom.toIntLinearMap_injective (TensorProduct.ext' h))

end AddCommGrpCat
