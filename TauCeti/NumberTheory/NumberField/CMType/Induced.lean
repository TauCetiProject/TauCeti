/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.ComplexExtension

/-!
# Infinite-place representatives in an induced CM type

When the base has one infinite place, the representative in the induced CM type is the
extension of the chosen base embedding at that place. This lets the relative norm formula
indexed by infinite places be used with the representatives of the induced CM type.
-/

public section

open NumberField

namespace TauCeti.CMType

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Subsingleton (InfinitePlace K)]

/-- For an induced CM type, the representative at `w` is the unique embedding at `w`
extending the selected base embedding, when the base has only one infinite place. -/
theorem embedding_induced (Φ : CMType K) {σ : K →+* ℂ} (hσ : σ ∈ Φ) (w : InfinitePlace L) :
    (Φ.induced (algebraMap K L)).embedding w =
      ((ComplexEmbedding.Extension.equivInfinitePlace
        (fun h ↦ Φ.ringHom_star_ne_self σ (ComplexEmbedding.isReal_iff.mp h))).symm w).val := by
  apply ((Φ.induced (algebraMap K L)).embedding_eq_iff).mpr
  constructor
  · rw [mem_induced, ComplexEmbedding.Extension.comp_eq]
    exact hσ
  · exact ComplexEmbedding.Extension.mk_equivInfinitePlace_symm_apply _ w

end TauCeti.CMType
