/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.Category

import Mathlib.RingTheory.Regular.LinearMap

/-!
# Splitting of the short exact sequence of a regular element

For a module `M` over a commutative ring `R` and an element `r` regular on `M`, the projection
`M ⟶ M ⧸ r M` in Mathlib's short exact sequence `0 ⟶ M ⟶ M ⟶ M ⧸ r M ⟶ 0`, with first map
multiplication by `r`, is a split epimorphism exactly when `r M = M`
(`IsSMulRegular.isSplitEpi_smulShortComplex_g_iff`).
-/

public section

universe v u

open CategoryTheory Limits Pointwise

namespace IsSMulRegular

variable {R : Type u} [CommRing R] {M : ModuleCat.{v} R} {r : R}

/-- If `r` is regular on `M`, the projection `M ⟶ M ⧸ r M` is a split epimorphism exactly when
`r M = M`. -/
theorem isSplitEpi_smulShortComplex_g_iff (hr : IsSMulRegular M r) :
    IsSplitEpi (M.smulShortComplex r).g ↔ r • (⊤ : Submodule R M) = ⊤ := by
  rw [← Submodule.Quotient.subsingleton_iff]
  refine ⟨fun _ ↦ ModuleCat.subsingleton_of_isZero (M := (M.smulShortComplex r).X₃) ?_,
    fun h ↦ ⟨⟨0, (@ModuleCat.isZero_of_subsingleton _ _ (M.smulShortComplex r).X₃ h).eq_of_src
      _ _⟩⟩⟩
  -- A section of `g` vanishes, as `r` kills `M ⧸ r M` and is regular on `M`.
  have hσ : section_ (M.smulShortComplex r).g = 0 := ModuleCat.hom_ext <|
    (hr.linearMap_subsingleton_of_mem_annihilator (QuotSMulTop.mem_annihilator M r)).elim _ _
  -- Hence the identity of `M ⧸ r M`, which factors through the section, vanishes.
  rw [IsZero.iff_id_eq_zero, ← IsSplitEpi.id (M.smulShortComplex r).g, hσ, zero_comp]

end IsSMulRegular
