/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Associator

/-!
# Total degree and balanced reassociation

The balanced associator preserves total degree for a right `B`-module, a `(B,C)`-bimodule,
and a left `C`-module. Neither endpoint needs a second action. Consequently reassociation
restricts to each homogeneous piece, as required for tensor composition of DG modules.

The carrier map is `BalancedTensorProduct.assoc`; no new associator is constructed here.
The grading convention follows B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

namespace TauCeti.BalancedTensorProduct

variable {R B C M N P : Type*} [CommRing R] [Semiring B] [Semiring C]
  [Module R B] [Module R C]
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module B N] [Module Cᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module C P]
  [SMulCommClass B R N] [SMulCommClass Cᵐᵒᵖ R N] [SMulCommClass B Cᵐᵒᵖ N]
  {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [DirectSum.Decomposition ℬ] [DirectSum.Decomposition 𝒞]
  (G : InternalGrading R M) (H : InternalGrading R N) (I : InternalGrading R P)
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece G.piece]
  [SetLike.GradedSMul ℬ H.piece]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece H.piece]
  [SetLike.GradedSMul 𝒞 I.piece]

attribute [local instance 100] leftModule rightModule

attribute [local instance] gradedSMul_left gradedSMul_right

local notation "GL" => grading (𝒜 := 𝒞) (grading (𝒜 := ℬ) G H) I
local notation "GR" => grading (𝒜 := ℬ) G (grading (𝒜 := 𝒞) H I)

/-- Balanced reassociation preserves the sum of the three input degrees. -/
theorem isHomogeneous_assoc :
    LinearMap.IsHomogeneous (assoc (k := R) (B := B) (C := C) (M := M) (N := N)
      (P := P)).toLinearMap (GL).piece (GR).piece 0 := by
  apply isHomogeneous_of_tmul (𝒜 := 𝒞) (grading (𝒜 := ℬ) G H) I
  intro p q x y hx hy
  let f : BalancedTensorProduct R B M N →ₗ[R] BalancedTensorProduct R B M
      (BalancedTensorProduct R C N P) := assoc.toLinearMap ∘ₗ (mk R C).flip y
  -- Fixing the last factor gives a map of degree q on the inner balanced tensor product.
  have h : f x ∈ (GR).piece (p + q) :=
    map_mem_of_tmul (𝒜 := ℬ) G H (GR).piece f q (fun hm hn ↦ by
      simp only [f, LinearMap.comp_apply, LinearMap.flip_apply, mk_apply,
        LinearEquiv.coe_coe, assoc_tmul]
      simpa only [add_assoc] using tmul_mem_grading (𝒜 := ℬ) G (grading (𝒜 := 𝒞) H I) hm
        (tmul_mem_grading (𝒜 := 𝒞) H I hn hy)) hx
  simpa only [f, LinearMap.comp_apply, LinearMap.flip_apply, mk_apply,
    LinearEquiv.coe_coe, add_zero] using h

/-- The inverse balanced associator also preserves total degree. -/
theorem isHomogeneous_assoc_symm :
    LinearMap.IsHomogeneous (assoc (k := R) (B := B) (C := C) (M := M) (N := N)
      (P := P)).symm.toLinearMap (GR).piece (GL).piece 0 := by
  simpa only [neg_zero] using (isHomogeneous_assoc G H I).linearEquiv_symm

/-- Reassociation maps each total-degree piece onto the piece of the same degree.
This is not a simp lemma, since `grading_piece` already rewrites its left-hand side. -/
theorem map_assoc_grading_piece (p : ℤ) :
    ((GL).piece p).map assoc.toLinearMap = (GR).piece p := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr fun x hx ↦ by
      simpa only [add_zero, Submodule.mem_comap, LinearEquiv.coe_coe] using
        (isHomogeneous_assoc G H I).map_mem hx
  · intro x hx
    refine ⟨assoc.symm x, ?_, LinearEquiv.apply_symm_apply _ x⟩
    simpa only [add_zero, LinearEquiv.coe_coe, SetLike.mem_coe] using
      (isHomogeneous_assoc_symm G H I).map_mem hx

end TauCeti.BalancedTensorProduct
