/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Splitting off the span of a finite orthonormal family

For a finite orthonormal family `v : ι → E` in an inner product space, every vector `u` is
`∑ i, ⟪v i, u⟫ • v i` plus a vector orthogonal to the family, and the coefficients and the
orthogonal part are determined by `u`. So `(c, w) ↦ ∑ i, c i • v i + w` is an isomorphism of
topological vector spaces `(ι → 𝕜) × (span 𝕜 (range v))ᗮ ≃L[𝕜] E`
(`Orthonormal.prodOrthogonalEquiv`), with inverse
`u ↦ (fun i ↦ ⟪v i, u⟫, u - ∑ i, ⟪v i, u⟫ • v i)`.

## Main definitions and results

* `Submodule.mem_orthogonal_span_range_iff`: a vector is orthogonal to the span of a family iff it
  is orthogonal to every member.
* `Orthonormal.prodOrthogonalEquiv`: the isomorphism `(ι → 𝕜) × (span 𝕜 (range v))ᗮ ≃L[𝕜] E`,
  with `Orthonormal.prodOrthogonalEquiv_apply` and `Orthonormal.prodOrthogonalEquiv_symm_apply`.
-/

public section

noncomputable section

open Set Submodule
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
  {v : ι → E}

omit [Fintype ι] in
/-- A vector is orthogonal to the span of a family iff it is orthogonal to every member of the
family. -/
theorem Submodule.mem_orthogonal_span_range_iff {w : E} :
    w ∈ (span 𝕜 (range v))ᗮ ↔ ∀ i, ⟪v i, w⟫_𝕜 = 0 :=
  (mem_orthogonalBilin_span (B := innerₛₗ 𝕜)).trans forall_mem_range

namespace Orthonormal

/-- Removing from `u` its components along an orthonormal family leaves a vector orthogonal to
the family. -/
theorem sub_sum_inner_smul_mem_orthogonal (hv : Orthonormal 𝕜 v) (u : E) :
    u - ∑ i, ⟪v i, u⟫_𝕜 • v i ∈ (span 𝕜 (range v))ᗮ :=
  Submodule.mem_orthogonal_span_range_iff.2 fun i ↦ by
    rw [inner_sub_right, hv.inner_right_fintype, sub_self]

/-- **Splitting off the span of a finite orthonormal family.** For a finite orthonormal family
`v`, the map `(c, w) ↦ ∑ i, c i • v i + w` is an isomorphism of topological vector spaces from
`(ι → 𝕜) × (span 𝕜 (range v))ᗮ` onto `E`. Its inverse sends `u` to its coefficients `⟪v i, u⟫`
and to `u - ∑ i, ⟪v i, u⟫ • v i`. -/
def prodOrthogonalEquiv (hv : Orthonormal 𝕜 v) :
    ((ι → 𝕜) × (span 𝕜 (range v))ᗮ) ≃L[𝕜] E :=
  { toLinearEquiv :=
    { toFun := fun p ↦ ∑ i, p.1 i • v i + (p.2 : E)
      map_add' := fun p q ↦ by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
          Submodule.coe_add]
        abel
      map_smul' := fun c p ↦ by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, Submodule.coe_smul, RingHom.id_apply, smul_add]
      invFun := fun u ↦ (fun i ↦ ⟪v i, u⟫_𝕜, ⟨_, hv.sub_sum_inner_smul_mem_orthogonal u⟩)
      left_inv := fun p ↦ by
        have hc (j : ι) : ⟪v j, ∑ i, p.1 i • v i + (p.2 : E)⟫_𝕜 = p.1 j := by
          rw [inner_add_right, hv.inner_right_fintype,
            Submodule.mem_orthogonal_span_range_iff.1 p.2.property j, add_zero]
        refine Prod.ext (funext hc) (Subtype.ext ?_)
        simp only [hc, add_sub_cancel_left]
      right_inv := fun u ↦ add_sub_cancel _ _ }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- `Orthonormal.prodOrthogonalEquiv` sends `(c, w)` to `∑ i, c i • v i + w`. -/
@[simp]
theorem prodOrthogonalEquiv_apply (hv : Orthonormal 𝕜 v)
    (p : (ι → 𝕜) × (span 𝕜 (range v))ᗮ) :
    hv.prodOrthogonalEquiv p = ∑ i, p.1 i • v i + (p.2 : E) := by
  rfl

/-- The inverse of `Orthonormal.prodOrthogonalEquiv` sends `u` to its coefficients `⟪v i, u⟫`
and to `u - ∑ i, ⟪v i, u⟫ • v i`. -/
@[simp]
theorem prodOrthogonalEquiv_symm_apply (hv : Orthonormal 𝕜 v) (u : E) :
    hv.prodOrthogonalEquiv.symm u =
      (fun i ↦ ⟪v i, u⟫_𝕜, ⟨_, hv.sub_sum_inner_smul_mem_orthogonal u⟩) := by
  rfl

end Orthonormal
