/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Projective
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# The conjugation representation of `PU(p, q)` is a closed embedding

Over `ℝ` or `ℂ` (any `RCLike` field `𝕜`), the conjugation representation
`Ad : PU(p, q) → Aut(M_{p ⊕ q}(𝕜))`, `[g] ↦ (X ↦ g X g⁻¹)`
(`TauCeti.Matrix.ProjectiveIndefiniteUnitaryGroup.innerAut`), is a closed embedding of the
projective indefinite unitary group, with its quotient topology, into the space of maps of the
matrix algebra to itself with the topology of pointwise convergence. On the finite-dimensional
space of linear maps of the matrix algebra this is the usual topology, so `Ad` is a continuous
injective homomorphism with closed image, and a homeomorphism onto that image.

The proof shows that conjugation is already a proper map on `U(p, q)`. For `g ∈ U(p, q)` the
inverse is `J gᴴ J` with `J = diag(1, …, 1, -1, …, -1)`, so the diagonal entry at `a` of
`g E_bb g⁻¹`, for the matrix unit `E_bb`, is `± ‖g_ab‖²`. A family of conjugations converging
pointwise therefore has bounded matrix entries, and the bounded subsets of the closed subset
`U(p, q)` of the matrices are compact. Properness passes to the quotient by the centre because
the quotient map is continuous and surjective.

As a consequence `PU(p, q)` is Hausdorff. With the local compactness and second countability of
`U(p, q)` (from `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup`), which pass to quotient groups,
this makes `PU(p, q)` a Hausdorff, locally compact, second-countable topological group, so it
carries Haar measures.

## Main results

* `TauCeti.Matrix.indefiniteUnitaryGroup.norm_innerAut_single_apply_self`: the diagonal entry at
  `a` of `g E_bb g⁻¹` has norm `‖g_ab‖²`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.isProperMap_innerAut`: conjugation by elements of
  `U(p, q)` is a proper map to the space of maps of the matrix algebra.
* `TauCeti.Matrix.ProjectiveIndefiniteUnitaryGroup.isClosedEmbedding_innerAut`: the conjugation
  representation of `PU(p, q)` is a closed embedding.
* `TauCeti.Matrix.ProjectiveIndefiniteUnitaryGroup.instT2Space`: `PU(p, q)` is Hausdorff.

## References

* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. 197 (2023), Section 2, for `PU(1, n)` and its topology.
-/

public section

open Filter Matrix Topology

namespace TauCeti

namespace Matrix

variable {p q 𝕜 : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [RCLike 𝕜]

namespace indefiniteUnitaryGroup

/-- **Matrix entries of `g ∈ U(p, q)` from its conjugation.** The diagonal entry at `a` of
`g E_bb g⁻¹`, for the matrix unit `E_bb`, is `g_ab (g⁻¹)_ba = J_bb J_aa ‖g_ab‖²`, because
`g⁻¹ = J gᴴ J`; its norm is `‖g_ab‖²`. -/
theorem norm_innerAut_single_apply_self (g : indefiniteUnitaryGroup p q 𝕜) (a b : p ⊕ q) :
    ‖GeneralLinearGroup.innerAut (g : GL (p ⊕ q) 𝕜) (single b b 1) a a‖ =
      ‖((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) a b‖ ^ 2 := by
  have hd (i : p ⊕ q) : ‖Sum.elim (fun _ => (1 : 𝕜)) (fun _ => -1) i‖ = 1 := by
    rcases i with i | i <;> simp
  -- Only the summand at `b` of the product with the matrix unit `E_bb` survives.
  rw [GeneralLinearGroup.innerAut_apply, val_inv_of_mem_indefiniteUnitaryGroup g.property,
    Matrix.mul_apply, Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
  simp [LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal, diagonal_mul, hd, sq]

/-- **Conjugation by elements of `U(p, q)` is a proper map** to the space of maps of the matrix
algebra with the topology of pointwise convergence. If the conjugations by `g` converge along an
ultrafilter, the entries `‖g_ab‖² = ‖(g E_bb g⁻¹)_aa‖` stay bounded
(`norm_innerAut_single_apply_self`), so the ultrafilter lives on a bounded, hence compact, subset
of the closed subset `U(p, q)` of the matrices and converges there. -/
theorem isProperMap_innerAut :
    IsProperMap fun g : indefiniteUnitaryGroup p q 𝕜 =>
      ⇑(GeneralLinearGroup.innerAut (g : GL (p ⊕ q) 𝕜)) := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨GeneralLinearGroup.continuous_innerAut.comp continuous_subtypeVal, fun 𝒰 T hT => ?_⟩
  set c : p ⊕ q → p ⊕ q → ℝ := fun a b => ‖T (single b b 1) a a‖ + 2
  set S : Set (Matrix (p ⊕ q) (p ⊕ q) 𝕜) :=
    Set.univ.pi fun a => Set.univ.pi fun b => Metric.closedBall 0 (c a b)
  have hS : IsCompact S := isCompact_univ_pi fun a => isCompact_univ_pi fun b =>
    isCompact_closedBall _ _
  have hev : ∀ᶠ g : indefiniteUnitaryGroup p q 𝕜 in 𝒰, ∀ a b,
      ‖((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) a b‖ ≤ c a b := by
    refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
    have hlim : Tendsto (fun g : indefiniteUnitaryGroup p q 𝕜 =>
        ‖GeneralLinearGroup.innerAut (g : GL (p ⊕ q) 𝕜) (single b b 1) a a‖) 𝒰
        (𝓝 ‖T (single b b 1) a a‖) :=
      ((continuous_norm.comp (continuous_id.matrix_elem a a)).tendsto _).comp
        (((continuous_apply (single b b 1)).tendsto T).comp hT)
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one _))] with g hg
    rw [norm_innerAut_single_apply_self] at hg
    -- `x ≤ 1 + x²` for every real `x`.
    nlinarith [sq_nonneg (‖((g : GL (p ⊕ q) 𝕜) : Matrix (p ⊕ q) (p ⊕ q) 𝕜) a b‖ - 1)]
  obtain ⟨g, -, hg⟩ := ((unitaryGroupOf.isClosedEmbedding_val
    LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal).isCompact_preimage hS).ultrafilter_le_nhds'
      𝒰 (Ultrafilter.mem_coe.1 (hev.mono fun g hg => Set.mem_univ_pi.2 fun a =>
        Set.mem_univ_pi.2 fun b => mem_closedBall_zero_iff.2 (hg a b)))
  exact ⟨g, hg⟩

end indefiniteUnitaryGroup

namespace ProjectiveIndefiniteUnitaryGroup

/-- The conjugation representation of `PU(p, q)` is continuous, as a map to the space of maps of
the matrix algebra with the topology of pointwise convergence. -/
theorem continuous_innerAut :
    Continuous fun γ : ProjectiveIndefiniteUnitaryGroup p q 𝕜 => ⇑(innerAut γ) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <|
    (GeneralLinearGroup.continuous_innerAut.comp continuous_subtypeVal).congr fun g => by simp

/-- **The conjugation representation of `PU(p, q)` is a closed embedding** into the space of maps
of the matrix algebra with the topology of pointwise convergence: it is continuous, injective
(`innerAut_injective`) and closed, since a closed subset of `PU(p, q)` is the image of its closed
preimage in `U(p, q)`, on which conjugation is a proper map. In particular `Ad(PU(p, q))` is
closed and `Ad` is a homeomorphism onto it. -/
theorem isClosedEmbedding_innerAut :
    IsClosedEmbedding fun γ : ProjectiveIndefiniteUnitaryGroup p q 𝕜 => ⇑(innerAut γ) := by
  refine .of_continuous_injective_isClosedMap continuous_innerAut
    (DFunLike.coe_injective.comp innerAut_injective) fun C hC => ?_
  rw [← Set.image_preimage_eq C QuotientGroup.mk_surjective, Set.image_image]
  convert indefiniteUnitaryGroup.isProperMap_innerAut.isClosedMap _
    (hC.preimage QuotientGroup.continuous_mk) using 2
  simp

/-- `PU(p, q)` over `ℝ` or `ℂ` is Hausdorff: its conjugation representation embeds it in a
Hausdorff space. -/
instance instT2Space : T2Space (ProjectiveIndefiniteUnitaryGroup p q 𝕜) :=
  isClosedEmbedding_innerAut.isEmbedding.t2Space

end ProjectiveIndefiniteUnitaryGroup

end Matrix

end TauCeti
