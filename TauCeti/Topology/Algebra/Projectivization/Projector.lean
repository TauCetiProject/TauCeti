/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Projectivization.Projector
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Topological properties of the rank-one projector embedding

The projector map `Projectivization.projector : ℙ K (ι → K) → Matrix ι ι K` sends a line spanned
by `x` to the matrix `x xᵀ / (xᵀ x)`, and over an ordered field is a bijection onto the *projector
locus* `TauCeti.projectorLocus ι K` of symmetric idempotent matrices of trace one
(`Projectivization.range_projector`). Here we establish its topological properties.

The projector map is continuous for the quotient topology on projective space. Over any Hausdorff
topological ordered field with continuous inversion, the projector locus is closed and recovering a
line from a nonzero-diagonal row gives a continuous inverse on the locus, so the projector map is a
closed embedding: a homeomorphism from projective space onto the projector locus. Over `ℝ`,
projective space is compact, hence the real projector locus is compact as well. The semialgebraic
and Nash properties of the same embedding are in
`TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding`.

## Main results

* `TauCeti.isClosed_projectorLocus`: the projector locus is closed over a field with a Hausdorff
  ring topology.
* `Projectivization.continuous_projector`: the projector map is continuous.
* `Projectivization.isClosedEmbedding_projector`: over a Hausdorff topological ordered field with
  continuous inversion, the projector map is a closed embedding.
* `TauCeti.isCompact_projectorLocus`: over `ℝ`, the projector locus is compact.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-- The projector locus is closed. -/
theorem isClosed_projectorLocus {ι K : Type*} [Fintype ι] [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] : IsClosed (projectorLocus ι K) := by
  have h : projectorLocus ι K = {A | Aᵀ = A} ∩ {A | A * A = A} ∩ {A | A.trace = 1} := by
    ext A; simp [IsSymm, IsIdempotentElem, and_assoc]
  rw [h]
  exact ((isClosed_eq continuous_id.matrix_transpose continuous_id).inter
    (isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id)).inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

end TauCeti

namespace Projectivization

open TauCeti

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

/-- The projector map is continuous for the quotient topology on projective space. -/
theorem continuous_projector : Continuous (projector : ℙ K (ι → K) → Matrix ι ι K) := by
  rw [continuous_iff]
  have hcomp : projector ∘ mk' K = fun x : {x : ι → K // x ≠ 0} ↦ rankOneProjector x.val :=
    funext fun x ↦ by simp
  simp only [hcomp, rankOneProjector_def]
  exact ((continuous_subtypeVal.dotProduct continuous_subtypeVal).inv₀ fun x ↦
    dotProduct_self_eq_zero.not.mpr x.property).smul
    (continuous_subtypeVal.matrix_vecMulVec continuous_subtypeVal)

/-- Over a Hausdorff topological ordered field with continuous inversion, the projector map is a
closed embedding, hence a homeomorphism from projective space onto the projector locus
`TauCeti.projectorLocus ι K`. -/
theorem isClosedEmbedding_projector [T2Space K] :
    IsClosedEmbedding (projector : ℙ K (ι → K) → Matrix ι ι K) := by
  let g : range (projector : ℙ K (ι → K) → Matrix ι ι K) → ℙ K (ι → K) := fun A ↦ A.property.choose
  have hpg (A : range (projector : ℙ K (ι → K) → Matrix ι ι K)) : projector (g A) = A.val :=
    A.property.choose_spec
  have hg_left : g ∘ rangeFactorization projector = id :=
    funext fun p ↦ projector_injective (hpg ⟨projector p, mem_range_self p⟩)
  have hg_cont : Continuous g := continuous_iff_continuousAt.2 fun A ↦ by
    obtain ⟨r, hr⟩ := exists_mem_affineOpen (g A)
    have hArr : A.val r r ≠ 0 := hpg A ▸ (projector_apply_self_pos_iff.2 hr).ne'
    let U : Set (range (projector : ℙ K (ι → K) → Matrix ι ι K)) := {B | B.val r r ≠ 0}
    have hU_open : IsOpen U := isOpen_ne.preimage (continuous_subtypeVal.matrix_elem r r)
    have hU_cont : ContinuousOn g U := by
      rw [continuousOn_iff_continuous_domRestrict]
      let row : U → {v : ι → K // v ≠ 0} := fun B ↦ ⟨B.val.val r, fun h0 ↦ B.property
          (congr_fun h0 r)⟩
      have hrow_cont : Continuous row := (continuous_pi fun j ↦
        (continuous_subtypeVal.comp continuous_subtypeVal).matrix_elem r j).subtype_mk _
      refine (isQuotientMap_mk'.continuous.comp hrow_cont).congr fun B ↦ ?_
      have hB : projector (g B.val) = B.val.val := hpg B.val
      have hBrr : projector (g B.val) r r ≠ 0 := hB.symm ▸ B.property
      simpa only [Function.comp_apply, row, mk'_eq_mk, domRestrict_apply, ← hB] using
        mk_projector_row (g B.val) hBrr fun h0 ↦ hBrr (congr_fun h0 r)
    exact hU_cont.continuousAt (hU_open.mem_nhds hArr)
  have hind : IsInducing (projector : ℙ K (ι → K) → Matrix ι ι K) :=
    IsInducing.subtypeVal.comp <| IsInducing.of_comp (f := rangeFactorization projector) (g := g)
      continuous_projector.rangeFactorization hg_cont
      (by simpa [hg_left] using (IsInducing.id (X := ℙ K (ι → K))))
  exact ⟨⟨hind, projector_injective⟩, range_projector (ι := ι) (K := K) ▸ isClosed_projectorLocus⟩

end Projectivization

namespace TauCeti

/-- The real projector locus is compact, being the image of compact real projective space. -/
theorem isCompact_projectorLocus {ι : Type*} [Fintype ι] : IsCompact (projectorLocus ι ℝ) :=
  Projectivization.range_projector (ι := ι) (K := ℝ) ▸
    isCompact_range Projectivization.continuous_projector

end TauCeti
