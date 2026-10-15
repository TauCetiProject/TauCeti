/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.TraceCoefficient.Isometry

/-!
# The equivariant Peter-Weyl Hilbert sum

The normalized trace isometries identify `L²(G)` with the Hilbert sum of the
Hilbert-Schmidt endomorphism spaces of the irreducible models. In these coordinates,
bi-translation acts separately on each summand by `T ↦ π g ∘ T ∘ π h⁻¹`.
The reconstruction formula uses `√(dim V_π) · trace (T ∘ π x⁻¹)` on each summand.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 G ι : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {models : ι → IrrepModel 𝕜 G}

/-- The normalized trace embeddings form a Hilbert sum of `L²(G)` over a skeleton of the unitary
dual. The summands carry the Hilbert-Schmidt inner product on row-column coordinates. -/
theorem isHilbertSum_traceCoeffBlock (h : IsIrrepSkeleton models) :
    IsHilbertSum 𝕜 (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim))
      fun i => (peterWeylBlock (models i)).subtypeₗᵢ.comp
        (traceCoeffBlockIsometry (models i)).toLinearIsometry := by
  refine IsHilbertSum.mk (fun i j hij a b => ?_) ?_
  · exact orthogonalFamily_peterWeylBlock h.pairwise_isEmpty_equiv hij
      (traceCoeffBlockIsometry (models i) a) (traceCoeffBlockIsometry (models j) b)
  · have hrange : ∀ i, LinearMap.range
        (((peterWeylBlock (models i)).subtypeₗᵢ.comp
          (traceCoeffBlockIsometry (models i)).toLinearIsometry).toLinearMap) =
        peterWeylBlock (models i) := by
      intro i
      exact (LinearMap.range_comp_of_range_eq_top (peterWeylBlock (models i)).subtype
        (traceCoeffBlockIsometry (models i)).toLinearEquiv.range).trans
        (Submodule.range_subtype _)
    simp only [hrange]
    exact (topologicalClosure_iSup_peterWeylBlock h).ge

/-- The Peter-Weyl isometry from `L²(G)` to the Hilbert sum of Hilbert-Schmidt endomorphism spaces,
using normalized trace coefficients for its inverse. -/
noncomputable def peterWeylTraceEquiv (h : IsIrrepSkeleton models) :
    Lp 𝕜 2 (haarProb G) ≃ₗᵢ[𝕜]
      lp (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim)) 2 :=
  (isHilbertSum_traceCoeffBlock h).linearIsometryEquiv

/-- Each row-column coordinate is the inner product with the corresponding transposed
Peter-Weyl block basis vector, viewed in `L²(G)`. -/
@[simp]
theorem peterWeylTraceEquiv_apply (h : IsIrrepSkeleton models)
    (f : Lp 𝕜 2 (haarProb G)) (i : ι) (j k : Fin (models i).dim) :
    peterWeylTraceEquiv h f i (j, k) =
      ⟪(peterWeylBlockOrthonormalBasis (models i) (k, j) : Lp 𝕜 2 (haarProb G)), f⟫_𝕜 := by
  classical
  have hs : (peterWeylTraceEquiv h).symm
      (lp.single 2 i (EuclideanSpace.single (j, k) 1)) =
        (peterWeylBlockOrthonormalBasis (models i) (k, j) : Lp 𝕜 2 (haarProb G)) := by
    simp [peterWeylTraceEquiv]
  rw [← hs, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm,
    lp.inner_single_left, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- Reconstruct an `L²` function as the sum of its normalized trace coefficients. -/
theorem peterWeylTraceEquiv_symm_apply (h : IsIrrepSkeleton models)
    (a : lp (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim)) 2) :
    (peterWeylTraceEquiv h).symm a = ∑' i,
      (Real.sqrt (models i).dim : 𝕜) •
        ContRepresentation.traceCoeffLp (models i).rep (models i).continuous_rep
          (Matrix.toEuclideanCLM (n := Fin (models i).dim) (𝕜 := 𝕜)
            (fun j k => a i (j, k))) := by
  rw [peterWeylTraceEquiv, IsHilbertSum.linearIsometryEquiv_symm_apply]
  exact tsum_congr fun i => coe_traceCoeffBlockIsometry (models i) (a i)

/-- The biregular action transported to the Peter-Weyl Hilbert sum. It is the componentwise
two-sided matrix action, as characterized by `peterWeylTraceRep_apply`. -/
noncomputable def peterWeylTraceRep (h : IsIrrepSkeleton models) :
    ContRepresentation 𝕜 (G × G)
      (lp (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim)) 2) :=
  ContinuousLinearEquiv.congr (peterWeylTraceEquiv h).toContinuousLinearEquiv (biRegularLp 𝕜 G)

/-- The Peter-Weyl Hilbert-sum action preserves the Hilbert-space inner product. -/
theorem isUnitary_peterWeylTraceRep (h : IsIrrepSkeleton models) :
    ContRepresentation.IsUnitary (peterWeylTraceRep h) :=
  (isUnitary_biRegularLp 𝕜 G).congr (peterWeylTraceEquiv h)

/-- The Hilbert-sum action is strongly continuous: each orbit map is continuous. -/
theorem continuous_peterWeylTraceRep_apply (h : IsIrrepSkeleton models)
    (a : lp (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim)) 2) :
    Continuous (fun p => peterWeylTraceRep h p a) := by
  simp only [peterWeylTraceRep, ContinuousLinearEquiv.congr_apply]
  exact (peterWeylTraceEquiv h).continuous.comp
    (continuous_biRegularLp_apply ((peterWeylTraceEquiv h).symm a))

/-- In Peter-Weyl coordinates, bi-translation acts independently on each matrix summand. -/
@[simp]
theorem peterWeylTraceRep_apply (h : IsIrrepSkeleton models) (p : G × G)
    (a : lp (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim)) 2) (i : ι) :
    peterWeylTraceRep h p a i = peterWeylMatrixRep (models i) p (a i) := by
  let b : lp (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim)) 2 :=
    ⟨fun i => peterWeylMatrixRep (models i) p (a i), Memℓp.of_norm (by
      simpa only [(isUnitary_peterWeylMatrixRep _).norm_map] using a.2.norm)⟩
  have ha := (isHilbertSum_traceCoeffBlock h).hasSum_linearIsometryEquiv_symm a
  have hb := (isHilbertSum_traceCoeffBlock h).hasSum_linearIsometryEquiv_symm b
  have hab : biRegularLp 𝕜 G p ((peterWeylTraceEquiv h).symm a) =
      (peterWeylTraceEquiv h).symm b := by
    apply HasSum.unique (ha.mapL (biRegularLp 𝕜 G p))
    convert hb using 1
    · funext i
      exact (traceCoeffBlockIsometry_intertwines (models i) p (a i)).symm
    · rw [peterWeylTraceEquiv]
  rw [peterWeylTraceRep, ContinuousLinearEquiv.congr_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, hab,
    LinearIsometryEquiv.apply_symm_apply]

/-- The Peter-Weyl isometry intertwines bi-translation with the two-sided matrix action on every
Hilbert-Schmidt summand. -/
@[simp]
theorem peterWeylTraceEquiv_biRegularLp (h : IsIrrepSkeleton models) (p : G × G)
    (f : Lp 𝕜 2 (haarProb G)) (i : ι) :
    peterWeylTraceEquiv h (biRegularLp 𝕜 G p f) i =
      peterWeylMatrixRep (models i) p (peterWeylTraceEquiv h f i) := by
  have hmap := peterWeylTraceRep_apply h p (peterWeylTraceEquiv h f) i
  rw [peterWeylTraceRep, ContinuousLinearEquiv.congr_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] at hmap
  exact hmap

end TauCeti
