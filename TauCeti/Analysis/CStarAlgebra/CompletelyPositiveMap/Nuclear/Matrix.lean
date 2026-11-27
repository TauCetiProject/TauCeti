/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.CompletelyBounded

/-!
# Matrix amplification of nuclear completely positive contractions

The amplification `φₙ : M_n(A) → M_n(B)` of a completely positive map, applying `φ` entrywise
(`CompletelyPositiveMap.mapCStarMatrix`), is completely positive, and a contraction when `φ` is
(`CompletelyPositiveMap.norm_mapCStarMatrix_apply_le`).

If `φ` is a nuclear contraction, so is every amplification
(`CompletelyPositiveMap.IsNuclearContraction.mapCStarMatrix`): a net of factorizations
`βᵢ ∘ αᵢ` through `M_k` converging to `φ` pointwise amplifies to factorizations
`(βᵢ)ₙ ∘ (αᵢ)ₙ` through `M_n(M_k) ≅ M_{n × k}`, a nuclear C⋆-algebra, converging to `φₙ`
entrywise, hence in norm, since the norm of `M_n(B)` induces the product topology.

## Main declarations

* `CompletelyPositiveMap.IsNuclearContraction.mapCStarMatrix`: amplifications of nuclear
  contractions are nuclear contractions.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer (2006), IV.3.1.4.
-/

public section

open scoped CStarAlgebra ComplexOrder Topology

open Filter

namespace CompletelyPositiveMap

variable {A B : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Amplifications of nuclear contractions.** If `φ : A → B` is a nuclear contraction, so is its
amplification `φₙ : M_n(A) → M_n(B)`. -/
theorem IsNuclearContraction.mapCStarMatrix {φ : A →CP B} (h : φ.IsNuclearContraction)
    (n : Type*) [Fintype n] : (φ.mapCStarMatrix n).IsNuclearContraction := by
  classical
  obtain ⟨m, α, β, hα, hβ, hlim⟩ := h.exists_tendsto
  refine IsNuclearContraction.of_forall_exists fun F ε hε ↦ ?_
  -- The amplified factorizations converge to `φₙ` entrywise, hence in `M_n(B)`.
  have htend (x : CStarMatrix n n A) : Tendsto
      (fun i ↦ (((β i).comp (α i)).mapCStarMatrix n) x) atTop (𝓝 (φ.mapCStarMatrix n x)) := by
    simp only [mapCStarMatrix_apply]
    exact tendsto_pi_nhds.2 fun p ↦ tendsto_pi_nhds.2 fun q ↦ by
      simpa [CStarMatrix.map_apply] using hlim (x p q)
  have hev : ∀ᶠ i in atTop, ∀ x ∈ F,
      ‖(((β i).comp (α i)).mapCStarMatrix n) x - φ.mapCStarMatrix n x‖ < ε :=
    (eventually_all_finset F).2 fun x _ ↦ by
      simpa [dist_eq_norm] using (Metric.tendsto_nhds.1 (htend x)) ε hε
  obtain ⟨i, hi⟩ := hev.exists
  refine ⟨((β i).comp (α i)).mapCStarMatrix n, ?_, hi⟩
  rw [mapCStarMatrix_comp]
  have hid := TauCeti.CStarAlgebra.IsNuclear.isNuclearContraction_id
    (A := CStarMatrix n n (CStarMatrix (Fin (m i)) (Fin (m i)) ℂ))
  have hαn (x : CStarMatrix n n A) : ‖(α i).mapCStarMatrix n x‖ ≤ ‖x‖ := by
    simpa using norm_mapCStarMatrix_apply_le (c := 1) (α i) (by simpa using hα i) x
  have hβn (x : CStarMatrix n n (CStarMatrix (Fin (m i)) (Fin (m i)) ℂ)) :
      ‖(β i).mapCStarMatrix n x‖ ≤ ‖x‖ := by
    simpa using norm_mapCStarMatrix_apply_le (c := 1) (β i) (by simpa using hβ i) x
  simpa using (hid.comp_right _ hαn).comp_left _ hβn

end CompletelyPositiveMap
