/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Unitization
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Isometry
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.CompletelyBounded

/-!
# Matrix amplification of nuclear completely positive contractions

The amplification `φₙ : M_n(A) → M_n(B)` of a completely positive map, applying `φ` entrywise
(`CompletelyPositiveMap.mapCStarMatrix`), is completely positive. If `φ` is a contraction, so is
every amplification (`CompletelyPositiveMap.norm_mapCStarMatrix_apply_le`), also for nonunital
`A`: the amplification of `φ` is the restriction of the amplification of the unital extension
`φ⁺ : A⁺¹ → B⁺¹` to `M_n(A) ⊆ M_n(A⁺¹)`, and `M_n(A) → M_n(A⁺¹)` and `M_n(B) → M_n(B⁺¹)` are
isometric.

If `φ` is a nuclear contraction, so is every amplification
(`CompletelyPositiveMap.IsNuclearContraction.mapCStarMatrix`): a net of factorizations
`βᵢ ∘ αᵢ` through `M_k` converging to `φ` pointwise amplifies to factorizations
`(βᵢ)ₙ ∘ (αᵢ)ₙ` through `M_n(M_k) ≅ M_{n × k}`, a nuclear C⋆-algebra, converging to `φₙ`
entrywise, hence in norm, since the norm of `M_n(B)` induces the product topology.

## Main declarations

* `CompletelyPositiveMap.norm_mapCStarMatrix_apply_le`: amplifications of completely positive
  contractions are contractions.
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

/-- **Amplifications of completely positive contractions are contractions.** For a completely
positive contraction `φ : A → B`, with `A` possibly nonunital, `‖φₙ x‖ ≤ ‖x‖` on `M_n(A)`. -/
theorem norm_mapCStarMatrix_apply_le (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) {n : Type*}
    [Fintype n] (x : CStarMatrix n n A) : ‖φ.mapCStarMatrix n x‖ ≤ ‖x‖ := by
  let ιA := CStarMatrix.mapₙₐ (n := n) (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let ιB := CStarMatrix.mapₙₐ (n := n) (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hιA : Function.Injective ιA := CStarMatrix.map_injective Unitization.inr_injective
  have hιB : Function.Injective ιB := CStarMatrix.map_injective Unitization.inr_injective
  have h1 : ‖φ.unitization hφ 1‖ ≤ 1 := by
    rw [unitization_apply_one]
    exact CStarRing.norm_one_le
  have hfac : ιB (φ.mapCStarMatrix n x) = (ιA x).map (φ.unitization hφ) :=
    CStarMatrix.ext fun i j ↦ by
      simp [ιA, ιB, CStarMatrix.mapₗ_apply, CStarMatrix.map_apply]
  rw [← NonUnitalStarAlgHom.norm_map ιB hιB, hfac, ← NonUnitalStarAlgHom.norm_map ιA hιA x]
  calc ‖(ιA x).map (φ.unitization hφ)‖ ≤ ‖φ.unitization hφ 1‖ * ‖ιA x‖ :=
        CompletelyPositiveMapClass.norm_map_cstarMatrix_le _ _
    _ ≤ 1 * ‖ιA x‖ := by gcongr
    _ = ‖ιA x‖ := one_mul _

/-- The amplification of a composite is the composite of the amplifications. -/
theorem mapCStarMatrix_comp {C : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] (φ : A →CP B) (ψ : B →CP C) (n : Type*) [Fintype n] :
    (ψ.comp φ).mapCStarMatrix n = (ψ.mapCStarMatrix n).comp (φ.mapCStarMatrix n) := by
  ext x i j
  simp

/-- `M_n(M_k)` is nuclear, through `M_n(M_k) ≅ M_{n × k}`. -/
private theorem isNuclear_cstarMatrix_cstarMatrix (n : Type*) [Fintype n] (k : ℕ) :
    TauCeti.CStarAlgebra.IsNuclear (CStarMatrix n n (CStarMatrix (Fin k) (Fin k) ℂ)) :=
  .of_starAlgEquiv (CStarMatrix.compStarAlgEquiv ℂ n (Fin k) ℂ)

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
  have hid := (isNuclear_cstarMatrix_cstarMatrix n (m i)).isNuclearContraction_id
  simpa using (hid.comp_right _ (norm_mapCStarMatrix_apply_le (α i) (hα i))).comp_left _
    (norm_mapCStarMatrix_apply_le (β i) (hβ i))

end CompletelyPositiveMap
