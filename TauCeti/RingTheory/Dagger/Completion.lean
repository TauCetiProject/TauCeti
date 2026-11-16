/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.GaussNorm
public import TauCeti.Analysis.Normed.Algebra.Completion

/-!
# Completion of the Monsky–Washnitzer algebra

Over a complete ultrametric normed commutative ring `K`, the metric completion of the
Monsky–Washnitzer algebra for its Gauss norm is isometrically isomorphic to the Tate algebra.
The isomorphism
extends `toTate`, so in particular it preserves the polynomial coordinates and the coefficient
ring. This identifies the analytic completion of overconvergent functions on a polydisc.

Over a nontrivially normed field, the Monsky–Washnitzer algebra with at least one variable
is incomplete: its isometric image is dense and proper in the Tate algebra.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2 and Proposition 1.6.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries UniformSpace

variable {σ K : Type*} [NormedCommRing K] [IsUltrametricDist K]

section Complete

variable [CompleteSpace K]

variable (σ K) in
/-- The completion of the Monsky–Washnitzer algebra is the unit-radius Tate algebra,
as an algebra over the coefficient ring. -/
noncomputable def completionAlgEquiv :
    Completion (washnitzerAlgebra σ K) ≃ₐ[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) :=
  (toTate σ K).completionAlgEquiv isometry_toTate denseRange_toTate

/-- The completion comparison extends the original inclusion into the Tate algebra. -/
@[simp]
theorem completionAlgEquiv_coe (f : washnitzerAlgebra σ K) :
    completionAlgEquiv σ K (f : Completion (washnitzerAlgebra σ K)) = toTate σ K f :=
  AlgHom.completionAlgEquiv_coe _ _ _ f

/-- The inverse completion comparison sends an overconvergent series to its completion class. -/
@[simp]
theorem completionAlgEquiv_symm_toTate (f : washnitzerAlgebra σ K) :
    (completionAlgEquiv σ K).symm (toTate σ K f) = (f : Completion (washnitzerAlgebra σ K)) := by
  rw [← completionAlgEquiv_coe, AlgEquiv.symm_apply_apply]

/-- The algebraic completion comparison is an isometry. -/
theorem isometry_completionAlgEquiv : Isometry (completionAlgEquiv σ K) :=
  AlgHom.isometry_completionAlgEquiv _ _ _

/-- The completion comparison preserves the Gauss norm. -/
@[simp]
theorem norm_completionAlgEquiv (f : Completion (washnitzerAlgebra σ K)) :
    ‖completionAlgEquiv σ K f‖ = ‖f‖ :=
  AlgHom.norm_completionAlgEquiv _ _ _ f

end Complete

section NontriviallyNormedField

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Nonempty σ]

/-- In at least one variable, overconvergent series over a nontrivially normed field are
incomplete for the Gauss norm. Completeness of the coefficient field is not required. -/
theorem not_completeSpace : ¬ CompleteSpace (washnitzerAlgebra σ L) := by
  intro h
  let := h
  have hsurj : Function.Surjective (toTate σ L) := by
    intro f
    have hf := denseRange_toTate (σ := σ) (R := L) f
    rwa [isometry_toTate.isClosedEmbedding.isClosed_range.closure_eq] at hf
  apply (washnitzerAlgebra_toSubring_lt (σ := σ) (K := L)).not_ge
  intro f hf
  obtain ⟨g, hg⟩ := hsurj ⟨f, hf⟩
  have hg' : (g : MvPowerSeries σ L) = f := by
    simpa only [coe_toTate] using congrArg Subtype.val hg
  exact hg' ▸ g.2

end NontriviallyNormedField

end TauCeti.Dagger.washnitzerAlgebra
