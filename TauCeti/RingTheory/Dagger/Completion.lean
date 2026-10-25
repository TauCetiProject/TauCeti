/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.GaussNorm
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Completion of the Monsky–Washnitzer algebra

Over a complete ultrametric normed field `K`, the metric completion of the Monsky–Washnitzer
algebra for its Gauss norm is isometrically isomorphic to the Tate algebra. The isomorphism
extends `toTate`, so in particular it preserves the polynomial coordinates and the coefficient
field. This identifies the analytic completion of overconvergent functions on a polydisc.

Over a nontrivially normed field, the Monsky–Washnitzer algebra with at least one variable
is incomplete: its isometric image is dense and proper in the Tate algebra.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2 and Proposition 1.6.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries UniformSpace

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

section Complete

variable [CompleteSpace K]

private noncomputable def completionHom :
    Completion (washnitzerAlgebra σ K) →ₐ[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) where
  __ := Completion.extensionHom (toTate σ K).toRingHom isometry_toTate.continuous
  commutes' a :=
    (Completion.extensionHom_coe (toTate σ K).toRingHom isometry_toTate.continuous
      (algebraMap K _ a)).trans ((toTate σ K).commutes a)

private theorem completionHom_coe (f : washnitzerAlgebra σ K) :
    completionHom (f : Completion (washnitzerAlgebra σ K)) = toTate σ K f :=
  Completion.extensionHom_coe (toTate σ K).toRingHom isometry_toTate.continuous f

private theorem isometry_completionHom : Isometry (completionHom (σ := σ) (K := K)) :=
  isometry_toTate.completion_extension

private theorem completionHom_surjective :
    Function.Surjective (completionHom (σ := σ) (K := K)) := by
  have hd : DenseRange (completionHom (σ := σ) (K := K)) := denseRange_toTate.mono <| by
    rintro _ ⟨f, rfl⟩
    exact ⟨f, completionHom_coe f⟩
  intro f
  have hf := hd f
  rwa [isometry_completionHom.isClosedEmbedding.isClosed_range.closure_eq] at hf

variable (σ K) in
/-- The completion of the Monsky–Washnitzer algebra is the unit-radius Tate algebra,
as an algebra over the coefficient field. -/
noncomputable def completionAlgEquiv :
    Completion (washnitzerAlgebra σ K) ≃ₐ[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) :=
  AlgEquiv.ofBijective completionHom ⟨isometry_completionHom.injective, completionHom_surjective⟩

/-- The completion comparison extends the original inclusion into the Tate algebra. -/
@[simp]
theorem completionAlgEquiv_coe (f : washnitzerAlgebra σ K) :
    completionAlgEquiv σ K (f : Completion (washnitzerAlgebra σ K)) = toTate σ K f :=
  completionHom_coe f

/-- The inverse completion comparison sends an overconvergent series to its completion class. -/
@[simp]
theorem completionAlgEquiv_symm_toTate (f : washnitzerAlgebra σ K) :
    (completionAlgEquiv σ K).symm (toTate σ K f) = (f : Completion (washnitzerAlgebra σ K)) := by
  rw [← completionAlgEquiv_coe, AlgEquiv.symm_apply_apply]

/-- The algebraic completion comparison is an isometry. -/
theorem isometry_completionAlgEquiv : Isometry (completionAlgEquiv σ K) :=
  isometry_completionHom

/-- The completion comparison preserves the Gauss norm. -/
@[simp]
theorem norm_completionAlgEquiv (f : Completion (washnitzerAlgebra σ K)) :
    ‖completionAlgEquiv σ K f‖ = ‖f‖ :=
  (AddMonoidHomClass.isometry_iff_norm _).mp isometry_completionAlgEquiv f

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
