/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.ClosedIdeal

import TauCeti.Analysis.Normed.Algebra.Completion

/-!
# The residue norm of a dagger algebra and its completion

Let `A = W_n ⧸ I` be a `K`-dagger algebra with `W_n = K⟨X₁, …, Xₙ⟩†` the Monsky–Washnitzer
algebra, presented by `φ : W_n ↠ A`. The *residue seminorm* of the presentation is
`|a| = inf {‖f‖ : f ∈ W_n, φ f = a}` with the Gauss norm on `W_n`. It is a norm, because every
ideal of `W_n` is closed for the Gauss norm, so the quotient seminorm is definite, and in fact
the infimum is attained. This file transports it to a norm on `A` along the chosen minimal
presentation, shows that the completion map `τ : A → Â = T_n ⧸ I T_n` of
`TauCeti.Dagger.toCompletion` is an isometry with dense image, and constructs the isometric
`K`-algebra equivalence `UniformSpace.Completion A ≃ₐ[K] completion K A` identifying `Â` with the
metric completion of `A`.

This is the completion comparison of Grosse-Klönne, *Rigid analytic spaces with overconvergent
structure sheaf*, §1, Proposition 1.6: `A` is to its completion `Â` as `W_n` is to `T_n`, with the
residue norm playing the role of the Gauss norm. It is the prerequisite for the canonical
topology of dagger algebras: the uniqueness of the topology rests on the automatic continuity
of arbitrary `K`-algebra homomorphisms of dagger algebras, which is established separately.

## The chosen residue norm

The isometry `isometry_toCompletion` compares the residue norm transported along the chosen
minimal presentation with the quotient Gauss norm on `completion K A`. The residue norm is
carried explicitly by `residueNormedCommRing` and the local `letI` declarations in the results,
rather than by a global instance. With these structures installed locally,
`residueCompletionAlgEquiv` identifies `UniformSpace.Completion A` isometrically as a `K`-algebra
with `completion K A`.

## Main definitions

* `TauCeti.Dagger.residueAlgEquiv`: the isomorphism of `A` with the residue algebra
  `W_n ⧸ ker (presentation K A)` of the chosen minimal presentation.
* `TauCeti.Dagger.residueNormedCommRing` and `TauCeti.Dagger.residueNormedAlgebra`: the
  transported ultrametric algebra norm on `A`. Not instances, since they depend on the chosen
  presentation.
* `TauCeti.Dagger.residueContinuousAlgEquiv`: promotes `TauCeti.Dagger.residueAlgEquiv` to a
  topological `K`-algebra isomorphism for `TauCeti.Dagger.residueNormedCommRing`.
* `TauCeti.Dagger.residueCompletionAlgEquiv`: the isometric `K`-algebra equivalence
  `UniformSpace.Completion A ≃ₐ[K] completion K A`.

## Main results

* `TauCeti.Dagger.norm_presentation_le`: the residue norm of `A` is bounded by the Gauss norm of
  every representing series.
* `TauCeti.Dagger.exists_presentation_norm_eq`: the infimum defining the residue norm is
  attained by a representative.
* `TauCeti.Dagger.norm_toCompletion`, `TauCeti.Dagger.isometry_toCompletion`: the completion
  map `τ : A → Â` is an isometry for the residue norm and the quotient Gauss norm of `Â`.
  Its image is dense (`TauCeti.Dagger.denseRange_toCompletion`), so `Â` is a metric
  completion of the residue-normed `A` (`TauCeti.Dagger.isometry_residueCompletionAlgEquiv`).
* `TauCeti.Dagger.residueNormedCommRing_toUniformSpace_eq_comap`,
  `TauCeti.Dagger.residueNormedCommRing_toUniformSpace_eq`, and
  `TauCeti.Dagger.residueNormedCommRing_toTopologicalSpace_eq_induced`: the uniformity and
  topology of `residueNormedCommRing K A` are pulled back from `completion K A` along
  `toCompletion K A`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6.
-/

public section

open UniformSpace

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section Algebraic

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "W" => washnitzerAlgebra (Fin (presentationDim K A)) K
local notation "I" => RingHom.ker (presentation K A)

/-- The isomorphism of a dagger algebra `A` with the residue algebra
`W_n ⧸ ker (presentation K A)` of the chosen minimal presentation. -/
noncomputable def residueAlgEquiv : A ≃ₐ[K] W ⧸ I :=
  (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm

/-- `residueAlgEquiv K A` is the inverse of the first isomorphism theorem for the chosen
presentation `presentation K A`. -/
theorem residueAlgEquiv_def :
    residueAlgEquiv K A =
      (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm :=
  (rfl)

/-- The residue isomorphism sends the image of a series to its quotient class. -/
@[simp] theorem residueAlgEquiv_presentation (f : W) :
    residueAlgEquiv K A (presentation K A f) = Ideal.Quotient.mk _ f := by
  have h := Ideal.quotientKerAlgEquivOfSurjective_mk (presentation_surjective K A) f
  simp only [residueAlgEquiv, ← h, AlgEquiv.symm_apply_apply]

end Algebraic

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "W" => washnitzerAlgebra (Fin (presentationDim K A)) K
local notation "I" => RingHom.ker (presentation K A)

/-- The residue norm on a dagger algebra: the norm `‖x‖ = ‖residueAlgEquiv K A x‖`,
transported from the quotient Gauss norm of the chosen minimal presentation. It is an
ultrametric `K`-algebra norm (`TauCeti.Dagger.isUltrametricDist_residueNormedCommRing`,
`TauCeti.Dagger.residueNormedAlgebra`). Like the quotient Gauss norm of `Â`, it depends on
the chosen presentation, so it is not an instance. -/
noncomputable abbrev residueNormedCommRing : NormedCommRing A :=
  NormedCommRing.induced A _ (residueAlgEquiv K A) (residueAlgEquiv K A).injective

/-- The residue norm `TauCeti.Dagger.residueNormedCommRing` is a `K`-algebra norm. -/
noncomputable abbrev residueNormedAlgebra :
    letI := residueNormedCommRing K A
    NormedAlgebra K A :=
  letI := residueNormedCommRing K A
  NormedAlgebra.induced K A _ (residueAlgEquiv K A)

/-- `TauCeti.Dagger.residueAlgEquiv` preserves the residue norm. -/
@[simp↓] theorem norm_residueAlgEquiv (x : A) :
    letI := residueNormedCommRing K A
    ‖residueAlgEquiv K A x‖ = ‖x‖ :=
  rfl

/-- The residue isomorphism `residueAlgEquiv K A : A ≃ₐ[K] W_n ⧸ ker (presentation K A)` as a
topological `K`-algebra isomorphism for `residueNormedCommRing K A`. -/
noncomputable def residueContinuousAlgEquiv :
    letI := residueNormedCommRing K A
    A ≃A[K] W ⧸ I :=
  letI := residueNormedCommRing K A
  have hiso : Isometry (residueAlgEquiv K A) :=
    (AddMonoidHomClass.isometry_iff_norm (residueAlgEquiv K A)).mpr (norm_residueAlgEquiv K A)
  have hiso_symm : Isometry (residueAlgEquiv K A).symm :=
    (AddMonoidHomClass.isometry_iff_norm (residueAlgEquiv K A).symm).mpr fun x ↦
      (norm_residueAlgEquiv K A ((residueAlgEquiv K A).symm x)).symm.trans
        (congrArg norm ((residueAlgEquiv K A).apply_symm_apply x))
  { residueAlgEquiv K A with
    continuous_toFun := hiso.continuous
    continuous_invFun := hiso_symm.continuous }

/-- `residueContinuousAlgEquiv` has the same underlying function as `residueAlgEquiv`. -/
@[simp↓]
theorem coe_residueContinuousAlgEquiv :
    letI := residueNormedCommRing K A
    ⇑(residueContinuousAlgEquiv K A) = ⇑(residueAlgEquiv K A) :=
  letI := residueNormedCommRing K A
  (rfl)

/-- The underlying `AlgEquiv` of `residueContinuousAlgEquiv` is `residueAlgEquiv`. -/
@[simp↓]
theorem toAlgEquiv_residueContinuousAlgEquiv :
    letI := residueNormedCommRing K A
    (residueContinuousAlgEquiv K A).toAlgEquiv = residueAlgEquiv K A :=
  letI := residueNormedCommRing K A
  (rfl)

/-- `residueContinuousAlgEquiv` sends `presentation K A f` to the quotient class of `f`. -/
@[simp↓]
theorem residueContinuousAlgEquiv_presentation (f : W) :
    letI := residueNormedCommRing K A
    residueContinuousAlgEquiv K A (presentation K A f) = Ideal.Quotient.mk _ f :=
  letI := residueNormedCommRing K A
  residueAlgEquiv_presentation K A f

/-- The inverse of `residueContinuousAlgEquiv` sends the quotient class of `f` to
`presentation K A f`. -/
@[simp↓]
theorem residueContinuousAlgEquiv_symm_mk (f : W) :
    letI := residueNormedCommRing K A
    (residueContinuousAlgEquiv K A).symm (Ideal.Quotient.mk _ f) = presentation K A f :=
  letI := residueNormedCommRing K A
  (residueContinuousAlgEquiv K A).symm_apply_eq.mpr
    (residueContinuousAlgEquiv_presentation K A f).symm

/-- The residue norm on a dagger algebra is ultrametric. -/
theorem isUltrametricDist_residueNormedCommRing :
    letI := residueNormedCommRing K A
    IsUltrametricDist A :=
  letI := residueNormedCommRing K A
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [← norm_residueAlgEquiv, map_add] using
      IsUltrametricDist.norm_add_le_max (residueAlgEquiv K A x) (residueAlgEquiv K A y)

/-- The residue norm of the image of a series is at most its Gauss norm. -/
theorem norm_presentation_le (f : W) :
    letI := residueNormedCommRing K A
    ‖presentation K A f‖ ≤ ‖f‖ :=
  letI := residueNormedCommRing K A
  by
    have h := Ideal.Quotient.norm_mk_le I f
    rwa [← residueAlgEquiv_presentation, norm_residueAlgEquiv] at h

/-- The infimum defining the residue norm is attained: every element of a dagger algebra is
represented by a series of equal Gauss norm. -/
theorem exists_presentation_norm_eq (a : A) :
    letI := residueNormedCommRing K A
    ∃ f : W, presentation K A f = a ∧ ‖f‖ = ‖a‖ :=
  letI := residueNormedCommRing K A
  by
  obtain ⟨f, hf, hnorm⟩ := Ideal.exists_mk_eq_and_norm_eq_washnitzerAlgebra I
    (residueAlgEquiv K A a)
  have hfa : presentation K A f = a := by
    have h := congrArg (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)) hf
    rw [Ideal.quotientKerAlgEquivOfSurjective_mk] at h
    simpa only [residueAlgEquiv, AlgEquiv.apply_symm_apply] using h
  refine ⟨f, hfa, ?_⟩
  rw [← norm_residueAlgEquiv]
  exact hnorm

/-- The completion map is an isometry for the residue norm on `A` and the quotient Gauss
norm on `Â`. -/
@[simp↓] theorem norm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    ‖toCompletion K A a‖ = ‖a‖ :=
  letI := residueNormedCommRing K A
  by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  rw [toCompletion_presentation, Ideal.norm_mk_map_toTate,
    ← residueAlgEquiv_presentation, norm_residueAlgEquiv]

/-- The completion map `τ : A → Â` is an isometry. -/
theorem isometry_toCompletion :
    letI := residueNormedCommRing K A
    Isometry (toCompletion K A) :=
  letI := residueNormedCommRing K A
  (AddMonoidHomClass.isometry_iff_norm (E := A) (F := completion K A)
    (toCompletion K A)).mpr
    fun a ↦ norm_toCompletion K A a

/-- The uniformity of `residueNormedCommRing K A` is pulled back from `completion K A` along
`toCompletion K A`. -/
theorem residueNormedCommRing_toUniformSpace_eq_comap :
    (residueNormedCommRing K A).toUniformSpace =
      UniformSpace.comap (toCompletion K A) inferInstance :=
  letI := residueNormedCommRing K A
  (isometry_toCompletion K A).isUniformInducing.comap_uniformSpace.symm

/-- The topology of `residueNormedCommRing K A` is induced from `completion K A` along
`toCompletion K A`. -/
theorem residueNormedCommRing_toTopologicalSpace_eq_induced :
    (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced (toCompletion K A) inferInstance := by
  rw [residueNormedCommRing_toUniformSpace_eq_comap, UniformSpace.toTopologicalSpace_comap]
  rfl

/-- **Metric completion comparison** (Grosse-Klönne, Proposition 1.6 (1)). With the residue norm
`residueNormedCommRing K A`, the metric completion `UniformSpace.Completion A` is isomorphic as a
`K`-algebra to `completion K A`. -/
noncomputable def residueCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Completion A ≃ₐ[K] completion K A :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  AlgHom.completionAlgEquiv (R := K) (A := A) (B := completion K A)
    (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion

/-- `residueCompletionAlgEquiv K A` extends `toCompletion K A` on elements of `A`. -/
@[simp↓]
theorem residueCompletionAlgEquiv_coe (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    residueCompletionAlgEquiv K A (a : Completion A) = toCompletion K A a :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    exact AlgHom.completionAlgEquiv_coe (R := K) (A := A) (B := completion K A)
      (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion a

/-- The inverse of `residueCompletionAlgEquiv K A` recovers the completion class of `a : A`. -/
@[simp↓]
theorem residueCompletionAlgEquiv_symm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    (residueCompletionAlgEquiv K A).symm (toCompletion K A a) = (a : Completion A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    exact AlgHom.completionAlgEquiv_symm_apply (R := K) (A := A) (B := completion K A)
      (toCompletion K A) (isometry_toCompletion K A) denseRange_toCompletion a

/-- `residueCompletionAlgEquiv K A` is an isometry for the completed residue norm and the quotient
Gauss norm on `completion K A`. -/
theorem isometry_residueCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Isometry (residueCompletionAlgEquiv K A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    unfold residueCompletionAlgEquiv
    exact AlgHom.isometry_completionAlgEquiv _ _ _

/-- `residueCompletionAlgEquiv K A` preserves norms. -/
@[simp↓]
theorem norm_residueCompletionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    ∀ x : Completion A, ‖residueCompletionAlgEquiv K A x‖ = ‖x‖ :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by
    intro x
    rw [← dist_zero_right (residueCompletionAlgEquiv K A x),
      ← map_zero (residueCompletionAlgEquiv K A),
      (isometry_residueCompletionAlgEquiv K A).dist_eq, dist_zero_right]

variable {K A} in
/-- Any uniform additive group structure on `A` for which `toCompletion K A` is topologically
inducing coincides with the uniformity of `residueNormedCommRing K A`. -/
theorem residueNormedCommRing_toUniformSpace_eq [UniformSpace A] [IsUniformAddGroup A]
    (hA : Topology.IsInducing (toCompletion K A)) :
    (residueNormedCommRing K A).toUniformSpace = ‹UniformSpace A› :=
  (residueNormedCommRing_toUniformSpace_eq_comap K A).trans
    (AddMonoidHom.isUniformInducing_of_isInducing hA).comap_uniformSpace

end TauCeti.Dagger
