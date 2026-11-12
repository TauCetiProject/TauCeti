/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.ClosedIdeal
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# The residue norm of a dagger algebra and its completion

Let `K` be a complete nontrivially normed ultrametric field and `A = W_n ⧸ I` a
`K`-dagger algebra with `W_n = K⟨X₁, …, Xₙ⟩†` the Monsky–Washnitzer
algebra, presented by `φ : W_n ↠ A`. The *residue seminorm* of the presentation is
`|a| = inf {‖f‖ : f ∈ W_n, φ f = a}` with the Gauss norm on `W_n`. It is a norm, because every
ideal of `W_n` is closed for the Gauss norm, so the quotient seminorm is definite, and in fact
the infimum is attained. This file transports it to a norm on `A` along the chosen minimal
presentation, shows that the completion map `τ : A → Â = T_n ⧸ I T_n` of
`TauCeti.Dagger.toCompletion` is an isometry. Together with its dense image, established in
`TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion`, this identifies `Â` with the metric
completion of `A`.

This is the completion comparison of Grosse-Klönne, *Rigid analytic spaces with overconvergent
structure sheaf*, §1, Proposition 1.6 (1): `A` is to its completion `Â` as `W_n` is to `T_n`,
with the
residue norm playing the role of the Gauss norm. It is the prerequisite for the canonical
topology of dagger algebras: the uniqueness of the topology rests on the automatic continuity
of arbitrary `K`-algebra homomorphisms of dagger algebras, Proposition 1.6 (2).

## The chosen residue norm

The isometry `isometry_toCompletion` compares the residue norm transported along the chosen
minimal presentation with the quotient Gauss norm on `completion K A`. The residue norm is
carried explicitly by `residueNormedCommRing` and the local `letI` declarations in the results,
rather than by a global instance: the unbundled ring `A` may already have its own norm. With
these structures installed locally, `completionAlgEquiv` identifies `UniformSpace.Completion A`
with `completion K A` as normed `K`-algebras. The dense-range result used here is established in
`TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion`.

## Main definitions

* `TauCeti.Dagger.residueNormedCommRing` and `TauCeti.Dagger.residueNormedAlgebra`: the
  transported ultrametric algebra norm on `A`, provided explicitly because `A` may already
  have its own norm.

## Main results

* `TauCeti.Dagger.norm_presentation_le`: the residue norm of `A` is bounded by the Gauss norm of
  every representing series.
* `TauCeti.Dagger.exists_presentation_eq_and_norm_eq`: the infimum defining the residue norm is
  attained by a representative.
* `TauCeti.Dagger.norm_toCompletion`, `TauCeti.Dagger.isometry_toCompletion`: the completion
  map `τ : A → Â` is an isometry for the residue norm and the quotient Gauss norm of `Â`.
  Its image is dense (`TauCeti.Dagger.denseRange_toCompletion`), so `Â` is a metric
  completion of the residue-normed `A`.
* `TauCeti.Dagger.completionAlgEquiv`: the isometric algebra equivalence from the metric
  completion of the residue-normed `A` to `completion K A`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 (1).
* The residue equivalence and transported norm adapt `TauCeti.IsAffinoidAlgebra.residueAlgEquiv`
  and `TauCeti.IsAffinoidAlgebra.residueNormedCommRing` from
  `TauCeti.RingTheory.Affinoid.QuotientNorm`.
-/

public section

open UniformSpace

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "W" => washnitzerAlgebra (Fin (presentationDim K A)) K
local notation "I" => RingHom.ker (presentation K A)

/-- The residue norm on a dagger algebra: the norm `‖x‖ = ‖residueAlgEquiv K A x‖`,
transported from the quotient Gauss norm of the chosen minimal presentation. It is an
ultrametric `K`-algebra norm (`TauCeti.Dagger.isUltrametricDist_residueNormedCommRing`,
`TauCeti.Dagger.residueNormedAlgebra`). It is provided explicitly because the unbundled
ring `A` may already have its own norm. -/
noncomputable abbrev residueNormedCommRing : NormedCommRing A :=
  NormedCommRing.induced A _ (residueAlgEquiv K A) (residueAlgEquiv K A).injective

/-- The residue norm `TauCeti.Dagger.residueNormedCommRing` is a `K`-algebra norm. -/
noncomputable abbrev residueNormedAlgebra :
    letI := residueNormedCommRing K A
    NormedAlgebra K A :=
  letI := residueNormedCommRing K A
  NormedAlgebra.induced K A _ (residueAlgEquiv K A)

variable {K A}

/-- `TauCeti.Dagger.residueAlgEquiv` preserves the residue norm. -/
theorem norm_residueAlgEquiv (x : A) :
    letI := residueNormedCommRing K A
    ‖residueAlgEquiv K A x‖ = ‖x‖ := (rfl)

variable (K A) in
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

variable (K) in
/-- The infimum defining the residue norm is attained: every element of a dagger algebra is
represented by a series of equal Gauss norm. -/
theorem exists_presentation_eq_and_norm_eq (a : A) :
    letI := residueNormedCommRing K A
    ∃ f : W, presentation K A f = a ∧ ‖f‖ = ‖a‖ :=
  letI := residueNormedCommRing K A
  by
  obtain ⟨f, hf, hnorm⟩ := Ideal.exists_mk_eq_and_norm_eq_washnitzerAlgebra I
    (residueAlgEquiv K A a)
  have hfa : presentation K A f = a :=
    (residueAlgEquiv K A).injective (by rwa [residueAlgEquiv_presentation])
  refine ⟨f, hfa, ?_⟩
  rw [← norm_residueAlgEquiv]
  exact hnorm

/-- The completion map is an isometry for the residue norm on `A` and the quotient Gauss
norm on `Â`. -/
theorem norm_toCompletion (a : A) :
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
    fun a ↦ norm_toCompletion a

private noncomputable def completionHom :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Completion A →ₐ[K] completion K A :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  { Completion.extensionHom (toCompletion K A).toRingHom isometry_toCompletion.continuous with
    commutes' a :=
      (Completion.extensionHom_coe (toCompletion K A).toRingHom isometry_toCompletion.continuous
        (algebraMap K A a)).trans ((toCompletion K A).commutes a) }

variable (K A) in
/-- The metric completion for the chosen residue norm is the dagger completion as a
`K`-algebra. -/
noncomputable def completionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Completion A ≃ₐ[K] completion K A :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  have hi : Isometry (completionHom (K := K) (A := A)) :=
    isometry_toCompletion.completion_extension
  AlgEquiv.ofBijective completionHom ⟨hi.injective, by
    have hd : DenseRange (completionHom (K := K) (A := A)) :=
      denseRange_toCompletion.mono <| by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, Completion.extensionHom_coe _ isometry_toCompletion.continuous a⟩
    intro a
    have ha := hd a
    rwa [hi.isClosedEmbedding.isClosed_range.closure_eq] at ha⟩

/-- The completion comparison extends the dagger completion map. -/
@[simp]
theorem completionAlgEquiv_coe (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    completionAlgEquiv K A (a : Completion A) = toCompletion K A a :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  Completion.extensionHom_coe (toCompletion K A).toRingHom isometry_toCompletion.continuous a

/-- The inverse comparison sends the image of an element to its metric completion class. -/
@[simp]
theorem completionAlgEquiv_symm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    (completionAlgEquiv K A).symm (toCompletion K A a) = (a : Completion A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  by rw [← completionAlgEquiv_coe, AlgEquiv.symm_apply_apply]

/-- The comparison between the metric completion and the dagger completion is an isometry. -/
theorem isometry_completionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    Isometry (completionAlgEquiv K A) :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  isometry_toCompletion.completion_extension

/-- The completion comparison preserves the residue norm. -/
@[simp]
theorem norm_completionAlgEquiv :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    ∀ a : Completion A, ‖completionAlgEquiv K A a‖ = ‖a‖ :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  fun a ↦ Isometry.norm_map_of_map_zero (f := completionAlgEquiv K A)
    isometry_completionAlgEquiv (completionAlgEquiv K A).toRingEquiv.map_zero a

end TauCeti.Dagger
