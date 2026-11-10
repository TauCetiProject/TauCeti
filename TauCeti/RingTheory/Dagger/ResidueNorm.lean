/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.ClosedIdeal
public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Dagger.Noetherian

/-!
# The residue norm of a dagger algebra and its completion

Let `A = W_n ⧸ I` be a `K`-dagger algebra with `W_n = K⟨X₁, …, Xₙ⟩†` the Monsky–Washnitzer
algebra, presented by `φ : W_n ↠ A`. The *residue seminorm* of the presentation is
`|a| = inf {‖f‖ : f ∈ W_n, φ f = a}` with the Gauss norm on `W_n`. It is a norm, because every
ideal of `W_n` is closed for the Gauss norm, so the quotient seminorm is definite, and in fact
the infimum is attained. This file transports it to a norm on `A` along the chosen minimal
presentation, shows that the completion map `τ : A → Â = T_n ⧸ I T_n` of
`TauCeti.Dagger.toCompletion` is an isometry with dense image, so that `Â` is a metric
completion of `A`.

This is the completion comparison of Grosse-Klönne, *Rigid analytic spaces with overconvergent
structure sheaf*, §1, Proposition 1.6: `A` is to its completion `Â` as `W_n` is to `T_n`, with the
residue norm playing the role of the Gauss norm. It is the prerequisite for the canonical
topology of dagger algebras: the uniqueness of the topology rests on the automatic continuity
of arbitrary `K`-algebra homomorphisms of dagger algebras, which is established separately.

## What this file does and does not do

It shows that `τ : A → Â` is an isometry with dense range for the residue norm, in the
presentation-independent form `isometry_toCompletion`. Note that the residue norm is not an
instance: it depends on the chosen presentation of `A`, so no global `NormedCommRing A`
instance can be declared, and statements that need the residue norm carry it explicitly
via a `letI`. For this reason the literal statement `UniformSpace.Completion A ≃ₐ[K]
completion K A` cannot be formulated with typeclass instances in this file; the isometry
and density results above are the usable content of the comparison.

The residue norm depends on the chosen minimal presentation, so it is carried by the
`residueNormedCommRing` structure rather than by an instance, exactly as
`TauCeti.IsAffinoidAlgebra.residueNormedCommRing` is for affinoid algebras.

## Main definitions

* `TauCeti.Dagger.residueAlgEquiv`: the isomorphism of `A` with the residue algebra
  `W_n ⧸ ker (presentation K A)` of the chosen minimal presentation.
* `TauCeti.Dagger.residueNormedCommRing` and `TauCeti.Dagger.residueNormedAlgebra`: the
  transported ultrametric algebra norm on `A`. Not instances, since they depend on the chosen
  presentation.

## Main results

* `TauCeti.Dagger.norm_presentation_le`: the residue norm of `A` is bounded by the Gauss norm of
  every representing series.
* `TauCeti.Dagger.exists_presentation_norm_eq`: the infimum defining the residue norm is
  attained by a representative.
* `TauCeti.Dagger.norm_toCompletion`, `TauCeti.Dagger.isometry_toCompletion`: the completion
  map `τ : A → Â` is an isometry for the residue norm and the quotient Gauss norm of `Â`.
  Its image is dense (`TauCeti.Dagger.denseRange_toCompletion`), so `Â` is a metric
  completion of the residue-normed `A`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6.
-/

public section

open UniformSpace

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

local notation "W" => washnitzerAlgebra (Fin (presentationDim K A)) K
local notation "I" => RingHom.ker (presentation K A)

/-- The isomorphism of a dagger algebra `A` with the residue algebra
`W_n ⧸ ker (presentation K A)` of the chosen minimal presentation. -/
noncomputable def residueAlgEquiv : A ≃ₐ[K] W ⧸ I :=
  (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm

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
theorem norm_residueAlgEquiv (x : A) :
    letI := residueNormedCommRing K A
    ‖residueAlgEquiv K A x‖ = ‖x‖ :=
  rfl

/-- The residue norm on a dagger algebra is ultrametric. -/
theorem isUltrametricDist_residueNormedCommRing :
    letI := residueNormedCommRing K A
    IsUltrametricDist A :=
  letI := residueNormedCommRing K A
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [← norm_residueAlgEquiv, map_add] using
      IsUltrametricDist.norm_add_le_max (residueAlgEquiv K A x) (residueAlgEquiv K A y)

omit [CompleteSpace K] in
/-- The residue isomorphism sends the image of a series to its quotient class. -/
theorem residueAlgEquiv_presentation (f : W) :
    residueAlgEquiv K A (presentation K A f) = Ideal.Quotient.mk _ f := by
  have h := Ideal.quotientKerAlgEquivOfSurjective_mk (presentation_surjective K A) f
  simp only [residueAlgEquiv, ← h, AlgEquiv.symm_apply_apply]

/-- The residue norm of the image of a series is at most its Gauss norm. -/
theorem norm_presentation_le (f : W) :
    letI := residueNormedCommRing K A
    ‖presentation K A f‖ ≤ ‖f‖ :=
  letI := residueNormedCommRing K A
  by
    have h := Ideal.Quotient.norm_mk_le_norm I f
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

/-- The completion map is contractive: the quotient norm of `τ a` is at most the residue
norm of `a`. -/
theorem norm_toCompletion_le (a : A) :
    letI := residueNormedCommRing K A
    ‖toCompletion K A a‖ ≤ ‖a‖ :=
  letI := residueNormedCommRing K A
  by
  obtain ⟨f, rfl, hf⟩ := exists_presentation_norm_eq K A a
  rw [toCompletion_presentation]
  calc ‖Ideal.Quotient.mk _ (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f)‖
      ≤ ‖washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f‖ :=
        Ideal.Quotient.norm_mk_le_norm _ _
    _ = ‖f‖ := washnitzerAlgebra.norm_toTate f
    _ = ‖presentation K A f‖ := hf

/-- The residue norm is bounded by the norm of the completion: `τ : A → Â` is an isometric
embedding for the residue norm and the quotient Gauss norm of `Â`. -/
theorem residueNorm_le_norm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    ‖a‖ ≤ ‖toCompletion K A a‖ :=
  letI := residueNormedCommRing K A
  by
  set M := ‖toCompletion K A a‖
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- A `T_n`-lift of `τ a` within `ε` of `M`.
  obtain ⟨h, hh, hnorm⟩ := Ideal.Quotient.exists_norm_mk_lt (toCompletion K A a) hε
  -- A series of equal Gauss norm representing `a`.
  obtain ⟨f, hf, _⟩ := exists_presentation_norm_eq K A a
  have heq : Ideal.Quotient.mk
      (Ideal.map (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K) I) h =
      Ideal.Quotient.mk _
        (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f) := by
    rw [← toCompletion_presentation, hf]
    exact hh
  have hmem : h - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f ∈
      Ideal.map (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K) I := by
    rwa [Ideal.Quotient.eq] at heq
  -- `I` is finitely generated; pick a generating set `S`.
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp
    ((isNoetherianRing_iff_ideal_fg W).mp inferInstance I)
  have hmap : Ideal.map (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K) I =
      Ideal.span (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K '' S) := by
    rw [← hS, Ideal.map_span]
  rw [hmap] at hmem
  -- Write the difference as a finite combination of the images of the generators.
  obtain ⟨m, c, s, hsum⟩ := Submodule.mem_span_set'.mp hmem
  -- Choose, for each `s i`, a generator `s₀ i ∈ S` mapping to it, and approximate the
  -- coefficient `c i` by an overconvergent series within `δ`, with `δ` small compared to
  -- `C = ∑ ‖s₀ i‖`.
  set C := ∑ i, ‖(s i).1‖ with hC_def
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  set δ := ε / (1 + C) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδC : δ * C ≤ ε := by
    rw [hδ_def]
    have hle : C ≤ 1 + C := by linarith
    calc ε / (1 + C) * C ≤ ε / (1 + C) * (1 + C) := by gcongr
      _ = ε := by field_simp
  have step : ∀ i : Fin m, ∃ (s₀ : W) (hs₀ : s₀ ∈ S)
      (wᵢ : W), washnitzerAlgebra.toTate (Fin (presentationDim K A)) K s₀ = (s i).1 ∧
        ‖c i - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K wᵢ‖ < δ := by
    intro i
    obtain ⟨s₀, hs₀, htoTate⟩ := (s i).2
    obtain ⟨wᵢ, hwᵢ⟩ := Metric.denseRange_iff.mp washnitzerAlgebra.denseRange_toTate
      (c i) δ hδ
    have hnorm : ‖c i - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K wᵢ‖ < δ := by
      rw [← dist_eq_norm]
      exact hwᵢ
    exact ⟨s₀, hs₀, wᵢ, htoTate, hnorm⟩
  choose s₀ hs₀ w htoTate hw using step
  -- Assemble the overconvergent series `f' = f + ∑ᵢ (w i) * (s₀ i)` representing `a`.
  set f' := f + ∑ i, w i * s₀ i with hf'_def
  have hzero : ∀ i, presentation K A (s₀ i) = 0 := fun i ↦ by
    have hs₀i : s₀ i ∈ I :=
      hS ▸ Submodule.subset_span (hs₀ i)
    exact RingHom.mem_ker.mp hs₀i
  have hf' : presentation K A f' = a := by
    rw [hf'_def, map_add, map_sum, hf]
    have hz : ∀ i, presentation K A (w i * s₀ i) = 0 := fun i ↦ by
      rw [map_mul, hzero i, mul_zero]
    simp [hz]
  -- Bound the defect `h - toTate f'` term by term.
  have hdefect :
      ‖h - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f'‖ ≤ δ * C := by
    have hsub : h - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f' =
        ∑ i, (c i - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i)) *
          (s i).1 := by
      have h1 : washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f' =
          washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f +
            ∑ i, washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i) *
              (s i).1 := by
        rw [hf'_def, map_add, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, htoTate i]
      have h2 : h - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f =
          ∑ i, c i * (s i).1 := by
        rw [← hsum]
        exact Finset.sum_congr rfl fun i _ ↦ smul_eq_mul _ _
      rw [h1, sub_add_eq_sub_sub, h2,
        ← Finset.sum_sub_distrib (fun i ↦ c i * (s i).1)
          (fun i ↦ washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i) * (s i).1)]
      exact Finset.sum_congr rfl fun i _ ↦
        (sub_mul (c i) (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i))
          (s i).1).symm
    rw [hsub]
    calc ‖∑ i, (c i - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i)) *
          (s i).1‖ ≤ ∑ i, ‖(c i - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i)) *
              (s i).1‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i - washnitzerAlgebra.toTate (Fin (presentationDim K A)) K (w i)‖ *
              ‖(s i).1‖ := Finset.sum_le_sum fun i _ ↦ norm_mul_le _ _
      _ ≤ ∑ i, δ * ‖(s i).1‖ := Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_right (hw i).le (norm_nonneg _)
      _ = δ * C := by rw [hC_def, Finset.mul_sum]
  calc ‖a‖ ≤ ‖f'‖ := hf' ▸ norm_presentation_le K A f'
    _ = ‖washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f'‖ :=
        (washnitzerAlgebra.norm_toTate f').symm
    _ = ‖h + (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f' - h)‖ := by
        congr 1; abel
    _ ≤ max ‖h‖ ‖washnitzerAlgebra.toTate (Fin (presentationDim K A)) K f' - h‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max (M + ε) (δ * C) :=
        max_le_max hnorm.le (by rwa [norm_sub_rev])
    _ ≤ M + ε :=
        max_le le_rfl (by have hM : 0 ≤ M := norm_nonneg (toCompletion K A a); linarith [hδC, hM])

/-- The completion map is an isometry for the residue norm on `A` and the quotient Gauss
norm on `Â`. -/
theorem norm_toCompletion (a : A) :
    letI := residueNormedCommRing K A
    ‖toCompletion K A a‖ = ‖a‖ :=
  le_antisymm (norm_toCompletion_le K A a) (residueNorm_le_norm_toCompletion K A a)

/-- The completion map `τ : A → Â` is an isometry. -/
theorem isometry_toCompletion :
    letI := residueNormedCommRing K A
    Isometry (toCompletion K A) :=
  letI := residueNormedCommRing K A
  (AddMonoidHomClass.isometry_iff_norm (E := A) (F := completion K A)
    (toCompletion K A)).mpr
    fun a ↦ norm_toCompletion K A a

end TauCeti.Dagger
