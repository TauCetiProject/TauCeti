/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Rat
public import TauCeti.NumberTheory.ComplexMultiplication.ClassFunction
public import TauCeti.NumberTheory.NumberField.CMType.Overlap
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.FieldTheory.IsAlgClosed.Automorphism
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.FieldTheory.Normal.Closure
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Galois descent of the averaged overlap

A CM type determines a rational CM class function on each finite Galois subfield of `ℂ`
containing the images of all embeddings of the CM algebra. Evaluating it on the restriction of
a complex automorphism recovers the conjugacy-averaged overlap of the original type. This
description determines the function on every such subfield and is compatible with refinement.
The resulting element of CM⁰ on the absolute Galois group is `CMType.galoisAverageOverlap`.

## References

* F. Andreatta, E. Z. Goren, B. Howard and K. Madapusi Pera, *Faltings heights of abelian
  varieties with complex multiplication*, Ann. of Math. 187 (2018), Definition 9.1.1.
-/

public section

namespace TauCeti.CMType

variable {E : Type*} [CommRing E] [StarCompCommute E]

/-- On a finite Galois field containing all embedding images there is a unique CM class
function whose pullback to the complex automorphisms is the averaged overlap. -/
theorem existsUnique_averageOverlap_restrictNormal [Finite (E →+* ℂ)] (Φ : CMType E)
    (K : FiniteGaloisIntermediateField ℚ ℂ)
    (hK : ∀ (φ : E →+* ℂ) (x : E), φ x ∈ K.toIntermediateField) :
    ∃! a : CMClassFunction ℚ ((starRingAut : RingAut ℂ).toRatAlgEquiv.restrictNormal K),
      ∀ σ : Gal(ℂ/ℚ), a.val.val (σ.restrictNormal K) = Φ.averageOverlap σ.toRingEquiv := by
  let π := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℂ) K
  have hπ : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective_of_isAlgClosed
  let f : ClassFunction ℚ Gal(ℂ/ℚ) :=
    ⟨fun σ ↦ Φ.averageOverlap σ.toRingEquiv, ClassFunction.mem_iff.mpr
      fun g h ↦ averageOverlap_conj h.toRingEquiv g.toRingEquiv Φ⟩
  have hperiod : π.ker ≤ rightTranslationStabilizer f.val := by
    intro τ hτ
    have hfix := (AlgEquiv.restrictNormal_eq_one_iff K.toIntermediateField τ).mp hτ
    exact mem_rightTranslationStabilizer.mpr fun σ ↦
      averageOverlap_mul_of_forall_comp_eq Φ σ.toRingEquiv
        (τ := τ.toRingEquiv) fun φ ↦ RingHom.ext fun x ↦ hfix _ (hK φ x)
  obtain ⟨a, ha⟩ := (ClassFunction.mem_range_comap_iff f hπ).mpr hperiod
  have heval (σ : Gal(ℂ/ℚ)) : a.val (π σ) = Φ.averageOverlap σ.toRingEquiv :=
    (ClassFunction.comap_apply π a σ).symm.trans
      (congrArg (fun b : ClassFunction ℚ Gal(ℂ/ℚ) ↦ b.val σ) ha)
  let c := (starRingAut : RingAut ℂ).toRatAlgEquiv
  have hamem : a ∈ CMClassFunction ℚ (π c) := by
    refine CMClassFunction.mem_iff.mpr ⟨IsLocallyConstant.of_discrete _, hπ.forall.mpr fun σ ↦ ?_⟩
    rw [← map_mul, ← π.map_one, heval, heval, heval, heval]
    rw [AlgEquiv.toRingEquiv_one, ← RingAut.one_eq_refl, averageOverlap_one,
      RingEquiv.toRingEquiv_toRatAlgEquiv, averageOverlap_starRingAut, add_zero]
    exact averageOverlap_add_averageOverlap_starRingAut_mul Φ σ.toRingEquiv
  refine ⟨⟨a, hamem⟩, heval, fun b hb ↦ ?_⟩
  ext x
  obtain ⟨σ, rfl⟩ := hπ x
  exact (hb σ).trans (heval σ).symm

variable [Algebra ℚ E] [FiniteDimensional ℚ E]
variable (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Algebra Ω ℂ]

/-- The averaged overlap determines a unique element of CM⁰ on the absolute Galois group.
The embedding of the algebraic closure in `ℂ` fixes the restriction map and the complex
conjugation. The algebra of the CM type may be a product. -/
theorem existsUnique_averageOverlap_galois (Φ : CMType E) :
    ∃! a : CMClassFunction ℚ ((starRingAut : RingAut ℂ).toRatAlgEquiv.restrictNormal Ω),
      ∀ σ : Gal(ℂ/ℚ), a.val.val (σ.restrictNormal Ω) = Φ.averageOverlap σ.toRingEquiv := by
  obtain ⟨K, hK⟩ := exists_finiteGaloisIntermediateField_forall_algHom_mem ℚ E ℂ
  have : Finite (E →+* ℂ) := (RingHom.equivRatAlgHom E ℂ).finite_iff.mpr inferInstance
  obtain ⟨a, ha, -⟩ := Φ.existsUnique_averageOverlap_restrictNormal K (fun φ ↦ hK φ.toRatAlgHom)
  -- Embed the finite level in the chosen closure compatibly with its given inclusion in ℂ.
  let ι := IsScalarTower.toAlgHom ℚ Ω ℂ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : K →ₐ[ℚ] Ω := IsAlgClosed.lift
  obtain ⟨s, hs⟩ := (ι.comp j).exists_comp_eq_of_normal K.toIntermediateField.val
  let i := j.comp s.toAlgHom
  have hi : ι.comp i = K.toIntermediateField.val := hs
  let π := i.restrictNormalHom
  have hπ : Continuous π := by
    have : FiniteDimensional ℚ i.fieldRange := i.toLinearMap.finiteDimensional_range
    apply MonoidHom.continuous_of_isOpen_ker
    rw [AlgHom.ker_restrictNormalHom]
    exact IntermediateField.fixingSubgroup_isOpen _
  have hres (σ : Gal(ℂ/ℚ)) : π (σ.restrictNormal Ω) = σ.restrictNormal K := by
    simpa only [π, AlgHom.restrictNormalHom_toAlgHom, hi, IntermediateField.restrictNormalHom_val,
      AlgEquiv.restrictNormalHom_apply_eq_restrictNormal, ι]
      using ι.restrictNormalHom_restrictNormalHom i σ
  have heval (σ : Gal(ℂ/ℚ)) :
      (ClassFunction.comap π a.val).val (σ.restrictNormal Ω) = Φ.averageOverlap σ.toRingEquiv := by
    rw [ClassFunction.comap_apply, hres, ha]
  refine ⟨⟨ClassFunction.comap π a.val, CMClassFunction.comap_mem π hπ ?_⟩, heval, fun b hb ↦ ?_⟩
  · rw [hres]
    exact a.property
  · ext x
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective_of_isAlgClosed (Ω := ℂ) x
    exact (hb σ).trans (heval σ).symm

/-- The conjugacy-averaged overlap of a CM type, as a CM class function on the absolute
Galois group of the rationals. -/
noncomputable def galoisAverageOverlap (Φ : CMType E) :
    CMClassFunction ℚ ((starRingAut : RingAut ℂ).toRatAlgEquiv.restrictNormal Ω) :=
  (existsUnique_averageOverlap_galois Ω Φ).choose

/-- Evaluate the absolute Galois overlap by lifting the automorphism to `ℂ`. -/
@[simp]
theorem galoisAverageOverlap_restrictNormal (Φ : CMType E) (σ : Gal(ℂ/ℚ)) :
    (galoisAverageOverlap Ω Φ).val.val (σ.restrictNormal Ω) = Φ.averageOverlap σ.toRingEquiv :=
  (existsUnique_averageOverlap_galois Ω Φ).choose_spec.1 σ

/-- Each overlap generator vanishes at complex conjugation. -/
theorem galoisAverageOverlap_starRingAut (Φ : CMType E) :
    (galoisAverageOverlap Ω Φ).val.val ((starRingAut : RingAut ℂ).toRatAlgEquiv.restrictNormal Ω) =
      0 := by simp

/-- Each overlap generator is invariant under inversion on the absolute Galois group. -/
@[simp]
theorem galoisAverageOverlap_inv (Φ : CMType E) (g : Gal(Ω/ℚ)) :
    (galoisAverageOverlap Ω Φ).val.val g⁻¹ = (galoisAverageOverlap Ω Φ).val.val g := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective_of_isAlgClosed (Ω := ℂ) g
  rw [← map_inv]
  simp only [AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
    galoisAverageOverlap_restrictNormal, AlgEquiv.aut_inv, AlgEquiv.symm_toRingEquiv]
  exact averageOverlap_inv Φ σ.toRingEquiv

end TauCeti.CMType
