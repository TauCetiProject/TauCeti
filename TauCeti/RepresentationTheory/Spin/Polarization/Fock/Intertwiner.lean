/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Intertwiner
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Spinors
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Unitary polarization independence of the Fock spinor module

For an orthogonal complex structure `J` on a finite-dimensional real inner product space `V` with
`Q v = -‖v‖²`, `TauCeti.AlmostComplexStructure.fockInnerProductSpace` equips the Fock spinor
module `⋀ W` (`W` the holomorphic `i`-eigenspace of `J`) with a canonical Hermitian inner product
under which real Clifford generators act skew-adjointly.

While the carrier `⋀ W` depends on the choice of orthogonal complex structure `J`, this file shows
that the resulting Hermitian Clifford module is **independent of `J` up to a `Circle`-torsor of
unitary intertwiners** — and more generally, for any linear isometry `f : V ≃ₗᵢ[ℝ] V'` between
real inner product spaces carrying orthogonal complex structures `J` and `J'`, the Fock modules of
`J` and `J'` (both on `⋀ W` and on the dedicated Hilbert-space carrier `FockSpinors`) are
intertwined along `f` by a complex linear isometry equivalence, unique up to a phase in `Circle`.

## Main results

* `TauCeti.AlmostComplexStructure.exists_unitary_intertwiner_realFockAction`,
  `TauCeti.AlmostComplexStructure.existsUnique_circle_smul_intertwiner_realFockAction`: existence
  and `Circle`-uniqueness of unitary Fock intertwiners on `⋀ W`.
* `TauCeti.AlmostComplexStructure.exists_unitary_intertwiner_fockSpinorAction`,
  `TauCeti.AlmostComplexStructure.existsUnique_circle_smul_intertwiner_fockSpinorAction`: the same
  on `FockSpinors` equipped with `fockSpinorsNormedAddCommGroup` and `fockSpinorsInnerProductSpace`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module

section Intertwiner

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  (J : AlmostComplexStructure V) (J' : AlmostComplexStructure V')
  {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hQJ' : ∀ v, Q' (J' v) = Q' v) (hQnd' : Q'.Nondegenerate) (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)

/-- **Existence of unitary Fock intertwiners**: for any linear isometry `f : V ≃ₗᵢ[ℝ] V'`, the
native Hermitian Fock spinor modules of `J` and `J'` are intertwined along `f` by a complex linear
isometry equivalence. -/
theorem exists_unitary_intertwiner_realFockAction (f : V ≃ₗᵢ[ℝ] V') :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    letI := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockInnerProductSpace hQJ' hQnd' hQ'
    ∃ U : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W ≃ₗᵢ[ℂ]
        ExteriorAlgebra ℂ (J'.spinPolarizationData hQJ' hQnd').W,
      ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ J.realFockAction hQJ hQnd (ι Q v) =
        J'.realFockAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockInnerProductSpace hQJ' hQnd' hQ'
  have hV : finrank ℝ V = 2 * (finrank ℝ V / 2) :=
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
  have hS' : finrank ℂ (ExteriorAlgebra ℂ (J'.spinPolarizationData hQJ' hQnd').W) =
      2 ^ (finrank ℝ V / 2) := by
    rw [J'.finrank_fock hQJ' hQnd', f.toLinearEquiv.finrank_eq]
  exact exists_unitary_intertwiner_of_finrank_eq hQ hQ' f hV
    (J.adjoint_realFockAction_ι hQJ hQnd hQ) (J'.adjoint_realFockAction_ι hQJ' hQnd' hQ')
    (J.finrank_fock hQJ hQnd) hS'

/-- **Uniqueness of unitary Fock intertwiners up to `Circle`**: any two unitary intertwiners
between the Hermitian Fock modules of `J` and `J'` along a map `f : V → V'` differ by a unique
phase in `Circle`. -/
theorem existsUnique_circle_smul_intertwiner_realFockAction {f : V → V'} :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    letI := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockInnerProductSpace hQJ' hQnd' hQ'
    ∀ U₁ U₂ : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W ≃ₗᵢ[ℂ]
        ExteriorAlgebra ℂ (J'.spinPolarizationData hQJ' hQnd').W,
      (∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ J.realFockAction hQJ hQnd (ι Q v) =
        J'.realFockAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap) →
      (∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ J.realFockAction hQJ hQnd (ι Q v) =
        J'.realFockAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap) →
      ∃! z : Circle, ∀ s, U₂ s = (z : ℂ) • U₁ s := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockInnerProductSpace hQJ' hQnd' hQ'
  intro U₁ U₂ hU₁ hU₂
  have hsurj : Function.Surjective (liftBaseChange ℂ Q (J.realFockAction hQJ hQnd)) := by
    rw [J.liftBaseChange_realFockAction hQJ hQnd]
    exact (J.fockAction_bijective hQJ hQnd).surjective
  exact existsUnique_circle_smul_intertwiner hsurj U₁ U₂ hU₁ hU₂

/-- Along any linear isometry `f : V ≃ₗᵢ[ℝ] V'`, the Hilbert Fock spinor spaces `FockSpinors` of
`J` and `J'` are intertwined by a unitary equivalence. -/
theorem exists_unitary_intertwiner_fockSpinorAction (f : V ≃ₗᵢ[ℝ] V') :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
    ∃ U : J.FockSpinors hQJ hQnd ≃ₗᵢ[ℂ] J'.FockSpinors hQJ' hQnd',
      ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ J.fockSpinorAction hQJ hQnd (ι Q v) =
        J'.fockSpinorAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockInnerProductSpace hQJ' hQnd' hQ'
  obtain ⟨U, hU⟩ := J.exists_unitary_intertwiner_realFockAction J' hQJ hQnd hQ hQJ' hQnd' hQ' f
  refine ⟨(J.fockSpinorsLinearIsometryEquiv hQJ hQnd hQ).trans
    (U.trans (J'.fockSpinorsLinearIsometryEquiv hQJ' hQnd' hQ').symm), fun v ↦ ?_⟩
  ext ψ
  simpa using LinearMap.congr_fun (hU v) ψ.toExterior

/-- Any two unitary intertwiners between `J.FockSpinors` and `J'.FockSpinors` along `f : V → V'`
differ by a unique phase in `Circle`. -/
theorem existsUnique_circle_smul_intertwiner_fockSpinorAction {f : V → V'} :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
    ∀ U₁ U₂ : J.FockSpinors hQJ hQnd ≃ₗᵢ[ℂ] J'.FockSpinors hQJ' hQnd',
      (∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ J.fockSpinorAction hQJ hQnd (ι Q v) =
        J'.fockSpinorAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap) →
      (∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ J.fockSpinorAction hQJ hQnd (ι Q v) =
        J'.fockSpinorAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap) →
      ∃! z : Circle, ∀ ψ, U₂ ψ = (z : ℂ) • U₁ ψ := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
  intro U₁ U₂ hU₁ hU₂
  exact existsUnique_circle_smul_intertwiner
    (J.liftBaseChange_fockSpinorAction_surjective hQJ hQnd) U₁ U₂ hU₁ hU₂

end Intertwiner

end TauCeti.AlmostComplexStructure

end
