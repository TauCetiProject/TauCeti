/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Fintype.Powerset

/-!
# Antiholomorphic coefficients of alternating maps

`ContinuousAlternatingMap.conjCoeff` evaluates an alternating map on an increasing tuple of
coordinate vectors. For maps of type `(0,k)`, these evaluations determine the map.
`TauCeti.conjCoeffForm` assembles such a map from its coefficients; coefficient extraction and
assembly are inverse on the relevant cardinality and type. Assembly preserves regularity for
coefficients on any real normed parameter space.
-/

public section

open Complex Finset

namespace ContinuousAlternatingMap

section Evaluation

variable {ι : Type*} [LinearOrder ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Evaluation of an alternating map on the increasing coordinate tuple indexed by `J`;
sets of the wrong cardinality give zero. For type `(0,k)` this is its coframe coefficient. -/
noncomputable def conjCoeff {k : ℕ}
    (φ : (ι → ℂ) [⋀^Fin k]→L[ℝ] F) (J : Finset ι) : F :=
  if h : #J = k then φ fun i ↦ Pi.single (J.orderEmbOfFin h i) 1 else 0

/-- Coordinate evaluation on a set of the correct cardinality. -/
theorem conjCoeff_of_card_eq {k : ℕ}
    (φ : (ι → ℂ) [⋀^Fin k]→L[ℝ] F) {J : Finset ι} (hJ : #J = k) :
    φ.conjCoeff J = φ (fun i ↦ Pi.single (J.orderEmbOfFin hJ i) 1) := by
  simp [conjCoeff, hJ]

/-- Coordinate evaluation vanishes for sets of the wrong cardinality. -/
theorem conjCoeff_of_card_ne {k : ℕ}
    (φ : (ι → ℂ) [⋀^Fin k]→L[ℝ] F) {J : Finset ι} (hJ : #J ≠ k) :
    φ.conjCoeff J = 0 := by
  simp [conjCoeff, hJ]

end Evaluation

variable {ι : Type*} [LinearOrder ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- Alternating maps of type `(0,k)` agree when their coordinate coefficients agree. -/
theorem IsOfType.eq_of_conjCoeff_eq [Finite ι] {k : ℕ}
    {φ ψ : (ι → ℂ) [⋀^Fin k]→L[ℝ] F}
    (hφ : φ.IsOfType (I • ContinuousLinearMap.id ℝ (ι → ℂ)) 0 k)
    (hψ : ψ.IsOfType (I • ContinuousLinearMap.id ℝ (ι → ℂ)) 0 k)
    (h : ∀ J, #J = k → φ.conjCoeff J = ψ.conjCoeff J) : φ = ψ := by
  apply sub_eq_zero.1
  refine (hφ.sub hψ).eq_zero_of_forall_apply_orderEmbOfFin fun J hJ ↦ ?_
  rw [ContinuousAlternatingMap.sub_apply, ← φ.conjCoeff_of_card_eq hJ,
    ← ψ.conjCoeff_of_card_eq hJ, h J hJ, sub_self]

end ContinuousAlternatingMap

namespace TauCeti

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F] {k : ℕ}

/-- The alternating map `∑_J a_J d(conj z)_J` on `ι → ℂ`, summed over the sets `J` with `k`
elements, with coefficients `a_J ∈ F`; the entries of `a` at other sets are ignored. It has type
`(0,k)` (`TauCeti.isOfType_conjCoeffForm`) and takes the value `a_J` on the coordinate vectors
indexed by `J` (`TauCeti.conjCoeffForm_apply_orderEmbOfFin`). -/
noncomputable def conjCoeffForm (k : ℕ) (a : Finset ι → F) : (ι → ℂ) [⋀^Fin k]→L[ℝ] F :=
  ∑ J : ((Finset.univ : Finset ι).powersetCard k),
    ((ContinuousLinearMap.lsmul ℝ ℂ).flip (a J)).compContinuousAlternatingMap
      (ContinuousAlternatingMap.conjCoordForm
        (J.val.orderEmbOfFin (Finset.mem_powersetCard_univ.1 J.property)))

/-- The alternating map `∑_J a_J d(conj z)_J` has type `(0,k)`. -/
theorem isOfType_conjCoeffForm (a : Finset ι → F) :
    (conjCoeffForm k a).IsOfType (I • ContinuousLinearMap.id ℝ (ι → ℂ)) 0 k := by
  refine ContinuousAlternatingMap.IsOfType.sum (zero_add k) fun J _ ↦ ?_
  exact (ContinuousAlternatingMap.isOfType_conjCoordForm _).compContinuousAlternatingMap
    fun c x ↦ by simp [smul_smul]

/-- The alternating map `∑_J a_J d(conj z)_J` takes the value `a_J` on the coordinate vectors
indexed by a set `J` with `k` elements, in increasing order. -/
@[simp]
theorem conjCoeffForm_apply_orderEmbOfFin (a : Finset ι → F) {J : Finset ι} (hJ : #J = k) :
    conjCoeffForm k a (fun i ↦ Pi.single (J.orderEmbOfFin hJ i) 1) = a J := by
  classical
  rw [conjCoeffForm, ContinuousAlternatingMap.sum_apply,
    Finset.sum_eq_single ⟨J, Finset.mem_powersetCard_univ.2 hJ⟩]
  · simp [ContinuousAlternatingMap.conjCoordForm_apply_single_self
      (J.orderEmbOfFin hJ).injective]
  · intro K _ hKJ
    have hK := Finset.mem_powersetCard_univ.1 K.property
    have hKJ : K.val ≠ J := fun h ↦ hKJ (Subtype.ext h)
    -- Equal-sized distinct coordinate sets have a vector outside the other set.
    obtain ⟨x, hxJ, hxK⟩ := Finset.not_subset.1 fun hJK ↦
      hKJ (Finset.eq_of_subset_of_card_le hJK (hK.trans hJ.symm).le).symm
    obtain ⟨b, rfl⟩ : x ∈ Set.range (J.orderEmbOfFin hJ) := by
      rwa [Finset.range_orderEmbOfFin]
    have h₀ := ContinuousAlternatingMap.conjCoordForm_apply_single_eq_zero
      (K.val.orderEmbOfFin hK) (f := J.orderEmbOfFin hJ) (a := b)
      (by rwa [Finset.range_orderEmbOfFin])
    simp [h₀]
  · simp

/-- Reading a coefficient of an assembled form recovers the given coefficient. -/
@[simp]
theorem conjCoeff_conjCoeffForm (a : Finset ι → F) {J : Finset ι} (hJ : #J = k) :
    (conjCoeffForm k a).conjCoeff J = a J := by
  rw [ContinuousAlternatingMap.conjCoeff_of_card_eq _ hJ, conjCoeffForm_apply_orderEmbOfFin]

/-- A form of type `(0,k)` is reconstructed from its antiholomorphic coefficients. -/
theorem conjCoeffForm_conjCoeff {φ : (ι → ℂ) [⋀^Fin k]→L[ℝ] F}
    (hφ : φ.IsOfType (I • ContinuousLinearMap.id ℝ (ι → ℂ)) 0 k) :
    conjCoeffForm k φ.conjCoeff = φ := by
  exact (isOfType_conjCoeffForm _).eq_of_conjCoeff_eq hφ
    fun J hJ ↦ conjCoeff_conjCoeffForm _ hJ

/-- Assembling coefficients `u_J` that are `C^n` on a set in any real normed parameter space
into `∑_J u_J d(conj z)_J` gives a field of alternating maps that is `C^n` there. -/
theorem contDiffOn_conjCoeffForm {n : WithTop ℕ∞} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {u : Finset ι → X → F} {s : Set X}
    (hu : ∀ J, #J = k → ContDiffOn ℝ n (u J) s) :
    ContDiffOn ℝ n (fun z ↦ conjCoeffForm k fun J ↦ u J z) s := by
  simp only [conjCoeffForm]
  refine ContDiffOn.sum fun J _ ↦ ?_
  exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ (ι → ℂ) ℂ F (Fin k) ∘L
    (ContinuousLinearMap.lsmul ℝ ℂ).flip).contDiff.comp_contDiffOn
      (hu J (Finset.mem_powersetCard_univ.1 J.property))).clm_apply contDiffOn_const

end TauCeti
