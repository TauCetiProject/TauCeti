/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Totally real subspaces of complex modules

This file gives an elementary example of a totally real real subspace of a complex module and
develops the complex-linear algebra of maximal totally real subspaces. A real basis of such a
subspace is a complex basis of the ambient space. Complex-linear automorphisms act transitively on
these subspaces, and an endomorphism preserving one has real determinant.

## Main declarations

* `TauCeti.IsTotallyReal.linearIndependent_complex`: real-linearly independent vectors of a
  totally real subspace are complex-linearly independent.
* `TauCeti.IsMaximalTotallyReal.complexBasis`: a real basis of a maximal totally real subspace,
  as a complex basis of the ambient space.
* `TauCeti.IsMaximalTotallyReal.det_eq_det_restrict`: a complex-linear map preserving a maximal
  totally real subspace has the same (real) determinant as its restriction.
* `TauCeti.IsMaximalTotallyReal.exists_linearEquiv_map_eq`: complex-linear automorphisms act
  transitively on maximal totally real subspaces.
-/

public section

namespace TauCeti

open Module

variable {ι : Type*}

/-- **The real span of vectors, one in each coordinate, is totally real.** The image of the
real-linear map `τ ↦ (τ i • v i)ᵢ` from `ι → ℝ` to `ι → ℂ` meets its image under multiplication by
`i` only in `0`. -/
theorem isTotallyReal_range_pi_smulRight {v : ι → ℂ} :
    IsTotallyReal ((LinearMap.lsmul ℂ (ι → ℂ) Complex.I).restrictScalars ℝ)
      (LinearMap.range (LinearMap.pi fun i => (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight
        (v i))) := by
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  rintro _ ⟨τ, rfl⟩ ⟨_, ⟨σ, rfl⟩, hσ⟩
  funext i
  have h := congrFun hσ i
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, LinearMap.pi_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply, Complex.real_smul,
    smul_eq_mul] at h ⊢
  by_cases hi : v i = 0
  · simp [hi]
  · have h' : (σ i : ℂ) * Complex.I = τ i := mul_right_cancel₀ hi (by rw [← h]; ring)
    have hτ : τ i = 0 := by simpa using (congrArg Complex.re h').symm
    simp [hτ]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  {L : Submodule ℝ E}

/-- Vectors of a totally real subspace of a complex module that are linearly independent over `ℝ`
are linearly independent over `ℂ`. -/
theorem IsTotallyReal.linearIndependent_complex
    (hL : IsTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L) {ι : Type*}
    {v : ι → E} (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L) : LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hsum i hi
  -- Split `∑ gⱼ vⱼ` into `a + i b` with `a, b ∈ L`; total reality forces `a = b = 0`.
  set a : E := ∑ j ∈ s, (g j).re • v j
  set b : E := ∑ j ∈ s, (g j).im • v j
  have hsplit : ∑ j ∈ s, g j • v j = a + Complex.I • b := by
    simp only [a, b, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
      ← add_smul, mul_comm]
    simp
  have hb : b ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hvL j)
  have hab : a = -(Complex.I • b) := eq_neg_of_add_eq_zero_left (hsplit ▸ hsum)
  have ha0 : a = 0 := by
    refine Submodule.disjoint_def.1 hL.disjoint a (L.sum_mem fun j _ => L.smul_mem _ (hvL j)) ?_
    rw [hab]
    exact Submodule.neg_mem _ ⟨b, hb, rfl⟩
  have hb0 : b = 0 := by
    rw [ha0, zero_eq_neg, smul_eq_zero] at hab
    exact hab.resolve_left Complex.I_ne_zero
  exact Complex.ext (hv s _ ha0 i hi) (hv s _ hb0 i hi)

namespace IsMaximalTotallyReal

variable (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
include hL

/-- Vectors spanning a maximal totally real subspace over `ℝ` span the ambient complex module over
`ℂ`. -/
theorem span_complex_eq_top {ι : Type*} {v : ι → E} (hv : Submodule.span ℝ (Set.range v) = L) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  have hle : L ≤ (Submodule.span ℂ (Set.range v)).restrictScalars ℝ :=
    hv ▸ Submodule.span_le_restrictScalars ℝ ℂ _
  have hJle : L.map ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) ≤
      (Submodule.span ℂ (Set.range v)).restrictScalars ℝ := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem _ Complex.I (hle hx)
  rw [← Submodule.restrictScalars_eq_top_iff ℝ, eq_top_iff, ← hL.sup_eq_top]
  exact sup_le hle hJle

/-- A real basis of a maximal totally real subspace `L` of a complex module `E` is a complex basis
of `E`: `L` is a real form of `E`. -/
noncomputable def complexBasis {ι : Type*} (b : Basis ι ℝ L) : Basis ι ℂ E :=
  Basis.mk (v := L.subtype ∘ b)
    (hL.isTotallyReal.linearIndependent_complex
      (b.linearIndependent.map' L.subtype L.ker_subtype) fun i => (b i).2)
    (hL.span_complex_eq_top (by
      rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top])).ge

@[simp]
theorem complexBasis_apply {ι : Type*} (b : Basis ι ℝ L) (i : ι) :
    hL.complexBasis b i = b i :=
  Basis.mk_apply _ _ _

/-- The complex coordinates of a vector of `L` in `complexBasis b` are its real coordinates in
`b`. -/
@[simp]
theorem complexBasis_repr_coe {ι : Type*} (b : Basis ι ℝ L) (x : L) (i : ι) :
    (hL.complexBasis b).repr x i = b.repr x i := by
  have h : ((hL.complexBasis b).repr.toLinearMap.restrictScalars ℝ).comp L.subtype =
      (Finsupp.mapRange.linearMap Complex.ofRealAm.toLinearMap).comp b.repr.toLinearMap :=
    b.ext fun j => by
      have hj := (hL.complexBasis b).repr_self j
      rw [complexBasis_apply] at hj
      simp [hj]
  simpa using DFunLike.congr_fun (LinearMap.congr_fun h x) i

/-- A complex-linear automorphism maps maximal totally real subspaces to maximal totally real
subspaces. -/
theorem map_linearEquiv (A : E ≃ₗ[ℂ] E) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
      (L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ)) := by
  have hcomm : ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ).comp
      ((A : E →ₗ[ℂ] E).restrictScalars ℝ) =
        ((A : E →ₗ[ℂ] E).restrictScalars ℝ).comp
          ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) :=
    LinearMap.ext fun x => (A.map_smul Complex.I x).symm
  rw [isMaximalTotallyReal_iff, ← Submodule.map_comp, hcomm, Submodule.map_comp]
  exact Submodule.isCompl_map (A.restrictScalars ℝ) hL.isCompl

variable [FiniteDimensional ℂ E]

/-- A maximal totally real subspace has real dimension equal to the complex dimension of the
ambient module. -/
theorem finrank_eq_finrank_complex : finrank ℝ L = finrank ℂ E := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  rw [finrank_eq_card_basis (hL.complexBasis (Module.finBasis ℝ L)), Fintype.card_fin]

/-- A complex-linear endomorphism `f` preserving a maximal totally real subspace `L` is the
complexification of its restriction to `L`, so its determinant is the (real) determinant of that
restriction. -/
theorem det_eq_det_restrict (f : E →ₗ[ℂ] E) (hf : ∀ x ∈ L, f x ∈ L) :
    LinearMap.det f = ((LinearMap.det ((f.restrictScalars ℝ).restrict hf) : ℝ) : ℂ) := by
  classical
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  let b := Module.finBasis ℝ L
  rw [← LinearMap.det_toMatrix (hL.complexBasis b), ← LinearMap.det_toMatrix b]
  refine ((Complex.ofRealHom.map_det _).trans (congrArg Matrix.det ?_)).symm
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, complexBasis_apply]
  exact (hL.complexBasis_repr_coe b ((f.restrictScalars ℝ).restrict hf (b j)) i).symm

/-- The complex-linear automorphisms act transitively on the maximal totally real subspaces of a
finite-dimensional complex module. -/
theorem exists_linearEquiv_map_eq {L' : Submodule ℝ E}
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L') :
    ∃ A : E ≃ₗ[ℂ] E, L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ) = L' := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have hspan {K : Submodule ℝ E} (c : Basis (Fin (finrank ℂ E)) ℝ K) :
      Submodule.span ℝ (Set.range (K.subtype ∘ c)) = K := by
    rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
  let b := Module.finBasisOfFinrankEq ℝ L hL.finrank_eq_finrank_complex
  let b' := Module.finBasisOfFinrankEq ℝ L' hL'.finrank_eq_finrank_complex
  obtain ⟨A, hA⟩ : ∃ A : E ≃ₗ[ℂ] E, ∀ i, A (b i) = b' i :=
    ⟨(hL.complexBasis b).equiv (hL'.complexBasis b') (Equiv.refl _), fun i => by
      simpa using (hL.complexBasis b).equiv_apply i (hL'.complexBasis b') (Equiv.refl _)⟩
  refine ⟨A, ?_⟩
  rw [← hspan b, Submodule.map_span, ← Set.range_comp, ← hspan b']
  congr 2
  funext i
  exact hA i

end IsMaximalTotallyReal

end TauCeti
