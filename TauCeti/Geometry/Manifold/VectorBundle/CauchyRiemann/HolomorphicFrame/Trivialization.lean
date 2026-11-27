/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HolomorphicFrame.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
import TauCeti.Topology.VectorBundle.RestrictScalars

/-!
# Trivializations defined by holomorphic kernel frames

A nonvanishing smooth kernel section of a complex-linear Cauchy–Riemann operator on a line
bundle defines a complex-linear trivialization in the original total-space topology. Its real
smoothness follows by reading the frame as the real frame consisting of the section and its
multiple by `I`. The resulting trivialization belongs to the original real smooth maximal atlas.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix C.1.
-/

public section

noncomputable section

open Bundle Module Set
open scoped ContDiff Manifold Topology TauCeti.ComplexManifold

namespace TauCeti.IsNonvanishingHolomorphicOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [VectorBundle ℂ F V]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
  {σ : Π x : M, V x} {U : Set M}
  (hσ : IsNonvanishingHolomorphicOn F D σ U) (b : Basis Unit ℂ F)

include hσ b in
private theorem complexFrame : IsLocalFrameOn 𝓘(ℂ, E) F 0 (fun _ : Unit ↦ σ) U :=
  .of_finrank_eq_one (by simpa using finrank_eq_card_basis b)
    (contMDiffOn_zero_iff.2 hσ.contMDiffOn.continuousOn) hσ.ne_zero

/-- The complex-linear trivialization associated with a nonvanishing holomorphic frame and a
basis of the rank-one model. Its topology is the original total-space topology. -/
def trivialization (hU : IsOpen U) : Trivialization F (π F V) :=
  (complexFrame hσ b).trivialization hU b

/-- The trivialization has the domain of the holomorphic frame as its base set. -/
@[simp]
theorem baseSet_trivialization (hU : IsOpen U) : (hσ.trivialization b hU).baseSet = U :=
  (complexFrame hσ b).baseSet_trivialization hU b

/-- The frame trivialization is complex linear on every fibre. -/
instance isLinear_trivialization (hU : IsOpen U) : (hσ.trivialization b hU).IsLinear ℂ :=
  inferInstanceAs (((complexFrame hσ b).trivialization hU b).IsLinear ℂ)

/-- On its domain, the frame trivialization reads the kernel frame as the chosen model basis. -/
@[simp]
theorem trivialization_apply_frame (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    hσ.trivialization b hU ⟨x, σ x⟩ = (x, b ()) :=
  (complexFrame hσ b).trivialization_apply_frame hU b hx ()

/-- On the frame domain, the inverse trivialization reconstructs a vector by its unique
complex coordinate. -/
@[simp]
theorem trivialization_symm_apply (hU : IsOpen U) {x : M} (hx : x ∈ U) (w : F) :
    (hσ.trivialization b hU).symm x w = b.coord () w • σ x := by
  simpa only [trivialization, Fintype.sum_unique, Basis.coord_apply] using
    (complexFrame hσ b).trivialization_symm_apply hU b hx w

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
include hσ b in
private theorem realFrame :
    IsLocalFrameOn 𝓘(ℝ, E) F ∞ (fun i : Fin 2 × Unit ↦ Complex.basisOneI i.1 • σ) U where
  linearIndependent {x} hx := by
    let c := (complexFrame hσ b).toBasisAt hx
    convert (Complex.basisOneI.smulTower c).linearIndependent using 1
    ext i
    simp only [Basis.smulTower_apply, c, IsLocalFrameOn.toBasisAt_coe, Pi.smul_apply]
  generating {x} hx := by
    let c := (complexFrame hσ b).toBasisAt hx
    convert (Complex.basisOneI.smulTower c).span_eq.ge using 1
    congr 2
    ext i
    simp only [Basis.smulTower_apply, c, IsLocalFrameOn.toBasisAt_coe, Pi.smul_apply]
  contMDiffOn i :=
    ContMDiffOn.smul_totalSpace (a := fun _ ↦ Complex.basisOneI i.1)
      contMDiffOn_const hσ.contMDiffOn

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] in
/-- The complex frame trivialization lies in the maximal atlas of the original real smooth
bundle. It therefore changes neither the underlying topology nor the smooth bundle. -/
theorem trivialization_mem_maximalAtlas (hU : IsOpen U) :
    (hσ.trivialization b hU).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear M F 𝓘(ℝ, E) ∞).maximalAtlas (TotalSpace F V) := by
  let e := hσ.trivialization b hU
  let eR := (realFrame hσ b).trivialization hU (Complex.basisOneI.smulTower b)
  let : e.IsLinear ℝ := Trivialization.isLinear_restrictScalars ℝ ℂ e
  refine Trivialization.mem_maximalAtlas_of_eq_on_baseSet (e₁ := e) (e₂ := eR) ?_ ?_ ?_
  · exact (hσ.baseSet_trivialization b hU).trans
      ((realFrame hσ b).baseSet_trivialization hU _).symm
  · intro x hx v
    have hxU : x ∈ U := by simpa only [e, baseSet_trivialization] using hx
    have hxR : x ∈ eR.baseSet := by
      simpa only [eR, IsLocalFrameOn.baseSet_trivialization] using hxU
    have hlin : (e.continuousLinearMapAt ℝ x).toLinearMap =
        (eR.continuousLinearMapAt ℝ x).toLinearMap := by
      apply ((realFrame hσ b).toBasisAt hxU).ext
      intro i
      simp only [IsLocalFrameOn.toBasisAt_coe, Pi.smul_apply, ContinuousLinearMap.coe_coe]
      rw [e.continuousLinearMapAt_apply_of_mem (R := ℝ) hx,
        eR.continuousLinearMapAt_apply_of_mem (R := ℝ) hxR,
        ← e.continuousLinearMapAt_apply_of_mem (R := ℂ) hx, map_smul,
        e.continuousLinearMapAt_apply_of_mem (R := ℂ) hx]
      rw [hσ.trivialization_apply_frame b hU hxU]
      have hr := (realFrame hσ b).trivialization_apply_frame hU
        (Complex.basisOneI.smulTower b) hxU i
      simp only [Pi.smul_apply] at hr
      rw [hr]
      exact (Basis.smulTower_apply _ _ i).symm
    apply Prod.ext
    · exact (e.coe_fst' hx).trans (eR.coe_fst' hxR).symm
    · simpa only [ContinuousLinearMap.coe_coe,
        e.continuousLinearMapAt_apply_of_mem (R := ℝ) hx,
        eR.continuousLinearMapAt_apply_of_mem (R := ℝ) hxR] using
        LinearMap.congr_fun hlin v
  · exact (realFrame hσ b).trivialization_mem_maximalAtlas hU _

end TauCeti.IsNonvanishingHolomorphicOn
