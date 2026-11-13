/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Limits of Floer solutions in a manifold

Let maps `u i` into a manifold `M` solve the Floer equation `(du - X_K)^{0,1} = 0` at points
`z i → z₀`, for a domain-dependent almost complex structure `J(z, x)` on `T_x M`. If their
derivatives converge in the tangent bundle to the derivative of a map `v`, the Hamiltonian vector
fields of `K` are continuous into the tangent bundle, and `J` is continuous in tangent coordinates,
then `v` solves the Floer equation at `z₀`. On a manifold there is no norm on the derivatives
without a choice of metric, so convergence is convergence in the tangent bundle, and the passage to
the limit is read in a trivialization of the tangent bundle at the limit point.

## Main results

* `TauCeti.isComplexLinearMap_of_tendsto_tangentBundle`: tangent-bundle limits of complex-linear
  maps are complex linear, for structures continuous in tangent coordinates.
* `SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto`: a map whose derivative is the
  limit in the tangent bundle of derivatives of Floer solutions is a Floer solution, for
  structures continuous in tangent coordinates.
-/

public section

open Filter Function Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Limits of complex-linear maps in the tangent bundle are complex linear.** Let real-linear
maps `A i : ℝ × ℝ → T_(x i) M` be complex linear for structures `J(z i, x i)`, where `J(z, x)` is a
domain-dependent structure on `T_x M` and `z i → z₀`. If the values `A i e` converge in the tangent
bundle to `L e`, for a linear map `L : ℝ × ℝ → T_(x₀) M`, and `J` is continuous at `(z₀, x₀)` in the
tangent coordinates at `x₀`, then `L` is complex linear for `J(z₀, x₀)`. This is the coordinate
argument shared by `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_tendsto` and
`TauCeti.SmoothTwoForm.isComplexLinearMap_of_tendsto_rescale`
(`TauCeti/Geometry/Symplectic/Floer/Rescaling/Manifold.lean`), where it was first given for
rescaled maps. -/
theorem _root_.TauCeti.isComplexLinearMap_of_tendsto_tangentBundle [FiniteDimensional ℝ E]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {z : ι → ℝ × ℝ}
    {z₀ : ℝ × ℝ} {x : ι → M} {x₀ : M} {A : (i : ι) → ℝ × ℝ →L[ℝ] TangentSpace I (x i)}
    {L : ℝ × ℝ →L[ℝ] TangentSpace I x₀} (hz : Tendsto z l (𝓝 z₀))
    (hA : ∀ e, Tendsto (fun i ↦ (⟨x i, A i e⟩ : TangentBundle I M)) l (𝓝 ⟨x₀, L e⟩))
    (hJ : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ p.2 x₀ p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z₀, x₀))
    (hsol : ∀ᶠ i in l, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z i) (x i))
      (A i).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z₀ x₀) L.toLinearMap := by
  set T := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ x₀
  have hx : Tendsto x l (𝓝 x₀) := ((T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hA 0)).1
  have hbase : ∀ᶠ i in l, x i ∈ T.baseSet := hx (T.open_baseSet.mem_nhds hx₀)
  -- In coordinates, the maps `A i` converge to `L`, and the structures along the sequence converge
  -- to `J z₀ x₀`.
  have hP (e : ℝ × ℝ) := ((T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hA e)).2
  have h := (isBoundedBilinearMap_apply.continuous.tendsto _).comp
    ((hJ.tendsto.comp (hz.prodMk_nhds hx)).prodMk_nhds (hP stdComplexLineReal))
  -- Pass to the limit in `A i (0, 1) = J_i (A i (1, 0))`, read in coordinates, where the
  -- coordinate expression of `J_i` acts on coordinates of vectors as `J_i` on the vectors.
  have hlim : T.continuousLinearMapAt ℝ x₀ (L stdComplexLineImag) =
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x₀ x₀ x₀
        (J z₀ x₀).toLinearMap.toContinuousLinearMap
        (T.continuousLinearMapAt ℝ x₀ (L stdComplexLineReal)) :=
    tendsto_nhds_unique (hP stdComplexLineImag) (h.congr' ((hsol.and hbase).mono
      fun i ⟨hi, hb⟩ ↦ ?_))
  · rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, Bundle.Trivialization.symmL_continuousLinearMapAt _ hx₀]
      at hlim
    rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe]
    rw [← T.coe_continuousLinearEquivAt_eq hx₀] at hlim
    exact (T.continuousLinearEquivAt ℝ x₀ hx₀).injective hlim
  · rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe] at hi
    simp only [comp_apply]
    rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, Bundle.Trivialization.symmL_continuousLinearMapAt _ hb, hi]
    rfl

/-- **Limits of Floer solutions are Floer solutions.** Let maps `u i` solve the Floer equation
`(du - X_K)^{0,1} = 0` at points `z i → z₀`, for a domain-dependent structure `J(z, x)` on
`T_x M`, and let their derivatives at `z i` converge in the tangent bundle to the derivative of a
map `v` at `z₀`. If the Hamiltonian vector fields of `K` are continuous at `(z₀, v z₀)` as maps
into the tangent bundle, and `J` is continuous at `(z₀, v z₀)` in the tangent coordinates at
`v z₀`, then `v` solves the Floer equation at `z₀`. The perturbed derivatives converge by
`TauCeti.SmoothTwoForm.tendsto_perturbedMFDeriv`, and the coordinate argument is
`TauCeti.isComplexLinearMap_of_tendsto_tangentBundle`, adapted from
`TauCeti.SmoothTwoForm.isComplexLinearMap_of_tendsto_rescale`. -/
theorem isComplexLinearMap_perturbedMFDeriv_of_tendsto (ω : SmoothTwoForm I M)
    [FiniteDimensional ℝ E] {Ks Kt : ℝ × ℝ → M → ℝ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → ℝ × ℝ → M} {z : ι → ℝ × ℝ} {z₀ : ℝ × ℝ} {v : ℝ × ℝ → M}
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hz : Tendsto z l (𝓝 z₀))
    (hdu : ∀ e, Tendsto (fun i ↦ (⟨u i (z i), mfderiv 𝓘(ℝ, ℝ × ℝ) I (u i) (z i) e⟩ :
      TangentBundle I M)) l (𝓝 ⟨v z₀, mfderiv 𝓘(ℝ, ℝ × ℝ) I v z₀ e⟩))
    (hJ : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) (v z₀) p.2 (v z₀)
        p.2 (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z₀, v z₀))
    (hXs : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (z₀, v z₀))
    (hXt : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (z₀, v z₀))
    (hsol : ∀ᶠ i in l, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (z i) (u i (z i))) (ω.perturbedMFDeriv Ks Kt (u i) (z i)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z₀ (v z₀))
      (ω.perturbedMFDeriv Ks Kt v z₀).toLinearMap :=
  isComplexLinearMap_of_tendsto_tangentBundle hz
    (fun e ↦ by
      rw [perturbedMFDeriv_apply ω Ks Kt v z₀ e]
      exact ω.tendsto_perturbedMFDeriv hz hdu hXs hXt e) hJ hsol

end TauCeti.SmoothTwoForm
