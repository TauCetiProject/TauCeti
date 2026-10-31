/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Analysis.MvPolynomial.HomogeneousSubmodule
public import TauCeti.Geometry.Manifold.Projectivization.Polynomial
public import TauCeti.Topology.Algebra.Projectivization.ZeroLocus

/-!
# Linearization of projective incidence equations

In a ratio chart of projective space, the equations of the universal incidence variety are
linear in their homogeneous coefficients and polynomial in the affine coordinates. Their joint
derivative is the sum of the spatial Jacobian and evaluation of the coefficient variation.
The latter is always onto: the monomial in the normalized coordinate evaluates to one, in
every degree, including zero. Thus the universal equations are regular even at singular fibers.

The coefficient space here is the native product of homogeneous submodules, with its existing
module topology. Analytic derivative statements use any continuous linear parametrization from
a normed space; in particular they apply to the inverse monomial-coefficient equivalence.
No norm on the polynomial carrier is chosen.

On the kernel of the joint linearization, the projection to coefficients is onto exactly when
the cone Jacobian is onto. This identifies the linear regularity condition for the incidence
projection on the same native projective carrier as its zero loci.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Lecture 14, for the universal incidence
  correspondence and the projective Jacobian criterion.
-/

public section

open MvPolynomial

namespace TauCeti

variable {𝕜 ι : Type*} {n : ℕ} {d : ι → ℕ}

section Equations

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]

/-- The equations in the `i`-th projective ratio chart, viewed as a continuous linear map in
the homogeneous coefficients. The affine coordinate `a` represents `i.insertNth 1 a`. -/
noncomputable def projectiveIncidenceChartEquations (i : Fin (n + 1)) (a : Fin n → 𝕜) :
    (∀ k, homogeneousSubmodule (Fin (n + 1)) 𝕜 (d k)) →L[𝕜] (ι → 𝕜) :=
  ContinuousLinearMap.pi fun k ↦
    ({ toLinearMap := (aeval (i.insertNth 1 a)).toLinearMap.comp
        (homogeneousSubmodule (Fin (n + 1)) 𝕜 (d k)).subtype
       cont := IsModuleTopology.continuous_of_linearMap _ } :
      homogeneousSubmodule (Fin (n + 1)) 𝕜 (d k) →L[𝕜] 𝕜).comp
        (ContinuousLinearMap.proj k)

/-- The incidence equations are evaluation of the dehomogenized equations. -/
@[simp]
theorem projectiveIncidenceChartEquations_apply (i : Fin (n + 1)) (a : Fin n → 𝕜)
    (c : ∀ k, homogeneousSubmodule (Fin (n + 1)) 𝕜 (d k)) :
    projectiveIncidenceChartEquations i a c = fun k ↦ eval a (dehomogenize i (c k :
      MvPolynomial (Fin (n + 1)) 𝕜)) := by
  ext k
  simp [projectiveIncidenceChartEquations, eval_dehomogenize]

/-- Every coefficient variation of the chart equations is realizable, including in degree zero.
The normalized-coordinate monomial in each equation provides a preimage. -/
theorem surjective_projectiveIncidenceChartEquations (i : Fin (n + 1)) (a : Fin n → 𝕜) :
    Function.Surjective (projectiveIncidenceChartEquations (d := d) i a) := by
  intro y
  let m (k : ι) : homogeneousSubmodule (Fin (n + 1)) 𝕜 (d k) :=
    ⟨X i ^ d k, by simpa using (isHomogeneous_X 𝕜 i).pow (d k)⟩
  refine ⟨fun k ↦ y k • m k, ?_⟩
  ext k
  simp [m]

end Equations

variable [NontriviallyNormedField 𝕜]

section Analytic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable (Φ : F →L[𝕜] (∀ k, homogeneousSubmodule (Fin (n + 1)) 𝕜 (d k)))

/-- The universal chart equations are analytic jointly in the spatial and coefficient
coordinates, along any continuous linear parametrization of the coefficients. -/
theorem analyticAt_projectiveIncidenceChartEquations_comp [Fintype ι] (i : Fin (n + 1))
    (z : (Fin n → 𝕜) × F) :
    AnalyticAt 𝕜 (fun q : (Fin n → 𝕜) × F ↦
      projectiveIncidenceChartEquations i q.1 (Φ q.2)) z := by
  apply AnalyticAt.pi
  intro k
  have ha : AnalyticAt 𝕜 (fun q : (Fin n → 𝕜) × F ↦
      i.insertNth (α := fun _ ↦ 𝕜) 1 q.1) z := by
    apply AnalyticAt.pi
    intro j
    refine Fin.succAboveCases i ?_ (fun l ↦ ?_) j
    · simpa using (analyticAt_const (𝕜 := 𝕜) (x := z) (v := (1 : 𝕜)))
    · simpa only [Fin.insertNth_apply_succAbove] using
        (analyticAt_pi_iff.mp (analyticAt_fst (𝕜 := 𝕜) (p := z)) l)
  have h := (analyticAt_eval_homogeneousSubmodule_comp
    ((ContinuousLinearMap.proj k).comp Φ)
    (z.2, i.insertNth 1 z.1)).comp₂ analyticAt_snd ha
  simpa [projectiveIncidenceChartEquations_apply, eval_dehomogenize] using h

/-- The joint derivative consists of the spatial derivative and evaluation of the coefficient
variation. The coefficient term is independent of the base family. -/
theorem hasFDerivAt_projectiveIncidenceChartEquations_comp [Finite ι] (i : Fin (n + 1))
    (a : Fin n → 𝕜) (b : F) :
    HasFDerivAt (fun q : (Fin n → 𝕜) × F ↦
      projectiveIncidenceChartEquations i q.1 (Φ q.2))
      ((fderiv 𝕜 (fun x ↦ projectiveIncidenceChartEquations i x (Φ b)) a).coprod
        ((projectiveIncidenceChartEquations i a).comp Φ)) (a, b) := by
  let := Fintype.ofFinite ι
  have hf := (analyticAt_projectiveIncidenceChartEquations_comp Φ i (a, b)).differentiableAt
  have hleft := fderiv_slice_left hf
  have hlinear : HasFDerivAt (fun y ↦ projectiveIncidenceChartEquations i a (Φ y))
      ((projectiveIncidenceChartEquations i a).comp Φ) b :=
    ((projectiveIncidenceChartEquations i a).comp Φ).hasFDerivAt
  have hright := hlinear.unique (hf.hasFDerivAt.comp b
    (hasFDerivAt_prodMk_right (𝕜 := 𝕜) a b))
  rw [hleft, hright, ContinuousLinearMap.coprod_comp_inl_inr]
  exact hf.hasFDerivAt

/-- The universal chart equations have surjective derivative whenever the coefficient
parametrization is onto. No regularity of the individual fiber is assumed. -/
theorem surjective_fderiv_projectiveIncidenceChartEquations_comp [Finite ι]
    (hΦ : Function.Surjective Φ) (i : Fin (n + 1)) (a : Fin n → 𝕜) (b : F) :
    Function.Surjective (fderiv 𝕜 (fun q : (Fin n → 𝕜) × F ↦
      projectiveIncidenceChartEquations i q.1 (Φ q.2)) (a, b)) := by
  rw [(hasFDerivAt_projectiveIncidenceChartEquations_comp Φ i a b).fderiv]
  intro y
  obtain ⟨c, hc⟩ := surjective_projectiveIncidenceChartEquations (d := d) i a y
  obtain ⟨v, rfl⟩ := hΦ c
  exact ⟨(0, v), by simpa using hc⟩

end Analytic

section Complex

variable (c : ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k))
variable {i : Fin (n + 1)} {L : Projectivization ℂ (Fin (n + 1) → ℂ)}

/-- In the native ratio chart the joint incidence locus is precisely the zero set of the
chart equations, with the coefficient family unchanged. -/
theorem mem_complexProjectiveIncidence_iff_chartEquations_eq_zero
    (hi : L ∈ Projectivization.affineOpen i) :
    (c, L) ∈ complexProjectiveIncidence (n + 1) d ↔
      projectiveIncidenceChartEquations i (Projectivization.affineChart i L) c = 0 := by
  rw [mem_complexProjectiveIncidence,
    mem_complexProjectiveZeroLocus_iff_eval_affineChart
      (fun k ↦ (mem_homogeneousSubmodule _ _).mp (c k).2) hi]
  simp only [_root_.funext_iff, projectiveIncidenceChartEquations_apply, Pi.zero_apply]

/-- At an incidence point, projection of the kernel of the joint chart linearization onto the
native coefficient space is surjective exactly when the cone Jacobian is surjective.
This is the linear regularity criterion for the incidence projection. -/
theorem surjective_parameterProj_projectiveIncidenceChartEquations_iff [Finite ι]
    (hL : (c, L) ∈ complexProjectiveIncidence (n + 1) d)
    (hi : L ∈ Projectivization.affineOpen i) :
    Function.Surjective
      ((fderiv ℂ (fun x ↦ projectiveIncidenceChartEquations i x c)
        (Projectivization.affineChart i L)).parameterProj
          (projectiveIncidenceChartEquations (d := d) i (Projectivization.affineChart i L))) ↔
      Function.Surjective (jacobiMatrixAt (fun k ↦ (c k :
        MvPolynomial (Fin (n + 1)) ℂ)) L.rep).mulVec := by
  have htotal : Function.Surjective
      ((fderiv ℂ (fun x ↦ projectiveIncidenceChartEquations i x c)
        (Projectivization.affineChart i L)).coprod
          (projectiveIncidenceChartEquations (d := d) i (Projectivization.affineChart i L))) := by
    intro y
    obtain ⟨v, hv⟩ := surjective_projectiveIncidenceChartEquations (d := d)
      i (Projectivization.affineChart i L) y
    exact ⟨(0, v), by simpa using hv⟩
  rw [ContinuousLinearMap.parameterProj_surjective_iff _ _ htotal]
  simpa only [projectiveIncidenceChartEquations_apply] using
    surjective_fderiv_eval_dehomogenize_affineChart_iff i
      (fun k ↦ (mem_homogeneousSubmodule _ _).mp (c k).2)
      (mem_complexProjectiveIncidence.mp hL) hi

end Complex

end TauCeti
