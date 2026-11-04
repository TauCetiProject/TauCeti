/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.ContMDiffMap.Hadamard
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The vanishing ideal of a point and its cotangent space

For a point `x` of a smooth real manifold `M`, the smooth real functions vanishing at `x` form an
ideal `I_x` of the ring `C^∞⟮I, M; ℝ⟯`, the kernel of evaluation at `x`. When `x` is an interior
point of a finite-dimensional Hausdorff manifold, the square of `I_x`, the ideal of finite sums of
products of two functions vanishing at `x`, consists exactly of the functions whose value and
differential both vanish at `x`. Consequently, at such a point, the algebraic cotangent space
`I_x / I_x²` is canonically the cotangent space `T_x*M`, the class of `f` going to `df_x`. This is
the scalar foundation of the algebraic description of jets and differential operators.

## Main results

* `TauCeti.smoothVanishingIdeal`: the ideal of smooth real functions vanishing at a point.
* `TauCeti.mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint`: at an interior point of a
  finite-dimensional Hausdorff manifold, `f ∈ I_x²` if and only if `f x = 0` and `df_x = 0`.
* `TauCeti.mem_smoothVanishingIdeal_sq_iff`: the same at every point of a boundaryless manifold.
* `TauCeti.smoothCotangentEquiv`: the real-linear equivalence `I_x / I_x² ≃ T_x*M` sending the
  class of `f` to its differential at `x`.

## Implementation notes

The square is computed by Hadamard's lemma in a chart. Up to a function vanishing near `x`, a
function with vanishing value and differential at `x` is a finite sum of products of localized
coordinate functions and their Hadamard coefficients, all vanishing at `x`. A function vanishing
near `x` is itself the product of a function vanishing at `x` with one minus a bump function.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6.
-/

public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The ideal of smooth real functions on `M` vanishing at `x`: the kernel of evaluation at `x`. -/
def smoothVanishingIdeal (x : M) : Ideal C^∞⟮I, M; ℝ⟯ :=
  RingHom.ker (ContMDiffMap.evalRingHom x)

variable {I}

/-- A smooth function lies in the vanishing ideal at `x` exactly when it vanishes at `x`. -/
@[simp]
theorem mem_smoothVanishingIdeal_iff {x : M} {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ smoothVanishingIdeal I x ↔ f x = 0 :=
  RingHom.mem_ker

/-- A function in the square of the vanishing ideal at `x` vanishes at `x`. -/
theorem apply_eq_zero_of_mem_smoothVanishingIdeal_sq {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ 2) : f x = 0 :=
  mem_smoothVanishingIdeal_iff.mp (Ideal.pow_le_self two_ne_zero hf)

/-- A function in the square of the vanishing ideal at `x` has zero differential at `x`. -/
theorem mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ 2) : mvfderiv I f x = 0 := by
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun g hg h hh ↦ ?_) (fun g h hg hh ↦ ?_)
  · rw [mem_smoothVanishingIdeal_iff] at hg hh
    rw [ContMDiffMap.coe_mul,
      mvfderiv_mul (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
        (h.contMDiff.mdifferentiable (by simp)).mdifferentiableAt,
      hg, hh, zero_smul, zero_smul, add_zero]
  · rw [ContMDiffMap.coe_add,
      mvfderiv_add (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
        (h.contMDiff.mdifferentiable (by simp)).mdifferentiableAt,
      hg, hh, add_zero]

variable (I) in
/-- The differential at `x` of the functions vanishing at `x`, as a real-linear map. -/
private def mvfderivSmoothVanishingIdeal (x : M) :
    smoothVanishingIdeal I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) where
  toFun f := mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x
  map_add' f g := by
    rw [Submodule.coe_add, ContMDiffMap.coe_add,
      mvfderiv_add ((f : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
        ((g : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
  map_smul' c f := by
    rw [Submodule.coe_smul_of_tower, ContMDiffMap.coe_smul, mvfderiv_const_smul_field,
      RingHom.id_apply]

private theorem mvfderivSmoothVanishingIdeal_apply (x : M) (f : smoothVanishingIdeal I x) :
    mvfderivSmoothVanishingIdeal I x f = mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x :=
  rfl

/-- The differential at `x` kills products of two functions vanishing at `x`, so it descends to
the algebraic cotangent space. -/
private theorem mvfderivSmoothVanishingIdeal_mul (x : M) (f g : smoothVanishingIdeal I x) :
    mvfderivSmoothVanishingIdeal I x (f * g) = 0 := by
  rw [mvfderivSmoothVanishingIdeal_apply]
  refine mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq ?_
  rw [sq]
  exact Ideal.mul_mem_mul f.2 g.2

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- A smooth function vanishing on a neighbourhood of `x` lies in the square of the vanishing ideal
at `x`. -/
theorem mem_smoothVanishingIdeal_sq_of_eventuallyEq_zero {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : (f : M → ℝ) =ᶠ[𝓝 x] 0) : f ∈ smoothVanishingIdeal I x ^ 2 := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hf).mem_iff.mp hf
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  have hχ : ⇑χ = b := ContMDiffMap.coeFn_mk _ _
  have hfac : f = (1 - χ) * f := by
    ext y
    by_cases hy : b y = 0
    · simp [hχ, hy]
    · simp [show f y = 0 from hb hy]
  rw [hfac, sq]
  refine Ideal.mul_mem_mul ?_ (mem_smoothVanishingIdeal_iff.mpr hf.eq_of_nhds)
  simp [hχ]

/-- **Hadamard's lemma for the vanishing ideal.** At an interior point `x`, a smooth function whose
value and differential vanish at `x` lies in the square of the vanishing ideal at `x`. -/
theorem mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero {x : M} (hx : I.IsInteriorPoint x)
    {f : C^∞⟮I, M; ℝ⟯} (hf₀ : f x = 0) (hf₁ : mvfderiv I f x = 0) :
    f ∈ smoothVanishingIdeal I x ^ 2 := by
  -- Near `x`, write `f` as a smooth function `g` of a globally smooth localized chart `F`.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨g, hg⟩ := exists_contMDiffMap_comp_eventuallyEq hx F hF f
  have hgF : g (F x) = 0 := hg.eq_of_nhds.symm.trans hf₀
  -- The differential of `g` at `F x` is that of `f` at `x`, since `F` has the chart's differential.
  have hdg (v : TangentSpace I x) : fderiv ℝ g (F x) v = 0 := by
    have hFv : mvfderiv I F x v = v := by
      rw [hF.mvfderiv_eq]
      simp only [mvfderiv, mfderiv_extChartAt_self]
      -- Both tangent identifications are the identity of `E` across type synonyms.
      rfl
    have hgd : DifferentiableAt ℝ g (F x) :=
      (g.contMDiff.contDiff.differentiable (by simp)) (F x)
    have h := mvfderiv_comp_apply_of_differentiableAt hgd
      (F.contMDiff.mdifferentiable (by simp)).mdifferentiableAt v
    rw [← hg.mvfderiv_eq, hf₁, hFv, zero_apply] at h
    exact h.symm
  -- Hadamard's lemma factors `g` through the coordinates of a basis, with coefficients vanishing
  -- at `F x`; pulling back by `F` gives a sum of products of functions vanishing at `x`.
  let b := Module.finBasis ℝ E
  obtain ⟨a, hax, ha⟩ := ContMDiffMap.exists_hadamard_coords g (F x) b
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ b.coord i (F y) - b.coord i (F x),
      ((b.coord i).toContinuousLinearMap.contDiff.contMDiff.comp F.contMDiff).sub contMDiff_const⟩
  have hc (i) (y : M) : c i y = b.coord i (F y) - b.coord i (F x) := rfl
  let p : C^∞⟮I, M; ℝ⟯ := ∑ i, (a i).comp F * c i
  have hp : p ∈ smoothVanishingIdeal I x ^ 2 := by
    refine Ideal.sum_mem _ fun i _ ↦ ?_
    rw [sq]
    refine Ideal.mul_mem_mul ?_ ?_ <;> rw [mem_smoothVanishingIdeal_iff]
    · simpa [hax] using hdg (b i)
    · simp [c]
  -- The remainder `f - p` vanishes near `x`.
  have hfp : f - p ∈ smoothVanishingIdeal I x ^ 2 := by
    refine mem_smoothVanishingIdeal_sq_of_eventuallyEq_zero ?_
    filter_upwards [hg] with y hy
    have hpy : p y = ∑ i, a i (F y) * (b.coord i (F y) - b.coord i (F x)) := by
      simp [p, hc]
    rw [Pi.zero_apply, ContMDiffMap.coe_sub, Pi.sub_apply, hpy, ← ha (F y), hy,
      Function.comp_apply, hgF, sub_zero, sub_self]
  simpa using add_mem hfp hp

/-- At an interior point `x` of a finite-dimensional Hausdorff real manifold, a smooth function is
a finite sum of products of smooth functions vanishing at `x` if and only if its value and its
differential vanish at `x`. -/
theorem mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint {x : M} (hx : I.IsInteriorPoint x)
    (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ 2 ↔ f x = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  rw [← mvfderiv_eq_zero_iff]
  exact ⟨fun hf ↦ ⟨apply_eq_zero_of_mem_smoothVanishingIdeal_sq hf,
      mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq hf⟩,
    fun hf ↦ mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero hx hf.1 hf.2⟩

/-- On a finite-dimensional Hausdorff boundaryless real manifold, a smooth function is a finite sum
of products of smooth functions vanishing at `x` if and only if its value and its differential
vanish at `x`. -/
theorem mem_smoothVanishingIdeal_sq_iff [BoundarylessManifold I M] (x : M)
    (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ 2 ↔ f x = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) f x = 0 :=
  mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint BoundarylessManifold.isInteriorPoint f

/-- **The algebraic cotangent space of a point is the cotangent space.** At an interior point `x`
of a finite-dimensional Hausdorff real manifold, sending a function vanishing at `x` to its
differential at `x` induces a real-linear equivalence `I_x / I_x² ≃ T_x*M`. -/
def smoothCotangentEquiv {x : M} (hx : I.IsInteriorPoint x) :
    (smoothVanishingIdeal I x).Cotangent ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective
    (Ideal.Cotangent.lift (mvfderivSmoothVanishingIdeal I x) (mvfderivSmoothVanishingIdeal_mul x))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro u hu
      obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ u
      rw [Ideal.Cotangent.lift_toCotangent, mvfderivSmoothVanishingIdeal_apply] at hu
      rw [Ideal.toCotangent_eq_zero]
      exact mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero hx
        (mem_smoothVanishingIdeal_iff.mp f.2) hu,
    fun L ↦ by
      -- Realize `L` as the differential of a smooth function vanishing at `x`.
      obtain ⟨f, hf, -, -, hf₀, hf₁⟩ :=
        exists_contMDiff_hasCompactSupport_mvfderiv_eq (I := I) x (0 : ℝ) L Filter.univ_mem
      refine ⟨(smoothVanishingIdeal I x).toCotangent
        ⟨⟨f, hf⟩, mem_smoothVanishingIdeal_iff.mpr hf₀⟩, ?_⟩
      rw [Ideal.Cotangent.lift_toCotangent, mvfderivSmoothVanishingIdeal_apply]
      exact hf₁⟩

/-- The equivalence `I_x / I_x² ≃ T_x*M` sends the class of `f` to the differential `df_x`. -/
@[simp]
theorem smoothCotangentEquiv_toCotangent {x : M} (hx : I.IsInteriorPoint x)
    (f : smoothVanishingIdeal I x) :
    smoothCotangentEquiv hx ((smoothVanishingIdeal I x).toCotangent f) =
      mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x :=
  Ideal.Cotangent.lift_toCotangent _ (mvfderivSmoothVanishingIdeal_mul x) f

end TauCeti
