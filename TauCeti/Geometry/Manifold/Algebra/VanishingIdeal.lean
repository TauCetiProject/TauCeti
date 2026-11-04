/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.DerivationBundle
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# The vanishing ideal of a point and the algebraic cotangent space

For a point `x` of a smooth real manifold `M`, the smooth functions vanishing at `x` form the
ideal `I_x = smoothVanishingIdeal x` of the algebra `C^∞⟮I, M; ℝ⟯`, the kernel of evaluation at `x`.
Its square `I_x ^ 2` consists of the finite sums of products of two functions vanishing at `x`.

At an interior point of a finite-dimensional Hausdorff manifold, a smooth function lies in `I_x ^ 2`
exactly when it vanishes at `x` together with its differential. Near `x` the function is read in a
chart and factored by Hadamard's lemma through the centred coordinate functions, with coefficients
the partial derivatives; a bump function equal to `1` near `x` turns this local factorization into
a global one, since a function vanishing near `x` is the product of itself with `1 - χ`.

Consequently the algebraic cotangent space `I_x / I_x ^ 2` (Mathlib's `Ideal.Cotangent`) is the
cotangent space `T_x*M`, the class of `f ∈ I_x` corresponding to its differential `df_x`. This is
the algebraic description of covectors used to define differential operators and their symbols
through iterated commutators with multiplication operators.

## Main definitions and results

* `TauCeti.smoothVanishingIdeal`: the ideal of smooth real functions vanishing at a point.
* `TauCeti.sub_mem_smoothVanishingIdeal_sq_of_eventuallyEq`: two smooth functions with the same
  germ at `x` are congruent modulo `I_x ^ 2`.
* `TauCeti.mem_smoothVanishingIdeal_sq_iff`: at an interior point, `f ∈ I_x ^ 2` if and only if
  `f x = 0` and `df_x = 0`.
* `TauCeti.smoothCotangentEquiv`: the real-linear equivalence `I_x / I_x ^ 2 ≃ T_x*M` sending the
  class of `f` to `df_x`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §§1.3–1.6.
-/

public noncomputable section

open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The ideal of smooth real functions on `M` vanishing at the point `x`, the kernel of evaluation
at `x`. -/
def smoothVanishingIdeal (x : M) : Ideal C^∞⟮I, M; ℝ⟯ :=
  RingHom.ker (ContMDiffMap.evalRingHom x)

/-- A smooth function lies in the vanishing ideal of `x` exactly when it vanishes at `x`. -/
@[simp]
theorem mem_smoothVanishingIdeal {x : M} {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ smoothVanishingIdeal x ↔ f x = 0 :=
  RingHom.mem_ker

/-- The vanishing ideal of `x` is the kernel of evaluation at `x`. -/
theorem smoothVanishingIdeal_eq_ker (x : M) :
    smoothVanishingIdeal (I := I) x = RingHom.ker (ContMDiffMap.evalRingHom x) :=
  (rfl)

/-- A smooth function in the square of the vanishing ideal of `x` has zero differential at `x`. -/
theorem mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal x ^ 2) : mvfderiv I f x = 0 := by
  rw [pow_two] at hf
  -- Induct over sums of products of two functions vanishing at `x`.
  refine Submodule.mul_induction_on (C := fun g : C^∞⟮I, M; ℝ⟯ ↦ mvfderiv I g x = 0) hf
    (fun a ha c hc ↦ ?_) (fun a c ha hc ↦ ?_)
  · rw [mem_smoothVanishingIdeal] at ha hc
    rw [ContMDiffMap.coe_mul, mvfderiv_mul (a.contMDiff.mdifferentiableAt (by simp))
      (c.contMDiff.mdifferentiableAt (by simp)), ha, hc, zero_smul, zero_smul, add_zero]
  · rw [ContMDiffMap.coe_add, mvfderiv_add (a.contMDiff.mdifferentiableAt (by simp))
      (c.contMDiff.mdifferentiableAt (by simp)), ha, hc, add_zero]

/-- The differential at `x` of the functions vanishing at `x`, as a real-linear map. -/
private def vanishingIdealMvfderiv (x : M) :
    smoothVanishingIdeal (I := I) x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) where
  toFun f := mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x
  map_add' f g := by
    rw [Submodule.coe_add, ContMDiffMap.coe_add]
    exact mvfderiv_add ((f : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiableAt (by simp))
      ((g : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiableAt (by simp))
  map_smul' c f := by
    rw [Submodule.coe_smul_of_tower, ContMDiffMap.coe_smul]
    exact mvfderiv_const_smul_field (f : M → ℝ) x c

private theorem vanishingIdealMvfderiv_apply (x : M) (f : smoothVanishingIdeal (I := I) x) :
    vanishingIdealMvfderiv x f = mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x :=
  rfl

/-- The differential at `x` vanishes on products of two functions vanishing at `x`. -/
private theorem vanishingIdealMvfderiv_mul (x : M) (f g : smoothVanishingIdeal (I := I) x) :
    vanishingIdealMvfderiv x (f * g) = 0 := by
  rw [vanishingIdealMvfderiv_apply]
  refine mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul f.2 g.2

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- Two smooth functions with the same germ at `x` are congruent modulo the square of the vanishing
ideal of `x`: their difference is the product of itself with `1 - χ`, for a bump function `χ` at
`x` supported where the two functions agree. -/
theorem sub_mem_smoothVanishingIdeal_sq_of_eventuallyEq {x : M} {f g : C^∞⟮I, M; ℝ⟯}
    (hfg : (f : M → ℝ) =ᶠ[𝓝 x] g) : f - g ∈ smoothVanishingIdeal x ^ 2 := by
  have hs : {y | f y = g y} ∈ 𝓝 x := hfg
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.mp hs
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  have hχ (y : M) : (1 - χ) y = 1 - b y := by
    rw [ContMDiffMap.coe_sub, ContMDiffMap.coe_one, Pi.sub_apply, Pi.one_apply]
    -- The bundled bump function evaluates as `b` itself (`ContMDiffMap.coeFn_mk`).
    rfl
  have hprod : (1 - χ) * (f - g) = f - g := by
    ext y
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, hχ]
    by_cases hy : b y = 0
    · rw [hy, sub_zero, one_mul]
    · have hyfg : f y = g y := hb hy
      simp [hyfg]
  rw [← hprod, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · rw [mem_smoothVanishingIdeal, hχ, b.eventuallyEq_one.eq_of_nhds, Pi.one_apply, sub_self]
  · simp [hfg.eq_of_nhds]

/-- **Hadamard's lemma on a manifold.** At an interior point `x` of a finite-dimensional Hausdorff
manifold, a smooth function vanishing at `x` together with its differential is a finite sum of
products of two smooth functions vanishing at `x`. -/
theorem mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero {x : M} (hx : I.IsInteriorPoint x)
    {f : C^∞⟮I, M; ℝ⟯} (hf₀ : f x = 0) (hf₁ : mvfderiv I f x = 0) :
    f ∈ smoothVanishingIdeal x ^ 2 := by
  -- Near `x`, read `f` as `g ∘ F` for a globally smooth map `F` with the germ of the chart.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨g, hg⟩ := exists_contMDiffMap_comp_eventuallyEq hx F hF f
  have hgx : g (F x) = 0 := hg.eq_of_nhds.symm.trans hf₀
  -- The chart has identity differential, so the differential of `g` at `F x` is `df_x = 0`.
  have hdg : fderiv ℝ g (F x) = 0 := by
    ext w
    -- `TangentSpace I x` is the model space `E` as a type synonym.
    let v : TangentSpace I x := w
    have hF' : mvfderiv I F x v = w := by
      rw [mvfderiv_apply_eq_mfderiv_apply, hF.mfderiv_eq, mfderiv_extChartAt_self]
      -- What remains is the identity followed by `tangentSpaceCast`, which identifies two
      -- tangent spaces of the model space that are both `E` itself.
      rfl
    have hcomp := mvfderiv_comp_apply_of_differentiableAt
      (g.contMDiff.contDiff.differentiable (by simp) (F x))
      (F.contMDiff.mdifferentiableAt (by simp)) v
    rw [hF', ← hg.mvfderiv_eq, hf₁] at hcomp
    exact hcomp.symm
  -- Hadamard's lemma for `g` at `F x` in the coordinates of a basis `b`, pulled back along `F`.
  let b := Module.finBasis ℝ E
  obtain ⟨a, hax, ha⟩ := g.exists_hadamard_coords (F x) b
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ b.coord i (F y), (b.coord i).toContinuousLinearMap.contDiff.contMDiff.comp F.contMDiff⟩
  -- The pulled-back identity holds pointwise by `ha`, as the bundled compositions evaluate as
  -- the composed functions (`ContMDiffMap.comp_apply`, `ContMDiffMap.coeFn_mk`).
  have hfactor := sub_algebraMap_eq_sum_mul_sub_algebraMap x (g.comp F) (fun i ↦ (a i).comp F) c
    fun y ↦ ha (F y)
  rw [show g.comp F x = 0 from hgx, map_zero, sub_zero] at hfactor
  have hgF : g.comp F ∈ smoothVanishingIdeal x ^ 2 := by
    rw [hfactor]
    refine Ideal.sum_mem _ fun i _ ↦ ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ ?_
    · simp [hax, hdg]
    · simp [Algebra.algebraMap_eq_smul_one]
  simpa using add_mem (sub_mem_smoothVanishingIdeal_sq_of_eventuallyEq (g := g.comp F) hg) hgF

/-- At an interior point `x` of a finite-dimensional Hausdorff manifold, a smooth function lies in
the square of the vanishing ideal of `x` exactly when it vanishes at `x` together with its
differential. -/
@[simp]
theorem mem_smoothVanishingIdeal_sq_iff {x : M} (hx : I.IsInteriorPoint x)
    {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ smoothVanishingIdeal x ^ 2 ↔ f x = 0 ∧ mvfderiv I f x = 0 := by
  refine ⟨fun hf ↦ ⟨?_, mvfderiv_eq_zero_of_mem_smoothVanishingIdeal_sq hf⟩,
    fun hf ↦ mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero hx hf.1 hf.2⟩
  exact mem_smoothVanishingIdeal.mp (Ideal.pow_le_self two_ne_zero hf)

/-- **The algebraic cotangent space is the cotangent space.** At an interior point `x` of a
finite-dimensional Hausdorff manifold, the quotient `I_x / I_x ^ 2` of the vanishing ideal of `x`
is real-linearly equivalent to `T_x*M`, the class of `f ∈ I_x` going to its differential `df_x`. -/
def smoothCotangentEquiv (x : M) (hx : I.IsInteriorPoint x) :
    (smoothVanishingIdeal (I := I) x).Cotangent ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective
    (Ideal.Cotangent.lift (vanishingIdealMvfderiv x) (vanishingIdealMvfderiv_mul x)) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_,
      (Ideal.Cotangent.lift_surjective_iff _ _).mpr fun L ↦ ?_⟩
    · -- A class with zero differential is represented by an element of `I_x ^ 2`.
      obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ c
      rw [Ideal.Cotangent.lift_toCotangent, vanishingIdealMvfderiv_apply] at hc
      exact (Ideal.toCotangent_eq_zero _ f).mpr
        (mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero hx (mem_smoothVanishingIdeal.mp f.2) hc)
    · -- Every covector is the differential of a smooth function vanishing at `x`.
      obtain ⟨f, hf, -, -, hfx, hdf⟩ :=
        exists_contMDiff_hasCompactSupport_mvfderiv_eq (I := I) x (0 : ℝ) L Filter.univ_mem
      refine ⟨⟨⟨f, hf⟩, mem_smoothVanishingIdeal.mpr hfx⟩, ?_⟩
      rw [vanishingIdealMvfderiv_apply]
      exact hdf

/-- The equivalence `I_x / I_x ^ 2 ≃ T_x*M` sends the class of `f` to its differential at `x`. -/
@[simp]
theorem smoothCotangentEquiv_toCotangent (x : M) (hx : I.IsInteriorPoint x)
    (f : smoothVanishingIdeal (I := I) x) :
    smoothCotangentEquiv x hx ((smoothVanishingIdeal x).toCotangent f) =
      mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x := by
  rw [smoothCotangentEquiv]
  exact (LinearEquiv.ofBijective_apply _ _).trans
    ((Ideal.Cotangent.lift_toCotangent _ _ f).trans (vanishingIdealMvfderiv_apply x f))

end TauCeti
