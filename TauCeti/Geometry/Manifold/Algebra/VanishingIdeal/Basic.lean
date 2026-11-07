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
* `TauCeti.mem_smoothVanishingIdeal_pow_succ_of_iteratedFDeriv_eq_zero`: Hadamard's lemma of order
  `m`; at an interior point, a function whose chart expression has vanishing derivatives of every
  order at most `m` lies in `I_x ^ (m + 1)`.
* `TauCeti.mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint`: at an interior point of a
  finite-dimensional Hausdorff manifold, `f ∈ I_x²` if and only if `f x = 0` and `df_x = 0`.
* `TauCeti.mem_smoothVanishingIdeal_sq_iff`: the same at every point of a boundaryless manifold.
* `TauCeti.smoothCotangentEquiv`: the real-linear equivalence `I_x / I_x² ≃ T_x*M` sending the
  class of `f` to its differential at `x`.

## Implementation notes

The powers of `I_x` are reached by Taylor's formula in a chart. Up to a function vanishing near
`x`, a function whose chart expression has vanishing derivatives of order at most `m` at the image
of `x` is a finite sum of products of `m + 1` localized coordinate functions vanishing at `x` with
smooth coefficients. A function vanishing near `x` is itself the product of a function vanishing
at `x` with any power of one minus a bump function. The square is the case `m = 1`: at an interior
point, the differential of `f` is the derivative of its chart expression. The converse inclusions
for higher powers are in `TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6 and §12.
-/

public section

open scoped ContDiff Manifold Topology Nat

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

/-- A function in the square of the vanishing ideal at `x` has zero differential at `x`.

Unlike its order-`m` analogue
`TauCeti.iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow`, this holds
at every point of every manifold, with no interior-point, finite-dimensionality or Hausdorff
hypothesis, which is what lets the differential descend to `I_x / I_x²` in general. -/
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

/-- A smooth function vanishing on a neighbourhood of `x` lies in every power of the vanishing
ideal at `x`. -/
theorem mem_smoothVanishingIdeal_pow_of_eventuallyEq_zero {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : (f : M → ℝ) =ᶠ[𝓝 x] 0) (n : ℕ) : f ∈ smoothVanishingIdeal I x ^ n := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hf).mem_iff.mp hf
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  have hχ : ⇑χ = b := ContMDiffMap.coeFn_mk _ _
  have hfac : f = (1 - χ) * f := by
    ext y
    by_cases hy : b y = 0
    · simp [hχ, hy]
    · simp [show f y = 0 from hb hy]
  -- Iterating `f = (1 - χ) f` gives `f = (1 - χ) ^ n f`, and `1 - χ` vanishes at `x`.
  have hpow : f = (1 - χ) ^ n * f := by
    induction n with
    | zero => rw [pow_zero, one_mul]
    | succ n ih => rw [pow_succ, mul_assoc, ← hfac, ← ih]
  rw [hpow]
  refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ n)
  simp [hχ]

/-- **Hadamard's lemma of order `m`.** At an interior point `x`, a smooth function whose chart
expression has vanishing derivatives of every order at most `m` at the image of `x` lies in
`I_x ^ (m + 1)`. -/
theorem mem_smoothVanishingIdeal_pow_succ_of_iteratedFDeriv_eq_zero {x : M}
    (hx : I.IsInteriorPoint x) {m : ℕ} {f : C^∞⟮I, M; ℝ⟯}
    (hf : ∀ k ≤ m,
      iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0) :
    f ∈ smoothVanishingIdeal I x ^ (m + 1) := by
  -- Near `x`, write `f` as a smooth function `g` of a globally smooth localized chart `F`.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨g, hg⟩ := exists_contMDiffMap_comp_eventuallyEq hx F hF f
  have hFx : F x = extChartAt I x x := hF.eq_of_nhds
  have hchart := comp_extChartAt_symm_eventuallyEq_of_eventuallyEq_comp hx hF hg
  have hgk (k : ℕ) (hk : k ≤ m) : iteratedFDeriv ℝ k g (F x) = 0 := by
    rw [hFx, ← (hchart.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hf k hk
  -- Taylor's formula writes `g` as a combination of products of `m + 1` coordinate functions
  -- vanishing at `F x`; pulling back by `F` gives an element of `I_x ^ (m + 1)`.
  let b := Module.finBasis ℝ E
  obtain ⟨a, ha⟩ := ContMDiffMap.exists_taylor_coords g (F x) b m
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ b.coord i (F y) - b.coord i (F x),
      ((b.coord i).toContinuousLinearMap.contDiff.contMDiff.comp F.contMDiff).sub contMDiff_const⟩
  have hc (i) (y : M) : c i y = b.coord i (F y) - b.coord i (F x) := rfl
  let P : C^∞⟮I, M; ℝ⟯ := ∑ r, (a r).comp F * ∏ j, c (r j)
  have hP : P ∈ smoothVanishingIdeal I x ^ (m + 1) := by
    refine Ideal.sum_mem _ fun r _ ↦ Ideal.mul_mem_left _ _ ?_
    have := Ideal.prod_mem_prod (s := Finset.univ)
      (I := fun _ : Fin (m + 1) ↦ smoothVanishingIdeal I x) (x := fun j ↦ c (r j))
      fun j _ ↦ mem_smoothVanishingIdeal_iff.mpr (by simp [hc])
    simpa using this
  -- The remainder `f - P` vanishes near `x`, since the Taylor polynomial of `g` at `F x` is zero.
  have hfP : f - P ∈ smoothVanishingIdeal I x ^ (m + 1) := by
    refine mem_smoothVanishingIdeal_pow_of_eventuallyEq_zero ?_ _
    filter_upwards [hg] with y hy
    have hPy : P y = ∑ r, a r (F y) * ∏ j, (b.coord (r j) (F y) - b.coord (r j) (F x)) := by
      have hprod (r : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
          ⇑(∏ j, c (r j)) = ∏ j, ⇑(c (r j)) :=
        map_prod ContMDiffMap.coeFnRingHom _ _
      simp only [P, ContMDiffMap.coe_sum, Finset.sum_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
        ContMDiffMap.comp_apply, hprod, Finset.prod_apply, hc]
    have hsum : ∑ k ∈ Finset.range (m + 1),
        (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k g (F x) (fun _ ↦ F y - F x) = 0 :=
      Finset.sum_eq_zero fun k hk ↦ by
        rw [hgk k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
        simp
    rw [Pi.zero_apply, ContMDiffMap.coe_sub, Pi.sub_apply, hPy, hy, Function.comp_apply,
      ha (F y), hsum, zero_add, sub_self]
  simpa using add_mem hfP hP

/-- **Hadamard's lemma for the vanishing ideal.** At an interior point `x`, a smooth function whose
value and differential vanish at `x` lies in the square of the vanishing ideal at `x`. -/
theorem mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero {x : M} (hx : I.IsInteriorPoint x)
    {f : C^∞⟮I, M; ℝ⟯} (hf₀ : f x = 0) (hf₁ : mvfderiv I f x = 0) :
    f ∈ smoothVanishingIdeal I x ^ 2 := by
  refine mem_smoothVanishingIdeal_pow_succ_of_iteratedFDeriv_eq_zero hx (m := 1) fun k hk ↦ ?_
  rw [← norm_eq_zero]
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply, extChartAt_to_inv, hf₀, norm_zero]
  · -- At an interior point, the differential of `f` is the derivative of its chart expression.
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := (f.contMDiff.mdifferentiable (by simp)) x
    rw [mvfderiv_eq_zero_iff, hmd.mfderiv,
      fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx), writtenInExtChartAt,
      extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at hf₁
    rw [norm_iteratedFDeriv_one, norm_eq_zero]
    ext v
    -- The tangent spaces of `M` at `x` and of `ℝ` at `f x` are `E` and `ℝ` themselves.
    exact congrArg (· v) hf₁

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
