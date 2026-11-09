/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
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
`I_x / I_x²` is canonically the cotangent space `T_x*M`, the class of `f` going to `df_x`. This
identification is natural: pulling functions back along a smooth map corresponds to the transpose
of its differential, so restriction to an open set is an isomorphism, and the classes of the chart
coordinates form the dual basis of the coordinate basis. This is the scalar foundation of the
algebraic description of jets and differential operators.

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
* `TauCeti.smoothCotangentMap`: the pullback `I_x / I_x² → I_y / I_y²` along a smooth map `φ`
  with `φ y = x`, functorial in `φ`. Under `smoothCotangentEquiv` it is the transpose of `dφ_y`
  (`TauCeti.smoothCotangentEquiv_smoothCotangentMap`), so it is bijective when `dφ_y` is
  invertible (`TauCeti.smoothCotangentMap_bijective`).
* `TauCeti.smoothCotangentRestrictEquiv`: restriction to an open neighbourhood of `x` is an
  isomorphism of algebraic cotangent spaces.
* `TauCeti.smoothCotangentBasis`: the basis of `I_x / I_x²` dual to a chosen basis of the model
  space, formed by the classes of the localized chart coordinates
  (`TauCeti.smoothCotangentBasis_eq_toCotangent`).
* `TauCeti.smoothVanishingIdeal_sq_eq_self`: on a zero-dimensional manifold `I_x² = I_x`.

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

open scoped ContDiff Manifold Topology

open TopologicalSpace

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

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- The vanishing ideal at `φ y` is the preimage of the vanishing ideal at `y` under the pullback
`f ↦ f ∘ φ` along a smooth map `φ`. -/
@[simp]
theorem comap_smoothVanishingIdeal (φ : C^∞⟮J, N; I, M⟯) (y : N) :
    (smoothVanishingIdeal J y).comap (ContMDiffMap.compRightAlgHom ℝ ℝ φ) =
      smoothVanishingIdeal I (φ y) :=
  Ideal.ext fun f ↦ by simp

/-- The pullback along `φ` of a smooth function vanishing at `x = φ y` vanishes at `y`. -/
theorem comp_mem_smoothVanishingIdeal (φ : C^∞⟮J, N; I, M⟯) {x : M} {y : N} (h : φ y = x)
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ smoothVanishingIdeal I x) :
    f.comp φ ∈ smoothVanishingIdeal J y := by
  simp [h, mem_smoothVanishingIdeal_iff.mp hf]

/-- The pullback `I_x / I_x² → I_y / I_y²` of algebraic cotangent spaces along a smooth map
`φ : N → M` with `φ y = x`, induced by `f ↦ f ∘ φ`. Under the identifications
`smoothCotangentEquiv` it is the transpose of the differential of `φ` at `y`
(`TauCeti.smoothCotangentEquiv_smoothCotangentMap`). The point `x` is a separate argument so that
the map composes along composites of smooth maps (`TauCeti.smoothCotangentMap_comp`). -/
def smoothCotangentMap (φ : C^∞⟮J, N; I, M⟯) {x : M} {y : N} (h : φ y = x) :
    (smoothVanishingIdeal I x).Cotangent →ₗ[ℝ] (smoothVanishingIdeal J y).Cotangent :=
  Ideal.mapCotangent _ _ (ContMDiffMap.compRightAlgHom ℝ ℝ φ)
    (by rw [comap_smoothVanishingIdeal, h])

/-- The pullback along `φ` sends the class of `f` to the class of `f ∘ φ`. -/
@[simp]
theorem smoothCotangentMap_toCotangent (φ : C^∞⟮J, N; I, M⟯) {x : M} {y : N} (h : φ y = x)
    (f : smoothVanishingIdeal I x) :
    smoothCotangentMap φ h ((smoothVanishingIdeal I x).toCotangent f) =
      (smoothVanishingIdeal J y).toCotangent
        ⟨(f : C^∞⟮I, M; ℝ⟯).comp φ, comp_mem_smoothVanishingIdeal φ h f.2⟩ :=
  (Ideal.mapCotangent_toCotangent _ _ _ _ f).trans
    (congrArg _ (Subtype.ext (ContMDiffMap.compRightAlgHom_apply ℝ φ _)))

/-- The pullback along the identity is the identity. -/
@[simp]
theorem smoothCotangentMap_id (x : M) (h : (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) x = x) :
    smoothCotangentMap ContMDiffMap.id h = LinearMap.id := by
  refine LinearMap.ext fun u ↦ ?_
  obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ u
  rw [smoothCotangentMap_toCotangent, LinearMap.id_apply]
  exact congrArg _ (Subtype.ext (ContMDiffMap.ext fun _ ↦ rfl))

/-- The pullback along a composite is the composite of the pullbacks, in the reverse order. -/
theorem smoothCotangentMap_comp (φ : C^∞⟮J, N; I, M⟯) (ψ : C^∞⟮K, P; J, N⟯) {x : M} {y : N}
    {z : P} (h : φ.comp ψ z = x) (hφ : φ y = x) (hψ : ψ z = y) :
    smoothCotangentMap (φ.comp ψ) h = smoothCotangentMap ψ hψ ∘ₗ smoothCotangentMap φ hφ := by
  refine LinearMap.ext fun u ↦ ?_
  obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ u
  rw [LinearMap.comp_apply, smoothCotangentMap_toCotangent, smoothCotangentMap_toCotangent,
    smoothCotangentMap_toCotangent]
  exact congrArg _ (Subtype.ext (ContMDiffMap.ext fun _ ↦ rfl))

end Pullback

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
        (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k g (F x) (fun _ ↦ F y - F x) = 0 :=
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

/-- **Coordinate differentials.** If, near an interior point `x`, a function `f` vanishing at `x`
agrees with a linear functional `ℓ` of the chart coordinates, then the cotangent class of `f`
corresponds to `ℓ`. In particular, for a basis `b` of the model space, the classes of the
localized coordinate functions `b.coord i ∘ extChartAt I x` correspond to the dual basis. -/
theorem smoothCotangentEquiv_toCotangent_of_eventuallyEq {x : M} (hx : I.IsInteriorPoint x)
    (f : smoothVanishingIdeal I x) (ℓ : E →L[ℝ] ℝ)
    (hf : (f : M → ℝ) =ᶠ[𝓝 x] fun y ↦ ℓ (extChartAt I x y) - ℓ (extChartAt I x x)) :
    smoothCotangentEquiv hx ((smoothVanishingIdeal I x).toCotangent f) = ℓ := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  have hfF : (f : M → ℝ) =ᶠ[𝓝 x] (fun e ↦ ℓ e - ℓ (F x)) ∘ F := by
    filter_upwards [hf, hF] with y hy hFy
    simp [hy, hFy, hF.eq_of_nhds]
  ext v
  have hd : DifferentiableAt ℝ (fun e ↦ ℓ e - ℓ (F x)) (F x) :=
    ℓ.differentiableAt.sub_const _
  rw [smoothCotangentEquiv_toCotangent, hfF.mvfderiv_eq,
    mvfderiv_comp_apply_of_differentiableAt hd
      (F.contMDiff.mdifferentiable (by simp)).mdifferentiableAt,
    mvfderiv_apply_of_eventuallyEq_extChartAt hF v, fderiv_sub_const, ContinuousLinearMap.fderiv]
  -- Both sides evaluate `ℓ` at `v`, read once as a tangent vector and once in the model space.
  rfl

/-- **The coordinate-differential basis.** At an interior point `x`, the basis of `I_x / I_x²`
corresponding under `smoothCotangentEquiv` to the dual basis of a basis `b` of the model space.
Its `i`-th vector is the class of any function vanishing at `x` that agrees near `x` with the
localized chart coordinate `b.coord i ∘ extChartAt I x - b.coord i (extChartAt I x x)`
(`smoothCotangentBasis_eq_toCotangent`); such functions exist
(`exists_toCotangent_eq_smoothCotangentBasis`). -/
def smoothCotangentBasis {x : M} (hx : I.IsInteriorPoint x) {ι : Type*}
    (b : Module.Basis ι ℝ E) : Module.Basis ι ℝ (smoothVanishingIdeal I x).Cotangent := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  -- Read `b` as a basis of `T_x M = E`, and transport its dual basis, as continuous functionals,
  -- to `I_x / I_x²`.
  let b' : Module.Basis ι ℝ (TangentSpace I x) := b
  exact (b'.dualBasis.map LinearMap.toContinuousLinearMap).map (smoothCotangentEquiv hx).symm

/-- The coordinate-differential basis corresponds under `smoothCotangentEquiv` to the dual basis
of `b`. -/
@[simp]
theorem smoothCotangentEquiv_smoothCotangentBasis {x : M} (hx : I.IsInteriorPoint x) {ι : Type*}
    (b : Module.Basis ι ℝ E) (i : ι) :
    smoothCotangentEquiv hx (smoothCotangentBasis hx b i) =
      LinearMap.toContinuousLinearMap (b.coord i) := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  simp only [smoothCotangentBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  -- The dual basis of `b` is `b.coord`, read on `T_x M` and on the model space `E`.
  exact congrArg _ (congrFun b.coe_dualBasis i)

/-- The `i`-th coordinate-differential basis vector is the class of any function vanishing at `x`
that agrees near `x` with the localized chart coordinate
`b.coord i ∘ extChartAt I x - b.coord i (extChartAt I x x)`. -/
theorem smoothCotangentBasis_eq_toCotangent {x : M} (hx : I.IsInteriorPoint x) {ι : Type*}
    (b : Module.Basis ι ℝ E) (i : ι) (f : smoothVanishingIdeal I x)
    (hf : (f : M → ℝ) =ᶠ[𝓝 x]
      fun y ↦ b.coord i (extChartAt I x y) - b.coord i (extChartAt I x x)) :
    smoothCotangentBasis hx b i = (smoothVanishingIdeal I x).toCotangent f := by
  apply (smoothCotangentEquiv hx).injective
  rw [smoothCotangentEquiv_smoothCotangentBasis]
  exact (smoothCotangentEquiv_toCotangent_of_eventuallyEq hx f _ (by simpa using hf)).symm

/-- Each coordinate-differential basis vector is the class of a smooth function vanishing at `x`
that agrees near `x` with the localized chart coordinate
`b.coord i ∘ extChartAt I x - b.coord i (extChartAt I x x)`. -/
theorem exists_toCotangent_eq_smoothCotangentBasis {x : M} (hx : I.IsInteriorPoint x)
    {ι : Type*} (b : Module.Basis ι ℝ E) (i : ι) :
    ∃ c : smoothVanishingIdeal I x, (c : M → ℝ) =ᶠ[𝓝 x]
        (fun y ↦ b.coord i (extChartAt I x y) - b.coord i (extChartAt I x x)) ∧
      (smoothVanishingIdeal I x).toCotangent c = smoothCotangentBasis hx b i := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  let c : smoothVanishingIdeal I x :=
    ⟨⟨fun y ↦ b.coord i (F y) - b.coord i (F x),
      ((b.coord i).toContinuousLinearMap.contDiff.contMDiff.comp F.contMDiff).sub contMDiff_const⟩,
      mem_smoothVanishingIdeal_iff.mpr (sub_self _)⟩
  have hc : (c : M → ℝ) =ᶠ[𝓝 x]
      fun y ↦ b.coord i (extChartAt I x y) - b.coord i (extChartAt I x x) := by
    filter_upwards [hF] with y hy
    simp [c, hy, hF.eq_of_nhds]
  exact ⟨c, hc, (smoothCotangentBasis_eq_toCotangent hx b i c hc).symm⟩

/-- **Zero-dimensional manifolds.** When the model space is zero, the algebraic cotangent space
at every point vanishes. -/
theorem subsingleton_smoothCotangent [Subsingleton E] (x : M) :
    Subsingleton (smoothVanishingIdeal I x).Cotangent :=
  -- In the zero space the nonempty set `range I` is everything, so every point is interior.
  have hx : I.IsInteriorPoint x := by
    rw [ModelWithCorners.IsInteriorPoint,
      Set.Nonempty.eq_univ ⟨_, Set.mem_range_self (f := I) (chartAt H x x)⟩, interior_univ]
    exact Set.mem_univ _
  -- A continuous linear functional on the zero space `TangentSpace I x = E` is zero.
  have : Subsingleton (TangentSpace I x) := ‹Subsingleton E›
  (smoothCotangentEquiv hx).toEquiv.subsingleton

/-- When the model space is zero, the vanishing ideal at every point equals its square: every
smooth function vanishing at `x` is a finite sum of products of such functions. -/
theorem smoothVanishingIdeal_sq_eq_self [Subsingleton E] (x : M) :
    smoothVanishingIdeal I x ^ 2 = smoothVanishingIdeal I x := by
  have := subsingleton_smoothCotangent (I := I) x
  rw [sq]
  exact (Ideal.cotangent_subsingleton_iff _).mp this

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

/-- **Naturality of the cotangent identification.** For a smooth map `φ : N → M` and interior
points `y` and `x = φ y`, the pullback of cotangent classes along `φ` corresponds, under
`smoothCotangentEquiv`, to the transpose of the differential `dφ_y`: the class of `f` at `x`
goes to `df_x ∘ dφ_y`. -/
theorem smoothCotangentEquiv_smoothCotangentMap (φ : C^∞⟮J, N; I, M⟯) {x : M} {y : N}
    (h : φ y = x) (hx : I.IsInteriorPoint x) (hy : J.IsInteriorPoint y)
    (u : (smoothVanishingIdeal I x).Cotangent) :
    smoothCotangentEquiv hy (smoothCotangentMap φ h u) =
      (smoothCotangentEquiv hx u).comp (mfderiv J I φ y) := by
  subst h
  obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ u
  rw [smoothCotangentMap_toCotangent, smoothCotangentEquiv_toCotangent,
    smoothCotangentEquiv_toCotangent]
  exact mvfderiv_comp y ((f : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiable (by simp) _)
    (φ.contMDiff.mdifferentiable (by simp) y)

/-- If the differential of a smooth map `φ` at an interior point `y` is invertible, for instance
for a local diffeomorphism, the pullback of cotangent classes `I_x / I_x² → I_y / I_y²` along `φ`,
where `x = φ y` is interior, is bijective. -/
theorem smoothCotangentMap_bijective (φ : C^∞⟮J, N; I, M⟯) {x : M} {y : N} (h : φ y = x)
    (hx : I.IsInteriorPoint x) (hy : J.IsInteriorPoint y) (hφ : (mfderiv J I φ y).IsInvertible) :
    Function.Bijective (smoothCotangentMap φ h) := by
  subst h
  obtain ⟨e, he⟩ := hφ
  -- Under the cotangent identifications the pullback is precomposition with `e`, a bijection.
  have hmap : ⇑(smoothCotangentMap φ rfl) = (smoothCotangentEquiv hy).symm ∘
      e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) ∘ smoothCotangentEquiv hx := by
    funext u
    rw [Function.comp_apply, Function.comp_apply, LinearEquiv.eq_symm_apply,
      smoothCotangentEquiv_smoothCotangentMap φ rfl hx hy, ← he]
    ext v
    simp
  rw [hmap]
  exact (smoothCotangentEquiv hy).symm.bijective.comp
    ((e.symm.arrowCongr _).bijective.comp (smoothCotangentEquiv hx).bijective)

end Pullback

/-- **Restriction to an open set.** For an open set `U` and an interior point `x` of `M` lying in
`U`, restricting smooth functions from `M` to `U` induces an isomorphism of algebraic cotangent
spaces `I_x(M) / I_x(M)² ≃ I_x(U) / I_x(U)²`. -/
def smoothCotangentRestrictEquiv (U : Opens M) {x : U} (hx : I.IsInteriorPoint (x : M)) :
    (smoothVanishingIdeal I (x : M)).Cotangent ≃ₗ[ℝ] (smoothVanishingIdeal I x).Cotangent :=
  LinearEquiv.ofBijective
    (smoothCotangentMap (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯) (y := x)
      (by simp))
    (smoothCotangentMap_bijective _ _ hx (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx)
      ⟨Manifold.tangentSpaceOpenEquiv x, (Manifold.mfderiv_subtype_val x).symm⟩)

/-- Restriction to an open set is the pullback of cotangent classes along the inclusion of `U`. -/
theorem coe_smoothCotangentRestrictEquiv (U : Opens M) {x : U} (hx : I.IsInteriorPoint (x : M)) :
    ⇑(smoothCotangentRestrictEquiv U hx) =
      smoothCotangentMap (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯) (y := x)
        (by simp) :=
  funext (LinearEquiv.ofBijective_apply _)

/-- Restriction to an open set sends the class of `f` to the class of its restriction. -/
@[simp]
theorem smoothCotangentRestrictEquiv_toCotangent (U : Opens M) {x : U}
    (hx : I.IsInteriorPoint (x : M)) (f : smoothVanishingIdeal I (x : M)) :
    smoothCotangentRestrictEquiv U hx ((smoothVanishingIdeal I (x : M)).toCotangent f) =
      (smoothVanishingIdeal I x).toCotangent
        ⟨(f : C^∞⟮I, M; ℝ⟯).comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯),
          comp_mem_smoothVanishingIdeal _ (by simp) f.2⟩ := by
  rw [coe_smoothCotangentRestrictEquiv]
  exact smoothCotangentMap_toCotangent _ (by simp) f

/-- Restriction to an open set is compatible with the identifications of the algebraic cotangent
spaces with the cotangent space, the tangent spaces of `U` and `M` at `x` being identified by
`tangentSpaceOpenEquiv`. -/
theorem smoothCotangentEquiv_smoothCotangentRestrictEquiv (U : Opens M) {x : U}
    (hx : I.IsInteriorPoint (x : M)) (u : (smoothVanishingIdeal I (x : M)).Cotangent) :
    smoothCotangentEquiv (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx)
        (smoothCotangentRestrictEquiv U hx u) =
      (smoothCotangentEquiv hx u).comp
        (Manifold.tangentSpaceOpenEquiv x).toContinuousLinearMap := by
  rw [← Manifold.mfderiv_subtype_val x]
  exact smoothCotangentEquiv_smoothCotangentMap _ (by simp) hx _ u

end TauCeti
