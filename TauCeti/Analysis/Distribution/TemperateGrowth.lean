/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Sign
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Derivatives of functions of temperate growth

A smooth function whose iterated derivatives are all bounded — or even only those of positive order,
by the mean value theorem — has temperate growth. Typical examples
are smooth functions which outside a ball agree with a homogeneous function of degree at most `0`,
and diffeomorphisms whose derivatives of positive order are bounded.
So does a smooth function satisfying symbol estimates
`‖D^k f(x)‖ ≤ C_k (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)` of some real order `m`, and the rescaled
Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r`, together with its multiples
`x ↦ (a ‖x‖ ^ 2 + c) ^ r` for `0 ≤ a` and `0 < c`. On a real inner product space, so does the
logarithm `x ↦ log (1 + ‖x‖ ^ 2)` of the squared Japanese bracket, which enters the complex powers
of the Japanese bracket. So does the exponential `y ↦ exp(i ⟪y, ξ⟫)` of an angular frequency
`ξ`, which therefore defines a tempered distribution.

The derivative `Df` of a function `f` of temperate growth has temperate growth, since the iterated
derivatives of `Df` are those of `f` shifted by one order. So does each directional derivative
`x ↦ Df(x) v`. These are the coefficients that appear when the Leibniz rule is applied to the
product of a Schwartz function or a tempered distribution with `f`. Applying a fixed continuous
linear map `L` to the values, for instance taking coordinates of a matrix-valued `f`, also
preserves temperate growth.

On a finite-dimensional space the determinant is a polynomial in the matrix entries, so it has
temperate growth, and so does the Jacobian determinant `x ↦ det Df(x)`. The absolute value of a
real function of temperate growth without zeros has temperate growth: on the connected space `E`
the function has constant sign. These give the Jacobian factor `|det Dφ⁻¹|` of a change of
variables `φ` of Schwartz functions.

When the derivatives of positive order of `φ⁻¹` are bounded, so are all derivatives of the
Jacobian factor `|det Dφ⁻¹|`. This is an input of the Sobolev estimates for changes of variables
in `TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables`.

If `g ∘ f = id` and `g` has temperate growth, then `‖x‖` is
bounded by a polynomial in `‖f x‖`, the growth condition of Mathlib's `SchwartzMap.compCLM`.

A smooth map between arbitrary real normed spaces that is affine outside a compact set has
uniformly bounded derivatives of every positive order and temperate growth. Its order-zero values
need not be bounded. A measure of temperate growth is finite on compact sets.

## Main results

* `ContDiff.exists_bound_iteratedFDeriv_pos_and_hasTemperateGrowth_of_eqOn_affine`:
  smooth maps affine outside a compact set have bounded positive derivatives and temperate growth.

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: bounded derivatives give temperate
  growth.
* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos`: bounded positive-order derivatives
  give temperate growth.
* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow`: symbol estimates
  give temperate growth.
* `Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow`: the rescaled Bessel potential has
  temperate growth.
* `TauCeti.hasTemperateGrowth_mul_norm_sq_add_rpow`: so does `x ↦ (a ‖x‖ ^ 2 + c) ^ r` for
  `0 ≤ a` and `0 < c`.
* `Function.hasTemperateGrowth_log_one_add_norm_sq`: `x ↦ log (1 + ‖x‖ ^ 2)` has temperate growth.
* `Function.hasTemperateGrowth_norm_sub_pow`: `y ↦ ‖x - y‖ ^ (2N)` has temperate growth.
* `Function.HasTemperateGrowth.fderiv`: `Df` has temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: `x ↦ Df(x) v` has temperate growth.
* `Function.HasTemperateGrowth.continuousLinearMap_comp`: `L ∘ f` has temperate growth for a
  continuous linear map `L`.
* `Function.HasTemperateGrowth.basis_repr`: the coordinates of `f` in a finite basis have temperate
  growth.
* `Function.HasTemperateGrowth.basis_repr_fderiv_apply`: so do the coordinates of `Df(x) v` in a
  basis.
* `Function.HasTemperateGrowth.prod`: finite products of functions of temperate growth.
* `ContinuousLinearEquiv.hasTemperateGrowth_comp_iff`: precomposing with a continuous linear
  equivalence preserves and reflects temperate growth.
* `ContinuousLinearMap.hasTemperateGrowth_det`, `Function.HasTemperateGrowth.det_fderiv`: the
  determinant and the Jacobian determinant have temperate growth.
* `Function.HasTemperateGrowth.abs`: `|f|` has temperate growth if `f` has no zeros.
* `Function.HasTemperateGrowth.abs_det_fderiv_symm`: the Jacobian factor `|det Dφ⁻¹|` of a
  bijection `φ` such that `φ` and `φ⁻¹` have temperate growth.
* `Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le`: the Jacobian
  factor `|det Dφ⁻¹|` has a bounded derivative of order `n` when those of `φ⁻¹` of orders `1` to
  `n + 1` are bounded.
* `Function.HasTemperateGrowth.exists_norm_le_of_leftInverse`: a polynomial lower bound for
  `‖f x‖` from a left inverse of temperate growth.
* `MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts`: a measure of temperate
  growth is finite on compact sets.
-/

public section

open scoped ContDiff

namespace ContDiff

open Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth map affine outside a compact set has uniformly bounded derivatives of every positive
order and temperate growth. The source and target may be arbitrary real normed spaces; no bound
on the values of the map itself is asserted. -/
theorem exists_bound_iteratedFDeriv_pos_and_hasTemperateGrowth_of_eqOn_affine
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (a : F) (L : E →L[ℝ] F)
    (heq : EqOn f (fun x ↦ a + L x) Kᶜ) :
    (∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) ∧
      Function.HasTemperateGrowth f := by
  have hA : ContDiff ℝ ∞ (fun x ↦ a + L x) := contDiff_const.add L.contDiff
  have hs : HasCompactSupport (fun x ↦ f x - (a + L x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    exact hx (sub_eq_zero.mpr (heq hxK))
  have htemp : Function.HasTemperateGrowth f := by
    have h := (hs.hasTemperateGrowth (hf.sub hA)).add
      ((Function.HasTemperateGrowth.const a).add L.hasTemperateGrowth)
    convert h using 1
    funext x
    simp
  have hd : HasCompactSupport (fun x ↦ fderiv ℝ f x - L) := by
    convert hs.fderiv ℝ using 1
    funext x
    rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hA.differentiable (by simp) x),
      (L.hasFDerivAt.const_add a).fderiv]
  have hdcd : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f x - L) :=
    (hf.fderiv_right (by simp)).sub contDiff_const
  refine ⟨?_, htemp⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨C, _, hC⟩ := hd.exists_bound_iteratedFDeriv hdcd m
  refine ⟨C + ‖L‖, fun x ↦ ?_⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have heqD : fderiv ℝ f = (fun x ↦ fderiv ℝ f x - L) + (fun _ ↦ L) := by
    funext x
    simp
  rw [heqD, iteratedFDeriv_add (hdcd.of_le (by simp)) contDiff_const, Pi.add_apply]
  apply (norm_add_le _ _).trans
  exact add_le_add (hC m le_rfl x) (by
    by_cases hm : m = 0
    · subst m
      simp
    · simp [iteratedFDeriv_const_of_ne hm])

end ContDiff

namespace Function.HasTemperateGrowth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F}

/-- A smooth function all of whose iterated derivatives are bounded has temperate growth. -/
theorem of_norm_iteratedFDeriv_le (hf : ContDiff ℝ ∞ f)
    (hbd : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : f.HasTemperateGrowth :=
  ⟨hf, fun n ↦ ⟨0, (hbd n).imp fun C hC x ↦ by simpa using hC x⟩⟩

/-- A smooth function whose iterated derivatives of all positive orders are bounded has temperate
growth: the mean value theorem bounds `‖f x‖` linearly by `‖f 0‖ + C₁ ‖x‖`. -/
theorem of_norm_iteratedFDeriv_le_of_pos (hf : ContDiff ℝ ∞ f)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : f.HasTemperateGrowth := by
  refine ⟨hf, fun n ↦ ?_⟩
  rcases n with _ | n
  · obtain ⟨C₁, hC₁⟩ := hbd 1 le_rfl
    refine ⟨1, ‖f 0‖ + max C₁ 0, fun x ↦ ?_⟩
    have hmvt : ‖f x - f 0‖ ≤ max C₁ 0 * ‖x - 0‖ :=
      convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun y _ ↦ hf.differentiable (by simp) y)
        (fun y _ ↦ (norm_iteratedFDeriv_one f).symm.trans_le ((hC₁ y).trans (le_max_left _ _)))
        (Set.mem_univ 0) (Set.mem_univ x)
    rw [norm_iteratedFDeriv_zero, pow_one]
    calc ‖f x‖ = ‖f 0 + (f x - f 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f 0‖ + ‖f x - f 0‖ := norm_add_le _ _
      _ ≤ ‖f 0‖ + max C₁ 0 * ‖x‖ := by simpa only [sub_zero] using add_le_add_right hmvt ‖f 0‖
      _ ≤ (‖f 0‖ + max C₁ 0) * (1 + ‖x‖) := by
        nlinarith [norm_nonneg (f 0), norm_nonneg x, le_max_right C₁ 0]
  · obtain ⟨C, hC⟩ := hbd (n + 1) (by omega)
    exact ⟨0, C, fun x ↦ by simpa using hC x⟩

/-- **Symbol estimates give temperate growth.** A smooth function whose `k`-th derivative is
bounded by `C_k (1 + ‖x‖²) ^ ((m - k) / 2)` for every `k` has temperate growth. -/
theorem of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow {m : ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ k : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)) :
    f.HasTemperateGrowth := by
  refine ⟨hf, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbound k
  refine ⟨⌈m⌉₊, max C 0, fun x ↦ (hC x).trans ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hw : (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖) ^ ⌈m⌉₊ :=
    calc (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖ ^ 2) ^ ((⌈m⌉₊ : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by
            have := Nat.le_ceil m
            have : (0 : ℝ) ≤ k := k.cast_nonneg
            linarith)
      _ ≤ (1 + ‖x‖) ^ ⌈m⌉₊ := TauCeti.one_add_norm_sq_rpow_le_one_add_norm_pow x ⌈m⌉₊
  calc C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ max C 0 * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + ‖x‖) ^ ⌈m⌉₊ := mul_le_mul_of_nonneg_left hw (le_max_right _ _)

/-- The derivative of a function of temperate growth has temperate growth. -/
theorem fderiv (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right le_rfl, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x ↦ by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩

/-- A directional derivative `x ↦ Df(x) v` of a function of temperate growth has temperate
growth. -/
theorem fderiv_apply (hf : f.HasTemperateGrowth) (v : E) :
    (fun x ↦ _root_.fderiv ℝ f x v).HasTemperateGrowth :=
  (ContinuousLinearMap.apply ℝ F v).hasTemperateGrowth.comp hf.fderiv

/-- Applying a fixed continuous linear map `L` to the values of a function of temperate growth gives
a function of temperate growth. The map `L` may be linear over a normed `ℝ`-algebra `𝕜`, such
as `ℂ`. -/
theorem continuousLinearMap_comp {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G] (L : F →L[𝕜] G) (hf : f.HasTemperateGrowth) :
    (L ∘ f).HasTemperateGrowth :=
  (L.restrictScalars ℝ).hasTemperateGrowth.comp hf

/-- The coordinates `x ↦ b.repr (f x) i` of a function of temperate growth in a finite basis `b`
have temperate growth. -/
theorem basis_repr {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
    [Finite ι] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    (hf : f.HasTemperateGrowth) (b : Module.Basis ι 𝕜 F) (i : ι) :
    (fun x ↦ b.repr (f x) i).HasTemperateGrowth := by
  have := b.finiteDimensional_of_finite
  exact hf.continuousLinearMap_comp (LinearMap.toContinuousLinearMap (b.coord i))

/-- The coordinates in a basis `b` of the directional derivative `x ↦ Df(x) v` of a function `f` of
temperate growth have temperate growth. These are the coefficients of the chain rule for
composition with `f`. -/
theorem basis_repr_fderiv_apply {𝕜 ι : Type*} [RCLike 𝕜] [Finite ι]
    (hf : f.HasTemperateGrowth) (b : Module.Basis ι ℝ F) (v : E) (i : ι) :
    (fun x ↦ ((b.repr (_root_.fderiv ℝ f x v) i : ℝ) : 𝕜)).HasTemperateGrowth :=
  (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth.comp ((hf.fderiv_apply v).basis_repr b i)

/-- A finite product of functions of temperate growth has temperate growth. -/
theorem prod {ι R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] {f : ι → E → R}
    (s : Finset ι) (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HasTemperateGrowth.const]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (by simp)).mul (ih fun i hi ↦ hf i (by simp [hi]))

/-- If `g ∘ f = id` with `g` of temperate growth, then `‖x‖` is bounded by a polynomial in
`‖f x‖`. -/
theorem exists_norm_le_of_leftInverse {g : F → E} (hg : g.HasTemperateGrowth)
    (h : LeftInverse g f) : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖f x‖) ^ k := by
  obtain ⟨k, C, hC⟩ := hg.2 0
  exact ⟨k, C, fun x ↦ by simpa [h x] using hC (f x)⟩

/-- A continuous real function without zeros on `E` has the constant sign of its value at `0`. -/
private theorem abs_eq_sign_mul {f : E → ℝ} (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) (x : E) :
    |f x| = (SignType.sign (f 0) : ℝ) * f x := by
  rw [← sign_mul_self, isPreconnected_univ.sign_eq_of_continuousOn hf.continuousOn
    (fun y _ ↦ h0 y) (Set.mem_univ x) (Set.mem_univ 0)]

/-- The absolute value of a real function of temperate growth without zeros has temperate growth:
by the intermediate value theorem the function has constant sign. -/
theorem abs {f : E → ℝ} (hf : f.HasTemperateGrowth) (h0 : ∀ x, f x ≠ 0) :
    (fun x ↦ |f x|).HasTemperateGrowth := by
  simpa only [abs_eq_sign_mul hf.1.continuous h0] using (HasTemperateGrowth.const _).fun_mul hf

end Function.HasTemperateGrowth

/-- Precomposing with a continuous linear equivalence preserves and reflects temperate growth. -/
theorem ContinuousLinearEquiv.hasTemperateGrowth_comp_iff {D V W : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : D ≃L[ℝ] V) {g : V → W} :
    (g ∘ e).HasTemperateGrowth ↔ g.HasTemperateGrowth :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp e.symm.hasTemperateGrowth,
    fun h ↦ h.comp e.hasTemperateGrowth⟩

/-- On a finite-dimensional space the determinant has temperate growth, being a polynomial in the
matrix entries. -/
theorem ContinuousLinearMap.hasTemperateGrowth_det {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (fun A : E →L[ℝ] E ↦ A.det).HasTemperateGrowth := by
  let b := Module.finBasis ℝ E
  have h : (fun A : E →L[ℝ] E ↦ A.det) = fun A ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, b.coord (σ i) (A (b i)) := by
    funext A
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [LinearMap.toMatrix_apply, Units.smul_def]
  have hprod (σ : Equiv.Perm (Fin (Module.finrank ℝ E))) :
      (fun A : E →L[ℝ] E ↦ ∏ i, b.coord (σ i) (A (b i))).HasTemperateGrowth :=
    Function.HasTemperateGrowth.prod _ fun i _ ↦ ((b.coord (σ i)).toContinuousLinearMap.comp
      (ContinuousLinearMap.apply ℝ E (b i) : (E →L[ℝ] E) →L[ℝ] E)).hasTemperateGrowth
  rw [h]
  exact Function.HasTemperateGrowth.sum fun σ _ ↦
    (Function.HasTemperateGrowth.const _).fun_mul (hprod σ)

/-- The Jacobian determinant `x ↦ det Df(x)` of a function of temperate growth on a
finite-dimensional space has temperate growth. -/
theorem Function.HasTemperateGrowth.det_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} (hf : f.HasTemperateGrowth) :
    (fun x ↦ (_root_.fderiv ℝ f x).det).HasTemperateGrowth :=
  ContinuousLinearMap.hasTemperateGrowth_det.comp hf.fderiv

/-- For a bijection `φ` of a finite-dimensional space such that `φ` and `φ⁻¹` have temperate
growth, the Jacobian factor `y ↦ |det Dφ⁻¹(y)|` of the change of variables has temperate growth:
`det Dφ⁻¹(y)` has no zeros, being the reciprocal of `det Dφ(φ⁻¹ y)`. -/
theorem Function.HasTemperateGrowth.abs_det_fderiv_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) :
    (fun y ↦ |(_root_.fderiv ℝ φ.symm y).det|).HasTemperateGrowth :=
  hψ.det_fderiv.abs fun y ↦ φ.det_fderiv_symm_ne_zero (hφ.1.differentiable (by simp) _)
    (hψ.1.differentiable (by simp) y)

/-- If `φ` and `φ⁻¹` have temperate growth and the derivatives of `φ⁻¹` of orders `1` to `n + 1`
are bounded, then the derivative of order `n` of the Jacobian factor `|det Dφ⁻¹|` is bounded. -/
theorem Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth) (n : ℕ)
    (hb : ∀ m ≤ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (m + 1) φ.symm x‖ ≤ C) :
    ∃ C, ∀ y, ‖iteratedFDeriv ℝ n
      (fun y ↦ ((|(_root_.fderiv ℝ φ.symm y).det| : ℝ) : ℂ)) y‖ ≤ C := by
  -- The determinant of the bounded smooth map `Dφ⁻¹` has bounded derivatives.
  obtain ⟨C, hC⟩ := (ContinuousLinearMap.hasTemperateGrowth_det.1.of_le
    (by exact_mod_cast le_top)).exists_norm_iteratedFDeriv_comp_le
      (hψ.fderiv.1.of_le (by exact_mod_cast le_top))
      fun m hm ↦ (hb m hm).imp fun C hC x ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hC x
  -- `det Dφ⁻¹` has no zeros on the connected space `E`, hence a constant sign `ε`.
  have hε := Function.HasTemperateGrowth.abs_eq_sign_mul hψ.det_fderiv.1.continuous
    fun y ↦ φ.det_fderiv_symm_ne_zero (hφ.1.differentiable (by simp) _)
      (hψ.1.differentiable (by simp) y)
  set ε : ℝ := (SignType.sign (_root_.fderiv ℝ φ.symm 0).det : ℝ)
  have hJ : (fun y ↦ ((|(_root_.fderiv ℝ φ.symm y).det| : ℝ) : ℂ)) =
      fun y ↦
        (ε • Complex.ofRealCLM) (((fun A : E →L[ℝ] E ↦ A.det) ∘ _root_.fderiv ℝ φ.symm) y) := by
    funext y
    simp only [Function.comp_apply, _root_.smul_apply, Complex.ofRealCLM_apply,
      Complex.real_smul, hε y, Complex.ofReal_mul]
  rw [hJ]
  simpa only [mul_one] using
    (ε • Complex.ofRealCLM).exists_norm_iteratedFDeriv_comp_left_le (w := fun _ ↦ 1)
      ((ContinuousLinearMap.hasTemperateGrowth_det.1.comp hψ.fderiv.1).of_le
        (by exact_mod_cast le_top)) ⟨C, fun y ↦ by simpa using hC y⟩

namespace Function

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The rescaled Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_one_add_norm_smul_sq_rpow (c r : ℝ) :
    (fun x : H ↦ (1 + ‖c • x‖ ^ 2) ^ r).HasTemperateGrowth :=
  (hasTemperateGrowth_one_add_norm_sq_rpow H r).comp (by fun_prop)

/-- For `0 ≤ a` and `0 < c`, the function `x ↦ (a ‖x‖ ^ 2 + c) ^ r` has temperate growth: it is
`c ^ r (1 + ‖√(a / c) • x‖ ^ 2) ^ r`, a multiple of a rescaled Bessel potential. -/
theorem _root_.TauCeti.hasTemperateGrowth_mul_norm_sq_add_rpow {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (r : ℝ) :
    (fun x : H ↦ (a * ‖x‖ ^ 2 + c) ^ r).HasTemperateGrowth := by
  have h : (fun x : H ↦ (a * ‖x‖ ^ 2 + c) ^ r) =
      fun x ↦ c ^ r * (1 + ‖√(a / c) • x‖ ^ 2) ^ r := by
    ext x
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (div_nonneg ha hc.le), ← Real.mul_rpow hc.le (by positivity)]
    congr 1
    field_simp
    ring
  rw [h]
  fun_prop

/-- On a real inner product space `H`, the logarithm `x ↦ log (1 + ‖x‖ ^ 2)` of the squared
Japanese bracket has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_log_one_add_norm_sq :
    (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2)).HasTemperateGrowth := by
  -- The function is bounded by `‖x‖ ^ 2`, and its derivative `(1 + ‖x‖ ^ 2)⁻¹ D‖x‖ ^ 2` has
  -- temperate growth.
  have hderiv (x : H) : HasFDerivAt (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2))
      ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ) • fderiv ℝ (fun x : H ↦ ‖x‖ ^ 2) x) x := by
    have h := (((contDiff_norm_sq ℝ (E := H) (n := 1)).differentiable one_ne_zero).differentiableAt
      (x := x)).hasFDerivAt.const_add 1
    rw [Real.rpow_neg_one]
    exact h.log (ne_of_gt (by positivity))
  have hfd : fderiv ℝ (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2)) =
      (fun x : H ↦ (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) • fderiv ℝ (fun x : H ↦ ‖x‖ ^ 2) :=
    funext fun x ↦ (hderiv x).fderiv
  refine HasTemperateGrowth.of_fderiv (k := 2) (C := 1) ?_
    (fun x ↦ (hderiv x).differentiableAt) fun x ↦ ?_
  · rw [hfd]
    exact (hasTemperateGrowth_one_add_norm_sq_rpow H (-1)).smul
      (hasTemperateGrowth_norm_sq H).fderiv
  · have hle : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    rw [Real.norm_of_nonneg (Real.log_nonneg hle), one_mul]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ‖x‖ ^ 2)
    nlinarith [norm_nonneg x]

/-- The exponential `y ↦ exp(i ⟪y, ξ⟫)` of angular frequency `ξ` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_exp_inner_mul_I (ξ : H) :
    (fun y : H ↦ Complex.exp (inner ℝ y ξ * Complex.I)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- An even power `y ↦ ‖x - y‖ ^ (2N)` of the distance to a point has temperate growth. -/
theorem hasTemperateGrowth_norm_sub_pow (x : H) (N : ℕ) :
    (fun y : H ↦ ‖x - y‖ ^ (2 * N)).HasTemperateGrowth := by
  have h : (fun y : H ↦ ‖x - y‖ ^ (2 * N)) = ((fun z : H ↦ ‖z‖ ^ 2) ∘ fun y ↦ x - y) ^ N := by
    funext y
    simp [pow_mul]
  rw [h]
  exact ((hasTemperateGrowth_norm_sq H).comp (by fun_prop)).pow N

end Function

open MeasureTheory

/-- A measure of temperate growth is finite on compact sets: `(1 + ‖x‖) ^ (-n)` is integrable and
bounded below by a positive constant on any bounded set. -/
theorem MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E)
    [h : μ.HasTemperateGrowth] : IsFiniteMeasureOnCompacts μ := by
  obtain ⟨n, hn⟩ := h.exists_integrable
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hε : 0 < (1 + max R 0) ^ (-(n : ℝ)) := by positivity
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hn.measure_norm_ge_lt_top hε)
  have hx' : ‖x‖ ≤ max R 0 := by simpa using (hR hx).trans (le_max_left R 0)
  rw [Set.mem_ofPred_eq, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
