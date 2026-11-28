/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Complex

/-!
# Coordinate differentials in the complex algebraic cotangent space

At an interior point of a finite-dimensional Hausdorff real manifold, center the real chart
coordinates at the point and localize them to global functions. Their classes as complex-valued
functions form a complex basis of the vanishing ideal modulo its square. The coordinates of
the class of a function are its complex-valued directional derivatives along the chosen real
tangent basis. In these bases, pullback acts by the transpose of the real Jacobian matrix
with entries included into the complex numbers.

The comparison with the real coordinate classes uses the inclusion `TauCeti.smoothCotangentOfReal`
and the real basis `TauCeti.smoothCotangentBasis`.
-/

public noncomputable section

open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] {x : M} {ι : Type*}

/-- The complex cotangent basis dual to a real tangent basis. Its coordinate functionals
evaluate the associated complex-valued covector on the real basis vectors. -/
def complexSmoothCotangentBasis (hx : I.IsInteriorPoint x) (b : Module.Basis ι ℝ E) :
    Module.Basis ι ℂ (complexSmoothVanishingIdeal I x).Cotangent := by
  haveI : Finite ι := Module.Finite.finite_basis b
  let e : (E →L[ℝ] ℂ) ≃ₗ[ℂ] (E →ₗ[ℝ] ℂ) :=
    LinearEquiv.ofBijective (ContinuousLinearMap.coeLM ℂ)
      LinearMap.toContinuousLinearMap.symm.bijective
  exact .ofEquivFun (((complexSmoothCotangentEquiv hx).trans e).trans (b.constr ℂ).symm)

/-- Each coordinate of a complex cotangent class is evaluation on the corresponding real
tangent basis vector. In particular the coordinates of `[f]` are the derivatives of `f`. -/
@[simp]
theorem complexSmoothCotangentBasis_repr (hx : I.IsInteriorPoint x) (b : Module.Basis ι ℝ E)
    (u : (complexSmoothVanishingIdeal I x).Cotangent) (i : ι) :
    (complexSmoothCotangentBasis hx b).repr u i = complexSmoothCotangentEquiv hx u (b i) := by
  simp only [complexSmoothCotangentBasis, Module.Basis.ofEquivFun_repr_apply,
    LinearEquiv.trans_apply, Module.Basis.constr_symm_apply]
  rfl

/-- The complex coordinate differentials are the images of the real coordinate differentials.
In particular their classes are independent of the choice of localization of the chart. -/
@[simp]
theorem smoothCotangentOfReal_smoothCotangentBasis (hx : I.IsInteriorPoint x)
    (b : Module.Basis ι ℝ E) (i : ι) :
    smoothCotangentOfReal I x (smoothCotangentBasis hx b i) =
      complexSmoothCotangentBasis hx b i := by
  classical
  apply (complexSmoothCotangentBasis hx b).repr.injective
  ext j
  rw [complexSmoothCotangentBasis_repr, complexSmoothCotangentEquiv_smoothCotangentOfReal,
    smoothCotangentEquiv_smoothCotangentBasis, Module.Basis.repr_self_apply]
  -- The coordinate functional lives on the model space, identified here with the tangent fiber.
  change (↑(b.repr (b j) i) : ℂ) = _
  rw [b.repr_self_apply]
  split_ifs <;> simp_all

/-- Each complex basis covector is the complex-valued coordinate functional of the real basis. -/
@[simp]
theorem complexSmoothCotangentEquiv_complexSmoothCotangentBasis (hx : I.IsInteriorPoint x)
    (b : Module.Basis ι ℝ E) (i : ι) :
    complexSmoothCotangentEquiv hx (complexSmoothCotangentBasis hx b i) =
      Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (b.coord i)) := by
  rw [← smoothCotangentOfReal_smoothCotangentBasis,
    complexSmoothCotangentEquiv_smoothCotangentOfReal, smoothCotangentEquiv_smoothCotangentBasis]
  rfl

/-- Any vanishing complex function with the germ of the centered real chart coordinate
represents the corresponding complex basis vector. -/
theorem complexSmoothCotangentBasis_eq_toCotangent (hx : I.IsInteriorPoint x)
    (b : Module.Basis ι ℝ E) (i : ι) (f : complexSmoothVanishingIdeal I x)
    (hf : (f : M → ℂ) =ᶠ[𝓝 x] fun y ↦
      ((b.coord i (extChartAt I x y) - b.coord i (extChartAt I x x) : ℝ) : ℂ)) :
    complexSmoothCotangentBasis hx b i = (complexSmoothVanishingIdeal I x).toCotangent f := by
  obtain ⟨g, hg, hclass⟩ := exists_toCotangent_eq_smoothCotangentBasis hx b i
  rw [← smoothCotangentOfReal_smoothCotangentBasis, ← hclass, smoothCotangentOfReal_toCotangent]
  apply (complexSmoothCotangentEquiv hx).injective
  rw [complexSmoothCotangentEquiv_toCotangent, complexSmoothCotangentEquiv_toCotangent]
  apply Filter.EventuallyEq.mvfderiv_eq
  filter_upwards [hg, hf] with y hy hfy
  exact (ContMDiffMap.ofReal_apply _ y).trans ((congrArg Complex.ofReal hy).trans hfy.symm)

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [T2Space N]

/-- In coordinate-differential bases, pullback of complex cotangent classes is represented by
the transpose of the real Jacobian, viewed as a complex matrix. -/
theorem toMatrix_complexSmoothCotangentMap {κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (φ : C^∞⟮J, N; I, M⟯) {y : N} (h : φ y = x)
    (hx : I.IsInteriorPoint x) (hy : J.IsInteriorPoint y)
    (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E') :
    LinearMap.toMatrix (complexSmoothCotangentBasis hx b) (complexSmoothCotangentBasis hy c)
        (complexSmoothCotangentMap φ h) =
      (LinearMap.toMatrix c b (mfderiv J I φ y).toLinearMap).transpose.map Complex.ofRealHom := by
  subst x
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply, complexSmoothCotangentBasis_repr,
    complexSmoothCotangentEquiv_complexSmoothCotangentMap φ rfl hx hy,
    complexSmoothCotangentEquiv_complexSmoothCotangentBasis, Matrix.map_apply,
    Matrix.transpose_apply]
  exact congrArg Complex.ofReal
    (LinearMap.toMatrix_apply c b (mfderiv J I φ y).toLinearMap j i).symm

end TauCeti
