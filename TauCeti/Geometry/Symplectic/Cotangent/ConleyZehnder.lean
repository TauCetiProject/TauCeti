/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Geometry.Symplectic.Cotangent.SignConvention
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic

/-!
# The harmonic oscillator on `T*ℝ` and its Conley–Zehnder index in both sign conventions

On the linear cotangent space `T*ℝ = ℝ × ℝ*`, with position `q = x.1` and momentum `p = x.2 1`,
Tau Ceti uses the form `ω = -dλ` and the convention `ω(X_H, ·) = dH`, while the literature on
cotangent bundles often uses `ω_src = dλ` and `ω_src(X, ·) = -dH`. The fibrewise negation
`ν(q, p) = (q, -p)` is a symplectomorphism from `(T*ℝ, dλ)` to `(T*ℝ, ω)`
(`TauCeti.isSymplectomorphism_cotangentFiberNeg`), and data in the second convention is read in the
first by transporting along `ν` and replacing `H` by `-H ∘ ν⁻¹`
(`TauCeti.Geometry.Symplectic.Cotangent.SignConvention`). This file checks on the harmonic
oscillator `H = (q² + p²) / 2` that the transport changes neither the linearized flow nor its
Conley–Zehnder index.

* **Before transport.** In the convention of `dλ`, the field of `H` is `p ∂_q - q ∂_p`, whose flow
  is the clockwise rotation `(q, p) ↦ (q cos t + p sin t, -q sin t + p cos t)`, the evolution
  `TauCeti.oscillatorEvolution` of the oscillator on `ℝ × ℝ` read on `T*ℝ`
  (`TauCeti.realCotangentRotation`,
  `TauCeti.hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two`). It is linear,
  so it is its own linearization.
* **After transport.** The flow of `-H ∘ ν⁻¹ = -H` for `ω` is the conjugate `ν ∘ φ_t ∘ ν⁻¹` of the
  rotation (`TauCeti.hamiltonianFlow_neg_real_sq_add_momentum_sq_div_two`), by the general fact
  that a linear symplectomorphism conjugates Hamiltonian flows
  (`TauCeti.SymplecticForm.IsSymplectomorphism.map_hamiltonianFlow`).
* **Frames.** The basis `(∂_q, ∂_p)` (`TauCeti.realCotangentBasis`) is symplectic for `dλ` in the
  convention `ω(b i, b j) = J i j` of `Matrix.J`
  (`TauCeti.toMatrix_realCotangentBasis_rescale_neg_one`), and its image `(∂_q, -∂_p)` under `ν`
  (`TauCeti.realCotangentNegBasis`) is symplectic for `ω`
  (`TauCeti.toMatrix_realCotangentNegBasis`).
* **The same symplectic path.** In these two frames the linearized flows have the same matrix at
  every time and every base point, the realification of `e^{-it}`
  (`TauCeti.toMatrix_fderiv_hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two`,
  `TauCeti.toMatrix_fderiv_hamiltonianFlow_neg_real_sq_add_momentum_sq_div_two`): a linearized
  flow transported along a linear symplectomorphism has, in the transported frame, the same matrix
  (`TauCeti.SymplecticForm.IsSymplectomorphism.toMatrix_fderiv_hamiltonianFlow`). So, for
  `t ∈ [0, 1]`, they are the same path `TauCeti.realCotangentRotationPath` of symplectic
  matrices, and its Conley–Zehnder index is `1`
  (`TauCeti.conleyZehnderIndex_realCotangentRotationPath`), as for the clockwise rotation path
  `exp (t J S)` with `S = -1` of `TauCeti.GLSymplectic.conleyZehnderIndex`.

The frames matter: `(∂_q, -∂_p)` is symplectic for `ω` but not for `dλ`, and transport along the
symplectomorphism `ν` moves the frame together with the dynamics, so that both linearized flows are
read in frames symplectic for their own forms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2, for the convention
  `ω(X_H, ·) = -dH` with `ω = dλ`.
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index of a path of symplectic matrices).
-/

public section

noncomputable section

open Matrix
open scoped NNReal unitInterval

namespace TauCeti

open SymplecticForm

/-! ### Coordinates and symplectic frames on `T*ℝ` -/

/-- The identification of `ℝ × ℝ` with `T*ℝ = ℝ × ℝ*` reading a momentum `p` as the covector
`y ↦ y p`, through Mathlib's `ContinuousLinearMap.toSpanSingletonCLE`. -/
def realCotangentProdEquiv : (ℝ × ℝ) ≃L[ℝ] (ℝ × StrongDual ℝ ℝ) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr ContinuousLinearMap.toSpanSingletonCLE

/-- `realCotangentProdEquiv` keeps the position and sends the momentum `p` to `y ↦ y p`. -/
@[simp]
theorem realCotangentProdEquiv_apply (x : ℝ × ℝ) :
    realCotangentProdEquiv x = (x.1, ContinuousLinearMap.toSpanSingleton ℝ x.2) := by
  ext <;> simp [realCotangentProdEquiv]

/-- The inverse of `realCotangentProdEquiv` evaluates the covector at `1`. -/
@[simp]
theorem realCotangentProdEquiv_symm_apply (x : ℝ × StrongDual ℝ ℝ) :
    realCotangentProdEquiv.symm x = (x.1, x.2 1) := by
  simp [realCotangentProdEquiv]

/-- The basis `(∂_q, ∂_p)` of `T*ℝ`: the image under `realCotangentProdEquiv` of the standard basis
of `ℝ × ℝ`, indexed by `Fin 1 ⊕ Fin 1` as in `Matrix.J`. -/
def realCotangentBasis : Module.Basis (Fin 1 ⊕ Fin 1) ℝ (ℝ × StrongDual ℝ ℝ) :=
  ((Module.Basis.singleton (Fin 1) ℝ).prod (Module.Basis.singleton (Fin 1) ℝ)).map
    realCotangentProdEquiv.toLinearEquiv

/-- The first coordinate of a vector of `T*ℝ` in the basis `(∂_q, ∂_p)` is its position. -/
@[simp]
theorem realCotangentBasis_repr_inl (x : ℝ × StrongDual ℝ ℝ) (i : Fin 1) :
    realCotangentBasis.repr x (Sum.inl i) = x.1 := by
  simp [realCotangentBasis]

/-- The second coordinate of a vector of `T*ℝ` in the basis `(∂_q, ∂_p)` is its momentum. -/
@[simp]
theorem realCotangentBasis_repr_inr (x : ℝ × StrongDual ℝ ℝ) (i : Fin 1) :
    realCotangentBasis.repr x (Sum.inr i) = x.2 1 := by
  simp [realCotangentBasis]

/-- The first vector of `realCotangentBasis` is the position direction `∂_q = (1, 0)`. -/
@[simp]
theorem realCotangentBasis_inl (i : Fin 1) : realCotangentBasis (Sum.inl i) = (1, 0) := by
  simp [realCotangentBasis]

/-- The second vector of `realCotangentBasis` is the momentum direction `∂_p = (0, 1)`. -/
@[simp]
theorem realCotangentBasis_inr (i : Fin 1) :
    realCotangentBasis (Sum.inr i) = (0, ContinuousLinearMap.id ℝ ℝ) := by
  ext <;> simp [realCotangentBasis]

/-- **`(∂_q, ∂_p)` is a symplectic frame for `dλ`.** The matrix of the form `dλ`, the rescaling of
`ω = -dλ` by `-1`, in the basis `(∂_q, ∂_p)` is the standard matrix `Matrix.J`. -/
theorem toMatrix_realCotangentBasis_rescale_neg_one :
    LinearMap.BilinForm.toMatrix realCotangentBasis
        (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).toBilinForm =
      J (Fin 1) ℝ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, J]

/-- The basis `(∂_q, -∂_p)` of `T*ℝ`, the image of `realCotangentBasis` under the fibrewise
negation `ν`. -/
def realCotangentNegBasis : Module.Basis (Fin 1 ⊕ Fin 1) ℝ (ℝ × StrongDual ℝ ℝ) :=
  realCotangentBasis.map (cotangentFiberNeg (V := ℝ)).toLinearEquiv

@[simp]
theorem realCotangentNegBasis_apply (i : Fin 1 ⊕ Fin 1) :
    realCotangentNegBasis i = cotangentFiberNeg (realCotangentBasis i) :=
  Module.Basis.map_apply _ _ i

@[simp]
theorem realCotangentNegBasis_repr (x : ℝ × StrongDual ℝ ℝ) (i : Fin 1 ⊕ Fin 1) :
    realCotangentNegBasis.repr x i = realCotangentBasis.repr (cotangentFiberNeg x) i := by
  simp [realCotangentNegBasis, cotangentFiberNeg_symm]

/-- **`(∂_q, -∂_p)` is a symplectic frame for `ω`.** The matrix of the canonical form `ω = -dλ` in
the image under `ν` of the frame `(∂_q, ∂_p)` is the standard matrix `Matrix.J`, since `ν` is a
symplectomorphism from `dλ` to `ω`. -/
theorem toMatrix_realCotangentNegBasis :
    LinearMap.BilinForm.toMatrix realCotangentNegBasis
        strongDualCotangentSymplecticForm.toBilinForm = J (Fin 1) ℝ := by
  rw [← toMatrix_realCotangentBasis_rescale_neg_one]
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply,
    realCotangentNegBasis_apply]
  exact (isSymplectomorphism_iff.1 isSymplectomorphism_cotangentFiberNeg) _ _

/-! ### The oscillator flow before and after transport -/

/-- The harmonic oscillator `(q² + p²) / 2` is even in the momentum, so it is unchanged by the
fibrewise negation `ν`. -/
@[simp]
theorem real_sq_add_momentum_sq_div_two_comp_cotangentFiberNeg :
    (fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) ∘ cotangentFiberNeg =
      fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2 := by
  funext y
  simp

/-- The clockwise rotation `(q, p) ↦ (q cos t + p sin t, -q sin t + p cos t)` of `T*ℝ` through the
angle `t`: the evolution `TauCeti.oscillatorEvolution t` of the harmonic oscillator on `ℝ × ℝ`,
read on `T*ℝ` through `realCotangentProdEquiv`. It is the time-`t` map of the harmonic oscillator
`(q² + p²) / 2` for `dλ` in the convention `dλ(X, ·) = -dH`
(`TauCeti.hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two`). -/
def realCotangentRotation (t : ℝ) : (ℝ × StrongDual ℝ ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ) :=
  (realCotangentProdEquiv : (ℝ × ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ)).comp
    ((oscillatorEvolution t).comp
      (realCotangentProdEquiv.symm : (ℝ × StrongDual ℝ ℝ) →L[ℝ] (ℝ × ℝ)))

theorem realCotangentRotation_apply (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    realCotangentRotation t x =
      realCotangentProdEquiv (oscillatorEvolution t (realCotangentProdEquiv.symm x)) :=
  (rfl)

@[simp]
theorem realCotangentRotation_apply_fst (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    (realCotangentRotation t x).1 = Real.cos t * x.1 + Real.sin t * x.2 1 := by
  simp [realCotangentRotation_apply, oscillatorEvolution_apply]

@[simp]
theorem realCotangentRotation_apply_snd_apply (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) (y : ℝ) :
    (realCotangentRotation t x).2 y = (-Real.sin t * x.1 + Real.cos t * x.2 1) * y := by
  simp [realCotangentRotation_apply, oscillatorEvolution_apply, mul_comm]

@[simp]
theorem realCotangentRotation_zero : realCotangentRotation 0 = ContinuousLinearMap.id ℝ _ := by
  ext x <;> simp

/-- The Hamiltonian vector field `p ∂_q - q ∂_p` of the harmonic oscillator for `dλ`, in the
convention `dλ(X, ·) = -dH`, is the continuous linear map `(q, p) ↦ (p, -q)`. -/
private theorem hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two_eq :
    (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) =
      ⇑(((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
          (ContinuousLinearMap.snd ℝ ℝ (StrongDual ℝ ℝ))).prod
        (-(ContinuousLinearMap.fst ℝ ℝ (StrongDual ℝ ℝ)).smulRight
          (ContinuousLinearMap.id ℝ ℝ))) := by
  funext x
  rw [hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two]
  ext <;> simp

/-- The Hamiltonian vector field of the harmonic oscillator for `dλ`, in the convention
`dλ(X, ·) = -dH`, is globally Lipschitz, being linear. -/
theorem
  exists_lipschitzWith_hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two :
    ∃ K : ℝ≥0, LipschitzWith K
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)) := by
  rw [hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two_eq]
  exact ⟨_, ContinuousLinearMap.lipschitzWith _⟩

/-- The negated harmonic oscillator `-(q² + p²) / 2` has a globally Lipschitz Hamiltonian vector
field for `ω`, being linear. -/
theorem exists_lipschitzWith_hamiltonianVectorField_neg_real_sq_add_momentum_sq_div_two :
    ∃ K : ℝ≥0, LipschitzWith K
      (strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)) := by
  obtain ⟨K, hK⟩ :=
    exists_lipschitzWith_hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two
  -- The field for `ω` is the opposite of the field for `dλ`, its rescaling by `-1`.
  have h : strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) =
      -(strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) := by
    funext x
    rw [Pi.neg_apply, hamiltonianVectorField_rescale_neg_one, neg_neg, hamiltonianVectorField_neg]
  rw [h]
  exact ⟨K, hK.neg⟩

/-- The rotations solve Hamilton's equation `q' = p`, `p' = -q` of the harmonic oscillator for
`dλ` in the convention `dλ(X, ·) = -dH`. -/
theorem hasDerivAt_realCotangentRotation (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    HasDerivAt (fun s ↦ realCotangentRotation s x)
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) (realCotangentRotation t x))
      t := by
  rw [hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two]
  -- Read the oscillator equation `q' = p`, `p' = -q` on `ℝ × ℝ` through `realCotangentProdEquiv`.
  convert (realCotangentProdEquiv : (ℝ × ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ)).hasFDerivAt.comp_hasDerivAt
    t (hasDerivAt_oscillatorEvolution t (realCotangentProdEquiv.symm x)) using 1
  · ext <;> simp [oscillatorEvolution_apply]
  · ext <;> simp [oscillatorEvolution_apply]

/-- **The harmonic oscillator before transport.** For `H = (q² + p²) / 2` on `T*ℝ`, the flow of
the field `X` with `dλ(X, ·) = -dH`, the Hamiltonian flow of `-H` for `dλ` in Tau Ceti's
convention, is the clockwise rotation `realCotangentRotation t`. -/
theorem hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two {K : ℝ≥0}
    (hX : LipschitzWith K
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)))
    (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianFlow
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t x =
      realCotangentRotation t x := by
  have h := eq_flowOfLipschitz hX (γ := fun s ↦ realCotangentRotation s x)
    (fun s ↦ hasDerivAt_realCotangentRotation s x) t
  rw [realCotangentRotation_zero, ContinuousLinearMap.id_apply] at h
  rw [SymplecticForm.hamiltonianFlow_eq]
  exact h.symm

/-- **The harmonic oscillator after transport.** The Hamiltonian flow of `-H ∘ ν⁻¹ = -H` for
`ω = -dλ`, with `H = (q² + p²) / 2`, is the conjugate `ν ∘ realCotangentRotation t ∘ ν⁻¹` of the
flow before transport. -/
theorem hamiltonianFlow_neg_real_sq_add_momentum_sq_div_two {K : ℝ≥0}
    (hX : LipschitzWith K
      (strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)))
    (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    strongDualCotangentSymplecticForm.hamiltonianFlow
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t x =
      cotangentFiberNeg (realCotangentRotation t (cotangentFiberNeg x)) := by
  have hHν : (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) ∘
      (cotangentFiberNeg (V := ℝ)).toLinearEquiv =
      -fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2 := by
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, Pi.neg_comp,
      real_sq_add_momentum_sq_div_two_comp_cotangentFiberNeg]
  obtain ⟨K₁, hX₁⟩ :=
    exists_lipschitzWith_hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two
  have hX₁' : LipschitzWith K₁
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        ((-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) ∘
          (cotangentFiberNeg (V := ℝ)).toLinearEquiv)) := by
    rwa [hHν]
  -- Before transport the flow of the oscillator, written as `H ∘ ν`, is the rotation.
  have hsrc (y : ℝ × StrongDual ℝ ℝ) :
      (strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianFlow
        ((-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) ∘
          (cotangentFiberNeg (V := ℝ)).toLinearEquiv) hX₁' t y =
        realCotangentRotation t y :=
    (hamiltonianFlow_apply_eq_of_eventuallyEq _ _ hX₁' hX₁ fun _ _ ↦
      Filter.EventuallyEq.of_eq hHν).trans
      (hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two hX₁ t y)
  have h := isSymplectomorphism_cotangentFiberNeg.map_hamiltonianFlow _ hX₁' hX t
    (cotangentFiberNeg x)
  rw [hsrc] at h
  simpa using h.symm

/-! ### The linearized flows and their Conley–Zehnder index -/

/-- The linearized flow of the harmonic oscillator before transport is the rotation itself. -/
theorem fderiv_hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two {K : ℝ≥0}
    (hX : LipschitzWith K
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)))
    (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    fderiv ℝ ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianFlow
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t) x =
      realCotangentRotation t := by
  have h : ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianFlow
      (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t :
        ℝ × StrongDual ℝ ℝ → ℝ × StrongDual ℝ ℝ) = realCotangentRotation t :=
    funext (hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two hX t)
  rw [h, ContinuousLinearMap.fderiv]

/-- The linearized flow of the harmonic oscillator after transport is the conjugate by `ν` of the
rotation. -/
theorem fderiv_hamiltonianFlow_neg_real_sq_add_momentum_sq_div_two {K : ℝ≥0}
    (hX : LipschitzWith K
      (strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)))
    (t : ℝ) (x : ℝ × StrongDual ℝ ℝ) :
    fderiv ℝ (strongDualCotangentSymplecticForm.hamiltonianFlow
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t) x =
      (cotangentFiberNeg (V := ℝ) : (ℝ × StrongDual ℝ ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ)).comp
        ((realCotangentRotation t).comp
          (cotangentFiberNeg (V := ℝ) : (ℝ × StrongDual ℝ ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ))) := by
  have h : (strongDualCotangentSymplecticForm.hamiltonianFlow
      (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t :
        ℝ × StrongDual ℝ ℝ → ℝ × StrongDual ℝ ℝ) =
      (cotangentFiberNeg (V := ℝ) : (ℝ × StrongDual ℝ ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ)).comp
        ((realCotangentRotation t).comp
          (cotangentFiberNeg (V := ℝ) : (ℝ × StrongDual ℝ ℝ) →L[ℝ] (ℝ × StrongDual ℝ ℝ))) :=
    funext (hamiltonianFlow_neg_real_sq_add_momentum_sq_div_two hX t)
  rw [h, ContinuousLinearMap.fderiv]

/-- In the frame `(∂_q, ∂_p)` the rotation `realCotangentRotation t` has the matrix
`[[cos t, sin t], [-sin t, cos t]]`, the realification of `e^{-it}`. -/
theorem toMatrix_realCotangentRotation (t : ℝ) :
    LinearMap.toMatrix realCotangentBasis realCotangentBasis (realCotangentRotation t) =
      (diagonal fun _ : Fin 1 ↦ Complex.exp (((-t : ℝ) : ℂ) * Complex.I)).realify := by
  have hre : (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)).re = Real.cos t := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)).im = -Real.sin t := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp only [LinearMap.toMatrix_apply, realify_apply_inl_inl, realify_apply_inl_inr,
      realify_apply_inr_inl, realify_apply_inr_inr, diagonal_apply_eq, RCLike.re_to_complex,
      RCLike.im_to_complex, hre, him] <;> simp

/-- The path `t ↦ e^{-it}`, `t ∈ [0, 1]`, of `1 × 1` unitary matrices. -/
def realCotangentRotationUnitaryPath :
    Path (unitaryTorusHom (Fin 1) fun _ ↦ Circle.exp 0)
      (unitaryTorusHom (Fin 1) fun _ ↦ Circle.exp (-1)) where
  toFun t := unitaryTorusHom (Fin 1) fun _ ↦ Circle.exp (-t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- `realCotangentRotationUnitaryPath t` is `e^{-it}`. -/
@[simp]
theorem realCotangentRotationUnitaryPath_apply (t : I) :
    realCotangentRotationUnitaryPath t = unitaryTorusHom (Fin 1) fun _ ↦ Circle.exp (-t) :=
  (rfl)

/-- The path `t ↦ [[cos t, sin t], [-sin t, cos t]]`, `t ∈ [0, 1]`, of symplectic matrices: the
realification of `t ↦ e^{-it}`, the clockwise rotation `exp (t J S)` with `S = -1`. It is the
linearized flow of the harmonic oscillator on `T*ℝ` in a symplectic frame, both before and after
transport along the fibrewise negation. -/
def realCotangentRotationPath :
    Path (GLSymplectic.ofUnitary (unitaryTorusHom (Fin 1) fun _ ↦ Circle.exp 0))
      (GLSymplectic.ofUnitary (unitaryTorusHom (Fin 1) fun _ ↦ Circle.exp (-1))) :=
  realCotangentRotationUnitaryPath.map GLSymplectic.continuous_ofUnitary

/-- The matrix of `realCotangentRotationPath t` is the realification of `e^{-it}`. -/
@[simp]
theorem coe_realCotangentRotationPath (t : I) :
    ((realCotangentRotationPath t : GL (Fin 1 ⊕ Fin 1) ℝ) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) =
      (diagonal fun _ : Fin 1 ↦ Complex.exp (((-t : ℝ) : ℂ) * Complex.I)).realify := by
  simp [realCotangentRotationPath, Circle.coe_exp, Complex.exp_neg]

/-- **The linearized flow before transport.** For `H = (q² + p²) / 2` on `T*ℝ`, the linearized
flow of the field `X` with `dλ(X, ·) = -dH`, at any base point, has in the symplectic frame
`(∂_q, ∂_p)` of `dλ` the matrix `realCotangentRotationPath t` at every time `t ∈ [0, 1]`. -/
theorem toMatrix_fderiv_hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two
    {K : ℝ≥0} (hX : LipschitzWith K
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)))
    (t : I) (x : ℝ × StrongDual ℝ ℝ) :
    LinearMap.toMatrix realCotangentBasis realCotangentBasis
        (fderiv ℝ ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianFlow
          (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t) x) =
      ((realCotangentRotationPath t : GL (Fin 1 ⊕ Fin 1) ℝ) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) := by
  rw [fderiv_hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two,
    coe_realCotangentRotationPath, ← toMatrix_realCotangentRotation]

/-- **The linearized flow after transport.** The linearized flow of the Hamiltonian
`-H ∘ ν⁻¹ = -H` for `ω = -dλ`, at any base point, has in the symplectic frame `(∂_q, -∂_p)` of `ω`
the same matrix `realCotangentRotationPath t` as the flow before transport in the frame
`(∂_q, ∂_p)`, at every time `t ∈ [0, 1]`. -/
theorem toMatrix_fderiv_hamiltonianFlow_neg_real_sq_add_momentum_sq_div_two {K : ℝ≥0}
    (hX : LipschitzWith K
      (strongDualCotangentSymplecticForm.hamiltonianVectorField
        (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2)))
    (t : I) (x : ℝ × StrongDual ℝ ℝ) :
    LinearMap.toMatrix realCotangentNegBasis realCotangentNegBasis
        (fderiv ℝ (strongDualCotangentSymplecticForm.hamiltonianFlow
          (-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) hX t) x) =
      ((realCotangentRotationPath t : GL (Fin 1 ⊕ Fin 1) ℝ) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) := by
  obtain ⟨K₁, hX₁⟩ :=
    exists_lipschitzWith_hamiltonianVectorField_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two
  have hX₁' : LipschitzWith K₁
      ((strongDualCotangentSymplecticForm.rescale (-1) (by norm_num)).hamiltonianVectorField
        ((-fun y : ℝ × StrongDual ℝ ℝ ↦ (y.1 ^ 2 + y.2 1 ^ 2) / 2) ∘
          (cotangentFiberNeg (V := ℝ)).toLinearEquiv)) := by
    rwa [ContinuousLinearEquiv.coe_toLinearEquiv, Pi.neg_comp,
      real_sq_add_momentum_sq_div_two_comp_cotangentFiberNeg]
  -- Transport along `ν` moves the frame `(∂_q, ∂_p)` to `(∂_q, -∂_p)` with the dynamics.
  have h := isSymplectomorphism_cotangentFiberNeg.toMatrix_fderiv_hamiltonianFlow
    realCotangentBasis _ hX₁' hX t (cotangentFiberNeg.symm x)
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    Pi.neg_comp, real_sq_add_momentum_sq_div_two_comp_cotangentFiberNeg] at h
  rw [realCotangentNegBasis, h]
  exact toMatrix_fderiv_hamiltonianFlow_rescale_neg_one_neg_real_sq_add_momentum_sq_div_two _ t _

/-- **The Conley–Zehnder index of the harmonic oscillator.** The linearized flow
`realCotangentRotationPath` of the harmonic oscillator on `T*ℝ`, the same path of symplectic
matrices before and after transport along the fibrewise negation, has Conley–Zehnder index `1`:
it is the clockwise rotation through the angle `1 < 2π`. -/
theorem conleyZehnderIndex_realCotangentRotationPath :
    GLSymplectic.conleyZehnderIndex realCotangentRotationPath = 1 := by
  rw [realCotangentRotationPath,
    GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation
      realCotangentRotationUnitaryPath (α := fun _ ↦ -1)
      (fun _ ↦ by rw [abs_neg, abs_one]; linarith [Real.two_le_pi])
      (fun t ↦ by
        simp [Circle.coe_exp, Complex.exp_neg])]
  simp [Real.sign_neg, Real.sign_one]

end TauCeti
