/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Matrix
public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.Topology.Algebra.Module.Equiv.Fin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Realification and complexification of complex and real coordinate operators

`TauCeti.realCoords n` identifies `Fin n → ℂ` real-linearly with `Fin (n + n) → ℝ`, listing the
real parts of the coordinates first and their imaginary parts second. It is the splitting
`TauCeti.complexToRealPi` with its two coordinate blocks concatenated by `finSumFinEquiv`.

For a complex-linear operator `g` between complex coordinate spaces, `g.realifyCoords` is the
same map read in these real coordinates; its matrix is the realification `Matrix.realify` of the
complex matrix of `g` (`ContinuousLinearMap.toMatrix'_realifyCoords`). For a real-linear operator
`g` between real coordinate spaces, `g.complexifyCoords` is its complex-linear extension: the
complexification `ContinuousLinearMap.complexify` read in the coordinates
`TauCeti.Complexification.equivPi`. It acts by `g` on the real and on the imaginary parts of the
coordinates (`ContinuousLinearMap.complexifyCoords_apply`); its matrix is the matrix of `g` with
entries regarded as complex numbers (`ContinuousLinearMap.toMatrix'_complexifyCoords`). Both
constructions preserve identities, composition and addition, and both depend continuously on the
operator, so they can be applied to continuous families of transition matrices.

In real coordinates, the realification of a complexification is block diagonal with two copies
of the original operator (`ContinuousLinearMap.splitCoords_realifyCoords_complexifyCoords`,
`ContinuousLinearMap.realifyCoords_complexifyCoords`), the operator
form of `Matrix.realify_map_ofReal`. This is the coordinate form of the isomorphism between the
realification of the complexification of a real vector space and two copies of that space.
-/

public section

open Complex
open scoped Matrix

namespace TauCeti

/-- The real coordinates of a complex coordinate vector: the real parts of its coordinates,
followed by their imaginary parts. This is `TauCeti.complexToRealPi` with the two coordinate
blocks concatenated by `finSumFinEquiv`. -/
noncomputable def realCoords (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] (Fin (n + n) → ℝ) :=
  (complexToRealPi (Fin n)).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + n) => ℝ) finSumFinEquiv)

/-- The first `n` real coordinates are the real parts. -/
@[simp] theorem realCoords_apply_castAdd (n : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    realCoords n v (Fin.castAdd n i) = (v i).re := by
  rw [← finSumFinEquiv_apply_left]
  simp [realCoords, ContinuousLinearEquiv.piCongrLeft, Homeomorph.piCongrLeft,
    -finSumFinEquiv_apply_left]

/-- The last `n` real coordinates are the imaginary parts. -/
@[simp] theorem realCoords_apply_addNat (n : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    realCoords n v (i.addNat n) = (v i).im := by
  rw [← Fin.natAdd_eq_addNat, ← finSumFinEquiv_apply_right]
  simp [realCoords, ContinuousLinearEquiv.piCongrLeft, Homeomorph.piCongrLeft,
    -finSumFinEquiv_apply_right]

/-- The two coordinate blocks of `realCoords n v` are the real and imaginary parts of `v`. -/
theorem splitCoords_realCoords (n : ℕ) (v : Fin n → ℂ) :
    splitCoords (𝕜 := ℝ) n n (realCoords n v) = (fun i => (v i).re, fun i => (v i).im) := by
  ext i <;> simp only [splitCoords_apply, Fin.natAdd_eq_addNat, realCoords_apply_castAdd,
    realCoords_apply_addNat]

/-- Concatenating the two blocks of `TauCeti.complexToRealPi` gives `realCoords`. -/
theorem realCoords_comp_finSumFinEquiv (n : ℕ) (v : Fin n → ℂ) :
    realCoords n v ∘ finSumFinEquiv = complexToRealPi (Fin n) v := by
  funext k
  cases k <;> simp

/-- In real coordinates, a complex matrix acts by its realification, with the two coordinate
blocks concatenated by `finSumFinEquiv`. -/
theorem realCoords_mulVec {m n : ℕ} (M : Matrix (Fin n) (Fin m) ℂ) (z : Fin m → ℂ) :
    realCoords n (M *ᵥ z) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv M.realify *ᵥ realCoords m z := by
  apply finSumFinEquiv.surjective.injective_comp_right
  simp [Matrix.submatrix_mulVec_equiv, realCoords_comp_finSumFinEquiv, complexToRealPi_mulVec,
    Function.comp_assoc]

theorem realCoords_apply (n : ℕ) (v : Fin n → ℂ) :
    realCoords n v = (splitCoords (𝕜 := ℝ) n n).symm (fun i => (v i).re, fun i => (v i).im) := by
  rw [← splitCoords_realCoords, ContinuousLinearEquiv.symm_apply_apply]

/-- A complex vector is recovered from the two blocks of its real coordinates. -/
@[simp] theorem realCoords_symm_apply (n : ℕ) (w : Fin (n + n) → ℝ) (i : Fin n) :
    (realCoords n).symm w i =
      ((splitCoords (𝕜 := ℝ) n n w).1 i : ℂ) + ((splitCoords (𝕜 := ℝ) n n w).2 i : ℂ) * I := by
  obtain ⟨v, rfl⟩ := (realCoords n).surjective w
  rw [ContinuousLinearEquiv.symm_apply_apply, splitCoords_realCoords, re_add_im]

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {l m n : ℕ}

/-! ### Realification -/

/-- A complex-linear operator between complex coordinate spaces, read as a real-linear operator
in real coordinates (`TauCeti.realCoords`). -/
noncomputable def realifyCoords (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (Fin (m + m) → ℝ) →L[ℝ] (Fin (n + n) → ℝ) :=
  (realCoords n).toContinuousLinearMap.comp
    ((g.restrictScalars ℝ).comp (realCoords m).symm.toContinuousLinearMap)

theorem realifyCoords_apply (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) (w : Fin (m + m) → ℝ) :
    g.realifyCoords w = realCoords n (g ((realCoords m).symm w)) := (rfl)

@[simp] theorem realifyCoords_realCoords (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) (v : Fin m → ℂ) :
    g.realifyCoords (realCoords m v) = realCoords n (g v) := by
  rw [realifyCoords_apply, ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem realifyCoords_id :
    (ContinuousLinearMap.id ℂ (Fin n → ℂ)).realifyCoords =
      ContinuousLinearMap.id ℝ (Fin (n + n) → ℝ) := by
  ext w : 1
  simp [realifyCoords_apply]

@[simp] theorem realifyCoords_comp (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ))
    (f : (Fin l → ℂ) →L[ℂ] (Fin m → ℂ)) :
    (g.comp f).realifyCoords = g.realifyCoords.comp f.realifyCoords := by
  ext w : 1
  simp [realifyCoords_apply]

@[simp] theorem realifyCoords_add (f g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (f + g).realifyCoords = f.realifyCoords + g.realifyCoords := by
  ext w : 1
  simp [realifyCoords_apply]

/-- The matrix of a realified operator is the realification `Matrix.realify` of its complex
matrix, with the two blocks of real coordinates concatenated by `finSumFinEquiv`. -/
theorem toMatrix'_realifyCoords (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    LinearMap.toMatrix' (g.realifyCoords : (Fin (m + m) → ℝ) →ₗ[ℝ] (Fin (n + n) → ℝ)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (LinearMap.toMatrix' (g : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ))).realify := by
  rw [← LinearMap.toMatrix'_toLin' (Matrix.reindex _ _ _)]
  congr 1
  refine LinearMap.ext fun w => ?_
  obtain ⟨z, rfl⟩ := (realCoords m).surjective w
  rw [Matrix.toLin'_apply, ← realCoords_mulVec]
  simp

/-- Realification depends continuously on the complex operator. -/
theorem continuous_realifyCoords :
    Continuous (realifyCoords : ((Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) → _) :=
  (((continuous_restrictScalars (𝕜' := ℝ)).clm_comp_const _).const_clm_comp _)

/-! ### Complexification -/

/-- The complex-linear extension of a real-linear operator between real coordinate spaces: the
complexification `ContinuousLinearMap.complexify` read in the coordinates
`TauCeti.Complexification.equivPi`. It acts by the original operator on the real parts and on the
imaginary parts of the coordinates. -/
noncomputable def complexifyCoords (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin m → ℂ) →L[ℂ] (Fin n → ℂ) :=
  (Complexification.equivPi (Fin n)).toContinuousLinearMap.comp
    (g.complexify.comp (Complexification.equivPi (Fin m)).symm.toContinuousLinearMap)

@[simp] theorem complexifyCoords_apply (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (v : Fin m → ℂ)
    (i : Fin n) :
    g.complexifyCoords v i = ⟨g (fun k => (v k).re) i, g (fun k => (v k).im) i⟩ := by
  simp [complexifyCoords]

@[simp] theorem complexifyCoords_ofReal (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (v : Fin m → ℝ) :
    g.complexifyCoords (fun k => (v k : ℂ)) = fun i => (g v i : ℂ) := by
  funext i
  apply Complex.ext
  · simp
  · simp only [complexifyCoords_apply, ofReal_im]
    -- The imaginary parts form the zero vector, written as a constant function.
    exact congrFun (map_zero g) i

@[simp] theorem complexifyCoords_id :
    (ContinuousLinearMap.id ℝ (Fin n → ℝ)).complexifyCoords =
      ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
  ext v : 1
  simp [complexifyCoords]

@[simp] theorem complexifyCoords_comp (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (f : (Fin l → ℝ) →L[ℝ] (Fin m → ℝ)) :
    (g.comp f).complexifyCoords = g.complexifyCoords.comp f.complexifyCoords := by
  ext v : 1
  simp [complexifyCoords]

@[simp] theorem complexifyCoords_add (f g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (f + g).complexifyCoords = f.complexifyCoords + g.complexifyCoords := by
  simp only [complexifyCoords, ← complexifyₗᵢ_apply, map_add, add_comp, comp_add]

/-- The matrix of a complexified operator is the original real matrix with its entries regarded
as complex numbers. -/
theorem toMatrix'_complexifyCoords (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    LinearMap.toMatrix' (g.complexifyCoords : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
      (LinearMap.toMatrix' (g : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))).map ((↑) : ℝ → ℂ) := by
  ext i j
  have hj : (Pi.single j 1 : Fin m → ℂ) = fun k => ((Pi.single j 1 : Fin m → ℝ) k : ℂ) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  simp only [LinearMap.toMatrix'_apply, Matrix.map_apply, coe_coe, hj, complexifyCoords_ofReal]

/-- Complexification depends continuously on the real operator. -/
theorem continuous_complexifyCoords :
    Continuous (complexifyCoords : ((Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) → _) :=
  ((((complexifyₗᵢ (Fin m → ℝ) (Fin n → ℝ)).continuous.clm_comp_const
    (Complexification.equivPi (Fin m)).symm.toContinuousLinearMap).const_clm_comp
      (Complexification.equivPi (Fin n)).toContinuousLinearMap).congr
        fun g => by rw [complexifyₗᵢ_apply, complexifyCoords])

/-- In real coordinates, the realification of the complexification of `g` acts by `g` on the
block of real parts and on the block of imaginary parts. -/
theorem splitCoords_realifyCoords_complexifyCoords (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (w : Fin (m + m) → ℝ) :
    splitCoords (𝕜 := ℝ) n n (g.complexifyCoords.realifyCoords w) =
      (g (splitCoords (𝕜 := ℝ) m m w).1, g (splitCoords (𝕜 := ℝ) m m w).2) := by
  obtain ⟨v, rfl⟩ := (realCoords m).surjective w
  rw [realifyCoords_realCoords, splitCoords_realCoords, splitCoords_realCoords]
  ext i <;> simp

/-- In real coordinates, the realification of the complexification of `g` acts by `g` on the
real parts and on the imaginary parts separately. -/
theorem realifyCoords_complexifyCoords (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    g.complexifyCoords.realifyCoords =
      (splitCoords n n).symm.toContinuousLinearMap.comp
        ((g.prodMap g).comp (splitCoords m m).toContinuousLinearMap) := by
  ext w : 1
  apply (splitCoords (𝕜 := ℝ) n n).injective
  rw [splitCoords_realifyCoords_complexifyCoords]
  simp

end ContinuousLinearMap
