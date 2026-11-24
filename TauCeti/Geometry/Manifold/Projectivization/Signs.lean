/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.LinearAlgebra.Projectivization.Signs
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The derivative of a sign change of the homogeneous coordinates

A sign change `ε : Fin (n + 1) → ℤˣ` of the homogeneous coordinates acts on the projective space
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` by a diffeomorphism (`Projectivization.instContMDiffConstSMul`). In the
affine chart at `k` it is the linear map changing the signs of the affine coordinates by
`TauCeti.chartSigns ε k` (`TauCeti.affineChart_signs_smul`), so its derivative, read through the
derivative of that chart, is this linear map
(`TauCeti.mvfderiv_affineChart_mfderiv_signs_smul`).

At the coordinate point `[eₖ]`, which the sign changes fix, this determines the derivative of the
sign change as an endomorphism of the tangent space up to conjugation. For instance the reflection
negating the `k`-th coordinate acts on the tangent space at `[eₖ]` by `-1`
(`TauCeti.mfderiv_mulSingle_neg_one_smul_mk_single`). These derivatives are what the symmetries of
real projective space do to orientations of tangent spaces at its coordinate points, as used in
the signs of the integral Morse complex of `ℝℙ²`.
-/

public section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- **The derivative of a sign change in an affine chart.** At a point `x` of the affine open at
`k`, the derivative of the sign change `ε`, followed by the derivative of the affine chart at `k`
at `ε • x`, is the derivative of that chart at `x` followed by the change of signs
`chartSigns ε k` of the affine coordinates. -/
theorem mvfderiv_affineChart_mfderiv_signs_smul (ε : Fin (n + 1) → ℤˣ) (k : Fin (n + 1))
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∈ affineOpen k)
    (v : TangentSpace 𝓘(𝕜, Fin n → 𝕜) x) :
    mvfderiv 𝓘(𝕜, Fin n → 𝕜) (affineChart k) (ε • x)
        (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (ε • ·) x v) =
      chartSigns ε k • mvfderiv 𝓘(𝕜, Fin n → 𝕜) (affineChart k) x v := by
  set e := affineOpenPartialHomeomorph (K := 𝕜) k
  have he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, Fin n → 𝕜) 1 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
    affineOpenPartialHomeomorph_mem_maximalAtlas k
  -- The sign change of the affine coordinates, as a continuous linear map.
  set S : (Fin n → 𝕜) →L[𝕜] Fin n → 𝕜 :=
    ContinuousLinearMap.pi fun j ↦ ((chartSigns ε k j : ℤ) : 𝕜) • ContinuousLinearMap.proj j
  have hS (z : Fin n → 𝕜) : S z = chartSigns ε k • z := by
    ext j
    simp [S, Units.smul_def, zsmul_eq_mul]
  -- In the chart `e`, the sign change is `S`.
  have hEq : Set.EqOn (e ∘ (ε • ·)) (S ∘ e) e.source := fun y _ ↦ by
    simp [e, hS, affineChart_signs_smul]
  have hxe : x ∈ e.source := by simpa [e] using hx
  have hεx : ε • x ∈ e.source := by simpa [e] using hx
  have h := mfderiv_eq_fderiv_comp_of_eqOn he hEq hxe
  rw [S.fderiv] at h
  have hc := mvfderiv_comp_apply (g := (e : _ → Fin n → 𝕜)) (f := fun y ↦ ε • y) x
    (mdifferentiableAt_of_mem_maximalAtlas he hεx)
    ((contMDiff_const_smul ε (n := 1)).mdifferentiableAt one_ne_zero) v
  rw [← hS, ← coe_affineOpenPartialHomeomorph]
  exact hc.symm.trans (DFunLike.congr_fun h v)

/-- **A reflection acts by `-1` at a coordinate point.** The reflection
`Pi.mulSingle k (-1)` negating the `k`-th homogeneous coordinate fixes the coordinate point `[eₖ]`
(`TauCeti.signs_smul_mk_single`) and acts on its tangent space by `-1`, since it changes the sign
of every affine coordinate of the chart at `k`. -/
theorem mfderiv_mulSingle_neg_one_smul_mk_single (k : Fin (n + 1))
    (v : TangentSpace 𝓘(𝕜, Fin n → 𝕜) (mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp))) :
    mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ((Pi.mulSingle k (-1) : Fin (n + 1) → ℤˣ) • ·)
      (mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp)) v = -v := by
  have hx : mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp) ∈ affineOpen k := by simp
  have h := mvfderiv_affineChart_mfderiv_signs_smul (Pi.mulSingle k (-1)) k hx v
  have hneg (w : Fin n → 𝕜) : (-1 : Fin n → ℤˣ) • w = -w := by
    ext j
    simp
  rw [chartSigns_mulSingle_neg_one_self, signs_smul_mk_single, hneg, ← map_neg,
    ← coe_affineOpenPartialHomeomorph] at h
  have hinj := (isInvertible_mfderiv_chart
    (affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜' := 𝕜) k)
    (y := mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp)) (by simp)).injective
  exact hinj h

end TauCeti
