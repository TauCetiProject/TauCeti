/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Complex coordinates for quaternionic derivatives

Writing `q = v + j w`, where `v = t + i x` and `w = y - i z`, gives two useful real
continuous linear equivalences with `ℂ × ℂ`. The left coordinates `(v, conj w)` intertwine
left complex multiplication with ordinary complex scalar multiplication; the right coordinates
`(v, w)` intertwine right complex multiplication with that same scalar multiplication.
No extra scalar-action instance is placed on the quaternions.

Consequently, right quaternion multiplication becomes complex-linear in the left coordinates,
and left quaternion multiplication becomes complex-linear in the right coordinates. We bundle
these operators and identify their real restrictions. Transporting a real derivative of either
multiplication shape therefore gives a complex derivative, the regularity input for rigidity
of one-sided quaternionic differentiation.

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, Theorem 1, for the rigidity of one-sided quaternionic differentiation.
* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.1, for quaternion multiplication conventions.
-/

public section

open Quaternion

namespace TauCeti

/-- The coordinates `(t + i x, y + i z)` adapted to left complex multiplication. -/
noncomputable def leftComplexCoords : ℍ ≃L[ℝ] ℂ × ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun q => (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩)
      invFun := fun z => ⟨z.1.re, z.1.im, z.2.re, z.2.im⟩
      left_inv := fun q => by ext <;> rfl
      right_inv := fun z => by ext <;> rfl
      map_add' := fun q r => by ext <;> rfl
      map_smul' := fun r q => by
        apply Prod.ext <;> apply Complex.ext <;> simp }

-- Coordinate expansions are explicit: simp preserves the coordinate maps so that it can use
-- their multiplication and scalar-action rules without expanding into real components.
theorem _root_.Quaternion.leftComplexCoords_apply (q : ℍ) :
    leftComplexCoords q = (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩) := (rfl)

theorem leftComplexCoords_symm_apply (z : ℂ × ℂ) :
    leftComplexCoords.symm z = ⟨z.1.re, z.1.im, z.2.re, z.2.im⟩ := (rfl)

/-- The coordinates `(t + i x, y - i z)` adapted to right complex multiplication. -/
noncomputable def rightComplexCoords : ℍ ≃L[ℝ] ℂ × ℂ :=
  leftComplexCoords.trans
    ((ContinuousLinearEquiv.refl ℝ ℂ).prodCongr Complex.conjCLE)

theorem _root_.Quaternion.rightComplexCoords_apply (q : ℍ) :
    rightComplexCoords q = (⟨q.re, q.imI⟩, ⟨q.imJ, -q.imK⟩) := by
  apply Prod.ext <;> apply Complex.ext <;>
    simp [rightComplexCoords, leftComplexCoords_apply]

theorem rightComplexCoords_symm_apply (z : ℂ × ℂ) :
    rightComplexCoords.symm z = ⟨z.1.re, z.1.im, z.2.re, -z.2.im⟩ := by
  apply rightComplexCoords.injective
  simp [rightComplexCoords_apply]

/-- The two coordinate choices differ by conjugation of the second component. -/
theorem _root_.Quaternion.leftComplexCoords_eq_prodMap_star_rightComplexCoords (q : ℍ) :
    leftComplexCoords q = Prod.map id star (rightComplexCoords q) := by
  apply Prod.ext <;> apply Complex.ext <;>
    simp [leftComplexCoords_apply, rightComplexCoords_apply]

/-- Changing from left to right coordinates conjugates the second component. -/
@[simp]
theorem rightComplexCoords_leftComplexCoords_symm (z : ℂ × ℂ) :
    rightComplexCoords (leftComplexCoords.symm z) = (z.1, star z.2) := by
  simpa [Prod.map] using (congrArg (Prod.map id star)
    (leftComplexCoords_eq_prodMap_star_rightComplexCoords (leftComplexCoords.symm z))).symm

/-- Reconstruction in the convention `q = v + j w`. -/
theorem _root_.Quaternion.eq_coeComplex_add_j_mul (q : ℍ) :
    q = ((rightComplexCoords q).1 : ℍ) +
      (⟨0, 0, 1, 0⟩ : ℍ) * ((rightComplexCoords q).2 : ℍ) := by
  ext <;> simp [rightComplexCoords_apply]

/-- In right coordinates, `v + j w` has components `(v, w)`. -/
@[simp]
theorem rightComplexCoords_coeComplex_add_j_mul (v w : ℂ) :
    rightComplexCoords ((v : ℍ) + (⟨0, 0, 1, 0⟩ : ℍ) * (w : ℍ)) = (v, w) := by
  apply Prod.ext <;> apply Complex.ext <;> simp [rightComplexCoords_apply]

/-- In left coordinates, `v + j w` has components `(v, conj w)`. -/
@[simp]
theorem leftComplexCoords_coeComplex_add_j_mul (v w : ℂ) :
    leftComplexCoords ((v : ℍ) + (⟨0, 0, 1, 0⟩ : ℍ) * (w : ℍ)) = (v, star w) := by
  simp only [leftComplexCoords_eq_prodMap_star_rightComplexCoords,
    rightComplexCoords_coeComplex_add_j_mul, Prod.map, id_eq]

/-- Conjugating a function expressed as `g(v,w) + j h(v,w)` by the right coordinates
leaves both component functions unchanged. -/
theorem rightComplexCoords_comp_comp_symm_apply {f : ℍ → ℍ} {g h : ℂ × ℂ → ℂ}
    (hf : ∀ q, f q = (g (rightComplexCoords q) : ℍ) +
      (⟨0, 0, 1, 0⟩ : ℍ) * (h (rightComplexCoords q) : ℍ)) (z : ℂ × ℂ) :
    (rightComplexCoords ∘ f ∘ rightComplexCoords.symm) z = (g z, h z) := by
  simp only [Function.comp_apply, hf, rightComplexCoords_coeComplex_add_j_mul,
    ContinuousLinearEquiv.apply_symm_apply]

/-- In the left-coordinate conjugate, the second input and the second output are both
conjugated; conjugating only the output would give the wrong function. -/
theorem leftComplexCoords_comp_comp_symm_apply {f : ℍ → ℍ} {g h : ℂ × ℂ → ℂ}
    (hf : ∀ q, f q = (g (rightComplexCoords q) : ℍ) +
      (⟨0, 0, 1, 0⟩ : ℍ) * (h (rightComplexCoords q) : ℍ)) (z : ℂ × ℂ) :
    (leftComplexCoords ∘ f ∘ leftComplexCoords.symm) z =
      (g (z.1, star z.2), star (h (z.1, star z.2))) := by
  simp only [Function.comp_apply, hf, leftComplexCoords_coeComplex_add_j_mul,
    rightComplexCoords_leftComplexCoords_symm]

/-- Left complex multiplication is scalar multiplication in the left coordinates. -/
@[simp]
theorem leftComplexCoords_coeComplex_mul (c : ℂ) (q : ℍ) :
    leftComplexCoords ((c : ℍ) * q) = c • leftComplexCoords q := by
  apply Prod.ext <;> apply Complex.ext <;> simp [leftComplexCoords_apply]

/-- Right complex multiplication is scalar multiplication in the right coordinates. -/
@[simp]
theorem rightComplexCoords_mul_coeComplex (c : ℂ) (q : ℍ) :
    rightComplexCoords (q * (c : ℍ)) = c • rightComplexCoords q := by
  apply Prod.ext <;> apply Complex.ext <;> simp [rightComplexCoords_apply] <;> ring

@[simp]
theorem leftComplexCoords_symm_smul (c : ℂ) (z : ℂ × ℂ) :
    leftComplexCoords.symm (c • z) = (c : ℍ) * leftComplexCoords.symm z := by
  apply leftComplexCoords.injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, leftComplexCoords_coeComplex_mul]

@[simp]
theorem rightComplexCoords_symm_smul (c : ℂ) (z : ℂ × ℂ) :
    rightComplexCoords.symm (c • z) = rightComplexCoords.symm z * (c : ℍ) := by
  apply rightComplexCoords.injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, rightComplexCoords_mul_coeComplex]

end TauCeti

namespace Quaternion

open TauCeti

/-- Right quaternion multiplication, complex-linear in the left coordinates. -/
noncomputable def mulRightComplex (b : ℍ) : (ℂ × ℂ) →L[ℂ] ℂ × ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => leftComplexCoords (leftComplexCoords.symm z * b)
      map_add' := fun z w => by simp only [map_add, add_mul]
      map_smul' := fun c z => by
        simp only [leftComplexCoords_symm_smul, mul_assoc, leftComplexCoords_coeComplex_mul,
          RingHom.id_apply] }

/-- Left quaternion multiplication, complex-linear in the right coordinates. -/
noncomputable def mulLeftComplex (a : ℍ) : (ℂ × ℂ) →L[ℂ] ℂ × ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => rightComplexCoords (a * rightComplexCoords.symm z)
      map_add' := fun z w => by simp only [map_add, mul_add]
      map_smul' := fun c z => by
        simp only [rightComplexCoords_symm_smul, ← mul_assoc, rightComplexCoords_mul_coeComplex,
          RingHom.id_apply] }

@[simp]
theorem mulRightComplex_apply (b : ℍ) (z : ℂ × ℂ) :
    mulRightComplex b z = leftComplexCoords (leftComplexCoords.symm z * b) := (rfl)

@[simp]
theorem mulLeftComplex_apply (a : ℍ) (z : ℂ × ℂ) :
    mulLeftComplex a z = rightComplexCoords (a * rightComplexCoords.symm z) := (rfl)

/-- The real restriction of the complex right-multiplication operator is the transported
real right-multiplication operator. -/
theorem mulRightComplex_restrictScalars (b : ℍ) :
    (mulRightComplex b).restrictScalars ℝ =
      leftComplexCoords.toContinuousLinearMap.comp
        (((ContinuousLinearMap.mul ℝ ℍ).flip b).comp
          leftComplexCoords.symm.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro z
  simp

/-- The real restriction of the complex left-multiplication operator is the transported
real left-multiplication operator. -/
theorem mulLeftComplex_restrictScalars (a : ℍ) :
    (mulLeftComplex a).restrictScalars ℝ =
      rightComplexCoords.toContinuousLinearMap.comp
        ((ContinuousLinearMap.mul ℝ ℍ a).comp
          rightComplexCoords.symm.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro z
  simp

end Quaternion

namespace HasFDerivAt

open TauCeti

/-- A real right-multiplication derivative becomes a complex derivative in left coordinates. -/
theorem leftComplexCoords {f : ℍ → ℍ} {q b : ℍ}
    (hf : HasFDerivAt f ((ContinuousLinearMap.mul ℝ ℍ).flip b) q) :
    HasFDerivAt (leftComplexCoords ∘ f ∘ leftComplexCoords.symm)
      (mulRightComplex b) (leftComplexCoords q) := by
  apply hasFDerivAt_of_restrictScalars (𝕜 := ℝ)
    (g' := (mulRightComplex b).restrictScalars ℝ)
  · rw [mulRightComplex_restrictScalars, TauCeti.leftComplexCoords.comp_hasFDerivAt_iff,
      TauCeti.leftComplexCoords.symm.comp_right_hasFDerivAt_iff]
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  · rfl

/-- A real left-multiplication derivative becomes a complex derivative in right coordinates. -/
theorem rightComplexCoords {f : ℍ → ℍ} {q a : ℍ}
    (hf : HasFDerivAt f (ContinuousLinearMap.mul ℝ ℍ a) q) :
    HasFDerivAt (rightComplexCoords ∘ f ∘ rightComplexCoords.symm)
      (mulLeftComplex a) (rightComplexCoords q) := by
  apply hasFDerivAt_of_restrictScalars (𝕜 := ℝ)
    (g' := (mulLeftComplex a).restrictScalars ℝ)
  · rw [mulLeftComplex_restrictScalars, TauCeti.rightComplexCoords.comp_hasFDerivAt_iff,
      TauCeti.rightComplexCoords.symm.comp_right_hasFDerivAt_iff]
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  · rfl

end HasFDerivAt
