/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.RingTheory.AlgebraTower
public import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# The canonical real orientation of a complex vector space

A complex basis `b` of a complex vector space `E` determines the real basis
`(b₀, I • b₀, b₁, I • b₁, …)` of `E` (`Module.Basis.complexToReal`). The real change-of-basis
determinant between two such real bases is the squared modulus of the complex one
(`Module.Basis.det_complexToReal`), so it is positive and all complex bases induce the same real
orientation. A finite-dimensional complex vector space therefore carries a canonical real
orientation `TauCeti.complexOrientation E`, which involves no choice of basis. Complex-linear
equivalences transport it, so complex-linear automorphisms preserve it. On `ℂ` itself it is
Mathlib's standard orientation `Complex.orientation`.

This is the linear model for the canonical orientation of a complex manifold, whose chart
transitions have complex-linear derivatives.

The real module structure of `E` is an ambient one compatible with the complex structure
(`IsScalarTower ℝ ℂ E`), as for a complex normed space or a real space with a complex structure.

## Main definitions

* `Module.Basis.complexToReal`: the real basis `(b i, I • b i)` underlying a complex basis `b`.
* `TauCeti.complexOrientation`: the canonical real orientation of a complex vector space, indexed
  by `Fin (2 * finrank ℂ E)`.

## Main results

* `Module.Basis.det_complexToReal`: the real determinant between the real bases underlying two
  complex bases is the squared modulus of their complex determinant.
* `Module.Basis.orientation_complexToReal_eq`: all complex bases give the same real orientation.
* `Module.Basis.complexOrientation_eq`: every complex basis computes the canonical orientation.
* `LinearEquiv.map_complexOrientation`: complex-linear equivalences transport canonical
  orientations.
* `TauCeti.reindex_complexOrientation_complex`: on `ℂ`, the canonical orientation is
  `Complex.orientation`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §1.
* D. Huybrechts, *Complex Geometry: An Introduction*, §1.2.
-/

public section

open Module

namespace Module.Basis

variable {ι ι' E F : Type*}
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-- The real basis underlying a complex basis `b`: its vectors are `b i` at index `(i, 0)` and
`I • b i` at index `(i, 1)`. -/
noncomputable def complexToReal (b : Basis ι ℂ E) : Basis (ι × Fin 2) ℝ E :=
  Complex.basisOneI.smulTower' b

/-- The vectors of the real basis `b.complexToReal` are `Complex.basisOneI k • b i`, that is,
`b i` and `I • b i`. -/
@[simp]
theorem complexToReal_apply (b : Basis ι ℂ E) (i : ι) (k : Fin 2) :
    b.complexToReal (i, k) = Complex.basisOneI k • b i :=
  smulTower'_apply _ _ _

/-- The real coordinates of a vector in the basis `b.complexToReal` are the real and imaginary
parts of its complex coordinates in `b`. -/
@[simp]
theorem complexToReal_repr_apply (b : Basis ι ℂ E) (x : E) (i : ι) (k : Fin 2) :
    b.complexToReal.repr x (i, k) = Complex.basisOneI.repr (b.repr x i) k :=
  smulTower'_repr _ _ _ _

/-- The real basis underlying a complex basis is natural in complex-linear equivalences. -/
theorem complexToReal_map (b : Basis ι ℂ E) (f : E ≃ₗ[ℂ] F) :
    (b.map f).complexToReal = b.complexToReal.map (f.restrictScalars ℝ) :=
  eq_of_apply_eq fun ⟨i, k⟩ ↦ by simp

/-- Reindexing a complex basis reindexes its underlying real basis. -/
theorem complexToReal_reindex (b : Basis ι ℂ E) (e : ι ≃ ι') :
    (b.reindex e).complexToReal = b.complexToReal.reindex (e.prodCongr (Equiv.refl _)) :=
  eq_of_apply_eq fun ⟨i, k⟩ ↦ by simp

variable [Fintype ι] [DecidableEq ι]

/-- The real determinant between the real bases underlying two complex bases is the squared
modulus of their complex determinant. -/
theorem det_complexToReal (b c : Basis ι ℂ E) :
    b.complexToReal.det c.complexToReal = Complex.normSq (b.det c) := by
  -- `c` is the image of `b` under the complex-linear automorphism `f` with `f (b i) = c i`.
  set f : E ≃ₗ[ℂ] E := b.equiv c (Equiv.refl ι)
  have hc : c = b.map f := by simp [f, map_equiv]
  have hcR : ⇑c.complexToReal = (f.restrictScalars ℝ : E →ₗ[ℝ] E) ∘ b.complexToReal := by
    rw [hc, complexToReal_map, coe_map, LinearEquiv.coe_coe]
  have hcC : ⇑c = (f : E →ₗ[ℂ] E) ∘ b := by
    rw [hc, coe_map, LinearEquiv.coe_coe]
  rw [hcR, hcC]
  simp only [det_comp, det_self, mul_one]
  exact LinearMap.det_restrictScalars_eq_normSq _

/-- Any two complex bases induce the same real orientation. -/
theorem orientation_complexToReal_eq (b c : Basis ι ℂ E) :
    b.complexToReal.orientation = c.complexToReal.orientation := by
  rw [orientation_eq_iff_det_pos, det_complexToReal]
  exact Complex.normSq_pos.mpr (b.isUnit_det c).ne_zero

end Module.Basis

namespace TauCeti

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]

/-- The index equivalence `Fin n × Fin 2 ≃ Fin (2 * n)` sending `(i, k)` to `2 * i + k`. It orders
the real basis `b.complexToReal` as `(b₀, I • b₀, b₁, I • b₁, …)`. -/
def complexRealIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

/-- The position of `(i, k)` under `complexRealIndexEquiv` is `2 * i + k`. -/
@[simp]
theorem complexRealIndexEquiv_apply_val (n : ℕ) (i : Fin n) (k : Fin 2) :
    (complexRealIndexEquiv n (i, k) : ℕ) = 2 * i + k := by
  simp [complexRealIndexEquiv, Nat.add_comm]

/-- Casting along an equality of real dimensions commutes with `complexRealIndexEquiv`. -/
@[simp]
theorem cast_complexRealIndexEquiv {m n : ℕ} (h : 2 * m = 2 * n) (i : Fin m) (k : Fin 2) :
    Fin.cast h (complexRealIndexEquiv m (i, k)) =
      complexRealIndexEquiv n (Fin.cast (by omega) i, k) :=
  Fin.ext (by simp)

/-- The canonical real orientation of a finite-dimensional complex vector space `E`: the
orientation of the real basis `(b₀, I • b₀, b₁, I • b₁, …)` for any complex basis `b` of `E`
(`Module.Basis.complexOrientation_eq`). -/
noncomputable def complexOrientation : Orientation ℝ E (Fin (2 * finrank ℂ E)) :=
  Orientation.reindex ℝ E (complexRealIndexEquiv _) (finBasis ℂ E).complexToReal.orientation

end TauCeti

namespace Module.Basis

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]

/-- The canonical real orientation is the orientation of the real basis
`(b₀, I • b₀, b₁, I • b₁, …)` underlying any complex basis `b`. -/
theorem complexOrientation_eq (b : Basis (Fin (finrank ℂ E)) ℂ E) :
    TauCeti.complexOrientation E =
      Orientation.reindex ℝ E (TauCeti.complexRealIndexEquiv _) b.complexToReal.orientation := by
  rw [TauCeti.complexOrientation, orientation_complexToReal_eq (finBasis ℂ E) b]

end Module.Basis

namespace LinearEquiv

open TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]

/-- A complex-linear equivalence transports the canonical real orientation of its source to that
of its target, after identifying the index types through the equality of complex dimensions. -/
theorem map_complexOrientation (f : E ≃ₗ[ℂ] F) :
    Orientation.map _ (f.restrictScalars ℝ) (complexOrientation E) =
      Orientation.reindex ℝ F (finCongr (by rw [f.finrank_eq])) (complexOrientation F) := by
  set b := finBasis ℂ E
  rw [b.complexOrientation_eq, ((b.map f).reindex (finCongr f.finrank_eq)).complexOrientation_eq]
  simp only [← Basis.orientation_reindex, ← Basis.orientation_map, Basis.complexToReal_reindex,
    Basis.complexToReal_map]
  congr 1
  refine Basis.eq_of_apply_eq fun j ↦ ?_
  obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv _).surjective j
  simp

/-- Complex-linear automorphisms preserve the canonical real orientation. -/
@[simp]
theorem map_complexOrientation_self (f : E ≃ₗ[ℂ] E) :
    Orientation.map _ (f.restrictScalars ℝ) (complexOrientation E) = complexOrientation E := by
  simpa using f.map_complexOrientation

end LinearEquiv

namespace TauCeti

/-- On `ℂ`, the canonical real orientation is Mathlib's standard orientation, given by the basis
`(1, I)`. -/
theorem reindex_complexOrientation_complex :
    Orientation.reindex ℝ ℂ (finCongr (by simp)) (complexOrientation ℂ) = Complex.orientation := by
  set b : Basis (Fin (finrank ℂ ℂ)) ℂ ℂ :=
    (Basis.singleton (Fin 1) ℂ).reindex (finCongr (finrank_self ℂ).symm)
  rw [b.complexOrientation_eq, ← Basis.orientation_reindex, ← Basis.orientation_reindex,
    Complex.orientation]
  congr 1
  refine Basis.eq_of_apply_eq fun j ↦ ?_
  fin_cases j <;> simp [b, complexRealIndexEquiv, finProdFinEquiv, Fin.modNat]

end TauCeti
