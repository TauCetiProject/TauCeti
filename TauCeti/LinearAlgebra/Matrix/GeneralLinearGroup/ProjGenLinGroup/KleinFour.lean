/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InvariantLine
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.ProjectiveImage
import TauCeti.GroupTheory.SpecificGroups.KleinFour
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonzeroTrace
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Involutions of `PGL(2, K)` and Klein four projective images

An invertible `2 × 2` matrix `g` over a field `K` maps to an involution of `PGL(2, K)` exactly
when it is traceless, provided `2 ≠ 0` in `K`: by Cayley–Hamilton `g ^ 2 = trace g • g - det g • 1`,
so `g ^ 2` is scalar for traceless `g`, while if `g ^ 2` is scalar and `trace g ≠ 0` then `g` itself
is scalar. Lifts `a`, `b` of two distinct nontrivial commuting involutions of `PGL(2, K)` therefore
have `a`, `b` and `a * b` traceless, and the polarized Cayley–Hamilton identity makes them
anticommute: `a * b = -(b * a)`.

Consequently a two-dimensional representation whose projective image is a Klein four group has no
invariant line when `2 ≠ 0`. This is the exceptional branch of the reducibility criterion for
determinant kernels of residual representations (Caraiani–Newton, Lemma 5.6.5): under that
lemma's trace hypothesis `(tr ρ g)² = (1 + det ρ g)²` whenever `det ρ g ≠ 1`, when the projective
image is `A₄` and the determinant has order three, the determinant kernel has projective image
`(ℤ/2)²`. This file handles that Klein four case, showing that such a determinant kernel fixes no
line. In characteristic `2` the statement fails: the
upper unitriangular matrices over `𝔽₄` have Klein four projective image and fix a line.

## Main results

* `Matrix.ProjGenLinGroup.trace_eq_zero_of_mk_sq_eq_one`: a lift of a nontrivial involution of
  `PGL(2, K)` is traceless.
* `Matrix.ProjGenLinGroup.mk_sq_eq_one_of_trace_eq_zero`,
  `Matrix.ProjGenLinGroup.mk_ne_one_of_trace_eq_zero`,
  `Matrix.ProjGenLinGroup.orderOf_mk_eq_two_iff_trace_eq_zero`: conversely a traceless matrix maps
  to an involution, nontrivial when `2 ≠ 0`.
* `Matrix.ProjGenLinGroup.mul_eq_neg_mul_of_mk_sq_eq_one`: lifts of the nontrivial elements of a
  Klein four subgroup of `PGL(2, K)` anticommute.
* `MonoidHom.not_hasInvariantLine_of_mk_sq_eq_one`,
  `MonoidHom.not_hasInvariantLine_of_isKleinFour`,
  `MonoidHom.not_hasInvariantLine_of_mulEquiv`: a representation whose projective image
  contains, or is, a Klein four group has no invariant line when `2 ≠ 0`.

## References

* A. Caraiani, J. Newton, *On the modularity of elliptic curves over imaginary quadratic fields*,
  Lemma 5.6.5, pp. 85–86.
-/

public section

open Matrix

open scoped MatrixGroups

namespace Matrix.ProjGenLinGroup

section CommRing

variable {R : Type*} [CommRing R] {g : GL (Fin 2) R}

/-- A traceless invertible `2 × 2` matrix squares to the scalar `-det g`, so its class in
`PGL(2, R)` squares to the identity. -/
theorem mk_sq_eq_one_of_trace_eq_zero (h : (g : Matrix (Fin 2) (Fin 2) R).trace = 0) :
    mk g ^ 2 = 1 := by
  rw [← map_pow, sq, mk_eq_one]
  exact GeneralLinearGroup.mul_self_mem_center_of_trace_eq_zero h

/-- A traceless invertible `2 × 2` matrix is not scalar when `2 ≠ 0`, since a scalar `u` has
trace `2 u`. -/
theorem mk_ne_one_of_trace_eq_zero (h2 : (2 : R) ≠ 0)
    (h : (g : Matrix (Fin 2) (Fin 2) R).trace = 0) : mk g ≠ 1 := by
  rw [Ne, mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨u, rfl⟩
  -- The trace of the scalar `u` is `2 * u`, so `2 = 0` since `u` is a unit.
  exact h2 (by simpa using h)

end CommRing

variable {K : Type*} [Field K] {g : GL (Fin 2) K}

/-- **A lift of a nontrivial involution of `PGL(2, K)` is traceless.** If `g ^ 2 = c • 1` and
`trace g ≠ 0`, Cayley–Hamilton exhibits `g` as the scalar `(c + det g) / trace g`. -/
theorem trace_eq_zero_of_mk_sq_eq_one (hsq : mk g ^ 2 = 1) (hne : mk g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
  rw [← map_pow, mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hsq
  obtain ⟨c, hc⟩ := hsq
  by_contra htr
  have hg2 : (g : Matrix (Fin 2) (Fin 2) K) ^ 2 = c • 1 := by
    simpa [smul_one_eq_diagonal] using hc.symm
  -- Cayley–Hamilton with `g ^ 2 = c • 1` exhibits `trace g • g` as a scalar.
  have hCH : (g : Matrix (Fin 2) (Fin 2) K).trace • (g : Matrix (Fin 2) (Fin 2) K) =
      (c + (g : Matrix (Fin 2) (Fin 2) K).det) • 1 := by
    rw [add_smul, ← hg2, sq_eq_trace_smul_sub_det_smul_one_fin_two, sub_add_cancel]
  refine hne (mk_eq_one.2 (GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
    ⟨(g : Matrix (Fin 2) (Fin 2) K).trace⁻¹ * (c + (g : Matrix (Fin 2) (Fin 2) K).det), ?_⟩))
  rw [scalar_apply, ← smul_one_eq_diagonal, mul_smul, ← hCH]
  simp [smul_smul, htr]

/-- When `2 ≠ 0`, the class of an invertible `2 × 2` matrix in `PGL(2, K)` has order two exactly
when the matrix is traceless. -/
theorem orderOf_mk_eq_two_iff_trace_eq_zero (h2 : (2 : K) ≠ 0) :
    orderOf (mk g) = 2 ↔ (g : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
  rw [orderOf_eq_prime_iff]
  exact ⟨fun h ↦ trace_eq_zero_of_mk_sq_eq_one h.1 h.2,
    fun h ↦ ⟨mk_sq_eq_one_of_trace_eq_zero h, mk_ne_one_of_trace_eq_zero h2 h⟩⟩

/-- **Lifts of a Klein four subgroup of `PGL(2, K)` anticommute.** If the classes of `a`, `b` and
`a * b` are nontrivial involutions, then `a`, `b` and `a * b` are traceless, hence
`a * b = -(b * a)`. -/
theorem mul_eq_neg_mul_of_mk_sq_eq_one {a b : GL (Fin 2) K} (ha : mk a ^ 2 = 1) (hb : mk b ^ 2 = 1)
    (hab : mk (a * b) ^ 2 = 1) (ha₁ : mk a ≠ 1) (hb₁ : mk b ≠ 1) (hab₁ : mk (a * b) ≠ 1) :
    (a : Matrix (Fin 2) (Fin 2) K) * b = -((b : Matrix (Fin 2) (Fin 2) K) * a) := by
  refine mul_eq_neg_mul_of_trace_eq_zero_fin_two (trace_eq_zero_of_mk_sq_eq_one ha ha₁)
    (trace_eq_zero_of_mk_sq_eq_one hb hb₁) ?_
  rw [← Units.val_mul]
  exact trace_eq_zero_of_mk_sq_eq_one hab hab₁

end Matrix.ProjGenLinGroup

namespace MonoidHom

section Monoid

variable {G : Type*} [Monoid G] {K : Type*} [Field K] {ρ : G →* GL (Fin 2) K}

/-- If the classes of `ρ g`, `ρ h` and `ρ (g * h)` are nontrivial involutions of `PGL(2, K)`, that
is, the projective image of `ρ` contains a Klein four group, then `ρ` has no invariant line when
`2 ≠ 0`. -/
theorem not_hasInvariantLine_of_mk_sq_eq_one (h2 : (2 : K) ≠ 0) {g h : G}
    (hg : ProjGenLinGroup.mk (ρ g) ^ 2 = 1) (hh : ProjGenLinGroup.mk (ρ h) ^ 2 = 1)
    (hgh : ProjGenLinGroup.mk (ρ (g * h)) ^ 2 = 1) (hg₁ : ProjGenLinGroup.mk (ρ g) ≠ 1)
    (hh₁ : ProjGenLinGroup.mk (ρ h) ≠ 1) (hgh₁ : ProjGenLinGroup.mk (ρ (g * h)) ≠ 1) :
    ¬ ρ.HasInvariantLine := by
  rw [map_mul] at hgh hgh₁
  exact not_hasInvariantLine_of_mul_eq_neg_mul h2
    (ProjGenLinGroup.mul_eq_neg_mul_of_mk_sq_eq_one hg hh hgh hg₁ hh₁ hgh₁)

end Monoid

variable {G : Type*} [Group G] {K : Type*} [Field K] {ρ : G →* GL (Fin 2) K}

/-- **A representation with Klein four projective image has no invariant line** when `2 ≠ 0`. -/
theorem not_hasInvariantLine_of_isKleinFour (h2 : (2 : K) ≠ 0) [IsKleinFour ρ.projectiveImage] :
    ¬ ρ.HasInvariantLine := by
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ρ.projectiveImage)
    (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  -- Two generators `x`, `y` of the Klein four group, with `x`, `y` and `x * y` nontrivial.
  set x := e.symm (Multiplicative.ofAdd (1, 0))
  set y := e.symm (Multiplicative.ofAdd (0, 1))
  have hsq (z : ρ.projectiveImage) : (z : PGL(2, K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, sq, IsKleinFour.mul_self, Subgroup.coe_one]
  have hne {z : ρ.projectiveImage} (hz : e z ≠ 1) : (z : PGL(2, K)) ≠ 1 := by
    rw [Ne, OneMemClass.coe_eq_one, ← e.map_eq_one_iff]
    exact hz
  obtain ⟨g, hg⟩ := ρ.mem_projectiveImage.1 x.property
  obtain ⟨h, hh⟩ := ρ.mem_projectiveImage.1 y.property
  have hgh : ProjGenLinGroup.mk (ρ (g * h)) = ((x * y : ρ.projectiveImage) : PGL(2, K)) := by
    rw [map_mul, map_mul, Subgroup.coe_mul, hg, hh]
  refine not_hasInvariantLine_of_mk_sq_eq_one h2 (g := g) (h := h) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hg, hsq]
  · rw [hh, hsq]
  · rw [hgh, hsq]
  · rw [hg]
    exact hne (by simp [x])
  · rw [hh]
    exact hne (by simp [y])
  · rw [hgh]
    exact hne (by simp only [x, y, map_mul, MulEquiv.apply_symm_apply]; decide)

/-- A representation whose projective image is isomorphic to `(ℤ/2)²` has no invariant line when
`2 ≠ 0`. This is the form of `not_hasInvariantLine_of_isKleinFour` for a projective image given
with an explicit isomorphism, as in the exceptional branch of Caraiani–Newton, Lemma 5.6.5. -/
theorem not_hasInvariantLine_of_mulEquiv (h2 : (2 : K) ≠ 0)
    (e : ρ.projectiveImage ≃* Multiplicative (ZMod 2 × ZMod 2)) : ¬ ρ.HasInvariantLine :=
  have := e.symm.isKleinFour
  not_hasInvariantLine_of_isKleinFour h2

end MonoidHom
