/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Graded.BesselGroup

/-!
# The unipotent character of a graded hermitian form

Let `R` be a commutative ring with an involution, `J = TauCeti.gradedGram X s N` the graded Gram
matrix on `X ⊕ Fin s`, `𝔢 = TauCeti.gradedShift X s N c` its shift for a constant `c`, and
`ψ : AddChar R M` an additive character. The **unipotent character** is the function
`ψ_U (g) = ψ (tr (𝔢 g))` on the isometries `g` of `J` (`TauCeti.gradedUnipotentChar`). For
`ψ` the standard character of the adeles of a CM field `E` twisted by `j / 2` (that is,
`AddChar.mulShift ψ (j / 2)`), this is the character `u ↦ ψ (j / 2 * tr (𝔢 u))` of the unipotent
group
of a graded hermitian space by which the Bessel and Fourier–Jacobi models of automorphic forms
transform, in the unfolding of a period of a theta lift along the flag of the grades.

Since the shift lowers the grade by exactly two, `tr (𝔢 A)` only sees the entries of `A` that raise
the grade by exactly two. Hence:

* `ψ_U` is multiplicative on the second term `U^{≥2}` of the degree filtration of the unipotent
  group of the grades (`TauCeti.gradedUnipotentFiltration X s N 2`), the isometries `g` for which
  `g - 1` raises the grade by at least two (`TauCeti.gradedUnipotentChar_mul`); it is the character
  `TauCeti.gradedUnipotentCharHom` of that group. For a string of odd length this group is the
  whole unipotent group of the grades (`TauCeti.gradedUnipotentFiltration_two`).
* `ψ_U` is invariant under conjugation by every isometry commuting with the shift, in particular by
  the copy of `U(X)` embedded as the `X`-block
  (`TauCeti.gradedUnipotentChar_gradedInclusion_mul_mul_inv`).
* `ψ_U` is trivial at every isometry whose matrix, like the constants `N` and `c`, comes from a
  subring `K` along a ring homomorphism `f : K →+* R` on which `ψ` is trivial
  (`TauCeti.gradedUnipotentChar_eq_one_of_coe_eq_map`); for the adeles of `E` and `K = E` these are
  the rational points.
* `ψ_U` is continuous when `ψ` is (`TauCeti.continuous_gradedUnipotentChar`).

## Main definitions

* `TauCeti.gradedUnipotentChar X s N c ψ`: the function `g ↦ ψ (tr (𝔢 g))`.
* `TauCeti.gradedUnipotentCharHom X s N c ψ`: its restriction to `U^{≥2}`, as a homomorphism.

## Main results

* `TauCeti.trace_gradedShift_mul_mul`: `tr (𝔢 (A B)) = tr (𝔢 A) + tr (𝔢 B)` when `A - 1` and
  `B - 1` raise the grade by `d` and `d'` with `2 < d + d'`.
* `TauCeti.gradedUnipotentChar_mul`: the corresponding multiplicativity of `ψ_U`.
* `TauCeti.gradedUnipotentChar_mul_mul_inv`,
  `TauCeti.gradedUnipotentChar_gradedInclusion_mul_mul_inv`: invariance under conjugation.
* `TauCeti.gradedUnipotentChar_eq_one_of_coe_eq_map`: triviality on rational points.
* `TauCeti.continuous_gradedUnipotentChar`: continuity.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Weil/Periods/Equivariant.lean`
  (declarations `New.Grading.unipotentChar`, `New.Grading.unipotentChar_mul`,
  `New.Grading.unipotentChar_of_mem_Gamma`, `New.Grading.unipotentChar_conj`,
  `New.Grading.trace_shift_mul`, `New.Grading.commute_shift_ratCoordMatrix_inclX`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The statements follow these declarations, recast for the
  isometries of the graded Gram matrix over any commutative ring with involution and any additive
  character; the proof of multiplicativity here uses the degree bound on `𝔢 (A - 1) (B - 1)`
  instead of the degree-two part of a matrix.
* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical
  L-values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), Section 12, for the generic characters of the unipotent radicals of
  Bessel subgroups.
-/

public section

open Matrix

namespace TauCeti

/-! ### The unipotent character -/

section Char

variable {R : Type*} [CommRing R] [StarRing R] {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}
  {N : R} {M : Type*} [Monoid M]

variable (X s N) in
/-- The **unipotent character** `ψ_U (g) = ψ (tr (𝔢 g))` of the graded Gram matrix, for the shift
`𝔢 = gradedShift X s N c` and an additive character `ψ`; it is multiplicative on the isometries `g`
for which `g - 1` raises the grade by at least two (`gradedUnipotentChar_mul`). -/
def gradedUnipotentChar (c : R) (ψ : AddChar R M) (g : unitaryGroupOf (gradedGram X s N)) : M :=
  ψ (gradedShift X s N c * ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)).trace

variable {c : R} {ψ : AddChar R M}

/-- Unfolding `TauCeti.gradedUnipotentChar`. -/
theorem gradedUnipotentChar_apply (g : unitaryGroupOf (gradedGram X s N)) :
    gradedUnipotentChar X s N c ψ g =
      ψ (gradedShift X s N c * ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)).trace :=
  (rfl)

/-- The unipotent character is `1` at the identity, since the shift has trace zero. -/
@[simp]
theorem gradedUnipotentChar_one : gradedUnipotentChar X s N c ψ 1 = 1 := by
  simp [gradedUnipotentChar_apply]

/-- **Multiplicativity of the unipotent character.** If `g - 1` and `h - 1` raise the grade by at
least `d` and `d'` with `2 < d + d'`, then `ψ_U (g h) = ψ_U (g) ψ_U (h)`. -/
theorem gradedUnipotentChar_mul {d d' : ℤ} (hdd' : 2 < d + d')
    {g h : unitaryGroupOf (gradedGram X s N)}
    (hg : RaisesDegree (gradedGrade X s) d
      (((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1))
    (hh : RaisesDegree (gradedGrade X s) d'
      (((h : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) - 1)) :
    gradedUnipotentChar X s N c ψ (g * h) =
      gradedUnipotentChar X s N c ψ g * gradedUnipotentChar X s N c ψ h := by
  simp only [gradedUnipotentChar_apply, Subgroup.coe_mul, Units.val_mul,
    trace_gradedShift_mul_mul N c hdd' hg hh, AddChar.map_add_eq_mul]

variable (X s N c ψ) in
/-- The unipotent character as a character of the second term `U^{≥2}` of the degree filtration of
the unipotent group of the grades. -/
def gradedUnipotentCharHom : gradedUnipotentFiltration X s N 2 →* M where
  toFun g := gradedUnipotentChar X s N c ψ g
  map_one' := gradedUnipotentChar_one
  map_mul' g h := gradedUnipotentChar_mul (d := 2) (d' := 2) (by norm_num)
    (mem_gradedUnipotentFiltration_iff.1 g.property).2
    (mem_gradedUnipotentFiltration_iff.1 h.property).2

@[simp]
theorem gradedUnipotentCharHom_apply (g : gradedUnipotentFiltration X s N 2) :
    gradedUnipotentCharHom X s N c ψ g = gradedUnipotentChar X s N c ψ g :=
  (rfl)

/-- The unipotent character is invariant under conjugation by an isometry whose matrix commutes
with the shift. -/
theorem gradedUnipotentChar_mul_mul_inv {r : unitaryGroupOf (gradedGram X s N)}
    (hr : Commute (gradedShift X s N c)
      ((r : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R))
    (g : unitaryGroupOf (gradedGram X s N)) :
    gradedUnipotentChar X s N c ψ (r * g * r⁻¹) = gradedUnipotentChar X s N c ψ g := by
  simp only [gradedUnipotentChar_apply, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hr.eq,
    Matrix.mul_assoc _ (gradedShift X s N c), trace_units_conj (r : GL (X ⊕ Fin s) R)]

/-- The unipotent character is invariant under conjugation by the image of `U(X)`. -/
theorem gradedUnipotentChar_gradedInclusion_mul_mul_inv (a : unitaryGroup X R)
    (g : unitaryGroupOf (gradedGram X s N)) :
    gradedUnipotentChar X s N c ψ
        (gradedInclusion X s N a * g * (gradedInclusion X s N a)⁻¹) =
      gradedUnipotentChar X s N c ψ g :=
  gradedUnipotentChar_mul_mul_inv (by
    rw [coe_gradedInclusion]
    exact commute_gradedShift_fromBlocks N c _) g

/-- **The unipotent character is trivial on rational points.** Let `f : K →+* R` be a ring
homomorphism on whose image `ψ` is trivial, and let `N`, `c` and the matrix of `g` come from `K`
along `f`. Then `ψ_U (g) = 1`. -/
theorem gradedUnipotentChar_eq_one_of_coe_eq_map {K : Type*} [Ring K] (f : K →+* R)
    (hψ : ∀ x, ψ (f x) = 1) {N₀ c₀ : K} (hN : f N₀ = N) (hc : f c₀ = c)
    {g : unitaryGroupOf (gradedGram X s N)} {A : Matrix (X ⊕ Fin s) (X ⊕ Fin s) K}
    (hA : ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) = A.map f) :
    gradedUnipotentChar X s N c ψ g = 1 := by
  have htrace : (gradedShift X s N c *
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R)).trace =
      f (gradedShift X s N₀ c₀ * A).trace := by
    rw [hA, ← hN, ← hc, ← gradedShift_map, ← Matrix.map_mul, AddMonoidHom.map_trace]
  rw [gradedUnipotentChar_apply, htrace, hψ]

/-- The unipotent character is continuous when the additive character is. -/
@[fun_prop]
theorem continuous_gradedUnipotentChar [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
    [TopologicalSpace M] (hψ : Continuous ψ) : Continuous (gradedUnipotentChar X s N c ψ) := by
  have hval : Continuous fun g : unitaryGroupOf (gradedGram X s N) ↦
      ((g : GL (X ⊕ Fin s) R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R) :=
    Units.continuous_val.comp continuous_subtypeVal
  exact hψ.comp (continuous_const.matrix_mul hval).matrix_trace

end Char

end TauCeti
