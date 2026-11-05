/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Projectivization.Action
import TauCeti.LinearAlgebra.Matrix.Congruence
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The special isometry group of a sesquilinear Gram matrix

Let `σ` be an endomorphism of a commutative ring `K` and `Q` a square matrix over `K`. Together they
define the `σ`-sesquilinear form

```text
h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = ∑ i j, σ (x i) * Q i j * y j
```

on `n → K`, and a matrix `g` preserves it, `h(g x, g y) = h(x, y)`, exactly when
`(g ^ σ)ᵀ * Q * g = Q`, where `g ^ σ` applies `σ` to every entry. The matrices of determinant one
with this property form the subgroup `Matrix.specialIsometryGroup Q σ` of the special linear group.
For `σ` an involution and `Q` Hermitian or skew-Hermitian (`(Q ^ σ)ᵀ = ε • Q` with `ε = ±1`) this is
a special unitary group `SU(Q)`; for `σ = id` the defining equation is that of the bilinear isometry
monoid `Matrix.isometryMatrices Q`, and the group is the special orthogonal group of a symmetric `Q`
or the symplectic group of an alternating one. The finite special unitary groups `SU_{r+1}(q)`
arise in this form as the Steinberg fixed points of the twisted groups `²A_r(q)`.

Over a field the group acts on the projective space `ℙ K (n → K)` through the special linear group.
A point is *isotropic* when a representative `v` satisfies `h(v, v) = 0`; this does not depend on
the representative, and the isometries permute the isotropic points. They form the
sub-`MulAction` `Matrix.isotropicPoints Q σ`, the natural permutation domain of a unitary group.

## Main definitions

* `Matrix.specialIsometryGroup Q σ`: the matrices of determinant one preserving the
  `σ`-sesquilinear form of Gram matrix `Q`.
* `Matrix.isotropicPoints Q σ`: the isotropic points of projective space, as a sub-`MulAction` of
  the special isometry group.

## Main results

* `Matrix.mem_specialIsometryGroup_iff`: the defining matrix equation.
* `Matrix.mem_isotropicPoints_iff`: a point is isotropic when its chosen representative is.
* `Matrix.mk_mem_isotropicPoints_iff`: the point of a nonzero vector is isotropic exactly when the
  vector is.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 7 and 10.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing K]

variable (Q : Matrix n n K) (σ : K →+* K)

/-- **The special isometry group of a sesquilinear Gram matrix**: the matrices `g` of determinant
one with `(g ^ σ)ᵀ * Q * g = Q`, that is, the special linear transformations preserving the
`σ`-sesquilinear form `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)`. For an involution `σ` and a Hermitian or
skew-Hermitian `Q` it is the special unitary group of `Q`. -/
def specialIsometryGroup : Subgroup (SpecialLinearGroup n K) where
  carrier := {g | ((g : Matrix n n K).map σ)ᵀ * Q * g = Q}
  one_mem' := by
    simp [Matrix.map_one σ σ.map_zero σ.map_one]
  mul_mem' {g g'} hg hg' := by
    simp only [Set.mem_ofPred_eq, SpecialLinearGroup.coe_mul] at hg hg' ⊢
    rw [transpose_map_mul_mul_mul, hg, hg']
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := transpose_map_mul_mul_mul σ Q (g : Matrix n n K)
      ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K)
    rw [hg, ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one,
      Matrix.map_one σ σ.map_zero σ.map_one, transpose_one, Matrix.one_mul, Matrix.mul_one] at h
    exact h.symm

variable {Q σ}

/-- An element of the special linear group is an isometry exactly when `(g ^ σ)ᵀ * Q * g = Q`. -/
@[simp]
theorem mem_specialIsometryGroup_iff {g : SpecialLinearGroup n K} :
    g ∈ Q.specialIsometryGroup σ ↔ ((g : Matrix n n K).map σ)ᵀ * Q * g = Q :=
  Iff.rfl

end CommRing

section Field

variable [Field K] {Q : Matrix n n K} {σ : K →+* K}

omit [DecidableEq n] in
/-- Isotropy of a projective point does not depend on the representative. -/
private theorem comp_rep_mk_dotProduct_mulVec_rep_mk_eq_zero_iff {v : n → K} (hv : v ≠ 0) :
    (σ ∘ (Projectivization.mk K v hv).rep) ⬝ᵥ (Q *ᵥ (Projectivization.mk K v hv).rep) = 0 ↔
      (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [← ha, Units.smul_def, comp_smul_dotProduct_mulVec_smul]
  have hσa : σ (a : K) ≠ 0 := (map_ne_zero σ).mpr a.ne_zero
  simp [hσa, a.ne_zero]

variable (Q σ) in
/-- **The isotropic points of projective space**: the points `[v]` with `h(v, v) = 0`, as a
sub-`MulAction` of the special isometry group. Whether `[v]` is isotropic does not depend on the
representative `v` (`Matrix.mk_mem_isotropicPoints_iff`). -/
def isotropicPoints : SubMulAction (Q.specialIsometryGroup σ) (ℙ K (n → K)) where
  carrier := {p | (σ ∘ p.rep) ⬝ᵥ (Q *ᵥ p.rep) = 0}
  smul_mem' g p hp := by
    induction p using Projectivization.ind with | h v hv => ?_
    simp only [Set.mem_ofPred_eq, comp_rep_mk_dotProduct_mulVec_rep_mk_eq_zero_iff] at hp ⊢
    rw [Subgroup.smul_def, Projectivization.smul_mk,
      comp_rep_mk_dotProduct_mulVec_rep_mk_eq_zero_iff, SpecialLinearGroup.smul_def, smul_eq_mulVec,
      comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), hp]

/-- A point lies in `isotropicPoints` exactly when its chosen representative is isotropic. -/
theorem mem_isotropicPoints_iff {p : ℙ K (n → K)} :
    p ∈ Q.isotropicPoints σ ↔ (σ ∘ p.rep) ⬝ᵥ (Q *ᵥ p.rep) = 0 :=
  Iff.rfl

/-- **Isotropy of a point is isotropy of any representative**: `[v]` is isotropic exactly when
`h(v, v) = 0`. -/
@[simp]
theorem mk_mem_isotropicPoints_iff {v : n → K} (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ Q.isotropicPoints σ ↔ (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 := by
  rw [mem_isotropicPoints_iff, comp_rep_mk_dotProduct_mulVec_rep_mk_eq_zero_iff]

/-- The representative of an isotropic point is an isotropic vector. -/
theorem comp_rep_dotProduct_mulVec_rep (p : Q.isotropicPoints σ) :
    (σ ∘ (p : ℙ K (n → K)).rep) ⬝ᵥ (Q *ᵥ (p : ℙ K (n → K)).rep) = 0 :=
  mem_isotropicPoints_iff.mp p.2

end Field

end Matrix
