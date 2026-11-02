/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Unitary transvections

Let `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` be the `σ`-sesquilinear form of a Gram matrix `Q`
(`Matrix.specialIsometryGroup`). For a vector `v` and a scalar `a` the *unitary transvection*

```text
τ_{v,a} : x ↦ x + a h(v, x) v,         matrix  1 + a v (vᵀ ^ σ Q),
```

is `Matrix.unitaryTransvection Q σ v a`. When `v` is isotropic, `h(v, v) = 0`, it has determinant
one and `τ_{v,a} τ_{v,b} = τ_{v,a+b}`. If moreover `σ` is an involution and `Q` is
`ε`-Hermitian, `(Q ^ σ)ᵀ = ε • Q`, then

```text
(τ_{v,a} ^ σ)ᵀ Q τ_{v,a} = Q + (a + ε σ(a)) (Q v) (vᵀ ^ σ Q),
```

so `τ_{v,a}` is an isometry when `a + ε σ(a) = 0`, and, over a field, for a nondegenerate `Q` and
`v ≠ 0`, only then. For a Hermitian form (`ε = 1`) the admissible parameters are the elements of
trace zero. An isometry `g` conjugates `τ_{v,a}` to `τ_{g v,a}`, and rescaling `v` by `c` rescales
the parameter by `c σ(c)`.

To an isotropic point `p` of projective space this attaches the group
`Matrix.unitaryTransvectionSubgroup Q σ p` of isometries that are unitary transvections along a
representative of `p`. It does not depend on the representative, it is abelian, and conjugation
by an isometry `g` carries it to the group of `g • p`. These are the commutativity and conjugacy
axioms of an Iwasawa structure (`MulAction.IwasawaStructure`) for the action of a special unitary
group on its isotropic points, the action from which the simplicity of the projective special
unitary groups is deduced.

For `σ = id` and the standard alternating Gram matrix `TauCeti.JFin`, `τ_{v,a}` is the symplectic
transvection `TauCeti.GLSymplecticFin.symplecticTransvection`
(`TauCeti.GLSymplecticFin.coe_symplecticTransvection_eq_unitaryTransvection`). That construction in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transvection`, together with the Iwasawa
structure of `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Iwasawa`, served as the
model for this file; the basic laws of symplectic transvections are derived from the general ones
proved here.

## Main definitions

* `Matrix.unitaryTransvection Q σ v a`: the matrix `1 + a v (vᵀ ^ σ Q)` of `τ_{v,a}`.
* `Matrix.unitaryTransvectionSubgroup Q σ p`: the unitary transvections along an isotropic point.

## Main results

* `Matrix.unitaryTransvection_mulVec`: `τ_{v,a} x = x + a h(v, x) v`, and
  `Matrix.toLin'_unitaryTransvection`: as a linear map it is Mathlib's `LinearMap.transvection`.
* `Matrix.det_unitaryTransvection`, `Matrix.unitaryTransvection_mul_unitaryTransvection`: an
  isotropic vector gives transvections of determinant one, additive in the parameter.
* `Matrix.transpose_map_unitaryTransvection_mul_mul`: the defect of `τ_{v,a}` from being an
  isometry of an `ε`-Hermitian form.
* `Matrix.exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection`: for `a + ε σ(a) = 0` the
  transvection `τ_{v,a}` along an isotropic vector is a special isometry.
* `Matrix.exists_coe_eq_unitaryTransvection_iff`: for a nondegenerate `ε`-Hermitian `Q`, the
  transvection `τ_{v,a}` along an isotropic point is an isometry exactly when `a + ε σ(a) = 0`.
* `Matrix.mul_unitaryTransvection_mul_of_mul_eq_one`,
  `Matrix.coe_mul_unitaryTransvection_mul_coe_inv`: a form-preserving `g` conjugates `τ_{v,a}` to
  `τ_{g v,a}`.
* `Matrix.unitaryTransvectionSubgroup_smul`: `T(g • p) = g T(p) g⁻¹`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing K] (Q : Matrix n n K) (σ : K →+* K)

/-- **The unitary transvection** `τ_{v,a} : x ↦ x + a h(v, x) v` along `v`, for the sesquilinear
form `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)`. Its matrix is `1 + a v (vᵀ ^ σ Q)`. It has determinant one
when `v` is isotropic (`Matrix.det_unitaryTransvection`). For an involution `σ` and an
`ε`-Hermitian `Q` it is then an isometry when `a + ε σ(a) = 0`
(`Matrix.exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection`), and, if moreover `K` is a
field, `Q` is nondegenerate and `v ≠ 0`, only then (`Matrix.exists_coe_eq_unitaryTransvection_iff`).
-/
def unitaryTransvection (v : n → K) (a : K) : Matrix n n K :=
  1 + a • vecMulVec v ((σ ∘ v) ᵥ* Q)

variable {Q σ}

/-- The matrix of the unitary transvection `τ_{v,a}` is `1 + a v (vᵀ ^ σ Q)`. -/
theorem unitaryTransvection_def (v : n → K) (a : K) :
    Q.unitaryTransvection σ v a = 1 + a • vecMulVec v ((σ ∘ v) ᵥ* Q) :=
  (rfl)

/-- The unitary transvection `τ_{v,a}` sends `x` to `x + a h(v, x) v`. -/
theorem unitaryTransvection_mulVec (v : n → K) (a : K) (x : n → K) :
    Q.unitaryTransvection σ v a *ᵥ x = x + (a * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  rw [unitaryTransvection, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, ← dotProduct_mulVec, smul_smul]

/-- As a linear map, the unitary transvection `τ_{v,a}` is Mathlib's transvection
`x ↦ x + f x • v` for the linear form `f = a h(v, ·)`. -/
theorem toLin'_unitaryTransvection (v : n → K) (a : K) :
    toLin' (Q.unitaryTransvection σ v a) =
      LinearMap.transvection (dotProductEquiv K n (a • ((σ ∘ v) ᵥ* Q))) v := by
  refine LinearMap.ext fun x ↦ ?_
  rw [toLin'_apply, unitaryTransvection_mulVec, LinearMap.transvection.apply,
    dotProductEquiv_apply_apply, smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul]

/-- The unitary transvection with parameter `0` is the identity. -/
@[simp]
theorem unitaryTransvection_zero_right (v : n → K) : Q.unitaryTransvection σ v 0 = 1 := by
  simp [unitaryTransvection]

/-- The unitary transvection along the zero vector is the identity. -/
@[simp]
theorem unitaryTransvection_zero_left (a : K) : Q.unitaryTransvection σ 0 a = 1 := by
  simp [unitaryTransvection]

/-- Rescaling the vector by `c` rescales the parameter by `c σ(c)`: `τ_{c v,a} = τ_{v,a c σ(c)}`. -/
theorem unitaryTransvection_smul (c : K) (v : n → K) (a : K) :
    Q.unitaryTransvection σ (c • v) a = Q.unitaryTransvection σ v (a * c * σ c) := by
  rw [unitaryTransvection, unitaryTransvection, RingHom.comp_smul, smul_vecMul, vecMulVec_smul,
    smul_vecMulVec, smul_smul, smul_smul, mul_right_comm a (σ c) c]

omit [DecidableEq n] in
/-- The rank-one part `v (vᵀ ^ σ Q)` of a transvection along an isotropic vector squares to zero. -/
private theorem vecMulVec_mul_vecMulVec_eq_zero {v : n → K}
    (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (x : n → K) :
    vecMulVec x ((σ ∘ v) ᵥ* Q) * vecMulVec v ((σ ∘ v) ᵥ* Q) = 0 := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, hv, zero_smul, vecMulVec_zero]

/-- **Unitary transvections along an isotropic vector are additive in the parameter**:
`τ_{v,a} τ_{v,b} = τ_{v,a+b}`. -/
theorem unitaryTransvection_mul_unitaryTransvection {v : n → K}
    (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a b : K) :
    Q.unitaryTransvection σ v a * Q.unitaryTransvection σ v b =
      Q.unitaryTransvection σ v (a + b) := by
  simp only [unitaryTransvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec_eq_zero hv, smul_zero, add_zero, add_smul]
  abel

/-- **A transvection along an isotropic vector has determinant one.** -/
@[simp]
theorem det_unitaryTransvection {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a : K) :
    (Q.unitaryTransvection σ v a).det = 1 := by
  rw [unitaryTransvection, ← smul_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← dotProduct_mulVec, hv,
    smul_zero, add_zero]

/-- **A form-preserving matrix conjugates `τ_{v,a}` to `τ_{M v,a}`**: if `(M ^ σ)ᵀ Q M = Q` and
`M M' = 1`, then `M τ_{v,a} M' = τ_{M v,a}`. -/
theorem mul_unitaryTransvection_mul_of_mul_eq_one {M M' : Matrix n n K} (hMM' : M * M' = 1)
    (hM : (M.map σ)ᵀ * Q * M = Q) (v : n → K) (a : K) :
    M * Q.unitaryTransvection σ v a * M' = Q.unitaryTransvection σ (M *ᵥ v) a := by
  -- The isometry equation `(M ^ σ)ᵀ Q M = Q` gives `(M ^ σ)ᵀ Q = Q M'`.
  have hQM : (M.map σ)ᵀ * Q = Q * M' := by
    calc (M.map σ)ᵀ * Q = (M.map σ)ᵀ * Q * (M * M') := by rw [hMM', Matrix.mul_one]
      _ = (M.map σ)ᵀ * Q * M * M' := by simp only [Matrix.mul_assoc]
      _ = Q * M' := by rw [hM]
  have hrow : (σ ∘ (M *ᵥ v)) ᵥ* Q = ((σ ∘ v) ᵥ* Q) ᵥ* M' := by
    rw [comp_mulVec_eq_vecMul_transpose_map, vecMul_vecMul, hQM, vecMul_vecMul]
  rw [unitaryTransvection, unitaryTransvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    hMM', Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, hrow]

/-- **An isometry conjugates `τ_{v,a}` to `τ_{g v,a}`.** -/
theorem coe_mul_unitaryTransvection_mul_coe_inv {g : SpecialLinearGroup n K}
    (hg : g ∈ Q.specialIsometryGroup σ) (v : n → K) (a : K) :
    (g : Matrix n n K) * Q.unitaryTransvection σ v a * ((g⁻¹ : SpecialLinearGroup n K) :
      Matrix n n K) = Q.unitaryTransvection σ ((g : Matrix n n K) *ᵥ v) a :=
  mul_unitaryTransvection_mul_of_mul_eq_one
    (by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one])
    ((mem_specialIsometryGroup_iff).mp hg) v a

/-- **The isometry defect of a unitary transvection.** If `σ` is an involution, `Q` is
`ε`-Hermitian and `v` is isotropic, then
`(τ_{v,a} ^ σ)ᵀ Q τ_{v,a} = Q + (a + ε σ(a)) (Q v) (vᵀ ^ σ Q)`. In particular `τ_{v,a}` preserves
the form when `a + ε σ(a) = 0`. -/
theorem transpose_map_unitaryTransvection_mul_mul (hσ : Function.Involutive σ) {ε : K}
    (hQ : (Q.map σ)ᵀ = ε • Q) {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (a : K) :
    ((Q.unitaryTransvection σ v a).map σ)ᵀ * Q * Q.unitaryTransvection σ v a =
      Q + (a + ε * σ a) • vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) := by
  -- Applying `σ` to the row `vᵀ ^ σ Q` gives `vᵀ (Q ^ σ) = ε (Q v)ᵀ`, as `σ` is an involution.
  have hw : σ ∘ ((σ ∘ v) ᵥ* Q) = ε • (Q *ᵥ v) := by
    ext i
    have hσv : σ ∘ (σ ∘ v) = v := funext fun j ↦ hσ (v j)
    rw [Function.comp_apply, RingHom.map_vecMul, hσv, ← mulVec_transpose, hQ, smul_mulVec]
  have hT : ((Q.unitaryTransvection σ v a).map σ)ᵀ =
      1 + (σ a * ε) • vecMulVec (Q *ᵥ v) (σ ∘ v) := by
    have hmap : (Q.unitaryTransvection σ v a).map σ =
        1 + σ a • vecMulVec (σ ∘ v) (σ ∘ ((σ ∘ v) ᵥ* Q)) := by
      ext i j
      simp [unitaryTransvection, Matrix.one_apply, vecMulVec_apply, apply_ite σ]
    rw [hmap, hw, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec,
      smul_vecMulVec, smul_smul]
  have h₁ : vecMulVec (Q *ᵥ v) (σ ∘ v) * Q = vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) :=
    vecMulVec_mul _ _ _
  have h₂ : Q * vecMulVec v ((σ ∘ v) ᵥ* Q) = vecMulVec (Q *ᵥ v) ((σ ∘ v) ᵥ* Q) :=
    mul_vecMulVec _ _ _
  rw [hT, unitaryTransvection]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h₁, h₂, vecMulVec_mul_vecMulVec_eq_zero hv, smul_zero, add_zero]
  module

/-- **Admissible unitary transvections are isometries.** If `σ` is an involution, `Q` is
`ε`-Hermitian, `v` is isotropic and `a + ε σ(a) = 0`, then `τ_{v,a}` is the matrix of an element of
the special isometry group of `Q`. -/
theorem exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection (hσ : Function.Involutive σ)
    {ε : K} (hQ : (Q.map σ)ᵀ = ε • Q) {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : K}
    (ha : a + ε * σ a = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, (g : Matrix n n K) = Q.unitaryTransvection σ v a := by
  let t : SpecialLinearGroup n K := ⟨_, det_unitaryTransvection hv a⟩
  refine ⟨t, ?_, rfl⟩
  rw [mem_specialIsometryGroup_iff, SpecialLinearGroup.coe_mk,
    transpose_map_unitaryTransvection_mul_mul hσ hQ hv, ha, zero_smul, add_zero]

end CommRing

section Field

variable [Field K] {Q : Matrix n n K} {σ : K →+* K}

/-- Along a nonzero multiple `c v` of `v`, the unitary transvections are those along `v`. -/
theorem exists_eq_unitaryTransvection_smul_iff {c : K} (hc : c ≠ 0) (v : n → K)
    (M : Matrix n n K) :
    (∃ a, M = Q.unitaryTransvection σ (c • v) a) ↔ ∃ a, M = Q.unitaryTransvection σ v a := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  simp_rw [unitaryTransvection_smul]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨_, ha⟩, fun ⟨a, ha⟩ ↦ ⟨a / (c * σ c), ?_⟩⟩
  rw [ha]
  congr 1
  field_simp

variable (Q σ) in
/-- **The unitary transvection group of an isotropic point** `p`: the isometries that are unitary
transvections `τ_{v,a}` along a representative `v` of `p`. It does not depend on the
representative (`Matrix.mem_unitaryTransvectionSubgroup_mk_iff`), and is abelian. -/
def unitaryTransvectionSubgroup (p : Q.isotropicPoints σ) :
    Subgroup (Q.specialIsometryGroup σ) where
  carrier := {g | ∃ a : K, ((g : SpecialLinearGroup n K) : Matrix n n K) =
    Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a}
  one_mem' := ⟨0, by simp⟩
  mul_mem' {g g'} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ha, hb,
      unitaryTransvection_mul_unitaryTransvection (comp_rep_dotProduct_mulVec_rep p)]
  inv_mem' {g} := by
    rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have h₁ : ((g : SpecialLinearGroup n K) : Matrix n n K) *
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep (-a) = 1 := by
      rw [ha, unitaryTransvection_mul_unitaryTransvection (comp_rep_dotProduct_mulVec_rep p),
        add_neg_cancel, unitaryTransvection_zero_right]
    have h₂ : ((g : SpecialLinearGroup n K) : Matrix n n K) *
        ((g⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        SpecialLinearGroup.coe_one]
    rw [← inv_eq_right_inv h₂, inv_eq_right_inv h₁]

/-- An isometry lies in the transvection group of `p` exactly when it is a unitary transvection
along the chosen representative of `p`. -/
theorem mem_unitaryTransvectionSubgroup_iff {p : Q.isotropicPoints σ}
    {g : Q.specialIsometryGroup σ} :
    g ∈ Q.unitaryTransvectionSubgroup σ p ↔
      ∃ a, ((g : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a :=
  Iff.rfl

/-- **The transvection group does not depend on the representative**: an isometry lies in the
transvection group of the point `[v]` exactly when it is a unitary transvection along `v`. -/
@[simp]
theorem mem_unitaryTransvectionSubgroup_mk_iff {v : n → K} (hv : v ≠ 0)
    (hp : Projectivization.mk K v hv ∈ Q.isotropicPoints σ) {g : Q.specialIsometryGroup σ} :
    g ∈ Q.unitaryTransvectionSubgroup σ ⟨_, hp⟩ ↔
      ∃ a, ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [mem_unitaryTransvectionSubgroup_iff]
  dsimp only
  rw [← hc, Units.smul_def, exists_eq_unitaryTransvection_smul_iff c.ne_zero]

/-- **The transvection group of an isotropic point is abelian.** -/
instance (p : Q.isotropicPoints σ) : IsMulCommutative (Q.unitaryTransvectionSubgroup σ p) :=
  ⟨⟨fun x y ↦ by
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    have hv := comp_rep_dotProduct_mulVec_rep p
    have h : ((((x * y : Q.unitaryTransvectionSubgroup σ p) : Q.specialIsometryGroup σ) :
        SpecialLinearGroup n K) : Matrix n n K) =
        ((((y * x : Q.unitaryTransvectionSubgroup σ p) : Q.specialIsometryGroup σ) :
          SpecialLinearGroup n K) : Matrix n n K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ha, hb,
        unitaryTransvection_mul_unitaryTransvection hv,
        unitaryTransvection_mul_unitaryTransvection hv, add_comm]
    exact Subtype.ext (Subtype.ext (Subtype.ext h))⟩⟩

/-- **Conjugation moves transvection groups along the action**: `T(g • p) = g T(p) g⁻¹`. -/
theorem unitaryTransvectionSubgroup_smul (g : Q.specialIsometryGroup σ)
    (p : Q.isotropicPoints σ) :
    Q.unitaryTransvectionSubgroup σ (g • p) =
      MulAut.conj g • Q.unitaryTransvectionSubgroup σ p := by
  -- Both groups consist of the unitary transvections along `g v`, for a representative `v`.
  set v := (p : ℙ K (n → K)).rep
  have hgv : (g : SpecialLinearGroup n K) • v ≠ 0 :=
    (smul_ne_zero_iff_ne (g : SpecialLinearGroup n K)).mpr (p : ℙ K (n → K)).rep_nonzero
  have hgp : ((g • p : Q.isotropicPoints σ) : ℙ K (n → K)) =
      Projectivization.mk K ((g : SpecialLinearGroup n K) • v) hgv := by
    rw [SubMulAction.val_smul, Subgroup.smul_def,
      ← Projectivization.smul_mk _ (p : ℙ K (n → K)).rep_nonzero, Projectivization.mk_rep]
  have hconj : ∀ h : Q.specialIsometryGroup σ, ∀ (u : n → K) (a : K),
      ((h : SpecialLinearGroup n K) : Matrix n n K) * Q.unitaryTransvection σ u a *
        ((h⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) =
        Q.unitaryTransvection σ (((h : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u) a :=
    fun h u a ↦ by
      rw [Subgroup.coe_inv]
      exact coe_mul_unitaryTransvection_mul_coe_inv h.2 u a
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  have hmem : x ∈ Q.unitaryTransvectionSubgroup σ (g • p) ↔
      ∃ a, ((x : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v) a := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K _ hgv
    rw [mem_unitaryTransvectionSubgroup_iff, hgp, ← hc, Units.smul_def,
      exists_eq_unitaryTransvection_smul_iff c.ne_zero, SpecialLinearGroup.smul_def,
      smul_eq_mulVec]
  rw [hmem]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨g⁻¹ * x * g, ⟨a, ?_⟩, by simp [MulAut.smul_def, mul_assoc]⟩
    have h := hconj g⁻¹ (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v) a
    rw [inv_inv, ← ha] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul, h, mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
      ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, SpecialLinearGroup.coe_one,
      one_mulVec]
  · rintro ⟨y, ⟨a, ha⟩, rfl⟩
    refine ⟨a, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ha, hconj]

variable {ε : K}

/-- **Every admissible parameter gives an isometry.** If `σ` is an involution and `Q` is
`ε`-Hermitian, then for every `a` with `a + ε σ(a) = 0` the transvection `τ_{v,a}` along the
representative `v` of an isotropic point lies in its transvection group. -/
theorem exists_coe_eq_unitaryTransvection (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (p : Q.isotropicPoints σ) {a : K} (ha : a + ε * σ a = 0) :
    ∃ g : Q.unitaryTransvectionSubgroup σ p,
      (((g : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a := by
  obtain ⟨g, hg, hga⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ
    (comp_rep_dotProduct_mulVec_rep p) ha
  exact ⟨⟨⟨g, hg⟩, a, hga⟩, hga⟩

/-- **The parameters of the transvection group of an isotropic point.** If `σ` is an involution
and `Q` is a nondegenerate `ε`-Hermitian matrix, the transvection `τ_{v,a}` along the
representative `v` of an isotropic point is an isometry exactly when `a + ε σ(a) = 0`. For a
Hermitian form these are the elements of trace zero. -/
theorem exists_coe_eq_unitaryTransvection_iff (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (p : Q.isotropicPoints σ) (a : K) :
    (∃ g : Q.unitaryTransvectionSubgroup σ p,
      (((g : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a) ↔ a + ε * σ a = 0 := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, exists_coe_eq_unitaryTransvection hσ hQ p⟩
  set v := (p : ℙ K (n → K)).rep
  have hv := comp_rep_dotProduct_mulVec_rep p
  have h := (mem_specialIsometryGroup_iff).mp (g : Q.specialIsometryGroup σ).2
  rw [hg, transpose_map_unitaryTransvection_mul_mul hσ hQ hv, add_eq_left, smul_eq_zero,
    vecMulVec_eq_zero] at h
  -- The column `Q v` and the row `vᵀ ^ σ Q` are nonzero, as `Q` is invertible and `v ≠ 0`.
  have hQv : Q *ᵥ v ≠ 0 := fun h0 ↦
    hdet (exists_mulVec_eq_zero_iff.mp ⟨v, (p : ℙ K (n → K)).rep_nonzero, h0⟩)
  have hσv : σ ∘ v ≠ 0 := fun h0 ↦ (p : ℙ K (n → K)).rep_nonzero <| funext fun i ↦
    (map_eq_zero σ).mp (congrFun h0 i)
  have hvQ : (σ ∘ v) ᵥ* Q ≠ 0 := fun h0 ↦
    hdet (exists_vecMul_eq_zero_iff.mp ⟨σ ∘ v, hσv, h0⟩)
  exact h.resolve_right (not_or.mpr ⟨hQv, hvQ⟩)

end Field

end Matrix
