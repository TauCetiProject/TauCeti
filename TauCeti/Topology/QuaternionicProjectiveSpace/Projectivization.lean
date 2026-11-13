/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Projectivization
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import TauCeti.Topology.QuaternionicProjectiveSpace.Charts
public import TauCeti.Topology.QuaternionicProjectiveSpace.Homogeneous

/-!
# Quaternionic projective space as the projectivization of right lines

The quaternionic coordinate space `ℍⁿ⁺¹ = Fin (n + 1) → ℍ` is a right `ℍ`-module, that is, a
left module over the opposite ring `ℍᵐᵒᵖ`, with `op q • v = v q`. Its projectivization
`ℙ ℍᵐᵒᵖ (Fin (n + 1) → ℍ)`, with Mathlib's quotient topology, is the space of right quaternionic
lines `{v q | q ∈ ℍ}`: nonzero vectors `v` and `v q` define the same point. This file compares it
with Tau Ceti's sphere-quotient model `TauCeti.QuaternionicProjectiveSpace n`, the unit sphere
`S⁴ⁿ⁺³ ⊆ ℍⁿ⁺¹` modulo unit quaternions acting on the right.

Every right line meets the unit sphere in exactly one orbit of the unit quaternions, so the class
of a unit vector `x` corresponds to its line `[x]`, and the line of a nonzero vector `v` to the
class of `v / ‖v‖` (`TauCeti.QuaternionicProjectiveSpace.projectivizationHomeomorph`). Under this
homeomorphism:

* the homogeneous-ratio charts are the right ratios of an arbitrary representative: the chart on
  `v_k ≠ 0` sends the line of `v` to `(v_j v_k⁻¹)_(j ≠ k)`, a formula unchanged under
  `v ↦ v q` since `(v_j q) (v_k q)⁻¹ = v_j v_k⁻¹`, and its inverse sends `z` to the line of the
  representative with `k`-th coordinate `1` and remaining coordinates `z`
  (`TauCeti.QuaternionicProjectiveSpace.projectivizationAffineChart`);
* a quaternionic unitary matrix `A ∈ Sp(n + 1)` acts on lines by `[v] ↦ [A v]`, so the
  homogeneous-space description `Sp(n + 1) / (Sp(1) × Sp(n)) ≃ₜ HPⁿ` sends the coset of `A` to
  the line `[A e₀]` of the first column of `A`.

## Main declarations

* `TauCeti.QuaternionicProjectiveSpace.projectivizationHomeomorph`: the homeomorphism
  `HPⁿ ≃ₜ ℙ ℍᵐᵒᵖ (Fin (n + 1) → ℍ)`.
* `TauCeti.QuaternionicProjectiveSpace.ratio_projectivizationHomeomorph_symm_mk`: the homogeneous
  ratios are the right ratios `v_j v_k⁻¹` of any nonzero representative.
* `TauCeti.QuaternionicProjectiveSpace.projectivizationAffineChart`: the homogeneous-ratio chart on
  the projectivization, with `projectivizationAffineChart_mk` and
  `projectivizationAffineChart_symm_apply`.
* `TauCeti.QuaternionicProjectiveSpace.projectivizationHomeomorph_smul_symm_mk`: the action of
  `Sp(n + 1)` on lines.
* `TauCeti.QuaternionicProjectiveSpace.projectivizationHomeomorph_unitaryQuotientHomeomorph_mk`:
  the coset of `A ∈ Sp(n + 1)` corresponds to the line `[A e₀]`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Example 0.6.
-/

public section

noncomputable section

open Metric Set MulOpposite
open scoped LinearAlgebra.Projectivization Matrix Quaternion RightActions

namespace TauCeti

namespace QuaternionicProjectiveSpace

variable {n : ℕ}

/-- The unit vector `v / ‖v‖` of a nonzero quaternionic coordinate vector. -/
private def normalizeSphere :
    C({v : Fin (n + 1) → ℍ // v ≠ 0}, sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :=
  normalizeToSphere (fun v : {v : Fin (n + 1) → ℍ // v ≠ 0} ↦ WithLp.toLp 2 v.1)
    ((PiLp.continuous_toLp 2 _).comp continuous_subtype_val)
    fun v ↦ (WithLp.toLp_eq_zero 2).not.2 v.2

private theorem coe_normalizeSphere (v : {v : Fin (n + 1) → ℍ // v ≠ 0}) :
    ((normalizeSphere v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)) =
      ‖(WithLp.toLp 2 v.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖⁻¹ • WithLp.toLp 2 v.1 := by
  simp [normalizeSphere, NormedSpace.normalize]

/-- Nonzero vectors spanning the same right line have normalizations in the same orbit of the
unit quaternions. -/
private theorem mk_normalizeSphere_eq (v w : {v : Fin (n + 1) → ℍ // v ≠ 0}) (q : ℍ)
    (hvw : v.1 = op q • w.1) : mk n (normalizeSphere v) = mk n (normalizeSphere w) := by
  set a := ‖(WithLp.toLp 2 v.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖
  set b := ‖(WithLp.toLp 2 w.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖
  have ha : a ≠ 0 := norm_ne_zero_iff.2 ((WithLp.toLp_eq_zero 2).not.2 v.2)
  have hb : b ≠ 0 := norm_ne_zero_iff.2 ((WithLp.toLp_eq_zero 2).not.2 w.2)
  -- `v / ‖v‖ = (w / ‖w‖) c` with `c = (‖w‖ / ‖v‖) q`, which is then a unit quaternion.
  set c : ℍ := (b / a) • q
  have hsmul : ((normalizeSphere w : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)) <• c =
      (normalizeSphere v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) := by
    refine PiLp.ext fun i ↦ ?_
    have hvi : v.1 i = w.1 i * q := by rw [hvw, Pi.smul_apply, op_smul_eq_mul]
    simp only [coe_normalizeSphere, PiLp.smul_apply, op_smul_eq_mul, c, smul_mul_assoc,
      mul_smul_comm, smul_smul, hvi]
    congr 1
    simp only [a, b] at ha hb ⊢
    field_simp
  have hc : ‖c‖ = 1 := by
    have h := congrArg norm hsmul
    simpa only [norm_smul, norm_op, mem_sphere_zero_iff_norm.1 (normalizeSphere v).2,
      mem_sphere_zero_iff_norm.1 (normalizeSphere w).2, mul_one] using h
  exact (mk_eq_mk_iff n _ _).2 ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, Subtype.ext hsmul⟩

variable (n) in
/-- **Quaternionic projective space is the projectivization of right lines**: the class of a
unit vector `x ∈ S⁴ⁿ⁺³` corresponds to the right line `[x]` in `ℍⁿ⁺¹`, and the line of a nonzero
vector `v` to the class of `v / ‖v‖`. -/
def projectivizationHomeomorph : QuaternionicProjectiveSpace n ≃ₜ ℙ ℍᵐᵒᵖ (Fin (n + 1) → ℍ) where
  toFun := QuaternionicProjectiveSpace.lift n
    (fun x ↦ Projectivization.mk ℍᵐᵒᵖ (WithLp.ofLp (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ))
      ((WithLp.ofLp_eq_zero 2).not.2 (ne_zero_of_mem_unit_sphere x))) fun q x ↦
      (Projectivization.mk_eq_mk_iff' _ _ _ _ _).2 ⟨op (q : ℍ), funext fun i ↦ by simp⟩
  invFun := Projectivization.lift (fun v ↦ mk n (normalizeSphere v)) fun v w q hvw ↦
    mk_normalizeSphere_eq v w (unop q) hvw
  left_inv p := by
    induction p using QuaternionicProjectiveSpace.inductionOn with
    | h x =>
      simp only [QuaternionicProjectiveSpace.lift_mk, Projectivization.lift_mk]
      congr 1
      refine Subtype.ext ?_
      rw [coe_normalizeSphere]
      simp [mem_sphere_zero_iff_norm.1 x.2]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [Projectivization.lift_mk, QuaternionicProjectiveSpace.lift_mk]
      refine (Projectivization.mk_eq_mk_iff' _ _ _ _ _).2
        ⟨op ((‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖⁻¹ : ℝ) : ℍ), ?_⟩
      funext i
      simp only [coe_normalizeSphere, Pi.smul_apply, op_smul_eq_mul, PiLp.smul_apply]
      exact Quaternion.mul_coe_eq_smul _ _
  continuous_toFun := by
    refine (isOpenQuotientMap_mk n).isQuotientMap.continuous_iff.2 ?_
    simp only [Function.comp_def, QuaternionicProjectiveSpace.lift_mk]
    exact Projectivization.continuous_mk
      ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val) _
  continuous_invFun :=
    Projectivization.continuous_iff.2 ((continuous_mk n).comp normalizeSphere.continuous)

/-- The class of a unit vector `x` is the right line `[x]`. -/
@[simp]
theorem projectivizationHomeomorph_mk (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    projectivizationHomeomorph n (mk n x) =
      Projectivization.mk ℍᵐᵒᵖ (WithLp.ofLp (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ))
        ((WithLp.ofLp_eq_zero 2).not.2 (ne_zero_of_mem_unit_sphere x)) :=
  QuaternionicProjectiveSpace.lift_mk n _ _ x

/-- The right line of a nonzero vector `v` is the class of the unit vector `v / ‖v‖`. -/
theorem projectivizationHomeomorph_symm_mk (v : Fin (n + 1) → ℍ) (hv : v ≠ 0) :
    (projectivizationHomeomorph n).symm (Projectivization.mk ℍᵐᵒᵖ v hv) =
      mk n ⟨NormedSpace.normalize (WithLp.toLp 2 v), mem_sphere_zero_iff_norm.2
        (NormedSpace.norm_normalize ((WithLp.toLp_eq_zero 2).not.2 hv))⟩ :=
  congrArg (mk n) (Subtype.ext (coe_normalizeSphere ⟨v, hv⟩))

/-- **The homogeneous ratios are right ratios of representatives**: on the right line of a nonzero
vector `v`, the homogeneous ratio `X_j X_k⁻¹` is `v_j v_k⁻¹`. The formula does not depend on the
representative, since `(v_j q) (v_k q)⁻¹ = v_j v_k⁻¹` for every nonzero quaternion `q`. -/
@[simp]
theorem ratio_projectivizationHomeomorph_symm_mk (k j : Fin (n + 1)) (v : Fin (n + 1) → ℍ)
    (hv : v ≠ 0) :
    ratio k j ((projectivizationHomeomorph n).symm (Projectivization.mk ℍᵐᵒᵖ v hv)) =
      v j * (v k)⁻¹ := by
  have hn : ‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((WithLp.toLp_eq_zero 2).not.2 hv)
  simp only [projectivizationHomeomorph_symm_mk, ratio_mk, NormedSpace.normalize,
    PiLp.smul_apply, smul_inv₀, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_inv, mul_inv_cancel₀ hn, one_smul]

/-- **The affine parametrization has the representative with `k`-th coordinate one**: the point
with chart coordinates `z` in the chart of `X_k ≠ 0` is the right line of the vector whose `k`-th
coordinate is `1` and whose remaining coordinates are `z`. -/
@[simp]
theorem projectivizationHomeomorph_affineParam (k : Fin (n + 1)) (z : Fin n → ℍ) :
    projectivizationHomeomorph n (affineParam k z) =
      Projectivization.mk ℍᵐᵒᵖ (Fin.insertNth (α := fun _ ↦ ℍ) k 1 z)
        (Function.ne_iff.2 ⟨k, by simp⟩) := by
  rw [eq_comm, ← Homeomorph.symm_apply_eq]
  exact ((affineChart k).injOn (by simp) (by simp) (funext fun j ↦ by simp)).symm

/-- **The homogeneous-ratio chart on the projectivization of right lines**: on the right lines
`[v]` with `v_k ≠ 0` it is `[v] ↦ (v_j v_k⁻¹)_(j ≠ k)`
(`TauCeti.QuaternionicProjectiveSpace.projectivizationAffineChart_mk`), and its inverse sends `z` to
the line of the vector with `k`-th coordinate `1` and remaining coordinates `z`
(`TauCeti.QuaternionicProjectiveSpace.projectivizationAffineChart_symm_apply`). It is the chart
`TauCeti.QuaternionicProjectiveSpace.affineChart k` of the sphere-quotient model, transported along
`TauCeti.QuaternionicProjectiveSpace.projectivizationHomeomorph`. -/
def projectivizationAffineChart (k : Fin (n + 1)) :
    OpenPartialHomeomorph (ℙ ℍᵐᵒᵖ (Fin (n + 1) → ℍ)) (Fin n → ℍ) :=
  (projectivizationHomeomorph n).symm.transOpenPartialHomeomorph (affineChart k)

/-- The right line of `v` lies in the domain of the chart of `X_k ≠ 0` exactly when `v_k ≠ 0`. -/
@[simp]
theorem mk_mem_projectivizationAffineChart_source_iff (k : Fin (n + 1)) (v : Fin (n + 1) → ℍ)
    (hv : v ≠ 0) :
    Projectivization.mk ℍᵐᵒᵖ v hv ∈ (projectivizationAffineChart k).source ↔ v k ≠ 0 := by
  simp [projectivizationAffineChart]

/-- The chart of `X_k ≠ 0` takes values in the whole quaternionic affine space. -/
@[simp]
theorem projectivizationAffineChart_target (k : Fin (n + 1)) :
    (projectivizationAffineChart k).target = univ := by
  simp [projectivizationAffineChart]

/-- The chart of `X_k ≠ 0` sends the right line of `v` to the right ratios `v_j v_k⁻¹`, computed
on any representative. -/
@[simp]
theorem projectivizationAffineChart_mk (k : Fin (n + 1)) (v : Fin (n + 1) → ℍ) (hv : v ≠ 0)
    (j : Fin n) :
    projectivizationAffineChart k (Projectivization.mk ℍᵐᵒᵖ v hv) j =
      v (k.succAbove j) * (v k)⁻¹ := by
  simp [projectivizationAffineChart]

/-- The inverse of the chart of `X_k ≠ 0` sends `z` to the right line of the vector with `k`-th
coordinate `1` and remaining coordinates `z`. -/
@[simp]
theorem projectivizationAffineChart_symm_apply (k : Fin (n + 1)) (z : Fin n → ℍ) :
    (projectivizationAffineChart k).symm z =
      Projectivization.mk ℍᵐᵒᵖ (Fin.insertNth (α := fun _ ↦ ℍ) k 1 z)
        (Function.ne_iff.2 ⟨k, by simp⟩) := by
  simp [projectivizationAffineChart]

/-- **`Sp(n + 1)` acts on right lines through matrix multiplication**: a quaternionic unitary
matrix `A` sends the right line of `v` to the right line of `A v`. -/
@[simp]
theorem projectivizationHomeomorph_smul_symm_mk
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (v : Fin (n + 1) → ℍ) (hv : v ≠ 0) :
    projectivizationHomeomorph n (A • (projectivizationHomeomorph n).symm
        (Projectivization.mk ℍᵐᵒᵖ v hv)) =
      Projectivization.mk ℍᵐᵒᵖ (A.1 *ᵥ v)
        (((Matrix.mulVec_injective_of_isUnit Unitary.isUnit_coe).ne_iff'
          (Matrix.mulVec_zero _)).2 hv) := by
  rw [projectivizationHomeomorph_symm_mk, smul_mk, projectivizationHomeomorph_mk]
  refine (Projectivization.mk_eq_mk_iff' _ _ _ _ _).2
    ⟨op ((‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖⁻¹ : ℝ) : ℍ), funext fun i ↦ ?_⟩
  simp only [LinearIsometryEquiv.coe_smul_unitSphere, quaternionUnitaryIsometry_apply,
    NormedSpace.normalize, WithLp.ofLp_toLp, WithLp.ofLp_smul, Matrix.mulVec_smul, Pi.smul_apply,
    op_smul_eq_mul]
  exact Quaternion.mul_coe_eq_smul _ _

variable (n) in
/-- The base point `[e₀]` of `HPⁿ` is the right line of the first standard basis vector. -/
@[simp]
theorem projectivizationHomeomorph_basePoint :
    projectivizationHomeomorph n (basePoint n) =
      Projectivization.mk ℍᵐᵒᵖ (Pi.single 0 (1 : ℍ)) (Pi.single_ne_zero_iff.2 one_ne_zero) := by
  rw [basePoint_def, projectivizationHomeomorph_mk]

/-- **The homogeneous-space description on right lines**: the homeomorphism
`Sp(n + 1) ⧸ (Sp(1) × Sp(n)) ≃ₜ HPⁿ`, followed by `projectivizationHomeomorph`, sends the coset of
a quaternionic unitary matrix `A` to the right line `[A e₀]` spanned by its first column. -/
theorem projectivizationHomeomorph_unitaryQuotientHomeomorph_mk
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    projectivizationHomeomorph n (unitaryQuotientHomeomorph n (QuotientGroup.mk A)) =
      Projectivization.mk ℍᵐᵒᵖ (A.1 *ᵥ Pi.single 0 (1 : ℍ))
        (((Matrix.mulVec_injective_of_isUnit Unitary.isUnit_coe).ne_iff'
          (Matrix.mulVec_zero _)).2 (Pi.single_ne_zero_iff.2 one_ne_zero)) := by
  rw [unitaryQuotientHomeomorph_mk, ← (projectivizationHomeomorph n).symm_apply_apply
    (basePoint n), projectivizationHomeomorph_basePoint, projectivizationHomeomorph_smul_symm_mk]

end QuaternionicProjectiveSpace

end TauCeti
