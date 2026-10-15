/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.NoncommRing

/-!
# Splitting a binary plane off a Clifford algebra

For units `a` and `b` of a commutative ring `R` and an arbitrary quadratic module `(M, Q)`, the
Clifford algebra of the orthogonal sum `⟨a, b⟩ ⊥ Q` is an ordinary (ungraded) tensor product

`C(⟨a, b⟩ ⊥ Q) ≅ ℍ[R, a, b] ⊗ C(-a⁻¹b⁻¹ · Q)`.

The plane `⟨a, b⟩` is Mathlib's `CliffordAlgebraQuaternion.Q a b`, whose Clifford algebra is the
quaternion algebra `ℍ[R, a, b]`. The mechanism is the plane's volume element `ω = e₁e₂`, which is
the quaternion unit `k`: it squares to `-ab`, anticommutes with the plane vectors, and commutes
with the vectors of `M`. Hence `m ↦ ι m · ω` turns the generators of `C(Q)` into elements commuting
with the plane, squaring to `-ab · Q m`; rescaling the form by `(-ab)⁻¹ = -a⁻¹b⁻¹` compensates.

Iterating this over a diagonal form expresses the Clifford algebra of an even-dimensional
diagonal form as a tensor product of quaternion algebras, which is how the Clifford invariant of
a quadratic form is computed in terms of quaternion symbols (Lam, Chapter V, §2 and V.3.20).

## Main definitions

* `CliffordAlgebra.quaternionPlaneEquivTensor`: the algebra equivalence
  `C(⟨a, b⟩ ⊥ Q) ≃ₐ[R] ℍ[R, a, b] ⊗[R] C(-a⁻¹b⁻¹ · Q)`.

## Main results

* `CliffordAlgebra.quaternionPlaneEquivTensor_ι`: it sends a generator `(v, m)` to
  `(v₁ i + v₂ j) ⊗ 1 + k ⊗ ι m`.
* `CliffordAlgebra.quaternionPlaneEquivTensor_symm_tmul_one` and
  `CliffordAlgebra.quaternionPlaneEquivTensor_symm_one_tmul`: its inverse on each tensor factor.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, §2.
* The construction adapts the volume-element argument of
  `TauCeti.LinearAlgebra.CliffordAlgebra.NegativePlane` (`CliffordAlgebra.negativePlaneEquivTensor`)
  from the real plane `⟨-1, -1⟩` to an arbitrary plane `⟨a, b⟩`: the same generator lift, inclusions
  of the two factors, commutation argument, tensor-product lift, and check of the two composites.
-/

public section

open QuadraticMap
open scoped Quaternion TensorProduct

namespace CliffordAlgebra

section Ring

variable {R : Type*} [Ring R] (a b : Rˣ)

/-- The pure quaternion `v₁ i + v₂ j` attached to a plane vector. -/
private abbrev pureQuaternion (v : R × R) : ℍ[R,(a : R),(b : R)] := ⟨0, v.1, v.2, 0⟩

private theorem k_mul_pureQuaternion_add (v : R × R) :
    (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) * pureQuaternion a b v +
      pureQuaternion a b v * ⟨0, 0, 0, 1⟩ = 0 := by
  ext <;> simp

end Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) (a b : Rˣ)

/-- The scalar `-a⁻¹b⁻¹` rescaling the complementary form. -/
private abbrev planeScale : R := -(↑a⁻¹ * ↑b⁻¹)

private theorem planeScale_mul : planeScale a b * -((a : R) * b) = 1 := by
  rw [planeScale, neg_mul_neg, mul_mul_mul_comm, Units.inv_mul, Units.inv_mul, one_mul]

private abbrev PlaneForm : QuadraticForm R ((R × R) × M) :=
  (CliffordAlgebraQuaternion.Q (a : R) b).prod Q

private abbrev PlaneTensor :=
  ℍ[R,(a : R),(b : R)] ⊗[R] CliffordAlgebra (planeScale a b • Q)

/-! ### Quaternion identities -/

private theorem k_mul_k :
    (⟨0, 0, 0, 1⟩ * ⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) = algebraMap R _ (-((a : R) * b)) := by
  ext <;> simp

/-! ### The forward map -/

private noncomputable def planeGenerator : (R × R) × M →ₗ[R] PlaneTensor Q a b :=
  LinearMap.coprod
    (((TensorProduct.mk R ℍ[R,(a : R),(b : R)]
        (CliffordAlgebra (planeScale a b • Q))).flip 1).comp
      (CliffordAlgebraQuaternion.toQuaternion.toLinearMap.comp
        (ι (CliffordAlgebraQuaternion.Q (a : R) b))))
    ((TensorProduct.mk R ℍ[R,(a : R),(b : R)] (CliffordAlgebra (planeScale a b • Q))
      ⟨0, 0, 0, 1⟩).comp (ι (planeScale a b • Q)))

private theorem planeGenerator_apply (x : (R × R) × M) :
    planeGenerator Q a b x =
      pureQuaternion a b x.1 ⊗ₜ 1 + (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) ⊗ₜ ι _ x.2 := by
  simp [planeGenerator]

private theorem planeGenerator_sq (x : (R × R) × M) :
    planeGenerator Q a b x * planeGenerator Q a b x =
      algebraMap R (PlaneTensor Q a b) (PlaneForm Q a b x) := by
  rw [planeGenerator_apply]
  set A : PlaneTensor Q a b := pureQuaternion a b x.1 ⊗ₜ 1 with hA
  set B : PlaneTensor Q a b := (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) ⊗ₜ ι _ x.2 with hB
  have hAA : A * A = algebraMap R _ (CliffordAlgebraQuaternion.Q (a : R) b x.1) := by
    rw [hA, Algebra.TensorProduct.tmul_mul_tmul, pureQuaternion,
      ← CliffordAlgebraQuaternion.toQuaternion_ι, ← map_mul, ι_sq_scalar, AlgHom.commutes,
      one_mul, Algebra.TensorProduct.algebraMap_apply]
  have hBB : B * B = algebraMap R _ (Q x.2) := by
    rw [hB, Algebra.TensorProduct.tmul_mul_tmul, k_mul_k, ι_sq_scalar,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul,
      ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one, smul_apply, smul_eq_mul,
      ← mul_assoc, mul_comm (-((a : R) * b)), planeScale_mul, one_mul]
  have hAB : A * B + B * A = 0 := by
    rw [hA, hB, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, ← TensorProduct.add_tmul, add_comm, k_mul_pureQuaternion_add,
      TensorProduct.zero_tmul]
  have hexpand : (A + B) * (A + B) = A * A + (A * B + B * A) + B * B := by noncomm_ring
  rw [hexpand, hAA, hBB, hAB, add_zero, ← map_add, QuadraticMap.prod_apply]

private noncomputable def planeToTensor :
    CliffordAlgebra (PlaneForm Q a b) →ₐ[R] PlaneTensor Q a b :=
  lift _ ⟨planeGenerator Q a b, planeGenerator_sq Q a b⟩

private theorem planeToTensor_ι (x : (R × R) × M) :
    planeToTensor Q a b (ι _ x) =
      pureQuaternion a b x.1 ⊗ₜ 1 + (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) ⊗ₜ ι _ x.2 := by
  rw [planeToTensor, lift_ι_apply, planeGenerator_apply]

/-! ### The inverse map -/

/-- The quaternion algebra of the plane, included in `C(⟨a, b⟩ ⊥ Q)`. -/
private noncomputable def quaternionInclusion :
    ℍ[R,(a : R),(b : R)] →ₐ[R] CliffordAlgebra (PlaneForm Q a b) :=
  (map (Isometry.inl (CliffordAlgebraQuaternion.Q (a : R) b) Q)).comp
    CliffordAlgebraQuaternion.ofQuaternion

private theorem quaternionInclusion_pureQuaternion (v : R × R) :
    quaternionInclusion Q a b (pureQuaternion a b v) = ι _ (v, 0) := by
  rw [pureQuaternion, ← CliffordAlgebraQuaternion.toQuaternion_ι, quaternionInclusion,
    AlgHom.comp_apply, CliffordAlgebraQuaternion.ofQuaternion_toQuaternion, map_apply_ι]
  -- Mathlib states no apply lemma for `QuadraticMap.Isometry.inl`; it is `LinearMap.inl`.
  rfl

/-- The volume element `e₁e₂` of the plane, the image of the quaternion unit `k`. -/
private noncomputable abbrev planeVolume : CliffordAlgebra (PlaneForm Q a b) :=
  quaternionInclusion Q a b ⟨0, 0, 0, 1⟩

private theorem planeVolume_mul_self :
    planeVolume Q a b * planeVolume Q a b = algebraMap R _ (-((a : R) * b)) := by
  rw [← map_mul, k_mul_k, AlgHom.commutes]

private theorem planeVolume_anticomm (v : R × R) :
    planeVolume Q a b * ι _ (v, 0) = -(ι _ (v, 0) * planeVolume Q a b) := by
  rw [eq_neg_iff_add_eq_zero, ← quaternionInclusion_pureQuaternion, ← map_mul, ← map_mul,
    ← map_add, k_mul_pureQuaternion_add, map_zero]

private theorem commute_ι_inr_planeVolume (m : M) :
    Commute (ι (PlaneForm Q a b) (0, m)) (planeVolume Q a b) := by
  have hk : CliffordAlgebraQuaternion.ofQuaternion (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) =
      ι (CliffordAlgebraQuaternion.Q (a : R) b) (1, 0) *
        ι (CliffordAlgebraQuaternion.Q (a : R) b) (0, 1) := by
    simp
  have h := commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
    (Isometry.inl (CliffordAlgebraQuaternion.Q (a : R) b) Q)
    (Isometry.inr (CliffordAlgebraQuaternion.Q (a : R) b) Q)
    (fun x y => IsOrtho.inl_inr x y) _ (ι Q m)
    (hk ▸ ι_mul_ι_mem_evenOdd_zero _ _ _) (ι_mem_evenOdd_one Q m)
  rw [map_apply_ι] at h
  exact h.symm

/-- The generators of `C(-a⁻¹b⁻¹ · Q)` inside `C(⟨a, b⟩ ⊥ Q)`: `m ↦ -a⁻¹b⁻¹ · ι m · ω`. -/
private noncomputable def baseGenerator : M →ₗ[R] CliffordAlgebra (PlaneForm Q a b) :=
  planeScale a b • ((LinearMap.mulRight R (planeVolume Q a b)).comp
    ((ι (PlaneForm Q a b)).comp (LinearMap.inr R (R × R) M)))

private theorem baseGenerator_apply (m : M) :
    baseGenerator Q a b m = planeScale a b • (ι _ (0, m) * planeVolume Q a b) := rfl

private theorem baseGenerator_sq (m : M) :
    baseGenerator Q a b m * baseGenerator Q a b m =
      algebraMap R _ ((planeScale a b • Q) m) := by
  have hX : ι (PlaneForm Q a b) (0, m) * planeVolume Q a b *
      (ι (PlaneForm Q a b) (0, m) * planeVolume Q a b) =
        algebraMap R _ (Q m * -((a : R) * b)) := by
    rw [(commute_ι_inr_planeVolume Q a b m).symm.mul_mul_mul_comm,
      planeVolume_mul_self, ι_sq_scalar, ← map_mul, QuadraticMap.prod_apply, map_zero, zero_add]
  rw [baseGenerator_apply, smul_mul_smul_comm, hX, Algebra.smul_def, ← map_mul, smul_apply,
    smul_eq_mul]
  congr 1
  calc
    _ = (planeScale a b * Q m) * (planeScale a b * -((a : R) * b)) := by ring
    _ = _ := by rw [planeScale_mul, mul_one]

private noncomputable def baseInclusion :
    CliffordAlgebra (planeScale a b • Q) →ₐ[R] CliffordAlgebra (PlaneForm Q a b) :=
  lift _ ⟨baseGenerator Q a b, baseGenerator_sq Q a b⟩

private theorem baseInclusion_ι (m : M) :
    baseInclusion Q a b (ι _ m) = planeScale a b • (ι _ (0, m) * planeVolume Q a b) := by
  rw [baseInclusion, lift_ι_apply, baseGenerator_apply]

private theorem commute_quaternionInclusion_baseInclusion (x : ℍ[R,(a : R),(b : R)])
    (y : CliffordAlgebra (planeScale a b • Q)) :
    Commute (quaternionInclusion Q a b x) (baseInclusion Q a b y) := by
  -- It suffices to commute every element of `C(⟨a, b⟩)` past the generators `ι m · ω`.
  suffices h : ∀ (z : CliffordAlgebra (CliffordAlgebraQuaternion.Q (a : R) b)) (m : M),
      Commute (map (Isometry.inl (CliffordAlgebraQuaternion.Q (a : R) b) Q) z)
        (ι _ (0, m) * planeVolume Q a b) by
    induction y using CliffordAlgebra.induction with
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Algebra.commutes r _ |>.symm
    | ι m =>
      rw [baseInclusion_ι]
      exact (h (CliffordAlgebraQuaternion.ofQuaternion x) m).smul_right _
    | mul y₁ y₂ h₁ h₂ => simpa only [map_mul] using h₁.mul_right h₂
    | add y₁ y₂ h₁ h₂ => simpa only [map_add] using h₁.add_right h₂
  intro z m
  induction z using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact Algebra.commutes r _
  | ι v =>
    have hv : map (Isometry.inl (CliffordAlgebraQuaternion.Q (a : R) b) Q) (ι _ v) =
        ι (PlaneForm Q a b) (v, 0) :=
      -- As above, `QuadraticMap.Isometry.inl` unfolds to `LinearMap.inl`.
      map_apply_ι _ v
    have hvm : ι (PlaneForm Q a b) (v, 0) * ι _ (0, m) = -(ι _ (0, m) * ι _ (v, 0)) :=
      ι_mul_ι_comm_of_isOrtho (IsOrtho.inl_inr v m)
    rw [hv, Commute, SemiconjBy, ← mul_assoc, hvm, mul_assoc, planeVolume_anticomm]
    noncomm_ring
  | mul z₁ z₂ h₁ h₂ => simpa only [map_mul] using h₁.mul_left h₂
  | add z₁ z₂ h₁ h₂ => simpa only [map_add] using h₁.add_left h₂

private noncomputable def tensorToPlane :
    PlaneTensor Q a b →ₐ[R] CliffordAlgebra (PlaneForm Q a b) :=
  Algebra.TensorProduct.lift (quaternionInclusion Q a b) (baseInclusion Q a b)
    (commute_quaternionInclusion_baseInclusion Q a b)

/-! ### The two composites -/

private theorem planeVolume_mul_baseInclusion_ι (m : M) :
    planeVolume Q a b * baseInclusion Q a b (ι _ m) = ι _ (0, m) := by
  rw [baseInclusion_ι, mul_smul_comm, ← mul_assoc, ← (commute_ι_inr_planeVolume Q a b m).eq,
    mul_assoc, planeVolume_mul_self, ← Algebra.commutes, ← Algebra.smul_def, smul_smul,
    planeScale_mul, one_smul]

private theorem tensorToPlane_comp_planeToTensor :
    (tensorToPlane Q a b).comp (planeToTensor Q a b) = AlgHom.id R _ := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  rintro ⟨v, m⟩
  simpa [planeToTensor_ι, tensorToPlane, quaternionInclusion_pureQuaternion,
    planeVolume_mul_baseInclusion_ι] using (map_add (ι (PlaneForm Q a b)) (v, 0) (0, m)).symm

private theorem planeToTensor_comp_quaternionInclusion :
    (planeToTensor Q a b).comp (quaternionInclusion Q a b) =
      Algebra.TensorProduct.includeLeft := by
  have hi := quaternionInclusion_pureQuaternion Q a b (1, 0)
  have hj := quaternionInclusion_pureQuaternion Q a b (0, 1)
  ext
  · simp [hi, planeToTensor_ι]
  · simp [hj, planeToTensor_ι]

private theorem planeToTensor_planeVolume :
    planeToTensor Q a b (planeVolume Q a b) =
      (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) ⊗ₜ 1 := by
  rw [planeVolume, ← AlgHom.comp_apply, planeToTensor_comp_quaternionInclusion,
    Algebra.TensorProduct.includeLeft_apply]

private theorem planeToTensor_comp_baseInclusion :
    (planeToTensor Q a b).comp (baseInclusion Q a b) = Algebra.TensorProduct.includeRight := by
  apply CliffordAlgebra.hom_ext
  ext m
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    baseInclusion_ι, map_smul, map_mul, planeToTensor_ι, planeToTensor_planeVolume,
    Algebra.TensorProduct.includeRight_apply, pureQuaternion, Prod.fst_zero, Prod.snd_zero]
  have h0 : (⟨0, 0, 0, 0⟩ : ℍ[R,(a : R),(b : R)]) = 0 := by ext <;> rfl
  rw [h0, TensorProduct.zero_tmul, zero_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, k_mul_k,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul,
    smul_smul, planeScale_mul, one_smul]

private theorem planeToTensor_comp_tensorToPlane :
    (planeToTensor Q a b).comp (tensorToPlane Q a b) = AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [AlgHom.comp_apply, tensorToPlane, Algebra.TensorProduct.lift_tmul, map_mul,
    ← AlgHom.comp_apply, ← AlgHom.comp_apply, planeToTensor_comp_quaternionInclusion,
    planeToTensor_comp_baseInclusion]
  simp

/-! ### The equivalence -/

/-- **Splitting a binary plane off a Clifford algebra.** For units `a` and `b`, the Clifford
algebra of `⟨a, b⟩ ⊥ Q` is the tensor product of the quaternion algebra `ℍ[R, a, b]` with the
Clifford algebra of the rescaled form `-a⁻¹b⁻¹ · Q` (Lam, Chapter V, §2). -/
noncomputable def quaternionPlaneEquivTensor :
    CliffordAlgebra ((CliffordAlgebraQuaternion.Q (a : R) b).prod Q) ≃ₐ[R]
      ℍ[R,(a : R),(b : R)] ⊗[R] CliffordAlgebra (-(↑a⁻¹ * ↑b⁻¹ : R) • Q) :=
  AlgEquiv.ofAlgHom (planeToTensor Q a b) (tensorToPlane Q a b)
    (planeToTensor_comp_tensorToPlane Q a b) (tensorToPlane_comp_planeToTensor Q a b)

/-- `quaternionPlaneEquivTensor` sends a plane generator to the pure quaternion `v₁ i + v₂ j` and a
generator of `M` to `k ⊗ ι m`. -/
@[simp]
theorem quaternionPlaneEquivTensor_ι (x : (R × R) × M) :
    quaternionPlaneEquivTensor Q a b (ι _ x) =
      (⟨0, x.1.1, x.1.2, 0⟩ : ℍ[R,(a : R),(b : R)]) ⊗ₜ 1 +
        (⟨0, 0, 0, 1⟩ : ℍ[R,(a : R),(b : R)]) ⊗ₜ ι _ x.2 :=
  planeToTensor_ι Q a b x

/-- The inverse of `quaternionPlaneEquivTensor` on the quaternion factor is the inclusion of the
plane's Clifford algebra `ℍ[R, a, b] ≅ C(⟨a, b⟩)`. -/
@[simp]
theorem quaternionPlaneEquivTensor_symm_tmul_one (x : ℍ[R,(a : R),(b : R)]) :
    (quaternionPlaneEquivTensor Q a b).symm (x ⊗ₜ 1) =
      map (Isometry.inl (CliffordAlgebraQuaternion.Q (a : R) b) Q)
        (CliffordAlgebraQuaternion.ofQuaternion x) := by
  rw [quaternionPlaneEquivTensor, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply, tensorToPlane,
    Algebra.TensorProduct.lift_tmul, map_one, mul_one, quaternionInclusion, AlgHom.comp_apply]

/-- The inverse of `quaternionPlaneEquivTensor` sends `1 ⊗ ι m` to `-a⁻¹b⁻¹ · ι m · e₁e₂`. -/
@[simp]
theorem quaternionPlaneEquivTensor_symm_one_tmul (m : M) :
    (quaternionPlaneEquivTensor Q a b).symm (1 ⊗ₜ ι _ m) =
      -(↑a⁻¹ * ↑b⁻¹ : R) • (ι _ (0, m) * ι _ ((1, 0), 0) * ι _ ((0, 1), 0)) := by
  rw [quaternionPlaneEquivTensor, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply, tensorToPlane,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul, baseInclusion_ι, mul_assoc]
  congr 2
  rw [planeVolume, quaternionInclusion, AlgHom.comp_apply]
  simp

end CliffordAlgebra
