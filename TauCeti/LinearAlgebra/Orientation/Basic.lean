/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Orientation
import TauCeti.LinearAlgebra.Dimension.CardEqFinrank
import TauCeti.LinearAlgebra.Ray

/-!
# Transporting orientations along linear equivalences

Orientation transport commutes with composition, and determinants characterize when transported
rays agree. Integral unit signs retain or reverse orientations; signed Jacobians determine their
compatibility under linear equivalences.

## Main results

* `Orientation.map_trans`: transport along a composite is the composite of the transports.
* `Orientation.map_reindex`: transport along a linear equivalence commutes with reindexing.
* `Orientation.reindex_trans`: reindexing along a composite is the composite of the reindexings.
* `Orientation.reindex_finCongr_reindex_finCongr`: two successive casts of the index type compose.
* `Orientation.map_units_smul`, `Orientation.reindex_units_smul`: transport and reindexing commute
  with scaling by units.
* `Orientation.map_eq_map_iff_det_mul_pos`: `f` and `g` transport `x` to the same orientation
  if and only if `0 < det f * det g`.
* `Orientation.map_eq_map_of_det_pos`: two linear equivalences whose relative map has positive
  determinant transport an orientation to the same orientation.
* `Orientation.map_eq_det_inv_smul_of_card_eq_finrank`,
  `Orientation.map_eq_iff_det_pos_of_card_eq_finrank` and
  `Orientation.eq_or_eq_neg_of_card_eq_finrank`: the finite-dimensional facts about orientation
  transport, valid without finite-dimensionality (the index type is then empty).
* `Orientation.intCast_units_smul_eq_ite`: an integer unit acts by retention or reversal.
* `Orientation.intCast_units_smul_injective`: the two signs give distinct orientations.
* `Orientation.reindex_perm`: reindexing along a permutation multiplies by its sign.
* `Orientation.map_units_smul_eq_iff_det_mul_pos`: the signed-Jacobian compatibility criterion.
* `Orientation.map_units_smul_eq_units_smul_map_iff_det_mul_pos`: the same criterion between two
  spaces, relative to a reference linear equivalence.
* `Orientation.map_linearEquiv_neg`: transport along the negation of an `n`-dimensional space
  multiplies an orientation by `(-1) ^ n`.
* `Orientation.eq_or_eq_neg_of_card_eq_finrank`: any two orientations are equal or opposite when
  the index type has the dimension of the space, without assuming finite dimension.
* `Orientation.intCast_units_smul_ite_eq`: the relative sign reconstructs an orientation.
-/

public section

open Module

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  {M N P : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] {ι : Type*}

/-- Transporting an orientation along a composite of linear equivalences is the same as
transporting it along each in turn. -/
@[simp]
theorem Orientation.map_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) (x : Orientation R M ι) :
    Orientation.map ι (e.trans f) x = Orientation.map ι f (Orientation.map ι e x) := by
  induction x using Module.Ray.ind with | h v hv => rfl

/-- Transporting an orientation along a linear equivalence commutes with reindexing its index
type. -/
theorem Orientation.map_reindex {ι' : Type*} (e : M ≃ₗ[R] N) (f : ι ≃ ι')
    (x : Orientation R M ι) :
    Orientation.map ι' e (Orientation.reindex R M f x) =
      Orientation.reindex R N f (Orientation.map ι e x) := by
  induction x using Module.Ray.ind with | h v hv =>
    simp only [map_apply, reindex_apply]
    congr 1

/-- Reindexing an orientation along a composite of equivalences is the same as reindexing it along
each in turn. -/
theorem Orientation.reindex_trans {ι' ι'' : Type*} (e : ι ≃ ι') (e' : ι' ≃ ι'')
    (x : Orientation R M ι) :
    Orientation.reindex R M (e.trans e') x =
      Orientation.reindex R M e' (Orientation.reindex R M e x) := by
  induction x using Module.Ray.ind with | h v hv =>
    simp only [reindex_apply, AlternatingMap.domDomCongr_trans]

/-- Reindexing along two casts `Fin m ≃ Fin n ≃ Fin k` is reindexing along their composite cast. -/
@[simp]
theorem Orientation.reindex_finCongr_reindex_finCongr {m n k : ℕ} (h : m = n) (h' : n = k)
    (x : Orientation R M (Fin m)) :
    Orientation.reindex R M (finCongr h') (Orientation.reindex R M (finCongr h) x) =
      Orientation.reindex R M (finCongr (h.trans h')) x := by
  subst h h'
  simp [finCongr_refl, Orientation.reindex_refl]

/-- Transporting an orientation along a linear equivalence commutes with scaling by a unit. -/
@[simp]
theorem Orientation.map_units_smul (e : M ≃ₗ[R] N) (u : Rˣ) (x : Orientation R M ι) :
    Orientation.map ι e (u • x) = u • Orientation.map ι e x :=
  Module.Ray.map_units_smul _ u x

/-- Reindexing an orientation commutes with scaling by a unit. -/
@[simp]
theorem Orientation.reindex_units_smul {ι' : Type*} (e : ι ≃ ι') (u : Rˣ)
    (x : Orientation R M ι) :
    Orientation.reindex R M e (u • x) = u • Orientation.reindex R M e x :=
  Module.Ray.map_units_smul _ u x

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*}

/-- Integral unit signs act on orientations by retaining or reversing the ray. -/
theorem Orientation.intCast_units_smul_eq_ite (u : ℤˣ) (o : Orientation R M ι) :
    (Units.map (Int.castRingHom R).toMonoidHom u) • o = if u = 1 then o else -o := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [Module.Ray.neg_units_smul]

/-- Distinct integral unit signs induce distinct orientations. -/
theorem Orientation.intCast_units_smul_injective [IsDomain R] (o : Orientation R M ι) :
    Function.Injective (fun u : ℤˣ ↦ (Units.map (Int.castRingHom R).toMonoidHom u) • o) := by
  intro u v huv
  simp only [intCast_units_smul_eq_ite] at huv
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all [Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self o).symm]

/-- Reindexing an orientation along a permutation of its index type multiplies it by the sign of
the permutation. -/
theorem Orientation.reindex_perm [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (o : Orientation R M ι) :
    Orientation.reindex R M σ o =
      Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign σ) • o := by
  induction o using Module.Ray.ind with | h v hv =>
    simp only [Orientation.reindex_apply, AlternatingMap.domDomCongr_perm, smul_rayOfNeZero,
      Units.smul_def, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, eq_intCast,
      Int.cast_smul_eq_zsmul]

end CommRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

/-- When the index type has cardinality equal to the `finrank`, a linear self-equivalence
transports an orientation to its multiple by the inverse determinant. Unlike
`Orientation.map_eq_det_inv_smul`, this needs no finite-dimensionality: otherwise `ι` is empty and
the determinant is `1`. -/
theorem Orientation.map_eq_det_inv_smul_of_card_eq_finrank (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x := by
  by_cases hfd : FiniteDimensional R M
  · exact map_eq_det_inv_smul x f h
  · have := Module.isEmpty_of_card_eq_finrank_of_not_finite h hfd
    have hdet : LinearEquiv.det f = 1 :=
      Units.ext (by rw [LinearEquiv.coe_det]; exact LinearMap.det_eq_one_of_not_module_finite hfd _)
    rw [map_of_isEmpty, hdet, inv_one, one_smul]

/-- The determinant criterion for a linear self-equivalence to fix an orientation, without
finite-dimensionality: see `Orientation.map_eq_iff_det_pos`. -/
theorem Orientation.map_eq_iff_det_pos_of_card_eq_finrank (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  rw [map_eq_det_inv_smul_of_card_eq_finrank x f h, units_inv_smul, units_smul_eq_self_iff,
    LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the dimension, any two orientations are equal or
negations. Unlike `Orientation.eq_or_eq_neg`, this needs no `FiniteDimensional` hypothesis: a
nonempty index type forces positive `finrank`, hence finite dimension, and otherwise
there are only the two orientations of the zero-dimensional case. -/
theorem Orientation.eq_or_eq_neg_of_card_eq_finrank (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · -- the two orientations of the empty index type are `±positiveOrientation`
    rcases Orientation.eq_or_eq_neg_of_isEmpty x₁ with rfl | rfl <;>
      rcases Orientation.eq_or_eq_neg_of_isEmpty x₂ with rfl | rfl
    · exact .inl rfl
    · exact .inr (neg_neg (positiveOrientation : Orientation R M ι)).symm
    · exact .inr rfl
    · exact .inl rfl
  · have : FiniteDimensional R M := Module.finite_of_finrank_pos (h ▸ Fintype.card_pos)
    exact Orientation.eq_or_eq_neg x₁ x₂ h

/-- When the index type has cardinality equal to the `finrank`, two self-equivalences transport an
orientation to the same orientation if and only if their determinants have the same sign. No
finite-dimensionality is needed: otherwise `ι` is empty and both determinants are `1`. -/
theorem Orientation.map_eq_map_iff_det_mul_pos (x : Orientation R M ι)
    (f g : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = Orientation.map ι g x ↔
      0 < LinearMap.det (f : M →ₗ[R] M) * LinearMap.det (g : M →ₗ[R] M) := by
  have htransport : Orientation.map ι f x = Orientation.map ι g x ↔
      Orientation.map ι (f.trans g.symm) x = x := by
    rw [map_trans, ← map_symm, Equiv.symm_apply_eq]
  have hdet : LinearMap.det (f.trans g.symm : M →ₗ[R] M) =
      LinearMap.det (f : M →ₗ[R] M) / LinearMap.det (g : M →ₗ[R] M) := by
    simp [← LinearEquiv.coe_det, LinearEquiv.det_trans, LinearEquiv.det_symm,
      div_eq_mul_inv, mul_comm]
  rw [htransport, map_eq_iff_det_pos_of_card_eq_finrank _ _ h, hdet]
  exact div_pos_iff.trans mul_pos_iff.symm

/-- Two linear equivalences `S` and `T` such that `S.trans T.symm` has positive determinant
transport an orientation to the same orientation. -/
theorem Orientation.map_eq_map_of_det_pos {N : Type*} [AddCommGroup N]
    [Module R N] (x : Orientation R M ι) (S T : M ≃ₗ[R] N) (h : Fintype.card ι = finrank R M)
    (hdet : 0 < LinearMap.det ((S.trans T.symm : M ≃ₗ[R] M) : M →ₗ[R] M)) :
    Orientation.map ι S x = Orientation.map ι T x := by
  have hfix := (map_eq_iff_det_pos_of_card_eq_finrank x _ h).mpr hdet
  rwa [map_trans, ← map_symm, Equiv.symm_apply_eq] at hfix

/-- The signed Jacobian criterion for transporting orientations with arbitrary unit scalars. -/
theorem Orientation.map_units_smul_eq_iff_det_mul_pos
    (o : Orientation R M ι) (A : M ≃ₗ[R] M) (u v : Rˣ)
    (hι : Fintype.card ι = finrank R M) :
    Orientation.map ι A (u • o) = v • o ↔
      0 < (u : R) * (v : R) * LinearMap.det A.toLinearMap := by
  rw [map_eq_det_inv_smul_of_card_eq_finrank _ _ hι, ← inv_smul_eq_iff, ← mul_smul,
    ← mul_smul, units_smul_eq_self_iff]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, LinearEquiv.coe_det]
  have h := (div_pos_iff.trans mul_pos_iff.symm :
    0 < (u : R) / ((v : R) * LinearMap.det A.toLinearMap) ↔
      0 < (u : R) * ((v : R) * LinearMap.det A.toLinearMap))
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h

/-- The signed Jacobian criterion for transporting orientations between two spaces: a linear
equivalence `A : M ≃ N` carries `u • o` to `v • C o`, where `C : M ≃ N` is a reference
equivalence, exactly when `u v det (C⁻¹ ∘ A)` is positive. -/
theorem Orientation.map_units_smul_eq_units_smul_map_iff_det_mul_pos
    {N : Type*} [AddCommGroup N] [Module R N] (o : Orientation R M ι) (A C : M ≃ₗ[R] N)
    (u v : Rˣ) (hι : Fintype.card ι = finrank R M) :
    Orientation.map ι A (u • o) = v • Orientation.map ι C o ↔
      0 < (u : R) * (v : R) * LinearMap.det (A.trans C.symm).toLinearMap := by
  have hC : v • Orientation.map ι C o = Orientation.map ι C (v • o) := by
    rw [Orientation.map, Module.Ray.map_units_smul]
  rw [← map_units_smul_eq_iff_det_mul_pos o _ u v hι, hC, map_trans, ← map_symm,
    Equiv.symm_apply_eq]

/-- Transport along the negation of a space of dimension `n` multiplies an orientation by
`(-1) ^ n`. -/
theorem Orientation.map_linearEquiv_neg (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι (LinearEquiv.neg R) x = (-1 : Rˣ) ^ finrank R M • x := by
  rw [map_eq_det_inv_smul_of_card_eq_finrank _ _ h]
  congr 1
  have hneg : ((LinearEquiv.neg R : M ≃ₗ[R] M) : M →ₗ[R] M) = (-1 : R) • LinearMap.id := by
    ext; simp
  have hdet : LinearEquiv.det (LinearEquiv.neg R : M ≃ₗ[R] M) = (-1 : Rˣ) ^ finrank R M := by
    ext
    rw [LinearEquiv.coe_det, hneg, LinearMap.det_smul]
    simp
  rw [hdet]
  exact inv_eq_of_mul_eq_one_right (by simp [← mul_pow])

open Classical in
/-- The sign distinguishing two orientations reconstructs the second from the first when
the index type has the dimension of the space. -/
theorem Orientation.intCast_units_smul_ite_eq
    (model o : Orientation R M ι) (hι : Fintype.card ι = finrank R M) :
    (Units.map (Int.castRingHom R).toMonoidHom (if o = model then 1 else -1)) • model = o := by
  rcases eq_or_eq_neg_of_card_eq_finrank o model hι with h | h <;>
    simp [h, (Module.Ray.ne_neg_self model).symm]

end Field
