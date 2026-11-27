/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry
public import TauCeti.RingTheory.Idempotents.Module

/-!
# Dual coordinates on a split Hermitian space

For a signed Hermitian form over the exchange involution of `F × F`, the two idempotents
`(1, 0)` and `(0, 1)` give totally isotropic summands. If `V` is finite-dimensional over
the field `F`, the first component of the form gives a perfect pairing of the two summands.
Thus a vector has canonical coordinates in `A × Module.Dual F A`, where `A = (1, 0) • V`.

In these coordinates the signed Hermitian pairing of `(x, ℓ)` and `(y, k)` is
`(ℓ y, ε • k x)`. A linear automorphism preserves the pairing precisely when it
acts by an automorphism on `A` and by its inverse dual on the other summand.

## References

* W. T. Gan, Y. Qiu and S. Takeda, *The regularized Siegel–Weil formula (the second term
  identity) and the Rallis inner product formula*, §§2.1–2.2 and 2.9.
-/

public section

open Module
open scoped Pointwise

namespace TauCeti.SignedHermitianSpace

section CommRing

variable {F V : Type*} [CommRing F] [AddCommGroup V] [Module (F × F) V]
  [Module F V] [IsScalarTower F (F × F) V]

variable (F V) in
/-- The first idempotent summand of a module over the split algebra `F × F`. -/
abbrev splitFst : Submodule F V := ((1, 0) : F × F) • ⊤

variable (F V) in
/-- The second idempotent summand of a module over the split algebra `F × F`. -/
abbrev splitSnd : Submodule F V := ((0, 1) : F × F) • ⊤

/-- The first idempotent summand consists of the vectors fixed by `(1, 0)`. -/
theorem mem_splitFst_iff {v : V} : v ∈ splitFst F V ↔ ((1, 0) : F × F) • v = v :=
  IsIdempotentElem.mem_smul_top_iff_smul_eq_self (by
    ext <;> simp)

/-- The second idempotent summand consists of the vectors fixed by `(0, 1)`. -/
theorem mem_splitSnd_iff {v : V} : v ∈ splitSnd F V ↔ ((0, 1) : F × F) • v = v :=
  IsIdempotentElem.mem_smul_top_iff_smul_eq_self (by
    ext <;> simp)

variable {ε : ℤˣ}
  (H : SignedHermitianSpace (F × F) V
    ((RingEquiv.prodComm : F × F ≃+* F × F) : F × F →+* F × F) ε)

omit [Module F V] [IsScalarTower F (F × F) V] in
private theorem form_fst_smul_idempotents (v w : V) :
    (H.form (((0, 1) : F × F) • v) (((1, 0) : F × F) • w)).1 = (H.form v w).1 := by
  rw [H.form.map_smulₛₗ]
  simp [smul_eq_mul]

omit [Module F V] [IsScalarTower F (F × F) V] in
private theorem form_snd_eq_smul_fst (v w : V) : (H.form v w).2 = ε • (H.form w v).1 :=
  congrArg Prod.snd (H.form_swap w v)

/-- The first component of the signed Hermitian form pairs the second summand with the first. -/
def splitPairing : splitSnd F V →ₗ[F] Dual F (splitFst F V) :=
  LinearMap.mk₂ F (fun v w ↦ (H.form v w).1)
    (fun v v' w ↦ by
      rw [Submodule.coe_add, H.form.map_add]
      rfl)
    (fun r v w ↦ by
      rw [SetLike.val_smul, ← IsScalarTower.algebraMap_smul (A := F × F), H.form.map_smulₛₗ]
      simp [smul_eq_mul])
    (fun v w w' ↦ by simp)
    (fun r v w ↦ by
      rw [SetLike.val_smul, ← IsScalarTower.algebraMap_smul (A := F × F)]
      simp [smul_eq_mul])

/-- The cross pairing evaluates to the first coordinate of the original form. -/
@[simp]
theorem splitPairing_apply (v : splitSnd F V) (w : splitFst F V) :
    H.splitPairing v w = (H.form v w).1 := (rfl)

end CommRing

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (F × F) V]
  [Module F V] [IsScalarTower F (F × F) V] {ε : ℤˣ}
  (H : SignedHermitianSpace (F × F) V
    ((RingEquiv.prodComm : F × F ≃+* F × F) : F × F →+* F × F) ε)

/-- The cross pairing of the idempotent summands is perfect. -/
theorem isPerfPair_splitPairing [Module.Finite F V] : H.splitPairing.IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · refine (injective_iff_map_eq_zero _).2 fun v hv ↦ Subtype.ext (H.separatingLeft v fun w ↦ ?_)
    apply Prod.ext
    · have hw := LinearMap.congr_fun hv (smulTopRetraction (S := F) ((1, 0) : F × F) w)
      rw [splitPairing_apply, coe_smulTopRetraction_apply, LinearMap.zero_apply] at hw
      rw [← H.form_fst_smul_idempotents v w, mem_splitSnd_iff.mp v.property]
      exact hw
    · have hz : ((1, 0) : F × F) • (v : V) = 0 :=
        smul_eq_zero_of_mul_eq_zero_of_mem_smul_top
          (S := F) (e := ((0, 1) : F × F)) (by ext <;> simp) v.property
      rw [H.form_snd_eq_smul_fst, ← H.form_fst_smul_idempotents w v, hz]
      simp
  · refine (injective_iff_map_eq_zero _).2 fun w hw ↦ Subtype.ext (H.separatingRight w fun v ↦ ?_)
    apply Prod.ext
    · have hv := LinearMap.congr_fun hw (smulTopRetraction (S := F) ((0, 1) : F × F) v)
      rw [LinearMap.flip_apply, splitPairing_apply, coe_smulTopRetraction_apply,
        LinearMap.zero_apply] at hv
      rw [← H.form_fst_smul_idempotents v w, mem_splitFst_iff.mp w.property]
      exact hv
    · have hz : ((0, 1) : F × F) • (w : V) = 0 :=
        smul_eq_zero_of_mul_eq_zero_of_mem_smul_top
          (S := F) (e := ((1, 0) : F × F)) (by ext <;> simp) w.property
      rw [H.form_snd_eq_smul_fst, ← H.form_fst_smul_idempotents w v, hz, H.form.map_zero]
      simp

/-- Canonical coordinates on a split signed Hermitian space. The first coordinate is in the
first idempotent summand, and the second is a functional on that summand. -/
noncomputable def splitCoordinates [Module.Finite F V] :
    V ≃ₗ[F] splitFst F V × Dual F (splitFst F V) :=
  letI := H.isPerfPair_splitPairing
  have h : IsIdempotentElem ((1, 0) : F × F) := isIdempotentElem_iff.mpr (by ext <;> simp)
  (h.smulTopProdEquiv (f := (0, 1)) (by ext <;> simp)).trans
    ((LinearEquiv.refl F _).prodCongr H.splitPairing.toPerfPair)

/-- The vector coordinate is the projection given by the first idempotent. -/
@[simp]
theorem splitCoordinates_fst [Module.Finite F V] (v : V) :
    ((H.splitCoordinates v).1 : V) = ((1, 0) : F × F) • v := by
  simp [splitCoordinates, LinearEquiv.prodCongr_apply]

/-- The functional coordinate evaluates by pairing in the first component. -/
@[simp]
theorem splitCoordinates_snd_apply [Module.Finite F V] (v : V) (w : splitFst F V) :
    (H.splitCoordinates v).2 w = (H.form v w).1 := by
  rw [← H.form_fst_smul_idempotents v w, mem_splitFst_iff.mp w.property]
  simp [splitCoordinates, LinearEquiv.prodCongr_apply]

/-- The matrix-free formula for the form in its dual coordinates. -/
theorem form_eq_splitCoordinates [Module.Finite F V] (v w : V) :
    H.form v w =
      ((H.splitCoordinates v).2 (H.splitCoordinates w).1,
        ε • (H.splitCoordinates w).2 (H.splitCoordinates v).1) := by
  apply Prod.ext
  · simp
  · rw [H.form_snd_eq_smul_fst]
    simp

/-- Split scalars act through the first projection on vectors and the second on functionals. -/
@[simp]
theorem splitCoordinates_smul [Module.Finite F V] (a : F × F) (v : V) :
    H.splitCoordinates (a • v) =
      (a.1 • (H.splitCoordinates v).1, a.2 • (H.splitCoordinates v).2) := by
  refine Prod.ext (Subtype.ext ?_) (LinearMap.ext fun w ↦ ?_)
  · rw [splitCoordinates_fst, SetLike.val_smul, splitCoordinates_fst,
      ← IsScalarTower.algebraMap_smul (A := F × F) a.1, smul_smul, smul_smul]
    congr 1
    ext <;> simp
  · simp only [splitCoordinates_snd_apply, LinearMap.smul_apply]
    rw [H.form.map_smulₛₗ]
    simp [smul_eq_mul]

/-- A finite-dimensional split signed Hermitian space is perfect over the split algebra.
Every linear functional over the split algebra is obtained by pairing with a unique vector. -/
theorem split_form_bijective [Module.Finite F V] : Function.Bijective H.form := by
  refine ⟨LinearMap.ker_eq_bot.1 (LinearMap.separatingLeft_iff_ker_eq_bot.1 H.separatingLeft), ?_⟩
  intro f
  let f₁ := LinearMap.fst F F F ∘ₗ (f.restrictScalars F).comp (splitFst F V).subtype
  let f₂ := LinearMap.snd F F F ∘ₗ (f.restrictScalars F).comp (splitSnd F V).subtype
  let : H.splitPairing.IsPerfPair := H.isPerfPair_splitPairing
  obtain ⟨a, ha⟩ := (LinearMap.IsPerfPair.bijective_right H.splitPairing).surjective (ε • f₂)
  refine ⟨H.splitCoordinates.symm (a, f₁), LinearMap.ext fun w ↦ ?_⟩
  rw [H.form_eq_splitCoordinates, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · simp [f₁, map_smul, smul_eq_mul]
  · have h := LinearMap.congr_fun ha (smulTopRetraction (S := F) ((0, 1) : F × F) w)
    rw [LinearMap.flip_apply, splitPairing_apply, coe_smulTopRetraction_apply] at h
    simp only [splitCoordinates_snd_apply]
    rw [← H.form_fst_smul_idempotents w a, mem_splitFst_iff.mp a.property]
    simpa [f₂, map_smul, smul_eq_mul, smul_smul, Int.units_mul_self] using (congrArg (ε • ·) h)

variable [Module.Finite F V]

private noncomputable def splitIsometry (g : splitFst F V ≃ₗ[F] splitFst F V) :
    V ≃ₗ[F × F] V :=
  let e := H.splitCoordinates.trans (g.prodCongr g.symm.dualMap) |>.trans H.splitCoordinates.symm
  { e.toAddEquiv with
    map_smul' a v := by
      apply H.splitCoordinates.injective
      simp [e, LinearEquiv.prodCongr_apply] }

private theorem splitCoordinates_splitIsometry (g : splitFst F V ≃ₗ[F] splitFst F V) (v : V) :
    H.splitCoordinates (H.splitIsometry g v) =
      (g ((H.splitCoordinates v).1), g.symm.dualMap ((H.splitCoordinates v).2)) := by
  simp [splitIsometry, LinearEquiv.prodCongr_apply]

private theorem splitIsometry_mem_isometryGroup (g : splitFst F V ≃ₗ[F] splitFst F V) :
    H.splitIsometry g ∈ H.form.isometryGroup := by
  refine LinearMap.mem_isometryGroup_iff.mpr fun v w ↦ ?_
  rw [H.form_eq_splitCoordinates (H.splitIsometry g v), H.form_eq_splitCoordinates v]
  simp [H.splitCoordinates_splitIsometry, LinearEquiv.dualMap_apply]

private theorem splitCoordinates_isometry (e : H.form.isometryGroup) (v : V) :
    let g := (e : V ≃ₗ[F × F] V).smulTopCongr F (1, 0)
    H.splitCoordinates ((e : V ≃ₗ[F × F] V) v) =
      (g ((H.splitCoordinates v).1), g.symm.dualMap ((H.splitCoordinates v).2)) := by
  dsimp
  refine Prod.ext (Subtype.ext ?_) (LinearMap.ext fun w ↦ ?_)
  · rw [splitCoordinates_fst, LinearEquiv.coe_smulTopCongr_apply, splitCoordinates_fst, map_smul]
  · simp only [splitCoordinates_snd_apply, LinearEquiv.dualMap_apply]
    have he := H.form.isometryGroup_map_app e v
      (((e : V ≃ₗ[F × F] V).smulTopCongr F (1, 0)).symm w)
    rw [← LinearEquiv.coe_smulTopCongr_apply, LinearEquiv.apply_symm_apply] at he
    exact congrArg Prod.fst he

/-- The isometry group of a split signed Hermitian form is the general linear group of its first
idempotent summand. The map restricts an isometry to that summand. -/
noncomputable def splitIsometryGroupEquiv :
    H.form.isometryGroup ≃* (splitFst F V ≃ₗ[F] splitFst F V) where
  toFun e := (e : V ≃ₗ[F × F] V).smulTopCongr F (1, 0)
  invFun g := ⟨H.splitIsometry g, H.splitIsometry_mem_isometryGroup g⟩
  left_inv e := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply H.splitCoordinates.injective
    rw [H.splitCoordinates_splitIsometry]
    exact (H.splitCoordinates_isometry e v).symm
  right_inv g := by
    apply LinearEquiv.ext
    intro x
    have hx := mem_splitFst_iff.mp x.property
    have hx' : (H.splitCoordinates (x : V)).1 = x :=
      Subtype.ext ((H.splitCoordinates_fst x).trans hx)
    apply Subtype.ext
    rw [LinearEquiv.coe_smulTopCongr_apply]
    have h := congrArg (fun z : splitFst F V × Dual F (splitFst F V) ↦ (z.1 : V))
      (H.splitCoordinates_splitIsometry g (x : V))
    simpa only [splitCoordinates_fst, hx', ← map_smul, hx] using h
  map_mul' e f := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp only [LinearEquiv.coe_smulTopCongr_apply, mul_apply_eq_comp]
    rfl

/-- The general linear automorphism is the restriction of the isometry to the first summand. -/
@[simp]
theorem coe_splitIsometryGroupEquiv_apply (e : H.form.isometryGroup) (x : splitFst F V) :
    (H.splitIsometryGroupEquiv e x : V) = (e : V ≃ₗ[F × F] V) x := by
  exact LinearEquiv.coe_smulTopCongr_apply (e : V ≃ₗ[F × F] V) (1, 0) x

/-- In split coordinates, the inverse of the restriction isomorphism acts by `g` on vectors and
by the dual of `g.symm` on functionals. -/
@[simp]
theorem splitCoordinates_splitIsometryGroupEquiv_symm_apply
    (g : splitFst F V ≃ₗ[F] splitFst F V) (v : V) :
    H.splitCoordinates ((H.splitIsometryGroupEquiv.symm g : V ≃ₗ[F × F] V) v) =
      (g ((H.splitCoordinates v).1), g.symm.dualMap ((H.splitCoordinates v).2)) := by
  exact H.splitCoordinates_splitIsometry g v

end TauCeti.SignedHermitianSpace
