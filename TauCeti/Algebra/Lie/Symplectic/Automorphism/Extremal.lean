/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Automorphism.RankOne
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Extremal elements of the symplectic Lie algebra

Over a field of characteristic different from two, the nonzero extremal elements of a
symplectic Lie algebra are precisely the nonzero scalar multiples of its transvection
generators. Here extremality means that `[X,[X,Y]]` is proportional to `X` for every `Y`.
A Lie equivalence therefore carries each such rank-one line to another. Neither the
recognition theorem nor its application to Lie equivalences uses finite-dimensionality.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
attribute [local instance 100] LieRing.ofAssociativeRing

section Ring
variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

private theorem pairing_apply_apply_eq_zero (hB : B.IsAlt) {X : Module.End K V}
    (hX : X ∈ B.skewAdjointSubmodule) (v : V) : B v (X (X v)) = 0 := by
  have h : B (X v) (X v) = -B v (X (X v)) := by
    simpa using (mem_skewAdjointSubmodule (B := B) X).mp hX v (X v)
  rw [hB.self_eq_zero] at h
  exact neg_eq_zero.mp h.symm

variable [IsDomain K] [Module.IsTorsionFree K V]

-- Evaluation at v determines the scalar in the extremal identity.
private theorem double_bracket_eq_pairing_smul (hB : B.IsAlt) {X : Module.End K V}
    (hX : X ∈ B.skewAdjointSubmodule) (v : V)
    (h : ∃ c : K, ⁅X, ⁅X, (B.flip v).smulRight v⁆⁆ = c • X) :
    ⁅X, ⁅X, (B.flip v).smulRight v⁆⁆ = (2 * B v (X v)) • X := by
  by_cases hv : X v = 0
  · rw [lie_lie_smulRight_flip_of_apply_apply_eq_zero X hX v (by simp [hv]), hv]
    simp
  obtain ⟨c, hc⟩ := h
  refine hc.trans (congrArg (· • X) (smul_left_injective K hv ?_))
  have hval := (LinearMap.congr_fun hc v).symm
  rw [lie_lie_smulRight_flip_apply X hX, pairing_apply_apply_eq_zero hB hX,
    hB.self_eq_zero] at hval
  simpa only [LinearMap.smul_apply, zero_smul, zero_add, add_zero, two_mul, add_smul] using hval

end Ring

variable {K V : Type*} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
    {B : BilinForm K V}

-- At u with B(u,Xu) ≠ 0, evaluate the identities for the generators at u and at Xu.
-- The second evaluation removes a factor of three, including in characteristic three.
private theorem apply_apply_eq_zero_of_extremal (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {X : Module.End K V} (hX : X ∈ B.skewAdjointSubmodule) {u : V}
    (ht : B u (X u) ≠ 0)
    (h : ∀ v, ⁅X, ⁅X, (B.flip v).smulRight v⁆⁆ = (2 * B v (X v)) • X) : X (X u) = 0 := by
  let y := X u
  let w := X y
  let t := B u y
  let s := B y w
  have huω : B y u = -t := (hB.neg_eq u y).symm
  have hwω : B w y = -s := (hB.neg_eq y w).symm
  have huωw : B u w = 0 := pairing_apply_apply_eq_zero hB hX u
  have hval (v : V) :
      B v w • u + B v y • y + (B v y • y + B v u • w) = (2 * t) • X v := by
    simpa only [lie_lie_smulRight_flip_apply X hX, LinearMap.smul_apply] using
      LinearMap.congr_fun (h u) v
  have hw : (3 * t) • w = s • u := by
    have he := hval y
    rw [huω, hB.self_eq_zero, zero_smul, add_zero, zero_add] at he
    change s • u + -t • w = (2 * t) • w at he
    linear_combination (norm := module) -he
  have hs : s = 0 := by
    have he := congrArg (fun z ↦ B z y) hw
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hwω] at he
    change 3 * t * -s = s * t at he
    by_contra hs
    have h2 : (2 : K) ≠ 0 := NeZero.ne _
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) ht) hs
    linear_combination -he
  have hXw : X w = 0 := by
    have hwu : B w u = 0 := by rw [← hB.neg_eq u w, huωw, neg_zero]
    have he := hval w
    simp only [hB.self_eq_zero w, hwω, hs, neg_zero, hwu, zero_smul, zero_add] at he
    exact (smul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (NeZero.ne _) ht)
  have he := h y
  rw [lie_lie_smulRight_flip_of_apply_apply_eq_zero X hX y hXw] at he
  change (2 : K) • (B.flip w).smulRight w = (2 * s) • X at he
  rw [hs, mul_zero, zero_smul] at he
  have hN := (smul_eq_zero.mp he).resolve_left (NeZero.ne (2 : K))
  exact (smulRight_apply_eq_zero_iff.mp hN).elim
    (separatingRight_iff_linear_flip_nontrivial.mp hnd.2 w) (fun hw ↦ hw)

/-- A nonzero symplectic endomorphism is extremal exactly when it is a nonzero scalar multiple
of the infinitesimal transvection associated to a nonzero vector. -/
theorem extremal_iff_exists_smul_transvectionGenerator (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (X : skewAdjointLieSubalgebra B) (h0 : X ≠ 0) :
    (∀ Y : skewAdjointLieSubalgebra B, ∃ c : K, ⁅X, ⁅X, Y⁆⁆ = c • X) ↔
      ∃ (c : K) (u : V), c ≠ 0 ∧ u ≠ 0 ∧ X = c • transvectionGenerator hB u := by
  constructor
  · intro hX
    let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
    have hpair : B.compLeft X.val ≠ 0 := by
      intro he
      apply h0
      apply Subtype.ext
      change X.val = (0 : Module.End K V)
      apply B.compLeft_injective hnd
      rw [he]
      ext x y
      change 0 = (B (0 : V)) y
      simp
    obtain ⟨u, hu'⟩ := exists_bilinForm_self_ne_zero hpair (by
      constructor
      intro v z
      change B (X.val v) z = B (X.val z) v
      rw [(mem_skewAdjointSubmodule (B := B) X.val).mp X.property v z]
      simpa only [Pi.neg_apply, map_neg] using hB.neg_eq v (X.val z))
    have hu : B u (X.val u) ≠ 0 := by
      simpa only [compLeft_apply, ← hB.neg_eq (X.val u) u, neg_ne_zero] using hu'
    have h (v : V) := double_bracket_eq_pairing_smul hB X.property v (by
      obtain ⟨c, hc⟩ := hX (transvectionGenerator hB v)
      exact ⟨c, congrArg Subtype.val hc⟩)
    have he := h u
    rw [lie_lie_smulRight_flip_of_apply_apply_eq_zero X.val X.property u
      (apply_apply_eq_zero_of_extremal hB hnd X.property hu h), mul_smul] at he
    have hN := smul_right_injective (Module.End K V) (NeZero.ne (2 : K)) he
    refine ⟨(B u (X.val u))⁻¹, X.val u, inv_ne_zero hu, fun hz ↦ hu (by simp [hz]), ?_⟩
    apply Subtype.ext
    change X.val = (B u (X.val u))⁻¹ • (B.flip (X.val u)).smulRight (X.val u)
    rw [hN, inv_smul_smul₀ hu]
  · rintro ⟨c, u, -, -, rfl⟩ Y
    refine ⟨c * (-(2 : K) * B (Y.val u) u), Subtype.ext ?_⟩
    change ⁅c • (B.flip u).smulRight u, ⁅c • (B.flip u).smulRight u, Y.val⁆⁆ = _
    simp only [smul_lie, lie_smul, lie_lie_smulRight_flip_eq_smul (hB.self_eq_zero u), smul_smul]
    change (c * (c * _) : K) • _ = ((c * _) * c) • _
    ring_nf

variable {W : Type*} [AddCommGroup W] [Module K W] {C : BilinForm K W}

/-- A Lie equivalence sends each nonzero transvection generator to a nonzero multiple of one. -/
theorem exists_map_transvectionGenerator_eq_smul (hB : B.IsAlt) (hC : C.IsAlt)
    (hndC : C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C)
    {v : V} (hv : B.flip v ≠ 0) :
    ∃ (d : K) (w : W), d ≠ 0 ∧ w ≠ 0 ∧
      f (transvectionGenerator hB v) = d • transvectionGenerator hC w := by
  have hv0 : v ≠ 0 := fun hz ↦ hv (by simp [hz])
  have hN : transvectionGenerator hB v ≠ 0 := by
    intro h
    have he : (B.flip v).smulRight v = 0 := congrArg Subtype.val h
    exact (smulRight_apply_eq_zero_iff.mp he).elim hv hv0
  apply (extremal_iff_exists_smul_transvectionGenerator hC hndC (f (transvectionGenerator hB v))
    (fun h ↦ hN (f.injective (h.trans f.map_zero.symm)))).mp
  intro Y
  let Z := f.symm Y
  let c := -(2 : K) * B (Z.val v) v
  have h : ⁅transvectionGenerator hB v, ⁅transvectionGenerator hB v, Z⁆⁆ =
      c • transvectionGenerator hB v :=
    Subtype.ext (lie_lie_smulRight_flip_eq_smul (hB.self_eq_zero v) Z.val)
  refine ⟨c, ?_⟩
  simpa only [LieEquiv.map_lie, map_smul, Z, LieEquiv.apply_symm_apply] using congrArg f h

/-- The transported endomorphism of any scalar multiple of a transvection generator squares to
zero. This also covers generators in the radical of the source form. -/
theorem map_smul_transvectionGenerator_mul_self (hB : B.IsAlt) (hC : C.IsAlt)
    (hndC : C.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra C)
    (c : K) (v : V) :
    (f (c • transvectionGenerator hB v)).val * (f (c • transvectionGenerator hB v)).val = 0 := by
  by_cases hv : B.flip v = 0
  · have hN : transvectionGenerator hB v = 0 := Subtype.ext (by simp [hv])
    simp [hN]
  obtain ⟨d, w, -, -, H⟩ := exists_map_transvectionGenerator_eq_smul hB hC hndC f hv
  rw [map_smul, H]
  change (c • d • (C.flip w).smulRight w) * (c • d • (C.flip w).smulRight w) = 0
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smulRight_flip_mul_self hC]
  simp

end LinearMap.BilinForm
