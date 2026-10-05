/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Lifting homogeneous localizations away from an element

For a graded ring `A`, an element `f : A` and a ring homomorphism `φ : A →+* R` with `φ f` a unit,
`HomogeneousLocalization.Away.lift 𝒜 φ hf` is the ring homomorphism `A_{(f)} →+* R` sending
`a / fⁿ` to `φ a / (φ f)ⁿ`: the restriction to the degree-zero part `A_{(f)}` of the lift
`A_f →+* R` of `φ`. Geometrically, when `A` is `ℕ`-graded and `f` is homogeneous of positive
degree, `Spec A_{(f)}` is the standard affine chart `D₊(f)` of `Proj A`, and `Spec` of `lift` is
the morphism `Spec R ⟶ D₊(f) ⊆ Proj A` given by the "homogeneous coordinates" `φ`.

## Main definitions

* `HomogeneousLocalization.Away.lift`: the ring homomorphism `A_{(f)} →+* R` induced by `φ`.

## Main results

* `HomogeneousLocalization.Away.lift_mk`: `lift` sends `a / fⁿ` to `φ a * ((φ f)ⁿ)⁻¹`.
* `HomogeneousLocalization.Away.lift_algebraMap`: `lift` restricts to `φ` on the degree-zero
  part `𝒜 0`.
* `HomogeneousLocalization.Away.lift_comp_awayMap`: `lift` is compatible with the restriction
  `awayMap` from `A_{(f)}` to `A_{(fg)}`.
* `HomogeneousLocalization.Away.lift_comp_map`: `lift` is compatible with the map induced by a
  graded ring homomorphism.
* `HomogeneousLocalization.Away.lift_eq_of_forall_mem`: rescaling the homogeneous coordinates,
  so that `ψ a = cⁿ φ a` on the degree-`n` part, does not change `lift`.
-/

public section

namespace HomogeneousLocalization

variable {ι A B R σ τ : Type*} [CommRing A] [CommRing B] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B] [AddCommMonoid ι] [DecidableEq ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

variable (𝒜) in
/-- The ring homomorphism `A_{(f)} →+* R`, `a / fⁿ ↦ φ a / (φ f)ⁿ`, induced by a ring
homomorphism `φ : A →+* R` inverting `f`: the restriction of the lift `A_f →+* R` of `φ` to the
degree-zero part `A_{(f)}` of the localization. -/
noncomputable def Away.lift (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) : Away 𝒜 f →+* R :=
  (IsLocalization.Away.lift f hf).comp (algebraMap (Away 𝒜 f) (Localization.Away f))

private theorem Away.lift_apply (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) (z : Away 𝒜 f) :
    Away.lift 𝒜 φ hf z = IsLocalization.Away.lift f hf z.val :=
  (rfl)

/-- `Away.lift` sends `a / fⁿ` to `φ a / (φ f)ⁿ`. -/
@[simp]
theorem Away.lift_mk (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) {d : ι} (hfd : f ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    Away.lift 𝒜 φ hf (Away.mk 𝒜 hfd n a ha) = φ a * ↑(hf.unit ^ n)⁻¹ := by
  have hfn : φ (f ^ n) = ↑(hf.unit ^ n) := by
    rw [map_pow, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [Away.lift_apply, Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec, mul_left_comm, hfn, Units.mul_inv, mul_one]

/-- `Away.lift` restricts to `φ` on the degree-zero part `𝒜 0`. -/
@[simp]
theorem Away.lift_algebraMap (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) (a : 𝒜 0) :
    Away.lift 𝒜 φ hf (algebraMap (𝒜 0) (Away 𝒜 f) a) = φ a := by
  rw [Away.lift_apply, ← algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝒜 0) A, IsLocalization.Away.lift_eq,
    SetLike.GradeZero.algebraMap_apply]

/-- `Away.lift` is compatible with the restriction `awayMap : A_{(f)} →+* A_{(fg)}`. -/
theorem Away.lift_comp_awayMap (φ : A →+* R) {e : ι} {f g x : A} (hg : g ∈ 𝒜 e)
    (hx : x = f * g) (hφx : IsUnit (φ x)) (hφf : IsUnit (φ f)) :
    (Away.lift 𝒜 φ hφx).comp (awayMap 𝒜 hg hx) = Away.lift 𝒜 φ hφf := by
  ext z
  rw [RingHom.comp_apply, Away.lift_apply, Away.lift_apply, val_awayMap, ← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a ↦ ?_)
  simp [IsLocalization.Away.lift_eq]

/-- `Away.lift` is compatible with the map `A_{(s)} →+* B_{(F s)}` induced by a graded ring
homomorphism `F`. -/
@[simp]
theorem Away.lift_comp_map (φ : B →+* R) (F : 𝒜 →+*ᵍ ℬ) {s : A} (hs : IsUnit (φ (F s))) :
    (Away.lift ℬ φ hs).comp (Away.map F s) = Away.lift 𝒜 (φ.comp F.toRingHom) (f := s) hs := by
  ext z
  have hval : (Away.map F s z).val = Localization.awayMap F.toRingHom s z.val := by
    obtain ⟨c, rfl⟩ := mk_surjective z
    simp [Away.map, HomogeneousLocalization.map_mk, Localization.mk_eq_mk',
      IsLocalization.Away.map, IsLocalization.map_mk']
  rw [RingHom.comp_apply, Away.lift_apply, Away.lift_apply, hval, ← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
  simp [IsLocalization.Away.lift_eq, IsLocalization.Away.map]

/-- Rescaling homogeneous coordinates does not change `Away.lift`: if `ψ a = cⁿ φ a` for every
`a` of degree `n`, then `φ` and `ψ` induce the same homomorphism `A_{(f)} →+* R`. -/
theorem Away.lift_eq_of_forall_mem {𝒜 : ℕ → σ} [GradedRing 𝒜] (φ ψ : A →+* R) (c : Rˣ)
    (h : ∀ n, ∀ a ∈ 𝒜 n, ψ a = c ^ n * φ a) {f : A} {d : ℕ} (hfd : f ∈ 𝒜 d)
    (hψ : IsUnit (ψ f)) (hφ : IsUnit (φ f)) :
    Away.lift 𝒜 ψ hψ = Away.lift 𝒜 φ hφ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hfd z
  rw [Away.lift_mk, Away.lift_mk, Units.eq_mul_inv_iff_mul_eq, mul_assoc, mul_left_comm,
    Units.inv_mul_eq_iff_eq_mul]
  simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, h _ _ ha, h _ _ hfd, smul_eq_mul]
  ring

end HomogeneousLocalization
