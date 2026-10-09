/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Coefficients and lifts for homogeneous localizations

For a graded ring `A`, an element `f : A` and a ring homomorphism `φ : A →+* R` with `φ f` a unit,
`HomogeneousLocalization.Away.lift 𝒜 φ hf` is the ring homomorphism `A_{(f)} →+* R` sending
`a / fⁿ` to `φ a / (φ f)ⁿ`: the restriction to the degree-zero part `A_{(f)}` of the lift
`A_f →+* R` of `φ`. Geometrically, when `A` is `ℕ`-graded and `f` is homogeneous of positive
degree, `Spec A_{(f)}` is the standard affine chart `D₊(f)` of `Proj A`, and `Spec` of `lift` is
the morphism `Spec R ⟶ D₊(f) ⊆ Proj A` given by the "homogeneous coordinates" `φ`.

For a graded algebra over a coefficient ring, homogeneous localization inherits the
coefficient algebra structure, and fractions with a fixed homogeneous denominator depend
linearly on their numerator. This permits scalar extension of the homogeneous affine charts.

The file also records that the restriction map `A_{(f)} →+* A_{(fg)}` is injective when `g` is a
nonzerodivisor of `A`, that an element of `A_{(f)}` whose restriction to `A_{(fg)}` extends to
`A_{(g)}` lies in the degree-zero part `𝒜 0` when `[f, g]` is a regular sequence, and that a
homogeneous localization is reduced whenever the corresponding localization is.

## Main definitions

* `HomogeneousLocalization.Away.mkLinearMap`: the linear numerator map for a fixed denominator.
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
* `HomogeneousLocalization.awayMap_injective`: the restriction `awayMap` from `A_{(f)}` to
  `A_{(fg)}` is injective when `g` is a nonzerodivisor of `A`.
* `HomogeneousLocalization.fromZeroRingHom_injective`: the degree-zero part `𝒜 0` embeds in a
  homogeneous localization at nonzerodivisors.
* `HomogeneousLocalization.Away.mem_range_fromZeroRingHom_of_awayMap_eq`: for a regular sequence
  `[f, g]` of homogeneous elements, elements of `A_{(f)}` and `A_{(g)}` with the same image in
  `A_{(fg)}` come from `𝒜 0`.
* `HomogeneousLocalization.isReduced`: a homogeneous localization is reduced whenever the
  corresponding localization is, in particular for any reduced graded ring.

## Provenance

`HomogeneousLocalization.isReduced` is adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0) at commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/ForMathlib/ProjIntegral.lean`, declaration
`AlgebraicGeometry.Proj.isReduced_away`, which treats `Away 𝒜 f` for an `ℕ`-graded domain; here
the localization is at any submonoid and only its reducedness is assumed.
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

/-- Changing the value ring of homogeneous coordinates commutes with the chart lift. -/
@[simp]
theorem _root_.RingHom.comp_homogeneousLocalizationAwayLift {S : Type*} [CommRing S]
    (ψ : R →+* S) (φ : A →+* R)
    {f : A} (hf : IsUnit (φ f)) :
    ψ.comp (Away.lift 𝒜 φ hf) = Away.lift 𝒜 (ψ.comp φ) (hf.map ψ) := by
  unfold Away.lift
  rw [← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp [IsLocalization.Away.lift_eq]

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

/-- The restriction `awayMap : A_{(f)} →+* A_{(fg)}`, `a / fⁿ ↦ a gⁿ / (fg)ⁿ`, is injective when
`g` is a nonzerodivisor of `A`. -/
theorem awayMap_injective {e : ι} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (h : g ∈ nonZeroDivisors A) : Function.Injective (awayMap 𝒜 hg hx) := by
  intro z w hzw
  rw [ext_iff_val, val_awayMap, val_awayMap] at hzw
  -- `awayMap` restricts `A_f →+* A_{fg}`, which is injective if it kills no nonzero `a / 1`
  refine val_injective _ <| IsLocalization.injective_of_map_algebraMap_zero (M := .powers f) _ _
    (fun a ha ↦ ?_) hzw
  -- the image of `a / 1` in `A_{fg}` vanishes, so `(fg)ᵏ a = 0` for some `k`
  rw [IsLocalization.Away.lift_eq] at ha
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x (ha.trans (map_zero _).symm)
  -- as `g` is a nonzerodivisor, `fᵏ a = 0`, so `a / 1` vanishes in `A_f`
  rw [mul_zero, hx, mul_pow, mul_right_comm,
    mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem h k)] at hk
  exact (IsLocalization.map_eq_zero_iff (.powers f) _ a).mpr
    ⟨⟨f ^ k, pow_mem (Submonoid.mem_powers f) k⟩, hk⟩

variable (𝒜) in
/-- A homogeneous localization at `x` is reduced whenever the localization at `x` is reduced; in
particular, it is reduced whenever the graded ring is. -/
instance isReduced (x : Submonoid A) [IsReduced (Localization x)] :
    IsReduced (HomogeneousLocalization 𝒜 x) :=
  isReduced_of_injective (algebraMap _ (Localization x)) (val_injective x)

/-- The homogeneous localization map is the restriction of the ordinary localization map. -/
@[simp]
theorem val_map {ι A B σ τ : Type*} [AddCommMonoid ι] [DecidableEq ι]
    [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ι → σ} {ℬ : ι → τ}
    [GradedRing 𝒜] [GradedRing ℬ] (g : 𝒜 →+*ᵍ ℬ)
    {P : Submonoid A} {Q : Submonoid B} (h : P ≤ Q.comap g)
    (z : HomogeneousLocalization 𝒜 P) :
    (map g h z).val = IsLocalization.map (Localization Q) g.toRingHom h z.val := by
  obtain ⟨c, rfl⟩ := mk_surjective z
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk']
  exact (IsLocalization.map_mk' (S := Localization P) (Q := Localization Q) (g := g.toRingHom)
    (M := P) (T := Q) h (c.num : A) ⟨c.den, c.den_mem⟩).symm

/-- The degree-zero coefficient map sends `a` to the ordinary fraction `a/1`. -/
@[simp]
theorem val_fromZeroRingHom {ι A σ : Type*} [AddCommMonoid ι] [DecidableEq ι]
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
    [GradedRing 𝒜] (P : Submonoid A) (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 P a).val = algebraMap A (Localization P) a :=
  Localization.mk_one_eq_algebraMap _

/-- The degree-zero coefficient map `𝒜 0 → A_{(P)}` is injective when `P` consists of
nonzerodivisors. -/
theorem fromZeroRingHom_injective {ι A σ : Type*} [AddCommMonoid ι] [DecidableEq ι]
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
    {P : Submonoid A} (hP : P ≤ nonZeroDivisors A) :
    Function.Injective (fromZeroRingHom 𝒜 P) := fun a b hab ↦ by
  have := congr(val $hab)
  rw [val_fromZeroRingHom, val_fromZeroRingHom] at this
  exact Subtype.val_injective (IsLocalization.injective _ hP this)

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (P : Submonoid A)

/-- Homogeneous localization of a graded algebra is an algebra over its coefficient ring. -/
instance algebra : Algebra R (HomogeneousLocalization 𝒜 P) where
  algebraMap := (fromZeroRingHom 𝒜 P).comp (algebraMap R (𝒜 0))
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    apply val_injective P
    simp only [val_smul, Algebra.smul_def, val_mul, RingHom.comp_apply,
      val_fromZeroRingHom, SetLike.GradeZero.coe_algebraMap]
    rw [← IsScalarTower.algebraMap_apply R A (Localization P)]

/-- The coefficient map is the composite through the degree-zero part. -/
theorem algebraMap_eq_comp :
    algebraMap R (HomogeneousLocalization 𝒜 P) =
      (fromZeroRingHom 𝒜 P).comp (algebraMap R (𝒜 0)) := (rfl)

/-- Forgetting homogeneity respects coefficients. -/
@[simp]
theorem val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 P) r).val =
      algebraMap R (Localization P) r := by
  rw [algebraMap_eq_comp, RingHom.comp_apply, val_fromZeroRingHom]
  simp only [SetLike.GradeZero.coe_algebraMap,
    ← IsScalarTower.algebraMap_apply R A (Localization P)]

/-- The coefficient action factors through homogeneous localization into ordinary localization. -/
instance isScalarTower :
    IsScalarTower R (HomogeneousLocalization 𝒜 P) (Localization P) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := HomogeneousLocalization 𝒜 P)
    (A := Localization P) (by
    ext r
    exact (val_algebraMap 𝒜 P r).symm)

variable {𝒜}

/-- Fractions with a fixed homogeneous denominator depend linearly on the numerator. -/
noncomputable def Away.mkLinearMap {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) :
    𝒜 (n • d) →ₗ[R] Away 𝒜 f where
  toFun a := Away.mk 𝒜 hf n a a.2
  map_add' a b := by
    apply val_injective
    simp only [Away.val_mk, val_add, Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' r a := by
    apply val_injective
    simp only [Away.val_mk, val_smul, Submodule.coe_smul]
    exact (Localization.smul_mk (S := Submonoid.powers f) r (a : A) _).symm

/-- The linear numerator map forms the homogeneous fraction with the chosen denominator. -/
@[simp]
theorem Away.mkLinearMap_apply {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ)
    (a : 𝒜 (n • d)) : Away.mkLinearMap (𝒜 := 𝒜) hf n a = Away.mk 𝒜 hf n a a.2 := (rfl)

end HomogeneousLocalization

namespace HomogeneousLocalization

variable {ι A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [AddCancelCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- Let `f` and `g` be homogeneous elements forming a regular sequence `[f, g]` in `A`. If
`z ∈ A_{(f)}` and `w ∈ A_{(g)}` have the same image in `A_{(fg)}`, then `z` lies in the degree-zero
part `𝒜 0`.

Geometrically, a section of `Proj A` over `D₊(f) ∪ D₊(g)` comes from `𝒜 0`. -/
theorem Away.mem_range_fromZeroRingHom_of_awayMap_eq {d e : ι} {f g : A} (hf : f ∈ 𝒜 d)
    (hg : g ∈ 𝒜 e) (hfg : RingTheory.Sequence.IsWeaklyRegular A [f, g]) {z : Away 𝒜 f}
    {w : Away 𝒜 g} (h : awayMap 𝒜 hg rfl z = awayMap 𝒜 hf (mul_comm f g) w) :
    z ∈ (fromZeroRingHom 𝒜 (.powers f)).range := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  obtain ⟨k, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hg w
  have hf₀ := (RingTheory.Sequence.isWeaklyRegular_pair_iff.mp hfg).1
  -- in `A_{fg}`, `a gⁿ / (fg)ⁿ = b fᵏ / (fg)ᵏ`, so `(fg)ᴺ (fg)ᵏ a gⁿ = (fg)ᴺ (fg)ⁿ b fᵏ` for
  -- some `N`
  have h' := congr(val $h)
  rw [awayMap_mk, awayMap_mk, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists] at h'
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := h'
  -- cancelling `fᴺ⁺ᵏ`, `gᴺ⁺ᵏ⁺ⁿ a = fⁿ gᴺ⁺ⁿ b`, so `fⁿ` divides `a`
  have hdvd : f ^ n ∣ g ^ (N + k + n) * a := by
    refine ⟨g ^ (N + n) * b, sub_eq_zero.mp
      ((mem_nonZeroDivisors_iff_right.mp (pow_mem hf₀ (N + k))) _ ?_)⟩
    rw [sub_mul, sub_eq_zero]
    calc _ = (f * g) ^ N * ((f * g) ^ k * (a * g ^ n)) := by ring
      _ = (f * g) ^ N * ((f * g) ^ n * (b * f ^ k)) := hN
      _ = _ := by ring
  obtain ⟨c, hc⟩ := hfg.pow_dvd_of_pow_dvd_pow_mul hdvd
  -- comparing the components of degree `n • d`, `a = fⁿ c₀` for the degree-zero part `c₀` of `c`
  have hc₀ : a = f ^ n * (DirectSum.decompose 𝒜 c 0 : A) := by
    rw [← DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (SetLike.pow_mem_graded n hf), add_zero,
      ← hc, DirectSum.decompose_of_mem_same 𝒜 ha]
  refine ⟨DirectSum.decompose 𝒜 c 0, val_injective _ ?_⟩
  rw [val_fromZeroRingHom, Away.val_mk, hc₀, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

end HomogeneousLocalization
