/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.Injective
public import TauCeti.Algebra.Category.GradedModuleCat.Products
public import TauCeti.Algebra.Category.GradedModuleCat.RestrictScalars

/-!
# Graded coinduced modules and enough injectives

Let `A` be an internally `ℤ`-graded `k`-algebra. Given a `k`-module `V`, `A →ₗ[k] V` carries the
left `A`-action `(a • ψ)(b) = ψ(b * a)`. Maps supported on `A_{-p}` form the degree-`p` submodule
of the **graded coinduced module** associated to `V`, and their finite sums form a graded
`A`-submodule. Morphisms `M ⟶ (coinducedSingle 𝒜 V){n}` correspond `k`-linearly to `M_n →ₗ[k] V`
via evaluation at `1 ∈ A` and `f ↦ (x ↦ (b ↦ f((b • x)_n)))`, dual to `A{n}`; degreewise graded
products yield general coinduced graded modules.

When `V` is injective (or Baer) over `k`, its coinduced graded module is injective. In any module
universe `max uA v` at least that of `A`, embedding each homogeneous piece into an injective
`k`-module gives enough injectives when `k` is `max uA v`-small, and restricting the base ring of
`𝒜` to `ℤ` via `TauCeti.GradedModuleCat.restrictBaseEquivalence` transfers enough injectives to
`GradedModuleCat.{max uA v} 𝒜` over an arbitrary commutative base ring `k`.

## Main definitions

* `TauCeti.GradedModuleCat.coinducedSingle` and `TauCeti.GradedModuleCat.coinducedSingleApply`:
  the degree-zero coinduced graded `A`-module and its underlying `k`-linear evaluation map.
* `TauCeti.GradedModuleCat.coinducedSingleShiftLift`,
  `TauCeti.GradedModuleCat.coinducedSingleShiftHomEquiv`,
  `TauCeti.GradedModuleCat.coinducedSingleHomEquiv`, `TauCeti.GradedModuleCat.coinduced`, and
  `TauCeti.GradedModuleCat.coinducedHomEquiv`: lifts and universal properties of single and family
  coinduced graded modules.

## Main results

* `TauCeti.GradedModuleCat.injective_coinducedSingle_of_baer`,
  `TauCeti.GradedModuleCat.injective_coinducedSingle`,
  `TauCeti.GradedModuleCat.injective_coinduced_of_baer`, and
  `TauCeti.GradedModuleCat.injective_coinduced`: coinduced graded modules of Baer or injective
  `k`-modules are injective.
* `TauCeti.GradedModuleCat.enoughInjectives`: `GradedModuleCat.{max uA v} 𝒜` has enough injectives
  in every module universe at least that of `A`, over an arbitrary commutative base ring `k`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Sections 2.2 and 2.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v

section Single

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) (V : Type v) [AddCommGroup V] [Module k V]

/-- The `k`-linear maps `A →ₗ[k] V` vanishing on every homogeneous piece except `𝒜 (-p)`. -/
private def coinducedSinglePiece (p : ℤ) : Submodule k (A →ₗ[k] V) where
  carrier := {ψ | ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ≠ -p → ψ b = 0}
  zero_mem' _ _ _ _ := rfl
  add_mem' h₁ h₂ q b hb hq := by simp [h₁ q b hb hq, h₂ q b hb hq]
  smul_mem' c ψ hψ q b hb hq := by simp [hψ q b hb hq]

@[simp]
private theorem mem_coinducedSinglePiece_iff (p : ℤ) (ψ : A →ₗ[k] V) :
    ψ ∈ coinducedSinglePiece 𝒜 V p ↔ ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ≠ -p → ψ b = 0 := Iff.rfl

/-- Finite sums of homogeneous coinduced functionals inside `A →ₗ[k] V`. -/
private def coinducedSingleCarrier : Submodule k (A →ₗ[k] V) :=
  LinearMap.range (DirectSum.coeLinearMap (coinducedSinglePiece 𝒜 V))

private theorem coinducedSinglePiece_le_carrier (p : ℤ) :
    coinducedSinglePiece 𝒜 V p ≤ coinducedSingleCarrier 𝒜 V := fun ψ hψ ↦
  ⟨DirectSum.lof k ℤ (fun q ↦ coinducedSinglePiece 𝒜 V q) p ⟨ψ, hψ⟩,
    DirectSum.coeLinearMap_lof (coinducedSinglePiece 𝒜 V) p ⟨ψ, hψ⟩⟩

variable [GradedAlgebra 𝒜]

private theorem coinducedSingle_recompose_injective :
    Function.Injective (DirectSum.coeLinearMap (coinducedSinglePiece 𝒜 V)) := by
  intro x y hxy
  suffices hzero : x - y = 0 from sub_eq_zero.mp hzero
  have hz : DirectSum.coeLinearMap (coinducedSinglePiece 𝒜 V) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  set z := x - y
  refine DirectSum.ext fun p ↦ Subtype.ext <|
    (InternalGrading.ofDecomposition 𝒜).linearMap_ext fun q b hb ↦ ?_
  rw [InternalGrading.ofDecomposition_piece] at hb
  rw [DirectSum.zero_apply, Submodule.coe_zero, LinearMap.zero_apply]
  by_cases hqp : q = -p
  · classical
    have hsum : ∑ r ∈ z.support, (z r : A →ₗ[k] V) b = 0 := by
      have hzb := congrArg (fun f : A →ₗ[k] V ↦ f b) hz
      rw [← z.sum_support_of, map_sum, LinearMap.sum_apply, LinearMap.zero_apply] at hzb
      simpa only [DirectSum.coeLinearMap_of] using hzb
    rw [← hsum]
    refine (Finset.sum_eq_single p (fun r _ _ ↦ (z r).2 q b hb (by omega)) fun hp ↦ ?_).symm
    rw [DFinsupp.notMem_support_iff.mp hp, Submodule.coe_zero, LinearMap.zero_apply]
  · exact (z p).2 q b hb hqp

private def coinducedSingleEquiv :
    (⨁ p, coinducedSinglePiece 𝒜 V p) ≃ₗ[k] coinducedSingleCarrier 𝒜 V :=
  LinearEquiv.ofInjective (DirectSum.coeLinearMap (coinducedSinglePiece 𝒜 V))
    (coinducedSingle_recompose_injective 𝒜 V)

@[simp]
private theorem coinducedSingleEquiv_apply (x : ⨁ p, coinducedSinglePiece 𝒜 V p) :
    ((coinducedSingleEquiv 𝒜 V x : coinducedSingleCarrier 𝒜 V) : A →ₗ[k] V) =
      DirectSum.coeLinearMap (coinducedSinglePiece 𝒜 V) x :=
  LinearEquiv.ofInjective_apply _ _

private def coinducedSingleGrading : InternalGrading k (coinducedSingleCarrier 𝒜 V) ℤ :=
  (InternalGrading.ofDecomposition
    (DirectSum.summand k (fun p : ℤ ↦ coinducedSinglePiece 𝒜 V p))).map (coinducedSingleEquiv 𝒜 V)

private theorem mem_coinducedSingleGrading_piece_iff (p : ℤ) (ψ : coinducedSingleCarrier 𝒜 V) :
    ψ ∈ (coinducedSingleGrading 𝒜 V).piece p ↔
      ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ≠ -p → ψ.1 b = 0 := by
  rw [coinducedSingleGrading, InternalGrading.map_piece, InternalGrading.ofDecomposition_piece,
    DirectSum.summand_def]
  refine ⟨?_, fun hψ ↦ ?_⟩
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    simpa only [LinearEquiv.coe_coe, coinducedSingleEquiv_apply, DirectSum.coeLinearMap_lof] using
      (mem_coinducedSinglePiece_iff 𝒜 V p t.1).mp t.2
  · refine ⟨DirectSum.lof k ℤ (fun q ↦ coinducedSinglePiece 𝒜 V q) p ⟨ψ.1, hψ⟩, ⟨⟨ψ.1, hψ⟩, rfl⟩,
      Subtype.ext ?_⟩
    simp only [LinearEquiv.coe_coe, coinducedSingleEquiv_apply, DirectSum.coeLinearMap_lof]

/-- Right translation of the algebra argument on `A →ₗ[k] V`, bundled `k`-linearly in `a : A`. -/
private def coinducedActionLinear (ψ : A →ₗ[k] V) : A →ₗ[k] (A →ₗ[k] V) where
  toFun a := ψ.comp (LinearMap.mulRight k a)
  map_add' _ _ := LinearMap.ext fun _ ↦ by simp [mul_add]
  map_smul' _ _ := LinearMap.ext fun _ ↦ by simp

private theorem coinducedActionLinear_mem_piece {r p : ℤ} {a : A} (ha : a ∈ 𝒜 r)
    {ψ : A →ₗ[k] V} (hψ : ψ ∈ coinducedSinglePiece 𝒜 V p) :
    coinducedActionLinear V ψ a ∈ coinducedSinglePiece 𝒜 V (r + p) := fun q b hb _ ↦
  hψ (q + r) (b * a) (SetLike.GradedMul.mul_mem hb ha) (by omega)

private theorem coinducedActionLinear_mem_carrier (a : A) {ψ : A →ₗ[k] V}
    (hψ : ψ ∈ coinducedSingleCarrier 𝒜 V) :
    coinducedActionLinear V ψ a ∈ coinducedSingleCarrier 𝒜 V := by
  classical
  obtain ⟨y, rfl⟩ := hψ
  induction y using DirectSum.induction_on with
  | zero => simp [coinducedActionLinear]
  | add y z hy hz =>
    have hadd : coinducedActionLinear V (DirectSum.coeLinearMap _ y + DirectSum.coeLinearMap _ z)
        a = _ + _ := LinearMap.add_comp _ _ _
    rw [map_add, hadd]; exact (coinducedSingleCarrier 𝒜 V).add_mem hy hz
  | of p y =>
    rw [DirectSum.coeLinearMap_of, ← DirectSum.sum_support_decompose 𝒜 a, map_sum]
    exact (coinducedSingleCarrier 𝒜 V).sum_mem fun r _ ↦ coinducedSinglePiece_le_carrier 𝒜 V (r + p)
      (coinducedActionLinear_mem_piece 𝒜 V (DirectSum.decompose 𝒜 a r).2 y.2)

/-- The graded `𝒜`-module coinduced from a `k`-module `V` placed in degree zero. -/
def coinducedSingle : GradedModuleCat.{max uA v} 𝒜 := by
  let C := coinducedSingleCarrier 𝒜 V
  letI : SMul A C :=
    ⟨fun a ψ ↦ ⟨coinducedActionLinear V ψ.1 a, coinducedActionLinear_mem_carrier 𝒜 V a ψ.2⟩⟩
  have hsmul (a : A) (ψ : C) : (a • ψ).1 = coinducedActionLinear V ψ.1 a := rfl
  let extC {x y : C} (h : ∀ b, x.1 b = y.1 b) : x = y := Subtype.ext (LinearMap.ext h)
  letI : Module A C :=
    { one_smul := fun _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear]
      mul_smul := fun _ _ _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear, mul_assoc]
      smul_zero := fun _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear]
      smul_add := fun _ _ _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear]
      add_smul := fun _ _ _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear, mul_add]
      zero_smul := fun _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear] }
  letI : IsScalarTower k A C := ⟨fun _ _ _ ↦ extC fun _ ↦ by simp [hsmul, coinducedActionLinear]⟩
  let G := coinducedSingleGrading 𝒜 V
  letI : SetLike.GradedSMul 𝒜 G.piece :=
    ⟨fun {r p} a ψ ha hψ ↦ (mem_coinducedSingleGrading_piece_iff 𝒜 V (r + p) (a • ψ)).mpr
      (coinducedActionLinear_mem_piece 𝒜 V ha
        ((mem_coinducedSingleGrading_piece_iff 𝒜 V p ψ).mp hψ))⟩
  exact { carrier := C, grading := G }

variable {𝒜 V}

/-- The underlying `k`-linear functional `A →ₗ[k] V` of an element of `coinducedSingle`. -/
def coinducedSingleApply : coinducedSingle 𝒜 V →ₗ[k] (A →ₗ[k] V) :=
  (coinducedSingleCarrier 𝒜 V).subtype

/-- Internal carrier comparison keeping `coinducedSingle` sealed in public signatures. -/
private def toCoinducedSingle : coinducedSingleCarrier 𝒜 V ≃ₗ[k] coinducedSingle 𝒜 V :=
  LinearEquiv.refl k (coinducedSingleCarrier 𝒜 V)

@[simp]
private theorem coinducedSingleApply_toCoinducedSingle (y : coinducedSingleCarrier 𝒜 V) :
    coinducedSingleApply (toCoinducedSingle y) = y.1 := rfl

/-- Elements of `coinducedSingle` are determined by their underlying `k`-linear maps. -/
theorem coinducedSingleApply_injective :
    Function.Injective (coinducedSingleApply (𝒜 := 𝒜) (V := V)) := Submodule.subtype_injective _

/-- Two elements of `coinducedSingle` agree when they agree on every element of `A`. -/
@[ext]
theorem coinducedSingle_ext {x y : coinducedSingle 𝒜 V}
    (h : ∀ b : A, coinducedSingleApply x b = coinducedSingleApply y b) : x = y :=
  coinducedSingleApply_injective (LinearMap.ext h)

/-- Scalar multiplication on `coinducedSingle` multiplies the algebra argument on the right. -/
@[simp]
theorem coinducedSingleApply_smul (a : A) (x : coinducedSingle 𝒜 V) (b : A) :
    coinducedSingleApply (a • x) b = coinducedSingleApply x (b * a) := by
  rw [coinducedSingleApply]; rfl

/-- An element of `coinducedSingle` has degree `p` precisely when it vanishes outside `𝒜 (-p)`. -/
@[simp]
theorem mem_coinducedSingle_piece_iff (p : ℤ) (x : coinducedSingle 𝒜 V) :
    x ∈ (coinducedSingle 𝒜 V).grading.piece p ↔
      ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ≠ -p → coinducedSingleApply x b = 0 :=
  mem_coinducedSingleGrading_piece_iff 𝒜 V p x

omit [GradedAlgebra 𝒜] in
private def coinducedSingleShiftLiftLinear {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) : M →ₗ[k] (A →ₗ[k] V) where
  toFun x :=
    { toFun := fun b ↦ f (DirectSum.decompose M.grading.piece (b • x) n)
      map_add' := fun _ _ ↦ by rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply, map_add]
      map_smul' := fun _ _ ↦ by
        rw [RingHom.id_apply, smul_assoc, DirectSum.decompose_smul, DirectSum.smul_apply,
          map_smul] }
  map_add' _ _ := LinearMap.ext fun _ ↦ by
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [smul_add, DirectSum.decompose_add, DirectSum.add_apply, map_add]
  map_smul' c x := LinearMap.ext fun b ↦ by
    dsimp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
    rw [smul_comm b c x, DirectSum.decompose_smul, DirectSum.smul_apply, map_smul]

omit [GradedAlgebra 𝒜] in
@[simp]
private theorem coinducedSingleShiftLiftLinear_apply {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) (x : M) (b : A) :
    coinducedSingleShiftLiftLinear n f x b = f (DirectSum.decompose M.grading.piece (b • x) n) :=
  rfl

omit [GradedAlgebra 𝒜] in
private theorem coinducedSingleShiftLiftLinear_mem_piece {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) {p : ℤ} {x : M} (hx : x ∈ M.grading.piece p) :
    coinducedSingleShiftLiftLinear n f x ∈ coinducedSinglePiece 𝒜 V (p - n) := fun q b hb _ ↦ by
  have hbx : b • x ∈ M.grading.piece (q + p) := SetLike.GradedSMul.smul_mem hb hx
  have hdec : DirectSum.decompose M.grading.piece (b • x) n = 0 :=
    Subtype.ext (DirectSum.decompose_of_mem_ne M.grading.piece hbx (by omega))
  rw [coinducedSingleShiftLiftLinear_apply, hdec, map_zero]

omit [GradedAlgebra 𝒜] in
private theorem coinducedSingleShiftLiftLinear_mem_carrier {M : GradedModuleCat.{max uA v} 𝒜}
    (n : ℤ) (f : M.grading.piece n →ₗ[k] V) (x : M) :
    coinducedSingleShiftLiftLinear n f x ∈ coinducedSingleCarrier 𝒜 V := by
  classical
  rw [← DirectSum.sum_support_decompose M.grading.piece x, map_sum]
  exact (coinducedSingleCarrier 𝒜 V).sum_mem fun p _ ↦ coinducedSinglePiece_le_carrier 𝒜 V (p - n)
    (coinducedSingleShiftLiftLinear_mem_piece n f (DirectSum.decompose M.grading.piece x p).2)

/-- Lift a `k`-linear map on `M_n` to a graded morphism `M ⟶ (coinducedSingle 𝒜 V).shiftObj n`. -/
def coinducedSingleShiftLift {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) : M ⟶ (coinducedSingle 𝒜 V).shiftObj n :=
  let φ : M →ₗ[k] coinducedSingle 𝒜 V :=
    (toCoinducedSingle (𝒜 := 𝒜) (V := V)).toLinearMap.comp
      ((coinducedSingleShiftLiftLinear n f).codRestrict (coinducedSingleCarrier 𝒜 V)
        (coinducedSingleShiftLiftLinear_mem_carrier n f))
  ofHom
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun a x ↦ coinducedSingle_ext fun b ↦ by
        simp only [RingHom.id_apply, coinducedSingleApply_smul, φ, LinearMap.comp_apply,
          LinearEquiv.coe_coe, coinducedSingleApply_toCoinducedSingle,
          LinearMap.codRestrict_apply, coinducedSingleShiftLiftLinear_apply, mul_smul] }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      rw [add_zero, mem_shiftObj_piece_iff, mem_coinducedSingle_piece_iff]
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
        coinducedSingleApply_toCoinducedSingle, LinearMap.codRestrict_apply] using
        (mem_coinducedSinglePiece_iff 𝒜 V (p - n) _).mp
          (coinducedSingleShiftLiftLinear_mem_piece n f hx))

/-- Evaluating `coinducedSingleShiftLift n f` applies `f` to the degree-`n` part of `b • x`. -/
@[simp]
theorem coinducedSingleApply_coinducedSingleShiftLift {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) (x : M) (b : A) :
    (dsimp% only (coinducedSingleApply ((coinducedSingleShiftLift n f).hom x) b)) =
      f (DirectSum.decompose M.grading.piece (b • x) n) := by
  rw [coinducedSingleShiftLift]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coinducedSingleApply_toCoinducedSingle, LinearMap.codRestrict_apply,
    coinducedSingleShiftLiftLinear_apply]

/-- **Universal property of shifted coinduced modules.** Morphisms `M ⟶ (coinducedSingle 𝒜 V){n}`
correspond `k`-linearly to `k`-linear maps `M_n →ₗ[k] V`, via evaluation at `1 : A`. -/
def coinducedSingleShiftHomEquiv (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ) :
    (M ⟶ (coinducedSingle 𝒜 V).shiftObj n) ≃ₗ[k] (M.grading.piece n →ₗ[k] V) where
  toFun Ψ :=
    { toFun := fun x ↦ coinducedSingleApply (Ψ.hom x) 1
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun c x ↦ by
        rw [RingHom.id_apply, Submodule.coe_smul_of_tower, ← algebraMap_smul A c (x : M),
          Ψ.hom.map_smul, algebraMap_smul]
        simp }
  invFun := coinducedSingleShiftLift n
  left_inv Ψ := hom_ext <| M.grading.linearMap_ext fun p x hx ↦ coinducedSingleApply_injective <|
    (InternalGrading.ofDecomposition 𝒜).linearMap_ext fun q b hb ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hb
      rw [coinducedSingleApply_coinducedSingleShiftLift]
      have hbx_eq : coinducedSingleApply (Ψ.hom x) b = coinducedSingleApply (Ψ.hom (b • x)) 1 := by
        rw [Ψ.hom.map_smul, coinducedSingleApply_smul, one_mul]
      rw [hbx_eq]
      have hbx : b • x ∈ M.grading.piece (q + p) := SetLike.GradedSMul.smul_mem hb hx
      by_cases hqp : q + p = n
      · subst hqp; dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [DirectSum.decompose_of_mem_same M.grading.piece hbx]
      · have hdec : DirectSum.decompose M.grading.piece (b • x) n = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne M.grading.piece hbx hqp)
        have hΨ := map_mem Ψ hbx
        rw [mem_shiftObj_piece_iff, mem_coinducedSingle_piece_iff] at hΨ
        simp only [hdec, map_zero, hΨ 0 1 (SetLike.GradedOne.one_mem (A := 𝒜)) (by omega)]
  right_inv f := LinearMap.ext fun x ↦ by
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [coinducedSingleApply_coinducedSingleShiftLift, one_smul]
    exact congrArg f (Subtype.ext (DirectSum.decompose_of_mem_same M.grading.piece x.2))
  map_add' _ _ := LinearMap.ext fun _ ↦ by simp
  map_smul' _ _ := LinearMap.ext fun _ ↦ by simp

/-- The forward universal-property map evaluates at `1 : A`. -/
@[simp]
theorem coinducedSingleShiftHomEquiv_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ)
    (Ψ : M ⟶ (coinducedSingle 𝒜 V).shiftObj n) (x : M.grading.piece n) :
    coinducedSingleShiftHomEquiv M V n Ψ x = coinducedSingleApply (Ψ.hom x) 1 := by
  rw [coinducedSingleShiftHomEquiv]; rfl

/-- The inverse universal-property map is `coinducedSingleShiftLift`. -/
@[simp]
theorem coinducedSingleShiftHomEquiv_symm_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ) (f : M.grading.piece n →ₗ[k] V) :
    (coinducedSingleShiftHomEquiv M V n).symm f = coinducedSingleShiftLift n f := by
  rw [coinducedSingleShiftHomEquiv]; rfl

/-- Applying `coinducedSingleShiftHomEquiv` to `coinducedSingleShiftLift n f` recovers `f`. -/
@[simp]
theorem coinducedSingleShiftHomEquiv_coinducedSingleShiftLift (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ) (f : M.grading.piece n →ₗ[k] V) :
    coinducedSingleShiftHomEquiv M V n (coinducedSingleShiftLift n f) = f :=
  (coinducedSingleShiftHomEquiv M V n).apply_symm_apply f

/-- Lifting `coinducedSingleShiftHomEquiv M V n Ψ` recovers `Ψ`. -/
@[simp]
theorem coinducedSingleShiftLift_coinducedSingleShiftHomEquiv (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ)
    (Ψ : M ⟶ (coinducedSingle 𝒜 V).shiftObj n) :
    coinducedSingleShiftLift n (coinducedSingleShiftHomEquiv M V n Ψ) = Ψ :=
  (coinducedSingleShiftHomEquiv M V n).symm_apply_apply Ψ

/-- **Universal property of degree-zero coinduced modules.** Morphisms `M ⟶ coinducedSingle 𝒜 V`
correspond `k`-linearly to `k`-linear maps `M_0 →ₗ[k] V`. -/
def coinducedSingleHomEquiv (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] :
    (M ⟶ coinducedSingle 𝒜 V) ≃ₗ[k] (M.grading.piece 0 →ₗ[k] V) :=
  (Linear.homCongr k (Iso.refl M) ((shiftFunctorZeroIso 𝒜).app (coinducedSingle 𝒜 V)).symm).trans
    (coinducedSingleShiftHomEquiv M V 0)

/-- Evaluating a degree-zero coinduced morphism reads its values on `M_0` at `1 : A`. -/
@[simp]
theorem coinducedSingleHomEquiv_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V]
    (Ψ : M ⟶ coinducedSingle 𝒜 V) (x : M.grading.piece 0) :
    coinducedSingleHomEquiv M V Ψ x = coinducedSingleApply (Ψ.hom x) 1 := by
  simp [coinducedSingleHomEquiv, Linear.homCongr_apply]

/-- Evaluating `(coinducedSingleHomEquiv M V).symm f` applies `f` to `(b • x)_0`. -/
@[simp]
theorem coinducedSingleApply_coinducedSingleHomEquiv_symm (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V]
    (f : M.grading.piece 0 →ₗ[k] V) (x : M) (b : A) :
    coinducedSingleApply (((coinducedSingleHomEquiv M V).symm f).hom x) b =
      f (DirectSum.decompose M.grading.piece (b • x) 0) := by
  simp [coinducedSingleHomEquiv, Linear.homCongr_symm_apply]

/-- Precomposing a morphism into `coinducedSingle 𝒜 V` restricts the degree-zero map. -/
theorem coinducedSingleHomEquiv_comp {X Y : GradedModuleCat.{max uA v} 𝒜} (f : X ⟶ Y)
    (Ψ : Y ⟶ coinducedSingle 𝒜 V) (x : X.grading.piece 0) :
    coinducedSingleHomEquiv X V (f ≫ Ψ) x =
      coinducedSingleHomEquiv Y V Ψ ⟨f.hom x, map_mem f x.2⟩ := by simp

private theorem injective_coinducedSingle_of_extension {V : Type v} [AddCommGroup V] [Module k V]
    (hext : ∀ ⦃M N : Type (max uA v)⦄ [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
      (f : M →ₗ[k] N), Function.Injective f → ∀ g : M →ₗ[k] V,
        ∃ h : N →ₗ[k] V, ∀ x, h (f x) = g x) :
    Injective (coinducedSingle 𝒜 V) where
  factors {X Y} g f hf := by
    have hinj : Function.Injective f.hom := (mono_iff_injective f).mp hf
    let f₀ : X.grading.piece 0 →ₗ[k] Y.grading.piece 0 :=
      (f.hom.restrictScalars k).restrict fun _ hx ↦ map_mem f hx
    obtain ⟨h₀, hh₀⟩ := hext f₀ (fun _ _ hxy ↦ Subtype.ext (hinj (congrArg Subtype.val hxy)))
      (coinducedSingleHomEquiv X V g)
    refine ⟨(coinducedSingleHomEquiv Y V).symm h₀,
      (coinducedSingleHomEquiv X V).injective (LinearMap.ext fun x ↦ ?_)⟩
    rw [coinducedSingleHomEquiv_comp, LinearEquiv.apply_symm_apply]; exact hh₀ x

/-- If `V` satisfies Baer's criterion over `k`, `coinducedSingle 𝒜 V` is injective. -/
theorem injective_coinducedSingle_of_baer {V : Type v} [AddCommGroup V] [Module k V]
    (hV : Module.Baer k V) : Injective (coinducedSingle 𝒜 V) :=
  injective_coinducedSingle_of_extension fun _ _ _ _ _ _ f hf g ↦
    let ⟨h₀, hh₀⟩ := hV.extension_property f hf g; ⟨h₀, LinearMap.congr_fun hh₀⟩

/-- Coinducing an injective `k`-module produces an injective graded `𝒜`-module. -/
instance injective_coinducedSingle (V : Type (max uA v)) [AddCommGroup V] [Module k V]
    [inj : Module.Injective k V] : Injective (coinducedSingle 𝒜 V) :=
  injective_coinducedSingle_of_extension inj.out

end Single

section Family

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
  {I : Type (max uA v)} (d : I → ℤ)
  (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- The graded module coinduced from a family of `k`-modules `V i` placed in degrees `d i`,
realized as the degreewise product of shifted single-target coinduced modules. -/
abbrev coinduced : GradedModuleCat.{max uA v} 𝒜 :=
  product fun i ↦ (coinducedSingle 𝒜 (V i)).shiftObj (d i)

section UnivProp

variable {𝒜 d V}

/-- **Universal property of coinduced graded modules.** Morphisms into `coinduced 𝒜 d V`
correspond `k`-linearly to families of `k`-linear maps `M_{d i} →ₗ[k] V i`. -/
def coinducedHomEquiv (M : GradedModuleCat.{max uA v} 𝒜) :
    (M ⟶ coinduced 𝒜 d V) ≃ₗ[k] ∀ i, M.grading.piece (d i) →ₗ[k] V i where
  toFun Ψ i := coinducedSingleShiftHomEquiv M (V i) (d i) (Ψ ≫ productπ _ i)
  invFun f := productLift _ fun i ↦ (coinducedSingleShiftHomEquiv M (V i) (d i)).symm (f i)
  left_inv Ψ := product_hom_ext _ fun i ↦ by simp
  right_inv f := funext fun i ↦ by dsimp only; rw [productLift_π, LinearEquiv.apply_symm_apply]
  map_add' _ _ := funext fun _ ↦ by simp [Preadditive.add_comp]
  map_smul' _ _ := funext fun _ ↦ by simp [Linear.smul_comp]

/-- Applying `coinducedHomEquiv` at `i` projects onto the `i`-th factor and evaluates at `1`. -/
@[simp]
theorem coinducedHomEquiv_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (Ψ : M ⟶ coinduced 𝒜 d V) (i : I) :
    coinducedHomEquiv M Ψ i = coinducedSingleShiftHomEquiv M (V i) (d i) (Ψ ≫ productπ _ i) := by
  rw [coinducedHomEquiv]; rfl

/-- Following `(coinducedHomEquiv M).symm f` with `productπ _ i` recovers the `i`-th lift. -/
@[reassoc (attr := simp)]
theorem coinducedHomEquiv_symm_π (M : GradedModuleCat.{max uA v} 𝒜)
    (f : ∀ i, M.grading.piece (d i) →ₗ[k] V i) (i : I) :
    (coinducedHomEquiv M).symm f ≫ productπ _ i = coinducedSingleShiftLift (d i) (f i) := by
  rw [coinducedHomEquiv]; dsimp only [LinearEquiv.coe_symm_mk]
  rw [productLift_π, coinducedSingleShiftHomEquiv_symm_apply]

/-- If every `V i` satisfies Baer's criterion over `k`, `coinduced 𝒜 d V` is injective. -/
theorem injective_coinduced_of_baer (hV : ∀ i, Module.Baer k (V i)) :
    Injective (coinduced 𝒜 d V) := by
  have (i : I) : Injective (coinducedSingle 𝒜 (V i)) := injective_coinducedSingle_of_baer (hV i)
  infer_instance

end UnivProp

/-- Coinducing a family of injective `k`-modules gives an injective graded `𝒜`-module. -/
instance injective_coinduced (W : I → Type (max uA v)) [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] [∀ i, Module.Injective k (W i)] : Injective (coinduced 𝒜 d W) :=
  inferInstance

end Family

section EnoughInjectives

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

private theorem enoughInjectives_of_small [Small.{max uA v} k] :
    EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) where
  presentation M := by
    let P (s : ℤ) := Injective.under (ModuleCat.of k (M.grading.piece s))
    let ι (s : ℤ) : ModuleCat.of k (M.grading.piece s) ⟶ P s := Injective.ι _
    have (s : ℤ) : Module.Injective k (P s) :=
      Module.injective_module_of_injective_object k (P s)
        (inj := Injective.injective_under (ModuleCat.of k (M.grading.piece s)))
    let Q := coinduced 𝒜 (fun j : ULift.{max uA v} ℤ ↦ j.down) (fun j ↦ P j.down)
    let f : M ⟶ Q := (coinducedHomEquiv M).symm fun j ↦ (ι j.down).hom
    have hf : Function.Injective f.hom := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      apply (DirectSum.decompose M.grading.piece).injective
      rw [DirectSum.decompose_zero]
      refine DirectSum.ext fun s ↦ ((ModuleCat.mono_iff_injective (ι s)).mp inferInstance) ?_
      have hfac : f ≫ productπ _ (ULift.up s) = coinducedSingleShiftLift s (ι s).hom :=
        coinducedHomEquiv_symm_π M _ (ULift.up s)
      have heval := congrArg
        (fun g : M ⟶ (coinducedSingle 𝒜 (P s)).shiftObj s ↦ coinducedSingleApply (g.hom z) 1) hfac
      simpa [LinearMap.mem_ker.mp hz] using heval.symm
    have : Mono f := (mono_iff_injective f).mpr hf
    exact ⟨{ J := Q, f := f }⟩

/-- In any module universe `max uA v` at least that of `A`, `GradedModuleCat.{max uA v} 𝒜` has
enough injectives, with no smallness assumption on the base ring `k`. -/
instance enoughInjectives : EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) :=
  (restrictBaseEquivalence ℤ 𝒜).enoughInjectives_iff.2 enoughInjectives_of_small

end EnoughInjectives

end TauCeti.GradedModuleCat
