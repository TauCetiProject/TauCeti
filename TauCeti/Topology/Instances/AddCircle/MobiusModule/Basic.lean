/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Instances.Matrix

import TauCeti.Topology.Circle.AddCircle
import TauCeti.Topology.Order.IntermediateValue

/-!
# The Möbius module over the ring of continuous functions on the circle

Let `R = C(ℝ / ℤ, ℝ)` be the ring of continuous real functions on the circle `AddCircle 1`. The
reflection `ρ([t]) = [[cos 2πt, sin 2πt], [sin 2πt, −cos 2πt]]` of the plane in the line spanned
by `u(t) = (cos πt, sin πt)` is an involution of `R²`, and its fixed module `M ⊆ R²` is the module
of continuous sections of the Möbius line bundle: the line `ℝ u(t)` turns by a half turn while
`t` runs once around the circle. Since `ρ = 2p − 1` for the idempotent `p = u uᵀ`, the module
`M` is the image `pR²`.

The reflection, the module and the idempotent are defined more generally with coefficients in any
topological `ℝ`-algebra `A`, over the ring `C(ℝ / ℤ, A)`, through `algebraMap ℝ A`; the module
`TauCeti.mobiusSections ℂ` is the complex Möbius module.

This file proves the two module statements which say that `M` is finitely generated projective and
that the class `[M] − [R]` has order exactly two in `K₀(R)` (by the stable description of equality
in `K₀`):

* `M ⊕ M ≅ R²`: the quarter turn `J (v₀, v₁) = (−v₁, v₀)` anticommutes with `ρ`, so it carries `M`
  onto the module on which `ρ` acts by `−1`, a complement of `M`. This holds over any `A`.
* `M ⊕ Rᴺ ≇ Rᴺ⁺¹` for every `N`: an isomorphism would give, at each `t`, an invertible matrix of
  coordinates of the preimages of the standard basis, taken along `u(t)` in `M`. Since
  `u(t + 1) = −u(t)`, its determinant would be a continuous nowhere-vanishing function with
  `f (t + 1) = −f t`, which the intermediate value theorem forbids. For `N = 0` this says that `M`
  is not free of rank one, and with `M ⊕ M ≅ R²` it is not free at all.

## Main definitions

* `TauCeti.circleCoord`: the coordinate functions `[t] ↦ cos 2πt` and `[t] ↦ sin 2πt`.
* `TauCeti.mobiusReflection`: the reflection `ρ`, a `2 × 2` matrix over `C(ℝ / ℤ, A)`.
* `TauCeti.mobiusSections`: the Möbius module `M`, the kernel of `ρ − 1` acting on
  `C(ℝ / ℤ, A)²`.
* `TauCeti.mobiusSectionsProdEquiv`: the isomorphism `M × M ≃ C(ℝ / ℤ, A)²`, `(a, b) ↦ a + J b`.
* `TauCeti.mobiusProjection`: the symmetric idempotent `p = (1 + ρ) / 2`, pointwise `u uᵀ`.
* `TauCeti.mobiusSectionCoeff`: the coefficient `t ↦ ⟨u(t), w([t])⟩` of a pair `w` along
  `u(t) = (cos πt, sin πt)`, a continuous antiperiodic function on `ℝ`.

## Main results

* `TauCeti.mem_mobiusSections_iff`: the pointwise description of `M`.
* `TauCeti.range_mulVecLin_mobiusProjection`, `TauCeti.range_vecMulLinear_mobiusProjection`:
  `M` is the image of `p`.
* `TauCeti.map_mobiusProjection`: a continuous `ℝ`-algebra homomorphism `A → B` carries `p` over
  `A` to `p` over `B`.
* `TauCeti.apply_eq_mobiusSectionCoeff_mul`: a section of `M` is `⟨u, w⟩ u`.
* `TauCeti.isEmpty_mobiusSections_prod_linearEquiv`: `M × Rᴺ` is not isomorphic to `Rᴺ⁺¹`.
* `TauCeti.mobiusSections_order_two`: both statements together.
* `TauCeti.not_free_mobiusSections`: `M` is finitely generated projective but not free.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, (4.9.1), for the Möbius bundle as the nontrivial real line
  bundle on the circle.
-/

public section

noncomputable section

open Matrix Real

namespace TauCeti

section General

variable (A : Type*) [CommRing A] [TopologicalSpace A] [Algebra ℝ A] [ContinuousSMul ℝ A]

/-- The coordinate functions `[t] ↦ cos 2πt` and `[t] ↦ sin 2πt` on the circle `ℝ / ℤ`, the real
and imaginary parts of `AddCircle.toCircle`, as continuous `A`-valued functions through
`algebraMap ℝ A`. -/
def circleCoord (i : Fin 2) : C(AddCircle (1 : ℝ), A) :=
  ⟨fun x ↦ algebraMap ℝ A (![(AddCircle.toCircle x : ℂ).re, (AddCircle.toCircle x : ℂ).im] i), by
    have hc : Continuous fun x : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle x : ℂ) :=
      continuous_induced_dom.comp AddCircle.continuous_toCircle
    refine (continuous_algebraMap ℝ A).comp ?_
    fin_cases i
    · exact Complex.continuous_re.comp hc
    · exact Complex.continuous_im.comp hc⟩

variable {A}

/-- `circleCoord A 0` is the real part of `AddCircle.toCircle`. -/
theorem circleCoord_zero_apply (x : AddCircle (1 : ℝ)) :
    circleCoord A 0 x = algebraMap ℝ A (AddCircle.toCircle x : ℂ).re :=
  (rfl)

/-- `circleCoord A 1` is the imaginary part of `AddCircle.toCircle`. -/
theorem circleCoord_one_apply (x : AddCircle (1 : ℝ)) :
    circleCoord A 1 x = algebraMap ℝ A (AddCircle.toCircle x : ℂ).im :=
  (rfl)

@[simp]
theorem circleCoord_zero_apply_mk (t : ℝ) :
    circleCoord A 0 t = algebraMap ℝ A (cos (2 * π * t)) := by
  rw [circleCoord_zero_apply, AddCircle.re_toCircle_coe, div_one]

@[simp]
theorem circleCoord_one_apply_mk (t : ℝ) :
    circleCoord A 1 t = algebraMap ℝ A (sin (2 * π * t)) := by
  rw [circleCoord_one_apply, AddCircle.im_toCircle_coe, div_one]

variable [IsTopologicalRing A]

/-- Post-composing `circleCoord` with a continuous `ℝ`-algebra homomorphism changes the target
ring. -/
@[simp]
theorem compLeftContinuous_circleCoord {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra ℝ B] [ContinuousSMul ℝ B] (φ : A →ₐ[ℝ] B) (hφ : Continuous φ)
    (i : Fin 2) :
    (φ : A →+* B).compLeftContinuous _ hφ (circleCoord A i) = circleCoord B i := by
  ext x
  fin_cases i <;> exact φ.commutes _

/-- The circle coordinates satisfy `cos² + sin² = 1` in `C(ℝ / ℤ, A)`. -/
@[simp]
theorem circleCoord_zero_sq_add_circleCoord_one_sq :
    circleCoord A 0 ^ 2 + circleCoord A 1 ^ 2 = 1 := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H t => ?_
  simpa only [map_add, map_pow, map_one, ContinuousMap.add_apply, ContinuousMap.pow_apply,
    ContinuousMap.one_apply, circleCoord_zero_apply_mk, circleCoord_one_apply_mk] using
    congrArg (algebraMap ℝ A) (cos_sq_add_sin_sq (2 * π * t))

variable (A) in
/-- The reflection `ρ([t]) = [[cos 2πt, sin 2πt], [sin 2πt, −cos 2πt]]` over `C(ℝ / ℤ, A)`. At
`[t]` it is the reflection of the plane in the line spanned by `(cos πt, sin πt)`. -/
def mobiusReflection : Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), A) :=
  !![circleCoord A 0, circleCoord A 1; circleCoord A 1, -circleCoord A 0]

theorem mobiusReflection_def :
    mobiusReflection A =
      !![circleCoord A 0, circleCoord A 1; circleCoord A 1, -circleCoord A 0] :=
  (rfl)

/-- The reflection `ρ` is an involution. -/
theorem mobiusReflection_mul_self : mobiusReflection A * mobiusReflection A = 1 := by
  rw [mobiusReflection_def, mul_fin_two, one_fin_two]
  simp [← sq, mul_comm, add_comm (circleCoord A 1 ^ 2)]

variable (A) in
/-- The **Möbius module** over `C(ℝ / ℤ, A)`: the pairs `w` of continuous functions on the circle
fixed by the reflection `mobiusReflection`, that is, the continuous fields with `w([t])` on the
line spanned by `(cos πt, sin πt)`. This line turns by a half turn as `t` runs once around the
circle, so for `A = ℝ` this is the module of sections of the Möbius line bundle. -/
def mobiusSections : Submodule C(AddCircle (1 : ℝ), A) (Fin 2 → C(AddCircle (1 : ℝ), A)) :=
  LinearMap.ker (mulVecLin (mobiusReflection A - 1))

theorem mobiusSections_def :
    mobiusSections A = LinearMap.ker (mulVecLin (mobiusReflection A - 1)) :=
  (rfl)

/-- The Möbius module is the fixed module of the reflection `ρ`. -/
theorem mem_mobiusSections_iff_mulVec {w : Fin 2 → C(AddCircle (1 : ℝ), A)} :
    w ∈ mobiusSections A ↔ mobiusReflection A *ᵥ w = w := by
  simp [mobiusSections_def, sub_eq_zero]

/-- A pair `w = (w₀, w₁)` lies in the Möbius module iff `cos(2πt) w₀ + sin(2πt) w₁ = w₀` and
`sin(2πt) w₀ − cos(2πt) w₁ = w₁` at every point `[t]` of the circle. -/
theorem mem_mobiusSections_iff {w : Fin 2 → C(AddCircle (1 : ℝ), A)} :
    w ∈ mobiusSections A ↔ ∀ t : ℝ,
      cos (2 * π * t) • w 0 t + sin (2 * π * t) • w 1 t = w 0 t ∧
        sin (2 * π * t) • w 0 t - cos (2 * π * t) • w 1 t = w 1 t := by
  simp only [mem_mobiusSections_iff_mulVec, funext_iff, Fin.forall_fin_two, ContinuousMap.ext_iff,
    QuotientAddGroup.mk_surjective.forall, ← forall_and]
  simp [mobiusReflection_def, mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg,
    Algebra.smul_def]

/-! ### `M ⊕ M ≅ A²` -/

/-- The rotation `J = [[0, −1], [1, 0]]` by a quarter turn. It anticommutes with the reflection
`ρ`, so it carries the fixed line of `ρ` onto the line `ρ` negates. -/
private def quarterTurn : Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), A) := !![0, -1; 1, 0]

omit [Algebra ℝ A] [ContinuousSMul ℝ A] in
private theorem quarterTurn_mulVec (v : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    quarterTurn *ᵥ v = ![-v 1, v 0] := by
  ext i : 1
  fin_cases i <;> simp [quarterTurn, mulVec, dotProduct, Fin.sum_univ_two]

omit [Algebra ℝ A] [ContinuousSMul ℝ A] in
private theorem quarterTurn_mulVec_quarterTurn_mulVec (v : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    quarterTurn *ᵥ (quarterTurn *ᵥ v) = -v := by
  ext i : 1
  fin_cases i <;> simp [quarterTurn_mulVec]

private theorem mobiusReflection_mulVec_mobiusReflection_mulVec
    (v : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    mobiusReflection A *ᵥ (mobiusReflection A *ᵥ v) = v := by
  rw [mulVec_mulVec, mobiusReflection_mul_self, one_mulVec]

private theorem mobiusReflection_mulVec_quarterTurn_mulVec (v : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    mobiusReflection A *ᵥ (quarterTurn *ᵥ v) = -(quarterTurn *ᵥ (mobiusReflection A *ᵥ v)) := by
  have h : mobiusReflection A * quarterTurn = -(quarterTurn * mobiusReflection A) := by
    rw [quarterTurn, mobiusReflection_def, mul_fin_two, mul_fin_two]
    simp [add_comm]
  rw [mulVec_mulVec, h, neg_mulVec, mulVec_mulVec]

/-- The projection `w ↦ (w + ρ w) / 2` lands in the Möbius module. -/
private theorem half_add_mulVec_mem (w : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    (2⁻¹ : ℝ) • (w + mobiusReflection A *ᵥ w) ∈ mobiusSections A := by
  rw [mem_mobiusSections_iff_mulVec, mulVec_smul, mulVec_add,
    mobiusReflection_mulVec_mobiusReflection_mulVec, add_comm]

/-- The map `w ↦ J (ρ w − w) / 2`, the quarter turn back of the part of `w` negated by `ρ`, lands
in the Möbius module. -/
private theorem half_quarterTurn_mulVec_mem (w : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    (2⁻¹ : ℝ) • (quarterTurn *ᵥ (mobiusReflection A *ᵥ w - w)) ∈ mobiusSections A := by
  rw [mem_mobiusSections_iff_mulVec, mulVec_smul, mobiusReflection_mulVec_quarterTurn_mulVec,
    mulVec_sub, mobiusReflection_mulVec_mobiusReflection_mulVec, ← mulVec_neg, neg_sub]

variable (A) in
/-- The Möbius module `M` satisfies `M ⊕ M ≅ C(ℝ / ℤ, A)²`, through `(a, b) ↦ a + J b` with
`J (b₀, b₁) = (−b₁, b₀)` the quarter turn: `J` carries `M`, the fixed module of the reflection
`ρ`, onto its complement, the module on which `ρ` acts by `−1`. -/
def mobiusSectionsProdEquiv :
    (mobiusSections A × mobiusSections A) ≃ₗ[C(AddCircle (1 : ℝ), A)]
      (Fin 2 → C(AddCircle (1 : ℝ), A)) where
  toFun ab := (ab.1 : Fin 2 → C(AddCircle (1 : ℝ), A)) + quarterTurn *ᵥ (ab.2 : Fin 2 → _)
  map_add' ab cd := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, mulVec_add]
    abel
  map_smul' r ab := by simp [mulVec_smul]
  invFun w := (⟨_, half_add_mulVec_mem w⟩, ⟨_, half_quarterTurn_mulVec_mem w⟩)
  left_inv ab := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ab
    rw [mem_mobiusSections_iff_mulVec] at ha hb
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
      simp only [mulVec_add, mulVec_sub, mulVec_neg, mobiusReflection_mulVec_quarterTurn_mulVec,
        quarterTurn_mulVec_quarterTurn_mulVec, ha, hb] <;>
      module
  right_inv w := by
    simp only [mulVec_smul, quarterTurn_mulVec_quarterTurn_mulVec]
    module

/-- `mobiusSectionsProdEquiv` sends `(a, b)` to `a + J b`, with `J (b₀, b₁) = (−b₁, b₀)`. -/
@[simp]
theorem mobiusSectionsProdEquiv_apply (a b : mobiusSections A) :
    mobiusSectionsProdEquiv A (a, b) =
      (a : Fin 2 → C(AddCircle (1 : ℝ), A)) +
        ![-(b : Fin 2 → C(AddCircle (1 : ℝ), A)) 1, (b : Fin 2 → C(AddCircle (1 : ℝ), A)) 0] := by
  simp [mobiusSectionsProdEquiv, quarterTurn_mulVec]

/-- The first component of the inverse of `mobiusSectionsProdEquiv` is the projection
`w ↦ (w + ρ w) / 2` onto the Möbius module. -/
theorem coe_mobiusSectionsProdEquiv_symm_apply_fst (w : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    (((mobiusSectionsProdEquiv A).symm w).1 : Fin 2 → C(AddCircle (1 : ℝ), A)) =
      (2⁻¹ : ℝ) • (w + mobiusReflection A *ᵥ w) :=
  (rfl)

/-- The second component of the inverse of `mobiusSectionsProdEquiv` is
`w ↦ J (ρ w − w) / 2`, with `J (v₀, v₁) = (−v₁, v₀)` the quarter turn. -/
theorem coe_mobiusSectionsProdEquiv_symm_apply_snd (w : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    (((mobiusSectionsProdEquiv A).symm w).2 : Fin 2 → C(AddCircle (1 : ℝ), A)) =
      (2⁻¹ : ℝ) • ![w 1 - (mobiusReflection A *ᵥ w) 1, (mobiusReflection A *ᵥ w) 0 - w 0] := by
  have h : (((mobiusSectionsProdEquiv A).symm w).2 : Fin 2 → C(AddCircle (1 : ℝ), A)) =
      (2⁻¹ : ℝ) • (quarterTurn *ᵥ (mobiusReflection A *ᵥ w - w)) := (rfl)
  rw [h, quarterTurn_mulVec, Pi.sub_apply, Pi.sub_apply, neg_sub]

/-- A section `a` of the Möbius module corresponds to `(a, 0)`. -/
@[simp]
theorem mobiusSectionsProdEquiv_symm_apply_coe (a : mobiusSections A) :
    (mobiusSectionsProdEquiv A).symm a = (a, 0) :=
  (mobiusSectionsProdEquiv A).symm_apply_eq.2 <| by
    rw [mobiusSectionsProdEquiv_apply]
    ext i : 1
    fin_cases i <;> simp

/-- The Möbius module is finitely generated, as a direct summand of `C(ℝ / ℤ, A)²`. -/
instance : Module.Finite C(AddCircle (1 : ℝ), A) (mobiusSections A) :=
  .of_surjective (LinearMap.fst _ _ _ ∘ₗ (mobiusSectionsProdEquiv A).symm.toLinearMap)
    fun a ↦ ⟨a, by simp⟩

/-- The Möbius module is projective, as a direct summand of `C(ℝ / ℤ, A)²`. -/
instance : Module.Projective C(AddCircle (1 : ℝ), A) (mobiusSections A) :=
  .of_split ((mobiusSectionsProdEquiv A).toLinearMap ∘ₗ LinearMap.inl _ _ _)
    (LinearMap.fst _ _ _ ∘ₗ (mobiusSectionsProdEquiv A).symm.toLinearMap) <|
      LinearMap.ext fun _ ↦ by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.inl_apply, LinearEquiv.symm_apply_apply, LinearMap.fst_apply, LinearMap.id_apply]

/-! ### The Möbius module as the image of an idempotent -/

/-- The reflection `ρ` is symmetric. -/
@[simp]
theorem transpose_mobiusReflection : (mobiusReflection A)ᵀ = mobiusReflection A := by
  rw [mobiusReflection_def]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Entrywise application of a continuous `ℝ`-algebra homomorphism carries the reflection `ρ`
over `A` to the reflection over `B`. -/
@[simp]
theorem map_mobiusReflection {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra ℝ B] [ContinuousSMul ℝ B] (φ : A →ₐ[ℝ] B) (hφ : Continuous φ) :
    (mobiusReflection A).map ((φ : A →+* B).compLeftContinuous _ hφ) = mobiusReflection B := by
  rw [mobiusReflection_def, mobiusReflection_def]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable (A) in
/-- The idempotent `p = (1 + ρ) / 2` over `C(ℝ / ℤ, A)`. At `[t]` it is the orthogonal projection
`u(t) u(t)ᵀ` onto the line spanned by `u(t) = (cos πt, sin πt)` (`mobiusProjection_apply_mk`),
and its image is the Möbius module (`range_mulVecLin_mobiusProjection`). -/
def mobiusProjection : Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), A) :=
  (2⁻¹ : ℝ) • (1 + mobiusReflection A)

theorem mobiusProjection_def : mobiusProjection A = (2⁻¹ : ℝ) • (1 + mobiusReflection A) :=
  (rfl)

/-- Entrywise application of a continuous `ℝ`-algebra homomorphism carries the projection `p`
over `A` to the projection over `B`. -/
@[simp]
theorem map_mobiusProjection {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra ℝ B] [ContinuousSMul ℝ B] (φ : A →ₐ[ℝ] B) (hφ : Continuous φ) :
    (mobiusProjection A).map ((φ : A →+* B).compLeftContinuous _ hφ) = mobiusProjection B := by
  rw [mobiusProjection_def, mobiusProjection_def,
    Matrix.map_smul _ _ fun _ ↦ by ext; exact map_smul φ _ _, Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), map_mobiusReflection]

/-- At `[t]`, the matrix `p` is `u(t) u(t)ᵀ` with `u(t) = (cos πt, sin πt)`. -/
theorem mobiusProjection_apply_mk (i j : Fin 2) (t : ℝ) :
    mobiusProjection A i j t =
      algebraMap ℝ A (![cos (π * t), sin (π * t)] i * ![cos (π * t), sin (π * t)] j) := by
  have h : 2 * π * t = 2 * (π * t) := by ring
  rw [← map_mobiusProjection (Algebra.ofId ℝ A) (continuous_algebraMap ℝ A), map_apply]
  refine congrArg (algebraMap ℝ A) ?_
  fin_cases i <;> fin_cases j <;>
    simp [mobiusProjection_def, mobiusReflection_def, h, ← sq, cos_sq, sin_sq, sin_two_mul] <;>
    ring

/-- The projection `p` is symmetric. -/
@[simp]
theorem transpose_mobiusProjection : (mobiusProjection A)ᵀ = mobiusProjection A := by
  rw [mobiusProjection_def, transpose_smul, transpose_add, transpose_one,
    transpose_mobiusReflection]

theorem isIdempotentElem_mobiusProjection : IsIdempotentElem (mobiusProjection A) := by
  rw [IsIdempotentElem, mobiusProjection_def, smul_mul_smul_comm, mul_add, add_mul, add_mul,
    mobiusReflection_mul_self, one_mul, mul_one, one_mul]
  module

theorem mobiusProjection_mulVec (w : Fin 2 → C(AddCircle (1 : ℝ), A)) :
    mobiusProjection A *ᵥ w = (2⁻¹ : ℝ) • (w + mobiusReflection A *ᵥ w) := by
  rw [mobiusProjection_def, smul_mulVec, add_mulVec, one_mulVec]

/-- The Möbius module is the image `pA²` of the projection `p` acting on columns. -/
theorem range_mulVecLin_mobiusProjection :
    LinearMap.range (mulVecLin (mobiusProjection A)) = mobiusSections A := by
  refine le_antisymm ?_ fun w hw ↦ ⟨w, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [mulVecLin_apply, mobiusProjection_mulVec]
    exact half_add_mulVec_mem w
  · rw [mem_mobiusSections_iff_mulVec] at hw
    rw [mulVecLin_apply, mobiusProjection_mulVec, hw]
    module

/-- The Möbius module is the image of the symmetric projection `p` acting on rows. -/
theorem range_vecMulLinear_mobiusProjection :
    LinearMap.range (vecMulLinear (mobiusProjection A)) = mobiusSections A := by
  rw [← range_mulVecLin_mobiusProjection]
  congr 1
  refine LinearMap.ext fun w ↦ ?_
  rw [vecMulLinear_apply, mulVecLin_apply, ← vecMul_transpose, transpose_mobiusProjection]

end General

local notation "𝓒" => C(AddCircle (1 : ℝ), ℝ)

/-! ### `M ⊕ Rᴺ ≇ Rᴺ⁺¹` -/

private theorem continuous_apply_coe (f : 𝓒) : Continuous fun t : ℝ ↦ f t :=
  f.continuous.comp (AddCircle.continuous_mk' 1)

/-- The coefficient `t ↦ ⟨u(t), w([t])⟩` of a pair `w` of functions on the circle along
`u(t) = (cos πt, sin πt)`. On the Möbius module it is the map to antiperiodic functions on `ℝ`
inverse to `v ↦ ([t] ↦ v(t) u(t))`. -/
def mobiusSectionCoeff (w : Fin 2 → 𝓒) (t : ℝ) : ℝ :=
  cos (π * t) * w 0 t + sin (π * t) * w 1 t

theorem mobiusSectionCoeff_apply (w : Fin 2 → 𝓒) (t : ℝ) :
    mobiusSectionCoeff w t = cos (π * t) * w 0 t + sin (π * t) * w 1 t :=
  (rfl)

/-- The coefficient along `u` is continuous. -/
theorem continuous_mobiusSectionCoeff (w : Fin 2 → 𝓒) : Continuous (mobiusSectionCoeff w) := by
  unfold mobiusSectionCoeff
  have := continuous_apply_coe (w 0)
  have := continuous_apply_coe (w 1)
  fun_prop

/-- The coefficient along `u` changes sign over one turn, because `u(t + 1) = −u(t)`. -/
theorem antiperiodic_mobiusSectionCoeff (w : Fin 2 → 𝓒) :
    Function.Antiperiodic (mobiusSectionCoeff w) 1 := fun t ↦ by
  simp only [mobiusSectionCoeff_apply, AddCircle.coe_add_period, mul_add, mul_one, cos_add_pi,
    sin_add_pi]
  ring

/-- A section of the Möbius module lies on the line spanned by `u(t)`: `w([t]) = ⟨u, w⟩ u(t)`. -/
theorem apply_eq_mobiusSectionCoeff_mul {w : Fin 2 → 𝓒} (hw : w ∈ mobiusSections ℝ) (t : ℝ) :
    w 0 t = mobiusSectionCoeff w t * cos (π * t) ∧
      w 1 t = mobiusSectionCoeff w t * sin (π * t) := by
  obtain ⟨h₀, h₁⟩ := mem_mobiusSections_iff.1 hw t
  simp only [smul_eq_mul] at h₀ h₁
  rw [mul_assoc, cos_two_mul, sin_two_mul] at h₀ h₁
  have h := sin_sq_add_cos_sq (π * t)
  constructor <;> simp only [mobiusSectionCoeff_apply]
  · linear_combination (-1 / 2 : ℝ) * h₀
  · linear_combination (-1 / 2 : ℝ) * h₁ - w 1 t * h

section Frame

variable {N : ℕ} (φ : (mobiusSections ℝ × (Fin N → 𝓒)) ≃ₗ[𝓒] (Fin (N + 1) → 𝓒))

/-- The matrix `B(t)` whose `k`-th column holds the coordinates at `t` of `φ⁻¹(eₖ) = (aₖ, rₖ)` in
the frame `u(t), e₁, …, e_N` of the fibre: the first row is `⟨u(t), aₖ([t])⟩` and the others are
the entries of `rₖ([t])`. -/
private def frameMatrix (t : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i k ↦ Fin.cases (mobiusSectionCoeff (φ.symm (Pi.single k 1)).1 t)
    (fun l ↦ (φ.symm (Pi.single k 1)).2 l t) i

/-- The image under `φ` of the projection to the Möbius module of the `i`-th basis vector
of `R²`. -/
private def sectionImage (i : Fin 2) : Fin (N + 1) → 𝓒 :=
  φ (((mobiusSectionsProdEquiv ℝ).symm fun j ↦ if i = j then 1 else 0).1, 0)

/-- The image under `φ` of the `l`-th basis vector of `Rᴺ`. -/
private def freeImage (l : Fin N) : Fin (N + 1) → 𝓒 :=
  φ (0, fun m ↦ if l = m then 1 else 0)

/-- The matrix `C(t)` of `φ` in the frame `u(t), e₁, …, e_N` at `t`: an inverse of `B(t)`. -/
private def coframeMatrix (t : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun j i ↦ Fin.cases
    (cos (π * t) * sectionImage φ 0 j t + sin (π * t) * sectionImage φ 1 j t)
    (fun l ↦ freeImage φ l j t) i

private theorem apply_section (a : mobiusSections ℝ) :
    φ (a, 0) = ∑ i, (a : Fin 2 → 𝓒) i • sectionImage φ i := by
  let L : (Fin 2 → 𝓒) →ₗ[𝓒] Fin (N + 1) → 𝓒 := φ.toLinearMap ∘ₗ
    LinearMap.inl 𝓒 _ _ ∘ₗ LinearMap.fst 𝓒 _ _ ∘ₗ (mobiusSectionsProdEquiv ℝ).symm.toLinearMap
  have h : φ (a, 0) = L a := by simp [L]
  rw [h, LinearMap.pi_apply_eq_sum_univ L]
  simp only [L, sectionImage, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply,
    LinearMap.inl_apply]

private theorem apply_free (r : Fin N → 𝓒) : φ (0, r) = ∑ l, r l • freeImage φ l := by
  let L : (Fin N → 𝓒) →ₗ[𝓒] Fin (N + 1) → 𝓒 := φ.toLinearMap ∘ₗ LinearMap.inr 𝓒 _ _
  exact L.pi_apply_eq_sum_univ r

/-- `C(t) B(t) = 1`: this is `φ (φ⁻¹ eₖ) = eₖ`, read in the frames at `t`. -/
private theorem coframeMatrix_mul_frameMatrix (t : ℝ) :
    coframeMatrix φ t * frameMatrix φ t = 1 := by
  ext j k
  rcases hk : φ.symm (Pi.single k 1) with ⟨a, r⟩
  have h := congrArg (fun v : Fin (N + 1) → 𝓒 ↦ v j t) (φ.apply_symm_apply (Pi.single k 1))
  have hs : φ (a, r) = φ (a, 0) + φ (0, r) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  obtain ⟨ha₀, ha₁⟩ := apply_eq_mobiusSectionCoeff_mul a.property t
  simp only [hk, hs, apply_section, apply_free, Fin.sum_univ_two] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, ContinuousMap.coe_sum, ContinuousMap.coe_mul, Pi.mul_apply,
    Pi.single_apply, coframeMatrix, frameMatrix, Matrix.mul_apply, of_apply, hk, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Matrix.one_apply] at h ⊢
  rw [ha₀, ha₁, apply_ite (fun f : 𝓒 ↦ f t), ContinuousMap.one_apply,
    ContinuousMap.zero_apply] at h
  simp only [mul_comm (freeImage φ _ j _)]
  linear_combination h

/-- Over one turn the first row of `B` changes sign and the others are unchanged. -/
private theorem frameMatrix_add_one (t : ℝ) :
    frameMatrix φ (t + 1) = updateRow (frameMatrix φ t) 0 ((-1 : ℝ) • frameMatrix φ t 0) := by
  ext i k
  cases i using Fin.cases with
  | zero => simp [frameMatrix, antiperiodic_mobiusSectionCoeff _ t]
  | succ l => simp [frameMatrix]

/-- The determinant of `B` is antiperiodic. -/
private theorem antiperiodic_det_frameMatrix :
    Function.Antiperiodic (fun t ↦ (frameMatrix φ t).det) 1 := fun t ↦ by
  simp only [frameMatrix_add_one, det_updateRow_smul, updateRow_eq_self, neg_one_mul]

private theorem continuous_det_frameMatrix : Continuous fun t ↦ (frameMatrix φ t).det := by
  refine Continuous.matrix_det (continuous_matrix fun i k ↦ ?_)
  cases i using Fin.cases with
  | zero => simpa [frameMatrix] using continuous_mobiusSectionCoeff _
  | succ l => simpa [frameMatrix] using continuous_apply_coe _

end Frame

/-- The Möbius module `M` over `R = C(ℝ / ℤ, ℝ)` is not stably free: `M ⊕ Rᴺ ≇ Rᴺ⁺¹` for every
`N`. In particular (`N = 0`) `M` is not isomorphic to `R`.

Given such an isomorphism `φ`, the coordinates at `t` of the preimages `φ⁻¹(eₖ)`, taken along
`u(t) = (cos πt, sin πt)` in `M` and along the standard basis in `Rᴺ`, form a matrix `B(t)` which
is invertible at every `t`, its inverse being the matrix of `φ` in the same frames. Since
`u(t + 1) = −u(t)`, the determinant of `B` is a continuous antiperiodic function, so it vanishes
somewhere by the intermediate value theorem, a contradiction. -/
theorem isEmpty_mobiusSections_prod_linearEquiv (N : ℕ) :
    IsEmpty ((mobiusSections ℝ × (Fin N → 𝓒)) ≃ₗ[𝓒] (Fin (N + 1) → 𝓒)) := by
  refine ⟨fun φ ↦ ?_⟩
  obtain ⟨t, -, ht⟩ := (antiperiodic_det_frameMatrix φ).exists_mem_uIcc_eq_zero 0
    (continuous_det_frameMatrix φ).continuousOn
  have h := congrArg det (coframeMatrix_mul_frameMatrix φ t)
  rw [det_mul, det_one, ht, mul_zero] at h
  exact zero_ne_one h

/-- The Möbius module is not free: a basis would have one element, since `M ⊕ M ≅ R²`, which
`isEmpty_mobiusSections_prod_linearEquiv` excludes. -/
theorem not_free_mobiusSections : ¬ Module.Free 𝓒 (mobiusSections ℝ) := by
  intro _
  have h : Module.finrank 𝓒 (mobiusSections ℝ) = 1 := by
    have := (mobiusSectionsProdEquiv ℝ).finrank_eq
    rw [Module.finrank_prod, Module.finrank_fin_fun] at this
    omega
  exact (isEmpty_mobiusSections_prod_linearEquiv 0).false
    (LinearEquiv.prodUnique.trans (Module.finBasisOfFinrankEq 𝓒 _ h).equivFun)

/-- The Möbius module `M` over `R = C(ℝ / ℤ, ℝ)` satisfies `M ⊕ M ≅ R²` but `M ⊕ Rᴺ ≇ Rᴺ⁺¹` for
every `N`. By the stable description of equality in `K₀(R)`, the first statement says that
`2 ([M] − [R]) = 0` and the second that `[M] − [R] ≠ 0`. -/
theorem mobiusSections_order_two :
    Nonempty ((mobiusSections ℝ × mobiusSections ℝ) ≃ₗ[𝓒] (Fin 2 → 𝓒)) ∧
      ∀ N : ℕ, IsEmpty ((mobiusSections ℝ × (Fin N → 𝓒)) ≃ₗ[𝓒] (Fin (N + 1) → 𝓒)) :=
  ⟨⟨mobiusSectionsProdEquiv ℝ⟩, isEmpty_mobiusSections_prod_linearEquiv⟩

end TauCeti
