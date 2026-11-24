/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Time-weighted spaces of continuous functions

For `T, η : ℝ` and a normed space `X`, the space `C_η((0, T]; X)` consists of the continuous maps
`u : (0, T] → X` that may blow up at `t = 0` at most like `t^{-η}`, with the weighted norm

`‖u‖ = sup_{0 < t ≤ T} t^η ‖u t‖`.

These are the solution spaces of the local-in-time fixed-point arguments for parabolic equations
with rough initial data: the heat flow `e^{tΔ} u₀` of initial data `u₀` of regularity `s` has
regularity `s + 2σ` at time `t` with norm `O(t^{-σ})`, so the solution is sought in a weighted
space `C_η((0, T]; X)` of a better space `X`.

The map `u ↦ (t ↦ t^η • u t)` identifies `C_η((0, T]; X)` isometrically with the bounded
continuous functions on `(0, T]` (`TauCeti.TimeWeighted.weightedₗᵢ`); this defines the norm, and
makes `C_η((0, T]; X)` a Banach space when `X` is. When `X` is a real normed space, elements are
coerced to functions `ℝ → X`, vanishing off `(0, T]`.

A continuous bilinear map `B : E × F → G` acts pointwise on time-weighted functions, and the
weights multiply: `t ↦ B (u t) (v t)` lies in `C_{η₁ + η₂}((0, T]; G)` for `u ∈ C_{η₁}((0, T]; E)`
and `v ∈ C_{η₂}((0, T]; F)`, with `‖B (u, v)‖ ≤ ‖B‖ ‖u‖ ‖v‖`. Applied to the product of Besov
distributions of negative and positive regularity
(`TauCeti.BesovSpace.exists_norm_timeWeighted_bilinear_smulL_apply_apply_le`), this is the
local-in-time weighted form of the product map `𝒞^α × 𝒞^β → 𝒞^α`.

## Main declarations

* `TauCeti.TimeWeighted T η X`: the space `C_η((0, T]; X)`, a normed space over every normed field
  acting on `X`, complete when `X` is.
* `TauCeti.TimeWeighted.rpow_mul_norm_le` and `TauCeti.TimeWeighted.norm_le_iff`: the norm is the
  weighted supremum `sup_{0 < t ≤ T} t^η ‖u t‖`.
* `TauCeti.TimeWeighted.continuousOn`: the elements are continuous on `(0, T]`, and
  `TauCeti.TimeWeighted.mk` builds an element from a function continuous on `(0, T]` with a bound
  on its weighted norm.
* `TauCeti.TimeWeighted.bilinear`: the pointwise action
  `C_{η₁}((0, T]; E) × C_{η₂}((0, T]; F) → C_{η₁ + η₂}((0, T]; G)` of a continuous bilinear map,
  with `TauCeti.TimeWeighted.bilinear_apply` and `TauCeti.TimeWeighted.norm_bilinear_le`.

## References

* G. Da Prato, A. Debussche, *Strong solutions to the stochastic quantization equations*, Ann.
  Probab. **31** (2003), 1900–1916 (the weighted spaces of continuous functions on `(0, T]` with
  values in Besov spaces).
* J.-C. Mourrat, H. Weber, *Global well-posedness of the dynamic `Φ⁴` model in the plane*, Ann.
  Probab. **45** (2017), 2398–2476 (products in such weighted spaces).
-/

public section

noncomputable section

open Set
open scoped BoundedContinuousFunction

namespace TauCeti

/-- The space `C_η((0, T]; X)` of continuous maps `u : (0, T] → X` with finite weighted norm
`sup_{0 < t ≤ T} t^η ‖u t‖`. An element is stored as its weighted function `t ↦ t^η • u t`, a
bounded continuous function on `(0, T]` (`TauCeti.TimeWeighted.toWeighted`), and, when `X` is a
real normed space, is coerced to the function `ℝ → X` given by `u t` on `(0, T]` and by `0`
elsewhere. -/
def TimeWeighted (T _η : ℝ) (X : Type*) [NormedAddCommGroup X] : Type _ :=
  Ioc (0 : ℝ) T →ᵇ X

namespace TimeWeighted

variable {T η : ℝ} {X : Type*} [NormedAddCommGroup X]

instance : NormedAddCommGroup (TimeWeighted T η X) :=
  inferInstanceAs (NormedAddCommGroup (Ioc (0 : ℝ) T →ᵇ X))

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] : NormedSpace 𝕜 (TimeWeighted T η X) :=
  inferInstanceAs (NormedSpace 𝕜 (Ioc (0 : ℝ) T →ᵇ X))

instance [CompleteSpace X] : CompleteSpace (TimeWeighted T η X) :=
  inferInstanceAs (CompleteSpace (Ioc (0 : ℝ) T →ᵇ X))

/-- The weighted function `t ↦ t^η • u t` of `u ∈ C_η((0, T]; X)`, a bounded continuous function
on `(0, T]`. -/
def toWeighted (u : TimeWeighted T η X) : Ioc (0 : ℝ) T →ᵇ X :=
  u

/-- The element of `C_η((0, T]; X)` with weighted function `w`, that is `u t = t^{-η} • w t`. -/
def ofWeighted (w : Ioc (0 : ℝ) T →ᵇ X) : TimeWeighted T η X :=
  w

@[simp]
theorem toWeighted_ofWeighted (w : Ioc (0 : ℝ) T →ᵇ X) :
    toWeighted (ofWeighted w : TimeWeighted T η X) = w :=
  (rfl)

@[simp]
theorem ofWeighted_toWeighted (u : TimeWeighted T η X) : ofWeighted (toWeighted u) = u :=
  (rfl)

@[simp]
theorem norm_toWeighted (u : TimeWeighted T η X) : ‖toWeighted u‖ = ‖u‖ :=
  (rfl)

variable (T η X) in
/-- The weighted function `u ↦ (t ↦ t^η • u t)` as a linear isometric isomorphism of
`C_η((0, T]; X)` with the bounded continuous functions on `(0, T]`. -/
def weightedₗᵢ (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 X] :
    TimeWeighted T η X ≃ₗᵢ[𝕜] (Ioc (0 : ℝ) T →ᵇ X) where
  toFun := toWeighted
  invFun := ofWeighted
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  left_inv _ := (rfl)
  right_inv _ := (rfl)
  norm_map' _ := (rfl)

@[simp]
theorem coe_weightedₗᵢ (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 X] :
    ⇑(weightedₗᵢ T η X 𝕜) = toWeighted :=
  (rfl)

@[simp]
theorem coe_weightedₗᵢ_symm (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 X] :
    ⇑(weightedₗᵢ T η X 𝕜).symm = ofWeighted :=
  (rfl)

@[simp]
theorem toWeighted_zero : toWeighted (0 : TimeWeighted T η X) = 0 :=
  (rfl)

@[simp]
theorem toWeighted_add (u v : TimeWeighted T η X) :
    toWeighted (u + v) = toWeighted u + toWeighted v :=
  (rfl)

@[simp]
theorem toWeighted_neg (u : TimeWeighted T η X) : toWeighted (-u) = -toWeighted u :=
  (rfl)

@[simp]
theorem toWeighted_sub (u v : TimeWeighted T η X) :
    toWeighted (u - v) = toWeighted u - toWeighted v :=
  (rfl)

@[simp]
theorem toWeighted_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] (c : 𝕜)
    (u : TimeWeighted T η X) : toWeighted (c • u) = c • toWeighted u :=
  (rfl)

theorem toWeighted_injective : Function.Injective (toWeighted : TimeWeighted T η X → _) :=
  fun _ _ h ↦ h

/-- The weight `t ↦ t^η` is continuous on `(0, T]`. -/
private theorem continuous_rpow_Ioc : Continuous fun t : Ioc (0 : ℝ) T ↦ (t : ℝ) ^ η :=
  continuous_subtypeVal.rpow_const fun t ↦ Or.inl t.property.1.ne'

variable [NormedSpace ℝ X]

/-- The value `u t = t^{-η} • w t` of `u ∈ C_η((0, T]; X)` with weighted function `w`, for
`t ∈ (0, T]`, and `0` elsewhere. -/
instance : FunLike (TimeWeighted T η X) ℝ X where
  coe u t := if h : t ∈ Ioc (0 : ℝ) T then (t ^ η)⁻¹ • toWeighted u ⟨t, h⟩ else 0
  coe_injective u v h := toWeighted_injective <| BoundedContinuousFunction.ext fun t ↦ by
    have := congr_fun h t
    simp only [Subtype.coe_prop, dite_true] at this
    exact smul_right_injective X (inv_ne_zero (Real.rpow_pos_of_pos t.property.1 η).ne') this

theorem apply_of_mem (u : TimeWeighted T η X) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    u t = (t ^ η)⁻¹ • toWeighted u ⟨t, ht⟩ :=
  dite_eq_left ht

@[simp]
theorem apply_of_notMem (u : TimeWeighted T η X) {t : ℝ} (ht : t ∉ Ioc (0 : ℝ) T) : u t = 0 :=
  dite_eq_right ht

/-- The weighted function of `u` at `t ∈ (0, T]` is `t^η • u t`. -/
@[simp]
theorem toWeighted_apply (u : TimeWeighted T η X) (t : Ioc (0 : ℝ) T) :
    toWeighted u t = (t : ℝ) ^ η • u t := by
  rw [apply_of_mem u t.property, smul_inv_smul₀ (Real.rpow_pos_of_pos t.property.1 η).ne']

/-- The norm of the weighted function of `u` at `t ∈ (0, T]` is `t^η ‖u t‖`. -/
theorem norm_toWeighted_apply (u : TimeWeighted T η X) (t : Ioc (0 : ℝ) T) :
    ‖toWeighted u t‖ = (t : ℝ) ^ η * ‖u t‖ := by
  rw [toWeighted_apply, norm_smul_of_nonneg (Real.rpow_nonneg t.property.1.le η)]

@[ext]
theorem ext {u v : TimeWeighted T η X} (h : ∀ t ∈ Ioc (0 : ℝ) T, u t = v t) : u = v :=
  toWeighted_injective <| BoundedContinuousFunction.ext fun t ↦ by
    rw [toWeighted_apply, toWeighted_apply, h t t.property]

instance : IsZeroApply (TimeWeighted T η X) where
  zero_apply t := by
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · rw [apply_of_mem _ ht, toWeighted_zero, zero_apply, smul_zero]
    · rw [apply_of_notMem _ ht]

instance : IsAddApply (TimeWeighted T η X) where
  add_apply u v t := by
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · rw [apply_of_mem _ ht, apply_of_mem _ ht, apply_of_mem _ ht, toWeighted_add, add_apply,
        smul_add]
    · rw [apply_of_notMem _ ht, apply_of_notMem _ ht, apply_of_notMem _ ht, add_zero]

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 X] [SMulCommClass ℝ 𝕜 X] :
    IsSMulApply 𝕜 (TimeWeighted T η X) where
  smul_apply u c t := by
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · rw [apply_of_mem _ ht, apply_of_mem _ ht, toWeighted_smul, smul_apply, smul_comm]
    · rw [apply_of_notMem _ ht, apply_of_notMem _ ht, smul_zero]

instance : IsNegApply (TimeWeighted T η X) where
  neg_apply u t := by rw [← neg_one_smul ℝ u, smul_apply, neg_one_smul]

instance : IsSubApply (TimeWeighted T η X) where
  sub_apply u v t := by rw [sub_eq_add_neg, add_apply, neg_apply, sub_eq_add_neg]

/-- The weighted values are bounded by the norm: `t^η ‖u t‖ ≤ ‖u‖` for `0 < t ≤ T`. -/
theorem rpow_mul_norm_le (u : TimeWeighted T η X) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    t ^ η * ‖u t‖ ≤ ‖u‖ := by
  have h := (toWeighted u).norm_coe_le_norm ⟨t, ht⟩
  rwa [norm_toWeighted_apply, norm_toWeighted] at h

/-- **The weighted norm.** `‖u‖ = sup_{0 < t ≤ T} t^η ‖u t‖`: the norm is at most `C ≥ 0` exactly
when every weighted value is. -/
theorem norm_le_iff (u : TimeWeighted T η X) {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ ∀ t ∈ Ioc (0 : ℝ) T, t ^ η * ‖u t‖ ≤ C := by
  refine ⟨fun h t ht ↦ (u.rpow_mul_norm_le ht).trans h, fun h ↦ ?_⟩
  rw [← norm_toWeighted, BoundedContinuousFunction.norm_le hC]
  intro t
  rw [norm_toWeighted_apply]
  exact h t t.property

/-- The elements of `C_η((0, T]; X)` are continuous on `(0, T]`. -/
theorem continuousOn (u : TimeWeighted T η X) : ContinuousOn u (Ioc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hw : Continuous fun t : Ioc (0 : ℝ) T ↦ ((t : ℝ) ^ η)⁻¹ • toWeighted u t :=
    (continuous_rpow_Ioc.inv₀ fun t ↦ (Real.rpow_pos_of_pos t.property.1 η).ne').smul
      (toWeighted u).continuous
  exact hw.congr fun t ↦ (apply_of_mem u t.property).symm

/-- The element of `C_η((0, T]; X)` given on `(0, T]` by a function `f` continuous there with
weighted values `t^η ‖f t‖ ≤ C`. -/
def mk (f : ℝ → X) (hf : ContinuousOn f (Ioc (0 : ℝ) T)) (C : ℝ)
    (hC : ∀ t ∈ Ioc (0 : ℝ) T, t ^ η * ‖f t‖ ≤ C) : TimeWeighted T η X :=
  ofWeighted <| BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : Ioc (0 : ℝ) T ↦ (t : ℝ) ^ η • f t)
    (continuous_rpow_Ioc.smul hf.domRestrict) C fun t ↦ by
      rw [norm_smul_of_nonneg (Real.rpow_nonneg t.property.1.le η)]
      exact hC t t.property

@[simp]
theorem mk_apply_of_mem {f : ℝ → X} (hf : ContinuousOn f (Ioc (0 : ℝ) T)) {C : ℝ}
    (hC : ∀ t ∈ Ioc (0 : ℝ) T, t ^ η * ‖f t‖ ≤ C) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    mk f hf C hC t = f t := by
  rw [apply_of_mem _ ht]
  exact inv_smul_smul₀ (Real.rpow_pos_of_pos ht.1 η).ne' (f t)

theorem norm_mk_le {f : ℝ → X} (hf : ContinuousOn f (Ioc (0 : ℝ) T)) {C : ℝ}
    (hC : ∀ t ∈ Ioc (0 : ℝ) T, t ^ η * ‖f t‖ ≤ C) (hC₀ : 0 ≤ C) : ‖mk f hf C hC‖ ≤ C :=
  ((mk f hf C hC).norm_le_iff hC₀).2 fun t ht ↦ by rw [mk_apply_of_mem hf hC ht]; exact hC t ht

section Bilinear

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {η₁ η₂ : ℝ}

variable (T η₁ η₂) in
/-- **Products of time-weighted functions.** A continuous bilinear map `B : E × F → G` acts
pointwise, `(u, v) ↦ (t ↦ B (u t) (v t))` (`TauCeti.TimeWeighted.bilinear_apply`), as a continuous
bilinear map `C_{η₁}((0, T]; E) × C_{η₂}((0, T]; F) → C_{η₁ + η₂}((0, T]; G)`: the blow-up rates at
`t = 0` add up. -/
def bilinear (B : E →L[𝕜] F →L[𝕜] G) :
    TimeWeighted T η₁ E →L[𝕜] TimeWeighted T η₂ F →L[𝕜] TimeWeighted T (η₁ + η₂) G :=
  ContinuousLinearMap.compL 𝕜 _ _ _
      (weightedₗᵢ T (η₁ + η₂) G 𝕜).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (B.compLeftContinuousBounded₂ _).bilinearComp
      (weightedₗᵢ T η₁ E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
      (weightedₗᵢ T η₂ F 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

/-- The weighted function of a product is the pointwise product of the weighted functions:
`t^{η₁ + η₂} • B (u t) (v t) = B (t^{η₁} • u t) (t^{η₂} • v t)`. -/
theorem toWeighted_bilinear_apply_apply (B : E →L[𝕜] F →L[𝕜] G)
    (u : TimeWeighted T η₁ E) (v : TimeWeighted T η₂ F) (t : Ioc (0 : ℝ) T) :
    toWeighted (bilinear T η₁ η₂ B u v) t = B (toWeighted u t) (toWeighted v t) := by
  simp [bilinear]

/-- **The product estimate in time-weighted spaces.** `‖B (u, v)‖ ≤ ‖B‖ ‖u‖ ‖v‖`. -/
theorem norm_bilinear_apply_apply_le (B : E →L[𝕜] F →L[𝕜] G) (u : TimeWeighted T η₁ E)
    (v : TimeWeighted T η₂ F) : ‖bilinear T η₁ η₂ B u v‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ := by
  rw [← norm_toWeighted, ← norm_toWeighted u, ← norm_toWeighted v]
  exact B.norm_compLeftContinuousBounded₂_apply_apply_le (toWeighted u) (toWeighted v)

/-- The pointwise product has operator norm at most `‖B‖`. -/
theorem norm_bilinear_le (B : E →L[𝕜] F →L[𝕜] G) : ‖bilinear T η₁ η₂ B‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg B) (norm_bilinear_apply_apply_le B)

/-- The weights multiply: `(t^{η₁ + η₂})⁻¹ (t^{η₁} t^{η₂}) = 1` for `t > 0`. -/
private theorem rpow_add_inv_mul_rpow_mul_rpow {t : ℝ} (ht : 0 < t) :
    (t ^ (η₁ + η₂))⁻¹ * (t ^ η₁ * t ^ η₂) = 1 := by
  rw [Real.rpow_add ht]
  exact inv_mul_cancel₀ (mul_pos (Real.rpow_pos_of_pos ht η₁) (Real.rpow_pos_of_pos ht η₂)).ne'

variable [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F]
  [IsScalarTower ℝ 𝕜 F] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]

/-- The product of time-weighted functions is the pointwise product. -/
@[simp]
theorem bilinear_apply (B : E →L[𝕜] F →L[𝕜] G) (u : TimeWeighted T η₁ E)
    (v : TimeWeighted T η₂ F) (t : ℝ) : bilinear T η₁ η₂ B u v t = B (u t) (v t) := by
  by_cases ht : t ∈ Ioc (0 : ℝ) T
  · rw [apply_of_mem _ ht, toWeighted_bilinear_apply_apply]
    simp [ContinuousLinearMap.map_smul_of_tower, smul_smul, rpow_add_inv_mul_rpow_mul_rpow ht.1]
  · simp [apply_of_notMem _ ht]

end Bilinear

end TimeWeighted

end TauCeti
