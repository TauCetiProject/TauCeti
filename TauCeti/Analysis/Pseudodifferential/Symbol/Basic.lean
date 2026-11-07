/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# The symbol classes `S^m_{1,0}`

For a real order `m` and complex normed spaces `V`, `W`, a (local) symbol of order `m` is a
smooth map `a : ℝⁿ × ℝⁿ → (V →L[ℂ] W)`, `(x, ξ) ↦ a(x, ξ)`, such that on every compact set `K` of
positions, every mixed derivative satisfies the Hörmander estimate

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{K,α,β} ⟨ξ⟩^(m - |β|)` for `x ∈ K` and all `ξ`,

where `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. Every derivative in the frequency variable `ξ` gains one order
of decay, while derivatives in the position variable `x` cost nothing. These symbols are the
coefficients of pseudodifferential operators: the quantization of `a` is
`u ↦ (2π)^(-n) ∫∫ e^{i(x-y)·ξ} a(x, ξ) u(y) dy dξ`.

We define the class `TauCeti.Symbol n V W m` of these symbols, show that it is a complex vector
space, and develop the first operations of the symbol calculus:

* `TauCeti.Symbol.inclusion`: a symbol of order `m` is a symbol of every order `m' ≥ m`;
* `TauCeti.Symbol.frequencyDeriv`: a frequency derivative `∂_{ξ_j}` lowers the order by one;
* `TauCeti.Symbol.spatialDeriv`: a spatial derivative `∂_{x_j}` preserves the order;
* `TauCeti.Symbol.ofSpatial`: a smooth coefficient `f(x)` independent of the frequency, the symbol
  of multiplication by `f`, has order `0`; in particular so does a constant
  (`TauCeti.Symbol.const`);
* `TauCeti.Symbol.comp`: the pointwise composition `b(x, ξ) ∘ a(x, ξ)` (for matrices, the matrix
  product) of symbols of orders `m'` and `m` has order `m' + m`. By the Leibniz rule
  `ContinuousLinearMap.mixedDeriv_of_bilinear`, `∂_x^α ∂_ξ^β (b ∘ a)` is a sum of terms
  `∂_x^{α₁} ∂_ξ^{β₁} b ∘ ∂_x^{α₂} ∂_ξ^{β₂} a`, each of size
  `⟨ξ⟩^(m' - |β₁|) ⟨ξ⟩^(m - |β₂|) = ⟨ξ⟩^(m' + m - |β|)`.

A symbol is *smoothing* (`TauCeti.Symbol.IsSmoothing`) if it is a symbol of every order. Smoothing
symbols are closed under the operations above, and they form a two-sided ideal under composition
(`TauCeti.Symbol.IsSmoothing.comp_right`, `TauCeti.Symbol.IsSmoothing.comp_left`). A smooth
coefficient vanishing at all large frequencies is smoothing
(`TauCeti.Symbol.isSmoothing_ofBoundedFrequencySupport`), while in positive dimension a nonzero
constant is not (`TauCeti.Symbol.isSmoothing_const_iff`).

The estimates are only required locally uniformly in `x`. The predicate
`TauCeti.Symbol.IsUniform` asks for constants independent of `x`, and
`TauCeti.Symbol.HasCompactSpatialSupport` asks that the symbol vanish for `x` outside a fixed
compact set. Symbols with compact spatial support are uniform
(`TauCeti.Symbol.HasCompactSpatialSupport.isUniform`). The symbol of multiplication by `f` is
uniform exactly when all derivatives of `f` are bounded (`TauCeti.Symbol.isUniform_ofSpatial_iff`),
so the local estimates alone do not give uniform ones: a coordinate function `x_j` is a symbol of
order `0` that is not uniform (`TauCeti.Symbol.not_isUniform_ofSpatial_smul`).

The mixed derivative `TauCeti.mixedDeriv α β a x ξ`, defined with the coordinate derivatives,
takes the frequency derivatives first. For smooth `a` the two kinds of derivatives commute
(`TauCeti.mixedDeriv_eq_coordinateDeriv_snd`), which is what makes spatial derivatives of symbols
symbols of the same order.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.1.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

variable {n : ℕ}

/-- The weight `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)` is monotone in the exponent. -/
theorem rpow_weight_le_rpow_weight (ξ : CoordinateSpace n) {t t' : ℝ} (h : t ≤ t') :
    (1 + ‖ξ‖ ^ 2) ^ (t / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (t' / 2) :=
  Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

/-- The weight `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)` is positive. -/
theorem rpow_weight_pos (ξ : CoordinateSpace n) (t : ℝ) :
    0 < (1 + ‖ξ‖ ^ 2) ^ (t / 2) :=
  Real.rpow_pos_of_pos (by positivity) _

variable (n) in
/-- The class `S^m_{1,0}` of symbols of order `m` on `ℝⁿ × ℝⁿ` with values in `V →L[ℂ] W`: smooth
maps `a` such that on every compact set `K` of positions and for all words `α`, `β` of coordinate
indices, `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for some `C`, all `x ∈ K` and all
frequencies `ξ`, where `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)`. -/
@[ext]
structure Symbol (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] (m : ℝ) where
  /-- The coefficient `a(x, ξ)` of the symbol at the position `x` and the frequency `ξ`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  contDiff_coefficient : ContDiff ℝ ∞ coefficient
  exists_bound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

theorem coefficient_injective :
    Function.Injective (coefficient : Symbol n V W m → CoordinateSpace n × CoordinateSpace n → _) :=
  fun _ _ h => Symbol.ext h

/-- A symbol of order `m` has the growth bound `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` uniformly for `x` in each
compact set. -/
theorem exists_norm_coefficient_le (a : Symbol n V W m) (K : Set (CoordinateSpace n))
    (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound K hK [] []
  exact ⟨C, fun x hx ξ ↦ by simpa using hC x hx ξ⟩

/-- Each frequency slice `ξ ↦ a(x, ξ)` of a symbol is continuous. -/
theorem continuous_coefficient_slice (a : Symbol n V W m) (x : CoordinateSpace n) :
    Continuous fun ξ ↦ a.coefficient (x, ξ) :=
  a.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)

/-- A symbol satisfies its estimates with constants uniform in the position. -/
def IsUniform (a : Symbol n V W m) : Prop :=
  ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

/-- A symbol has compact spatial support if it vanishes, for every frequency, at every position
outside some compact set. -/
def HasCompactSpatialSupport (a : Symbol n V W m) : Prop :=
  ∃ K : Set (CoordinateSpace n), IsCompact K ∧ ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0

theorem isUniform_iff {a : Symbol n V W m} :
    a.IsUniform ↔ ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) :=
  Iff.rfl

theorem hasCompactSpatialSupport_iff {a : Symbol n V W m} :
    a.HasCompactSpatialSupport ↔
      ∃ K : Set (CoordinateSpace n), IsCompact K ∧ ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0 :=
  Iff.rfl

/-- A symbol with compact spatial support satisfies its estimates uniformly in the position:
outside the support all its mixed derivatives vanish. -/
theorem HasCompactSpatialSupport.isUniform {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) : a.IsUniform := by
  obtain ⟨K, hK, hKa⟩ := ha
  intro α β
  obtain ⟨C, hC, hCK⟩ := a.exists_bound K hK α β
  refine ⟨C, hC, fun x ξ => ?_⟩
  by_cases hx : x ∈ K
  · exact hCK x hx ξ
  · have hzero : ∀ᶠ y in nhds x, ∀ η, a.coefficient (y, η) = 0 :=
      Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hKa y hy
    rw [mixedDeriv_eq_zero_of_eventually hzero, norm_zero]
    exact mul_nonneg hC (rpow_weight_pos ξ _).le

/-- A symbol of order `m` is bounded by `C ⟨ξ⟩ ^ m` locally uniformly in the position. -/
theorem exists_bound_coefficient (a : Symbol n V W m) (K : Set (CoordinateSpace n))
    (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC, hCK⟩ := a.exists_bound K hK [] []
  exact ⟨C, hC, fun x hx ξ ↦ by simpa [mixedDeriv_nil_nil] using hCK x hx ξ⟩

section Module

instance : Zero (Symbol n V W m) where
  zero :=
    { coefficient := 0
      contDiff_coefficient := contDiff_const
      exists_bound := fun _ _ α β => ⟨0, le_rfl, fun x ξ => by simp⟩ }

instance : Add (Symbol n V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      contDiff_coefficient := a.contDiff_coefficient.add b.contDiff_coefficient
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK α β
        obtain ⟨D, hD, hb⟩ := b.exists_bound K hK α β
        exact ⟨C + D, add_nonneg hC hD, fun x hx ξ => norm_mixedDeriv_add_le
          a.contDiff_coefficient b.contDiff_coefficient (ha x hx ξ) (hb x hx ξ)⟩ }

instance : SMul ℂ (Symbol n V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      contDiff_coefficient := a.contDiff_coefficient.const_smul c
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK α β
        exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x hx ξ =>
          norm_mixedDeriv_smul_le a.contDiff_coefficient c (ha x hx ξ)⟩ }

instance : Neg (Symbol n V W m) where
  neg a :=
    { coefficient := -a.coefficient
      contDiff_coefficient := a.contDiff_coefficient.neg
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK α β
        exact ⟨C, hC, fun x hx ξ => by
          rw [mixedDeriv_neg, norm_neg]
          exact ha x hx ξ⟩ }

instance : Sub (Symbol n V W m) where
  sub a b := a + -b

instance : SMul ℕ (Symbol n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (Symbol n V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : Symbol n V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : Symbol n V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : Symbol n V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : Symbol n V W m) : (-a).coefficient = -a.coefficient := (rfl)

@[simp]
theorem coefficient_sub (a b : Symbol n V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : Symbol n V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : Symbol n V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (Symbol n V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (Symbol n V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

theorem IsUniform.add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a + b).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha α β
  obtain ⟨D, hD, hDb⟩ := hb α β
  exact ⟨C + D, add_nonneg hC hD, fun x ξ => norm_mixedDeriv_add_le
    a.contDiff_coefficient b.contDiff_coefficient (hCa x ξ) (hDb x ξ)⟩

theorem IsUniform.smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) : (c • a).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha α β
  exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x ξ =>
    norm_mixedDeriv_smul_le a.contDiff_coefficient c (hCa x ξ)⟩

theorem isUniform_zero : (0 : Symbol n V W m).IsUniform :=
  fun _ _ => ⟨0, le_rfl, fun x ξ => by simp⟩

theorem hasCompactSpatialSupport_zero : (0 : Symbol n V W m).HasCompactSpatialSupport :=
  ⟨∅, isCompact_empty, fun _ _ _ => rfl⟩

theorem HasCompactSpatialSupport.add {a b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) : (a + b).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := ha
  obtain ⟨L, hL, hLb⟩ := hb
  refine ⟨K ∪ L, hK.union hL, fun x hx ξ => ?_⟩
  rw [Set.mem_union, not_or] at hx
  simp [hKa x hx.1 ξ, hLb x hx.2 ξ]

theorem HasCompactSpatialSupport.smul {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (c : ℂ) : (c • a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := ha
  exact ⟨K, hK, fun x hx ξ => by simp [hKa x hx ξ]⟩

end Module

section Inclusion

/-- A symbol of order `m` is a symbol of every order `m' ≥ m`, since `⟨ξ⟩ ≥ 1`. -/
def inclusion (h : m ≤ m') : Symbol n V W m →ₗ[ℂ] Symbol n V W m' where
  toFun a :=
    { coefficient := a.coefficient
      contDiff_coefficient := a.contDiff_coefficient
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK α β
        refine ⟨C, hC, fun x hx ξ => (ha x hx ξ).trans ?_⟩
        exact mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ (by linarith)) hC }
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_inclusion (h : m ≤ m') (a : Symbol n V W m) :
    (inclusion h a).coefficient = a.coefficient := (rfl)

theorem inclusion_injective (h : m ≤ m') :
    Function.Injective (inclusion (n := n) (V := V) (W := W) h) :=
  fun _ _ hab => Symbol.ext (by simpa using congrArg Symbol.coefficient hab)

theorem IsUniform.inclusion {a : Symbol n V W m} (ha : a.IsUniform) (h : m ≤ m') :
    (inclusion h a).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha α β
  refine ⟨C, hC, fun x ξ => (hCa x ξ).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ (by linarith)) hC

theorem HasCompactSpatialSupport.inclusion {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (h : m ≤ m') : (inclusion h a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := ha
  exact ⟨K, hK, fun x hx ξ => by rw [coefficient_inclusion, hKa x hx ξ]⟩

end Inclusion

section Deriv

/-- One more frequency derivative lowers the order of the weight by one. -/
theorem order_sub_one_sub_length (m : ℝ) (β : List (Fin n)) (j : Fin n) :
    m - 1 - (β.length : ℝ) = m - ((β ++ [j]).length : ℝ) := by
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  ring

/-- The frequency derivative `∂_{ξ_j} a` of a symbol of order `m`, a symbol of order `m - 1`. -/
def frequencyDeriv (j : Fin n) : Symbol n V W m →ₗ[ℂ] Symbol n V W (m - 1) where
  toFun a :=
    { coefficient := fun p => coordinateDeriv [j] (fun η => a.coefficient (p.1, η)) p.2
      contDiff_coefficient := a.contDiff_coefficient.coordinateDeriv_snd [j]
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK α (β ++ [j])
        refine ⟨C, hC, fun x hx ξ => ?_⟩
        rw [mixedDeriv_coordinateDeriv_snd, order_sub_one_sub_length]
        exact ha x hx ξ }
  map_add' a b := by
    ext1
    funext p
    exact congrFun (coordinateDeriv_add [j]
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_right p.1)) _)
      (contDiff_infty.1 (b.contDiff_coefficient.comp (contDiff_prodMk_right p.1)) _)) p.2
  map_smul' c a := by
    ext1
    funext p
    exact congrFun (coordinateDeriv_const_smul [j]
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_right p.1)) _) c) p.2

@[simp]
theorem coefficient_frequencyDeriv (j : Fin n) (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (frequencyDeriv j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun η => a.coefficient (x, η)) ξ := (rfl)

/-- The mixed derivatives of `∂_{ξ_j} a` are those of `a` with one more frequency derivative. -/
@[simp]
theorem mixedDeriv_frequencyDeriv (j : Fin n) (a : Symbol n V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (frequencyDeriv j a).coefficient x ξ =
      mixedDeriv α (β ++ [j]) a.coefficient x ξ := by
  have h : (frequencyDeriv j a).coefficient =
      fun p => coordinateDeriv [j] (fun η => a.coefficient (p.1, η)) p.2 :=
    funext fun p => coefficient_frequencyDeriv j a p.1 p.2
  rw [h, mixedDeriv_coordinateDeriv_snd]

/-- The spatial derivative `∂_{x_j} a` of a symbol of order `m`, again a symbol of order `m`. -/
def spatialDeriv (j : Fin n) : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := fun p => coordinateDeriv [j] (fun y => a.coefficient (y, p.2)) p.1
      contDiff_coefficient := a.contDiff_coefficient.coordinateDeriv_fst [j]
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC, ha⟩ := a.exists_bound K hK (α ++ [j]) β
        exact ⟨C, hC, fun x hx ξ => by
          rw [mixedDeriv_coordinateDeriv_fst a.contDiff_coefficient]
          exact ha x hx ξ⟩ }
  map_add' a b := by
    ext1
    funext p
    exact congrFun (coordinateDeriv_add [j]
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_left p.2)) _)
      (contDiff_infty.1 (b.contDiff_coefficient.comp (contDiff_prodMk_left p.2)) _)) p.1
  map_smul' c a := by
    ext1
    funext p
    exact congrFun (coordinateDeriv_const_smul [j]
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_left p.2)) _) c) p.1

@[simp]
theorem coefficient_spatialDeriv (j : Fin n) (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (spatialDeriv j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun y => a.coefficient (y, ξ)) x := (rfl)

/-- The mixed derivatives of `∂_{x_j} a` are those of `a` with one more position derivative. -/
@[simp]
theorem mixedDeriv_spatialDeriv (j : Fin n) (a : Symbol n V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (spatialDeriv j a).coefficient x ξ =
      mixedDeriv (α ++ [j]) β a.coefficient x ξ := by
  have h : (spatialDeriv j a).coefficient =
      fun p => coordinateDeriv [j] (fun y => a.coefficient (y, p.2)) p.1 :=
    funext fun p => coefficient_spatialDeriv j a p.1 p.2
  rw [h, mixedDeriv_coordinateDeriv_fst a.contDiff_coefficient]

/-- The position derivative of a symbol in the `j`-th coordinate direction is the coefficient of
its spatial derivative `∂_{x_j} a`. -/
theorem fderiv_coefficient_single (a : Symbol n V W m) (j : Fin n) (x ξ : CoordinateSpace n) :
    fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x (EuclideanSpace.single j 1) =
      (spatialDeriv j a).coefficient (x, ξ) := by
  rw [coefficient_spatialDeriv, coordinateDeriv_cons, coordinateDeriv_nil]

/-- The position derivative of a symbol of order `m` is bounded by `C ⟨ξ⟩ ^ m` locally uniformly in
the position. -/
theorem exists_bound_fderiv_coefficient (a : Symbol n V W m) (K : Set (CoordinateSpace n))
    (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ ξ,
      ‖fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose C hC0 hC using fun j ↦ (spatialDeriv j a).exists_bound_coefficient K hK
  obtain ⟨D, -, hD⟩ :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.exists_opNorm_le (F := V →L[ℂ] W)
  refine ⟨D * ∑ j, C j, fun x hx ξ ↦ ?_⟩
  rw [mul_assoc]
  refine hD (mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)) fun j ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, fderiv_coefficient_single]
  refine (hC j x hx ξ).trans ?_
  gcongr
  exact Finset.single_le_sum (fun i _ ↦ hC0 i) (Finset.mem_univ j)

theorem IsUniform.frequencyDeriv {a : Symbol n V W m} (ha : a.IsUniform) (j : Fin n) :
    (frequencyDeriv j a).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha α (β ++ [j])
  refine ⟨C, hC, fun x ξ => ?_⟩
  rw [mixedDeriv_frequencyDeriv, order_sub_one_sub_length]
  exact hCa x ξ

theorem IsUniform.spatialDeriv {a : Symbol n V W m} (ha : a.IsUniform) (j : Fin n) :
    (spatialDeriv j a).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha (α ++ [j]) β
  refine ⟨C, hC, fun x ξ => ?_⟩
  rw [mixedDeriv_spatialDeriv]
  exact hCa x ξ

theorem HasCompactSpatialSupport.frequencyDeriv {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (j : Fin n) :
    (frequencyDeriv j a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := ha
  refine ⟨K, hK, fun x hx ξ => ?_⟩
  rw [coefficient_frequencyDeriv, show (fun η => a.coefficient (x, η)) = 0 from funext (hKa x hx),
    coordinateDeriv_zero, Pi.zero_apply]

theorem HasCompactSpatialSupport.spatialDeriv {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (j : Fin n) :
    (spatialDeriv j a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := ha
  refine ⟨K, hK, fun x hx ξ => ?_⟩
  have h : (fun y => a.coefficient (y, ξ)) =ᶠ[nhds x] 0 :=
    Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hKa y hy ξ
  rw [coefficient_spatialDeriv, (h.coordinateDeriv [j]).eq_of_nhds, coordinateDeriv_zero,
    Pi.zero_apply]

end Deriv

section Spatial

/-- The order-zero weight with no frequency derivative is `1`. -/
private theorem rpow_weight_zero (ξ : CoordinateSpace n) :
    (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - ([] : List (Fin n)).length) / 2) = 1 := by
  simp

/-- A smooth frequency-independent coefficient `a(x, ξ) = f(x)`, the symbol of multiplication by
`f`, is a symbol of order `0`. -/
def ofSpatial (f : CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f) : Symbol n V W 0 where
  coefficient := fun p => f p.1
  contDiff_coefficient := hf.comp contDiff_fst
  exists_bound := fun K hK α β => by
    rcases eq_or_ne β [] with rfl | hβ
    · obtain ⟨C, hC⟩ :=
        hK.exists_bound_of_continuousOn (hf.coordinateDeriv α).continuous.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
      rw [mixedDeriv_nil_comp_fst, rpow_weight_zero, mul_one]
      exact (hC x hx).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun x _ ξ => by simp [mixedDeriv_comp_fst f α hβ]⟩

@[simp]
theorem coefficient_ofSpatial (f : CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f)
    (p : CoordinateSpace n × CoordinateSpace n) : (ofSpatial f hf).coefficient p = f p.1 := (rfl)

/-- The symbol of multiplication by `f` satisfies uniform estimates exactly when every
coordinate derivative of `f` is bounded. -/
theorem isUniform_ofSpatial_iff {f : CoordinateSpace n → V →L[ℂ] W} (hf : ContDiff ℝ ∞ f) :
    (ofSpatial f hf).IsUniform ↔ ∀ α : List (Fin n), ∃ C, ∀ x, ‖coordinateDeriv α f x‖ ≤ C := by
  have hc : (ofSpatial f hf).coefficient = fun p => f p.1 := funext (coefficient_ofSpatial f hf)
  refine ⟨fun h α => ?_, fun h α β => ?_⟩
  · obtain ⟨C, -, hC⟩ := h α []
    refine ⟨C, fun x => ?_⟩
    simpa [hc, mixedDeriv_nil_comp_fst, rpow_weight_zero] using hC x 0
  · rcases eq_or_ne β [] with rfl | hβ
    · obtain ⟨C, hC⟩ := h α
      refine ⟨max C 0, le_max_right _ _, fun x ξ => ?_⟩
      rw [hc, mixedDeriv_nil_comp_fst, rpow_weight_zero, mul_one]
      exact (hC x).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun x ξ => by simp [hc, mixedDeriv_comp_fst f α hβ]⟩

/-- The local estimates do not imply the uniform ones: the coordinate function `x_j`, times a
nonzero coefficient `T`, is a symbol of order `0` that is unbounded in the position. -/
theorem not_isUniform_ofSpatial_smul (j : Fin n) {T : V →L[ℂ] W} (hT : T ≠ 0)
    (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n => x j • T) :
    ¬(ofSpatial _ hf).IsUniform := by
  rw [isUniform_ofSpatial_iff]
  intro h
  obtain ⟨C, hC⟩ := h []
  have hT' : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hx := hC (EuclideanSpace.single j ((|C| + 1) / ‖T‖))
  simp only [coordinateDeriv_nil, PiLp.single_apply, ite_true, norm_smul, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hT'.ne'] at hx
  linarith [le_abs_self C]

/-- The constant symbol with coefficient `T`, a symbol of order `0`. -/
def const (T : V →L[ℂ] W) : Symbol n V W 0 :=
  ofSpatial (fun _ => T) contDiff_const

@[simp]
theorem coefficient_const (T : V →L[ℂ] W) (p : CoordinateSpace n × CoordinateSpace n) :
    (const T : Symbol n V W 0).coefficient p = T := (rfl)

/-- A constant symbol satisfies the order-zero estimates uniformly. -/
theorem isUniform_const (T : V →L[ℂ] W) : (const T : Symbol n V W 0).IsUniform := by
  refine (isUniform_ofSpatial_iff contDiff_const).2 fun α => ⟨‖T‖, fun x => ?_⟩
  rcases eq_or_ne α [] with rfl | hα
  · simp
  · simp [coordinateDeriv_const T hα]

end Spatial

section Comp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m'' : ℝ}

/-- The product estimate behind `TauCeti.Symbol.comp`: bounds `C s t ⟨ξ⟩^(m' - |t|)` and
`D s t ⟨ξ⟩^(m - |t|)` on all mixed derivatives of `b` and `a` at `(x, ξ)` bound the mixed
derivative `∂_x^α ∂_ξ^β` of `b ∘ a` by a constant times `⟨ξ⟩^(m' + m - |β|)`. -/
private theorem norm_mixedDeriv_comp_le {b : CoordinateSpace n × CoordinateSpace n → W →L[ℂ] U}
    {a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hb : ContDiff ℝ ∞ b)
    (ha : ContDiff ℝ ∞ a) {x ξ : CoordinateSpace n} {C D : List (Fin n) → List (Fin n) → ℝ}
    (hC : ∀ s t, ‖mixedDeriv s t b x ξ‖ ≤ C s t * (1 + ‖ξ‖ ^ 2) ^ ((m' - t.length) / 2))
    (hD : ∀ s t, ‖mixedDeriv s t a x ξ‖ ≤ D s t * (1 + ‖ξ‖ ^ 2) ^ ((m - t.length) / 2))
    (α β : List (Fin n)) :
    ‖mixedDeriv α β (fun p => (b p).comp (a p)) x ξ‖ ≤
      (β.sublists'.revzip.map fun t =>
        (α.sublists'.revzip.map fun s => C s.1 t.1 * D s.2 t.2).sum).sum *
        (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  -- Composition of `ℂ`-linear maps, viewed as a continuous `ℝ`-bilinear map.
  have h := ((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).mixedDeriv_of_bilinear
    (α := α) (β := β) (hb.of_le (by exact_mod_cast le_top)) (ha.of_le (by exact_mod_cast le_top))
    x ξ
  simp only [ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.compL_apply] at h
  rw [h, ← List.sum_map_mul_right]
  refine (List.le_sum_of_subadditive norm norm_zero.le norm_add_le _).trans ?_
  rw [List.map_map]
  refine List.sum_le_sum fun t ht => ?_
  refine (List.le_sum_of_subadditive norm norm_zero.le norm_add_le _).trans ?_
  rw [List.map_map, ← List.sum_map_mul_right]
  refine List.sum_le_sum fun s _ => ?_
  have hw : (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' - t.1.length) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - t.2.length) / 2) := by
    rw [← Real.rpow_add (by positivity), ← (List.revzip_sublists' _ _ _ ht).length_eq,
      List.length_append]
    push_cast
    ring_nf
  calc ‖(mixedDeriv s.1 t.1 b x ξ).comp (mixedDeriv s.2 t.2 a x ξ)‖
      ≤ ‖mixedDeriv s.1 t.1 b x ξ‖ * ‖mixedDeriv s.2 t.2 a x ξ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C s.1 t.1 * (1 + ‖ξ‖ ^ 2) ^ ((m' - t.1.length) / 2)) *
        (D s.2 t.2 * (1 + ‖ξ‖ ^ 2) ^ ((m - t.2.length) / 2)) :=
        mul_le_mul (hC _ _) (hD _ _) (norm_nonneg _) ((norm_nonneg _).trans (hC _ _))
    _ = C s.1 t.1 * D s.2 t.2 * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
        rw [hw]
        ring

/-- The constant in `norm_mixedDeriv_comp_le` is nonnegative. -/
private theorem comp_bound_nonneg {C D : List (Fin n) → List (Fin n) → ℝ}
    (hC : ∀ s t, 0 ≤ C s t) (hD : ∀ s t, 0 ≤ D s t) (α β : List (Fin n)) :
    0 ≤ (β.sublists'.revzip.map fun t =>
        (α.sublists'.revzip.map fun s => C s.1 t.1 * D s.2 t.2).sum).sum :=
  List.sum_nonneg fun _ h => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
    exact List.sum_nonneg fun _ h' => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h'
      exact mul_nonneg (hC _ _) (hD _ _)

/-- The pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of symbols of orders `m'` and `m` is a
symbol of order `m' + m`. For matrix-valued symbols this is the matrix product. -/
def comp (b : Symbol n W U m') (a : Symbol n V W m) : Symbol n V U (m' + m) where
  coefficient p := (b.coefficient p).comp (a.coefficient p)
  contDiff_coefficient :=
    -- Composition of `ℂ`-linear maps, viewed as a continuous `ℝ`-bilinear map.
    (((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff
      (n := ∞)).comp (b.contDiff_coefficient.prodMk a.contDiff_coefficient)
  exists_bound K hK α β := by
    choose C hC0 hC using fun s t => b.exists_bound K hK s t
    choose D hD0 hD using fun s t => a.exists_bound K hK s t
    exact ⟨_, comp_bound_nonneg hC0 hD0 α β, fun x hx ξ => norm_mixedDeriv_comp_le
      b.contDiff_coefficient a.contDiff_coefficient (fun s t => hC s t x hx ξ)
      (fun s t => hD s t x hx ξ) α β⟩

@[simp]
theorem coefficient_comp (b : Symbol n W U m') (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (b.comp a).coefficient p = (b.coefficient p).comp (a.coefficient p) := (rfl)

theorem comp_add (b : Symbol n W U m') (a₁ a₂ : Symbol n V W m) :
    b.comp (a₁ + a₂) = b.comp a₁ + b.comp a₂ := by
  ext1
  funext p
  simp [ContinuousLinearMap.comp_add]

theorem add_comp (b₁ b₂ : Symbol n W U m') (a : Symbol n V W m) :
    (b₁ + b₂).comp a = b₁.comp a + b₂.comp a := by
  ext1
  funext p
  simp [ContinuousLinearMap.add_comp]

@[simp]
theorem comp_smul (c : ℂ) (b : Symbol n W U m') (a : Symbol n V W m) :
    b.comp (c • a) = c • b.comp a := by
  ext1
  funext p
  simp

@[simp]
theorem smul_comp (c : ℂ) (b : Symbol n W U m') (a : Symbol n V W m) :
    (c • b).comp a = c • b.comp a := by
  ext1
  funext p
  simp [ContinuousLinearMap.smul_comp]

@[simp]
theorem comp_zero (b : Symbol n W U m') : b.comp (0 : Symbol n V W m) = 0 := by
  ext1
  funext p
  simp

@[simp]
theorem zero_comp (a : Symbol n V W m) : (0 : Symbol n W U m').comp a = 0 := by
  ext1
  funext p
  simp

@[simp]
theorem comp_neg (b : Symbol n W U m') (a : Symbol n V W m) : b.comp (-a) = -b.comp a := by
  ext1
  funext p
  simp

@[simp]
theorem neg_comp (b : Symbol n W U m') (a : Symbol n V W m) : (-b).comp a = -b.comp a := by
  ext1
  funext p
  simp

theorem comp_sub (b : Symbol n W U m') (a₁ a₂ : Symbol n V W m) :
    b.comp (a₁ - a₂) = b.comp a₁ - b.comp a₂ := by
  ext1
  funext p
  simp [ContinuousLinearMap.comp_sub]

theorem sub_comp (b₁ b₂ : Symbol n W U m') (a : Symbol n V W m) :
    (b₁ - b₂).comp a = b₁.comp a - b₂.comp a := by
  ext1
  funext p
  simp [ContinuousLinearMap.sub_comp]

/-- Composing after raising the order of the outer symbol raises the order of the composition. -/
theorem inclusion_comp (h : m' ≤ m'') (b : Symbol n W U m') (a : Symbol n V W m) :
    (inclusion h b).comp a = inclusion (by linarith) (b.comp a) := by
  ext1
  funext p
  simp only [coefficient_comp, coefficient_inclusion]

/-- Composing after raising the order of the inner symbol raises the order of the composition. -/
theorem comp_inclusion (h : m ≤ m'') (b : Symbol n W U m') (a : Symbol n V W m) :
    b.comp (inclusion h a) = inclusion (by linarith) (b.comp a) := by
  ext1
  funext p
  simp only [coefficient_comp, coefficient_inclusion]

/-- Composition of symbols is associative, up to the identification of the orders
`(m'' + m') + m = m'' + (m' + m)`. -/
theorem comp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U'] (c : Symbol n U U' m'')
    (b : Symbol n W U m') (a : Symbol n V W m) :
    (c.comp b).comp a = inclusion (add_assoc m'' m' m).ge (c.comp (b.comp a)) := by
  ext1
  funext p
  simp only [coefficient_comp, coefficient_inclusion, ContinuousLinearMap.comp_assoc]

theorem IsUniform.comp {b : Symbol n W U m'} {a : Symbol n V W m} (hb : b.IsUniform)
    (ha : a.IsUniform) : (b.comp a).IsUniform := by
  intro α β
  choose C hC0 hC using hb
  choose D hD0 hD using ha
  exact ⟨_, comp_bound_nonneg hC0 hD0 α β, fun x ξ => norm_mixedDeriv_comp_le
    b.contDiff_coefficient a.contDiff_coefficient (fun s t => hC s t x ξ)
    (fun s t => hD s t x ξ) α β⟩

/-- Composing a symbol with compact spatial support on the right with another symbol keeps compact
spatial support. -/
theorem HasCompactSpatialSupport.comp_right {b : Symbol n W U m'}
    (hb : b.HasCompactSpatialSupport) (a : Symbol n V W m) :
    (b.comp a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKb⟩ := hb
  exact ⟨K, hK, fun x hx ξ => by simp [hKb x hx ξ]⟩

/-- Composing a symbol with compact spatial support on the left with another symbol keeps compact
spatial support. -/
theorem HasCompactSpatialSupport.comp_left {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (b : Symbol n W U m') :
    (b.comp a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := ha
  exact ⟨K, hK, fun x hx ξ => by simp [hKa x hx ξ]⟩

end Comp

section Smoothing

/-- A symbol is *smoothing*, or of order `-∞`, if its coefficient is a symbol of every real order:
the smoothing symbols are the intersection of all the classes `S^m_{1,0}`. -/
def IsSmoothing (a : Symbol n V W m) : Prop :=
  ∀ m' : ℝ, ∃ b : Symbol n V W m', b.coefficient = a.coefficient

/-- A symbol is smoothing exactly when its coefficient satisfies the symbol estimates of every real
order. -/
theorem isSmoothing_iff {a : Symbol n V W m} :
    a.IsSmoothing ↔ ∀ m' : ℝ, ∃ b : Symbol n V W m', b.coefficient = a.coefficient :=
  Iff.rfl

/-- The estimates characterizing smoothing symbols: a symbol is smoothing exactly when, for every
real order `m'`, every compact set `K` of positions and all words `α` and `β`, the mixed derivative
`∂_x^α ∂_ξ^β a(x, ξ)` is bounded by `C ⟨ξ⟩^(m' - |β|)` for all `x ∈ K` and all frequencies `ξ`,
with a constant `C` depending on `m'`, `K`, `α` and `β`. -/
theorem isSmoothing_iff_forall_exists_bound {a : Symbol n V W m} :
    a.IsSmoothing ↔ ∀ m' : ℝ, ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  refine ⟨fun h m' K hK α β => ?_, fun h m' => ⟨⟨a.coefficient, a.contDiff_coefficient, h m'⟩, rfl⟩⟩
  obtain ⟨b, hb⟩ := h m'
  exact hb ▸ b.exists_bound K hK α β

@[simp]
theorem isSmoothing_zero : (0 : Symbol n V W m).IsSmoothing :=
  fun _ => ⟨0, rfl⟩

theorem IsSmoothing.add {a b : Symbol n V W m} (ha : a.IsSmoothing) (hb : b.IsSmoothing) :
    (a + b).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  obtain ⟨b', hb'⟩ := hb m'
  exact ⟨a' + b', by simp [ha', hb']⟩

theorem IsSmoothing.smul {a : Symbol n V W m} (ha : a.IsSmoothing) (c : ℂ) :
    (c • a).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  exact ⟨c • a', by simp [ha']⟩

theorem IsSmoothing.neg {a : Symbol n V W m} (ha : a.IsSmoothing) : (-a).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  exact ⟨-a', by simp [ha']⟩

theorem IsSmoothing.sub {a b : Symbol n V W m} (ha : a.IsSmoothing) (hb : b.IsSmoothing) :
    (a - b).IsSmoothing := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem IsSmoothing.inclusion {a : Symbol n V W m} (ha : a.IsSmoothing) (h : m ≤ m') :
    (inclusion h a).IsSmoothing :=
  fun m'' => (ha m'').imp fun _ hb => by rw [hb, coefficient_inclusion]

theorem IsSmoothing.frequencyDeriv {a : Symbol n V W m} (ha : a.IsSmoothing) (j : Fin n) :
    (frequencyDeriv j a).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha (m' + 1)
  refine ⟨Symbol.inclusion (by linarith) (Symbol.frequencyDeriv j a'), ?_⟩
  funext ⟨x, ξ⟩
  simp [ha']

theorem IsSmoothing.spatialDeriv {a : Symbol n V W m} (ha : a.IsSmoothing) (j : Fin n) :
    (spatialDeriv j a).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  refine ⟨Symbol.spatialDeriv j a', ?_⟩
  funext ⟨x, ξ⟩
  simp [ha']

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- Smoothing symbols form a right ideal under composition: a smoothing symbol composed on the
right with any symbol is smoothing. -/
theorem IsSmoothing.comp_right {b : Symbol n W U m'} (hb : b.IsSmoothing) (a : Symbol n V W m) :
    (b.comp a).IsSmoothing := fun m'' => by
  obtain ⟨b', hb'⟩ := hb (m'' - m)
  exact ⟨Symbol.inclusion (by linarith) (b'.comp a), funext fun p => by simp [hb']⟩

/-- Smoothing symbols form a left ideal under composition: any symbol composed on the right with a
smoothing symbol is smoothing. -/
theorem IsSmoothing.comp_left {a : Symbol n V W m} (ha : a.IsSmoothing) (b : Symbol n W U m') :
    (b.comp a).IsSmoothing := fun m'' => by
  obtain ⟨a', ha'⟩ := ha (m'' - m')
  exact ⟨Symbol.inclusion (by linarith) (b.comp a'), funext fun p => by simp [ha']⟩

/-- A smooth coefficient vanishing at every frequency of norm at least `R`, such as the difference
of two cut-off expansions, is a symbol of every order `m`. -/
def ofBoundedFrequencySupport (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f) (R : ℝ) (hR : ∀ x ξ, R ≤ ‖ξ‖ → f (x, ξ) = 0) : Symbol n V W m where
  coefficient := f
  contDiff_coefficient := hf
  exists_bound K hK α β := by
    obtain ⟨C, hC, hCK⟩ := (contDiff_zero.2 (hf.mixedDeriv α β).continuous
      ).exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le hK R (m - β.length)
    refine ⟨C, hC, fun x hx ξ => ?_⟩
    rcases le_or_gt ‖ξ‖ R with hξ | hξ
    · simpa only [norm_iteratedFDeriv_zero] using hCK x hx ξ hξ
    · -- Near frequencies of norm `> R` the coefficient vanishes identically.
      have h0 : f =ᶠ[nhds (x, ξ)] 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds
          (show R < ‖(x, ξ).2‖ from hξ)] with p hp using hR p.1 p.2 hp.le
      rw [Filter.EventuallyEq.mixedDeriv_eq h0, mixedDeriv_zero, norm_zero]
      exact mul_nonneg hC (rpow_weight_pos ξ _).le

@[simp]
theorem coefficient_ofBoundedFrequencySupport
    (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : ∀ x ξ, R ≤ ‖ξ‖ → f (x, ξ) = 0) :
    (ofBoundedFrequencySupport f hf R hR : Symbol n V W m).coefficient = f := (rfl)

/-- A symbol vanishing at all large frequencies is smoothing. -/
@[simp]
theorem isSmoothing_ofBoundedFrequencySupport
    (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : ∀ x ξ, R ≤ ‖ξ‖ → f (x, ξ) = 0) :
    (ofBoundedFrequencySupport f hf R hR : Symbol n V W m).IsSmoothing :=
  fun _ => ⟨ofBoundedFrequencySupport f hf R hR, rfl⟩

/-- In positive dimension, a nonzero constant symbol is not smoothing: it does not even have order
`-2`. (On `ℝ⁰` every symbol is smoothing, since there `⟨ξ⟩ = 1`.) -/
theorem isSmoothing_const_iff (hn : n ≠ 0) {T : V →L[ℂ] W} :
    (const T : Symbol n V W 0).IsSmoothing ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨b, hb⟩ := h (-2)
    obtain ⟨C, hC0, hC⟩ := b.exists_bound {0} isCompact_singleton [] []
    by_contra hT
    have hT' : 0 < ‖T‖ := norm_pos_iff.2 hT
    -- At a frequency with `‖ξ‖ ^ 2 = C / ‖T‖` the order `-2` bound fails.
    let ξ : CoordinateSpace n := EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hn⟩ √(C / ‖T‖)
    have hξ : ‖ξ‖ ^ 2 = C / ‖T‖ := by
      rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
    have h := hC 0 rfl ξ
    rw [mixedDeriv_nil_nil, hb, coefficient_const, List.length_nil, Nat.cast_zero, sub_zero, hξ,
      show (-2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)] at h
    have : ‖T‖ * (1 + C / ‖T‖) = ‖T‖ + C := by field_simp
    linarith
  · subst h
    exact fun _ => ⟨0, by funext p; simp⟩

end Smoothing

end Symbol

end TauCeti
