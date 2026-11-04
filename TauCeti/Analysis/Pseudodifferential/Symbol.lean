/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.CoordinateDeriv

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
  (`TauCeti.Symbol.const`).

The estimates are only required locally uniformly in `x`. The predicate
`TauCeti.Symbol.IsUniform` asks for constants independent of `x`, and
`TauCeti.Symbol.HasCompactSpatialSupport` asks that the symbol vanish for `x` outside a fixed
compact set. Symbols with compact spatial support are uniform
(`TauCeti.Symbol.HasCompactSpatialSupport.isUniform`). The symbol of multiplication by `f` is
uniform exactly when all derivatives of `f` are bounded (`TauCeti.Symbol.isUniform_ofSpatial_iff`),
so the local estimates alone do not give uniform ones: a coordinate function `x_j` is a symbol of
order `0` that is not uniform (`TauCeti.Symbol.not_isUniform_ofSpatial_smul`).

The mixed derivative `TauCeti.mixedDeriv α β a x ξ` takes the frequency derivatives first. For
smooth `a` the two kinds of derivatives commute (`TauCeti.mixedDeriv_eq_coordinateDeriv_snd`),
which is what makes spatial derivatives of symbols symbols of the same order.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.1.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The mixed derivative `∂_x^α ∂_ξ^β a(x, ξ)` of a function of a position `x` and a frequency
`ξ`: first the frequency derivatives along `β`, then the position derivatives along `α`. -/
def mixedDeriv (α β : List (Fin n)) (a : CoordinateSpace n × CoordinateSpace n → A)
    (x ξ : CoordinateSpace n) : A :=
  coordinateDeriv α (fun y => coordinateDeriv β (fun η => a (y, η)) ξ) x

theorem mixedDeriv_def (α β : List (Fin n)) (a : CoordinateSpace n × CoordinateSpace n → A)
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = coordinateDeriv α (fun y => coordinateDeriv β (fun η => a (y, η)) ξ) x :=
  (rfl)

@[simp]
theorem mixedDeriv_nil_nil (a : CoordinateSpace n × CoordinateSpace n → A)
    (x ξ : CoordinateSpace n) : mixedDeriv [] [] a x ξ = a (x, ξ) := by
  simp [mixedDeriv_def]

/-- For a smooth function the position and frequency derivatives commute: the mixed derivative
may equally be computed by taking the position derivatives first. -/
theorem mixedDeriv_eq_coordinateDeriv_snd {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = coordinateDeriv β (fun η => coordinateDeriv α (fun y => a (y, η)) x) ξ :=
  (coordinateDeriv_coordinateDeriv_comm ha α β x ξ).symm

/-- The mixed derivatives of a smooth function are jointly smooth in the position and the
frequency. -/
theorem _root_.ContDiff.mixedDeriv {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (α β : List (Fin n)) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => mixedDeriv α β a p.1 p.2 :=
  ((ha.coordinateDeriv_snd β).coordinateDeriv_fst α)

/-- The mixed derivative of the frequency derivative `∂_{ξ_j} a` is a mixed derivative of `a`
with one more frequency derivative. -/
theorem mixedDeriv_coordinateDeriv_snd (α β : List (Fin n)) (j : Fin n)
    (a : CoordinateSpace n × CoordinateSpace n → A) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => coordinateDeriv [j] (fun η => a (p.1, η)) p.2) x ξ =
      mixedDeriv α (β ++ [j]) a x ξ := by
  simp only [mixedDeriv_def, coordinateDeriv_append]

/-- The mixed derivative of the position derivative `∂_{x_j} a` of a smooth function is a mixed
derivative of `a` with one more position derivative. -/
theorem mixedDeriv_coordinateDeriv_fst {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (α β : List (Fin n)) (j : Fin n) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => coordinateDeriv [j] (fun y => a (y, p.2)) p.1) x ξ =
      mixedDeriv (α ++ [j]) β a x ξ := by
  rw [mixedDeriv_def, mixedDeriv_def, coordinateDeriv_append]
  congr 1
  funext y
  exact coordinateDeriv_coordinateDeriv_comm ha [j] β y ξ

section Linear

variable {a b : CoordinateSpace n × CoordinateSpace n → A}

/-- A smooth function of two variables is smooth in its second variable. -/
private theorem contDiff_slice_snd (ha : ContDiff ℝ ∞ a) (y : CoordinateSpace n) :
    ContDiff ℝ ∞ fun η => a (y, η) :=
  ha.comp (contDiff_const.prodMk contDiff_id)

/-- A smooth function of two variables is smooth in its first variable. -/
private theorem contDiff_slice_fst (ha : ContDiff ℝ ∞ a) (ξ : CoordinateSpace n) :
    ContDiff ℝ ∞ fun y => a (y, ξ) :=
  ha.comp (contDiff_id.prodMk contDiff_const)

/-- The partial frequency derivatives of a smooth function, at a fixed frequency, are smooth in
the position. -/
private theorem contDiff_coordinateDeriv_slice (ha : ContDiff ℝ ∞ a) (β : List (Fin n))
    (ξ : CoordinateSpace n) :
    ContDiff ℝ ∞ fun y => coordinateDeriv β (fun η => a (y, η)) ξ :=
  (ha.coordinateDeriv_snd β).comp (contDiff_id.prodMk contDiff_const)

theorem mixedDeriv_add (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (a + b) x ξ = mixedDeriv α β a x ξ + mixedDeriv α β b x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (a + b) (y, η)) ξ) =
      (fun y => coordinateDeriv β (fun η => a (y, η)) ξ) +
        fun y => coordinateDeriv β (fun η => b (y, η)) ξ := by
    funext y
    exact congrFun (coordinateDeriv_add β (contDiff_infty.1 (contDiff_slice_snd ha y) _)
      (contDiff_infty.1 (contDiff_slice_snd hb y) _)) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_add α (contDiff_infty.1 (contDiff_coordinateDeriv_slice ha β ξ) _)
    (contDiff_infty.1 (contDiff_coordinateDeriv_slice hb β ξ) _), Pi.add_apply]

theorem mixedDeriv_const_smul {R : Type*} [Semiring R] [Module R A] [SMulCommClass ℝ R A]
    [ContinuousConstSMul R A] (ha : ContDiff ℝ ∞ a) (c : R) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (c • a) x ξ = c • mixedDeriv α β a x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (c • a) (y, η)) ξ) =
      c • fun y => coordinateDeriv β (fun η => a (y, η)) ξ := by
    funext y
    exact congrFun
      (coordinateDeriv_const_smul β (contDiff_infty.1 (contDiff_slice_snd ha y) _) c) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_const_smul α
    (contDiff_infty.1 (contDiff_coordinateDeriv_slice ha β ξ) _), Pi.smul_apply]

theorem mixedDeriv_neg (ha : ContDiff ℝ ∞ a) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (-a) x ξ = -mixedDeriv α β a x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (-a) (y, η)) ξ) =
      -fun y => coordinateDeriv β (fun η => a (y, η)) ξ := by
    funext y
    exact congrFun (coordinateDeriv_neg β (contDiff_infty.1 (contDiff_slice_snd ha y) _)) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_neg α (contDiff_infty.1 (contDiff_coordinateDeriv_slice ha β ξ) _),
    Pi.neg_apply]

@[simp]
theorem mixedDeriv_zero (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (0 : CoordinateSpace n × CoordinateSpace n → A) x ξ = 0 := by
  have h : (fun y => coordinateDeriv β (fun η => (0 : CoordinateSpace n × CoordinateSpace n → A)
      (y, η)) ξ) = 0 := by
    funext y
    exact congrFun (coordinateDeriv_zero β) ξ
  rw [mixedDeriv_def, h, coordinateDeriv_zero, Pi.zero_apply]

/-- If `a` vanishes for all frequencies at all positions near `x`, then so do all its mixed
derivatives at `x`. -/
theorem mixedDeriv_eq_zero_of_eventually {x : CoordinateSpace n}
    (h : ∀ᶠ y in nhds x, ∀ η, a (y, η) = 0) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = 0 := by
  have h' : (fun y => coordinateDeriv β (fun η => a (y, η)) ξ) =ᶠ[nhds x] 0 := by
    filter_upwards [h] with y hy
    have hy' : (fun η => a (y, η)) = 0 := funext hy
    rw [hy', coordinateDeriv_zero, Pi.zero_apply, Pi.zero_apply]
  rw [mixedDeriv_def, (h'.coordinateDeriv α).eq_of_nhds, coordinateDeriv_zero, Pi.zero_apply]

end Linear

/-- The weight `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)` is monotone in the exponent. -/
private theorem rpow_weight_le_rpow_weight (ξ : CoordinateSpace n) {t t' : ℝ} (h : t ≤ t') :
    (1 + ‖ξ‖ ^ 2) ^ (t / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (t' / 2) :=
  Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

private theorem rpow_weight_pos (ξ : CoordinateSpace n) (t : ℝ) :
    0 < (1 + ‖ξ‖ ^ 2) ^ (t / 2) :=
  Real.rpow_pos_of_pos (by positivity) _

section Bounds

variable {a b : CoordinateSpace n × CoordinateSpace n → A} {α β : List (Fin n)}
  {x ξ : CoordinateSpace n} {C D w : ℝ}

private theorem norm_mixedDeriv_add_le (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haC : ‖mixedDeriv α β a x ξ‖ ≤ C * w) (hbD : ‖mixedDeriv α β b x ξ‖ ≤ D * w) :
    ‖mixedDeriv α β (a + b) x ξ‖ ≤ (C + D) * w := by
  rw [mixedDeriv_add ha hb, add_mul]
  exact (norm_add_le _ _).trans (add_le_add haC hbD)

private theorem norm_mixedDeriv_smul_le {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 A]
    [SMulCommClass ℝ 𝕜 A] (ha : ContDiff ℝ ∞ a) (c : 𝕜) (haC : ‖mixedDeriv α β a x ξ‖ ≤ C * w) :
    ‖mixedDeriv α β (c • a) x ξ‖ ≤ (‖c‖ * C) * w := by
  rw [mixedDeriv_const_smul ha, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left haC (norm_nonneg c)

end Bounds

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

/-- A symbol satisfies its estimates with constants uniform in the position. -/
def IsUniform (a : Symbol n V W m) : Prop :=
  ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

/-- A symbol has compact spatial support if it vanishes, for every frequency, at every position
outside some compact set. -/
def HasCompactSpatialSupport (a : Symbol n V W m) : Prop :=
  ∃ K : Set (CoordinateSpace n), IsCompact K ∧ ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0

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
          rw [mixedDeriv_neg a.contDiff_coefficient, norm_neg]
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
private theorem order_sub_one_sub_length (m : ℝ) (β : List (Fin n)) (j : Fin n) :
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
      (contDiff_infty.1 (contDiff_slice_snd a.contDiff_coefficient p.1) _)
      (contDiff_infty.1 (contDiff_slice_snd b.contDiff_coefficient p.1) _)) p.2
  map_smul' c a := by
    ext1
    funext p
    exact congrFun (coordinateDeriv_const_smul [j]
      (contDiff_infty.1 (contDiff_slice_snd a.contDiff_coefficient p.1) _) c) p.2

@[simp]
theorem coefficient_frequencyDeriv (j : Fin n) (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (frequencyDeriv j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun η => a.coefficient (x, η)) ξ := (rfl)

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
      (contDiff_infty.1 (contDiff_slice_fst a.contDiff_coefficient p.2) _)
      (contDiff_infty.1 (contDiff_slice_fst b.contDiff_coefficient p.2) _)) p.1
  map_smul' c a := by
    ext1
    funext p
    exact congrFun (coordinateDeriv_const_smul [j]
      (contDiff_infty.1 (contDiff_slice_fst a.contDiff_coefficient p.2) _) c) p.1

@[simp]
theorem coefficient_spatialDeriv (j : Fin n) (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (spatialDeriv j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun y => a.coefficient (y, ξ)) x := (rfl)

theorem IsUniform.frequencyDeriv {a : Symbol n V W m} (ha : a.IsUniform) (j : Fin n) :
    (frequencyDeriv j a).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha α (β ++ [j])
  refine ⟨C, hC, fun x ξ => ?_⟩
  have h : (Symbol.frequencyDeriv j a).coefficient =
      fun p => coordinateDeriv [j] (fun η => a.coefficient (p.1, η)) p.2 :=
    funext fun p => coefficient_frequencyDeriv j a p.1 p.2
  rw [h, mixedDeriv_coordinateDeriv_snd, order_sub_one_sub_length]
  exact hCa x ξ

theorem IsUniform.spatialDeriv {a : Symbol n V W m} (ha : a.IsUniform) (j : Fin n) :
    (spatialDeriv j a).IsUniform := by
  intro α β
  obtain ⟨C, hC, hCa⟩ := ha (α ++ [j]) β
  refine ⟨C, hC, fun x ξ => ?_⟩
  have h : (Symbol.spatialDeriv j a).coefficient =
      fun p => coordinateDeriv [j] (fun y => a.coefficient (y, p.2)) p.1 :=
    funext fun p => coefficient_spatialDeriv j a p.1 p.2
  rw [h, mixedDeriv_coordinateDeriv_fst a.contDiff_coefficient]
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

/-- A frequency-independent function has no frequency derivatives. -/
private theorem mixedDeriv_comp_fst (f : CoordinateSpace n → V →L[ℂ] W) (α : List (Fin n))
    {β : List (Fin n)} (hβ : β ≠ []) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => f p.1) x ξ = 0 := by
  rw [mixedDeriv_def]
  simp only [coordinateDeriv_const _ hβ, Pi.zero_apply]
  rw [← Pi.zero_def, coordinateDeriv_zero, Pi.zero_apply]

/-- The position derivatives of a frequency-independent function are those of its profile. -/
private theorem mixedDeriv_nil_comp_fst (f : CoordinateSpace n → V →L[ℂ] W) (α : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α [] (fun p => f p.1) x ξ = coordinateDeriv α f x := by
  simp only [mixedDeriv_def, coordinateDeriv_nil]

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

end Symbol

end TauCeti
