/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Symbols of type `(1, 0)` on `ℝⁿ`

For a real order `m`, a (local) symbol of order `m` and type `(1, 0)` on `ℝⁿ × ℝⁿ` is a smooth map
`a : ℝⁿ × ℝⁿ → (V →L[ℂ] W)` such that on every compact set `K` of positions and for all lists of
coordinate directions `α`, `β`,

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{K,α,β} ⟨ξ⟩^(m - |β|)`  for `x ∈ K`, `ξ ∈ ℝⁿ`,

where `⟨ξ⟩ = (1 + |ξ|²)^(1/2)`. Every derivative in the frequency variable `ξ` improves the decay
by one order, while derivatives in the position variable `x` cost nothing. These are the symbols
of Hörmander's class `S^m_{1,0}` (M. Taylor, *Pseudodifferential operators: four lectures at
MSRI*, 2008, Lecture I, (1.15)), whose quantizations are the pseudodifferential operators of
order `m`. The coefficients are continuous linear maps between complex normed spaces, so that
symbols of operators between trivial vector bundles are covered.

This file sets up the carrier `TauCeti.Symbol n V W m` and its basic structure:

* symbols of order `m` form a complex vector space, and a symbol of order `m` is a symbol of
  every larger order (`TauCeti.Symbol.inclusion`);
* differentiation in a position coordinate preserves the order (`TauCeti.Symbol.spatialDeriv`),
  differentiation in a frequency coordinate lowers it by one (`TauCeti.Symbol.frequencyDeriv`);
* the predicates `TauCeti.Symbol.IsUniform` (the estimates hold with constants uniform in all
  `x ∈ ℝⁿ`) and `TauCeti.Symbol.HasCompactSpatialSupport` (the symbol vanishes for `x` outside a
  compact set); the second implies the first.

The basic examples are the order-zero symbols `TauCeti.Symbol.ofSpatial φ` depending only on the
position, which are uniform exactly when all derivatives of `φ` are bounded, and the order-one
symbols `TauCeti.Symbol.ofFrequencyLinear L` given by a linear function of the frequency, the
symbols of constant-coefficient first-order differential operators without zeroth-order term. A
nonzero linear function of the frequency is not a symbol of order zero.

Mixed derivatives `∂_x^α ∂_ξ^β` are indexed by lists of coordinates, so that they can be
iterated one direction at a time; for smooth maps they do not depend on the order of the
directions (`List.Perm.iteratedFDerivAlong_eq`).
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

/-- The Euclidean coordinate space `ℝⁿ` of a chart. -/
abbrev CoordinateSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

section Derivatives

variable {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The iterated coordinate derivative `∂_{j₁} ⋯ ∂_{jₖ} f` along the list of coordinates
`[j₁, …, jₖ]`, the derivative in the coordinate `jₖ` being taken first. -/
def coordinateDeriv (indices : List (Fin n)) (f : CoordinateSpace n → A) :
    CoordinateSpace n → A :=
  iteratedFDerivAlong ℝ (indices.map fun j => EuclideanSpace.single j 1) f

theorem coordinateDeriv_eq_iteratedFDerivAlong (l : List (Fin n)) (f : CoordinateSpace n → A) :
    coordinateDeriv l f = iteratedFDerivAlong ℝ (l.map fun j => EuclideanSpace.single j 1) f :=
  (rfl)

@[simp]
theorem coordinateDeriv_nil (f : CoordinateSpace n → A) : coordinateDeriv [] f = f := by
  simp [coordinateDeriv]

@[simp]
theorem coordinateDeriv_cons_apply (j : Fin n) (l : List (Fin n)) (f : CoordinateSpace n → A)
    (x : CoordinateSpace n) :
    coordinateDeriv (j :: l) f x =
      fderiv ℝ (coordinateDeriv l f) x (EuclideanSpace.single j 1) := by
  simp [coordinateDeriv]

@[simp]
theorem coordinateDeriv_cons_const (j : Fin n) (l : List (Fin n)) (c : A) :
    coordinateDeriv (j :: l) (fun _ : CoordinateSpace n => c) = 0 :=
  iteratedFDerivAlong_cons_const _ _ c

/-- The mixed derivative `∂_x^α ∂_ξ^β a(x, ξ)` of a function of a position `x` and a frequency
`ξ`: first differentiate in the frequency along `β`, then in the position along `α`. -/
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
  simp [mixedDeriv]

/-- For a smooth map, the mixed derivative `∂_x^α ∂_ξ^β a` is the iterated directional derivative
of `a` on `ℝⁿ × ℝⁿ` along the position directions of `α` followed by the frequency directions
of `β`. -/
theorem mixedDeriv_eq_iteratedFDerivAlong {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = iteratedFDerivAlong ℝ
      (α.map (fun j => (EuclideanSpace.single j 1, 0)) ++
        β.map (fun j => (0, EuclideanSpace.single j 1))) a (x, ξ) := by
  have hinner : ∀ y, coordinateDeriv β (fun η => a (y, η)) ξ = iteratedFDerivAlong ℝ
      (β.map (fun j => (0, EuclideanSpace.single j 1))) a (y, ξ) := fun y => by
    rw [coordinateDeriv, iteratedFDerivAlong_comp_of_hasFDerivAt (hasFDerivAt_prodMk_right y) ha _
      (by exact_mod_cast le_top)]
    simp [Function.comp_def]
  rw [mixedDeriv, funext hinner, coordinateDeriv,
    iteratedFDerivAlong_comp_of_hasFDerivAt (hasFDerivAt_prodMk_left · ξ)
      (ha.iteratedFDerivAlong (m := ∞) _ (by exact_mod_cast le_top)) _ (by exact_mod_cast le_top),
    iteratedFDerivAlong_append]
  simp [Function.comp_def]

@[simp]
theorem mixedDeriv_zero (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (0 : CoordinateSpace n × CoordinateSpace n → A) x ξ = 0 := by
  rw [mixedDeriv_eq_iteratedFDerivAlong (a := 0) contDiff_zero_fun, iteratedFDerivAlong_zero,
    Pi.zero_apply]

theorem mixedDeriv_add {a b : CoordinateSpace n × CoordinateSpace n → A} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (a + b) x ξ = mixedDeriv α β a x ξ + mixedDeriv α β b x ξ := by
  rw [mixedDeriv_eq_iteratedFDerivAlong (a := a + b) (ha.add hb),
    iteratedFDerivAlong_add ha hb _ (by exact_mod_cast le_top),
    mixedDeriv_eq_iteratedFDerivAlong ha, mixedDeriv_eq_iteratedFDerivAlong hb, Pi.add_apply]

theorem mixedDeriv_neg {a : CoordinateSpace n × CoordinateSpace n → A} (ha : ContDiff ℝ ∞ a)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (-a) x ξ = -mixedDeriv α β a x ξ := by
  rw [mixedDeriv_eq_iteratedFDerivAlong (a := -a) ha.neg, iteratedFDerivAlong_neg,
    mixedDeriv_eq_iteratedFDerivAlong ha, Pi.neg_apply]

theorem mixedDeriv_sub {a b : CoordinateSpace n × CoordinateSpace n → A} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (a - b) x ξ = mixedDeriv α β a x ξ - mixedDeriv α β b x ξ := by
  rw [mixedDeriv_eq_iteratedFDerivAlong (a := a - b) (ha.sub hb),
    iteratedFDerivAlong_sub ha hb _ (by exact_mod_cast le_top),
    mixedDeriv_eq_iteratedFDerivAlong ha, mixedDeriv_eq_iteratedFDerivAlong hb, Pi.sub_apply]

theorem mixedDeriv_const_smul {R : Type*} [Semiring R] [Module R A] [SMulCommClass ℝ R A]
    [ContinuousConstSMul R A] {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (c : R) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (c • a) x ξ = c • mixedDeriv α β a x ξ := by
  rw [mixedDeriv_eq_iteratedFDerivAlong (a := c • a) (ha.const_smul c),
    iteratedFDerivAlong_const_smul ha _ _ (by exact_mod_cast le_top),
    mixedDeriv_eq_iteratedFDerivAlong ha, Pi.smul_apply]

/-- Coordinate derivatives of smooth maps are smooth. -/
theorem _root_.ContDiff.coordinateDeriv {f : CoordinateSpace n → A} (hf : ContDiff ℝ ∞ f)
    (l : List (Fin n)) : ContDiff ℝ ∞ (coordinateDeriv l f) :=
  hf.iteratedFDerivAlong _ (by exact_mod_cast le_top)

@[simp]
theorem coordinateDeriv_zero (l : List (Fin n)) :
    coordinateDeriv l (0 : CoordinateSpace n → A) = 0 :=
  iteratedFDerivAlong_zero _

/-- The mixed derivatives of a smooth map vanish wherever the map vanishes nearby. -/
theorem mixedDeriv_eq_zero_of_eventuallyEq_zero {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) {x ξ : CoordinateSpace n} (h : a =ᶠ[𝓝 (x, ξ)] 0)
    (α β : List (Fin n)) : mixedDeriv α β a x ξ = 0 := by
  rw [mixedDeriv_eq_iteratedFDerivAlong ha, iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero h]

/-- For a function of the position alone, the mixed derivatives without frequency directions
are its coordinate derivatives. -/
@[simp]
theorem mixedDeriv_nil_right_comp_fst (φ : CoordinateSpace n → A) (α : List (Fin n))
    (x ξ : CoordinateSpace n) : mixedDeriv α [] (fun p => φ p.1) x ξ = coordinateDeriv α φ x := by
  simp [mixedDeriv]

/-- A function of the position alone has vanishing frequency derivatives. -/
@[simp]
theorem mixedDeriv_cons_right_comp_fst (φ : CoordinateSpace n → A) (α β : List (Fin n))
    (j : Fin n) (x ξ : CoordinateSpace n) : mixedDeriv α (j :: β) (fun p => φ p.1) x ξ = 0 := by
  simp only [mixedDeriv, coordinateDeriv_cons_const, Pi.zero_apply]
  exact congrFun (coordinateDeriv_zero α) x

/-- For a function of the frequency alone, the mixed derivatives without position directions
are its coordinate derivatives. -/
@[simp]
theorem mixedDeriv_nil_left_comp_snd (ψ : CoordinateSpace n → A) (β : List (Fin n))
    (x ξ : CoordinateSpace n) : mixedDeriv [] β (fun p => ψ p.2) x ξ = coordinateDeriv β ψ ξ := by
  simp [mixedDeriv]

/-- A function of the frequency alone has vanishing position derivatives. -/
@[simp]
theorem mixedDeriv_cons_left_comp_snd (ψ : CoordinateSpace n → A) (α β : List (Fin n))
    (j : Fin n) (x ξ : CoordinateSpace n) : mixedDeriv (j :: α) β (fun p => ψ p.2) x ξ = 0 :=
  congrFun (coordinateDeriv_cons_const j α (coordinateDeriv β ψ ξ)) x

/-- Differentiating in the position coordinate `j` appends `j` to the position directions. -/
theorem mixedDeriv_fderiv_spatial {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (j : Fin n) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => fderiv ℝ a p (EuclideanSpace.single j 1, 0)) x ξ =
      mixedDeriv (α ++ [j]) β a x ξ := by
  have hfun : (fun p => fderiv ℝ a p (EuclideanSpace.single j 1, 0)) =
      iteratedFDerivAlong ℝ [(EuclideanSpace.single j 1, 0)] a := by
    funext p
    simp
  rw [hfun, mixedDeriv_eq_iteratedFDerivAlong (ha.iteratedFDerivAlong _ (by exact_mod_cast le_top)),
    mixedDeriv_eq_iteratedFDerivAlong ha, ← iteratedFDerivAlong_append, List.map_append,
    List.append_assoc, List.append_assoc]
  exact congrFun
    ((List.perm_append_comm.append_left _).iteratedFDerivAlong_eq ha (by exact_mod_cast le_top)) _

/-- Differentiating in the frequency coordinate `j` appends `j` to the frequency directions. -/
theorem mixedDeriv_fderiv_frequency {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ ∞ a) (j : Fin n) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => fderiv ℝ a p (0, EuclideanSpace.single j 1)) x ξ =
      mixedDeriv α (β ++ [j]) a x ξ := by
  have hfun : (fun p => fderiv ℝ a p (0, EuclideanSpace.single j 1)) =
      iteratedFDerivAlong ℝ [(0, EuclideanSpace.single j 1)] a := by
    funext p
    simp
  rw [hfun, mixedDeriv_eq_iteratedFDerivAlong (ha.iteratedFDerivAlong _ (by exact_mod_cast le_top)),
    mixedDeriv_eq_iteratedFDerivAlong ha, ← iteratedFDerivAlong_append, List.map_append,
    List.append_assoc]
  rfl

end Derivatives

/-- **Symbols of order `m` and type `(1, 0)`.** A symbol of order `m` on `ℝⁿ` with values in
`V →L[ℂ] W` is a smooth coefficient `a(x, ξ)` of a position `x` and a frequency `ξ` such that on
every compact set `K` of positions and for all lists of coordinates `α` and `β`,
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for `x ∈ K` and all `ξ`, where
`⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. -/
@[ext]
structure Symbol (n : ℕ) (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The coefficient `a(x, ξ)` at the position `x` and the frequency `ξ`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  /-- The coefficient is smooth in both variables. -/
  smooth : ContDiff ℝ ∞ coefficient
  /-- The symbol estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` on compact sets of
  positions. -/
  derivative_bound : ∀ (K : Set (CoordinateSpace n)), IsCompact K →
    ∀ (α β : List (Fin n)), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - (β.length : ℝ)) / 2)

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

private theorem weight_nonneg (ξ : CoordinateSpace n) (r : ℝ) : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ r :=
  Real.rpow_nonneg (by positivity) r

/-! ### Symbol estimates on a set of positions

The local estimates of a symbol are the estimates on every compact set, and the uniform
estimates are the estimates on all of `ℝⁿ`; the closure properties are proved once for an
arbitrary set of positions. -/

/-- The symbol estimates of order `m` for positions in `S`. -/
private def BoundOn (S : Set (CoordinateSpace n)) (m : ℝ)
    (a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) : Prop :=
  ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ,
    ‖mixedDeriv α β a x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - (β.length : ℝ)) / 2)

variable {S : Set (CoordinateSpace n)} {a b : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}

private theorem BoundOn.zero :
    BoundOn S m (0 : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) :=
  fun _ _ => ⟨0, le_rfl, fun x _ ξ => by simp⟩

private theorem BoundOn.add (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (h₁ : BoundOn S m a)
    (h₂ : BoundOn S m b) : BoundOn S m (a + b) := fun α β => by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁ α β
  obtain ⟨C₂, hC₂, h₂⟩ := h₂ α β
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun x hx ξ => ?_⟩
  rw [mixedDeriv_add ha hb, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ x hx ξ) (h₂ x hx ξ))

private theorem BoundOn.neg (ha : ContDiff ℝ ∞ a) (h : BoundOn S m a) : BoundOn S m (-a) :=
  fun α β => by
  obtain ⟨C, hC, h⟩ := h α β
  exact ⟨C, hC, fun x hx ξ => by rw [mixedDeriv_neg ha, norm_neg]; exact h x hx ξ⟩

private theorem BoundOn.sub (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (h₁ : BoundOn S m a)
    (h₂ : BoundOn S m b) : BoundOn S m (a - b) := by
  rw [sub_eq_add_neg]
  exact h₁.add ha hb.neg (h₂.neg hb)

private theorem BoundOn.const_smul (ha : ContDiff ℝ ∞ a) (h : BoundOn S m a) (c : ℂ) :
    BoundOn S m (c • a) := fun α β => by
  obtain ⟨C, hC, h⟩ := h α β
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x hx ξ => ?_⟩
  rw [mixedDeriv_const_smul ha, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx ξ) (norm_nonneg c)

private theorem BoundOn.mono_order (h : BoundOn S m a) (hm : m ≤ m') : BoundOn S m' a :=
  fun α β => by
  obtain ⟨C, hC, h⟩ := h α β
  refine ⟨C, hC, fun x hx ξ => (h x hx ξ).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)

private theorem BoundOn.spatial (ha : ContDiff ℝ ∞ a) (h : BoundOn S m a) (j : Fin n) :
    BoundOn S m (fun p => fderiv ℝ a p (EuclideanSpace.single j 1, 0)) := fun α β => by
  obtain ⟨C, hC, h⟩ := h (α ++ [j]) β
  exact ⟨C, hC, fun x hx ξ => by rw [mixedDeriv_fderiv_spatial ha]; exact h x hx ξ⟩

private theorem BoundOn.frequency (ha : ContDiff ℝ ∞ a) (h : BoundOn S m a) (j : Fin n) :
    BoundOn S (m - 1) (fun p => fderiv ℝ a p (0, EuclideanSpace.single j 1)) := fun α β => by
  obtain ⟨C, hC, h⟩ := h α (β ++ [j])
  refine ⟨C, hC, fun x hx ξ => ?_⟩
  have he : (m - 1 - (β.length : ℝ)) / 2 = (m - ((β ++ [j]).length : ℝ)) / 2 := by
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    ring
  rw [mixedDeriv_fderiv_frequency ha, he]
  exact h x hx ξ

theorem coefficient_injective : Function.Injective (coefficient : Symbol n V W m → _) :=
  fun _ _ h => Symbol.ext h

/-! ### The vector space of symbols of order `m` -/

@[no_expose] instance : Zero (Symbol n V W m) where
  zero := ⟨0, contDiff_zero_fun, fun _ _ => BoundOn.zero⟩

@[no_expose] instance : Add (Symbol n V W m) where
  add a b := ⟨a.coefficient + b.coefficient, a.smooth.add b.smooth, fun K hK =>
    BoundOn.add a.smooth b.smooth (a.derivative_bound K hK) (b.derivative_bound K hK)⟩

@[no_expose] instance : Neg (Symbol n V W m) where
  neg a := ⟨-a.coefficient, a.smooth.neg, fun K hK =>
    BoundOn.neg a.smooth (a.derivative_bound K hK)⟩

@[no_expose] instance : Sub (Symbol n V W m) where
  sub a b := ⟨a.coefficient - b.coefficient, a.smooth.sub b.smooth, fun K hK =>
    BoundOn.sub a.smooth b.smooth (a.derivative_bound K hK) (b.derivative_bound K hK)⟩

@[no_expose] instance : SMul ℂ (Symbol n V W m) where
  smul c a := ⟨c • a.coefficient, a.smooth.const_smul c, fun K hK =>
    BoundOn.const_smul a.smooth (a.derivative_bound K hK) c⟩

instance : SMul ℕ (Symbol n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (Symbol n V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : Symbol n V W m).coefficient = 0 :=
  (rfl)

@[simp]
theorem coefficient_add (a b : Symbol n V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient :=
  (rfl)

@[simp]
theorem coefficient_neg (a : Symbol n V W m) : (-a).coefficient = -a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_sub (a b : Symbol n V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient :=
  (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : Symbol n V W m) : (c • a).coefficient = c • a.coefficient :=
  (rfl)

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
    coefficient_sub (fun _ _ => coefficient_nsmul _ _) (fun _ _ => coefficient_zsmul _ _)

instance : Module ℂ (Symbol n V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

/-! ### Order inclusions and derivatives -/

/-- A symbol of order `m` is a symbol of every larger order `m'`. -/
def inclusion (h : m ≤ m') : Symbol n V W m →ₗ[ℂ] Symbol n V W m' where
  toFun a := ⟨a.coefficient, a.smooth, fun K hK => BoundOn.mono_order (a.derivative_bound K hK) h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coefficient_inclusion (h : m ≤ m') (a : Symbol n V W m) :
    (inclusion h a).coefficient = a.coefficient :=
  (rfl)

@[simp]
theorem inclusion_refl (a : Symbol n V W m) : inclusion le_rfl a = a :=
  Symbol.ext rfl

@[simp]
theorem inclusion_inclusion {m'' : ℝ} (h₁ : m ≤ m') (h₂ : m' ≤ m'') (a : Symbol n V W m) :
    inclusion h₂ (inclusion h₁ a) = inclusion (h₁.trans h₂) a :=
  Symbol.ext rfl

theorem inclusion_injective (h : m ≤ m') :
    Function.Injective (inclusion h : Symbol n V W m → Symbol n V W m') :=
  fun a b hab => Symbol.ext (by simpa using congrArg coefficient hab)

/-- The derivative `∂_{x_j} a` of a symbol in the position coordinate `j`, a symbol of the same
order. -/
def spatialDeriv (j : Fin n) : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a := ⟨fun p => fderiv ℝ a.coefficient p (EuclideanSpace.single j 1, 0),
    (a.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, fun K hK =>
      BoundOn.spatial a.smooth (a.derivative_bound K hK) j⟩
  map_add' a b := Symbol.ext <| funext fun p => by
    simp [fderiv_add (a.smooth.differentiable (by simp) p) (b.smooth.differentiable (by simp) p)]
  map_smul' c a := Symbol.ext <| funext fun p => by
    simp [fderiv_const_smul (a.smooth.differentiable (by simp) p)]

@[simp]
theorem coefficient_spatialDeriv (j : Fin n) (a : Symbol n V W m) :
    (spatialDeriv j a).coefficient =
      fun p => fderiv ℝ a.coefficient p (EuclideanSpace.single j 1, 0) :=
  (rfl)

/-- The derivative `∂_{ξ_j} a` of a symbol of order `m` in the frequency coordinate `j`, a symbol
of order `m - 1`. -/
def frequencyDeriv (j : Fin n) : Symbol n V W m →ₗ[ℂ] Symbol n V W (m - 1) where
  toFun a := ⟨fun p => fderiv ℝ a.coefficient p (0, EuclideanSpace.single j 1),
    (a.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, fun K hK =>
      BoundOn.frequency a.smooth (a.derivative_bound K hK) j⟩
  map_add' a b := Symbol.ext <| funext fun p => by
    simp [fderiv_add (a.smooth.differentiable (by simp) p) (b.smooth.differentiable (by simp) p)]
  map_smul' c a := Symbol.ext <| funext fun p => by
    simp [fderiv_const_smul (a.smooth.differentiable (by simp) p)]

@[simp]
theorem coefficient_frequencyDeriv (j : Fin n) (a : Symbol n V W m) :
    (frequencyDeriv j a).coefficient =
      fun p => fderiv ℝ a.coefficient p (0, EuclideanSpace.single j 1) :=
  (rfl)

/-! ### Uniform symbols and compact spatial support -/

/-- A symbol is uniform if its symbol estimates hold with constants independent of the position
`x ∈ ℝⁿ`. This is extra information, not a consequence of the local estimates. -/
def IsUniform (a : Symbol n V W m) : Prop :=
  ∀ (α β : List (Fin n)), ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ξ, ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - (β.length : ℝ)) / 2)

/-- A symbol has compact spatial support if it vanishes, at every frequency, for positions
outside a fixed compact set. -/
def HasCompactSpatialSupport (a : Symbol n V W m) : Prop :=
  ∃ K : Set (CoordinateSpace n), IsCompact K ∧
    ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0

theorem isUniform_iff (a : Symbol n V W m) :
    a.IsUniform ↔ ∀ (α β : List (Fin n)), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ξ, ‖mixedDeriv α β a.coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - (β.length : ℝ)) / 2) :=
  Iff.rfl

theorem hasCompactSpatialSupport_iff (a : Symbol n V W m) :
    a.HasCompactSpatialSupport ↔ ∃ K : Set (CoordinateSpace n), IsCompact K ∧
      ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0 :=
  Iff.rfl

private theorem isUniform_iff_boundOn (a : Symbol n V W m) :
    a.IsUniform ↔ BoundOn Set.univ m a.coefficient := by
  simp [IsUniform, BoundOn]

@[simp]
theorem isUniform_zero : (0 : Symbol n V W m).IsUniform :=
  (isUniform_iff_boundOn _).2 BoundOn.zero

theorem IsUniform.add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a + b).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.add a.smooth b.smooth
    ((isUniform_iff_boundOn a).1 ha) ((isUniform_iff_boundOn b).1 hb)

theorem IsUniform.neg {a : Symbol n V W m} (ha : a.IsUniform) : (-a).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.neg a.smooth ((isUniform_iff_boundOn a).1 ha)

theorem IsUniform.sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a - b).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.sub a.smooth b.smooth
    ((isUniform_iff_boundOn a).1 ha) ((isUniform_iff_boundOn b).1 hb)

theorem IsUniform.const_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) :
    (c • a).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.const_smul a.smooth ((isUniform_iff_boundOn a).1 ha) c

theorem IsUniform.inclusion {a : Symbol n V W m} (ha : a.IsUniform) (h : m ≤ m') :
    (inclusion h a).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.mono_order ((isUniform_iff_boundOn a).1 ha) h

theorem IsUniform.spatialDeriv {a : Symbol n V W m} (ha : a.IsUniform) (j : Fin n) :
    (spatialDeriv j a).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.spatial a.smooth ((isUniform_iff_boundOn a).1 ha) j

theorem IsUniform.frequencyDeriv {a : Symbol n V W m} (ha : a.IsUniform) (j : Fin n) :
    (frequencyDeriv j a).IsUniform :=
  (isUniform_iff_boundOn _).2 <| BoundOn.frequency a.smooth ((isUniform_iff_boundOn a).1 ha) j

/-- A symbol with compact spatial support vanishes near every point whose position lies outside
some compact set. -/
theorem HasCompactSpatialSupport.exists_eventuallyEq_zero {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) : ∃ K : Set (CoordinateSpace n), IsCompact K ∧
      ∀ x ∉ K, ∀ ξ, a.coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
  obtain ⟨K, hK, h⟩ := ha
  refine ⟨K, hK, fun x hx ξ => ?_⟩
  filter_upwards [(hK.isClosed.isOpen_compl.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hx trivial)]
    with p hp using h p.1 hp.1 p.2

/-- **A compact spatial cutoff gives uniform bounds.** A symbol with compact spatial support is
uniform. -/
theorem HasCompactSpatialSupport.isUniform {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) : a.IsUniform := fun α β => by
  obtain ⟨K, hK, hzero⟩ := ha.exists_eventuallyEq_zero
  obtain ⟨C, hC, hb⟩ := a.derivative_bound K hK α β
  refine ⟨C, hC, fun x ξ => ?_⟩
  by_cases hx : x ∈ K
  · exact hb x hx ξ
  · rw [mixedDeriv_eq_zero_of_eventuallyEq_zero a.smooth (hzero x hx ξ), norm_zero]
    exact mul_nonneg hC (weight_nonneg ξ _)

@[simp]
theorem hasCompactSpatialSupport_zero : (0 : Symbol n V W m).HasCompactSpatialSupport :=
  ⟨∅, isCompact_empty, fun _ _ _ => rfl⟩

theorem HasCompactSpatialSupport.add {a b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) : (a + b).HasCompactSpatialSupport := by
  obtain ⟨K, hK, h₁⟩ := ha
  obtain ⟨L, hL, h₂⟩ := hb
  refine ⟨K ∪ L, hK.union hL, fun x hx ξ => ?_⟩
  rw [Set.mem_union, not_or] at hx
  simp [h₁ x hx.1 ξ, h₂ x hx.2 ξ]

theorem HasCompactSpatialSupport.neg {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) :
    (-a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, h⟩ := ha
  exact ⟨K, hK, fun x hx ξ => by simp [h x hx ξ]⟩

theorem HasCompactSpatialSupport.sub {a b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) : (a - b).HasCompactSpatialSupport := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem HasCompactSpatialSupport.const_smul {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (c : ℂ) : (c • a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, h⟩ := ha
  exact ⟨K, hK, fun x hx ξ => by simp [h x hx ξ]⟩

theorem HasCompactSpatialSupport.inclusion {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (h : m ≤ m') : (inclusion h a).HasCompactSpatialSupport :=
  ha

theorem HasCompactSpatialSupport.spatialDeriv {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (j : Fin n) :
    (spatialDeriv j a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, h⟩ := ha.exists_eventuallyEq_zero
  exact ⟨K, hK, fun x hx ξ => by simp [coefficient_spatialDeriv, (h x hx ξ).fderiv_eq]⟩

theorem HasCompactSpatialSupport.frequencyDeriv {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (j : Fin n) :
    (frequencyDeriv j a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, h⟩ := ha.exists_eventuallyEq_zero
  exact ⟨K, hK, fun x hx ξ => by simp [coefficient_frequencyDeriv, (h x hx ξ).fderiv_eq]⟩

/-! ### Examples -/

/-- A smooth function of the position alone is a symbol of order zero. -/
def ofSpatial (φ : CoordinateSpace n → V →L[ℂ] W) (hφ : ContDiff ℝ ∞ φ) : Symbol n V W 0 where
  coefficient p := φ p.1
  smooth := hφ.comp contDiff_fst
  derivative_bound K hK α β := by
    cases β with
    | nil =>
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        (hφ.coordinateDeriv α).continuous.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
      simpa using (hC x hx).trans (le_max_left C 0)
    | cons j β => exact ⟨0, le_rfl, fun x _ ξ => by simp⟩

@[simp]
theorem coefficient_ofSpatial (φ : CoordinateSpace n → V →L[ℂ] W) (hφ : ContDiff ℝ ∞ φ) :
    (ofSpatial φ hφ).coefficient = fun p => φ p.1 :=
  (rfl)

/-- A symbol depending only on the position is uniform exactly when all coordinate derivatives of
the function are bounded. -/
theorem isUniform_ofSpatial_iff {φ : CoordinateSpace n → V →L[ℂ] W} (hφ : ContDiff ℝ ∞ φ) :
    (ofSpatial φ hφ).IsUniform ↔ ∀ α : List (Fin n), ∃ C, ∀ x, ‖coordinateDeriv α φ x‖ ≤ C := by
  constructor
  · intro h α
    obtain ⟨C, -, hC⟩ := h α []
    exact ⟨C, fun x => by simpa [coefficient_ofSpatial] using hC x 0⟩
  · intro h α β
    cases β with
    | nil =>
      obtain ⟨C, hC⟩ := h α
      refine ⟨max C 0, le_max_right _ _, fun x ξ => ?_⟩
      simpa [coefficient_ofSpatial] using (hC x).trans (le_max_left C 0)
    | cons j β => exact ⟨0, le_rfl, fun x ξ => by simp [coefficient_ofSpatial]⟩

theorem hasCompactSpatialSupport_ofSpatial {φ : CoordinateSpace n → V →L[ℂ] W}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (ofSpatial φ hφ).HasCompactSpatialSupport :=
  ⟨tsupport φ, hc, fun x hx _ => by
    rw [coefficient_ofSpatial]
    exact image_eq_zero_of_notMem_tsupport hx⟩

/-- A nonzero linear function of the position is a symbol of order zero which is not uniform: the
symbol estimates of `x` at `ξ = 0` grow with `x`. -/
theorem _root_.ContinuousLinearMap.not_isUniform_ofSpatial
    (L : CoordinateSpace n →L[ℝ] V →L[ℂ] W) (hL : L ≠ 0) :
    ¬ (ofSpatial L L.contDiff).IsUniform := by
  rw [isUniform_ofSpatial_iff]
  intro h
  obtain ⟨C, hC⟩ := h []
  exact hL (ContinuousLinearMap.coe_injective
    (LinearMap.eq_zero_of_forall_norm_apply_le (f := L.toLinearMap) fun v => by simpa using hC v))

private theorem ofFrequencyLinear_bound (L : CoordinateSpace n →L[ℝ] V →L[ℂ] W)
    (α β : List (Fin n)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖mixedDeriv α β (fun p => L p.2) x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((1 - (β.length : ℝ)) / 2) := by
  refine ⟨‖L‖, norm_nonneg L, fun x ξ => ?_⟩
  rcases α with _ | ⟨i, α⟩
  · rcases β with _ | ⟨j, _ | ⟨k, β⟩⟩
    · -- `‖L ξ‖ ≤ ‖L‖ ‖ξ‖ ≤ ‖L‖ ⟨ξ⟩`
      rw [mixedDeriv_nil_left_comp_snd, coordinateDeriv_nil]
      refine (L.le_opNorm ξ).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
      rw [List.length_nil, Nat.cast_zero, sub_zero, ← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left zero_le_one)
    · -- `∂_{ξ_j} (L ξ) = L e_j`
      rw [mixedDeriv_nil_left_comp_snd, coordinateDeriv_cons_apply, coordinateDeriv_nil,
        ContinuousLinearMap.fderiv]
      simpa using L.le_opNorm (EuclideanSpace.single j 1)
    · have h0 : coordinateDeriv (j :: k :: β) L = 0 := L.iteratedFDerivAlong_cons_cons _ _ _
      rw [mixedDeriv_nil_left_comp_snd, h0, Pi.zero_apply, norm_zero]
      exact mul_nonneg (norm_nonneg L) (weight_nonneg ξ _)
  · rw [mixedDeriv_cons_left_comp_snd, norm_zero]
    exact mul_nonneg (norm_nonneg L) (weight_nonneg ξ _)

/-- A linear function of the frequency is a uniform symbol of order one. These are the symbols of
constant-coefficient first-order differential operators without zeroth-order term. -/
def ofFrequencyLinear (L : CoordinateSpace n →L[ℝ] V →L[ℂ] W) : Symbol n V W 1 where
  coefficient p := L p.2
  smooth := L.contDiff.comp contDiff_snd
  derivative_bound _ _ α β := by
    obtain ⟨C, hC, h⟩ := ofFrequencyLinear_bound L α β
    exact ⟨C, hC, fun x _ ξ => h x ξ⟩

@[simp]
theorem coefficient_ofFrequencyLinear (L : CoordinateSpace n →L[ℝ] V →L[ℂ] W) :
    (ofFrequencyLinear L).coefficient = fun p => L p.2 :=
  (rfl)

@[simp]
theorem isUniform_ofFrequencyLinear (L : CoordinateSpace n →L[ℝ] V →L[ℂ] W) :
    (ofFrequencyLinear L).IsUniform :=
  ofFrequencyLinear_bound L

/-- A nonzero linear function of the frequency is not a symbol of order zero: an order-zero
symbol is bounded in the frequency at a fixed position. -/
theorem coefficient_ne_ofFrequencyLinear {L : CoordinateSpace n →L[ℝ] V →L[ℂ] W} (hL : L ≠ 0)
    (a : Symbol n V W 0) : a.coefficient ≠ (ofFrequencyLinear L).coefficient := by
  intro ha
  obtain ⟨C, -, hC⟩ := a.derivative_bound {0} isCompact_singleton [] []
  refine hL (ContinuousLinearMap.coe_injective
    (LinearMap.eq_zero_of_forall_norm_apply_le (f := L.toLinearMap) (C := C) fun v => ?_))
  simpa [ha] using hC 0 rfl v

end Symbol

end TauCeti
