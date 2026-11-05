/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Iterated coordinate derivatives on `ℝⁿ`

For a function `f : ℝⁿ → A` and a word `α = [j₁, …, jₖ]` of coordinate indices,
`TauCeti.coordinateDeriv α f = ∂_{j₁} ⋯ ∂_{jₖ} f` is the iterated partial derivative, the
innermost derivative being taken in the direction of the last letter. Multi-index estimates
such as the symbol estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` of pseudodifferential
calculus are stated with this operation, the length of the word being the order of the
derivative.

For a smooth function, `coordinateDeriv α f x` is the `k`-th Fréchet derivative evaluated on the
corresponding standard basis vectors (`TauCeti.coordinateDeriv_eq_iteratedFDeriv`), so it is
bounded by the norm of `iteratedFDeriv`, and it is additive and homogeneous in `f`. Smoothness is
preserved, also jointly in an additional parameter (`ContDiff.coordinateDeriv_snd`,
`ContDiff.coordinateDeriv_fst`). For a smooth function of two variables, iterated coordinate
derivatives in the two variables commute (`TauCeti.coordinateDeriv_coordinateDeriv_comm`), by the
symmetry of second derivatives.

For a function `a(x, ξ)` of a position and a frequency, `TauCeti.mixedDeriv α β a x ξ` is the
mixed derivative `∂_x^α ∂_ξ^β a(x, ξ)`, taking the frequency derivatives first. It is linear in
smooth `a`, local in the position, and for smooth `a` the order of the two kinds of derivatives
does not matter (`TauCeti.mixedDeriv_eq_coordinateDeriv_snd`).

## Main declarations

* `TauCeti.CoordinateSpace n`: the Euclidean space `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
* `TauCeti.coordinateDeriv`: the iterated coordinate derivative along a word of indices.
* `TauCeti.coordinateDeriv_eq_iteratedFDeriv`: its comparison with `iteratedFDeriv`.
* `ContDiff.coordinateDeriv_snd`: joint smoothness of partial derivatives in the second variable.
* `TauCeti.coordinateDeriv_coordinateDeriv_comm`: partial derivatives in different variables
  commute.
* `TauCeti.mixedDeriv`: the mixed position-frequency derivative `∂_x^α ∂_ξ^β`.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

/-- The Euclidean coordinate space `ℝⁿ`, the model space of the charts of an `n`-manifold. -/
abbrev CoordinateSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The iterated coordinate derivative `∂_{j₁} ⋯ ∂_{jₖ} f` along the word `[j₁, …, jₖ]`. The
derivative in the direction of the last index is taken first. -/
def coordinateDeriv (indices : List (Fin n)) (f : CoordinateSpace n → A) :
    CoordinateSpace n → A :=
  match indices with
  | [] => f
  | j :: js => fun x => fderiv ℝ (coordinateDeriv js f) x (EuclideanSpace.single j 1)

@[simp]
theorem coordinateDeriv_nil (f : CoordinateSpace n → A) : coordinateDeriv [] f = f := (rfl)

theorem coordinateDeriv_cons (j : Fin n) (js : List (Fin n)) (f : CoordinateSpace n → A)
    (x : CoordinateSpace n) :
    coordinateDeriv (j :: js) f x =
      fderiv ℝ (coordinateDeriv js f) x (EuclideanSpace.single j 1) := (rfl)

/-- Differentiating along a concatenated word differentiates along the second word first. -/
theorem coordinateDeriv_append (α β : List (Fin n)) (f : CoordinateSpace n → A) :
    coordinateDeriv (α ++ β) f = coordinateDeriv α (coordinateDeriv β f) := by
  induction α with
  | nil => rfl
  | cons j js ih =>
    funext x
    rw [List.cons_append, coordinateDeriv_cons, coordinateDeriv_cons, ih]

/-- Iterated coordinate derivatives of a smooth function are smooth. -/
theorem _root_.ContDiff.coordinateDeriv {f : CoordinateSpace n → A} (hf : ContDiff ℝ ∞ f)
    (α : List (Fin n)) : ContDiff ℝ ∞ (coordinateDeriv α f) := by
  induction α with
  | nil => exact hf
  | cons j js ih =>
    exact (ih.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- A coordinate derivative of a `C^k` function along a word of length `k` is its `k`-th Fréchet
derivative, evaluated on the standard basis vectors named by the word, in the same order. -/
theorem coordinateDeriv_eq_iteratedFDeriv (α : List (Fin n)) {f : CoordinateSpace n → A}
    (hf : ContDiff ℝ α.length f) (x : CoordinateSpace n) :
    coordinateDeriv α f x =
      iteratedFDeriv ℝ α.length f x fun i => EuclideanSpace.single (α.get i) 1 := by
  induction α generalizing x with
  | nil => simp
  | cons j js ih =>
    have hf' : ContDiff ℝ (js.length + 1 : ℕ) f := hf
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ js.length f) x :=
      (hf'.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self _)) x
    rw [coordinateDeriv_cons,
      funext (ih (hf'.of_le (by exact_mod_cast Nat.le_succ _))),
      fderiv_continuousMultilinear_apply_const_apply hd]
    exact (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := f) (x := x) (n := js.length)
      fun i => EuclideanSpace.single ((j :: js).get i) 1).symm

/-- A coordinate derivative of a `C^k` function along a word of length `k` is bounded by the norm
of its `k`-th Fréchet derivative. -/
theorem norm_coordinateDeriv_le (α : List (Fin n)) {f : CoordinateSpace n → A}
    (hf : ContDiff ℝ α.length f) (x : CoordinateSpace n) :
    ‖coordinateDeriv α f x‖ ≤ ‖iteratedFDeriv ℝ α.length f x‖ := by
  rw [coordinateDeriv_eq_iteratedFDeriv α hf]
  refine ((iteratedFDeriv ℝ α.length f x).le_opNorm _).trans (le_of_eq ?_)
  simp

theorem coordinateDeriv_add (α : List (Fin n)) {f g : CoordinateSpace n → A}
    (hf : ContDiff ℝ α.length f) (hg : ContDiff ℝ α.length g) :
    coordinateDeriv α (f + g) = coordinateDeriv α f + coordinateDeriv α g := by
  funext x
  rw [Pi.add_apply, coordinateDeriv_eq_iteratedFDeriv α (f := f + g) (hf.add hg),
    coordinateDeriv_eq_iteratedFDeriv α hf, coordinateDeriv_eq_iteratedFDeriv α hg,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, add_apply]

theorem coordinateDeriv_const_smul {R : Type*} [Semiring R] [Module R A] [SMulCommClass ℝ R A]
    [ContinuousConstSMul R A] (α : List (Fin n)) {f : CoordinateSpace n → A}
    (hf : ContDiff ℝ α.length f) (c : R) :
    coordinateDeriv α (c • f) = c • coordinateDeriv α f := by
  funext x
  rw [Pi.smul_apply, coordinateDeriv_eq_iteratedFDeriv α (f := c • f) (hf.const_smul c),
    coordinateDeriv_eq_iteratedFDeriv α hf, iteratedFDeriv_const_smul_apply hf.contDiffAt,
    smul_apply]

theorem coordinateDeriv_neg (α : List (Fin n)) {f : CoordinateSpace n → A}
    (hf : ContDiff ℝ α.length f) :
    coordinateDeriv α (-f) = -coordinateDeriv α f := by
  funext x
  rw [Pi.neg_apply, coordinateDeriv_eq_iteratedFDeriv α (f := -f) hf.neg,
    coordinateDeriv_eq_iteratedFDeriv α hf, iteratedFDeriv_neg_apply, neg_apply]

@[simp]
theorem coordinateDeriv_zero (α : List (Fin n)) :
    coordinateDeriv α (0 : CoordinateSpace n → A) = 0 := by
  induction α with
  | nil => rfl
  | cons j js ih =>
    funext x
    rw [coordinateDeriv_cons, ih, fderiv_zero, Pi.zero_apply, Pi.zero_apply, zero_apply]

/-- Coordinate derivatives at a point only depend on the germ of the function there. -/
theorem _root_.Filter.EventuallyEq.coordinateDeriv {f g : CoordinateSpace n → A}
    {x : CoordinateSpace n} (h : f =ᶠ[nhds x] g) (α : List (Fin n)) :
    coordinateDeriv α f =ᶠ[nhds x] coordinateDeriv α g := by
  induction α with
  | nil => exact h
  | cons j js ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    rw [coordinateDeriv_cons, coordinateDeriv_cons, hy.fderiv_eq]

/-- Every nonempty coordinate derivative of a constant function vanishes. -/
theorem coordinateDeriv_const (c : A) {α : List (Fin n)} (hα : α ≠ []) :
    coordinateDeriv α (fun _ : CoordinateSpace n => c) = 0 := by
  obtain ⟨j, js, rfl⟩ := List.exists_cons_of_ne_nil hα
  funext x
  rw [coordinateDeriv_eq_iteratedFDeriv _ contDiff_const,
    iteratedFDeriv_const_of_ne (n := (j :: js).length) (List.length_pos_of_ne_nil hα).ne',
    Pi.zero_apply, Pi.zero_apply, zero_apply]

/-- Partial coordinate derivatives in the second variable of a smooth function of two variables
are jointly smooth. -/
theorem _root_.ContDiff.coordinateDeriv_snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {g : P × CoordinateSpace n → A} (hg : ContDiff ℝ ∞ g) (α : List (Fin n)) :
    ContDiff ℝ ∞ fun p : P × CoordinateSpace n => coordinateDeriv α (fun η => g (p.1, η)) p.2 := by
  induction α with
  | nil => exact hg
  | cons j js ih =>
    simp only [coordinateDeriv_cons]
    refine (ContDiff.fderiv (𝕜 := ℝ) (f := fun p η => coordinateDeriv js (fun η => g (p.1, η)) η)
      ?_ contDiff_snd (m := ∞) (n := ∞) le_rfl).clm_apply contDiff_const
    exact ih.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)

/-- Partial coordinate derivatives in the first variable of a smooth function of two variables
are jointly smooth. -/
theorem _root_.ContDiff.coordinateDeriv_fst {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {g : CoordinateSpace n × P → A} (hg : ContDiff ℝ ∞ g) (α : List (Fin n)) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × P => coordinateDeriv α (fun y => g (y, p.2)) p.1 :=
  ((hg.comp (contDiff_snd.prodMk contDiff_fst)).coordinateDeriv_snd α).comp
    (contDiff_snd.prodMk contDiff_fst)

/-- A first-order partial derivative in the first variable commutes with every iterated
coordinate derivative in the second variable. -/
private theorem coordinateDeriv_snd_fderiv_fst {G : CoordinateSpace n × CoordinateSpace n → A}
    (hG : ContDiff ℝ ∞ G) (v : CoordinateSpace n) (β : List (Fin n)) (x ξ : CoordinateSpace n) :
    coordinateDeriv β (fun η => fderiv ℝ (fun y => G (y, η)) x v) ξ =
      fderiv ℝ (fun y => coordinateDeriv β (fun η => G (y, η)) ξ) x v := by
  induction β generalizing ξ with
  | nil => rfl
  | cons i is ih =>
    rw [coordinateDeriv_cons, funext ih]
    exact fderiv_fderiv_slice_apply_comm
      (F := fun q => coordinateDeriv is (fun η => G (q.2, η)) q.1)
      (((hG.coordinateDeriv_snd is).comp (contDiff_snd.prodMk contDiff_fst)).contDiffAt.of_le
        (by simp)) _ v

/-- The partial coordinate derivatives in the second variable of a smooth function of two
variables, at a fixed value of the second variable, are smooth in the first variable. -/
theorem contDiff_coordinateDeriv_slice {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {g : P × CoordinateSpace n → A} (hg : ContDiff ℝ ∞ g) (β : List (Fin n))
    (ξ : CoordinateSpace n) : ContDiff ℝ ∞ fun y => coordinateDeriv β (fun η => g (y, η)) ξ :=
  (hg.coordinateDeriv_snd β).comp (contDiff_prodMk_left ξ)

/-- Iterated coordinate derivatives in the two variables of a smooth function commute. -/
theorem coordinateDeriv_coordinateDeriv_comm {G : CoordinateSpace n × CoordinateSpace n → A}
    (hG : ContDiff ℝ ∞ G) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    coordinateDeriv β (fun η => coordinateDeriv α (fun y => G (y, η)) x) ξ =
      coordinateDeriv α (fun y => coordinateDeriv β (fun η => G (y, η)) ξ) x := by
  induction α generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [coordinateDeriv_cons]
    rw [coordinateDeriv_snd_fderiv_fst (G := fun q => coordinateDeriv js (fun y => G (y, q.2)) q.1)
      (hG.coordinateDeriv_fst js)]
    exact congrArg (fun F => fderiv ℝ F x _) (funext ih)


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

/-- A frequency-independent function has no frequency derivatives. -/
theorem mixedDeriv_comp_fst (f : CoordinateSpace n → A) (α : List (Fin n))
    {β : List (Fin n)} (hβ : β ≠ []) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => f p.1) x ξ = 0 := by
  rw [mixedDeriv_def]
  simp only [coordinateDeriv_const _ hβ, Pi.zero_apply]
  rw [← Pi.zero_def, coordinateDeriv_zero, Pi.zero_apply]

/-- The position derivatives of a frequency-independent function are those of its profile. -/
theorem mixedDeriv_nil_comp_fst (f : CoordinateSpace n → A) (α : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α [] (fun p => f p.1) x ξ = coordinateDeriv α f x := by
  simp only [mixedDeriv_def, coordinateDeriv_nil]

section Linear

variable {a b : CoordinateSpace n × CoordinateSpace n → A}

theorem mixedDeriv_add (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (a + b) x ξ = mixedDeriv α β a x ξ + mixedDeriv α β b x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (a + b) (y, η)) ξ) =
      (fun y => coordinateDeriv β (fun η => a (y, η)) ξ) +
        fun y => coordinateDeriv β (fun η => b (y, η)) ξ := by
    funext y
    exact congrFun (coordinateDeriv_add β (contDiff_infty.1 (ha.comp (contDiff_prodMk_right y)) _)
      (contDiff_infty.1 (hb.comp (contDiff_prodMk_right y)) _)) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_add α
    (contDiff_infty.1 (contDiff_coordinateDeriv_slice ha β ξ) _)
    (contDiff_infty.1 (contDiff_coordinateDeriv_slice hb β ξ) _), Pi.add_apply]

theorem mixedDeriv_const_smul {R : Type*} [Semiring R] [Module R A] [SMulCommClass ℝ R A]
    [ContinuousConstSMul R A] (ha : ContDiff ℝ ∞ a) (c : R) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (c • a) x ξ = c • mixedDeriv α β a x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (c • a) (y, η)) ξ) =
      c • fun y => coordinateDeriv β (fun η => a (y, η)) ξ := by
    funext y
    exact congrFun
      (coordinateDeriv_const_smul β (contDiff_infty.1 (ha.comp (contDiff_prodMk_right y)) _) c) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_const_smul α
    (contDiff_infty.1 (contDiff_coordinateDeriv_slice ha β ξ) _), Pi.smul_apply]

theorem mixedDeriv_neg (ha : ContDiff ℝ ∞ a) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (-a) x ξ = -mixedDeriv α β a x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (-a) (y, η)) ξ) =
      -fun y => coordinateDeriv β (fun η => a (y, η)) ξ := by
    funext y
    exact congrFun
      (coordinateDeriv_neg β (contDiff_infty.1 (ha.comp (contDiff_prodMk_right y)) _)) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_neg α
    (contDiff_infty.1 (contDiff_coordinateDeriv_slice ha β ξ) _), Pi.neg_apply]

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

variable {α β : List (Fin n)} {x ξ : CoordinateSpace n} {C D w : ℝ}

/-- Bounds `C * w` and `D * w` on mixed derivatives of smooth `a` and `b` add to a bound on the
mixed derivative of `a + b`. -/
theorem norm_mixedDeriv_add_le (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haC : ‖mixedDeriv α β a x ξ‖ ≤ C * w) (hbD : ‖mixedDeriv α β b x ξ‖ ≤ D * w) :
    ‖mixedDeriv α β (a + b) x ξ‖ ≤ (C + D) * w := by
  rw [mixedDeriv_add ha hb, add_mul]
  exact (norm_add_le _ _).trans (add_le_add haC hbD)

/-- A bound `C * w` on a mixed derivative of smooth `a` gives the bound `(‖c‖ * C) * w` on the
mixed derivative of `c • a`. -/
theorem norm_mixedDeriv_smul_le {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 A]
    [SMulCommClass ℝ 𝕜 A] (ha : ContDiff ℝ ∞ a) (c : 𝕜) (haC : ‖mixedDeriv α β a x ξ‖ ≤ C * w) :
    ‖mixedDeriv α β (c • a) x ξ‖ ≤ (‖c‖ * C) * w := by
  rw [mixedDeriv_const_smul ha, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left haC (norm_nonneg c)

end Linear

end TauCeti
