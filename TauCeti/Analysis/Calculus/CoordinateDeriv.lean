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

## Main declarations

* `TauCeti.CoordinateSpace n`: the Euclidean space `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
* `TauCeti.coordinateDeriv`: the iterated coordinate derivative along a word of indices.
* `TauCeti.coordinateDeriv_eq_iteratedFDeriv`: its comparison with `iteratedFDeriv`.
* `ContDiff.coordinateDeriv_snd`: joint smoothness of partial derivatives in the second variable.
* `TauCeti.coordinateDeriv_coordinateDeriv_comm`: partial derivatives in different variables
  commute.
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

end TauCeti
