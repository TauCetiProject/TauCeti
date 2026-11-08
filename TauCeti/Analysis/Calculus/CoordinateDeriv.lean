/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Data.List.Sublists
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

Both satisfy the general Leibniz rule for a continuous bilinear map `B`: the derivative of
`x ↦ B (f x) (g x)` along a word `α` is the sum, over the pairs `(s, t)` of complementary subwords
of `α` (`α.sublists'.revzip`), of `B (∂^s f x) (∂^t g x)`
(`ContinuousLinearMap.coordinateDeriv_of_bilinear`,
`ContinuousLinearMap.mixedDeriv_of_bilinear`). This is what gives the product estimates of the
symbol calculus.

## Main declarations

* `TauCeti.CoordinateSpace n`: the Euclidean space `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
* `TauCeti.coordinateDeriv`: the iterated coordinate derivative along a word of indices.
* `TauCeti.coordinateDeriv_eq_iteratedFDeriv`: its comparison with `iteratedFDeriv`.
* `ContDiff.coordinateDeriv_snd`: joint smoothness of partial derivatives in the second variable.
* `TauCeti.coordinateDeriv_coordinateDeriv_comm`: partial derivatives in different variables
  commute.
* `TauCeti.mixedDeriv`: the mixed position-frequency derivative `∂_x^α ∂_ξ^β`.
* `TauCeti.mixedDeriv_eq_iteratedFDeriv`, `TauCeti.mixedDeriv_eq_iteratedFDeriv_append`: its
  comparison with `iteratedFDeriv` on the directions `TauCeti.mixedDirections`.
* `ContinuousLinearMap.coordinateDeriv_of_bilinear`, `ContinuousLinearMap.mixedDeriv_of_bilinear`:
  the Leibniz rules.
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

/-- Coordinate derivatives along a word of length `k` of a `C^N` function are `C^m` whenever
`m + k ≤ N`. -/
theorem _root_.ContDiff.coordinateDeriv_of_le {N m : WithTop ℕ∞} {f : CoordinateSpace n → A}
    (hf : ContDiff ℝ N f) (α : List (Fin n)) (hm : m + α.length ≤ N) :
    ContDiff ℝ m (coordinateDeriv α f) := by
  induction α generalizing m with
  | nil => exact hf.of_le (by simpa using hm)
  | cons j js ih =>
    refine ((ih ?_).fderiv_right (m := m) le_rfl).clm_apply contDiff_const
    simpa [add_assoc, add_comm (1 : WithTop ℕ∞)] using hm

/-- Iterated coordinate derivatives of a smooth function are smooth. -/
theorem _root_.ContDiff.coordinateDeriv {f : CoordinateSpace n → A} (hf : ContDiff ℝ ∞ f)
    (α : List (Fin n)) : ContDiff ℝ ∞ (coordinateDeriv α f) :=
  hf.coordinateDeriv_of_le α (by simp)

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

@[simp]
theorem coordinateDeriv_neg (α : List (Fin n)) (f : CoordinateSpace n → A) :
    coordinateDeriv α (-f) = -coordinateDeriv α f := by
  induction α with
  | nil => rfl
  | cons j js ih =>
    funext x
    rw [coordinateDeriv_cons, ih, fderiv_neg, neg_apply, Pi.neg_apply,
      coordinateDeriv_cons]

@[simp]
theorem coordinateDeriv_zero (α : List (Fin n)) :
    coordinateDeriv α (0 : CoordinateSpace n → A) = 0 := by
  induction α with
  | nil => rfl
  | cons j js ih =>
    funext x
    rw [coordinateDeriv_cons, ih, fderiv_zero, Pi.zero_apply, Pi.zero_apply, zero_apply]

/-- Coordinate derivatives of a finite sum of `C^k` functions, along a word of length `k`, are the
sum of the coordinate derivatives. -/
theorem coordinateDeriv_sum {ι : Type*} {s : Finset ι} (α : List (Fin n))
    {f : ι → CoordinateSpace n → A} (hf : ∀ i ∈ s, ContDiff ℝ α.length (f i)) :
    coordinateDeriv α (∑ i ∈ s, f i) = ∑ i ∈ s, coordinateDeriv α (f i) := by
  funext x
  have hsum : ContDiff ℝ α.length (∑ i ∈ s, f i) := by
    convert ContDiff.sum hf using 1
    exact Finset.sum_fn s f
  rw [Finset.sum_apply, coordinateDeriv_eq_iteratedFDeriv α hsum,
    iteratedFDeriv_sum_apply fun i hi => (hf i hi).contDiffAt, sum_apply]
  exact Finset.sum_congr rfl fun i hi => (coordinateDeriv_eq_iteratedFDeriv α (hf i hi) x).symm

/-- Coordinate derivatives of a finite sum, indexed by a list, of `C^k` functions, along a word of
length `k`, are the sum of the coordinate derivatives. -/
theorem coordinateDeriv_list_sum {ι : Type*} {L : List ι} (α : List (Fin n))
    {f : ι → CoordinateSpace n → A} (hf : ∀ i ∈ L, ContDiff ℝ α.length (f i))
    (x : CoordinateSpace n) :
    coordinateDeriv α (fun y => (L.map fun i => f i y).sum) x =
      (L.map fun i => coordinateDeriv α (f i) x).sum := by
  have h : (fun y => (L.map fun i => f i y).sum) = ∑ k : Fin L.length, f L[k.1] := by
    funext y
    rw [Finset.sum_apply]
    exact (Fin.sum_univ_fun_getElem L fun i => f i y).symm
  rw [h, coordinateDeriv_sum α fun k _ => hf _ (List.getElem_mem k.2), Finset.sum_apply]
  exact Fin.sum_univ_fun_getElem L fun i => coordinateDeriv α (f i) x

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

/-- Partial coordinate derivatives in the second variable, along a word of length `k`, of a `C^N`
function of two variables are jointly `C^m` whenever `m + k ≤ N`. -/
theorem _root_.ContDiff.coordinateDeriv_snd_of_le {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {N m : WithTop ℕ∞} {g : P × CoordinateSpace n → A} (hg : ContDiff ℝ N g)
    (α : List (Fin n)) (hm : m + α.length ≤ N) :
    ContDiff ℝ m fun p : P × CoordinateSpace n => coordinateDeriv α (fun η => g (p.1, η)) p.2 := by
  induction α generalizing m with
  | nil => exact hg.of_le (by simpa using hm)
  | cons j js ih =>
    simp only [coordinateDeriv_cons]
    refine (ContDiff.fderiv (𝕜 := ℝ) (f := fun p η => coordinateDeriv js (fun η => g (p.1, η)) η)
      ?_ contDiff_snd (m := m + 1) (n := m) le_rfl).clm_apply contDiff_const
    refine (ih ?_).comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    simpa [add_assoc, add_comm (1 : WithTop ℕ∞)] using hm

/-- Partial coordinate derivatives in the second variable of a smooth function of two variables
are jointly smooth. -/
theorem _root_.ContDiff.coordinateDeriv_snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {g : P × CoordinateSpace n → A} (hg : ContDiff ℝ ∞ g) (α : List (Fin n)) :
    ContDiff ℝ ∞ fun p : P × CoordinateSpace n => coordinateDeriv α (fun η => g (p.1, η)) p.2 :=
  hg.coordinateDeriv_snd_of_le α (by simp)

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

/-- The directions of the mixed derivative `∂_x^α ∂_ξ^β` in `ℝⁿ × ℝⁿ`: the standard basis vectors
of the position space named by `α`, followed by those of the frequency space named by `β`. -/
def mixedDirections (α β : List (Fin n)) : List (CoordinateSpace n × CoordinateSpace n) :=
  α.map (fun j => (EuclideanSpace.single j 1, 0)) ++
    β.map (fun j => (0, EuclideanSpace.single j 1))

theorem mixedDirections_def (α β : List (Fin n)) :
    mixedDirections α β = α.map (fun j => (EuclideanSpace.single j 1, 0)) ++
      β.map (fun j => (0, EuclideanSpace.single j 1)) :=
  (rfl)

@[simp]
theorem mixedDirections_cons (j : Fin n) (α β : List (Fin n)) :
    mixedDirections (j :: α) β = (EuclideanSpace.single j 1, 0) :: mixedDirections α β :=
  (rfl)

@[simp]
theorem mixedDirections_nil_cons (j : Fin n) (β : List (Fin n)) :
    mixedDirections [] (j :: β) = (0, EuclideanSpace.single j 1) :: mixedDirections [] β :=
  (rfl)

@[simp]
theorem length_mixedDirections (α β : List (Fin n)) :
    (mixedDirections α β).length = α.length + β.length := by
  simp [mixedDirections_def]

/-- The directions of `∂_x^α ∂_ξ^β` are unit vectors. -/
theorem prod_norm_mixedDirections (α β : List (Fin n)) :
    ∏ i, ‖(mixedDirections α β).get i‖ = 1 := by
  refine (Fin.prod_univ_fun_getElem (mixedDirections α β) Norm.norm).trans ?_
  simp [mixedDirections_def, Function.comp_def, Prod.norm_def, PiLp.norm_single]

/-- The mixed derivative of a `C^(|α| + |β|)` function is its Fréchet derivative of order
`|α| + |β|`, evaluated on the standard basis vectors of the position space named by `α`, followed
by those of the frequency space named by `β` (`TauCeti.mixedDirections`). -/
theorem mixedDeriv_eq_iteratedFDeriv (α β : List (Fin n))
    {a : CoordinateSpace n × CoordinateSpace n → A} (ha : ContDiff ℝ (α.length + β.length) a)
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = iteratedFDeriv ℝ (mixedDirections α β).length a (x, ξ)
      fun i => (mixedDirections α β).get i := by
  obtain ⟨N, ha, hN⟩ : ∃ N : ℕ, ContDiff ℝ N a ∧ α.length + β.length ≤ N :=
    ⟨_, by exact_mod_cast ha, le_rfl⟩
  clear ‹ContDiff ℝ (α.length + β.length) a›
  -- The derivatives of `a` of an order below `N` along fixed directions are differentiable, and
  -- one more derivative along `v` prepends `v` to the directions.
  have hd : ∀ L : List (CoordinateSpace n × CoordinateSpace n), L.length < N →
      Differentiable ℝ fun q => iteratedFDeriv ℝ L.length a q fun i => L.get i := fun L hL =>
    (ha.differentiable_iteratedFDeriv (mod_cast hL)).continuousMultilinear_apply_const _
  -- Differentiating along a curve `g` with derivative `g'` at `y`, in the direction `u`, prepends
  -- `g' u` to the directions.
  have hstep : ∀ L : List (CoordinateSpace n × CoordinateSpace n), L.length < N →
      ∀ {g : CoordinateSpace n → CoordinateSpace n × CoordinateSpace n}
        {g' : CoordinateSpace n →L[ℝ] CoordinateSpace n × CoordinateSpace n} {y},
        HasFDerivAt g g' y →
      ∀ u, iteratedFDeriv ℝ (g' u :: L).length a (g y) (fun i => (g' u :: L).get i) =
        fderiv ℝ (fun y => iteratedFDeriv ℝ L.length a (g y) fun i => L.get i) y u :=
    fun L hL g g' y hg u => by
      have h := ((hd L hL (g y)).hasFDerivAt.comp y hg).fderiv
      simp only [Function.comp_def] at h
      rw [h, ContinuousLinearMap.comp_apply, fderiv_continuousMultilinear_apply_const_apply
        (ha.differentiable_iteratedFDeriv (mod_cast hL) (g y))]
      exact iteratedFDeriv_succ_apply_left _
  induction α generalizing x with
  | nil =>
    simp only [List.length_nil, zero_add] at hN
    induction β generalizing ξ with
    | nil => exact (iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := a) (x := (x, ξ)) _).symm
    | cons j js ih =>
      have hL : (mixedDirections [] js).length < N := by
        simp only [length_mixedDirections, List.length_nil, zero_add, List.length_cons] at hN ⊢
        omega
      rw [mixedDirections_nil_cons]
      refine Eq.trans ?_
        (hstep _ hL (hasFDerivAt_prodMk_right x ξ) (EuclideanSpace.single j 1)).symm
      rw [← funext fun η => ih η (by simp only [List.length_cons] at hN; omega)]
      -- With no position derivatives, `mixedDeriv [] (j :: js) a x` unfolds to the frequency
      -- derivative of `mixedDeriv [] js a x`.
      rfl
  | cons j js ih =>
    have hL : (mixedDirections js β).length < N := by
      simp only [length_mixedDirections, List.length_cons] at hN ⊢
      omega
    rw [mixedDirections_cons]
    refine Eq.trans ?_
      (hstep _ hL (hasFDerivAt_prodMk_left x ξ) (EuclideanSpace.single j 1)).symm
    rw [← funext fun y => ih y (by simp only [List.length_cons] at hN; omega)]
    simp only [mixedDeriv_def, coordinateDeriv_cons]

/-- The mixed derivative of a `C^(|α| + |β|)` function is its Fréchet derivative of order
`|α| + |β|`, evaluated on the standard basis vectors of the position space named by `α`, followed
by those of the frequency space named by `β`, in the `Fin.append` form of the estimates for
derivatives in position and frequency directions. -/
theorem mixedDeriv_eq_iteratedFDeriv_append (α β : List (Fin n))
    {a : CoordinateSpace n × CoordinateSpace n → A} (ha : ContDiff ℝ (α.length + β.length) a)
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = iteratedFDeriv ℝ (α.length + β.length) a (x, ξ)
      (Fin.append (fun i => (EuclideanSpace.single (α.get i) 1, 0))
        fun i => (0, EuclideanSpace.single (β.get i) 1)) := by
  -- Transport the directions along `(mixedDirections α β).length = |α| + |β|`.
  have hcast : ∀ {k} (h : (mixedDirections α β).length = k),
      iteratedFDeriv ℝ (mixedDirections α β).length a (x, ξ)
          (fun i => (mixedDirections α β).get i) =
        iteratedFDeriv ℝ k a (x, ξ) fun i => (mixedDirections α β).get (Fin.cast h.symm i) := by
    rintro _ rfl
    rfl
  rw [mixedDeriv_eq_iteratedFDeriv α β ha, hcast (length_mixedDirections α β)]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp [mixedDirections_def, List.getElem_append_left, List.getElem_append_right]

/-- A mixed derivative of a `C^(|α| + |β|)` function is bounded by the norm of its Fréchet
derivative of order `|α| + |β|`. -/
theorem norm_mixedDeriv_le (α β : List (Fin n)) {a : CoordinateSpace n × CoordinateSpace n → A}
    (ha : ContDiff ℝ (α.length + β.length) a) (x ξ : CoordinateSpace n) :
    ‖mixedDeriv α β a x ξ‖ ≤ ‖iteratedFDeriv ℝ (α.length + β.length) a (x, ξ)‖ := by
  rw [mixedDeriv_eq_iteratedFDeriv α β ha, ← length_mixedDirections]
  calc _ ≤ ‖iteratedFDeriv ℝ (mixedDirections α β).length a (x, ξ)‖ *
        ∏ i, ‖(mixedDirections α β).get i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = _ := by rw [prod_norm_mixedDirections, mul_one]

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

@[simp]
theorem mixedDeriv_neg (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (-a) x ξ = -mixedDeriv α β a x ξ := by
  have h : (fun y => coordinateDeriv β (fun η => (-a) (y, η)) ξ) =
      -fun y => coordinateDeriv β (fun η => a (y, η)) ξ := by
    funext y
    exact congrFun (coordinateDeriv_neg β _) ξ
  simp only [mixedDeriv_def]
  rw [h, coordinateDeriv_neg α, Pi.neg_apply]

@[simp]
theorem mixedDeriv_zero (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (0 : CoordinateSpace n × CoordinateSpace n → A) x ξ = 0 := by
  have h : (fun y => coordinateDeriv β (fun η => (0 : CoordinateSpace n × CoordinateSpace n → A)
      (y, η)) ξ) = 0 := by
    funext y
    exact congrFun (coordinateDeriv_zero β) ξ
  rw [mixedDeriv_def, h, coordinateDeriv_zero, Pi.zero_apply]

/-- Mixed derivatives at `x` only depend on the values at positions near `x`: if `a` and `b` agree
for all frequencies at all positions near `x`, then so do all their mixed derivatives at `x`. -/
theorem mixedDeriv_congr_of_eventually {x : CoordinateSpace n}
    (h : ∀ᶠ y in nhds x, ∀ η, a (y, η) = b (y, η)) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = mixedDeriv α β b x ξ := by
  have h' : (fun y => coordinateDeriv β (fun η => a (y, η)) ξ) =ᶠ[nhds x]
      fun y => coordinateDeriv β (fun η => b (y, η)) ξ := by
    filter_upwards [h] with y hy
    rw [show (fun η => a (y, η)) = fun η => b (y, η) from funext hy]
  rw [mixedDeriv_def, mixedDeriv_def, (h'.coordinateDeriv α).eq_of_nhds]

/-- If `a` vanishes for all frequencies at all positions near `x`, then so do all its mixed
derivatives at `x`. -/
theorem mixedDeriv_eq_zero_of_eventually {x : CoordinateSpace n}
    (h : ∀ᶠ y in nhds x, ∀ η, a (y, η) = 0) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β a x ξ = 0 :=
  (mixedDeriv_congr_of_eventually (b := 0) h α β ξ).trans (mixedDeriv_zero α β x ξ)

/-- Cutting `a` off outside the positions of an open set `U` does not change its mixed derivatives
at positions of `U`. -/
theorem mixedDeriv_indicator_prod_univ_of_mem {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {x : CoordinateSpace n} (hx : x ∈ U) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β ((U ×ˢ Set.univ).indicator a) x ξ = mixedDeriv α β a x ξ := by
  refine mixedDeriv_congr_of_eventually ?_ α β ξ
  filter_upwards [hU.mem_nhds hx] with y hy η
  exact Set.indicator_of_mem (Set.mk_mem_prod hy (Set.mem_univ η)) _

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

section Leibniz

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The first-order product rule for a coordinate derivative of `x ↦ B (f x) (g x)`. -/
private theorem fderiv_bilinear_single (B : F →L[ℝ] G →L[ℝ] H) {f : CoordinateSpace n → F}
    {g : CoordinateSpace n → G} {x : CoordinateSpace n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    fderiv ℝ (fun y => B (f y) (g y)) x (EuclideanSpace.single j 1) =
      B (f x) (coordinateDeriv [j] g x) + B (coordinateDeriv [j] f x) (g x) := by
  rw [B.fderiv_of_bilinear hf hg]
  simp [coordinateDeriv_cons]

/-- The **Leibniz rule** for coordinate derivatives: for a continuous bilinear map `B` and `C^k`
functions `f` and `g`, the derivative of `x ↦ B (f x) (g x)` along a word `α` of length `k` is the
sum, over the pairs `(s, t)` of complementary subwords of `α`, of `B (∂^s f x) (∂^t g x)`. -/
theorem _root_.ContinuousLinearMap.coordinateDeriv_of_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    {f : CoordinateSpace n → F} {g : CoordinateSpace n → G} {α : List (Fin n)}
    (hf : ContDiff ℝ α.length f) (hg : ContDiff ℝ α.length g) (x : CoordinateSpace n) :
    coordinateDeriv α (fun y => B (f y) (g y)) x =
      (α.sublists'.revzip.map fun p =>
        B (coordinateDeriv p.1 f x) (coordinateDeriv p.2 g x)).sum := by
  induction α generalizing x with
  | nil => simp [List.revzip]
  | cons j js ih =>
    have hle : ∀ q : List (Fin n), q.length ≤ js.length →
        ((1 : WithTop ℕ∞) + q.length) ≤ ((j :: js).length : ℕ) := fun q hq => by
      rw [List.length_cons, add_comm]
      exact_mod_cast Nat.succ_le_succ hq
    have hlen : ∀ p ∈ js.sublists'.revzip, p.1.length ≤ js.length ∧ p.2.length ≤ js.length :=
      fun p hp => by
        have h := (List.revzip_sublists' _ _ _ hp).length_eq
        rw [List.length_append] at h
        omega
    have hf1 : ∀ p ∈ js.sublists'.revzip, ContDiff ℝ 1 (coordinateDeriv p.1 f) := fun p hp =>
      hf.coordinateDeriv_of_le _ (hle _ (hlen p hp).1)
    have hg1 : ∀ p ∈ js.sublists'.revzip, ContDiff ℝ 1 (coordinateDeriv p.2 g) := fun p hp =>
      hg.coordinateDeriv_of_le _ (hle _ (hlen p hp).2)
    have hterm : ∀ p ∈ js.sublists'.revzip, ContDiff ℝ ([j] : List (Fin n)).length
        fun y => B (coordinateDeriv p.1 f y) (coordinateDeriv p.2 g y) := fun p hp =>
      B.isBoundedBilinearMap.contDiff.comp ((hf1 p hp).prodMk (hg1 p hp))
    rw [← List.singleton_append, coordinateDeriv_append,
      funext (ih (hf.of_le (by simp)) (hg.of_le (by simp))), coordinateDeriv_list_sum _ hterm]
    rw [List.map_congr_left fun p hp => (by
      rw [coordinateDeriv_cons, coordinateDeriv_nil, fderiv_bilinear_single B
        ((hf1 p hp).differentiable one_ne_zero x) ((hg1 p hp).differentiable one_ne_zero x)] :
      coordinateDeriv [j] (fun y => B (coordinateDeriv p.1 f y) (coordinateDeriv p.2 g y)) x = _)]
    simp only [coordinateDeriv_cons, coordinateDeriv_nil, List.sum_map_add, List.singleton_append,
      List.revzip_sublists'_cons, List.map_append, List.map_map, List.sum_append,
      Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]

/-- The **Leibniz rule** for mixed derivatives: for a continuous bilinear map `B` and `C^k`
functions `a` and `b`, where `k` is the total length of the words `α` and `β`, the mixed derivative
`∂_x^α ∂_ξ^β` of `p ↦ B (a p) (b p)` is the sum, over the pairs `(s, s')` of complementary subwords
of `α` and `(t, t')` of `β`, of `B (∂_x^s ∂_ξ^t a) (∂_x^s' ∂_ξ^t' b)`. -/
theorem _root_.ContinuousLinearMap.mixedDeriv_of_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    {a : CoordinateSpace n × CoordinateSpace n → F} {b : CoordinateSpace n × CoordinateSpace n → G}
    {α β : List (Fin n)} (ha : ContDiff ℝ (α.length + β.length) a)
    (hb : ContDiff ℝ (α.length + β.length) b) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => B (a p) (b p)) x ξ =
      (β.sublists'.revzip.map fun t => (α.sublists'.revzip.map fun s =>
        B (mixedDeriv s.1 t.1 a x ξ) (mixedDeriv s.2 t.2 b x ξ)).sum).sum := by
  have hle : ∀ q : List (Fin n), q.length ≤ β.length →
      ((α.length : WithTop ℕ∞) + q.length) ≤ ((α.length + β.length : ℕ) : WithTop ℕ∞) :=
    fun q hq => by exact_mod_cast Nat.add_le_add_left hq _
  have hlen : ∀ t ∈ β.sublists'.revzip, t.1.length ≤ β.length ∧ t.2.length ≤ β.length :=
    fun t ht => by
      have h := (List.revzip_sublists' _ _ _ ht).length_eq
      rw [List.length_append] at h
      omega
  -- The frequency derivatives of `a` and `b`, at `ξ`, as functions of the position.
  have hsa : ∀ t ∈ β.sublists'.revzip,
      ContDiff ℝ α.length fun y => coordinateDeriv t.1 (fun η => a (y, η)) ξ := fun t ht =>
    (ha.coordinateDeriv_snd_of_le t.1 (hle _ (hlen t ht).1)).comp (contDiff_prodMk_left ξ)
  have hsb : ∀ t ∈ β.sublists'.revzip,
      ContDiff ℝ α.length fun y => coordinateDeriv t.2 (fun η => b (y, η)) ξ := fun t ht =>
    (hb.coordinateDeriv_snd_of_le t.2 (hle _ (hlen t ht).2)).comp (contDiff_prodMk_left ξ)
  have hinner : (fun y => coordinateDeriv β (fun η => B (a (y, η)) (b (y, η))) ξ) =
      fun y => (β.sublists'.revzip.map fun t => B (coordinateDeriv t.1 (fun η => a (y, η)) ξ)
        (coordinateDeriv t.2 (fun η => b (y, η)) ξ)).sum :=
    funext fun y => B.coordinateDeriv_of_bilinear
      ((ha.comp (contDiff_prodMk_right y)).of_le (by simp))
      ((hb.comp (contDiff_prodMk_right y)).of_le (by simp)) ξ
  have hterm : ∀ t ∈ β.sublists'.revzip, ContDiff ℝ α.length fun y =>
      B (coordinateDeriv t.1 (fun η => a (y, η)) ξ) (coordinateDeriv t.2 (fun η => b (y, η)) ξ) :=
    fun t ht => B.isBoundedBilinearMap.contDiff.comp ((hsa t ht).prodMk (hsb t ht))
  rw [mixedDeriv_def, hinner, coordinateDeriv_list_sum _ hterm]
  congr 1
  exact List.map_congr_left fun t ht => B.coordinateDeriv_of_bilinear (hsa t ht) (hsb t ht) x

end Leibniz

end TauCeti
