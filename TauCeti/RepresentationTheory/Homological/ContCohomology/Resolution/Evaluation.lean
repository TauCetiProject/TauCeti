/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic

/-!
# Evaluating the coinduced resolution at tuples of group elements

The `n`-th term of Mathlib's coinduced resolution `TopRep.resolutionX X n` is the iterated space
of continuous functions `C(G, C(G, …, C(G, X)))` with `n` copies of `G`. This file evaluates an
element `F` of it at a tuple `x : Fin n → G`, giving the function
`TopRep.resolutionEval X n F : (Fin n → G) → X`, `x ↦ F (x 0) (x 1) ⋯ (x (n - 1))`, and records
how the structure of the resolution reads on these values:

* evaluation is injective (`TopRep.resolutionEval_injective`);
* the action becomes the diagonal action, `(g • F) x = g • F (g⁻¹ x)`
  (`TopRep.resolutionEval_ρ_apply`), so that an invariant `F` satisfies `F (g x) = g • F x`
  (`TopRep.resolutionEval_mul_left_of_forall_ρ_eq`);
* the recursively defined differential `TopRep.d` becomes the alternating sum of face maps,
  `(d F) x = ∑ᵢ (-1)ⁱ F (x₀, …, x̂ᵢ, …, xₙ)` (`TopRep.resolutionEval_d_apply`);
* every continuous function on `Gⁿ` is the evaluation of an element, its iterated currying
  `TopRep.resolutionCurry` (`TopRep.resolutionEval_resolutionCurry`);
* over a locally compact group, the evaluation of every element is continuous
  (`TopRep.continuous_resolutionEval`).

Over a locally compact group, evaluation thus identifies the `n`-th term of the resolution with
the continuous functions `C(Gⁿ, X)` with the diagonal action, and its differential with the
alternating face differential. These are the formulas that compare the invariants of the
resolution, Mathlib's homogeneous cochains, with the inhomogeneous cochains `C(Gⁿ, X)`. Currying
needs no hypothesis on `G`; only the continuity of evaluations uses local compactness, through the
joint continuity of `C(G, Y) × G → Y`.

## Main definitions

* `TopRep.resolutionEval`: evaluation of the `n`-th term of the resolution at `n`-tuples, as a
  linear map.
* `TopRep.resolutionCurry`: the element of the `n`-th term obtained by currying a continuous
  function on `Gⁿ`.
-/

public section

namespace TopRep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep.{max v w} k G)

/-- The value `F (x 0) (x 1) ⋯ (x (n - 1))` of an element `F` of the `n`-th term
`C(G, C(G, …, C(G, X)))` of the coinduced resolution at a tuple `x : Fin n → G`, as a linear
function of `F`. -/
noncomputable def resolutionEval : (n : ℕ) → (resolutionX X n).V →ₗ[k] ((Fin n → G) → X.V)
  | 0 => LinearMap.pi fun _ ↦ LinearMap.id
  | n + 1 =>
    { toFun F x := resolutionEval n (F (x 0)) (Fin.tail x)
      map_add' F F' := by ext x; simp
      map_smul' c F := by ext x; simp }

-- Not a `simp` lemma, like `TopRep.resolutionEval_succ_apply`: `simp` does not find it.
theorem resolutionEval_zero_apply (F : (resolutionX X 0).V) (x : Fin 0 → G) :
    resolutionEval X 0 F x = F :=
  (rfl)

-- Not a `simp` lemma: the discrimination tree does not reduce the carrier `resolutionX X (n + 1)`
-- of the coinduced resolution, so `simp` never finds this lemma; rewrite with it instead.
theorem resolutionEval_succ_apply (n : ℕ) (F : (resolutionX X (n + 1)).V) (x : Fin (n + 1) → G) :
    resolutionEval X (n + 1) F x = resolutionEval X n (F (x 0)) (Fin.tail x) :=
  (rfl)

/-- An element of the coinduced resolution is determined by its values at tuples. -/
theorem resolutionEval_injective : ∀ n : ℕ, Function.Injective (resolutionEval X n)
  | 0, F, F', h => by
    have := congrFun h Fin.elim0
    rwa [resolutionEval_zero_apply, resolutionEval_zero_apply] at this
  | n + 1, F, F', h => by
    refine ContinuousMap.ext fun y ↦ resolutionEval_injective n (funext fun x ↦ ?_)
    have := congrFun h (Fin.cons y x)
    rwa [resolutionEval_succ_apply, resolutionEval_succ_apply, Fin.cons_zero, Fin.tail_cons]
      at this

/-- On values at tuples, the action on the coinduced resolution is the diagonal action:
`(g • F) x = g • F (g⁻¹ x)`. -/
theorem resolutionEval_ρ_apply :
    ∀ (n : ℕ) (g : G) (F : (resolutionX X n).V) (x : Fin n → G),
      resolutionEval X n ((resolutionX X n).ρ g F) x =
        X.ρ g (resolutionEval X n F fun i ↦ g⁻¹ * x i)
  | 0, _, _, _ => rfl
  | n + 1, g, F, x => by
    rw [resolutionEval_succ_apply, resolutionEval_succ_apply, resolutionX_succ_ρ_apply_apply]
    exact resolutionEval_ρ_apply n g _ _

variable {X} in
/-- A `G`-invariant element `F` of the coinduced resolution satisfies
`F (g x₀, …, g xₙ₋₁) = g • F (x₀, …, xₙ₋₁)`. -/
theorem resolutionEval_mul_left_of_forall_ρ_eq {n : ℕ} {F : (resolutionX X n).V}
    (hF : ∀ g, (resolutionX X n).ρ g F = F) (g : G) (x : Fin n → G) :
    resolutionEval X n F (fun i ↦ g * x i) = X.ρ g (resolutionEval X n F x) := by
  conv_lhs => rw [← hF g, resolutionEval_ρ_apply]
  simp

/-- On values at tuples, the differential of the coinduced resolution is the alternating sum of
the face maps: `(d F) x = ∑ᵢ (-1)ⁱ F (x₀, …, x̂ᵢ, …, xₙ)`. -/
theorem resolutionEval_d_apply :
    ∀ (n : ℕ) (F : (resolutionX X n).V) (x : Fin (n + 1) → G),
      resolutionEval X (n + 1) ((d X n).hom F) x =
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • resolutionEval X n F (x ∘ i.succAbove)
  | 0, F, x => by
    rw [Fin.sum_univ_one, resolutionEval_succ_apply, resolutionEval_zero_apply,
      resolutionEval_zero_apply, d_zero]
    simp
  | n + 1, F, x => by
    rw [Fin.sum_univ_succ, resolutionEval_succ_apply, hom_d_succ_apply_apply, map_sub,
      Pi.sub_apply, resolutionEval_d_apply n, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp [Fin.succAbove_zero, Fin.tail_def, Function.comp_def]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Function.comp_def, resolutionEval_succ_apply]
      simp [pow_succ, Fin.tail_def, Function.comp_def]

/-! ### Currying continuous functions on tuples -/

/-- Iterated currying of a continuous function of a parameter `t : T` and a tuple
`x : Fin n → G`, into a continuous family of elements of the `n`-th term of the coinduced
resolution. The parameter makes the recursion possible: currying the first entry of the tuple
moves it into the parameter. -/
private noncomputable def resolutionCurryAux :
    (n : ℕ) → {T : Type (max v w)} → [TopologicalSpace T] → C(T × (Fin n → G), X.V) →
      C(T, (resolutionX X n).V)
  | 0, _, _, φ => φ.comp ⟨fun t ↦ (t, Fin.elim0), by fun_prop⟩
  | n + 1, _, _, φ => ContinuousMap.curry (resolutionCurryAux n
      (φ.comp ⟨fun p ↦ (p.1.1, Fin.cons p.1.2 p.2), by fun_prop⟩))

private theorem resolutionEval_resolutionCurryAux :
    ∀ (n : ℕ) {T : Type (max v w)} [TopologicalSpace T] (φ : C(T × (Fin n → G), X.V)) (t : T)
      (x : Fin n → G), resolutionEval X n (resolutionCurryAux X n φ t) x = φ (t, x)
  | 0, _, _, φ, t, x => by
    rw [resolutionEval_zero_apply]
    exact congrArg (fun y ↦ φ (t, y)) (Subsingleton.elim _ _)
  | n + 1, _, _, φ, t, x => by
    rw [resolutionEval_succ_apply]
    exact (resolutionEval_resolutionCurryAux n _ (t, x 0) (Fin.tail x)).trans (by simp)

/-- The element `(x₀ ↦ (x₁ ↦ ⋯ ↦ f (x₀, …, xₙ₋₁)))` of the `n`-th term of the coinduced resolution
obtained by currying a continuous function `f` on `Gⁿ`. -/
noncomputable def resolutionCurry (n : ℕ) (f : C(Fin n → G, X.V)) : (resolutionX X n).V :=
  resolutionCurryAux X n (f.comp ⟨Prod.snd, continuous_snd⟩ : C(PUnit × (Fin n → G), X.V))
    PUnit.unit

/-- Currying is a right inverse of evaluation: every continuous function on `Gⁿ` is the
evaluation of an element of the `n`-th term of the coinduced resolution. -/
@[simp]
theorem resolutionEval_resolutionCurry (n : ℕ) (f : C(Fin n → G, X.V)) :
    resolutionEval X n (resolutionCurry X n f) = f :=
  funext fun x ↦ resolutionEval_resolutionCurryAux X n _ PUnit.unit x

/-! ### Continuity of evaluations over a locally compact group -/

variable [LocallyCompactSpace G]

private theorem continuous_resolutionEval_aux :
    ∀ (n : ℕ) {T : Type (max v w)} [TopologicalSpace T] (Φ : T → (resolutionX X n).V),
      Continuous Φ → Continuous fun p : T × (Fin n → G) ↦ resolutionEval X n (Φ p.1) p.2
  | 0, _, _, Φ, hΦ => (hΦ.comp continuous_fst).congr fun p ↦ (resolutionEval_zero_apply X _ _).symm
  | n + 1, _, _, Φ, hΦ => by
    have hΨ : Continuous fun q : _ × G ↦ (Φ q.1 : C(G, (resolutionX X n).V)) q.2 :=
      (hΦ.comp continuous_fst).eval continuous_snd
    exact (continuous_resolutionEval_aux n _ hΨ).comp
      (f := fun p : _ × (Fin (n + 1) → G) ↦ ((p.1, p.2 0), Fin.tail p.2)) (by fun_prop)

/-- Over a locally compact group, the values of an element of the coinduced resolution at tuples
form a continuous function on `Gⁿ`. -/
theorem continuous_resolutionEval (n : ℕ) (F : (resolutionX X n).V) :
    Continuous (resolutionEval X n F) :=
  (continuous_resolutionEval_aux X n (fun _ : PUnit ↦ F) continuous_const).comp
    (f := fun x ↦ (PUnit.unit, x)) (by fun_prop)

end TopRep
