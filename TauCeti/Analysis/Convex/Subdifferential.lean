/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Conjugate

/-!
# The subdifferential and conjugate-subgradient reciprocity

Let `E` and `F` be real vector spaces paired by `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, written
`⟪x, y⟫ = B x y`, and let `f : E → EReal`. A point `y : F` is a *subgradient* of `f` at `x` when
`f x` is finite and the affine function `x' ↦ f x + ⟪x' - x, y⟫` lies below `f` everywhere; the
set of subgradients is the *subdifferential* `∂f(x)`. It is empty wherever `f` is infinite.

The subdifferential is characterised by equality in the Fenchel–Young inequality: `y ∈ ∂f(x)`
exactly when `f x + f⋆ y = ⟪x, y⟫`, where `f⋆` is the Legendre–Fenchel conjugate of
`TauCeti.Analysis.Convex.Conjugate`. Equivalently, `x` maximises `x' ↦ ⟪x', y⟫ - f x'`. Since the
equality is symmetric in `(f, x)` and `(f⋆, y)` up to the biconjugate, it gives the
*conjugate-subgradient reciprocity*: `y ∈ ∂f(x)` implies `x ∈ ∂f⋆(y)` (for the transposed
pairing), and the converse holds at every point where `f⋆⋆ x = f x`, which is in particular the
case whenever `∂f(x)` is nonempty. Almost nothing here needs `f` convex: the subdifferential of
an arbitrary extended-real function is defined by the same inequality, it is a closed convex
subset of `F` for any topology in which the functionals `B x` are continuous, and it is monotone.
Convexity of `f` enters only to make the set of points at which a fixed `y` is a subgradient
convex.

## Main definitions

* `TauCeti.subdifferential B f x` — the set of `y : F` with `f x` finite and
  `f x + B (x' - x) y ≤ f x'` for every `x'`.
* `TauCeti.subgradientImage B f s` — the subgradient image `⋃ x ∈ s, ∂f(x)` of a set `s`.

## Main statements

* `TauCeti.mem_subdifferential_iff_forall_sub_le` — a subgradient at `x` is a `y` for which `x`
  maximises `x' ↦ B x' y - f x'`, and `TauCeti.mem_subdifferential_iff_add_fenchelConjugate_eq` —
  **the Fenchel–Young equality characterisation** `y ∈ ∂f(x) ↔ f x + f⋆ y = B x y`;
* `TauCeti.mem_subdifferential_coe_iff` — for a real-valued `f` the finiteness condition is
  automatic and membership is the subgradient inequality, and
  `TauCeti.mem_subdifferential_iff_forall_toReal_add_le` is the same statement between real
  representatives for an `f` that is never `⊥`;
* `TauCeti.apply_le_apply_of_mem_subdifferential` — the subdifferential is monotone;
* `TauCeti.convex_subdifferential` and `TauCeti.isClosed_subdifferential` — the subdifferential
  is convex, and closed for a topology making every `B x` continuous;
* `TauCeti.convex_setOf_mem_subdifferential` — for a convex `f`, the points at which a fixed `y`
  is a subgradient form a convex set;
* `TauCeti.mem_subdifferential_fenchelConjugate_of_mem_subdifferential` — **conjugate-subgradient
  reciprocity**: `y ∈ ∂f(x)` implies `x ∈ ∂f⋆(y)`;
* `TauCeti.fenchelConjugate_flip_fenchelConjugate_eq_of_mem_subdifferential` — `f⋆⋆ x = f x`
  wherever `f` has a subgradient;
* `TauCeti.mem_subdifferential_fenchelConjugate_iff` — where `f⋆⋆ x = f x`, the two subgradient
  relations are equivalent.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §23, in
  particular Theorem 23.5 and Corollary 23.5.1.
* I. Ekeland and R. Témam, *Convex Analysis and Variational Problems*, Classics in Applied
  Mathematics 28, SIAM 1999, Chapter I, §5.
-/

public section

noncomputable section

namespace TauCeti

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- The subdifferential of `f : E → EReal` at `x` with respect to the pairing `B`: the set of
`y : F` such that `f x` is finite and `f x + B (x' - x) y ≤ f x'` for every `x'`. It is empty
wherever `f` takes an infinite value. -/
def subdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set F :=
  {y | f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ x', f x + (B (x' - x) y : EReal) ≤ f x'}

variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f : E → EReal} {x : E} {y : F} {r : ℝ}

/-- The defining condition for a subgradient. -/
@[simp]
theorem mem_subdifferential_iff :
    y ∈ subdifferential B f x ↔
      f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ x', f x + (B (x' - x) y : EReal) ≤ f x' :=
  Iff.rfl

/-- A function has a subgradient at `x` only if it does not take the value `⊥` there. -/
theorem ne_bot_of_mem_subdifferential (h : y ∈ subdifferential B f x) : f x ≠ ⊥ :=
  h.1

/-- A function has a subgradient at `x` only if it does not take the value `⊤` there. -/
theorem ne_top_of_mem_subdifferential (h : y ∈ subdifferential B f x) : f x ≠ ⊤ :=
  h.2.1

/-- The subgradient inequality. -/
theorem add_le_of_mem_subdifferential (h : y ∈ subdifferential B f x) (x' : E) :
    f x + (B (x' - x) y : EReal) ≤ f x' :=
  h.2.2 x'

/-- A function with a subgradient somewhere never takes the value `⊥`: the affine minorant
through the subgradient is real everywhere. -/
theorem apply_ne_bot_of_mem_subdifferential (h : y ∈ subdifferential B f x) (x' : E) :
    f x' ≠ ⊥ := by
  intro hx'
  have h' := add_le_of_mem_subdifferential B h x'
  rw [hx', le_bot_iff, EReal.add_eq_bot_iff] at h'
  exact h'.elim (ne_bot_of_mem_subdifferential B h) (EReal.coe_ne_bot _)

/-- The subdifferential is empty where the function takes the value `⊥`. -/
theorem subdifferential_eq_empty_of_eq_bot (h : f x = ⊥) : subdifferential B f x = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hy => ne_bot_of_mem_subdifferential B hy h

/-- The subdifferential is empty where the function takes the value `⊤`. -/
theorem subdifferential_eq_empty_of_eq_top (h : f x = ⊤) : subdifferential B f x = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hy => ne_top_of_mem_subdifferential B hy h

/-- For a real-valued function, a subgradient is a `y` satisfying the subgradient inequality. -/
-- Not `@[simp]`: `mem_subdifferential_iff` already rewrites the left-hand side, so this lemma
-- fails the `simpNF` linter.
theorem mem_subdifferential_coe_iff (f : E → ℝ) :
    y ∈ subdifferential B (fun x => (f x : EReal)) x ↔ ∀ x', f x + B (x' - x) y ≤ f x' := by
  simp only [mem_subdifferential_iff, ne_eq, EReal.coe_ne_bot, EReal.coe_ne_top,
    not_false_eq_true, true_and, ← EReal.coe_add, EReal.coe_le_coe_iff]

/-- If `f` never takes the value `⊥` and is finite at `x`, then `y` is a subgradient at `x` exactly
when the subgradient inequality holds between real representatives at every point of the
effective domain. -/
theorem mem_subdifferential_iff_forall_toReal_add_le (hbot : ∀ x', f x' ≠ ⊥) (hx : f x ≠ ⊤) :
    y ∈ subdifferential B f x ↔
      ∀ x', f x' ≠ ⊤ → (f x).toReal + B (x' - x) y ≤ (f x').toReal := by
  have key : ∀ x', f x' ≠ ⊤ →
      (f x + B (x' - x) y ≤ f x' ↔ (f x).toReal + B (x' - x) y ≤ (f x').toReal) := fun x' hx' => by
    conv_lhs => rw [← EReal.coe_toReal hx (hbot x), ← EReal.coe_toReal hx' (hbot x')]
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  rw [mem_subdifferential_iff]
  refine ⟨fun h x' hx' => (key x' hx').1 (h.2.2 x'), fun h => ⟨hbot x, hx, fun x' => ?_⟩⟩
  rcases eq_or_ne (f x') ⊤ with hx' | hx'
  · rw [hx']
    exact le_top
  exact (key x' hx').2 (h x' hx')

/-- **Subgradients are monotone.** If `y₁ ∈ ∂f(x₁)` and `y₂ ∈ ∂f(x₂)`, then
`B (x₂ - x₁) y₁ ≤ B (x₂ - x₁) y₂`; for the inner product this is the monotonicity
`⟪x₂ - x₁, y₂ - y₁⟫ ≥ 0` of the subdifferential. -/
theorem apply_le_apply_of_mem_subdifferential {x₁ x₂ : E} {y₁ y₂ : F}
    (h₁ : y₁ ∈ subdifferential B f x₁) (h₂ : y₂ ∈ subdifferential B f x₂) :
    B (x₂ - x₁) y₁ ≤ B (x₂ - x₁) y₂ := by
  have hbot := apply_ne_bot_of_mem_subdifferential B h₁
  have e₁ := (mem_subdifferential_iff_forall_toReal_add_le B hbot
    (ne_top_of_mem_subdifferential B h₁)).1 h₁ x₂ (ne_top_of_mem_subdifferential B h₂)
  have e₂ := (mem_subdifferential_iff_forall_toReal_add_le B hbot
    (ne_top_of_mem_subdifferential B h₂)).1 h₂ x₁ (ne_top_of_mem_subdifferential B h₁)
  rw [← neg_sub x₂ x₁, map_neg, LinearMap.neg_apply] at e₂
  linarith

/-! ### Subgradient images -/

/-- The *subgradient image* `∂f(s) = ⋃ x ∈ s, ∂f(x)` of a set `s` with respect to the pairing
`B`: the set of all subgradients of `f` at points of `s`. -/
def subgradientImage (f : E → EReal) (s : Set E) : Set F :=
  ⋃ x ∈ s, subdifferential B f x

/-- A point of the subgradient image is a subgradient at some point of the set. -/
@[simp]
theorem mem_subgradientImage_iff {s : Set E} :
    y ∈ subgradientImage B f s ↔ ∃ x ∈ s, y ∈ subdifferential B f x := by
  simp only [subgradientImage, Set.mem_iUnion, exists_prop]

/-- The subgradient image is monotone in the set. -/
@[gcongr]
theorem subgradientImage_mono {s t : Set E} (h : s ⊆ t) :
    subgradientImage B f s ⊆ subgradientImage B f t :=
  Set.biUnion_subset_biUnion_left h

/-- The subgradient image of the empty set is empty. -/
@[simp]
theorem subgradientImage_empty : subgradientImage B f ∅ = ∅ :=
  Set.biUnion_empty _

/-- The subgradient image of a singleton is the subdifferential at that point. -/
@[simp]
theorem subgradientImage_singleton (x : E) : subgradientImage B f {x} = subdifferential B f x :=
  Set.biUnion_singleton _ _

/-- The subgradient image of a union is the union of the subgradient images. -/
@[simp]
theorem subgradientImage_union (s t : Set E) :
    subgradientImage B f (s ∪ t) = subgradientImage B f s ∪ subgradientImage B f t :=
  Set.biUnion_union s t _

/-- The subgradient image of an indexed union is the union of the subgradient images. -/
@[simp]
theorem subgradientImage_iUnion {ι : Sort*} (s : ι → Set E) :
    subgradientImage B f (⋃ i, s i) = ⋃ i, subgradientImage B f (s i) :=
  Set.biUnion_iUnion s _

/-! ### Subgradients and the conjugate -/

/-- When `f x = r` is real, `y` is a subgradient at `x` exactly when `x` maximises
`x' ↦ B x' y - f x'`, whose value at `x` is `B x y - r`. -/
theorem mem_subdifferential_iff_forall_sub_le (hr : f x = r) :
    y ∈ subdifferential B f x ↔
      ∀ x', (B x' y : EReal) - f x' ≤ ((B x y - r : ℝ) : EReal) := by
  rw [mem_subdifferential_iff, hr]
  simp only [ne_eq, EReal.coe_ne_bot, EReal.coe_ne_top, not_false_eq_true, true_and]
  refine forall_congr' fun x' => ?_
  rw [EReal.coe_sub_le_comm, ← EReal.coe_add, ← EReal.coe_sub, map_sub, LinearMap.sub_apply]
  have h : r + (B x' y - B x y) = B x' y - (B x y - r) := by ring
  rw [h]

/-- At a subgradient, the conjugate is given by the Fenchel–Young equality
`f⋆ y = B x y - f x`. -/
theorem fenchelConjugate_eq_of_mem_subdifferential (h : y ∈ subdifferential B f x) :
    fenchelConjugate B f y = (B x y : EReal) - f x := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
    ⟨(f x).toReal, (EReal.coe_toReal (ne_top_of_mem_subdifferential B h)
      (ne_bot_of_mem_subdifferential B h)).symm⟩
  refine le_antisymm (fenchelConjugate_le B fun x' => ?_) (sub_le_fenchelConjugate B f x y)
  rw [hr, ← EReal.coe_sub]
  exact (mem_subdifferential_iff_forall_sub_le B hr).1 h x'

/-- **The Fenchel–Young equality characterisation of subgradients**: `y ∈ ∂f(x)` exactly when
`f x + f⋆ y = B x y`. The equality forces both `f x` and `f⋆ y` to be finite. -/
theorem mem_subdifferential_iff_add_fenchelConjugate_eq :
    y ∈ subdifferential B f x ↔ f x + fenchelConjugate B f y = (B x y : EReal) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
      ⟨(f x).toReal, (EReal.coe_toReal (ne_top_of_mem_subdifferential B h)
        (ne_bot_of_mem_subdifferential B h)).symm⟩
    rw [fenchelConjugate_eq_of_mem_subdifferential B h, hr, ← EReal.coe_sub, ← EReal.coe_add,
      add_sub_cancel]
  · intro h
    have hbot : f x ≠ ⊥ := fun hx => by
      rw [hx, EReal.bot_add] at h
      exact EReal.coe_ne_bot _ h.symm
    have htop : f x ≠ ⊤ := fun hx => by
      rw [hx] at h
      rcases eq_or_ne (fenchelConjugate B f y) ⊥ with hy | hy
      · rw [hy, EReal.add_bot] at h
        exact EReal.coe_ne_bot _ h.symm
      · rw [EReal.top_add_of_ne_bot hy] at h
        exact EReal.coe_ne_top _ h.symm
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
    have hF : fenchelConjugate B f y = ((B x y - r : ℝ) : EReal) := by
      rw [hr] at h
      rw [EReal.coe_sub, ← h, EReal.add_sub_cancel_left]
    exact (mem_subdifferential_iff_forall_sub_le B hr).2 fun x' =>
      hF ▸ sub_le_fenchelConjugate B f x' y

/-! ### Convexity and closedness -/

/-- Where `f x = r` is real, the subdifferential is the intersection over `x'` of the affine
constraints `r + B (x' - x) y ≤ f x'`. -/
theorem subdifferential_eq_iInter (hr : f x = r) :
    subdifferential B f x = ⋂ x', {y | ((r + B (x' - x) y : ℝ) : EReal) ≤ f x'} := by
  ext y
  simp only [mem_subdifferential_iff, hr, ne_eq, EReal.coe_ne_bot, EReal.coe_ne_top,
    not_false_eq_true, true_and, Set.mem_iInter, Set.mem_ofPred_eq, EReal.coe_add]

/-- The subdifferential is a convex set: it is an intersection of half-spaces, or empty. -/
theorem convex_subdifferential (f : E → EReal) (x : E) : Convex ℝ (subdifferential B f x) := by
  rcases eq_or_ne (f x) ⊥ with hbot | hbot
  · rw [subdifferential_eq_empty_of_eq_bot B hbot]
    exact convex_empty
  rcases eq_or_ne (f x) ⊤ with htop | htop
  · rw [subdifferential_eq_empty_of_eq_top B htop]
    exact convex_empty
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [subdifferential_eq_iInter B hr]
  refine convex_iInter fun x' => ?_
  generalize f x' = z
  induction z with
  | bot =>
    simp only [le_bot_iff, EReal.coe_ne_bot, Set.ofPred_false]
    exact convex_empty
  | coe s =>
    simp only [EReal.coe_le_coe_iff, ← le_sub_iff_add_le']
    exact convex_halfSpace_le (B (x' - x)).isLinear (s - r)
  | top =>
    simp only [le_top, Set.ofPred_true]
    exact convex_univ

/-- For a convex `f`, the set of points at which `y` is a subgradient is convex: it is the set
of minimisers of the convex function `x ↦ f x - B x y`. -/
theorem convex_setOf_mem_subdifferential (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (y : F) :
    Convex ℝ {x | y ∈ subdifferential B f x} := by
  intro x₁ h₁ x₂ h₂ a b ha hb hab
  simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
  have hbot := apply_ne_bot_of_mem_subdifferential B h₁
  have ht₁ := ne_top_of_mem_subdifferential B h₁
  have ht₂ := ne_top_of_mem_subdifferential B h₂
  -- By convexity, `f` lies below the chord at the convex combination.
  have hz : f (a • x₁ + b • x₂) ≤ ((a * (f x₁).toReal + b * (f x₂).toReal : ℝ) : EReal) := by
    simpa using hf (x := (x₁, (f x₁).toReal)) (y := (x₂, (f x₂).toReal))
      (by simp [EReal.coe_toReal ht₁ (hbot x₁)]) (by simp [EReal.coe_toReal ht₂ (hbot x₂)])
      ha hb hab
  have hzt : f (a • x₁ + b • x₂) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hz
  have hzr := EReal.toReal_le_toReal hz (hbot _) (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at hzr
  -- The subgradient inequality at the combination is the combination of those at `x₁`, `x₂`.
  refine (mem_subdifferential_iff_forall_toReal_add_le B hbot hzt).2 fun x' hx' => ?_
  have e₁ := (mem_subdifferential_iff_forall_toReal_add_le B hbot ht₁).1 h₁ x' hx'
  have e₂ := (mem_subdifferential_iff_forall_toReal_add_le B hbot ht₂).1 h₂ x' hx'
  have hlin : B (x' - (a • x₁ + b • x₂)) y = a * B (x' - x₁) y + b * B (x' - x₂) y := by
    have : x' - (a • x₁ + b • x₂) = a • (x' - x₁) + b • (x' - x₂) := by
      conv_lhs => rw [← one_smul ℝ x', ← hab, add_smul]
      simp only [smul_sub]
      abel
    simp [this]
  have hsplit : (f x').toReal = a * (f x').toReal + b * (f x').toReal := by
    rw [← add_mul, hab, one_mul]
  rw [hlin]
  nlinarith [mul_le_mul_of_nonneg_left e₁ ha, mul_le_mul_of_nonneg_left e₂ hb]

/-- The subdifferential is closed for every topology on `F` in which each functional `B x` is
continuous: it is an intersection of closed half-spaces, or empty. -/
theorem isClosed_subdifferential [TopologicalSpace F] (hB : ∀ x, Continuous (B x))
    (f : E → EReal) (x : E) : IsClosed (subdifferential B f x) := by
  rcases eq_or_ne (f x) ⊥ with hbot | hbot
  · rw [subdifferential_eq_empty_of_eq_bot B hbot]
    exact isClosed_empty
  rcases eq_or_ne (f x) ⊤ with htop | htop
  · rw [subdifferential_eq_empty_of_eq_top B htop]
    exact isClosed_empty
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [subdifferential_eq_iInter B hr]
  exact isClosed_iInter fun x' =>
    isClosed_le (continuous_coe_real_ereal.comp (continuous_const.add (hB _))) continuous_const

end

/-! ### Conjugate-subgradient reciprocity -/

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f : E → EReal} {x : E} {y : F}

/-- **Conjugate-subgradient reciprocity.** If `y` is a subgradient of `f` at `x`, then `x` is a
subgradient of the conjugate `f⋆` at `y`, for the transposed pairing. -/
theorem mem_subdifferential_fenchelConjugate_of_mem_subdifferential
    (h : y ∈ subdifferential B f x) :
    x ∈ subdifferential B.flip (fenchelConjugate B f) y := by
  have hbot := ne_bot_of_mem_subdifferential B h
  have htop := ne_top_of_mem_subdifferential B h
  have hF : fenchelConjugate B f y = (B x y : EReal) - f x :=
    fenchelConjugate_eq_of_mem_subdifferential B h
  have hy : fenchelConjugate B f y ≠ ⊥ := fenchelConjugate_ne_bot B htop y
  have hy' : fenchelConjugate B f y ≠ ⊤ := by
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
    rw [hF, hr, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  rw [mem_subdifferential_iff_add_fenchelConjugate_eq, LinearMap.flip_apply]
  -- Fenchel–Young for `f⋆` gives `≥`; the biconjugate inequality `f⋆⋆ ≤ f` gives `≤`.
  refine le_antisymm ?_ (le_add_fenchelConjugate B.flip hy
    (fenchelConjugate_ne_bot B.flip hy' x))
  calc fenchelConjugate B f y + fenchelConjugate B.flip (fenchelConjugate B f) x
      ≤ fenchelConjugate B f y + f x :=
        add_le_add le_rfl (fenchelConjugate_flip_fenchelConjugate_le B f x)
    _ = (B x y : EReal) := by
        rw [add_comm, ← mem_subdifferential_iff_add_fenchelConjugate_eq]
        exact h

/-- Wherever `f` has a subgradient, `f` agrees with its biconjugate. -/
theorem fenchelConjugate_flip_fenchelConjugate_eq_of_mem_subdifferential
    (h : y ∈ subdifferential B f x) :
    fenchelConjugate B.flip (fenchelConjugate B f) x = f x := by
  have hx := mem_subdifferential_fenchelConjugate_of_mem_subdifferential B h
  have h₁ := (mem_subdifferential_iff_add_fenchelConjugate_eq B).1 h
  have h₂ := (mem_subdifferential_iff_add_fenchelConjugate_eq B.flip).1 hx
  rw [LinearMap.flip_apply, ← h₁, add_comm (f x)] at h₂
  obtain ⟨t, ht⟩ : ∃ t : ℝ, fenchelConjugate B f y = t :=
    ⟨(fenchelConjugate B f y).toReal, (EReal.coe_toReal (ne_top_of_mem_subdifferential B.flip hx)
      (ne_bot_of_mem_subdifferential B.flip hx)).symm⟩
  rw [ht] at h₂
  calc fenchelConjugate B.flip (fenchelConjugate B f) x
      = (t : EReal) + fenchelConjugate B.flip (fenchelConjugate B f) x - t :=
        EReal.add_sub_cancel_left.symm
    _ = (t : EReal) + f x - t := by rw [h₂]
    _ = f x := EReal.add_sub_cancel_left

/-- **Conjugate-subgradient reciprocity**, both ways: at a point where `f` agrees with its
biconjugate, `x` is a subgradient of `f⋆` at `y` exactly when `y` is a subgradient of `f` at
`x`. -/
theorem mem_subdifferential_fenchelConjugate_iff
    (hx : fenchelConjugate B.flip (fenchelConjugate B f) x = f x) :
    x ∈ subdifferential B.flip (fenchelConjugate B f) y ↔ y ∈ subdifferential B f x := by
  rw [mem_subdifferential_iff_add_fenchelConjugate_eq,
    mem_subdifferential_iff_add_fenchelConjugate_eq, hx, LinearMap.flip_apply, add_comm]

end

end TauCeti

end

end
