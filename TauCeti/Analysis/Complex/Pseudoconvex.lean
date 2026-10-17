/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.LeviForm

/-!
# Strict plurisubharmonicity, strong `q`-pseudoconvexity and the Morse index

Let `f` be a real function on a complex vector space `V` of complex dimension `n`. The function
is **strictly plurisubharmonic** at `x` if its Levi form `TauCeti.leviForm f x` is positive
definite, and **strongly `q`-pseudoconvex** at `x` if the Levi form has at least `n - q` positive
eigenvalues, that is, if it is positive definite on some complex subspace of dimension at least
`n - q`. With this convention, which counts positive directions at the point itself, strong
`0`-pseudoconvexity is strict plurisubharmonicity. In the Andreotti–Grauert convention, which
counts `n - q + 1` positive directions, it is strong `(q + 1)`-convexity.

The main result bounds the real Morse index: if `f` is strongly `q`-pseudoconvex at `x`, then the
negative index of inertia of the real Hessian of `f` at `x` is at most `n + q`; in particular a
strictly plurisubharmonic function has Morse index at most `n`. The linear-algebraic input is
`LinearMap.BilinForm.sigNeg_add_finrank_le_of_re_leviForm_pos`. Both conditions are preserved
by restriction along holomorphic immersions and by post-composition with increasing convex
functions of one real variable, and strict plurisubharmonicity is preserved by sums.

## Main definitions

* `TauCeti.IsStrictlyPlurisubharmonicAt f x`: the Levi form of `f` at `x` is positive definite.
* `TauCeti.IsStronglyPseudoconvexAt q f x`: the Levi form of `f` at `x` is positive definite on a
  complex subspace of codimension at most `q`.

## Main results

* `TauCeti.isStrictlyPlurisubharmonicAt_iff_hessianQuadraticForm`: strict plurisubharmonicity
  is positivity of `Hess f(v, v) + Hess f(I • v, I • v)`.
* `TauCeti.isStronglyPseudoconvexAt_zero_iff`: strong `0`-pseudoconvexity is strict
  plurisubharmonicity.
* `TauCeti.IsStronglyPseudoconvexAt.morseIndex_le`: the index bound `λ ≤ n + q`.
* `TauCeti.IsStrictlyPlurisubharmonicAt.morseIndex_le`: the index bound `λ ≤ n`.
* `TauCeti.IsStronglyPseudoconvexAt.comp`, `TauCeti.IsStrictlyPlurisubharmonicAt.comp`:
  restriction along a holomorphic map with injective derivative.
* `TauCeti.IsStronglyPseudoconvexAt.scalar_comp`,
  `TauCeti.IsStrictlyPlurisubharmonicAt.scalar_comp`: post-composition with a function `φ` with
  `φ' > 0` and `φ'' ≥ 0`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
* A. Andreotti and H. Grauert, *Théorèmes de finitude pour la cohomologie des espaces complexes*,
  Bull. Soc. Math. France 90 (1962).
-/

public section

open Complex Function Module Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {f g : V → ℝ} {x : V} {q r : ℕ}

/-- A real function `f` is **strictly plurisubharmonic** at `x` if its Levi form at `x` is
positive definite: `0 < Re (leviForm f x v v)` for every `v ≠ 0`. For `C²` functions the Levi
form is Hermitian, so its diagonal is real. -/
def IsStrictlyPlurisubharmonicAt (f : V → ℝ) (x : V) : Prop :=
  ∀ v : V, v ≠ 0 → 0 < (leviForm f x v v).re

/-- A real function `f` on a finite-dimensional complex space `V` is **strongly
`q`-pseudoconvex** at `x` if its Levi form at `x` has at least `dim_ℂ V - q` positive
eigenvalues: there is a complex subspace `P` with `dim_ℂ V ≤ dim_ℂ P + q` on which the Levi form
is positive definite. (By Sylvester's law of inertia for Hermitian forms, the largest dimension of
such a subspace is the number of positive eigenvalues.) For `q ≥ dim_ℂ V` the condition always
holds, and strong `0`-pseudoconvexity is strict plurisubharmonicity. -/
def IsStronglyPseudoconvexAt [FiniteDimensional ℂ V] (q : ℕ) (f : V → ℝ) (x : V) : Prop :=
  ∃ P : Submodule ℂ V,
    Fintype.card (Module.Free.ChooseBasisIndex ℂ V) ≤ finrank ℂ P + q ∧
    ∀ v ∈ P, v ≠ 0 → 0 < (leviForm f x v v).re

/-- The defining property of strict plurisubharmonicity. -/
theorem isStrictlyPlurisubharmonicAt_iff :
    IsStrictlyPlurisubharmonicAt f x ↔ ∀ v : V, v ≠ 0 → 0 < (leviForm f x v v).re :=
  Iff.rfl

/-- The defining property of strong `q`-pseudoconvexity. -/
theorem isStronglyPseudoconvexAt_iff [FiniteDimensional ℂ V] :
    IsStronglyPseudoconvexAt q f x ↔ ∃ P : Submodule ℂ V, finrank ℂ V ≤ finrank ℂ P + q ∧
      ∀ v ∈ P, v ≠ 0 → 0 < (leviForm f x v v).re := by
  rw [IsStronglyPseudoconvexAt, Module.finrank_eq_card_chooseBasisIndex]

/-- Strict plurisubharmonicity in terms of the real Hessian: `f` is strictly plurisubharmonic at
`x` exactly when `Hess f(v, v) + Hess f(I • v, I • v) > 0` for every `v ≠ 0`. -/
theorem isStrictlyPlurisubharmonicAt_iff_hessianQuadraticForm :
    IsStrictlyPlurisubharmonicAt f x ↔
      ∀ v : V, v ≠ 0 → 0 < hessianQuadraticForm f x v + hessianQuadraticForm f x (I • v) := by
  simp only [isStrictlyPlurisubharmonicAt_iff, re_leviForm_apply, hessianQuadraticForm_apply]
  exact forall₂_congr fun _ _ ↦ div_pos_iff_of_pos_right (by norm_num)

/-- Strong `q`-pseudoconvexity is weaker for larger `q`. -/
theorem IsStronglyPseudoconvexAt.mono [FiniteDimensional ℂ V]
    (h : IsStronglyPseudoconvexAt q f x) (hqr : q ≤ r) :
    IsStronglyPseudoconvexAt r f x := by
  rw [isStronglyPseudoconvexAt_iff] at h ⊢
  obtain ⟨P, hP, hpos⟩ := h
  exact ⟨P, by omega, hpos⟩

/-- A strictly plurisubharmonic function is strongly `q`-pseudoconvex for every `q`. -/
theorem IsStrictlyPlurisubharmonicAt.isStronglyPseudoconvexAt
    [FiniteDimensional ℂ V] (h : IsStrictlyPlurisubharmonicAt f x) (q : ℕ) :
    IsStronglyPseudoconvexAt q f x := by
  rw [isStronglyPseudoconvexAt_iff]
  exact ⟨⊤, by simp, fun v _ hv ↦ h v hv⟩

/-- Strong `0`-pseudoconvexity is strict plurisubharmonicity. -/
theorem isStronglyPseudoconvexAt_zero_iff [FiniteDimensional ℂ V] :
    IsStronglyPseudoconvexAt 0 f x ↔ IsStrictlyPlurisubharmonicAt f x := by
  constructor
  · rw [isStronglyPseudoconvexAt_iff]
    rintro ⟨P, hP, hpos⟩ v hv
    have hP : P = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm P.finrank_le hP)
    exact hpos v (hP ▸ Submodule.mem_top) hv
  · exact fun h ↦ h.isStronglyPseudoconvexAt 0

/-- Strict plurisubharmonicity at a point depends only on the germ of the function there. -/
theorem IsStrictlyPlurisubharmonicAt.congr_of_eventuallyEq
    (h : IsStrictlyPlurisubharmonicAt f x) (hfg : g =ᶠ[𝓝 x] f) :
    IsStrictlyPlurisubharmonicAt g x := by
  rw [IsStrictlyPlurisubharmonicAt, leviForm_congr_of_eventuallyEq hfg]
  exact h

/-- Strong `q`-pseudoconvexity at a point depends only on the germ of the function there. -/
theorem IsStronglyPseudoconvexAt.congr_of_eventuallyEq [FiniteDimensional ℂ V]
    (h : IsStronglyPseudoconvexAt q f x) (hfg : g =ᶠ[𝓝 x] f) :
    IsStronglyPseudoconvexAt q g x := by
  rw [isStronglyPseudoconvexAt_iff] at h ⊢
  rw [leviForm_congr_of_eventuallyEq hfg]
  exact h

/-- **The Morse index bound `λ ≤ n + q`.** If `f` is strongly `q`-pseudoconvex at `x`, then the
negative index of inertia of the real Hessian of `f` at `x` is at most `dim_ℂ V + q`. -/
theorem IsStronglyPseudoconvexAt.morseIndex_le [FiniteDimensional ℂ V]
    (h : IsStronglyPseudoconvexAt q f x) : morseIndex f x ≤ finrank ℂ V + q := by
  rw [isStronglyPseudoconvexAt_iff] at h
  obtain ⟨P, hP, hpos⟩ := h
  have hQ : hessianQuadraticForm f x = (fderiv ℝ (fderiv ℝ f) x).toBilinForm.toQuadraticMap :=
    QuadraticMap.ext fun v ↦ by simp
  have h₁ := (fderiv ℝ (fderiv ℝ f) x).toBilinForm.sigNeg_add_finrank_le_of_re_leviForm_pos
    (P := P) (by simpa only [leviForm_def] using hpos)
  have h₂ : finrank ℝ V = 2 * finrank ℂ V := finrank_real_eq_two_mul_finrank_complex
  rw [morseIndex_def, hQ]
  omega

/-- **The Morse index bound `λ ≤ n`.** The real Hessian of a strictly plurisubharmonic function
has negative index of inertia at most the complex dimension. -/
theorem IsStrictlyPlurisubharmonicAt.morseIndex_le [FiniteDimensional ℂ V]
    (h : IsStrictlyPlurisubharmonicAt f x) : morseIndex f x ≤ finrank ℂ V := by
  simpa using (h.isStronglyPseudoconvexAt 0).morseIndex_le

/-- **Restriction along a holomorphic immersion.** If `f` is strictly plurisubharmonic at `g b`
and the complex derivative of the holomorphic map `g` at `b` is injective, then `f ∘ g` is
strictly plurisubharmonic at `b`. -/
theorem IsStrictlyPlurisubharmonicAt.comp {f : V → ℝ} {g : W → V} {b : W}
    (h : IsStrictlyPlurisubharmonicAt f (g b)) (hf : ContDiffAt ℝ 2 f (g b))
    (hg : ContDiffAt ℂ 2 g b) (hg' : Injective (fderiv ℂ g b)) :
    IsStrictlyPlurisubharmonicAt (f ∘ g) b := fun v hv ↦ by
  rw [leviForm_comp_apply hf hg]
  exact h _ ((map_ne_zero_iff _ hg').2 hv)

/-- **Restriction along a holomorphic immersion.** If `f` is strongly `q`-pseudoconvex at `g b`
and the complex derivative of the holomorphic map `g` at `b` is injective, then `f ∘ g` is
strongly `q`-pseudoconvex at `b`: the preimage of a positive subspace of codimension at most `q`
is a positive subspace of codimension at most `q`. -/
theorem IsStronglyPseudoconvexAt.comp [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    {f : V → ℝ} {g : W → V} {b : W}
    (h : IsStronglyPseudoconvexAt q f (g b)) (hf : ContDiffAt ℝ 2 f (g b))
    (hg : ContDiffAt ℂ 2 g b) (hg' : Injective (fderiv ℂ g b)) :
    IsStronglyPseudoconvexAt q (f ∘ g) b := by
  rw [isStronglyPseudoconvexAt_iff] at h ⊢
  obtain ⟨P, hP, hpos⟩ := h
  refine ⟨P.comap (fderiv ℂ g b : W →ₗ[ℂ] V), ?_, fun v hv hv0 ↦ ?_⟩
  · have := Submodule.finrank_add_finrank_le_finrank_comap_add_finrank
      (fderiv ℂ g b : W →ₗ[ℂ] V) P
    omega
  · rw [leviForm_comp_apply hf hg]
    exact hpos _ hv ((map_ne_zero_iff _ hg').2 hv0)

/-- Post-composition with a function `φ` of one real variable with `φ'(f x) > 0` and
`φ''(f x) ≥ 0` preserves strict plurisubharmonicity at `x`. -/
theorem IsStrictlyPlurisubharmonicAt.scalar_comp {φ : ℝ → ℝ}
    (h : IsStrictlyPlurisubharmonicAt f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContDiffAt ℝ 2 f x) (hφ₁ : 0 < deriv φ (f x)) (hφ₂ : 0 ≤ iteratedDeriv 2 φ (f x)) :
    IsStrictlyPlurisubharmonicAt (φ ∘ f) x := fun v hv ↦
  (mul_pos hφ₁ (h v hv)).trans_le (le_re_leviForm_scalar_comp_apply_self hφ hf hφ₂ v)

/-- Post-composition with a function `φ` of one real variable with `φ'(f x) > 0` and
`φ''(f x) ≥ 0` preserves strong `q`-pseudoconvexity at `x`. -/
theorem IsStronglyPseudoconvexAt.scalar_comp [FiniteDimensional ℂ V] {φ : ℝ → ℝ}
    (h : IsStronglyPseudoconvexAt q f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContDiffAt ℝ 2 f x) (hφ₁ : 0 < deriv φ (f x)) (hφ₂ : 0 ≤ iteratedDeriv 2 φ (f x)) :
    IsStronglyPseudoconvexAt q (φ ∘ f) x := by
  rw [isStronglyPseudoconvexAt_iff] at h ⊢
  obtain ⟨P, hP, hpos⟩ := h
  exact ⟨P, hP, fun v hv hv0 ↦ (mul_pos hφ₁ (hpos v hv hv0)).trans_le
    (le_re_leviForm_scalar_comp_apply_self hφ hf hφ₂ v)⟩

/-- The sum of two `C²` functions strictly plurisubharmonic at `x` is strictly plurisubharmonic
at `x`. -/
theorem IsStrictlyPlurisubharmonicAt.add (hf : IsStrictlyPlurisubharmonicAt f x)
    (hg : IsStrictlyPlurisubharmonicAt g x) (hf' : ContDiffAt ℝ 2 f x)
    (hg' : ContDiffAt ℝ 2 g x) : IsStrictlyPlurisubharmonicAt (f + g) x := fun v hv ↦ by
  rw [leviForm_add hf' hg']
  simpa using add_pos (hf v hv) (hg v hv)

end TauCeti
