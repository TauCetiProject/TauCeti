/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Complex.LeviForm

/-!
# Strict plurisubharmonicity, strong `q`-pseudoconvexity and the Morse index

Let `f` be a real function on a complex vector space `V` of complex dimension `n`. The function
is **strictly plurisubharmonic** at `x` if its Levi form `TauCeti.leviForm f x` is positive
definite, and **strongly `q`-pseudoconvex** at `x` if the Levi form is positive definite on some
complex subspace of dimension at least `n - q`; here positivity means that the real part of the
Levi diagonal is positive. When `f` is `C²` the Levi form is Hermitian (`TauCeti.isSymm_leviForm`),
and this says that it has at least `n - q` positive eigenvalues. With this convention, which counts
positive directions at the point itself, strong `0`-pseudoconvexity is strict plurisubharmonicity.
In the Andreotti–Grauert convention, which counts `n - q + 1` positive directions, it is strong
`(q + 1)`-convexity.

The main result bounds the real Morse index: if `f` is strongly `q`-pseudoconvex at `x`, then the
negative index of inertia of the real Hessian of `f` at `x` is at most `n + q`; in particular a
strictly plurisubharmonic function has Morse index at most `n`. The linear-algebraic input is
`LinearMap.BilinForm.sigNeg_add_finrank_le_of_re_leviForm_pos`. Both conditions are preserved
by restriction along holomorphic immersions and by post-composition with increasing convex
functions of one real variable, and strict plurisubharmonicity is preserved by sums.

Strong `q`-pseudoconvexity is stable under `C²` perturbations. For a fixed positive complex
subspace this follows by testing the Levi diagonal on its compact real unit sphere. Consequently
the bilinear forms with at least `dim_ℂ V - q` positive directions form an open set. If the
second derivative of `f` varies continuously on a set `U`, its distance from the complement of
this open set gives a continuous positive tolerance on `U` within which every perturbation remains
strongly `q`-pseudoconvex.

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
* `TauCeti.isOpen_setOf_re_leviForm_posOnSubspace`: having an admissible Levi-positive complex
  subspace is open on continuous bilinear forms.
* `TauCeti.exists_continuousOn_pos_forall_isStronglyPseudoconvexAt`: strong
  `q`-pseudoconvexity is open in the fine `C²` topology, with a varying positive tolerance.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
* A. Andreotti and H. Grauert, *Théorèmes de finitude pour la cohomologie des espaces complexes*,
  Bull. Soc. Math. France 90 (1962).
-/

public section

open Complex Function Metric Module Set Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {f g : V → ℝ} {x : V} {q r : ℕ}

/-- A real function `f` is **strictly plurisubharmonic** at `x` if its Levi form at `x` is
positive definite: `0 < Re (leviForm f x v v)` for every `v ≠ 0`. For `C²` functions the Levi
form is Hermitian, so its diagonal is real. -/
def IsStrictlyPlurisubharmonicAt (f : V → ℝ) (x : V) : Prop :=
  ∀ v : V, v ≠ 0 → 0 < (leviForm f x v v).re

/-- A real function `f` on a finite-dimensional complex space `V` is **strongly
`q`-pseudoconvex** at `x` if there is a complex subspace `P` with `dim_ℂ V ≤ dim_ℂ P + q` on which
the Levi form at `x` is positive definite: `0 < Re (leviForm f x v v)` for every nonzero `v ∈ P`.
When `f` is `C²` the Levi form is Hermitian, and by Sylvester's law of inertia for Hermitian forms
the largest dimension of such a subspace is the number of positive eigenvalues, so the condition
says that the Levi form has at least `dim_ℂ V - q` positive eigenvalues. For `q ≥ dim_ℂ V` the
condition always holds, and strong `0`-pseudoconvexity is strict plurisubharmonicity. -/
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
@[simp]
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

/-! ### Perturbation openness -/

/-- **Strong `q`-pseudoconvexity is open on bilinear forms.** On a finite-dimensional complex
space, the continuous real bilinear forms whose Levi form is positive definite on some complex
subspace of codimension at most `q` form an open set.

The statement uses the additive dimension inequality from `IsStronglyPseudoconvexAt`, which also
covers `q ≥ dim_ℂ V` without truncated subtraction. -/
theorem isOpen_setOf_re_leviForm_posOnSubspace [FiniteDimensional ℂ V] (q : ℕ) :
    IsOpen {B : V →L[ℝ] V →L[ℝ] ℝ |
      ∃ P : Submodule ℂ V, finrank ℂ V ≤ finrank ℂ P + q ∧
        ∀ v ∈ P, v ≠ 0 → 0 < (B.toBilinForm.leviForm v v).re} := by
  rw [isOpen_iff_mem_nhds]
  intro B hB
  obtain ⟨P, hP, hpos⟩ := hB
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  have : FiniteDimensional ℝ P := Module.Finite.trans ℂ P
  -- Positivity persists uniformly on the compact unit sphere of the chosen positive subspace.
  have key : ∀ᶠ C in nhds B, ∀ v ∈ sphere (0 : P) 1,
      0 < (C.toBilinForm.leviForm (v : V) v).re := by
    refine (isCompact_sphere (0 : P) 1).eventually_forall_of_forall_eventually
      fun v hv ↦ ?_
    have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
    have hv0 : (v : V) ≠ 0 := by
      exact Subtype.coe_ne_coe.mpr (norm_ne_zero_iff.mp (hvnorm ▸ one_ne_zero))
    have hcont : Continuous fun z : (V →L[ℝ] V →L[ℝ] ℝ) × P ↦
        (z.1.toBilinForm.leviForm (z.2 : V) z.2).re := by
      simp only [LinearMap.BilinForm.re_leviForm_apply]
      have hv : Continuous fun z : (V →L[ℝ] V →L[ℝ] ℝ) × P ↦ (z.2 : V) :=
        continuous_subtype_val.comp continuous_snd
      have hvI : Continuous fun z : (V →L[ℝ] V →L[ℝ] ℝ) × P ↦ I • (z.2 : V) :=
        continuous_const_smul I |>.comp hv
      exact ((continuous_fst.clm_apply hv).clm_apply hv).add
        ((continuous_fst.clm_apply hvI).clm_apply hvI) |>.div_const 4
    exact (isOpen_lt continuous_const hcont).mem_nhds (hpos v v.2 hv0)
  filter_upwards [key] with C hC
  refine ⟨P, hP, fun v hv hv0 ↦ ?_⟩
  let u : P := ⟨v, hv⟩
  have hu0 : u ≠ 0 := Subtype.coe_ne_coe.mp hv0
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  let c : ℝ := ‖u‖⁻¹
  have hmem : c • u ∈ sphere (0 : P) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ hnorm]
  have hc := hC (c • u) hmem
  rw [LinearMap.BilinForm.re_leviForm_apply] at hc ⊢
  simp only [c, u, Submodule.coe_smul_of_tower, smul_comm I, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at hc
  have hfactor :
      (‖(⟨v, hv⟩ : P)‖⁻¹ * (‖(⟨v, hv⟩ : P)‖⁻¹ * (C.toBilinForm v v)) +
          ‖(⟨v, hv⟩ : P)‖⁻¹ * (‖(⟨v, hv⟩ : P)‖⁻¹ *
            (C.toBilinForm (I • v) (I • v)))) / 4 =
        ‖(⟨v, hv⟩ : P)‖⁻¹ ^ 2 *
          ((C.toBilinForm v v + C.toBilinForm (I • v) (I • v)) / 4) := by ring
  rw [hfactor] at hc
  exact pos_of_mul_pos_right hc (sq_nonneg ‖(⟨v, hv⟩ : P)‖⁻¹)

/-- **Strong `q`-pseudoconvexity is open in the fine `C²` topology.** Let the second derivative
of `f` vary continuously on `U`, and suppose `f` is strongly `q`-pseudoconvex at every point of
`U`. Then there is a tolerance `ε`, continuous and positive on `U`, such that every function whose
second derivative differs from that of `f` by less than `ε x` remains strongly
`q`-pseudoconvex at `x`.

No regularity of the perturbing function is required beyond the displayed pointwise control of its
totalized second derivative. -/
theorem exists_continuousOn_pos_forall_isStronglyPseudoconvexAt
    [FiniteDimensional ℂ V] {U : Set V} {f : V → ℝ} (q : ℕ)
    (hf : ContinuousOn (fun x ↦ fderiv ℝ (fderiv ℝ f) x) U)
    (hpos : ∀ x ∈ U, IsStronglyPseudoconvexAt q f x) :
    ∃ ε : V → ℝ, ContinuousOn ε U ∧ (∀ x ∈ U, 0 < ε x) ∧
      ∀ g : V → ℝ, ∀ x ∈ U,
        ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ < ε x →
          IsStronglyPseudoconvexAt q g x := by
  let S : Set (V →L[ℝ] V →L[ℝ] ℝ) :=
    {B | ∃ P : Submodule ℂ V, finrank ℂ V ≤ finrank ℂ P + q ∧
      ∀ v ∈ P, v ≠ 0 → 0 < (B.toBilinForm.leviForm v v).re}
  have hS : IsOpen S := isOpen_setOf_re_leviForm_posOnSubspace q
  have hmem (x : V) (hx : x ∈ U) : fderiv ℝ (fderiv ℝ f) x ∈ S := by
    simpa only [S, Set.mem_ofPred_eq, leviForm_def] using
      (isStronglyPseudoconvexAt_iff.mp (hpos x hx))
  rcases Sᶜ.eq_empty_or_nonempty with hempty | hne
  · -- This occurs, for example, when `q ≥ dim_ℂ V`; then every positive tolerance works.
    refine ⟨fun _ ↦ 1, continuousOn_const, fun _ _ ↦ one_pos, fun g x _ _ ↦ ?_⟩
    have hg : fderiv ℝ (fderiv ℝ g) x ∈ S :=
      (compl_empty_iff.mp hempty).symm ▸ mem_univ _
    simpa only [isStronglyPseudoconvexAt_iff, S, Set.mem_ofPred_eq, leviForm_def] using hg
  · -- Otherwise use the distance to the closed complement of the admissible forms.
    refine ⟨fun x ↦ infDist (fderiv ℝ (fderiv ℝ f) x) Sᶜ,
      (continuous_infDist_pt _).comp_continuousOn hf,
      fun x hx ↦ (hS.isClosed_compl.notMem_iff_infDist_pos hne).mp
        (not_not.mpr (hmem x hx)), fun g x _ hlt ↦ ?_⟩
    have hdist : dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ g) x) <
        infDist (fderiv ℝ (fderiv ℝ f) x) Sᶜ :=
      (dist_comm _ _).trans_lt
        ((dist_eq_norm (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ f) x)).trans_lt hlt)
    have hg : fderiv ℝ (fderiv ℝ g) x ∈ S :=
      not_not.mp (notMem_of_dist_lt_infDist hdist)
    simpa only [isStronglyPseudoconvexAt_iff, S, Set.mem_ofPred_eq, leviForm_def] using hg

end TauCeti
