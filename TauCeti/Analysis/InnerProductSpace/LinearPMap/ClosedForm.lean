/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Characterization

/-!
# The operator represented by a closed sesquilinear form

Let `V` be a complete inner-product space (the form domain), `H` a Hilbert space, `j : V →L[𝕜] H`
a continuous injective linear map with dense range, and `q : V →L⋆[𝕜] V →L[𝕜] 𝕜` a bounded
sesquilinear form (conjugate-linear in its first slot, linear in its second) satisfying a shifted
coercivity bound

`c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` (`0 < c`).

By the **first representation theorem** of Kato and Teschl, `q` represents a closed densely defined
partial linear operator `A = TauCeti.closedFormOperator j hj hdense q` on `H` whose graph consists
of all pairs `(x, h) ∈ H × H` for which some `u : V` satisfies `j u = x` and
`∀ v : V, q u v = ⟪h, j v⟫_𝕜`:

* the definition of `closedFormDomain` and `closedFormOperator`, its graph characterization, its
  formal self-adjointness when `q` is Hermitian, and its semibounded lower bound require neither
  completeness of `V` or `H` nor an inner product on `V` nor any coercivity witness, so the
  operator is canonically independent of `(ω, c)`;
* for every shift `α ≥ ω`, the shifted form `q_α(u, v) = q u v + α ⟪j u, j v⟫_𝕜`
  (`TauCeti.shiftedForm`) is `c`-coercive on `V`, and its `H`-forcing Lax--Milgram solution
  operator `S_α` inverts `A + α I` on `H`, placing `-α` in the resolvent set of `A` with
  `A.resolvent (-α) = -S_α` and making `A` closed and densely defined (and giving `A` compact
  resolvent whenever `j` is a compact operator, without assuming `q` is Hermitian);
* when `q` is Hermitian (`∀ u v, q u v = star (q v u)`), `A` is symmetric and `A + α I` is
  surjective, so the real-shift self-adjointness criterion
  (`LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective_add_smul`) makes `A` self-adjoint,
  maximality (`LinearPMap.eq_of_le_of_isSelfAdjoint`) makes `A` the unique self-adjoint operator
  satisfying the form identity on its domain (`TauCeti.eq_closedFormOperator_of_isSelfAdjoint`),
  and `TauCeti.existsUnique_selfAdjoint_of_closed_form` packages existence and uniqueness.

## Main declarations

* `TauCeti.closedFormDomain` and `TauCeti.closedFormOperator`: the domain and partial linear
  operator attached to `(j, q)`, characterized by `TauCeti.mem_graph_closedFormOperator_iff`,
  `TauCeti.eq_closedFormOperator_of_mem_graph_iff`, `TauCeti.closedFormOperator_apply_eq`, and
  `TauCeti.apply_closedFormOperator`.
* `TauCeti.isFormalAdjoint_closedFormOperator` and
  `TauCeti.neg_mul_norm_sq_le_re_inner_closedFormOperator`: symmetry for Hermitian forms and
  semibounded lower bounds.
* `TauCeti.shiftedForm`: the shifted sesquilinear form `q + α ⟪j ·, j ·⟫_𝕜`, with
  `TauCeti.coercive_shiftedForm` and `TauCeti.shiftedForm_hermitian`.
* `TauCeti.isResolventAt_closedFormOperator_neg_ofReal`,
  `TauCeti.neg_ofReal_mem_resolventSet_closedFormOperator`,
  `TauCeti.resolvent_closedFormOperator_neg_ofReal`, `TauCeti.isClosed_closedFormOperator`,
  `TauCeti.dense_domain_closedFormOperator`, and
  `TauCeti.hasCompactResolvent_closedFormOperator`: resolvent, closedness, density, and compact
  resolvent of `closedFormOperator` without assuming `q` is Hermitian.
* `TauCeti.isSelfAdjoint_closedFormOperator`,
  `TauCeti.exists_selfAdjoint_shifted_inverse_of_closed_form`,
  `TauCeti.exists_compact_selfAdjoint_shifted_inverse_of_closed_form`,
  `TauCeti.eq_closedFormOperator_of_isSelfAdjoint`, and
  `TauCeti.existsUnique_selfAdjoint_of_closed_form`: self-adjointness, shifted inverse, and
  uniqueness for Hermitian closed forms.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.2, Theorem 2.13.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.1,
  Theorem 2.1.
* J. K. Hunter, *Applied Analysis*, World Scientific (2001), §4.8 and Theorem 4.25.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

/-! ### Domain, operator, symmetry, and lower bound -/

section Definition

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The operator domain of a sesquilinear form `q` on `V` along `j : V →L[𝕜] H`: the vectors
`x = j u` whose functional `v ↦ q u v` is represented in `H` as `v ↦ ⟪h, j v⟫_𝕜`. -/
def closedFormDomain (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) : Submodule 𝕜 H where
  carrier := {x : H | ∃ u : V, j u = x ∧ ∃ h : H, ∀ v : V, q u v = ⟪h, j v⟫_𝕜}
  zero_mem' := ⟨0, map_zero j, 0, fun v => by simp⟩
  add_mem' := by
    rintro _ _ ⟨u₁, rfl, h₁, hh₁⟩ ⟨u₂, rfl, h₂, hh₂⟩
    exact ⟨u₁ + u₂, map_add j u₁ u₂, h₁ + h₂, fun v => by
      simp [map_add, hh₁ v, hh₂ v, inner_add_left]⟩
  smul_mem' := by
    rintro c _ ⟨u, rfl, h, hh⟩
    exact ⟨c • u, map_smul j c u, c • h, fun v => by simp [hh v, inner_smul_left]⟩

/-- Membership in `closedFormDomain j q`. -/
@[simp]
theorem mem_closedFormDomain_iff (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {x : H} :
    x ∈ closedFormDomain j q ↔ ∃ u : V, j u = x ∧ ∃ h : H, ∀ v : V, q u v = ⟪h, j v⟫_𝕜 :=
  Iff.rfl

/-- Every vector in `closedFormDomain j q` lies in the range of `j`. -/
theorem closedFormDomain_le_range (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) :
    closedFormDomain j q ≤ LinearMap.range (j : V →ₗ[𝕜] H) := by
  rintro x ⟨u, rfl, _⟩
  exact ⟨u, rfl⟩

/-- Chosen `H`-representative of `x : closedFormDomain j q`. -/
private def closedFormRep (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (x : closedFormDomain j q) : H :=
  x.2.choose_spec.2.choose

private theorem closedFormRep_eq (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (x : closedFormDomain j q) {u : V} {h : H}
    (hx : j u = x) (hu : ∀ v : V, q u v = ⟪h, j v⟫_𝕜) :
    closedFormRep j q x = h := by
  have hu_eq : x.2.choose = u := hj (x.2.choose_spec.1.trans hx.symm)
  refine hdense.eq_of_inner_left 𝕜 fun v => ?_
  rw [closedFormRep, ← x.2.choose_spec.2.choose_spec v, hu_eq, hu v]

/-- **The partial linear operator represented by a sesquilinear form.** Given an injective
continuous linear map `j : V →L[𝕜] H` with dense range and a bounded sesquilinear form
`q : V →L⋆[𝕜] V →L[𝕜] 𝕜`, `closedFormOperator j hj hdense q` has domain `closedFormDomain j q`
and sends `j u` to the unique `h : H` satisfying `∀ v, q u v = ⟪h, j v⟫_𝕜`. -/
def closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j) (hdense : DenseRange j)
    (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) : H →ₗ.[𝕜] H where
  domain := closedFormDomain j q
  toFun :=
    { toFun := closedFormRep j q
      map_add' := fun x y => by
        obtain ⟨u₁, hx₁, h₁, hh₁⟩ := x.2
        obtain ⟨u₂, hx₂, h₂, hh₂⟩ := y.2
        rw [closedFormRep_eq j hj hdense q x hx₁ hh₁, closedFormRep_eq j hj hdense q y hx₂ hh₂]
        refine closedFormRep_eq j hj hdense q (x + y) (u := u₁ + u₂) ?_ fun v => ?_
        · rw [map_add, hx₁, hx₂, Submodule.coe_add]
        · simp [map_add, hh₁ v, hh₂ v, inner_add_left]
      map_smul' := fun c x => by
        obtain ⟨u, hx, h, hh⟩ := x.2
        rw [RingHom.id_apply, closedFormRep_eq j hj hdense q x hx hh]
        refine closedFormRep_eq j hj hdense q (c • x) (u := c • u) ?_ fun v => ?_
        · rw [map_smul, hx, Submodule.coe_smul]
        · simp [hh v, inner_smul_left] }

/-- The domain of `closedFormOperator` is `closedFormDomain`. -/
@[simp]
theorem domain_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) :
    (closedFormOperator j hj hdense q).domain = closedFormDomain j q :=
  (rfl)

/-- Membership in the domain of `closedFormOperator`. -/
theorem mem_domain_closedFormOperator_iff (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {x : H} :
    x ∈ (closedFormOperator j hj hdense q).domain ↔
      ∃ u : V, j u = x ∧ ∃ h : H, ∀ v : V, q u v = ⟪h, j v⟫_𝕜 :=
  Iff.rfl

/-- If `q u · = ⟪h, j ·⟫_𝕜`, then `j u` lies in the domain of `closedFormOperator`. -/
theorem apply_mem_domain_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {u : V} {h : H}
    (hu : ∀ v : V, q u v = ⟪h, j v⟫_𝕜) :
    j u ∈ (closedFormOperator j hj hdense q).domain :=
  ⟨u, rfl, h, hu⟩

/-- Action of `closedFormOperator` on a represented vector. -/
theorem closedFormOperator_apply_eq (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {x : (closedFormOperator j hj hdense q).domain} {u : V} {h : H} (hx : j u = x)
    (hu : ∀ v : V, q u v = ⟪h, j v⟫_𝕜) :
    closedFormOperator j hj hdense q x = h :=
  closedFormRep_eq j hj hdense q x hx hu

/-- **Form identity of `closedFormOperator`.** If `j u = x` for `x` in the domain, then
`q u v = ⟪A x, j v⟫_𝕜` for all `v : V`. -/
theorem apply_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {x : (closedFormOperator j hj hdense q).domain} {u : V} (hx : j u = x) (v : V) :
    q u v = ⟪closedFormOperator j hj hdense q x, j v⟫_𝕜 := by
  obtain ⟨u', hx', h, hh⟩ := x.2
  have hu : u = u' := hj (hx.trans hx'.symm)
  rw [closedFormOperator_apply_eq j hj hdense q hx' hh, hu, hh v]

/-- **Graph characterization of `closedFormOperator`.** -/
theorem mem_graph_closedFormOperator_iff (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {p : H × H} :
    p ∈ (closedFormOperator j hj hdense q).graph ↔
      ∃ u : V, j u = p.1 ∧ ∀ v : V, q u v = ⟪p.2, j v⟫_𝕜 := by
  rcases p with ⟨x₀, y₀⟩
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, rfl, rfl⟩
    obtain ⟨u, hx, _⟩ := x.2
    exact ⟨u, hx, apply_closedFormOperator j hj hdense q hx⟩
  · rintro ⟨u, rfl, hu⟩
    have hmem := apply_mem_domain_closedFormOperator j hj hdense q hu
    exact ⟨⟨j u, hmem⟩, rfl, closedFormOperator_apply_eq j hj hdense q (x := ⟨j u, hmem⟩) rfl hu⟩

/-- Any partial linear operator whose graph is the form relation of `(j, q)` equals
`closedFormOperator j hj hdense q`. -/
theorem eq_closedFormOperator_of_mem_graph_iff (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {A : H →ₗ.[𝕜] H}
    (hA : ∀ x h : H, (x, h) ∈ A.graph ↔
      ∃ u : V, j u = x ∧ ∀ v : V, q u v = ⟪h, j v⟫_𝕜) :
    A = closedFormOperator j hj hdense q := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, h⟩
  rw [hA x h, mem_graph_closedFormOperator_iff]

/-- **Symmetry of `closedFormOperator`.** If `q` is Hermitian, `closedFormOperator` is formally
self-adjoint. -/
theorem isFormalAdjoint_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u)) :
    (closedFormOperator j hj hdense q).IsFormalAdjoint (closedFormOperator j hj hdense q) := by
  intro x y
  obtain ⟨u, hx, _⟩ := x.2
  obtain ⟨w, hy, _⟩ := y.2
  calc
    ⟪closedFormOperator j hj hdense q x, (y : H)⟫_𝕜
        = ⟪closedFormOperator j hj hdense q x, j w⟫_𝕜 := by rw [hy]
    _ = q u w := (apply_closedFormOperator j hj hdense q hx w).symm
    _ = star (q w u) := hHermitian u w
    _ = star ⟪closedFormOperator j hj hdense q y, j u⟫_𝕜 := by
          rw [apply_closedFormOperator j hj hdense q hy u]
    _ = ⟪j u, closedFormOperator j hj hdense q y⟫_𝕜 := inner_conj_symm _ _
    _ = ⟪(x : H), closedFormOperator j hj hdense q y⟫_𝕜 := by rw [hx]

/-- If `γ * ‖j u‖ ^ 2 ≤ re (q u u)` on `V`, then `closedFormOperator` is bounded below by `γ` on
its domain. -/
theorem mul_norm_sq_le_re_inner_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {γ : ℝ}
    (hγ : ∀ u : V, γ * ‖j u‖ ^ 2 ≤ RCLike.re (q u u))
    (x : (closedFormOperator j hj hdense q).domain) :
    γ * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪closedFormOperator j hj hdense q x, (x : H)⟫_𝕜 := by
  obtain ⟨u, hx, _⟩ := x.2
  have h := apply_closedFormOperator j hj hdense q hx u
  rw [← hx, ← congrArg RCLike.re h]
  exact hγ u

/-- A shifted coercivity bound `c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` (`0 ≤ c`) gives the
lower bound `-ω * ‖x‖ ^ 2 ≤ re ⟪A x, x⟫_𝕜` on the domain of `closedFormOperator`. -/
theorem neg_mul_norm_sq_le_re_inner_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {ω c : ℝ} (hc : 0 ≤ c)
    (hcoercive : ∀ u : V, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (x : (closedFormOperator j hj hdense q).domain) :
    -ω * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪closedFormOperator j hj hdense q x, (x : H)⟫_𝕜 := by
  refine mul_norm_sq_le_re_inner_closedFormOperator j hj hdense q (fun u => ?_) x
  have h0 : 0 ≤ c * ‖u‖ ^ 2 := mul_nonneg hc (sq_nonneg _)
  linarith [hcoercive u]

end Definition

/-! ### Shifted sesquilinear form -/

section ShiftedForm

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The shifted sesquilinear form `q_α(u, v) = q u v + α ⟪j u, j v⟫_𝕜` for `α : ℝ`. -/
def shiftedForm (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α : ℝ) : V →L⋆[𝕜] V →L[𝕜] 𝕜 :=
  q + (α : 𝕜) • (innerSL 𝕜).bilinearComp j j

/-- Pointwise evaluation of `shiftedForm`. -/
@[simp]
theorem shiftedForm_apply (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α : ℝ) (u v : V) :
    shiftedForm j q α u v = q u v + (α : 𝕜) * ⟪j u, j v⟫_𝕜 :=
  (rfl)

/-- Diagonal real part of `shiftedForm`: `re (q_α u u) = re (q u u) + α * ‖j u‖ ^ 2`. -/
theorem re_shiftedForm_self (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α : ℝ) (u : V) :
    RCLike.re (shiftedForm j q α u u) = RCLike.re (q u u) + α * ‖j u‖ ^ 2 := by
  rw [shiftedForm_apply, map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- Shifting a Hermitian form by a real multiple of `⟪j ·, j ·⟫_𝕜` preserves Hermiticity. -/
theorem shiftedForm_hermitian (j : V →L[𝕜] H) {q : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (hHermitian : ∀ u v, q u v = star (q v u)) (α : ℝ) (u v : V) :
    shiftedForm j q α u v = star (shiftedForm j q α v u) := by
  rw [shiftedForm_apply, shiftedForm_apply, star_add, star_mul', ← hHermitian u v]
  simp only [RCLike.star_def, RCLike.conj_ofReal, inner_conj_symm]

/-- If `c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` and `ω ≤ α`, then `shiftedForm j q α` is
`c`-coercive. -/
theorem coercive_shiftedForm (j : V →L[𝕜] H) {q : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ω α c : ℝ}
    (hα : ω ≤ α) (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2) (u : V) :
    c * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm j q α u u) := by
  rw [re_shiftedForm_self]
  have hle : ω * ‖j u‖ ^ 2 ≤ α * ‖j u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hα (sq_nonneg _)
  linarith [hcoercive u]

end ShiftedForm

/-! ### Resolvent, closedness, density, and self-adjointness -/

section Representation

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The `H`-forcing solution operator of `shiftedForm j q α` maps `H` into the domain of
`closedFormOperator` and right-inverts `A + α I`. -/
theorem formSolutionOperator_shiftedForm_mem_domain (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α c : ℝ} (hc : 0 < c)
    (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm j q α u u)) (h : H) :
    ∃ hmem : InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j h ∈
        (closedFormOperator j hj hdense q).domain,
      closedFormOperator j hj hdense q ⟨_, hmem⟩ +
        (α : 𝕜) • InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j h = h := by
  set u := InnerProductSpace.formSolutionMap (shiftedForm j q α) hc hcoer j h
  have hq : ∀ v : V, q u v = ⟪h - (α : 𝕜) • j u, j v⟫_𝕜 := fun v => by
    have hsol := InnerProductSpace.apply_formSolutionMap (shiftedForm j q α) hc hcoer j h v
    rw [shiftedForm_apply] at hsol
    rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, ← hsol]
    ring
  have hmem : InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j h ∈
      (closedFormOperator j hj hdense q).domain := by
    rw [InnerProductSpace.formSolutionOperator_apply]
    exact apply_mem_domain_closedFormOperator j hj hdense q hq
  refine ⟨hmem, ?_⟩
  have hju : j u = (⟨InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j h,
      hmem⟩ : (closedFormOperator j hj hdense q).domain) :=
    (InnerProductSpace.formSolutionOperator_apply (shiftedForm j q α) hc hcoer j h).symm
  rw [closedFormOperator_apply_eq j hj hdense q hju hq,
    InnerProductSpace.formSolutionOperator_apply, sub_add_cancel]

/-- The `H`-forcing solution operator of `shiftedForm j q α` left-inverts `A + α I` on the domain
of `closedFormOperator`. -/
theorem formSolutionOperator_shiftedForm_apply_add_smul (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α c : ℝ}
    (hc : 0 < c) (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm j q α u u))
    (x : (closedFormOperator j hj hdense q).domain) :
    InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j
      (closedFormOperator j hj hdense q x + (α : 𝕜) • (x : H)) = x := by
  obtain ⟨u, hx, _⟩ := x.2
  have hsol : u = InnerProductSpace.formSolutionMap (shiftedForm j q α) hc hcoer j
      (closedFormOperator j hj hdense q x + (α : 𝕜) • (x : H)) := by
    refine InnerProductSpace.eq_formSolutionMap (shiftedForm j q α) hc hcoer j fun v => ?_
    rw [shiftedForm_apply, apply_closedFormOperator j hj hdense q hx v, inner_add_left,
      inner_smul_left, RCLike.conj_ofReal, ← hx]
  rw [InnerProductSpace.formSolutionOperator_apply, ← hsol, hx]

/-- **Resolvent identity at `-α`.** Minus the `H`-forcing solution operator of `shiftedForm j q α`
is the resolvent of `closedFormOperator` at `-(α : 𝕜)`, without assuming `q` is Hermitian or `H`
is complete. -/
theorem isResolventAt_closedFormOperator_neg_ofReal (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α c : ℝ} (hc : 0 < c)
    (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm j q α u u)) :
    LinearPMap.IsResolventAt (closedFormOperator j hj hdense q) (-(α : 𝕜))
      (-InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j) := by
  set A := closedFormOperator j hj hdense q
  set S := InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j
  have hmem (y : H) : (-S) y ∈ A.domain := by
    rw [neg_apply, ← S.map_neg]
    exact (formSolutionOperator_shiftedForm_mem_domain j hj hdense q hc hcoer (-y)).1
  refine ⟨hmem, fun y => ?_, fun x => ?_⟩
  · obtain ⟨hm, hinv⟩ :=
      formSolutionOperator_shiftedForm_mem_domain j hj hdense q hc hcoer (-y)
    have hA : A ⟨(-S) y, hmem y⟩ = A ⟨S (-y), hm⟩ :=
      congrArg A (Subtype.ext (by dsimp only; rw [neg_apply, ← S.map_neg]))
    calc
      (-(α : 𝕜)) • (-S) y - A ⟨(-S) y, hmem y⟩
          = -(A ⟨S (-y), hm⟩ + (α : 𝕜) • S (-y)) := by
            rw [hA, neg_apply, ← S.map_neg, neg_smul]
            abel
      _ = y := by rw [hinv, neg_neg]
  · have hshift : (-(α : 𝕜)) • (x : H) - A x = -(A x + (α : 𝕜) • (x : H)) := by
      rw [neg_smul]
      abel
    rw [hshift, neg_apply, S.map_neg, neg_neg]
    exact formSolutionOperator_shiftedForm_apply_add_smul j hj hdense q hc hcoer x

/-- Every shift `-α` with `ω ≤ α` lies in the resolvent set of `closedFormOperator`. -/
theorem neg_ofReal_mem_resolventSet_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {ω α c : ℝ} (hc : 0 < c) (hα : ω ≤ α)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2) :
    (-(α : 𝕜)) ∈ (closedFormOperator j hj hdense q).resolventSet :=
  (isResolventAt_closedFormOperator_neg_ofReal j hj hdense q hc
    (coercive_shiftedForm j hα hcoercive)).mem_resolventSet

/-- Formula for the resolvent of `closedFormOperator` at `-(α : 𝕜)`. -/
theorem resolvent_closedFormOperator_neg_ofReal (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {ω α c : ℝ} (hc : 0 < c) (hα : ω ≤ α)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2) :
    (closedFormOperator j hj hdense q).resolvent (-(α : 𝕜)) =
      -InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc
        (coercive_shiftedForm j hα hcoercive) j :=
  LinearPMap.resolvent_eq_of_isResolventAt
    (isResolventAt_closedFormOperator_neg_ofReal j hj hdense q hc
      (coercive_shiftedForm j hα hcoercive))

/-- Norm bound `‖R(-α)‖ ≤ c⁻¹ * ‖j‖ ^ 2` on the resolvent of `closedFormOperator`. -/
theorem norm_resolvent_closedFormOperator_neg_ofReal_le (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {ω α c : ℝ}
    (hc : 0 < c) (hα : ω ≤ α)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2) :
    ‖(closedFormOperator j hj hdense q).resolvent (-(α : 𝕜))‖ ≤ c⁻¹ * ‖j‖ ^ 2 := by
  rw [resolvent_closedFormOperator_neg_ofReal j hj hdense q hc hα hcoercive, norm_neg]
  exact InnerProductSpace.norm_formSolutionOperator_le _ hc _ j

/-- **Closedness of `closedFormOperator`.** Under a shifted coercivity bound, `closedFormOperator`
is closed (even without Hermiticity of `q` or completeness of `H`). -/
theorem isClosed_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + α * ‖j u‖ ^ 2) :
    (closedFormOperator j hj hdense q).IsClosed :=
  LinearPMap.isClosed_of_mem_resolventSet
    (neg_ofReal_mem_resolventSet_closedFormOperator j hj hdense q hc le_rfl hcoercive)

/-- **Compact resolvent.** If the inclusion `j : V →L[𝕜] H` is a compact operator,
`closedFormOperator` has compact resolvent. -/
theorem hasCompactResolvent_closedFormOperator {j : V →L[𝕜] H} (hj : Function.Injective j)
    (hdense : DenseRange j) (hcompact : IsCompactOperator j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {α c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + α * ‖j u‖ ^ 2) :
    (closedFormOperator j hj hdense q).HasCompactResolvent := by
  refine LinearPMap.HasCompactResolvent.of_isCompactOperator_resolvent
    (neg_ofReal_mem_resolventSet_closedFormOperator j hj hdense q hc le_rfl hcoercive) ?_
  rw [resolvent_closedFormOperator_neg_ofReal j hj hdense q hc le_rfl hcoercive,
    InnerProductSpace.formSolutionOperator_eq_comp]
  exact (hcompact.comp_clm _).neg

section CompleteTarget

variable [CompleteSpace H]

/-- **Dense domain of `closedFormOperator`.** On a Hilbert space `H`, any shifted-coercive bounded
form `q` (even non-Hermitian) has densely defined `closedFormOperator`. -/
theorem dense_domain_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + α * ‖j u‖ ^ 2) :
    Dense ((closedFormOperator j hj hdense q).domain : Set H) := by
  have hcoer := coercive_shiftedForm j le_rfl hcoercive
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨hmem, _⟩ := formSolutionOperator_shiftedForm_mem_domain j hj hdense q hc hcoer w
  have horth : ⟪w, InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j w⟫_𝕜 =
      0 := Submodule.inner_left_of_mem_orthogonal hmem hw
  rw [InnerProductSpace.inner_formSolutionOperator_self] at horth
  have hle := hcoer (InnerProductSpace.formSolutionMap (shiftedForm j q α) hc hcoer j w)
  rw [horth, map_zero] at hle
  have hu0 : InnerProductSpace.formSolutionMap (shiftedForm j q α) hc hcoer j w = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp
      (le_antisymm (nonpos_of_mul_nonpos_right hle hc) (sq_nonneg _)))
  refine InnerProductSpace.formSolutionOperator_injective (shiftedForm j q α) hc hcoer hdense ?_
  rw [InnerProductSpace.formSolutionOperator_apply, hu0, map_zero, map_zero]

/-- **First representation theorem: self-adjointness.** For a Hermitian bounded sesquilinear form
`q` with a shifted coercivity bound, `closedFormOperator` is self-adjoint. -/
theorem isSelfAdjoint_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u)) {α c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + α * ‖j u‖ ^ 2) :
    IsSelfAdjoint (closedFormOperator j hj hdense q) := by
  refine (isFormalAdjoint_closedFormOperator j hj hdense q
    hHermitian).isSelfAdjoint_of_surjective_add_smul (α := α) fun h => ?_
  obtain ⟨hmem, hinv⟩ := formSolutionOperator_shiftedForm_mem_domain j hj hdense q hc
    (coercive_shiftedForm j le_rfl hcoercive) h
  exact ⟨⟨_, hmem⟩, hinv⟩

/-- **Shifted bounded self-adjoint inverse of a closed-form operator.** For any partial linear
operator `A` whose graph is the closed-form relation of `(j, q)` and any shift `α ≥ ω`, `A + α I`
has a bounded self-adjoint two-sided inverse `S_α : H →L[𝕜] H`. -/
theorem exists_selfAdjoint_shifted_inverse_of_closed_form (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u)) {ω α c : ℝ} (hc : 0 < c) (hα : ω ≤ α)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (A : H →ₗ.[𝕜] H)
    (hA : ∀ x f : H, (x, f) ∈ A.graph ↔
      ∃ u : V, j u = x ∧ ∀ v : V, q u v = ⟪f, j v⟫_𝕜) :
    ∃ S : H →L[𝕜] H, IsSelfAdjoint S ∧
      (∀ h : H, ∃ hS : S h ∈ A.domain, A ⟨S h, hS⟩ + (α : 𝕜) • S h = h) ∧
      ∀ x : A.domain, S (A x + (α : 𝕜) • (x : H)) = x := by
  obtain rfl := eq_closedFormOperator_of_mem_graph_iff j hj hdense q hA
  have hcoer := coercive_shiftedForm j hα hcoercive
  refine ⟨InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j,
    InnerProductSpace.isSelfAdjoint_formSolutionOperator (shiftedForm j q α) hc hcoer j
      (shiftedForm_hermitian j hHermitian α),
    formSolutionOperator_shiftedForm_mem_domain j hj hdense q hc hcoer,
    formSolutionOperator_shiftedForm_apply_add_smul j hj hdense q hc hcoer⟩

/-- **Compact shifted self-adjoint inverse of a compact closed-form pair.** When `j` is also
compact, the bounded self-adjoint inverse `S_α` of `A + α I` is a compact operator. -/
theorem exists_compact_selfAdjoint_shifted_inverse_of_closed_form {j : V →L[𝕜] H}
    (hj : Function.Injective j) (hdense : DenseRange j) (hcompact : IsCompactOperator j)
    (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (hHermitian : ∀ u v, q u v = star (q v u))
    {ω α c : ℝ} (hc : 0 < c) (hα : ω ≤ α)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (A : H →ₗ.[𝕜] H)
    (hA : ∀ x f : H, (x, f) ∈ A.graph ↔
      ∃ u : V, j u = x ∧ ∀ v : V, q u v = ⟪f, j v⟫_𝕜) :
    ∃ S : H →L[𝕜] H, IsCompactOperator S ∧ IsSelfAdjoint S ∧
      (∀ h : H, ∃ hS : S h ∈ A.domain, A ⟨S h, hS⟩ + (α : 𝕜) • S h = h) ∧
      ∀ x : A.domain, S (A x + (α : 𝕜) • (x : H)) = x := by
  obtain rfl := eq_closedFormOperator_of_mem_graph_iff j hj hdense q hA
  have hcoer := coercive_shiftedForm j hα hcoercive
  have hcomp : IsCompactOperator
      (InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j) := by
    rw [InnerProductSpace.formSolutionOperator_eq_comp]
    exact hcompact.comp_clm _
  refine ⟨InnerProductSpace.formSolutionOperator (shiftedForm j q α) hc hcoer j, hcomp,
    InnerProductSpace.isSelfAdjoint_formSolutionOperator (shiftedForm j q α) hc hcoer j
      (shiftedForm_hermitian j hHermitian α),
    formSolutionOperator_shiftedForm_mem_domain j hj hdense q hc hcoer,
    formSolutionOperator_shiftedForm_apply_add_smul j hj hdense q hc hcoer⟩

/-- **Maximality uniqueness of `closedFormOperator`.** Any self-adjoint partial linear operator `T`
whose domain vectors come from `V` via `j` and satisfy `q u v = ⟪T x, j v⟫_𝕜` is already equal to
`closedFormOperator j hj hdense q` (without assuming the reverse graph inclusion). -/
theorem eq_closedFormOperator_of_isSelfAdjoint (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u)) {α c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + α * ‖j u‖ ^ 2)
    {T : H →ₗ.[𝕜] H} (hT : IsSelfAdjoint T)
    (hrep : ∀ x : T.domain, ∃ u : V, j u = (x : H) ∧ ∀ v : V, q u v = ⟪T x, j v⟫_𝕜) :
    T = closedFormOperator j hj hdense q := by
  refine LinearPMap.eq_of_le_of_isSelfAdjoint hT
    (isSelfAdjoint_closedFormOperator j hj hdense q hHermitian hc hcoercive)
    (LinearPMap.le_of_le_graph ?_)
  rintro ⟨a, b⟩ hab
  obtain ⟨x, rfl, rfl⟩ := (LinearPMap.mem_graph_iff T).mp hab
  exact (mem_graph_closedFormOperator_iff j hj hdense q).mpr (hrep x)

end CompleteTarget

end Representation

/-- **First representation theorem for closed Hermitian forms** (Teschl, Theorem 2.13; Kato,
Chapter VI, Theorem 2.1). A bounded Hermitian sesquilinear form `q` on a complete inner-product
space `V`, with a continuous injective dense inclusion `j : V →L[𝕜] H` into a Hilbert space `H`
and a positive shifted coercivity bound `c * ‖u‖ ^ 2 ≤ re (q u u) + α * ‖j u‖ ^ 2` (`0 < c`),
represents a unique self-adjoint partial operator on `H`. -/
theorem existsUnique_selfAdjoint_of_closed_form
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    (j : V →L[𝕜] H) (hj : Function.Injective j) (hdense : DenseRange j)
    (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u))
    (α c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + α * ‖j u‖ ^ 2) :
    ∃! A : H →ₗ.[𝕜] H, IsSelfAdjoint A ∧
      ∀ x h : H, (x, h) ∈ A.graph ↔
        ∃ u : V, j u = x ∧ ∀ v : V, q u v = inner 𝕜 h (j v) :=
  ⟨closedFormOperator j hj hdense q,
    ⟨isSelfAdjoint_closedFormOperator j hj hdense q hHermitian hc hcoercive, fun x h =>
      mem_graph_closedFormOperator_iff j hj hdense q (p := (x, h))⟩,
    fun _ ⟨_, hA⟩ => eq_closedFormOperator_of_mem_graph_iff j hj hdense q hA⟩

end TauCeti
