/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Characterization

/-!
# The operator represented by a closed sesquilinear form

Let `V` be a complete inner-product space (the form domain), `H` a Hilbert space, `j : V →L[𝕜] H`
a continuous injective linear map with dense range, and `q : V →L⋆[𝕜] V →L[𝕜] 𝕜` a bounded
sesquilinear form (conjugate-linear in its first slot, linear in its second) admitting a real shift
`α : ℝ` for which the Fréchet--Riesz operator of `q_α(u, v) = q u v + α ⟪j u, j v⟫_𝕜`
(`ContinuousLinearMap.shiftedForm`) is invertible — in particular, any shifted-coercive form
satisfying

`c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` (`0 < c`, `ω ≤ α`),

by `ContinuousLinearMap.isUnit_continuousLinearMapOfBilin_shiftedForm`.

By the **first representation theorem** of Kato and Teschl, `q` represents a closed densely defined
partial linear operator `A = j.closedFormOperator hj hdense q` on `H` whose graph consists
of all pairs `(x, h) ∈ H × H` for which some `u : V` satisfies `j u = x` and
`∀ v : V, q u v = ⟪h, j v⟫_𝕜`:

* the definition of `closedFormDomain` and `closedFormOperator`, its graph characterization, its
  formal self-adjointness when `q` is Hermitian, its maximality uniqueness against self-adjoint
  restrictions when `H` is complete (`ContinuousLinearMap.eq_closedFormOperator_of_isSelfAdjoint`),
  and its semibounded lower bound require neither completeness of `V` nor an inner product on `V`
  nor any coercivity witness, so the operator is canonically independent of `(ω, c)`;
* whenever the shifted form `q_α` has invertible Fréchet--Riesz operator, its `H`-forcing
  Lax--Milgram solution operator `S_α` (`InnerProductSpace.formSolutionOperator`) inverts `A + α I`
  on `H`, placing `-α` in the resolvent set of `A` with `A.resolvent (-α) = -S_α` and making `A`
  closed (even without completeness of `H`), densely defined (when `H` is complete), and of compact
  resolvent whenever `j` is a compact operator (all without assuming `q` is Hermitian);
* when `q` is Hermitian (`∀ u v, q u v = star (q v u)`), `A` is symmetric and `A + α I` is
  surjective, so the real-shift self-adjointness criterion
  (`LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective_add_smul`) makes `A` self-adjoint, and
  `ContinuousLinearMap.existsUnique_selfAdjoint_of_closed_form` packages existence and uniqueness
  under shifted coercivity.

## Main declarations

* `ContinuousLinearMap.closedFormDomain` and `ContinuousLinearMap.closedFormOperator`: the domain
  and partial linear operator attached to `(j, q)`, characterized by
  `ContinuousLinearMap.mem_graph_closedFormOperator_iff`,
  `ContinuousLinearMap.eq_closedFormOperator_of_mem_graph_iff`,
  `ContinuousLinearMap.closedFormOperator_apply_eq`, and
  `ContinuousLinearMap.inner_closedFormOperator`.
* `ContinuousLinearMap.isFormalAdjoint_closedFormOperator`,
  `ContinuousLinearMap.eq_closedFormOperator_of_isSelfAdjoint`, and
  `ContinuousLinearMap.neg_mul_norm_sq_le_re_inner_closedFormOperator`: symmetry and
  maximal-symmetry uniqueness for Hermitian forms, and semibounded lower bounds.
* `ContinuousLinearMap.shiftedForm`: the shifted sesquilinear form `q + α ⟪j ·, j ·⟫_𝕜`, with
  `ContinuousLinearMap.shiftedForm_zero`, `ContinuousLinearMap.shiftedForm_shiftedForm`,
  `ContinuousLinearMap.shiftedForm_sub_shiftedForm`,
  `ContinuousLinearMap.mul_norm_sq_le_re_shiftedForm_self`,
  `ContinuousLinearMap.shiftedForm_eq_star`,
  `ContinuousLinearMap.closedFormDomain_shiftedForm`, and
  `ContinuousLinearMap.closedFormOperator_shiftedForm`.
* `ContinuousLinearMap.closedFormOperator_smul_id_smul_innerSL`: along `j = a • id`, the scalar
  form `b ⟪·, ·⟫_𝕜` represents the everywhere defined operator `(b / a ^ 2) • id`.
* `ContinuousLinearMap.isUnit_continuousLinearMapOfBilin_shiftedForm`: shifted coercivity gives
  invertibility of the Fréchet--Riesz operator of `shiftedForm j q α` for all `α ≥ ω`.
* `ContinuousLinearMap.range_formSolutionOperator_shiftedForm`,
  `ContinuousLinearMap.formSolutionOperator_shiftedForm_mem_domain`,
  `ContinuousLinearMap.closedFormOperator_formSolutionOperator_shiftedForm`,
  `ContinuousLinearMap.formSolutionOperator_shiftedForm_apply_add_smul`,
  `ContinuousLinearMap.isResolventAt_closedFormOperator_neg_ofReal`,
  `ContinuousLinearMap.neg_ofReal_mem_resolventSet_closedFormOperator`,
  `ContinuousLinearMap.resolvent_closedFormOperator_neg_ofReal`,
  `ContinuousLinearMap.norm_resolvent_closedFormOperator_neg_ofReal_le`,
  `ContinuousLinearMap.isClosed_closedFormOperator`,
  `ContinuousLinearMap.dense_domain_closedFormOperator`, and
  `ContinuousLinearMap.hasCompactResolvent_closedFormOperator`: range, domain/action/left-inverse
  normal forms, resolvent, closedness, density, and compact resolvent of `closedFormOperator` for
  any invertible real shift without assuming `q` is Hermitian.
* `ContinuousLinearMap.isSelfAdjoint_closedFormOperator` and
  `ContinuousLinearMap.existsUnique_selfAdjoint_of_closed_form`: self-adjointness and unique
  operator representation for Hermitian closed forms.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.3, Theorem 2.13.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.1,
  Theorem 2.1.
* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4, §4.8 and §4.10
  (Theorem 4.25).
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

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
  x.property.choose_spec.2.choose

private theorem closedFormRep_eq (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (x : closedFormDomain j q) {u : V} {h : H}
    (hx : j u = x) (hu : ∀ v : V, q u v = ⟪h, j v⟫_𝕜) :
    closedFormRep j q x = h := by
  have hu_eq : x.property.choose = u := hj (x.property.choose_spec.1.trans hx.symm)
  refine hdense.eq_of_inner_left 𝕜 fun v => ?_
  rw [closedFormRep, ← x.property.choose_spec.2.choose_spec v, hu_eq, hu v]

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
        obtain ⟨u₁, hx₁, h₁, hh₁⟩ := x.property
        obtain ⟨u₂, hx₂, h₂, hh₂⟩ := y.property
        rw [closedFormRep_eq j hj hdense q x hx₁ hh₁, closedFormRep_eq j hj hdense q y hx₂ hh₂]
        refine closedFormRep_eq j hj hdense q (x + y) (u := u₁ + u₂) ?_ fun v => ?_
        · rw [map_add, hx₁, hx₂, Submodule.coe_add]
        · simp [map_add, hh₁ v, hh₂ v, inner_add_left]
      map_smul' := fun c x => by
        obtain ⟨u, hx, h, hh⟩ := x.property
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
`⟪A x, j v⟫_𝕜 = q u v` for all `v : V`. -/
theorem inner_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {x : (closedFormOperator j hj hdense q).domain} {u : V} (hx : j u = x) (v : V) :
    ⟪closedFormOperator j hj hdense q x, j v⟫_𝕜 = q u v := by
  obtain ⟨u', hx', h, hh⟩ := x.property
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
    obtain ⟨u, hx, _⟩ := x.property
    exact ⟨u, hx, fun v => (inner_closedFormOperator j hj hdense q hx v).symm⟩
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
  obtain ⟨u, hx, _⟩ := x.property
  obtain ⟨w, hy, _⟩ := y.property
  calc
    ⟪closedFormOperator j hj hdense q x, (y : H)⟫_𝕜
        = ⟪closedFormOperator j hj hdense q x, j w⟫_𝕜 := by rw [hy]
    _ = q u w := inner_closedFormOperator j hj hdense q hx w
    _ = star (q w u) := hHermitian u w
    _ = star ⟪closedFormOperator j hj hdense q y, j u⟫_𝕜 := by
          rw [inner_closedFormOperator j hj hdense q hy u]
    _ = ⟪j u, closedFormOperator j hj hdense q y⟫_𝕜 := inner_conj_symm _ _
    _ = ⟪(x : H), closedFormOperator j hj hdense q y⟫_𝕜 := by rw [hx]

/-- **Maximality uniqueness of `closedFormOperator`.** Any self-adjoint partial linear operator `T`
on a Hilbert space `H` whose domain vectors come from `V` via `j` and satisfy
`q u v = ⟪T x, j v⟫_𝕜` is already equal to `closedFormOperator j hj hdense q` (without assuming
the reverse graph inclusion, an inner product or completeness on `V`, or coercivity). -/
theorem eq_closedFormOperator_of_isSelfAdjoint [CompleteSpace H] (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u)) {T : H →ₗ.[𝕜] H} (hT : IsSelfAdjoint T)
    (hrep : ∀ x : T.domain, ∃ u : V, j u = (x : H) ∧ ∀ v : V, q u v = ⟪T x, j v⟫_𝕜) :
    T = closedFormOperator j hj hdense q := by
  refine LinearPMap.eq_of_le_of_isFormalAdjoint hT
    (isFormalAdjoint_closedFormOperator j hj hdense q hHermitian)
    (LinearPMap.le_of_le_graph ?_)
  rintro ⟨a, b⟩ hab
  obtain ⟨x, rfl, rfl⟩ := (LinearPMap.mem_graph_iff T).mp hab
  exact (mem_graph_closedFormOperator_iff j hj hdense q).mpr (hrep x)

/-- If `γ * ‖j u‖ ^ 2 ≤ re (q u u)` on `V`, then `closedFormOperator` is bounded below by `γ` on
its domain. -/
theorem mul_norm_sq_le_re_inner_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {γ : ℝ}
    (hγ : ∀ u : V, γ * ‖j u‖ ^ 2 ≤ RCLike.re (q u u))
    (x : (closedFormOperator j hj hdense q).domain) :
    γ * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪closedFormOperator j hj hdense q x, (x : H)⟫_𝕜 := by
  obtain ⟨u, hx, _⟩ := x.property
  have h := inner_closedFormOperator j hj hdense q hx u
  rw [← hx, congrArg RCLike.re h]
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

/-- Shifting `q` by `0` leaves `q` unchanged. -/
@[simp]
theorem shiftedForm_zero (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) :
    shiftedForm j q 0 = q := by
  ext u v
  simp

/-- Iterated scalar shifts of `q` add their shift parameters. -/
@[simp]
theorem shiftedForm_shiftedForm (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α β : ℝ) :
    shiftedForm j (shiftedForm j q α) β = shiftedForm j q (α + β) := by
  ext u v
  simp [add_mul, add_assoc]

/-- **Comparison of two shifts.** The shifts by `α` and `β` differ by `(α - β) ⟪j ·, j ·⟫_𝕜`. -/
theorem shiftedForm_sub_shiftedForm (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α β : ℝ) :
    shiftedForm j q α - shiftedForm j q β =
      ((α - β : ℝ) : 𝕜) • (innerSL 𝕜).bilinearComp j j := by
  ext u v
  simp only [sub_apply, shiftedForm_apply, smul_apply, bilinearComp_apply, innerSL_apply_apply,
    smul_eq_mul, RCLike.ofReal_sub]
  ring

/-- Diagonal real part of `shiftedForm`: `re (q_α u u) = re (q u u) + α * ‖j u‖ ^ 2`. -/
theorem re_shiftedForm_self (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α : ℝ) (u : V) :
    RCLike.re (shiftedForm j q α u u) = RCLike.re (q u u) + α * ‖j u‖ ^ 2 := by
  rw [shiftedForm_apply, map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- Shifting a Hermitian form by a real multiple of `⟪j ·, j ·⟫_𝕜` preserves conjugate symmetry. -/
theorem shiftedForm_eq_star (j : V →L[𝕜] H) {q : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (hHermitian : ∀ u v, q u v = star (q v u)) (α : ℝ) (u v : V) :
    shiftedForm j q α u v = star (shiftedForm j q α v u) := by
  rw [shiftedForm_apply, shiftedForm_apply, star_add, star_mul', ← hHermitian u v]
  simp only [RCLike.star_def, RCLike.conj_ofReal, inner_conj_symm]

/-- If `c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` and `ω ≤ α`, then `shiftedForm j q α`
dominates `c * ‖u‖ ^ 2` on the diagonal. -/
theorem mul_norm_sq_le_re_shiftedForm_self (j : V →L[𝕜] H) {q : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ω α c : ℝ}
    (hα : ω ≤ α) (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2) (u : V) :
    c * ‖u‖ ^ 2 ≤ RCLike.re (shiftedForm j q α u u) := by
  rw [re_shiftedForm_self]
  have hle : ω * ‖j u‖ ^ 2 ≤ α * ‖j u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hα (sq_nonneg _)
  linarith [hcoercive u]

end ShiftedForm

section ShiftedOperator

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Shifting `q` by a real multiple of `⟪j ·, j ·⟫_𝕜` leaves `closedFormDomain` unchanged. -/
@[simp]
theorem closedFormDomain_shiftedForm (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α : ℝ) :
    closedFormDomain j (shiftedForm j q α) = closedFormDomain j q := by
  ext x
  simp only [mem_closedFormDomain_iff, shiftedForm_apply]
  refine exists_congr fun u => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨h, hh⟩
    refine ⟨h - (α : 𝕜) • j u, fun v => ?_⟩
    rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, ← hh v]
    ring
  · rintro ⟨h, hh⟩
    refine ⟨h + (α : 𝕜) • j u, fun v => ?_⟩
    rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal, hh v]

/-- Shifting `q` by `α` shifts `closedFormOperator` by `+(α : 𝕜) • I`, i.e.
`LinearPMap.subScalar _ (-(α : 𝕜))`. -/
theorem closedFormOperator_shiftedForm (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (α : ℝ) :
    closedFormOperator j hj hdense (shiftedForm j q α) =
      LinearPMap.subScalar (closedFormOperator j hj hdense q) (-(α : 𝕜)) := by
  refine LinearPMap.ext (by simp) fun x hx₁ hx₂ => ?_
  rw [LinearPMap.subScalar_apply]
  have hx₀ : x ∈ (closedFormOperator j hj hdense q).domain :=
    LinearPMap.subScalar_domain (closedFormOperator j hj hdense q) (-(α : 𝕜)) ▸ hx₂
  have ⟨u, hu, _⟩ := hx₀
  refine closedFormOperator_apply_eq j hj hdense (shiftedForm j q α) (u := u) hu fun v => ?_
  rw [shiftedForm_apply, _root_.neg_smul, sub_neg_eq_add, inner_add_left,
    inner_closedFormOperator j hj hdense q (x := ⟨x, hx₀⟩) hu v,
    inner_smul_left, RCLike.conj_ofReal, hu]

end ShiftedOperator

/-! ### Scalar forms -/

section ScalarForm

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The represented operator of a scalar form.** Along `j = a • id` with `a ≠ 0`, the form
`q(u, v) = b ⟪u, v⟫_𝕜` represents the everywhere defined operator `(conj b / ‖a‖ ^ 2) • id`: for
`x = a u` the representative `h` must satisfy `b ⟪u, v⟫ = ⟪h, a v⟫` for all `v`, so
`h = conj (b / a) • u = (conj b / ‖a‖ ^ 2) • x`. -/
theorem closedFormOperator_smul_id_smul_innerSL {a : 𝕜} (ha : a ≠ 0) (b : 𝕜)
    (hj : Function.Injective (a • ContinuousLinearMap.id 𝕜 H))
    (hdense : DenseRange (a • ContinuousLinearMap.id 𝕜 H)) :
    closedFormOperator (a • ContinuousLinearMap.id 𝕜 H) hj hdense (b • innerSL 𝕜) =
      ((starRingEnd 𝕜 b / ((‖a‖ ^ 2 : ℝ) : 𝕜)) • LinearMap.id).toPMap ⊤ := by
  have ha' : starRingEnd 𝕜 a ≠ 0 := (map_ne_zero _).2 ha
  have hnorm : ((‖a‖ ^ 2 : ℝ) : 𝕜) = starRingEnd 𝕜 a * a := by
    rw [RCLike.conj_mul]; push_cast; rfl
  rw [hnorm]
  symm
  refine eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h => ?_
  simp only [LinearPMap.mem_graph_iff, LinearMap.toPMap_domain, LinearMap.toPMap_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, Subtype.exists, Submodule.mem_top,
    exists_true_left, exists_eq_left, coe_id', smul_apply, innerSL_apply_apply]
  constructor
  · rintro rfl
    refine ⟨a⁻¹ • x, by simp [smul_smul, ha], fun v => ?_⟩
    simp only [inner_smul_left, inner_smul_right, map_inv₀, map_div₀, map_mul,
      RCLike.conj_conj, smul_eq_mul]
    field_simp
  · rintro ⟨u, rfl, hu⟩
    refine ext_inner_right 𝕜 fun v => ?_
    have := hu v
    simp only [inner_smul_left, inner_smul_right, map_div₀, map_mul, RCLike.conj_conj,
      smul_eq_mul] at this ⊢
    field_simp
    linear_combination this

end ScalarForm

/-! ### Resolvent, closedness, density, and self-adjointness -/

section Representation

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- If `c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` (`0 < c`) and `ω ≤ α`, then the Fréchet--Riesz
operator of `shiftedForm j q α` is a unit. -/
theorem isUnit_continuousLinearMapOfBilin_shiftedForm (j : V →L[𝕜] H)
    {q : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ω α c : ℝ} (hc : 0 < c) (hα : ω ≤ α)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2) :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α)) :=
  InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive _ hc
    (mul_norm_sq_le_re_shiftedForm_self j hα hcoercive)

private theorem apply_formSolutionMap_shiftedForm (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {α : ℝ} (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α)))
    (h : H) (v : V) :
    q (InnerProductSpace.formSolutionMap (shiftedForm j q α) hunit j h) v =
      ⟪h - (α : 𝕜) • InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j h,
        j v⟫_𝕜 := by
  have hsol := InnerProductSpace.apply_formSolutionMap (shiftedForm j q α) hunit j h v
  rw [shiftedForm_apply] at hsol
  rw [InnerProductSpace.formSolutionOperator_apply, inner_sub_left, inner_smul_left,
    RCLike.conj_ofReal, ← hsol]
  ring

/-- The range of the `H`-forcing solution operator of `shiftedForm j q α` is
`closedFormDomain j q`. -/
@[simp]
theorem range_formSolutionOperator_shiftedForm (j : V →L[𝕜] H) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {α : ℝ} (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    LinearMap.range
      (InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j : H →ₗ[𝕜] H) =
      closedFormDomain j q := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    exact ⟨_, (InnerProductSpace.formSolutionOperator_apply _ hunit j h).symm, _,
      apply_formSolutionMap_shiftedForm j q hunit h⟩
  · rintro x ⟨u, rfl, h₀, hu⟩
    refine ⟨h₀ + (α : 𝕜) • j u, ?_⟩
    have hsol : u = InnerProductSpace.formSolutionMap (shiftedForm j q α) hunit j
        (h₀ + (α : 𝕜) • j u) :=
      InnerProductSpace.eq_formSolutionMap (shiftedForm j q α) hunit j fun v => by
        rw [shiftedForm_apply, hu v, inner_add_left, inner_smul_left, RCLike.conj_ofReal]
    simp only [coe_coe, InnerProductSpace.formSolutionOperator_apply, ← hsol]

/-- The `H`-forcing solution operator of `shiftedForm j q α` maps `H` into the domain of
`closedFormOperator`. -/
theorem formSolutionOperator_shiftedForm_mem_domain (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) (h : H) :
    InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j h ∈
      (closedFormOperator j hj hdense q).domain := by
  rw [domain_closedFormOperator, ← range_formSolutionOperator_shiftedForm j q hunit]
  exact LinearMap.mem_range_self _ h

/-- Action of `closedFormOperator` on an element in the image of the `H`-forcing solution operator
of `shiftedForm j q α`. -/
@[simp]
theorem closedFormOperator_formSolutionOperator_shiftedForm (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) (h : H)
    (hx : InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j h ∈
      (closedFormOperator j hj hdense q).domain) :
    closedFormOperator j hj hdense q
      ⟨InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j h, hx⟩ =
      h - (α : 𝕜) • InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j h :=
  closedFormOperator_apply_eq j hj hdense q
    (InnerProductSpace.formSolutionOperator_apply (shiftedForm j q α) hunit j h).symm
    (apply_formSolutionMap_shiftedForm j q hunit h)

/-- The `H`-forcing solution operator of `shiftedForm j q α` left-inverts `A + α I` on the domain
of `closedFormOperator`. -/
@[simp]
theorem formSolutionOperator_shiftedForm_apply_add_smul (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α)))
    (x : (closedFormOperator j hj hdense q).domain) :
    InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j
      (closedFormOperator j hj hdense q x + (α : 𝕜) • (x : H)) = x := by
  obtain ⟨u, hx, _⟩ := x.property
  have hsol : u = InnerProductSpace.formSolutionMap (shiftedForm j q α) hunit j
      (closedFormOperator j hj hdense q x + (α : 𝕜) • (x : H)) := by
    refine InnerProductSpace.eq_formSolutionMap (shiftedForm j q α) hunit j fun v => ?_
    rw [shiftedForm_apply, ← inner_closedFormOperator j hj hdense q hx v, inner_add_left,
      inner_smul_left, RCLike.conj_ofReal, ← hx]
  rw [InnerProductSpace.formSolutionOperator_apply, ← hsol, hx]

/-- **Resolvent identity at `-α`.** Minus the `H`-forcing solution operator of `shiftedForm j q α`
is the resolvent of `closedFormOperator` at `-(α : 𝕜)`, without assuming `q` is Hermitian or `H`
is complete. -/
theorem isResolventAt_closedFormOperator_neg_ofReal (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    LinearPMap.IsResolventAt (closedFormOperator j hj hdense q) (-(α : 𝕜))
      (-InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j) := by
  refine LinearPMap.isResolventAt_iff_surjective_and_apply_smul_sub.mpr ⟨?_, fun x => ?_⟩
  · refine ((closedFormOperator j hj hdense q).surjective_neg_smul_sub_iff_surjective_add_smul
      (α : 𝕜)).mpr fun y => ?_
    exact ⟨⟨_, formSolutionOperator_shiftedForm_mem_domain j hj hdense q hunit y⟩, by simp⟩
  · have hshift :
        (-(α : 𝕜)) • (x : H) - closedFormOperator j hj hdense q x =
          -(closedFormOperator j hj hdense q x + (α : 𝕜) • (x : H)) := by
      rw [_root_.neg_smul]
      abel
    rw [hshift, _root_.neg_apply, map_neg, neg_neg,
      formSolutionOperator_shiftedForm_apply_add_smul]

/-- Whenever `shiftedForm j q α` has invertible Fréchet--Riesz operator, `-(α : 𝕜)` lies in the
resolvent set of `closedFormOperator`. -/
theorem neg_ofReal_mem_resolventSet_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    (-(α : 𝕜)) ∈ (closedFormOperator j hj hdense q).resolventSet :=
  (isResolventAt_closedFormOperator_neg_ofReal j hj hdense q hunit).mem_resolventSet

/-- Formula for the resolvent of `closedFormOperator` at `-(α : 𝕜)`. -/
theorem resolvent_closedFormOperator_neg_ofReal (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    (closedFormOperator j hj hdense q).resolvent (-(α : 𝕜)) =
      -InnerProductSpace.formSolutionOperator (shiftedForm j q α) hunit j :=
  LinearPMap.resolvent_eq_of_isResolventAt
    (isResolventAt_closedFormOperator_neg_ofReal j hj hdense q hunit)

/-- Norm bound `‖R(-α)‖ ≤ c⁻¹ * ‖j‖ ^ 2` on the resolvent of `closedFormOperator` from a lower
norm bound `c * ‖u‖ ≤ ‖B_α♯ u‖` on the shifted form's Fréchet--Riesz operator. -/
theorem norm_resolvent_closedFormOperator_neg_ofReal_le (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α c : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α)))
    (hc : 0 < c)
    (hle : ∀ u, c * ‖u‖ ≤ ‖InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α) u‖) :
    ‖(closedFormOperator j hj hdense q).resolvent (-(α : 𝕜))‖ ≤ c⁻¹ * ‖j‖ ^ 2 := by
  rw [resolvent_closedFormOperator_neg_ofReal j hj hdense q hunit, norm_neg]
  exact InnerProductSpace.norm_formSolutionOperator_le _ hunit hc hle j

/-- **Closedness of `closedFormOperator`.** Whenever some real shift `shiftedForm j q α` has
invertible Fréchet--Riesz operator, `closedFormOperator` is closed (even without Hermiticity of `q`
or completeness of `H`). -/
theorem isClosed_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    (closedFormOperator j hj hdense q).IsClosed :=
  LinearPMap.isClosed_of_mem_resolventSet
    (neg_ofReal_mem_resolventSet_closedFormOperator j hj hdense q hunit)

/-- **Compact resolvent.** If the inclusion `j : V →L[𝕜] H` is a compact operator and some real
shift `shiftedForm j q α` has invertible Fréchet--Riesz operator, `closedFormOperator` has compact
resolvent. -/
theorem hasCompactResolvent_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (hcompact : IsCompactOperator j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    {α : ℝ} (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    (closedFormOperator j hj hdense q).HasCompactResolvent := by
  refine LinearPMap.HasCompactResolvent.of_isCompactOperator_resolvent
    (neg_ofReal_mem_resolventSet_closedFormOperator j hj hdense q hunit) ?_
  rw [resolvent_closedFormOperator_neg_ofReal j hj hdense q hunit]
  exact (InnerProductSpace.isCompactOperator_formSolutionOperator _ hunit hcompact).neg

section CompleteTarget

variable [CompleteSpace H]

/-- **Dense domain of `closedFormOperator`.** On a Hilbert space `H`, whenever some real shift
`shiftedForm j q α` has invertible Fréchet--Riesz operator, `closedFormOperator` is densely defined
(without assuming Hermiticity or coercivity of `q`). -/
theorem dense_domain_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    Dense ((closedFormOperator j hj hdense q).domain : Set H) :=
  (InnerProductSpace.denseRange_formSolutionOperator_of_injective (shiftedForm j q α) hunit
    hj hdense).mono
    (Set.range_subset_iff.mpr (formSolutionOperator_shiftedForm_mem_domain j hj hdense q hunit))

/-- **First representation theorem: self-adjointness.** For a Hermitian bounded sesquilinear form
`q` with an invertible real shift `shiftedForm j q α`, `closedFormOperator` is self-adjoint. -/
theorem isSelfAdjoint_closedFormOperator (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hHermitian : ∀ u v, q u v = star (q v u)) {α : ℝ}
    (hunit : IsUnit (InnerProductSpace.continuousLinearMapOfBilin (shiftedForm j q α))) :
    IsSelfAdjoint (closedFormOperator j hj hdense q) :=
  (isFormalAdjoint_closedFormOperator j hj hdense q
    hHermitian).isSelfAdjoint_of_surjective_add_smul (RCLike.ofReal_im α) fun h =>
    ⟨⟨_, formSolutionOperator_shiftedForm_mem_domain j hj hdense q hunit h⟩, by simp⟩

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
    ⟨isSelfAdjoint_closedFormOperator j hj hdense q hHermitian
      (isUnit_continuousLinearMapOfBilin_shiftedForm j hc le_rfl hcoercive),
      fun x h => mem_graph_closedFormOperator_iff j hj hdense q (p := (x, h))⟩,
    fun _ ⟨_, hA⟩ => eq_closedFormOperator_of_mem_graph_iff j hj hdense q hA⟩

end ContinuousLinearMap
