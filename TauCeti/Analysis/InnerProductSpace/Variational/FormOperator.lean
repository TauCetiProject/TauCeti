/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Inverse
public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
public import TauCeti.Analysis.Semigroups.Generation.Form
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
import TauCeti.Analysis.Semigroups.Dissipative.Hilbert
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# The operator of a form that is coercive after a shift

Let `J : V → H` be a continuous linear map between real Hilbert spaces and `Q` a bounded bilinear
form on `V` that becomes coercive after a shift: for some `c`, the form

`B(u, v) = Q(u, v) + c ⟪J u, J v⟫`

is coercive on `V`. This is the situation of the quadratic form of an elliptic operator on
`V = H¹₀`, `H = L²`, with `J` the inclusion: the form of `∇*∇ + K` is coercive after adding
`c > sup (-K)`. This file realizes such a `Q` as an operator on `H`: the partial linear map
`IsCoercive.formOperator`, defined as `S⁻¹ - c`, where `S` is the solution operator of `B`
along `J` (`IsCoercive.formSolutionOperator`). When `J` has dense range, its graph is

`{(J u, f) : Q(u, v) = ⟪f, J v⟫ for every v ∈ V}`

(`IsCoercive.mem_graph_formOperator_iff`), so it does not depend on the shift `c`
(`IsCoercive.formOperator_eq`), and its domain consists of the `J u` for which `v ↦ Q(u, v)` is
bounded by a multiple of `‖J v‖` (`IsCoercive.mem_domain_formOperator_iff`), by the Riesz
representation of that functional, extended from the dense range of `J`. When `J` has dense
range and `Q` is symmetric:

* it is self-adjoint (`IsCoercive.isSelfAdjoint_formOperator`) and bounded below by `-c`,
  `⟪A x, x⟫ ≥ -c ‖x‖²` (`IsCoercive.neg_mul_norm_sq_le_inner_formOperator`);
* `-c` is a resolvent point, with `(A + c)⁻¹ = S`, that is resolvent `-S` at `-c`
  (`IsCoercive.resolvent_formOperator_neg`), and the resolvent is compact when `J` is
  (`IsCoercive.hasCompactResolvent_formOperator`);
* for `μ + c ≠ 0`, its eigenvectors for `μ` are the eigenvectors of `S` for `(μ + c)⁻¹`
  (`IsCoercive.exists_formOperator_apply_eq_smul_iff`); these nonzero eigenspaces of `S` are
  finite-dimensional when `J` is compact
  (`IsCoercive.finiteDimensional_eigenspace_formSolutionOperator`);
* when `J` is compact, `H` has a Hilbert basis of eigenvectors with eigenvalues greater than
  `-c`, only finitely many below any bound
  (`IsCoercive.exists_hilbertBasis_formOperator`).

For `V = W¹,²₀(D)` and `H = L²(D)` this is the **Dirichlet realization** of the operator, and for
the form of the normal Jacobi operator it is the Dirichlet Jacobi operator.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Chapter VI, §2 (the representation
  theorems for closed semibounded forms).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I*, Theorem VIII.15.
-/

public section

noncomputable section

open LinearPMap Module.End
open scoped InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B Q : V →L[ℝ] V →L[ℝ] ℝ} {J : V →L[ℝ] H} {c : ℝ}

/-- **The operator of a form coercive after a shift.** For a coercive form `B` along
`J : V →L[ℝ] H` and a shift `c`, the partial linear map `S⁻¹ - c` on `H`, where `S` is the solution
operator of `B` along `J`. When `J` has dense range and
`B(u, v) = Q(u, v) + c ⟪J u, J v⟫`, this is the operator represented by `Q`: its graph consists
of the pairs `(J u, f)` with `Q(u, v) = ⟪f, J v⟫` for every `v`
(`IsCoercive.mem_graph_formOperator_iff`). -/
def formOperator (hB : IsCoercive B) (J : V →L[ℝ] H) (c : ℝ) : H →ₗ.[ℝ] H :=
  subScalar (-hB.formGenerator J) c

/-- The form operator is the negative of the form semigroup generator, shifted by `c`. -/
theorem formOperator_def (hB : IsCoercive B) (J : V →L[ℝ] H) (c : ℝ) :
    hB.formOperator J c = subScalar (-hB.formGenerator J) c :=
  (rfl)

/-- The domain of the form operator is the range of its solution operator, for every shift. -/
@[simp]
theorem domain_formOperator (hB : IsCoercive B) (J : V →L[ℝ] H) (c : ℝ) :
    (hB.formOperator J c).domain = LinearMap.range (hB.formSolutionOperator J : H →ₗ[ℝ] H) := by
  rw [formOperator_def, subScalar_domain, neg_domain, hB.formGenerator_domain]

/-- On the image of the solution operator, the form operator sends `S f` to `f - c • S f`. -/
theorem formOperator_apply_formSolutionOperator (hB : IsCoercive B) (hJ : DenseRange J) (f : H) :
    hB.formOperator J c
        ⟨hB.formSolutionOperator J f, by
          rw [hB.domain_formOperator J c]
          exact LinearMap.mem_range_self _ f⟩ =
      f - c • hB.formSolutionOperator J f := by
  rw [LinearPMap.congr_fun (hB.formOperator_def J c) _ (by
      simpa only [subScalar_domain, neg_domain] using
        hB.formSolutionOperator_mem_formGenerator_domain (J := J) f),
    subScalar_apply, LinearPMap.neg_apply, hB.formGenerator_apply_formSolutionOperator hJ, neg_neg]

/-- The graph of the form operator through the solution operator: `(x, f)` lies on it exactly when
`S (f + c x) = x`. -/
theorem mem_graph_formOperator_iff_formSolutionOperator (hB : IsCoercive B) (hJ : DenseRange J)
    {x : H × H} :
    x ∈ (hB.formOperator J c).graph ↔ hB.formSolutionOperator J (x.2 + c • x.1) = x.1 := by
  rw [← ContinuousLinearMap.mem_graph_inverse_toPMap_top_iff _
    (hB.formSolutionOperator_injective hJ) (x := (x.1, x.2 + c • x.1))]
  simp only [formOperator_def, formGenerator_def, neg_neg, mem_graph_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨⟨y, by simpa using y.property⟩, hy, ?_⟩
    rw [← hxy, subScalar_apply, ← hy, sub_add_cancel]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨⟨y, by simp⟩, hy, ?_⟩
    have h := congrArg (· - c • x.1) hxy
    simp only [add_sub_cancel_right] at h
    rw [subScalar_apply, ← h, ← hy]

/-- **The graph of the form operator.** If `B(u, v) = Q(u, v) + c ⟪J u, J v⟫` and `J` has dense
range, then `(x, f)` lies on the graph of the form operator exactly when `x = J u` for some
`u ∈ V` with `Q(u, v) = ⟪f, J v⟫` for every `v ∈ V`. -/
theorem mem_graph_formOperator_iff (hB : IsCoercive B) (hJ : DenseRange J)
    (hBQ : ∀ u v, B u v = Q u v + c * ⟪J u, J v⟫_ℝ) {x : H × H} :
    x ∈ (hB.formOperator J c).graph ↔ ∃ u : V, J u = x.1 ∧ ∀ v, Q u v = ⟪x.2, J v⟫_ℝ := by
  rw [hB.mem_graph_formOperator_iff_formSolutionOperator hJ, formSolutionOperator_apply]
  constructor
  · intro h
    refine ⟨hB.formSolutionMap J (x.2 + c • x.1), h, fun v ↦ ?_⟩
    have := hB.apply_formSolutionMap J (x.2 + c • x.1) v
    rw [hBQ, h, inner_add_left, real_inner_smul_left] at this
    linarith
  · rintro ⟨u, hu, hQ⟩
    rw [← hB.eq_formSolutionMap J (u := u) fun v ↦ by
      rw [hBQ, hQ, inner_add_left, real_inner_smul_left, hu], hu]

/-- **The form operator does not depend on the shift.** When `J` has dense range, two coercive
shifts `B = Q + c ⟪J·, J·⟫` and `B' = Q + c' ⟪J·, J·⟫` of the same form `Q` give the same
operator. -/
theorem formOperator_eq {B' : V →L[ℝ] V →L[ℝ] ℝ} {c' : ℝ} (hB : IsCoercive B)
    (hB' : IsCoercive B') (hJ : DenseRange J) (hBQ : ∀ u v, B u v = Q u v + c * ⟪J u, J v⟫_ℝ)
    (hB'Q : ∀ u v, B' u v = Q u v + c' * ⟪J u, J v⟫_ℝ) :
    hB.formOperator J c = hB'.formOperator J c' :=
  eq_of_eq_graph <| Submodule.ext fun _ ↦ by
    rw [hB.mem_graph_formOperator_iff hJ hBQ, hB'.mem_graph_formOperator_iff hJ hB'Q]

/-- **The form operator is bounded below by `-c`**: `⟪A x, x⟫ ≥ -c ‖x‖²` on its domain. -/
theorem neg_mul_norm_sq_le_inner_formOperator (hB : IsCoercive B) (hJ : DenseRange J)
    (x : (hB.formOperator J c).domain) :
    -c * ‖(x : H)‖ ^ 2 ≤ ⟪hB.formOperator J c x, x⟫_ℝ := by
  have hx : (x : H) ∈ (hB.formGenerator J).domain := by
    simpa only [formOperator_def, subScalar_domain, neg_domain] using x.property
  have h := (TauCeti.Semigroups.isDissipative_iff_real_inner_nonpos _).1
    (hB.isDissipative_formGenerator hJ) ⟨x, hx⟩
  rw [LinearPMap.congr_fun (hB.formOperator_def J c) x.property
      (by simpa only [subScalar_domain, neg_domain] using hx),
    subScalar_apply, LinearPMap.neg_apply, inner_sub_left, inner_neg_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith

/-- **`-c` is a resolvent point of the form operator.** -/
theorem neg_mem_resolventSet_formOperator (hB : IsCoercive B) (hJ : DenseRange J) :
    -c ∈ (hB.formOperator J c).resolventSet := by
  rw [formOperator_def, TauCeti.LinearPMap.mem_resolventSet_subScalar_iff, neg_add_cancel,
    ← neg_zero, mem_resolventSet_neg_iff]
  exact hB.zero_mem_resolventSet_formGenerator hJ

/-- **`(A + c)⁻¹ = S`.** The resolvent of the form operator at `-c` is minus the solution
operator `S` of the shifted form, that is `(A + c)⁻¹ = S`. -/
theorem resolvent_formOperator_neg (hB : IsCoercive B) (hJ : DenseRange J) :
    (hB.formOperator J c).resolvent (-c) = -hB.formSolutionOperator J := by
  rw [formOperator_def, TauCeti.LinearPMap.resolvent_subScalar
      (TauCeti.LinearPMap.mem_resolventSet_subScalar_iff.1
        (hB.neg_mem_resolventSet_formOperator hJ)), neg_add_cancel,
    ← neg_zero, resolvent_neg (hB.zero_mem_resolventSet_formGenerator hJ),
    hB.resolvent_formGenerator_zero hJ]

/-- **The form operator has compact resolvent** when `J` is compact. -/
theorem hasCompactResolvent_formOperator (hB : IsCoercive B) (hJc : IsCompactOperator J)
    (hJ : DenseRange J) : (hB.formOperator J c).HasCompactResolvent :=
  .of_isCompactOperator_resolvent (hB.neg_mem_resolventSet_formOperator hJ) (by
    rw [hB.resolvent_formOperator_neg hJ]
    exact (hB.isCompactOperator_formSolutionOperator hJc).neg)

/-- **Eigenvectors of the form operator are eigenvectors of `S`.** For `μ + c ≠ 0`, `x` lies in
the domain of the form operator with `A x = μ x` exactly when `S x = (μ + c)⁻¹ x`. -/
theorem exists_formOperator_apply_eq_smul_iff (hB : IsCoercive B) (hJ : DenseRange J) {μ : ℝ}
    (hμ : μ + c ≠ 0) {x : H} :
    (∃ hx : x ∈ (hB.formOperator J c).domain, hB.formOperator J c ⟨x, hx⟩ = μ • x) ↔
      hB.formSolutionOperator J x = (μ + c)⁻¹ • x := by
  have hgraph : (∃ hx : x ∈ (hB.formOperator J c).domain,
      hB.formOperator J c ⟨x, hx⟩ = μ • x) ↔ (x, μ • x) ∈ (hB.formOperator J c).graph := by
    simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]
  rw [hgraph, hB.mem_graph_formOperator_iff_formSolutionOperator hJ]
  simp only
  rw [← add_smul, _root_.map_smul]
  exact (eq_inv_smul_iff₀ hμ).symm

/-- **The domain of the form operator.** If `B(u, v) = Q(u, v) + c ⟪J u, J v⟫` and `J` has dense
range, a vector `x` of `H` lies in the domain exactly when `x = J u` for some `u ∈ V` for which
`v ↦ Q(u, v)` is bounded by a multiple of `‖J v‖`. -/
theorem mem_domain_formOperator_iff (hB : IsCoercive B) (hJ : DenseRange J)
    (hBQ : ∀ u v, B u v = Q u v + c * ⟪J u, J v⟫_ℝ) {x : H} [CompleteSpace H] :
    x ∈ (hB.formOperator J c).domain ↔
      ∃ u : V, J u = x ∧ ∃ C : ℝ, ∀ v, |Q u v| ≤ C * ‖J v‖ := by
  simp only [mem_domain_iff, hB.mem_graph_formOperator_iff hJ hBQ]
  constructor
  · rintro ⟨f, u, hu, hQ⟩
    refine ⟨u, hu, ‖f‖, fun v ↦ ?_⟩
    rw [hQ]
    exact abs_real_inner_le_norm f (J v)
  · rintro ⟨u, hu, C, hC⟩
    -- The functional `v ↦ Q(u, v)` extends from the dense range of `J` to `H`; take its Riesz
    -- representative.
    have hbound : ∃ C, ∀ v, ‖(Q u : V →ₗ[ℝ] ℝ) v‖ ≤ C * ‖(J : V →ₗ[ℝ] H) v‖ :=
      ⟨C, fun v ↦ by simpa [Real.norm_eq_abs] using hC v⟩
    set φ := (Q u : V →ₗ[ℝ] ℝ).extendOfNorm (J : V →ₗ[ℝ] H)
    refine ⟨(InnerProductSpace.toDual ℝ H).symm φ, u, hu, fun v ↦ ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    exact (LinearMap.extendOfNorm_eq hJ hbound v).symm

/-- **The eigenvectors of the form operator.** If `B(u, v) = Q(u, v) + c ⟪J u, J v⟫` for a
symmetric `Q`, and `J` is compact with dense range, then `H` has a Hilbert basis of eigenvectors
of the form operator. Its eigenvalues are greater than `-c`, and only finitely many basis
vectors have eigenvalue below any given bound. -/
theorem exists_hilbertBasis_formOperator [CompleteSpace H] (hB : IsCoercive B)
    (hJc : IsCompactOperator J) (hJ : DenseRange J)
    (hBQ : ∀ u v, B u v = Q u v + c * ⟪J u, J v⟫_ℝ) (hsymm : ∀ u v, Q u v = Q v u) :
    ∃ (s : Set H) (b : HilbertBasis s ℝ H) (μ : s → ℝ), ⇑b = ((↑) : s → H) ∧
      (∀ x : s, -c < μ x) ∧
      (∀ x : s, ∃ hx : (x : H) ∈ (hB.formOperator J c).domain,
        hB.formOperator J c ⟨x, hx⟩ = μ x • (x : H)) ∧
      ∀ C : ℝ, {x : s | μ x ≤ C}.Finite := by
  have hsymmB (u v : V) : B u v = B v u := by
    rw [hBQ, hBQ, hsymm, real_inner_comm]
  obtain ⟨s, b, κ, u, hb, hκ, -, hJu, heq, -⟩ :=
    hB.exists_hilbertBasis_forall_apply_eq_smul_inner hJc hJ hsymmB
  refine ⟨s, b, fun x ↦ κ x - c, hb, fun x ↦ by linarith [hκ x], fun x ↦ ?_, fun C ↦ ?_⟩
  · refine (hB.exists_formOperator_apply_eq_smul_iff hJ (by simpa using (hκ x).ne')).2 ?_
    simpa [hJu] using hB.formSolutionOperator_apply_eq_inv_smul (hκ x).ne' (heq x)
  · exact (hB.finite_setOf_le_of_orthonormal hJc b.orthonormal hκ
      (fun x ↦ by rw [hb]; exact hJu x) heq (C + c)).subset
      fun x hx ↦ by simp only [Set.mem_ofPred_eq] at hx ⊢; linarith

variable [CompleteSpace H]

/-- **The form operator is self-adjoint** when `Q` is symmetric and `J` has dense range. -/
theorem isSelfAdjoint_formOperator (hB : IsCoercive B) (hJ : DenseRange J)
    (hBQ : ∀ u v, B u v = Q u v + c * ⟪J u, J v⟫_ℝ) (hsymmQ : ∀ u v, Q u v = Q v u) :
    IsSelfAdjoint (hB.formOperator J c) := by
  have hsymm (u v : V) : B u v = B v u := by
    rw [hBQ, hBQ, hsymmQ, real_inner_comm]
  have hS := ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top _
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
      (hB.isSymmetric_formSolutionOperator J hsymm)) (hB.formSolutionOperator_injective hJ)
  have hT : IsSelfAdjoint ((-c) • (1 : H →L[ℝ] H)) :=
    (IsSelfAdjoint.all (-c)).smul (IsSelfAdjoint.one _)
  have heq : hB.formOperator J c =
      (((-c) • (1 : H →L[ℝ] H) : H →L[ℝ] H) : H →ₗ[ℝ] H) +ᵥ
        ((hB.formSolutionOperator J : H →ₗ[ℝ] H).toPMap ⊤).inverse := by
    have hcoe : (((-c) • (1 : H →L[ℝ] H) : H →L[ℝ] H) : H →ₗ[ℝ] H) =
        -c • LinearMap.id := by
      simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one,
        Module.End.one_eq_id]
    rw [hcoe]
    -- Use the public evaluation API: the imported scalar-shift definition is opaque.
    have hA : hB.formOperator J c =
        subScalar ((hB.formSolutionOperator J : H →ₗ[ℝ] H).toPMap ⊤).inverse c := by
      rw [formOperator_def, formGenerator_def, neg_neg]
    refine LinearPMap.ext (by simp [hA]) fun x hf hg ↦ ?_
    rw [LinearPMap.congr_fun hA hf (by simpa only [subScalar_domain, vadd_domain] using hg)]
    simp [subScalar_apply, LinearPMap.vadd_apply, sub_eq_neg_add]
  rw [heq]
  exact LinearPMap.isSelfAdjoint_perturb_bounded hS hT

end IsCoercive
