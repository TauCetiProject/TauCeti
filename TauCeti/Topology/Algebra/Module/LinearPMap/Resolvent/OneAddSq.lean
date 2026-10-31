/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.DomainPow

/-!
# The bounded inverse of `1 + A²`

For a partial linear map `A` on a complex topological vector space whose resolvent set contains
`i` and `-i`, the factorization `1 + A² = (-i - A)(i - A)` shows that the composite of
resolvents

`(1 + A²)⁻¹ = R(-i) R(i)`

is a continuous linear inverse of `1 + A²`, defined on the iterated domain `D(A²)`. This is the
operator `LinearPMap.invOneAddSq`. It maps every vector into `D(A²)`, inverts `1 + A²` on both
sides, is injective and commutes with `A`. When `A` has compact resolvent it is a compact
operator.

For a self-adjoint operator on a Hilbert space, `±i` always lie in the resolvent set and
`(1 + A²)⁻¹` is the positive operator `R(i)* R(i)`; the spectral consequences are developed in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.CompactResolvent`. Here we also record the
algebraic facts behind them: an eigenvector of `(1 + A²)⁻¹` for a nonzero eigenvalue lies in
every iterated domain `D(Aⁿ)`, and `A` preserves each eigenspace of `(1 + A²)⁻¹`.

## Main definitions

* `LinearPMap.invOneAddSq`: the operator `(1 + A²)⁻¹ = R(-i) R(i)`.

## Main results

* `LinearPMap.invOneAddSq_add_apply_apply`, `LinearPMap.invOneAddSq_apply_add_apply`:
  `(1 + A²)⁻¹` is a two-sided inverse of `1 + A²`.
* `LinearPMap.HasCompactResolvent.isCompactOperator_invOneAddSq`: for an operator with compact
  resolvent, `(1 + A²)⁻¹` is compact.
* `LinearPMap.eigenspace_invOneAddSq_le_domainPow`: eigenvectors of `(1 + A²)⁻¹` for nonzero
  eigenvalues lie in every `D(Aⁿ)`.
* `LinearPMap.apply_mem_eigenspace_invOneAddSq`: `A` preserves the eigenspaces of `(1 + A²)⁻¹`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
* A. Connes, *Noncommutative Geometry*, Chapter IV, §2.
-/

public section

noncomputable section

open Complex Module End

namespace LinearPMap

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [Module ℂ X] {A : X →ₗ.[ℂ] X}

variable (A) in
/-- The bounded inverse `(1 + A²)⁻¹ = R(-i) R(i)` of `1 + A²`, for a partial linear map `A`
whose resolvent set contains `±i`; this holds for every self-adjoint operator on a Hilbert space.
Outside that case the value is the composite of the resolvents' junk values. -/
def invOneAddSq : X →L[ℂ] X :=
  A.resolvent (-I) ∘L A.resolvent I

theorem invOneAddSq_def : A.invOneAddSq = A.resolvent (-I) ∘L A.resolvent I := (rfl)

theorem invOneAddSq_apply (y : X) : A.invOneAddSq y = A.resolvent (-I) (A.resolvent I y) := (rfl)

variable (hp : I ∈ A.resolventSet) (hm : -I ∈ A.resolventSet)
include hp hm

/-- The two resolvents defining `(1 + A²)⁻¹` commute: `(1 + A²)⁻¹ = R(i) R(-i)`. -/
theorem invOneAddSq_eq_resolvent_I_comp : A.invOneAddSq = A.resolvent I ∘L A.resolvent (-I) :=
  resolvent_comm hm hp

/-- `(1 + A²)⁻¹` maps the iterated domain `D(Aⁿ)` into `D(Aⁿ⁺²)`. -/
theorem invOneAddSq_mem_domainPow_add_two {n : ℕ} {x : X} (hx : x ∈ A.domainPow n) :
    A.invOneAddSq x ∈ A.domainPow (n + 2) :=
  TauCeti.resolvent_mem_domainPow_succ hm (TauCeti.resolvent_mem_domainPow_succ hp hx)

/-- `(1 + A²)⁻¹` maps every vector into the iterated domain `D(A²)`. -/
theorem invOneAddSq_mem_domainPow_two (y : X) : A.invOneAddSq y ∈ A.domainPow 2 :=
  invOneAddSq_mem_domainPow_add_two hp hm (n := 0) (by simp)

omit hp in
/-- `(1 + A²)⁻¹` maps every vector into the domain of `A`. -/
theorem invOneAddSq_mem_domain (y : X) : A.invOneAddSq y ∈ A.domain :=
  resolvent_mem_domain hm _

/-- `(1 + A²)⁻¹` is a right inverse of `1 + A²`: `(1 + A²)⁻¹ y + A (A ((1 + A²)⁻¹ y)) = y`. -/
theorem invOneAddSq_add_apply_apply (y : X) (h₁ : A.invOneAddSq y ∈ A.domain)
    (h₂ : A ⟨A.invOneAddSq y, h₁⟩ ∈ A.domain) :
    A.invOneAddSq y + A ⟨A ⟨A.invOneAddSq y, h₁⟩, h₂⟩ = y := by
  set u : A.domain := ⟨A.resolvent I y, resolvent_mem_domain hp y⟩
  set v : A.domain := ⟨A.invOneAddSq y, h₁⟩
  have hu : A u = I • (u : X) - y := apply_resolvent hp y
  have hv : A v = -I • (v : X) - u := apply_resolvent hm (u : X)
  have hAv : (⟨A v, h₂⟩ : A.domain) = -I • v - u := Subtype.ext (by simp [hv])
  rw [hAv, map_sub, map_smul, hu, hv, smul_sub, smul_smul, neg_mul_neg, I_mul_I, neg_one_smul,
    neg_smul]
  abel

/-- `(1 + A²)⁻¹` is a left inverse of `1 + A²` on `D(A²)`: `(1 + A²)⁻¹ (x + A (A x)) = x`. -/
theorem invOneAddSq_apply_add_apply (x : A.domain) (hx : A x ∈ A.domain) :
    A.invOneAddSq (x + A ⟨A x, hx⟩) = x := by
  set w : A.domain := I • x - ⟨A x, hx⟩
  have hw : (x : X) + A ⟨A x, hx⟩ = -I • (w : X) - A w := by
    simp only [w, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
    rw [smul_sub, smul_smul, neg_mul, I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  rw [invOneAddSq_eq_resolvent_I_comp hp hm, ContinuousLinearMap.comp_apply, hw,
    resolvent_smul_sub_apply hm w]
  exact resolvent_smul_sub_apply hp x

/-- `(1 + A²)⁻¹` is injective. -/
theorem injective_invOneAddSq : Function.Injective A.invOneAddSq := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  have hd := invOneAddSq_mem_domainPow_two hp hm y
  obtain ⟨h₁, h₂⟩ := mem_domainPow_succ.mp hd
  rw [mem_domainPow_succ] at h₂
  have h0 : (⟨A.invOneAddSq y, h₁⟩ : A.domain) = 0 := Subtype.ext hy
  have h0' : (⟨A ⟨A.invOneAddSq y, h₁⟩, h₂.1⟩ : A.domain) = 0 := Subtype.ext (by simp [h0])
  rw [← invOneAddSq_add_apply_apply hp hm y h₁ h₂.1, h0', map_zero, hy, add_zero]

/-- `(1 + A²)⁻¹` commutes with `A` on its domain. -/
theorem invOneAddSq_apply_comm (x : A.domain) :
    A.invOneAddSq (A x) = A ⟨A.invOneAddSq x, invOneAddSq_mem_domain hm x⟩ := by
  rw [invOneAddSq_apply, resolvent_apply_comm hp x,
    resolvent_apply_comm hm ⟨A.resolvent I x, resolvent_mem_domain hp x⟩]
  exact congrArg A (Subtype.ext (invOneAddSq_apply (A := A) (x : X)).symm)

/-- An eigenvector of `(1 + A²)⁻¹` for a nonzero eigenvalue lies in every iterated domain
`D(Aⁿ)`: it is a multiple of its image under `(1 + A²)⁻¹`, which raises the order of regularity
by two. -/
theorem eigenspace_invOneAddSq_le_domainPow {μ : ℂ} (hμ : μ ≠ 0) (n : ℕ) :
    eigenspace (A.invOneAddSq : End ℂ X) μ ≤ A.domainPow n := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    have hKx : A.invOneAddSq x = μ • x := mem_eigenspace_iff.mp hx
    have hx' : x = μ⁻¹ • A.invOneAddSq x := by rw [hKx, inv_smul_smul₀ hμ]
    rw [hx']
    exact Submodule.smul_mem _ _
      (domainPow_succ_le A _ (invOneAddSq_mem_domainPow_add_two hp hm (ih hx)))

/-- `A` preserves each eigenspace of `(1 + A²)⁻¹`. -/
theorem apply_mem_eigenspace_invOneAddSq {μ : ℂ} (x : A.domain)
    (hx : (x : X) ∈ eigenspace (A.invOneAddSq : End ℂ X) μ) :
    A x ∈ eigenspace (A.invOneAddSq : End ℂ X) μ := by
  have hKx : A.invOneAddSq x = μ • (x : X) := mem_eigenspace_iff.mp hx
  have hK : (⟨A.invOneAddSq x, invOneAddSq_mem_domain hm x⟩ : A.domain) = μ • x :=
    Subtype.ext hKx
  rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe, invOneAddSq_apply_comm hp hm, hK,
    map_smul]

omit hm in
/-- For an operator with compact resolvent, `(1 + A²)⁻¹ = R(-i) R(i)` is a compact operator. -/
theorem HasCompactResolvent.isCompactOperator_invOneAddSq [IsTopologicalAddGroup X]
    [ContinuousConstSMul ℂ X] (h : A.HasCompactResolvent) :
    IsCompactOperator A.invOneAddSq := by
  rw [invOneAddSq_def, ContinuousLinearMap.coe_comp]
  exact (h.isCompactOperator_resolvent hp).clm_comp _

end LinearPMap
