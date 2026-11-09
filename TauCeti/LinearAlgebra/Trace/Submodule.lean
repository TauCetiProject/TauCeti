/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Exact

/-!
# Traces on spanning and complementary invariant submodules

When two invariant subspaces span a finite-dimensional vector space, the sum of the traces
on them is the ambient trace plus the trace on their intersection. Over any commutative ring `R`,
when two finite free invariant submodules are complementary, the ambient trace is the sum of the
traces on the two summands; over an integral domain `R`, on a rank-one invariant line `R ∙ v`
(`v ≠ 0`) in a torsion-free module, the trace is the eigenvalue on `v`.
-/

public section

namespace LinearMap

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Inclusion-exclusion for traces.** If two invariant subspaces span the whole space,
the sum of their traces equals the ambient trace plus the trace on their intersection. -/
theorem trace_restrict_add_trace_restrict_eq_trace_add_trace_restrict_inf
    {A B : Submodule K V} (hAB : Codisjoint A B) (f : V →ₗ[K] V)
    (hA : ∀ x ∈ A, f x ∈ A) (hB : ∀ x ∈ B, f x ∈ B) :
    trace K A (f.restrict hA) + trace K B (f.restrict hB) =
      trace K V f + trace K (A ⊓ B : Submodule K V)
        (f.restrict fun x hx ↦ ⟨hA x hx.1, hB x hx.2⟩) := by
  let i : (A ⊓ B : Submodule K V) →ₗ[K] A × B :=
    (Submodule.inclusion inf_le_left).prod (-Submodule.inclusion inf_le_right)
  let π : A × B →ₗ[K] V := A.subtype.coprod B.subtype
  have hi : Function.Injective i := fun x y h ↦
    Subtype.ext (congrArg (fun z : A × B ↦ (z.1 : V)) h)
  have hπ : Function.Surjective π := by
    intro x
    have hx : x ∈ A ⊔ B := by rw [codisjoint_iff.mp hAB]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  have hex : Function.Exact i π := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x.1, x.1.2, ?_⟩, ?_⟩
      · have h : (x.1 : V) = -(x.2 : V) := eq_neg_of_add_eq_zero_left hx
        rw [h]
        exact B.neg_mem x.2.2
      · apply Prod.ext
        · rfl
        · exact Subtype.ext (neg_eq_of_add_eq_zero_right hx)
    · rintro ⟨x, rfl⟩
      simp [π, i]
  have h := trace_eq_add_of_exact hi hπ hex
    (f := prodMap (f.restrict hA) (f.restrict hB))
    (fN := f.restrict fun x hx ↦ ⟨hA x hx.1, hB x hx.2⟩) (fQ := f)
    (by ext x <;> simp [i, LinearMap.restrict])
    (by ext x <;> simp [π, LinearMap.restrict])
  rw [trace_prodMap'] at h
  exact h.trans (add_comm _ _)

end Field

/-- **Trace on complementary invariant submodules.** If `A` and `B` are complementary finite free
submodules preserved by `f`, then the trace of `f` is the sum of the traces of its restrictions to
`A` and `B`. -/
theorem trace_eq_trace_restrict_add_trace_restrict
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {A B : Submodule R M} [Module.Free R A] [Module.Finite R A]
    [Module.Free R B] [Module.Finite R B] (hAB : IsCompl A B) (f : M →ₗ[R] M)
    (hA : ∀ x ∈ A, f x ∈ A) (hB : ∀ x ∈ B, f x ∈ B) :
    trace R M f = trace R A (f.restrict hA) + trace R B (f.restrict hB) := by
  have h : (Submodule.prodEquivOfIsCompl A B hAB).conj
      (prodMap (f.restrict hA) (f.restrict hB)) = f := by
    refine ext fun v ↦ ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A B hAB).surjective v
    simp [LinearEquiv.conj_apply]
  exact (congrArg (trace R M) h.symm).trans ((trace_conj' _ _).trans (trace_prodMap' _ _))

/-- **Trace on a spanned invariant line.** Over an integral domain `R`, if `v ≠ 0` in a torsion-free
`R`-module `M` is an eigenvector of `f` with eigenvalue `c`, then the restriction of `f` to `R ∙ v`
has trace `c`. -/
theorem trace_restrict_span_singleton
    {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    {v : M} (hv : v ≠ 0) {f : M →ₗ[R] M} {c : R}
    (hf : f v = c • v)
    (hspan : ∀ x ∈ Submodule.span R ({v} : Set M), f x ∈ Submodule.span R ({v} : Set M) := by
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hf]
      exact (Submodule.span R {v}).smul_mem a
        ((Submodule.span R {v}).smul_mem c (Submodule.mem_span_singleton_self v))) :
    trace R (Submodule.span R ({v} : Set M)) (f.restrict hspan) = c := by
  let e : R ≃ₗ[R] Submodule.span R ({v} : Set M) := LinearEquiv.toSpanNonzeroSingleton R M v hv
  have hconj : f.restrict hspan = e.conj (c • LinearMap.id) := by
    refine ext fun x ↦ Subtype.ext ?_
    obtain ⟨a, rfl⟩ := e.surjective x
    rw [coe_restrict_apply, LinearEquiv.conj_apply, comp_apply, comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, e.symm_apply_apply]
    simp [e, hf, smul_smul, mul_comm]
  rw [hconj, trace_conj', map_smul, trace_id, Module.finrank_self, Nat.cast_one,
    smul_eq_mul, mul_one]

end LinearMap
