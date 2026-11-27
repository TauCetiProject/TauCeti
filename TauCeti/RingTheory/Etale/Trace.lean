/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Trace.Basic
import TauCeti.Algebra.Algebra.Pi
import TauCeti.RingTheory.Etale.Discriminant
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.NormTrace.Pi
import TauCeti.RingTheory.Trace.Idempotent

/-!
# Traces on étale algebras over a field

Let `A` be an étale algebra over a field `K`, that is, a finite product of finite separable field
extensions of `K`, and let `Ω` be an algebraically closed field containing `K`. This file
describes the trace `Tr_{A/K}` through the `K`-algebra maps `A → Ω`, the geometric points of `A`,
extending Mathlib's `trace_eq_sum_embeddings` from fields to étale algebras.

* The trace is the sum over the geometric points: `Tr_{A/K} x = ∑_{φ : A → Ω} φ x` in `Ω`.
* If the partial trace `x ↦ ∑_{φ ∈ S} φ x` of a set `S` of geometric points takes values in `K`,
  then `S` is cut out by an idempotent `c` of `A`: `φ c = 1` for `φ ∈ S` and `φ c = 0` otherwise.
  The ideal `c A` is then a representation of `A` over `K` whose trace is that partial trace.

The second statement descends a representation of `A` defined over `Ω` to `K` once its trace is
`K`-valued. It constructs representations of a CM algebra with the type trace over every field
containing the reflex field.

## Main results

* `TauCeti.Algebra.Etale.algebraMap_trace_eq_finsum`: `Tr_{A/K} x = ∑_{φ : A → Ω} φ x`.
* `TauCeti.Algebra.Etale.exists_isIdempotentElem_algHom_apply_eq_indicator`: a set of geometric
  points with `K`-valued partial trace is cut out by an idempotent.
* `TauCeti.Algebra.Etale.exists_trace_eq_finsum`: a representation of `A` on some `Kⁿ` with a
  prescribed `K`-valued partial trace.
-/

public section

namespace TauCeti

namespace Algebra.Etale

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.Etale K A]
  (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]

/-- **The trace of an étale algebra is the sum over its geometric points.** For an étale algebra
`A` over a field `K` and an algebraically closed field `Ω` containing `K`,
`Tr_{A/K} x = ∑_{φ : A →ₐ[K] Ω} φ x`. This extends Mathlib's `trace_eq_sum_embeddings` from finite
separable field extensions to finite products of them. -/
theorem algebraMap_trace_eq_finsum (x : A) :
    algebraMap K Ω (Algebra.trace K A x) = ∑ᶠ φ : A →ₐ[K] Ω, φ x := by
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp ‹_›
  have := Fintype.ofFinite I
  have (i : I) : Module.Finite K (L i) := (hL i).1
  have (i : I) : Algebra.IsSeparable K (L i) := (hL i).2
  -- Transport along `A ≃ ∏ᵢ Lᵢ`, then split the geometric points along the factors.
  rw [← finsum_comp_equiv (AlgEquiv.arrowCongr e AlgEquiv.refl).symm]
  simp [← Algebra.trace_eq_of_algEquiv e, Algebra.trace_pi, AlgHom.finsum_apply_pi,
    trace_eq_sum_embeddings Ω]
  simp [finsum_eq_sum_of_fintype]

variable {Ω} in
/-- **Sets of geometric points with rational trace are cut out by idempotents.** Let `A` be an
étale algebra over a field `K` and `S` a set of `K`-algebra maps `A → Ω` to an algebraically closed
field, whose partial trace `x ↦ ∑_{φ ∈ S} φ x` takes values in `K`. Then some idempotent `c` of `A`
has `φ c = 1` for `φ ∈ S` and `φ c = 0` for `φ ∉ S`. -/
theorem exists_isIdempotentElem_algHom_apply_eq_indicator (S : Set (A →ₐ[K] Ω))
    (hS : ∀ x, ∑ᶠ φ ∈ S, φ x ∈ Set.range (algebraMap K Ω)) :
    ∃ c : A, IsIdempotentElem c ∧ ∀ φ : A →ₐ[K] Ω, φ c = S.indicator 1 φ := by
  classical
  have := Algebra.FormallyUnramified.finite_of_free K A
  have := Fintype.ofFinite (A →ₐ[K] Ω)
  -- The partial trace as a `K`-valued linear form on `A`.
  have hS' (x : A) : ∃ a, algebraMap K Ω a = ∑ᶠ φ ∈ S, φ x := hS x
  choose τ hτ using hS'
  have hfin : S.Finite := S.toFinite
  let t : A →ₗ[K] K :=
    { toFun := τ
      map_add' x y := (algebraMap K Ω).injective <| by
        simp only [map_add, hτ]
        exact finsum_mem_add_distrib hfin
      map_smul' r x := (algebraMap K Ω).injective <| by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul, hτ, Algebra.smul_def, map_mul,
          AlgHom.commutes]
        exact (mul_finsum_mem' (fun φ : A →ₐ[K] Ω ↦ φ x) _ hfin).symm }
  -- The nondegenerate trace form represents `t` as `y ↦ Tr_{A/K} (c y)`.
  have hnd := (Algebra.etale_iff_traceForm_nondegenerate K A).mp ‹_›
  obtain ⟨c, hc⟩ := (LinearMap.BilinForm.toDual _ hnd).surjective t
  have hct (y : A) : ∑ φ : A →ₐ[K] Ω, φ c * φ y = ∑ᶠ φ ∈ S, φ y := by
    have h := algebraMap_trace_eq_finsum (K := K) Ω (c * y)
    rw [finsum_eq_sum_of_fintype] at h
    simp only [map_mul] at h
    rw [← h, ← hτ, ← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, hc]
    -- `t y` is `τ y` by the definition of `t`.
    rfl
  have hind (y : A) : ∑ φ : A →ₐ[K] Ω, S.indicator 1 φ * φ y = ∑ᶠ φ ∈ S, φ y := by
    rw [finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun φ _ ↦ ?_
    by_cases hφ : φ ∈ S <;> simp [hφ]
  -- Compare the coefficients of `∑_φ φ c φ y = ∑_{φ ∈ S} φ y`, by Dedekind's independence of
  -- characters.
  have hval (φ : A →ₐ[K] Ω) : φ c = S.indicator 1 φ := by
    refine sub_eq_zero.mp (Fintype.linearIndependent_iff.mp (linearIndependent_toLinearMap K A Ω)
      (fun φ ↦ φ c - S.indicator 1 φ) (LinearMap.ext fun y ↦ ?_) φ)
    simp [LinearMap.sum_apply, sub_mul, Finset.sum_sub_distrib, hct, hind]
  -- The geometric points of the reduced algebra `A` separate its elements.
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  refine ⟨c, eq_of_forall_algHom_apply_eq (k := K) (K := Ω) fun φ ↦ ?_, hval⟩
  rw [map_mul, hval]
  by_cases hφ : φ ∈ S <;> simp [hφ]

variable {Ω} in
/-- **Representations of an étale algebra with a prescribed rational partial trace.** Let `A` be
an étale algebra over a field `K` and `S` a set of `K`-algebra maps `A → Ω` to an algebraically
closed field, whose partial trace `x ↦ ∑_{φ ∈ S} φ x` takes values in `K`. Then `A` has a
representation on some `Kⁿ` with trace `∑_{φ ∈ S} φ x`: the ideal `c A` of the idempotent `c`
cutting out `S`, whose trace is computed by `IsIdempotentElem.trace_lsmul_span_singleton`. -/
theorem exists_trace_eq_finsum (S : Set (A →ₐ[K] Ω))
    (hS : ∀ x, ∑ᶠ φ ∈ S, φ x ∈ Set.range (algebraMap K Ω)) :
    ∃ (n : ℕ) (ρ : A →ₐ[K] Module.End K (Fin n → K)),
      ∀ x, algebraMap K Ω (LinearMap.trace K (Fin n → K) (ρ x)) = ∑ᶠ φ ∈ S, φ x := by
  classical
  have := Algebra.FormallyUnramified.finite_of_free K A
  have := Fintype.ofFinite (A →ₐ[K] Ω)
  obtain ⟨c, hc, hcφ⟩ := exists_isIdempotentElem_algHom_apply_eq_indicator S hS
  let V := Ideal.span {c}
  let b := Module.finBasis K V
  refine ⟨_, (b.equivFun.conjAlgEquiv K).toAlgHom.comp (Algebra.lsmul K K V), fun x ↦ ?_⟩
  -- The trace is invariant under conjugation by `b.equivFun : V ≃ Kⁿ`.
  have htr : LinearMap.trace K _ (b.equivFun.conjAlgEquiv K (Algebra.lsmul K K V x)) =
      LinearMap.trace K V (Algebra.lsmul K K V x) :=
    LinearMap.trace_conj' _ b.equivFun
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, htr, hc.trace_lsmul_span_singleton,
    algebraMap_trace_eq_finsum Ω]
  simp [finsum_mem_def, hcφ, Set.indicator_apply]

end Algebra.Etale

end TauCeti
