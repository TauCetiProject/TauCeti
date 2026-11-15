/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.UnitEquation.Nondegenerate
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Specializing finite families of unit-equation solutions

A finite family of nondegenerate solutions over a finite-type domain can be specialized
to an algebraically closed extension of its ground field, without identifying distinct
solutions or creating vanishing subsums. Extra finite data can be kept distinct at the
same time. Coordinates represented by units remain units under the specialization.

The finite-data argument uses one specialization that distinguishes all coordinate values
and all subsums, together with zero. Distinguishing individual coordinates from zero alone
would not suffice to distinguish solutions.

These results supply the specialization step in transporting uniform unit-equation bounds
between characteristic-zero fields. They assert no finiteness theorem for unit equations.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §3,
  Lemmas 3.1–3.2.
-/

public section

open Finset

namespace TauCeti

variable {k A K ι σ : Type*} [Field k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] [IsAlgClosed K]
  [Fintype ι] [Finite σ]

/-- A finite family of distinct nondegenerate solutions over a finite-type domain has a
specialization to any algebraically closed extension of the ground field that preserves
distinctness and nondegeneracy. The same specialization is injective on any prescribed
additional finite subset of the domain. No characteristic assumption is needed. -/
theorem exists_specialization_nondegenerate_solutions (a : ι → A) (x : σ → ι → A)
    (hx : Function.Injective x) (h : ∀ j, IsNondegenerateSolution a (x j)) (t : Finset A) :
    ∃ f : A →ₐ[k] K, Set.InjOn f t ∧
      Function.Injective (fun j ↦ f ∘ x j) ∧
      ∀ j, IsNondegenerateSolution (f ∘ a) (f ∘ x j) := by
  classical
  let := Fintype.ofFinite σ
  let c : Finset A := univ.image fun p : σ × ι ↦ x p.1 p.2
  let b : Finset A := univ.image fun p : σ × Finset ι ↦ ∑ i ∈ p.2, a i * x p.1 i
  obtain ⟨f, hf⟩ := (t ∪ c ∪ b).exists_algHom_injOn (k := k) (K := K)
  have hc (j : σ) (i : ι) : x j i ∈ t ∪ c ∪ b := by
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_univ (j, i))))
  have hb (j : σ) (I : Finset ι) : ∑ i ∈ I, a i * x j i ∈ t ∪ c ∪ b :=
    mem_union_right _ (mem_image_of_mem _ (mem_univ (j, I)))
  refine ⟨f, hf.mono (by intro z hz; simp [hz]), ?_, fun j ↦ ?_⟩
  · intro j l hjl
    apply hx
    exact funext fun i ↦ hf (hc j i) (hc l i) (congrFun hjl i)
  · exact (h j).map f.toRingHom (hf.mono (by rintro z ⟨I, rfl⟩; exact hb j I))

end TauCeti
