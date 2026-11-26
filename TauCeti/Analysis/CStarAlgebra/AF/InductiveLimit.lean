/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AF.Basic
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Sequential
import TauCeti.Topology.Algebra.NonUnitalStarAlgebra.FiniteDimensional

/-!
# AF algebras as inductive limits

A C⋆-algebra is AF exactly when it is a sequential C⋆-inductive limit of finite-dimensional
C⋆-algebras; the connecting maps need not be injective. In one direction the images of the stages
of a limit are finite-dimensional C⋆-subalgebras, increasing and with dense union. In the other,
the stages of an AF algebra are closed, being finite-dimensional, so with the inclusions they form
a sequential colimit cocone, which identifies the algebra with the C⋆-inductive limit of its
stages.

## Main statements

* `TauCeti.CStarInductiveLimit.isAF`: the C⋆-inductive limit of a sequential directed system of
  finite-dimensional C⋆-algebras is AF.
* `TauCeti.IsSeqColimitCocone.isAF`: a C⋆-algebra carrying a sequential colimit cocone of
  finite-dimensional C⋆-algebras is AF.
* `TauCeti.isAF_iff_nonempty_starAlgEquiv_cStarInductiveLimit`: a C⋆-algebra is AF exactly when
  it is ⋆-isomorphic to the C⋆-inductive limit of a sequence of finite-dimensional C⋆-algebras.
-/

public section

universe u

open Set

namespace TauCeti

section Limit

variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)] [∀ n, FiniteDimensional ℂ (A n)]

/-- The C⋆-inductive limit of a sequential directed system of finite-dimensional C⋆-algebras is
AF: its stages are the images of the canonical maps. The connecting maps need not be
injective. -/
theorem CStarInductiveLimit.isAF {T : ∀ ⦃i j : ℕ⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
    [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
    [∀ i j (h : i ≤ j), NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
    [∀ i j (h : i ≤ j), StarHomClass (T h) (A i) (A j)] [DirectedSystem A (f · · ·)] :
    IsAF (CStarInductiveLimit A f) := by
  refine isAF_iff.2 ⟨fun n ↦ (CStarInductiveLimit.of A f n).range, fun m n h x hx ↦ ?_,
    fun _ ↦ inferInstance, ?_⟩
  · obtain ⟨a, rfl⟩ := hx
    exact ⟨f m n h a, CStarInductiveLimit.of_f h a⟩
  · simpa [NonUnitalStarAlgHom.coe_range] using CStarInductiveLimit.dense_iUnion_range_of A f

/-- A C⋆-algebra carrying a sequential colimit cocone of finite-dimensional C⋆-algebras is AF,
being ⋆-isomorphic to the C⋆-inductive limit of the cocone's system. -/
theorem IsSeqColimitCocone.isAF {C : Type*} [NonUnitalCStarAlgebra C]
    {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C} (hι : IsSeqColimitCocone α ι) :
    IsAF C :=
  ((CStarInductiveLimit.isSeqColimitCocone_of α).equiv hι).isAF_iff.1 CStarInductiveLimit.isAF

end Limit

/-- A C⋆-algebra is AF exactly when it is ⋆-isomorphic to the C⋆-inductive limit of a sequence of
finite-dimensional C⋆-algebras, with possibly noninjective connecting maps. For an AF algebra the
stages can be taken to be its finite-dimensional C⋆-subalgebras, with the inclusions as connecting
maps. -/
theorem isAF_iff_nonempty_starAlgEquiv_cStarInductiveLimit {C : Type u}
    [NonUnitalCStarAlgebra C] :
    IsAF C ↔ ∃ (A : ℕ → Type u) (_ : ∀ n, NonUnitalCStarAlgebra (A n))
      (_ : ∀ n, FiniteDimensional ℂ (A n)) (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)),
      Nonempty (C ≃⋆ₐ[ℂ] CStarInductiveLimit A (fun _ _ h ↦ seqTransHom α h)) := by
  refine ⟨fun h ↦ ?_, fun ⟨A, _, _, α, ⟨e⟩⟩ ↦ ?_⟩
  · obtain ⟨S, hmono, hfin, hdense⟩ := isAF_iff.1 h
    have (n : ℕ) : IsClosed (S n : Set C) :=
      have := hfin n
      (S n).isClosed_of_finiteDimensional
    exact ⟨fun n ↦ ↥(S n), inferInstance, hfin, _,
      ⟨(IsSeqColimitCocone.of_nonUnitalStarSubalgebra hmono hdense).equiv
        (CStarInductiveLimit.isSeqColimitCocone_of _)⟩⟩
  · exact e.symm.isAF_iff.1 CStarInductiveLimit.isAF

end TauCeti
