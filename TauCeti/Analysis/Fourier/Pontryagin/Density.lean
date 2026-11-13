/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Pontryagin.Uniqueness
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Density of the evaluation characters on a compact Pontryagin dual

The Pontryagin dual `PontryaginDual G` of a discrete abelian group `G` is compact, and the
evaluation characters `χ ↦ χ g`, `g ∈ G`, separate its points and are closed under conjugation.
By the Stone–Weierstrass theorem they therefore span a dense subspace of
`C(PontryaginDual G, ℂ)`. Consequently a closed subspace of `C(PontryaginDual G, ℂ)` containing
every evaluation character is everything, and a star homomorphism out of
`C(PontryaginDual G, ℂ)` into a C⋆-algebra is determined by its values on the evaluation
characters. This is the uniqueness statement for the spectral calculus of a unitary
representation of `G`.

## Main declarations

* `PontryaginDual.dense_span_evalBoundedContinuous`: the evaluation characters span a dense
  subspace of `C(PontryaginDual G, ℂ)`.
* `PontryaginDual.mem_of_isClosed_of_forall_evalBoundedContinuous_mem`: a closed subspace
  containing every evaluation character is everything.
* `PontryaginDual.starAlgHom_ext`: star homomorphisms out of `C(PontryaginDual G, ℂ)` into a
  C⋆-algebra agreeing on the evaluation characters are equal.
-/

public section

open scoped CStarAlgebra

namespace PontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- On the compact Pontryagin dual of a discrete abelian group, the evaluation characters span a
dense subspace of the continuous functions, by the Stone–Weierstrass theorem. -/
theorem dense_span_evalBoundedContinuous :
    Dense (Submodule.span ℂ (Set.range fun g : G => (evalBoundedContinuous g).toContinuousMap) :
      Set C(PontryaginDual (Multiplicative G), ℂ)) := by
  let S := (evalPoly (G := G)).map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
  have hS : Dense (S : Set C(PontryaginDual (Multiplicative G), ℂ)) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S
        separatesPoints_evalPoly, StarSubalgebra.coe_top]
  refine hS.mono ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, rfl⟩ := (mem_evalPoly f).1 hf
  simp only [Finsupp.sum, map_sum, SetLike.mem_coe]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- A closed subspace of the continuous functions on the compact Pontryagin dual of a discrete
abelian group which contains every evaluation character is the whole space. -/
theorem mem_of_isClosed_of_forall_evalBoundedContinuous_mem
    {M : Submodule ℂ C(PontryaginDual (Multiplicative G), ℂ)}
    (hM : IsClosed (M : Set C(PontryaginDual (Multiplicative G), ℂ)))
    (h : ∀ g : G, (evalBoundedContinuous g).toContinuousMap ∈ M)
    (f : C(PontryaginDual (Multiplicative G), ℂ)) : f ∈ M := by
  have hle : closure (Submodule.span ℂ (Set.range fun g : G =>
      (evalBoundedContinuous g).toContinuousMap) : Set C(PontryaginDual (Multiplicative G), ℂ)) ⊆
      M :=
    closure_minimal (SetLike.coe_subset_coe.2 (Submodule.span_le.2 (Set.range_subset_iff.2 h))) hM
  exact hle ((dense_span_evalBoundedContinuous (G := G)).closure_eq ▸ Set.mem_univ f)

/-- A unital star homomorphism from the continuous functions on the compact Pontryagin dual of a
discrete abelian group into a C⋆-algebra is determined by its values on the evaluation
characters. -/
theorem starAlgHom_ext {A : Type*} [CStarAlgebra A]
    {φ ψ : C(PontryaginDual (Multiplicative G), ℂ) →⋆ₐ[ℂ] A}
    (h : ∀ g : G, φ (evalBoundedContinuous g).toContinuousMap =
      ψ (evalBoundedContinuous g).toContinuousMap) : φ = ψ :=
  StarAlgHom.ext <| mem_of_isClosed_of_forall_evalBoundedContinuous_mem
    (M := (StarAlgHom.equalizer φ ψ).toSubalgebra.toSubmodule)
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) h

end PontryaginDual
