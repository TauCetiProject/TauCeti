/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.RepresentationTheory.Continuous.KFinite
import Mathlib.LinearAlgebra.StdBasis

/-!
# `K`-finite vectors: checks

Checks for `ContRepresentation.IsKFinite`.

* Every vector of a finite-dimensional representation is `K`-finite, and the zero vector always
  is.
* In the trivial representation every orbit is a point, so every vector is `K`-finite, even in an
  infinite-dimensional space; the trivial subgroup likewise makes every vector `K`-finite.
* The predicate needs no compactness to state, but without compactness it can fail: in the left
  regular representation of the infinite cyclic group on all functions `ℤ → ℂ`, the translates of
  the point mass at the identity are the point masses, which are linearly independent, so the
  point mass is not `K`-finite for `K = ⊤`.

## Main declarations

* `TauCeti.KFiniteChecks.exists_not_isKFinite_top`: some continuous representation of the infinite
  cyclic group has a vector that is not `K`-finite for `K = ⊤`. The witness, the left regular
  representation `funLeftRegular` on `ℤ → ℂ`, and its two lemmas are private to this file: they
  are test fixtures, not API.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), §4.1, pp. 20–22.
-/

public noncomputable section

namespace TauCeti.KFiniteChecks

open ContRepresentation

/-- Every vector of a finite-dimensional continuous representation is `K`-finite. -/
example (π : ContRepresentation ℂ (Multiplicative ℤ) (Fin 2 → ℂ)) (K : Subgroup (Multiplicative ℤ))
    (v : Fin 2 → ℂ) : π.IsKFinite K v :=
  Representation.IsGFinite.of_finiteDimensional v

/-- The zero vector is `K`-finite. -/
example {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (π : ContRepresentation ℂ G E) (K : Subgroup G) :
    π.IsKFinite K 0 :=
  Representation.IsGFinite.zero

/-- In the trivial representation, even on an infinite-dimensional space, every vector is
`K`-finite: its orbit is the single point `v`. -/
example {G : Type*} [Group G] (K : Subgroup G) (v : ℕ → ℂ) :
    (trivial ℂ G (ℕ → ℂ)).IsKFinite K v :=
  Representation.IsGFinite.of_mem (W := Submodule.span ℂ {v})
    (fun _ _ hw => by simpa [toMonoidHom_apply, restrict_apply, trivial_apply] using hw)
    (Submodule.mem_span_singleton_self v)

/-- For the trivial subgroup every vector is `K`-finite: its orbit is the single point `v`. -/
example {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (π : ContRepresentation ℂ G E) (v : E) : π.IsKFinite ⊥ v :=
  Representation.IsGFinite.of_mem (W := Submodule.span ℂ {v})
    (fun x _ hw => by rw [Subsingleton.elim x 1, map_one]; exact hw)
    (Submodule.mem_span_singleton_self v)

variable (G k : Type*) [Group G] [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- The left regular representation `(g • f)(x) = f(g⁻¹ x)` of a group `G` on all functions
`G → k`, with the product topology. -/
private def funLeftRegular : ContRepresentation k G (G → k) :=
  .ofMonoidHom
    { toFun g := ContinuousLinearMap.pi fun x => ContinuousLinearMap.proj (g⁻¹ * x)
      map_one' := by ext; simp
      map_mul' g h := by ext; simp [mul_assoc] }

variable {G k}

/-- The left regular representation evaluates functions at translated points. -/
private theorem funLeftRegular_apply (g : G) (f : G → k) (x : G) :
    funLeftRegular G k g f x = f (g⁻¹ * x) :=
  (rfl)

/-- The left regular representation carries the point mass at the identity to the point mass at
`g`. -/
private theorem funLeftRegular_single_one [DecidableEq G] (g : G) :
    funLeftRegular G k g (Pi.single 1 1) = Pi.single g 1 := by
  ext x
  rw [funLeftRegular_apply]
  by_cases hx : x = g
  · simp [hx]
  · rw [Pi.single_eq_of_ne (by rwa [ne_eq, inv_mul_eq_one, eq_comm]),
      Pi.single_eq_of_ne hx]

/-- **Without compactness, `K`-finiteness can fail.** In the left regular representation of the
infinite cyclic group on `ℤ → ℂ`, the translates of the point mass at the identity are linearly
independent, so the point mass is not `K`-finite for `K = ⊤`. -/
theorem exists_not_isKFinite_top :
    ∃ π : ContRepresentation ℂ (Multiplicative ℤ) (Multiplicative ℤ → ℂ),
      ¬ π.IsKFinite ⊤ (Pi.single 1 1) := by
  refine ⟨funLeftRegular (Multiplicative ℤ) ℂ, fun h => ?_⟩
  rw [isKFinite_iff] at h
  have hli : LinearIndependent ℂ fun x : (⊤ : Subgroup (Multiplicative ℤ)) =>
      funLeftRegular (Multiplicative ℤ) ℂ x (Pi.single 1 1) := by
    simpa only [funLeftRegular_single_one, Function.comp_def] using
      (Pi.linearIndependent_single_one (Multiplicative ℤ) ℂ).comp _ Subtype.val_injective
  have := (linearIndependent_span hli).finite
  exact not_finite (⊤ : Subgroup (Multiplicative ℤ))

end TauCeti.KFiniteChecks
