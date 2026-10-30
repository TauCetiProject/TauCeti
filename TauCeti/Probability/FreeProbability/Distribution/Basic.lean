/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FreeAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Joint algebraic distributions

The joint distribution of a family in an algebra with a linear functional is the functional
on noncommutative polynomials obtained by evaluation. Equality of joint distributions is
equivalent to equality of all ordered word moments, including the empty word. It therefore
determines the expectation of every noncommutative polynomial, without commutativity,
positivity, or traciality assumptions.

The transport formulas cover algebra homomorphisms, relabeling and subfamilies, and arbitrary
noncommutative polynomial substitutions. In particular, equal joint distributions remain
equal after applying the same family of polynomials. For two functionals on the same algebra,
equality of joint distributions is equivalent to agreement on the generated subalgebra.

Normalization is separate: the value on `1` is the original functional's value on `1`.
These are algebraic distributions; no involution or analytic scalar law is introduced here.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.

The word-moment criterion uses Mathlib's `FreeAlgebra.basisFreeMonoid`.
-/

public section

namespace TauCeti

variable {R A B ι κ : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The joint algebraic distribution of `a` with respect to `φ`: evaluate a noncommutative
polynomial at `a`, then apply `φ`. Normalization and positivity are separate conditions. -/
noncomputable def jointDistribution (φ : A →ₗ[R] R) (a : ι → A) :
    FreeAlgebra R ι →ₗ[R] R :=
  φ.comp (FreeAlgebra.lift R a).toLinearMap

/-- A joint distribution is the pullback of the functional along polynomial evaluation. -/
theorem jointDistribution_def (φ : A →ₗ[R] R) (a : ι → A) :
    jointDistribution φ a = φ.comp (FreeAlgebra.lift R a).toLinearMap := (rfl)

@[simp]
theorem jointDistribution_apply (φ : A →ₗ[R] R) (a : ι → A) (p : FreeAlgebra R ι) :
    jointDistribution φ a p = φ (FreeAlgebra.lift R a p) := (rfl)

/-- Evaluating the distribution on a word gives its ordered moment. For the empty word this
is `φ 1`. -/
theorem jointDistribution_list_prod (φ : A →ₗ[R] R) (a : ι → A) (w : List ι) :
    jointDistribution φ a (w.map (FreeAlgebra.ι R)).prod = φ (w.map a).prod := by
  simp [map_list_prod, List.map_map, Function.comp_def]

/-- Evaluating the distribution on a free-monoid basis vector gives its ordered moment. -/
theorem jointDistribution_basisFreeMonoid (φ : A →ₗ[R] R) (a : ι → A)
    (w : FreeMonoid ι) :
    jointDistribution φ a (FreeAlgebra.basisFreeMonoid R ι w) =
      φ (w.toList.map a).prod := by
  rw [basisFreeMonoid_apply, jointDistribution_list_prod]

/-- A joint algebraic distribution is determined by all its word moments, including the
empty word. The two families may live in different algebras. -/
theorem jointDistribution_eq_iff {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} :
    jointDistribution φ a = jointDistribution ψ b ↔
      ∀ w : List ι, φ (w.map a).prod = ψ (w.map b).prod := by
  constructor
  · intro h w
    simpa only [jointDistribution_list_prod] using
      LinearMap.congr_fun h (w.map (FreeAlgebra.ι R)).prod
  · intro h
    apply (FreeAlgebra.basisFreeMonoid R ι).ext
    intro w
    simpa only [jointDistribution_basisFreeMonoid] using h w.toList

/-- Evaluating the formal generators recovers the original polynomial functional. -/
@[simp]
theorem jointDistribution_ι (φ : FreeAlgebra R ι →ₗ[R] R) :
    jointDistribution φ (FreeAlgebra.ι R) = φ := by
  simpa only [jointDistribution, AlgHom.coe_id, Function.id_comp, AlgHom.toLinearMap_id,
    LinearMap.comp_id] using
    congrArg (fun f : FreeAlgebra R ι →ₐ[R] FreeAlgebra R ι => φ.comp f.toLinearMap)
      (FreeAlgebra.lift_comp_ι (AlgHom.id R (FreeAlgebra R ι)))

/-- Pulling a functional back along an algebra homomorphism is equivalent to mapping the
family forward. This also gives transport along algebra equivalences. -/
theorem jointDistribution_map (φ : B →ₗ[R] R) (f : A →ₐ[R] B) (a : ι → A) :
    jointDistribution (φ.comp f.toLinearMap) a = jointDistribution φ (f ∘ a) := by
  have h : f.comp (FreeAlgebra.lift R a) = FreeAlgebra.lift R (f ∘ a) := by
    ext i
    simp
  ext p
  exact congrArg φ (AlgHom.congr_fun h p)

/-- The distribution of a polynomially substituted family is obtained by applying the same
substitution to its joint distribution. -/
theorem jointDistribution_subst (φ : A →ₗ[R] R) (a : ι → A)
    (p : κ → FreeAlgebra R ι) :
    jointDistribution φ (fun j => FreeAlgebra.lift R a (p j)) =
      jointDistribution (jointDistribution φ a) p := by
  simpa only [jointDistribution, Function.comp_def] using
    (jointDistribution_map φ (FreeAlgebra.lift R a) p).symm

/-- Relabeling, including restriction to a subfamily, is pullback by the corresponding
map of free algebras. The label map need not be injective. -/
theorem jointDistribution_comp (φ : A →ₗ[R] R) (a : ι → A) (r : κ → ι) :
    jointDistribution φ (a ∘ r) =
      jointDistribution (jointDistribution φ a) (FreeAlgebra.ι R ∘ r) := by
  simpa [Function.comp_def] using jointDistribution_subst φ a (FreeAlgebra.ι R ∘ r)

/-- Equality of joint distributions is preserved by evaluating any family of
noncommutative polynomials. -/
theorem jointDistribution_subst_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (h : jointDistribution φ a = jointDistribution ψ b)
    (p : κ → FreeAlgebra R ι) :
    jointDistribution φ (fun j => FreeAlgebra.lift R a (p j)) =
      jointDistribution ψ (fun j => FreeAlgebra.lift R b (p j)) := by
  rw [jointDistribution_subst, jointDistribution_subst, h]

/-- Equal joint distributions have equal distributions on every relabeled family,
including every subfamily. -/
theorem jointDistribution_comp_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (h : jointDistribution φ a = jointDistribution ψ b)
    (r : κ → ι) :
    jointDistribution φ (a ∘ r) = jointDistribution ψ (b ∘ r) := by
  rw [jointDistribution_comp φ a r, jointDistribution_comp ψ b r, h]

/-- A surjective relabeling loses no information about the joint distribution. -/
theorem jointDistribution_comp_eq_iff {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} {r : κ → ι} (hr : Function.Surjective r) :
    jointDistribution φ (a ∘ r) = jointDistribution ψ (b ∘ r) ↔
      jointDistribution φ a = jointDistribution ψ b := by
  classical
  refine ⟨fun h => ?_, fun h => jointDistribution_comp_eq h r⟩
  have h' := jointDistribution_comp_eq h (Function.surjInv hr)
  simpa [Function.comp_def, Function.surjInv_eq] using h'

/-- Two functionals have the same joint distribution on a family exactly when they agree
on the unital subalgebra generated by that family. -/
theorem jointDistribution_eq_iff_eqOn_adjoin {φ ψ : A →ₗ[R] R} {a : ι → A} :
    jointDistribution φ a = jointDistribution ψ a ↔
      Set.EqOn φ ψ (Algebra.adjoin R (Set.range a)) := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  constructor
  · intro h x hx
    obtain ⟨p, rfl⟩ := hx
    exact LinearMap.congr_fun h p
  · intro h
    ext p
    exact h ⟨p, rfl⟩

end TauCeti
