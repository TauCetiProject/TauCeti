/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.Topology.Sheaves.Flasque

/-!
# Flasque sheaves of modules and the cohomology of rational functions

A sheaf of modules on a scheme is flasque when its underlying abelian presheaf is, that is, when
all of its restriction maps are surjective. `TauCeti/Topology/Sheaves/Flasque.lean` proves that a
flasque abelian sheaf has no higher cohomology; this file transports that statement to the
cohomology `Hⁿ(X, M)` of `TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` and applies it to the
sheaf `𝒦_X` of rational functions on an irreducible scheme.

The sheaf `𝒦_X` is constant with value the function field on nonempty open subsets and zero on
the empty one, so it is flasque. Consequently, for every short exact sequence
`0 ⟶ M ⟶ 𝒦_X ⟶ Q ⟶ 0` — for instance `M = 𝒪_X(D)` with `Q = 𝒦_X / 𝒪_X(D)` the sheaf of
principal parts — the long exact sequence collapses:

* `H¹(X, M)` is the cokernel of `H⁰(X, 𝒦_X) ⟶ H⁰(X, Q)`;
* `Hⁿ⁺²(X, M) ≅ Hⁿ⁺¹(X, Q)` for every `n`.

This is the principal-parts description of the cohomology of a divisorial sheaf on an integral
curve: vanishing of `H²(X, 𝒪_X(D))` reduces to vanishing of `H¹` of the sheaf of principal parts,
and `H¹(X, 𝒪_X(D))` is the space of principal parts modulo those of global rational functions,
which is where the dimension counts behind Riemann–Roch take place.

## Main declarations

* `Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque` and
  `Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque`: a flasque sheaf of modules has
  vanishing cohomology in every positive degree, over `X` and over every open subset;
* `Scheme.subsingleton_cohomology_rationalFunctions_succ`: the flasqueness of `𝒦_X` from
  `Scheme.isFlasque_rationalFunctions` gives `Hⁿ⁺¹(X, 𝒦_X) = 0`;
* for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₂` flasque:
  `Scheme.Modules.cohomologyδ_surjective_of_isFlasque`, the connecting map
  `Hⁿ(X, M₃) ⟶ Hⁿ⁺¹(X, M₁)` is surjective, and
  `Scheme.Modules.cohomologyδ_injective_of_isFlasque`, it is injective in positive degrees;
  `Scheme.Modules.cohomologySuccLinearEquivOfIsFlasque` packages the resulting isomorphism
  `Hⁿ⁺¹(X, M₃) ≃ₗ Hⁿ⁺²(X, M₁)` over the base ring, and
  `Scheme.Modules.cohomologyOneLinearEquivOfIsFlasque` identifies `H¹(X, M₁)` with the
  cokernel of `H⁰(X, M₂) ⟶ H⁰(X, M₃)`.

No formalization is vendored. The acyclicity of flasque abelian sheaves is
`TauCeti.Topology.subsingleton_H_succ_of_isFlasque`, and flasqueness is Mathlib's
`TopCat.Presheaf.IsFlasque`.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Exercise 1.16(a) (a constant sheaf on an irreducible
  space is flasque) and III, Proposition 2.5 (flasque sheaves are acyclic).
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5 (the cohomology of `𝒪_X(D)`
  on a curve through principal parts).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- A flasque sheaf of modules has vanishing cohomology over every open subset in every positive
degree. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
    (M : X.Modules) [M.presheaf.IsFlasque] (n : ℕ) (U : X.Opens) :
    Subsingleton (cohomologyOn M (n + 1) U) :=
  haveI : TopCat.Presheaf.IsFlasque ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj :=
    ‹M.presheaf.IsFlasque›
  TauCeti.Topology.subsingleton_H'_succ_of_isFlasque (X := X.toTopCat)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n U

/-- A flasque sheaf of modules has vanishing cohomology in every positive degree. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque
    (M : X.Modules) [M.presheaf.IsFlasque] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) :=
  haveI : TopCat.Presheaf.IsFlasque ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj :=
    ‹M.presheaf.IsFlasque›
  TauCeti.Topology.subsingleton_H_succ_of_isFlasque (X := X.toTopCat)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

section ShortExact

variable {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₂.presheaf.IsFlasque]

include hS

/-- If the middle term of a short exact sequence of sheaves of modules is flasque, then every
connecting map `Hⁿ⁰(X, M₃) ⟶ Hⁿ¹(X, M₁)` is surjective. -/
theorem cohomologyδ_surjective_of_isFlasque (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Surjective (cohomologyδ hS n₀ n₁ h) := by
  subst h
  intro x
  exact (exact_cohomologyδ_cohomologyMap hS n₀ (n₀ + 1) rfl x).mp
    (Subsingleton.elim _ _)

/-- If the middle term of a short exact sequence of sheaves of modules is flasque, then the
connecting map `Hⁿ⁺¹(X, M₃) ⟶ Hⁿ⁺²(X, M₁)` is injective. -/
theorem cohomologyδ_injective_of_isFlasque (n : ℕ) :
    Function.Injective (cohomologyδ hS (n + 1) (n + 2) rfl) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_cohomologyMap_cohomologyδ hS (n + 1) (n + 2) rfl x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

end ShortExact

section Base

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
  {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₂.presheaf.IsFlasque]

/-- If the middle term of a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules
on a scheme over `R` is flasque, the connecting map is an `R`-linear isomorphism
`Hⁿ⁺¹(X, M₃) ≃ Hⁿ⁺²(X, M₁)`. -/
def cohomologySuccLinearEquivOfIsFlasque (n : ℕ) :
    Cohomology S.X₃ (n + 1) ≃ₗ[R] Cohomology S.X₁ (n + 2) :=
  LinearEquiv.ofBijective (cohomologyδBaseLinear R X hS (n + 1) (n + 2) rfl) <| by
    constructor
    · intro x y hxy
      apply cohomologyδ_injective_of_isFlasque hS n
      simpa only [cohomologyδBaseLinear_apply] using hxy
    · intro y
      obtain ⟨x, hx⟩ := cohomologyδ_surjective_of_isFlasque hS (n + 1) (n + 2) rfl y
      exact ⟨x, by simpa only [cohomologyδBaseLinear_apply] using hx⟩

@[simp]
lemma cohomologySuccLinearEquivOfIsFlasque_apply (n : ℕ) (x : Cohomology S.X₃ (n + 1)) :
    cohomologySuccLinearEquivOfIsFlasque R hS n x = cohomologyδ hS (n + 1) (n + 2) rfl x := by
  exact (LinearEquiv.ofBijective_apply _ x).trans
    (cohomologyδBaseLinear_apply R X hS _ _ _ x)

/-- If the middle term of a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules
on a scheme over `R` is flasque, the connecting map identifies `H¹(X, M₁)` with the cokernel of
`H⁰(X, M₂) ⟶ H⁰(X, M₃)`, as `R`-modules. -/
def cohomologyOneLinearEquivOfIsFlasque :
    (Cohomology S.X₃ 0 ⧸ LinearMap.range (Scheme.Modules.cohomologyMapBaseLinear R X S.g 0)) ≃ₗ[R]
      Cohomology S.X₁ 1 :=
  (Submodule.quotEquivOfEq _ _ (by
      ext x
      have e (y : Cohomology S.X₂ 0) :
          Scheme.Modules.cohomologyMapBaseLinear R X S.g 0 y = cohomologyMap S.g 0 y := by
        rw [Scheme.Modules.cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
        rfl
      rw [LinearMap.mem_ker, LinearMap.mem_range, cohomologyδBaseLinear_apply]
      simp only [e]
      exact (exact_cohomologyMap_cohomologyδ hS 0 1 rfl x).symm)).trans
    ((cohomologyδBaseLinear R X hS 0 1 rfl).quotKerEquivOfSurjective (by
      intro y
      obtain ⟨x, hx⟩ := cohomologyδ_surjective_of_isFlasque hS 0 1 rfl y
      exact ⟨x, by simpa only [cohomologyδBaseLinear_apply] using hx⟩))

@[simp]
lemma cohomologyOneLinearEquivOfIsFlasque_mk (x : Cohomology S.X₃ 0) :
    cohomologyOneLinearEquivOfIsFlasque R hS (Submodule.Quotient.mk x) =
      cohomologyδ hS 0 1 rfl x := by
  rw [cohomologyOneLinearEquivOfIsFlasque, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x).trans
    (cohomologyδBaseLinear_apply R X hS _ _ _ x)

end Base

end Scheme.Modules

namespace Scheme

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- The sheaf `𝒦_X` of rational functions on an irreducible scheme has no higher cohomology. -/
theorem subsingleton_cohomology_rationalFunctions_succ (n : ℕ) :
    Subsingleton (Modules.Cohomology (rationalFunctions X) (n + 1)) :=
  inferInstance

end Scheme

end

end AlgebraicGeometry

end TauCeti
