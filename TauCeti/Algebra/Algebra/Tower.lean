/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Algebra towers: restriction of scalars and reversing a tower

Restricting the scalars of an `S`-algebra homomorphism along `R → S` (`AlgHom.restrictScalars`)
commutes with composition. Mathlib records injectivity of `AlgHom.restrictScalars` and its
interaction with the underlying ring and linear maps, but not this composition law, which is what a
rewrite needs when a composite homomorphism is restricted and then fed to a construction that is
functorial in `R`-algebra homomorphisms.

When `algebraMap R S` has a right inverse `algebraMap S R`, for instance when it is bijective, a
tower `R → S → M` can be reversed to a tower `S → R → M`, so that invariants of `M` relative to
two isomorphic base rings can be compared through tower formulas in both directions.

An `R`-algebra structure on an `S`-algebra `A` is determined by the scalar tower condition: every
`R`-algebra structure with `IsScalarTower R S A` is the one obtained by restricting scalars along
`R → S`. This identifies a restricted-scalars structure, such as the real algebra structure on
operators over an `RCLike` field, with the structure an instance provides in a concrete case.

## Main results

* `AlgHom.restrictScalars_comp`: `(f.comp g).restrictScalars R = (f.restrictScalars R).comp
  (g.restrictScalars R)`.
* `IsScalarTower.of_algebraMap_rightInverse`: a tower `R → S → M` gives a tower `S → R → M` when
  `algebraMap S R` is a right inverse of `algebraMap R S`.
* `Algebra.restrictScalars_eq`: an `R`-algebra structure on `A` compatible with the `S`-algebra
  structure is `Algebra.restrictScalars R S A`.
* `AlgEquiv.toRingEquiv_algebraMap_of_tower`: an `S`-algebra isomorphism fixes the image of `R`,
  stated as a compatibility of the underlying ring isomorphism along `RingEquiv.refl R`.
* `AlgHom.isScalarTower_compHom`: restricting a module action along an `R`-algebra homomorphism
  preserves the scalar tower with `R`.
* `IsScalarTower.linearMap_eq_restrictScalars_comp`: in a tower `R → S → A`, the structure map
  `R → A` is the composite of `R → S` and `S → A` as `R`-linear maps.
* `Submodule.annihilator_restrictScalars_span`: extending an `A`-submodule `N` by an `A`-algebra
  `R` preserves its `A`-annihilator.
* `Module.IsTorsionBySet.span`: if `s ⊆ A` annihilates `N`, it also annihilates the `R`-span of
  `N`.
-/

public section

variable {R S A B C : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
  [Semiring C] [Algebra R S] [Algebra S A] [Algebra S B] [Algebra S C] [Algebra R A] [Algebra R B]
  [Algebra R C] [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]

/-- Restricting scalars of a composite algebra homomorphism gives the composite of the restricted
algebra homomorphisms. -/
@[simp]
theorem AlgHom.restrictScalars_comp (f : B →ₐ[S] C) (g : A →ₐ[S] B) :
    (f.comp g).restrictScalars R = (f.restrictScalars R).comp (g.restrictScalars R) :=
  rfl

/-- A tower `R → S → M` gives a tower `S → R → M` when `algebraMap S R` is a right inverse of
`algebraMap R S`. Here `M` is any type with an action of `S` and a scalar multiplication by `R`,
for instance an `S`-algebra or an `S`-module; the tower makes `R` act through `algebraMap R S`. -/
theorem IsScalarTower.of_algebraMap_rightInverse {M : Type*} [SMul R M] [MulAction S M]
    [IsScalarTower R S M] [Algebra S R]
    (h : Function.RightInverse (algebraMap S R) (algebraMap R S)) : IsScalarTower S R M :=
  ⟨fun s r m ↦ by
    rw [← algebraMap_smul S (s • r) m, ← algebraMap_smul S r m, Algebra.smul_def, map_mul, h s,
      mul_smul]⟩

/-- An `R`-algebra structure on the `S`-algebra `A` forming a scalar tower `R → S → A` is the one
obtained by restricting scalars along `R → S`. -/
theorem Algebra.restrictScalars_eq : Algebra.restrictScalars R S A = ‹Algebra R A› :=
  Algebra.algebra_ext _ _ fun r ↦ (IsScalarTower.algebraMap_apply R S A r).symm

/-- **An isomorphism of `S`-algebras fixes the constants** of a scalar tower `R → S`, in the form
`τ (algebraMap R A c) = algebraMap R B (σ c)` with `τ = e.toRingEquiv` and `σ = RingEquiv.refl R`.
This is the compatibility hypothesis of semilinear transports such as
`TauCeti.Place.equivOfRingEquiv`, which `AlgEquiv.commutes` matches only up to unfolding. -/
theorem AlgEquiv.toRingEquiv_algebraMap_of_tower (e : A ≃ₐ[S] B) (c : R) :
    e.toRingEquiv (algebraMap R A c) = algebraMap R B (RingEquiv.refl R c) :=
  (e.restrictScalars R).commutes c

/-- Restricting a module action along an `R`-algebra homomorphism preserves the scalar tower with
`R`. -/
theorem AlgHom.isScalarTower_compHom {R A B M : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [AddCommMonoid M] [Module R M] [Module B M] [IsScalarTower R B M]
    (f : A →ₐ[R] B) :
    let : Module A M := Module.compHom M f.toRingHom
    IsScalarTower R A M := by
  let : Module A M := Module.compHom M f.toRingHom
  exact IsScalarTower.of_algebraMap_smul fun r m ↦ by
    simp [MulAction.compHom_smul_def, algebraMap_smul]

variable (R S A) in
/-- In a tower `R → S → A`, the structure map `R → A` is the composite of `R → S` and `S → A`, as
`R`-linear maps. -/
theorem IsScalarTower.linearMap_eq_restrictScalars_comp :
    Algebra.linearMap R A = (Algebra.linearMap S A).restrictScalars R ∘ₗ Algebra.linearMap R S := by
  ext
  simp

/-- Extending an `A`-submodule `N` to its `R`-span along an `A`-algebra `R` preserves its
`A`-annihilator. -/
@[simp]
theorem Submodule.annihilator_restrictScalars_span {A R M : Type*} [CommSemiring A] [Semiring R]
    [Algebra A R] [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower A R M]
    (N : Submodule A M) :
    ((Submodule.span R (N : Set M)).restrictScalars A).annihilator = N.annihilator := by
  refine le_antisymm (Submodule.annihilator_mono fun x hx ↦ Submodule.subset_span hx) ?_
  intro a ha
  rw [Submodule.mem_annihilator]
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_annihilator.mp ha y hy
  | zero => exact smul_zero a
  | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
  | smul r y _ hy =>
    rw [← algebraMap_smul R a (r • y), smul_smul, Algebra.commutes, ← smul_smul,
      algebraMap_smul, hy, smul_zero]

/-- If a set `s ⊆ A` annihilates an `A`-submodule `N`, then it also annihilates the `R`-span of
`N` in any scalar tower `A → R → M`. -/
theorem Module.IsTorsionBySet.span {A R M : Type*} [CommSemiring A] [Semiring R] [Algebra A R]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower A R M]
    (N : Submodule A M) {s : Set A} (hs : Module.IsTorsionBySet A N s) :
    Module.IsTorsionBySet A (Submodule.span R (N : Set M)) s := by
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hs ⊢
  intro a ha
  have ha' : a ∈ ((Submodule.span R (N : Set M)).restrictScalars A).annihilator := by
    rw [Submodule.annihilator_restrictScalars_span]
    exact hs ha
  rw [SetLike.mem_coe, Module.mem_annihilator]
  rintro ⟨x, hx⟩
  exact Subtype.ext (Submodule.mem_annihilator.mp ha' x hx)
