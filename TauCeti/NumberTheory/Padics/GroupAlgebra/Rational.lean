/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Module.LinearMap.Finite
import TauCeti.Algebra.Module.Projective.LinearMap
import TauCeti.Algebra.Module.Projective.Reduction
import TauCeti.Algebra.Module.Projective.Trans
import TauCeti.LinearAlgebra.Dimension.Localization
import TauCeti.NumberTheory.Padics.GroupAlgebra.Projective
import TauCeti.RingTheory.Jacobson.Semiprimary
import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# Projective `ℤ_p[G]`-modules with isomorphic rationalizations

Let `G` be a finite group. Swan's theorem (NSW (5.6.10)(ii)) says that a finitely generated
projective `ℤ_p[G]`-module `P` is determined up to isomorphism by its rationalization
`P ⊗ ℚ_p`. This file proves the comparison of hom counts that relates rationalizations to
reductions modulo `p`, and deduces Swan's theorem when `p` does not divide `|G|`.

For lattices `M` and `N` (finitely generated `ℤ_p[G]`-modules, torsion-free over `ℤ_p`) with
isomorphic rationalizations, clearing denominators gives injective `ℤ_p[G]`-linear maps `M → N`
and `N → M`. Hence the free `ℤ_p`-modules `Hom(P, M)` and `Hom(P, N)` have the same rank for
every finitely generated `P`. When `P` is projective, the maps from `P` into `M ⧸ p • M` are the
reductions modulo `p` of `Hom(P, M)`. Therefore `P` has as many maps into `M ⧸ p • M` as into
`N ⧸ p • N`: the number of maps from a projective module into the reduction of a lattice depends
only on the rationalization of the lattice (compare Serre's identity `⟨P, d(E)⟩ = ⟨P ⊗ ℚ_p, E⟩`
between the Cartan and decomposition maps, which also computes this number).

When `p ∤ |G|`, the ideal `(p)` is the Jacobson radical of `ℤ_p[G]`, so the reductions of `M` and
`N` are semisimple. Comparing the numbers of maps between these finite semisimple modules
identifies them, and projective covers lift the identification to `M ≃ N`. For general `G` the
reduction `M ⧸ p • M` need not be semisimple, and this last step does not apply.

## Main results

* `TauCeti.natCard_linearMap_quotient_eq_of_tensorRat`: a finitely generated projective
  `ℤ_p[G]`-module has equally many maps into the reductions modulo `p` of two lattices with
  isomorphic rationalizations.
* `TauCeti.nonempty_linearEquiv_of_projective_of_tensorRat_of_not_dvd`: for `p ∤ |G|`, finitely
  generated projective `ℤ_p[G]`-modules with isomorphic rationalizations are isomorphic.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10).
* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §15–16 (the `cde` triangle).
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

public section

namespace TauCeti

open scoped TensorProduct Pointwise

universe u v w x

section Lattice

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Monoid G] [Finite G]

local notation "A" => MonoidAlgebra ℤ_[p] G

/-- **Maps from a projective module into reductions of rationally isomorphic lattices.** Let `P`
be a finitely generated projective `ℤ_p[G]`-module and `M`, `N` finitely generated
`ℤ_p[G]`-modules, torsion-free over `ℤ_p`, with `ℤ_p[G]`-isomorphic rationalizations
`M ⊗ ℚ_p ≃ N ⊗ ℚ_p`. Then there are as many `ℤ_p[G]`-linear maps from `P` to `M ⧸ p • M` as to
`N ⧸ p • N`.

The rational isomorphism gives injective maps `M → N` and `N → M`, so the free `ℤ_p`-modules
`Hom(P, M)` and `Hom(P, N)` have the same rank; the maps from `P` into a reduction are the
reductions modulo `p` of these modules. -/
theorem natCard_linearMap_quotient_eq_of_tensorRat (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (M : Type w) [AddCommGroup M] [Module ℤ_[p] M] [Module A M] [IsScalarTower ℤ_[p] A M]
    [Module.Finite A M] [Module.IsTorsionFree ℤ_[p] M]
    (N : Type x) [AddCommGroup N] [Module ℤ_[p] N] [Module A N] [IsScalarTower ℤ_[p] A N]
    [Module.Finite A N] [Module.IsTorsionFree ℤ_[p] N]
    (h : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[A] (N ⊗[ℤ_[p]] ℚ_[p]))) :
    Nat.card (P →ₗ[A] M ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A M)) =
      Nat.card (P →ₗ[A] N ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A N)) := by
  obtain ⟨e⟩ := h
  obtain ⟨f, hf⟩ := IsFractionRing.exists_injective_linearMap_of_injective ℚ_[p] e.toLinearMap
    e.injective
  obtain ⟨g, hg⟩ := IsFractionRing.exists_injective_linearMap_of_injective ℚ_[p]
    e.symm.toLinearMap e.symm.injective
  -- `Hom(P, M)` and `Hom(P, N)` are free of finite rank over `ℤ_p` and embed in each other.
  have : Module.Finite ℤ_[p] M := .trans A M
  have : Module.Finite ℤ_[p] N := .trans A N
  have : Module.Finite ℤ_[p] (P →ₗ[A] M) := .linearMap_of_isNoetherian
  have : Module.Finite ℤ_[p] (P →ₗ[A] N) := .linearMap_of_isNoetherian
  have hfP : Function.Injective (LinearMap.compRight (M := P) ℤ_[p] f) := fun a b hab ↦
    LinearMap.ext fun x ↦ hf (LinearMap.congr_fun hab x)
  have hgP : Function.Injective (LinearMap.compRight (M := P) ℤ_[p] g) := fun a b hab ↦
    LinearMap.ext fun x ↦ hg (LinearMap.congr_fun hab x)
  obtain ⟨E⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq <|
    (LinearMap.finrank_le_finrank_of_injective hfP).antisymm
      (LinearMap.finrank_le_finrank_of_injective hgP)
  -- The maps from `P` into a reduction are the reductions of the maps into the lattice.
  have hp : IsRegular (p : ℤ_[p]) := isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Fact.out : p.Prime).ne_zero)
  have hcast : (p : A) = algebraMap ℤ_[p] A p := (map_natCast _ p).symm
  rw [hcast, ← Nat.card_congr (quotientSMulTopLinearMapEquiv P hp.isSMulRegular).toEquiv,
    ← Nat.card_congr (quotientSMulTopLinearMapEquiv P hp.isSMulRegular).toEquiv]
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ E ?_).toEquiv
  rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range]

end Lattice

section Coprime

variable (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G]

local notation "A" => MonoidAlgebra ℤ_[p] G

/-- **Projective `ℤ_p[G]`-modules are detected rationally when `p ∤ |G|`** (Swan's theorem
NSW (5.6.10)(ii) for a finite group of order prime to `p`). Two finitely generated projective
`ℤ_p[G]`-modules with `ℤ_p[G]`-isomorphic rationalizations are isomorphic.

The reductions `M ⧸ p • M` and `N ⧸ p • N` are semisimple, because `p` generates the Jacobson
radical of `ℤ_p[G]`, and by `TauCeti.natCard_linearMap_quotient_eq_of_tensorRat` there are as many
maps from `M` (or from `N`) into either reduction. Finite semisimple modules with these counts are
isomorphic, and the isomorphism of reductions lifts to `M ≃ N` because `M` and `N` are projective.
-/
theorem nonempty_linearEquiv_of_projective_of_tensorRat_of_not_dvd (hG : ¬p ∣ Nat.card G)
    (M : Type v) (N : Type w) [AddCommGroup M] [Module ℤ_[p] M] [Module A M]
    [IsScalarTower ℤ_[p] A M] [Module.Finite A M] [Module.Projective A M]
    [AddCommGroup N] [Module ℤ_[p] N] [Module A N] [IsScalarTower ℤ_[p] A N]
    [Module.Finite A N] [Module.Projective A N]
    (h : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[A] (N ⊗[ℤ_[p]] ℚ_[p]))) :
    Nonempty (M ≃ₗ[A] N) := by
  -- Projective `ℤ_p[G]`-modules are projective, hence torsion-free, over `ℤ_p`.
  have : Module.Projective ℤ_[p] M := .trans (S := A)
  have : Module.Projective ℤ_[p] N := .trans (S := A)
  -- Work with the radical quotients, which are finite and semisimple; the radical is `(p)`.
  have hJ := jacobson_padicInt_monoidAlgebra_eq_span_p p hG
  have : IsArtinianRing (A ⧸ Ring.jacobson A) := isArtinian_of_finite
  have : IsSemisimpleRing (A ⧸ Ring.jacobson A) :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson A)
  have := isSemisimpleModule_quotient_smul_top A (Ring.jacobson A) M
  have := isSemisimpleModule_quotient_smul_top A (Ring.jacobson A) N
  have := finite_quotient_jacobson_smul_top (R := A) M
  have := finite_quotient_jacobson_smul_top (R := A) N
  refine (Ring.jacobson A).nonempty_linearEquiv_of_quotient_smul_top M N le_rfl
    (IsSemisimpleModule.nonempty_linearEquiv_of_natCard_linearMap_mul_eq _ _ ?_)
  -- Maps out of a radical quotient are maps out of the module itself.
  simp only [Nat.card_congr (linearMapQuotientJacobsonEquiv M _).toEquiv,
    Nat.card_congr (linearMapQuotientJacobsonEquiv N _).toEquiv]
  rw [hJ, natCard_linearMap_quotient_eq_of_tensorRat M M N h,
    natCard_linearMap_quotient_eq_of_tensorRat N M N h, mul_comm]

end Coprime

end TauCeti
