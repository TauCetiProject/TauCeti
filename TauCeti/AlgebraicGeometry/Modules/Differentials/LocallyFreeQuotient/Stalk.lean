/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Spec
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
import TauCeti.RingTheory.Kaehler.SpreadSurjection

/-!
# The stalk criterion for locally free quotients of the differentials, local step

Let `X` be a scheme locally of finite presentation over `Spec k` and `x` a point of `X`. A
surjective `𝒪_{X,x}`-linear map `Ω[𝒪_{X,x}⁄k] → 𝒪_{X,x}^d` spreads out to a neighbourhood of
`x`: there is an open `V ∋ x` such that `Ω_{V/k}` admits a locally free quotient of rank `d`.
This is the local half of the converse to
`HasLocallyFreeQuotientOfDifferentials.exists_surjective_stalk`: a free rank-`d` quotient of the
differentials at a stalk extends to a neighbourhood.

On an affine open `U ∋ x`, the stalk `𝒪_{X,x}` is the localization of `A = Γ(X, U)` at the prime
of `x`, so the surjection spreads out to a surjection `Ω[A_s⁄k] → A_s^d` for some `s` not in
that prime (`KaehlerDifferential.exists_notMem_away_surjective`). The basic open `D(s) ∋ x` is
affine with ring of sections `A_s`, and a surjection `Ω[B⁄k] → B^d` for the sections `B` of an
affine open `V` gives a locally free quotient on `V`
(`hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective`).

## Main declarations

* `TauCeti.AlgebraicGeometry.exists_mem_hasLocallyFreeQuotientOfDifferentials_of_surjective`: a
  surjection `Ω[𝒪_{X,x}⁄k] → 𝒪_{X,x}^d` gives a locally free quotient of rank `d` of `Ω_{V/k}`
  on an open neighbourhood `V` of `x`.

## References

* The Stacks Project, *Commutative Algebra*, Lemma 10.10.2 (Tag 0583) and Lemma 10.40.5
  (Tag 00L2).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

attribute [local instance] Scheme.algebraOfOver

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The stalk criterion, local step.** Let `X` be locally of finite presentation over `Spec k`.
A surjective `𝒪_{X,x}`-linear map `Ω[𝒪_{X,x}⁄k] → 𝒪_{X,x}^d` at a point `x` spreads out: there is
an open neighbourhood `V` of `x` such that `Ω_{V/k}` admits a locally free quotient of rank `d`. -/
theorem exists_mem_hasLocallyFreeQuotientOfDifferentials_of_surjective
    [LocallyOfFinitePresentation (X ↘ Spec (.of k))] {d : ℕ} (x : X)
    (g : Ω[X.presheaf.stalk x⁄k] →ₗ[X.presheaf.stalk x] (Fin d → X.presheaf.stalk x))
    (hg : Function.Surjective g) :
    ∃ V : X.Opens, x ∈ V ∧ HasLocallyFreeQuotientOfDifferentials k V d := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Algebra.FinitePresentation k Γ(X, U) :=
    finitePresentation_sections_of_locallyOfFinitePresentation k X ⟨U, hU⟩
  -- The stalk is the localization of `Γ(X, U)` at the prime of `x`, compatibly with `k`.
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    Scheme.isScalarTower_base_section_stalk k X ⟨x, hxU⟩
  obtain ⟨s, hs, h⟩ := KaehlerDifferential.exists_notMem_away_surjective
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x) g hg
  -- The basic open `D(s)` is affine, with sections the localization of `Γ(X, U)` at `s`.
  let V : X.affineOpens := ⟨X.basicOpen s, hU.basicOpen s⟩
  have : IsLocalization.Away s Γ(X, X.basicOpen s) := hU.isLocalization_basicOpen s
  have : IsScalarTower k Γ(X, U) Γ(X, X.basicOpen s) := .of_algebraMap_eq fun r ↦
    (Scheme.presheaf_map_algebraMap (homOfLE (X.basicOpen_le s)) r).symm
  obtain ⟨g', hg'⟩ := h Γ(X, X.basicOpen s)
  refine ⟨X.basicOpen s, ?_,
    hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective k V g' hg'⟩
  rw [Scheme.mem_basicOpen' X s ⟨x, hxU⟩]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ s).mpr hs

end

end TauCeti.AlgebraicGeometry
