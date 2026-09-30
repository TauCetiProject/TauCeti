/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-!
# Domains with holomorphic square roots

A set `U ⊆ ℂ` *has holomorphic square roots* (`TauCeti.HasHolomorphicSquareRoots U`) if every
function holomorphic and nowhere zero on `U` is the square of a function holomorphic on `U`.

Beyond connectedness, this is the only consequence of simple connectivity that the proof of the
Riemann mapping theorem uses: the Koebe square-root trick takes a square root of `z - a` to inject
a proper domain into the disc, and a square root of a disc automorphism to beat a map that is not
onto. Isolating it as a hypothesis lets that proof run on every domain with the property, and so
shows that such a domain is conformally a disc, hence simply connected
(`TauCeti.HasHolomorphicSquareRoots.isSimplyConnected`, in
`Conformal/RiemannMapping/Existence.lean`). For an open connected set the two conditions are
therefore equivalent. In Rudin's list of characterisations of simply connected plane domains, this
file gives (b) ⇒ (i) (`IsSimplyConnected.hasHolomorphicSquareRoots`); the converse (i) ⇒ (b) is
`TauCeti.HasHolomorphicSquareRoots.isSimplyConnected`. A property that is easier to verify from the
geometry of the complement — for example vanishing of the winding numbers of cycles in `U` about
points outside `U`, via the homology form of Cauchy's theorem — thereby becomes a proof of simple
connectivity.

## Main definitions

* `TauCeti.HasHolomorphicSquareRoots` — nowhere-zero holomorphic functions have holomorphic square
  roots.

## Main results

* `IsSimplyConnected.hasHolomorphicSquareRoots` — a simply connected open set has
  holomorphic square roots.
* `TauCeti.HasHolomorphicSquareRoots.image` — the property is carried along a holomorphic map
  injective on an open set.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.11.
-/

public section

namespace TauCeti

open Function Set

variable {U : Set ℂ}

/-- A set `U ⊆ ℂ` **has holomorphic square roots** if every function holomorphic and nowhere zero
on `U` is, on `U`, the square of a function holomorphic on `U`. -/
def HasHolomorphicSquareRoots (U : Set ℂ) : Prop :=
  ∀ ⦃g : ℂ → ℂ⦄, DifferentiableOn ℂ g U → 0 ∉ g '' U →
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (fun z => f z ^ 2) g U

/-- A function holomorphic and nowhere zero on a set with holomorphic square roots has a
holomorphic square root there. -/
theorem HasHolomorphicSquareRoots.exists_differentiableOn_sq_eq (hU : HasHolomorphicSquareRoots U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hg₀ : 0 ∉ g '' U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (fun z => f z ^ 2) g U :=
  hU hg hg₀

/-- **A simply connected open set has holomorphic square roots.** This is the case `n = 2` of
`TauCeti.exists_differentiableOn_pow_eq`. -/
theorem _root_.IsSimplyConnected.hasHolomorphicSquareRoots (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) : HasHolomorphicSquareRoots U :=
  fun _ hg hg₀ => exists_differentiableOn_pow_eq hUc hUo hg hg₀ two_ne_zero

/-- **Holomorphic square roots are carried along injective holomorphic maps.** If `U` is open and
has holomorphic square roots, and `φ` is holomorphic and injective on `U`, then `φ '' U` has
holomorphic square roots: a root of `g ∘ φ` on `U`, composed with the holomorphic inverse
`Function.invFunOn φ U`, is a root of `g` on `φ '' U`. -/
theorem HasHolomorphicSquareRoots.image (hU : HasHolomorphicSquareRoots U) (hUo : IsOpen U)
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ U) (hφi : InjOn φ U) :
    HasHolomorphicSquareRoots (φ '' U) := by
  intro g hg hg₀
  have hmaps : MapsTo φ U (φ '' U) := mapsTo_image φ U
  obtain ⟨f, hfd, hfsq⟩ := hU.exists_differentiableOn_sq_eq (hg.comp hφ hmaps) (by
    rintro ⟨z, hz, hgz⟩
    exact hg₀ ⟨φ z, hmaps hz, hgz⟩)
  have hinv := (surjOn_image φ U).mapsTo_invFunOn
  refine ⟨f ∘ invFunOn φ U, hfd.comp (DifferentiableOn.invFunOn hφ hUo hφi) hinv, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simpa only [comp_apply, hφi.leftInvOn_invFunOn hz] using hfsq hz

end TauCeti
