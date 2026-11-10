/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FreeModule.CardQuotient
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import TauCeti.RingTheory.OrderOfVanishing

/-!
# The length of the cokernel of an endomorphism of a free module over a PID

Let `R` be a principal ideal domain and `f` an endomorphism of a finite free `R`-module `M` with
nonzero determinant. Then the length of `M ⧸ range f` is the order of vanishing
`Ring.ord R (det f) = length (R ⧸ (det f))`. The Smith normal form of `range f` splits the
quotient into the residue rings `R ⧸ (aᵢ)` of its diagonal coefficients, whose product is
associated to `det f`, and the order of vanishing is additive on products of nonzero elements.

This is the length counterpart of `LinearMap.card_quotient_range_eq_card_quotient_span_det`. It
needs no finiteness of residue rings: over a discrete valuation ring it says that the length of
the cokernel is the valuation of the determinant. Applied to the inclusion of a lattice into its
dual lattice, it computes the length of the quotient by the order of the Gram determinant.

## Main results

* `LinearMap.length_quotient_range_eq_ord_det`: for `det f ≠ 0`,
  `Module.length R (M ⧸ range f) = Ring.ord R (det f)`.
-/

public section

open Module Submodule

open scoped nonZeroDivisors

namespace LinearMap

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- **The length of the cokernel of an endomorphism of a finite free module over a principal
ideal domain** is the order of vanishing of its determinant, provided the determinant is
nonzero. -/
theorem length_quotient_range_eq_ord_det {f : M →ₗ[R] M} (hf : f.det ≠ 0) :
    Module.length R (M ⧸ range f) = Ring.ord R f.det := by
  classical
  let b := Module.Free.chooseBasis R M
  have hinj : Function.Injective f :=
    ker_eq_bot.mp (not_ne_iff.mp (mt det_eq_zero_iff_ker_ne_bot.mpr hf))
  have h : finrank R (range f) = finrank R M := (LinearEquiv.ofInjective f hinj).finrank_eq.symm
  have hassoc := associated_det_prod_smithNormalFormCoeffs hinj b h
  -- Every Smith coefficient is nonzero, since their product is associated to `det f ≠ 0`.
  have ha : ∀ i ∈ Finset.univ, smithNormalFormCoeffs b h i ∈ R⁰ := fun i hi ↦
    mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mp (hassoc.ne_zero_iff.mp hf) i hi)
  rw [(quotientEquivPiSpan (range f) b h).length_eq, Module.length_pi_of_fintype,
    Ring.ord_eq_of_associated hassoc, TauCeti.Ring.ord_prod _ ha]
  simp only [Ring.ord]

end LinearMap
