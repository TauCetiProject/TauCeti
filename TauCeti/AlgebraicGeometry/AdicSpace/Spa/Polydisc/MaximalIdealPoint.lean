/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MaximalIdealPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic

/-!
# Classical points of the closed polydisc as maximal-ideal points

Over a complete nonarchimedean field `K`, evaluation at a power-bounded tuple `a` has a closed
maximal kernel and residue field `K`. The classical point `f ↦ |f(a)|` of the closed polydisc is
therefore the maximal-ideal point attached to that kernel.

## Main results

* `TauCeti.ValuationSpectrum.classicalPoint_val_eq_maximalIdealPoint_val`: the classical point
  `x_a` of the closed polydisc is the maximal-ideal point at the kernel of evaluation at `a`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Examples 7.57 and 7.58.
-/

public section

noncomputable section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [NonarchimedeanRing K] {k : ℕ}

/-- **The classical points of the closed polydisc are maximal-ideal points**: the point
`x_a : f ↦ |f(a)|` attached to `a ∈ (K°)ᵏ` is the maximal-ideal point at the kernel of evaluation
at `a`. It does not depend on the auxiliary point `x` of `Spa (K, K°)`. -/
theorem classicalPoint_val_eq_maximalIdealPoint_val [IsUltrametricDist K]
    (x : spa (powerBoundedSubring K)) (a : Fin k → K) (ha : ∀ i, IsPowerBounded (a i)) :
    (classicalPoint x a ha).1 =
      (maximalIdealPoint K (RingHom.ker (evalAtHom a ha)) (isClosed_ker_evalAtHom a ha)).1 :=
  ext' fun f g ↦ by
    rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.2,
      maximalIdealPoint_vle_iff_of_ker_eq (𝔪 := RingHom.ker (evalAtHom a ha)) _
        (evalAtAlgHom a ha) (by ext f; simp [RingHom.mem_ker]), evalAtAlgHom_apply,
      evalAtAlgHom_apply]

end TauCeti.ValuationSpectrum
