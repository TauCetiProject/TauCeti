/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology

/-!
# The cup product with trivial `𝔽_p` coefficients

Multiplication in `𝔽_p` gives a continuous equivariant pairing of the trivial coefficient
representations. Its cup product in degrees `(1, 1)` is the bilinear pairing on continuous
cohomology used to define and study Demushkin groups. The coefficient representation is lifted
to the universe of the group, as required by the continuous cohomology complex.

## Main definitions

* `TauCeti.fpPairing`: multiplication on the trivial coefficient representation.
* `TauCeti.cupFp`: the resulting cup product `H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, I §1.4.
-/

public section

namespace TauCeti

open _root_.ContinuousCohomology

universe u

section Monoid

variable (p : ℕ) (G : Type u) [Monoid G]

/-- Multiplication of trivial `𝔽_p` coefficients, as a continuous equivariant bilinear pairing. -/
noncomputable def fpPairing :
    TopPairing (trivialFp p G) (trivialFp p G) (trivialFp p G) where
  bil := (((LinearMap.mul (ZMod p) (ZMod p)).comp
    (trivialFpEquiv p G).toLinearMap).compl₂
      (trivialFpEquiv p G).toLinearMap).compr₂
        (trivialFpEquiv p G).symm.toLinearMap
  cont := continuous_of_discreteTopology
  equivariant g x y := by simp

/-- The coefficient pairing is multiplication in `𝔽_p`, under the universe lift. -/
@[simp]
theorem fpPairing_bil_apply (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y =
      (trivialFpEquiv p G).symm (trivialFpEquiv p G x * trivialFpEquiv p G y) :=
  by simp [fpPairing]

/-- Multiplication on the trivial coefficient representation is symmetric. -/
theorem fpPairing_bil_comm (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y = (fpPairing p G).bil y x := by
  simp only [fpPairing_bil_apply, mul_comm]

end Monoid

section Group

variable (p : ℕ) (G : Type u) [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The degree-`(1,1)` cup product on continuous cohomology with trivial `𝔽_p` coefficients. -/
noncomputable def cupFp :
    cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 2 :=
  (fpPairing p G).cup 1 1

/-- On classes of cocycles, `cupFp` is the class of their cochain cup product. -/
@[simp]
theorem cupFp_π (a b : cocycles (trivialFp p G) 1) :
    cupFp p G (π (trivialFp p G) 1 a)
      (π (trivialFp p G) 1 b) =
        π (trivialFp p G) 2 ((fpPairing p G).cupCocycles 1 1 a b) := by
  simpa [cupFp] using (fpPairing p G).cup_π 1 1 a b

end Group

end TauCeti
