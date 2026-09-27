/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.GradedComm

/-!
# The cup product with trivial `ZMod p` coefficients

Multiplication in `ZMod p` gives a continuous equivariant pairing of the trivial coefficient
representations. Its cup product in degrees `(1, 1)` is the bilinear pairing on continuous
cohomology used to define and study Demushkin groups. The coefficient representation is lifted
to the universe of the group, as required by the continuous cohomology complex. When `p` is
prime, `ZMod p` is the field `𝔽_p`.

Because multiplication is commutative the opposite pairing of `fpPairing p G` is itself, and
graded commutativity of the cup product in bidegree `(1, 1)` reads `cupFp p G a b = - cupFp p G b a`
(`TauCeti.cupFp_gradedComm`).

## Main definitions

* `TauCeti.fpPairing`: multiplication on the trivial coefficient representation.
* `TauCeti.cupFp`: the resulting cup product `H¹(G, ZMod p) × H¹(G, ZMod p) → H²(G, ZMod p)`.

## Main results

* `TauCeti.fpPairing_flip`: the opposite of the multiplication pairing is itself.
* `TauCeti.cupFp_gradedComm`: the cup square is graded-commutative, `cupFp a b = - cupFp b a`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, I §1.4.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1.
-/

public section

namespace TauCeti

open _root_.ContinuousCohomology

universe u

section Monoid

variable (p : ℕ) (G : Type u) [Monoid G]

/-- Multiplication of trivial `ZMod p` coefficients as a continuous equivariant
bilinear pairing. -/
noncomputable def fpPairing :
    TopPairing (trivialFp p G) (trivialFp p G) (trivialFp p G) where
  bil := (((LinearMap.mul (ZMod p) (ZMod p)).comp
    (trivialFpEquiv p G).toLinearMap).compl₂
      (trivialFpEquiv p G).toLinearMap).compr₂
        (trivialFpEquiv p G).symm.toLinearMap
  cont := continuous_of_discreteTopology
  equivariant g x y := by simp

/-- The coefficient pairing is multiplication in `ZMod p`, under the universe lift. -/
@[simp]
theorem fpPairing_bil_apply (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y =
      (trivialFpEquiv p G).symm (trivialFpEquiv p G x * trivialFpEquiv p G y) :=
  by simp [fpPairing]

/-- Multiplication on the trivial coefficient representation is symmetric. -/
theorem fpPairing_bil_comm (x y : (trivialFp p G).V) :
    (fpPairing p G).bil x y = (fpPairing p G).bil y x := by
  simp only [fpPairing_bil_apply, mul_comm]

/-- The opposite of the multiplication pairing is itself, because multiplication in `ZMod p` is
commutative. -/
@[simp]
theorem fpPairing_flip : (fpPairing p G).flip = fpPairing p G :=
  TopPairing.ext (LinearMap.ext₂ fun x y ↦ by
    rw [TopPairing.flip_bil, fpPairing_bil_comm])

end Monoid

section Group

variable (p : ℕ) (G : Type u) [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The degree-`(1,1)` cup product on continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable def cupFp :
    cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 1 →ₗ[ZMod p] cohomFp p G 2 :=
  (fpPairing p G).cup 1 1

/-- The specialized cup product is the general cup product of the multiplication pairing.
This equation lets general cup-product results apply to arbitrary cohomology classes. -/
theorem cupFp_def : cupFp p G = (fpPairing p G).cup 1 1 := by
  simp only [cupFp]

/-- On classes of cocycles, `cupFp` is the class of their cochain cup product. -/
@[simp]
theorem cupFp_π (a b : cocycles (trivialFp p G) 1) :
    cupFp p G (π (trivialFp p G) 1 a)
      (π (trivialFp p G) 1 b) =
        π (trivialFp p G) 2 ((fpPairing p G).cupCocycles 1 1 a b) := by
  simpa [cupFp_def] using (fpPairing p G).cup_π 1 1 a b

/-- **Graded commutativity of the cup square**, `cupFp a b = - cupFp b a`: the bidegree-`(1, 1)`
graded commutativity of the cup product at the multiplication pairing, whose opposite pairing is
itself. -/
theorem cupFp_gradedComm (a b : cohomFp p G 1) : cupFp p G a b = -cupFp p G b a := by
  rw [cupFp_def, (fpPairing p G).cup_one_one_eq_neg_flip a b, fpPairing_flip]

end Group

end TauCeti
