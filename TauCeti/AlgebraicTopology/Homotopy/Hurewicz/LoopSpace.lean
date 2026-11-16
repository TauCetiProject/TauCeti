/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Comparison

/-!
# Hurewicz generators of loop spaces in every positive degree

Let `ΩX` be a loop space whose homotopy groups vanish below degree `n + 1`. The Hurewicz class of a
generalized loop `p` of `ΩX` of degree `n + 1` is an isomorphism `ℤ ≅ Hₙ₊₁(ΩX; ℤ)` exactly when the
class of `p` generates `πₙ₊₁(ΩX)` freely
(`HomotopyGroup.isIso_hurewicz_loopSpace_iff_bijective_zmultiplesHom`).

For `n ≥ 1` this is the Hurewicz theorem
(`HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom`), which needs nothing of `ΩX` beyond
its connectivity. In degree one the Hurewicz map identifies `H₁` only with the abelianization of
`π₁`, and the statement holds because the fundamental group of a loop space is commutative: the
loop-space shift identifies it with `π₂(X, x)`
(`HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom_of_commute`). So the criterion holds
uniformly in the degree for loop spaces, which is the form in which it applies to iterated loop
spaces, such as the double loop spaces of spheres.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2A.1 and
  Theorem 4.32.
-/

public section

open CategoryTheory
open scoped Topology Topology.Homotopy

namespace HomotopyGroup

variable {X : Type} [TopologicalSpace X] {x : X}

/-- **The Hurewicz class of a generalized loop of a loop space generates exactly when its homotopy
class does.** For a loop space `ΩX` whose homotopy groups vanish below degree `n + 1`, the Hurewicz
class of `p` is an isomorphism `ℤ ≅ Hₙ₊₁(ΩX; ℤ)` exactly when the class of `p` generates
`πₙ₊₁(ΩX)` freely. In degree one, `n = 0`, the fundamental group of the loop space is commutative,
so the abelianization in the degree-one Hurewicz theorem is not needed. -/
theorem isIso_hurewicz_loopSpace_iff_bijective_zmultiplesHom {n : ℕ}
    (hX : ∀ k < n + 1, Subsingleton (HomotopyGroup (Fin k) (Ω X x) (Path.refl x)))
    (p : Ω^ (Fin (n + 1)) (Ω X x) (Path.refl x)) :
    IsIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p) ↔
      Function.Bijective
        (zmultiplesHom (Additive (HomotopyGroup (Fin (n + 1)) (Ω X x) (Path.refl x)))
          (Additive.ofMul ⟦p⟧)) := by
  cases n with
  | zero =>
    have := (TauCeti.pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (Path.refl x)).2
      (hX 0 one_pos)
    refine isIso_hurewicz_iff_bijective_zmultiplesHom_of_commute (fun a b ↦ ?_) p
    -- The loop-space shift is an injective homomorphism into the commutative group `π₂(X, x)`.
    refine (pathLoopSpaceMulEquiv 0).injective ?_
    rw [_root_.map_mul, _root_.map_mul, mul_comm]
  | succ n => exact isIso_hurewicz_iff_bijective_zmultiplesHom hX p

end HomotopyGroup
