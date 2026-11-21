/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Comparison
import TauCeti.Algebra.Group.ZMultiples

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
loop-space shift identifies it with `π₂(X, x)` (`HomotopyGroup.mul_comm_pathLoopSpace`,
`HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom_of_commute`). So the criterion holds
uniformly in the degree for loop spaces, which is the form in which it applies to iterated loop
spaces, such as the double loop spaces of spheres.

Combined with the Hurewicz theorem for `X`, the criterion shows that the loop-space shift
`πₙ₊₁(Ω_x X) ≅ πₙ₊₂(X, x)` matches generating Hurewicz classes of `Ω_x X` and of `X`
(`HomotopyGroup.isIso_hurewicz_genLoopLoopHomeomorph_iff`), in every degree `n + 1 ≥ 1`.

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
    exact isIso_hurewicz_iff_bijective_zmultiplesHom_of_commute (mul_comm_pathLoopSpace 0) p
  | succ n => exact isIso_hurewicz_iff_bijective_zmultiplesHom hX p

/-- **The loop-space shift preserves generating Hurewicz classes.** If `πₖ(X, x)` vanishes for
`k < n + 2`, a generalized loop `g` of the loop space `Ω_x X` at the constant loop has a Hurewicz
class generating `Hₙ₊₁(Ω_x X; ℤ)` exactly when the generalized loop
`GenLoop.genLoopLoopHomeomorph x (n + 1) g` of `X` it corresponds to has one generating
`Hₙ₊₂(X; ℤ)`. -/
theorem isIso_hurewicz_genLoopLoopHomeomorph_iff {n : ℕ}
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (g : Ω^ (Fin (n + 1)) (Ω X x) (Path.refl x)) :
    IsIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (GenLoop.genLoopLoopHomeomorph x (n + 1) g)) ↔
      IsIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) g) := by
  have hΩ : ∀ k < n + 1, Subsingleton (HomotopyGroup (Fin k) (Ω X x) (Path.refl x)) :=
    fun k hk ↦ (TauCeti.subsingleton_homotopyGroup_loopSpace_iff x k).2 (hX (k + 1) (by omega))
  -- The shift sends the class of `g` to the class of the corresponding loop of `X`.
  have hF : (pathLoopSpaceMulEquiv n).toAdditive
      (Additive.ofMul (α := HomotopyGroup (Fin (n + 1)) (Ω X x) (Path.refl x)) ⟦g⟧) =
      Additive.ofMul (α := HomotopyGroup (Fin (n + 2)) X x)
        ⟦GenLoop.genLoopLoopHomeomorph x (n + 1) g⟧ := by
    rw [MulEquiv.toAdditive_apply_apply]
    exact congrArg Additive.ofMul (pathLoopSpaceMulEquiv_mk_eq_genLoopLoopHomeomorph n g)
  rw [isIso_hurewicz_iff_bijective_zmultiplesHom hX,
    isIso_hurewicz_loopSpace_iff_bijective_zmultiplesHom hΩ, ← hF]
  exact AddEquiv.bijective_zmultiplesHom_apply_iff _ _

end HomotopyGroup
