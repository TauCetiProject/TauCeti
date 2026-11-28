/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.TwistedRelativePosition

/-!
# Affine Deligne–Lusztig point loci

For a subgroup `I` of `G` preserved by an endomorphism `σ`, the relative position of `gI`
and `bσ(g)I` is the double coset of `g⁻¹ b σ(g)`. The fibres of this map give the sets of
affine Deligne–Lusztig points. The left-coset carrier works for nonnormal subgroups, including
Iwahori subgroups.

## References

* X. He, *Geometric and homological properties of affine Deligne-Lusztig varieties*,
  Ann. of Math. 179 (2014), Definition 1.1.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The point locus `X_I(w,b)` in the left-coset space `G ⧸ I`, the fibre of the twisted relative
position over `IwI`. -/
def affineDeligneLusztigPoints (I : Subgroup G) (σ : G →* G) (hσ : I.map σ ≤ I) (w b : G) :
    Set (G ⧸ I) :=
  I.twistedRelativePosition σ hσ b ⁻¹' {DoubleCoset.mk I I w}

/-- A point lies in the locus exactly when its twisted relative position is the label `IwI`. -/
theorem mem_affineDeligneLusztigPoints (I : Subgroup G) (σ : G →* G) (hσ : I.map σ ≤ I)
    {w b : G} {q : G ⧸ I} :
    q ∈ I.affineDeligneLusztigPoints σ hσ w b ↔
      I.twistedRelativePosition σ hσ b q = DoubleCoset.mk I I w := by
  simp [affineDeligneLusztigPoints]

/-- The representative criterion for the point locus is `g⁻¹ * b * σ g ∈ IwI`. -/
@[simp]
theorem mk_mem_affineDeligneLusztigPoints (I : Subgroup G) (σ : G →* G) (hσ : I.map σ ≤ I)
    {w b g : G} :
    (g : G ⧸ I) ∈ I.affineDeligneLusztigPoints σ hσ w b ↔
      σ.twistedConj g b ∈ DoubleCoset.doubleCoset w (I : Set G) (I : Set G) := by
  rw [I.mem_affineDeligneLusztigPoints, I.twistedRelativePosition_mk]
  exact eq_comm.trans (DoubleCoset.eq.trans DoubleCoset.mem_doubleCoset.symm)

/-- Representatives of the same double coset label the same affine Deligne–Lusztig point locus. -/
theorem affineDeligneLusztigPoints_eq_of_doubleCoset_eq (I : Subgroup G) (σ : G →* G)
    (hσ : I.map σ ≤ I) {w v : G} (b : G)
    (h : DoubleCoset.doubleCoset w (I : Set G) (I : Set G) = DoubleCoset.doubleCoset v I I) :
    I.affineDeligneLusztigPoints σ hσ w b = I.affineDeligneLusztigPoints σ hσ v b := by
  simp only [affineDeligneLusztigPoints, DoubleCoset.mk_eq_of_doubleCoset_eq h]

end Subgroup
