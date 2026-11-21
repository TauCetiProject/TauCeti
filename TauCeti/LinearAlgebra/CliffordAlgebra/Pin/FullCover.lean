/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Norm

/-!
# The Pin group and the even part of the normalized full Clifford cover

The normalized full Clifford cover `CliffordAlgebra.cliffordFullCover Q` consists of the Lipschitz
elements whose reverse norm `reverse x * x` is `1` or `-1`; it is also the set where the `star`
norm `star x * x` is `±1` (`CliffordAlgebra.mem_cliffordFullCover_iff_lipschitzNorm`). Mathlib's
Pin group consists of the Lipschitz elements whose `star` norm is `1`, so it is the subgroup of the
full cover where the `star` norm is `1`. In the same way the Spin group is the subgroup of even
elements of reverse norm `1`, inside the even part of the full cover.

Over a field in which `-1` is not a square, the kernel of the full-cover action on a nondegenerate
quadratic space is `{±1}` in positive dimension and trivial in dimension zero; in either case it
lies in the Spin group. Hence the Pin and Spin groups are the inverse images in the full cover of
their images in the orthogonal group.

## Main definitions

* `CliffordAlgebra.pinToCliffordFullCover`: the inclusion of the Pin group in the full cover.

## Main results

* `CliffordAlgebra.mem_range_pinToCliffordFullCover_iff`: the Pin group is the part of the full
  cover of `star` norm `1`.
* `CliffordAlgebra.comap_range_pinToOrthogonal`: when `-1` is not a square, the Pin group of a
  nondegenerate space is the inverse image of its image in `O(Q)`.

The corresponding Spin results, `CliffordAlgebra.mem_range_spinToCliffordFullCover_iff` and
`CliffordAlgebra.comap_range_spinToOrthogonal`, are in `Lipschitz.FullCover.Basic`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6 and Proposition 1.21, where `Pin(p, q)` is the norm `±1`
  cover.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe u v

section Ring

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)] (Q : QuadraticForm R M)

/-! ### The Pin group in the full cover -/

/-- The Pin group embeds in the normalized full cover through its canonical Lipschitz lift. -/
def pinToCliffordFullCover : pinGroup Q →* cliffordFullCover Q :=
  (pinToLipschitz Q).codRestrict _ fun x ↦
    (mem_cliffordFullCover_iff_lipschitzNorm Q _).2 (Or.inl (lipschitzNorm_pinToLipschitz Q x))

/-- The underlying Lipschitz element of the Pin-to-full-cover inclusion. -/
@[simp]
theorem coe_pinToCliffordFullCover_apply (x : pinGroup Q) :
    (pinToCliffordFullCover Q x : lipschitzGroup Q) = pinToLipschitz Q x := by
  simp only [pinToCliffordFullCover, MonoidHom.codRestrict_apply]

/-- The Pin-to-full-cover inclusion is injective. -/
theorem pinToCliffordFullCover_injective : Function.Injective (pinToCliffordFullCover Q) := by
  intro x y h
  apply Subtype.ext
  simpa only [coe_pinToCliffordFullCover_apply, coe_pinToLipschitz_apply] using
    congrArg (fun z : cliffordFullCover Q ↦
      (((z : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) h

/-- The Pin action is the restriction of the full-cover action pointwise. -/
@[simp 1100]
theorem cliffordFullCoverToOrthogonal_pinToCliffordFullCover_apply (x : pinGroup Q) :
    cliffordFullCoverToOrthogonal Q (pinToCliffordFullCover Q x) = pinToOrthogonal Q x := by
  rw [cliffordFullCoverToOrthogonal_apply, coe_pinToCliffordFullCover_apply,
    pinToOrthogonal_eq_lipschitzToOrthogonal]

/-- The restricted orthogonal action agrees with the Pin action on the included subgroup. -/
@[simp]
theorem cliffordFullCoverToOrthogonal_comp_pinToCliffordFullCover :
    (cliffordFullCoverToOrthogonal Q).comp (pinToCliffordFullCover Q) = pinToOrthogonal Q :=
  MonoidHom.ext (cliffordFullCoverToOrthogonal_pinToCliffordFullCover_apply Q)

/-- The inclusion of the Spin group in the full cover factors through the Pin group. -/
@[simp]
theorem pinToCliffordFullCover_spinToPin (x : spinGroup Q) :
    pinToCliffordFullCover Q (spinToPin Q x) = spinToCliffordFullCover Q x :=
  Subtype.ext (by
    rw [coe_pinToCliffordFullCover_apply, coe_spinToCliffordFullCover_apply, spinToLipschitz_apply])

/-- The inclusion of the Spin group in the full cover factors through the Pin group. -/
@[simp]
theorem pinToCliffordFullCover_comp_spinToPin :
    (pinToCliffordFullCover Q).comp (spinToPin Q) = spinToCliffordFullCover Q :=
  MonoidHom.ext (pinToCliffordFullCover_spinToPin Q)

/-- **The Pin group inside the full cover** is the subgroup of elements of `star` norm `1`. -/
theorem mem_range_pinToCliffordFullCover_iff (x : cliffordFullCover Q) :
    x ∈ (pinToCliffordFullCover Q).range ↔ lipschitzNorm Q x = 1 := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [coe_pinToCliffordFullCover_apply, lipschitzNorm_pinToLipschitz]
  · intro h
    refine ⟨⟨_, (mem_pinGroup_iff_lipschitzNorm_eq_one Q x).2 h⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact Units.ext (by rw [coe_pinToCliffordFullCover_apply, coe_pinToLipschitz_apply])

end Ring

/-! ### Comparison over a field -/

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-- **The Pin group is the inverse image of its image.** When `-1` is not a square, an element of
the full cover of a nondegenerate quadratic space acts like a Pin element exactly when it is one:
the kernel of the full-cover action, `{±1}` in positive dimension and trivial in dimension zero,
lies in the Pin group. -/
theorem comap_range_pinToOrthogonal (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K)) :
    (pinToOrthogonal Q).range.comap (cliffordFullCoverToOrthogonal Q) =
      (pinToCliffordFullCover Q).range := by
  have hker : (cliffordFullCoverToOrthogonal Q).ker ≤ (pinToCliffordFullCover Q).range := by
    refine (ker_cliffordFullCoverToOrthogonal_le_range_spinToCliffordFullCover hQ h).trans ?_
    rw [← pinToCliffordFullCover_comp_spinToPin, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  rw [← cliffordFullCoverToOrthogonal_comp_pinToCliffordFullCover, ← MonoidHom.map_range,
    Subgroup.comap_map_eq, sup_eq_left.2 hker]

end Field

end CliffordAlgebra
