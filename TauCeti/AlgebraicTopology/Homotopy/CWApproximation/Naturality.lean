/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead

/-!
# Naturality of CW approximation up to homotopy

A map `f : X → Y` into a path-connected space lifts to a map
`TauCeti.cwApproximationLift f x y : cwApproximation X x → cwApproximation Y y` of CW
approximations, so that the square formed with the approximation maps commutes up to homotopy
(`TauCeti.cwApproximationMap_comp_cwApproximationLift_homotopic`). The lift is unique up to
homotopy: a map of CW approximations is homotopic to it exactly when it makes the square commute up
to homotopy (`TauCeti.homotopic_cwApproximationLift_iff`). This is Hatcher's Proposition 4.18,
and it follows from the bijection `[K, X] ≃ [K, Y]` that a weak homotopy equivalence `X → Y`
induces on homotopy classes of maps out of a CW complex `K` (Hatcher, Proposition 4.22).

By uniqueness, CW approximation is a functor up to homotopy: the lift of the identity is homotopic
to the identity, the lift of a composite is homotopic to the composite of the lifts, and homotopic
maps have homotopic lifts. The lift of `f` is a weak homotopy equivalence exactly when `f` is, and
it is then a homotopy equivalence (`TauCeti.cwApproximationHomotopyEquiv`) by Whitehead's
theorem. Applied to the identity of `X`, this shows that the CW approximation does not depend on its
base point up to homotopy equivalence. Any other CW approximation of `X` is homotopy equivalent to
it as well (`ContinuousMap.IsWeakHomotopyEquivalence.exists_homotopyEquiv_comp_homotopic`).

## Main definitions

* `TauCeti.cwApproximationLift f x y`: the map of CW approximations induced by `f : X ⟶ Y`.
* `TauCeti.cwApproximationHomotopyEquiv`: the lift of a weak homotopy equivalence, as a homotopy
  equivalence.

## Main results

* `TauCeti.cwApproximationMap_comp_cwApproximationLift_homotopic`: the lift makes the square with
  the approximation maps commute up to homotopy.
* `TauCeti.homotopic_cwApproximationLift_iff`: the lift is unique up to homotopy.
* `TauCeti.cwApproximationLift_id_homotopic`, `TauCeti.cwApproximationLift_comp_homotopic`,
  `TauCeti.cwApproximationLift_homotopic_of_homotopic`: functoriality up to homotopy.
* `TauCeti.isWeakHomotopyEquivalence_cwApproximationLift_iff`: the lift of `f` is a weak homotopy
  equivalence exactly when `f` is.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.18 and Corollary 4.19 (naturality and uniqueness of CW approximations)
  and Proposition 4.22.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (x : X) (y : Y)

section Lift

variable [PathConnectedSpace Y]

/-- **The map of CW approximations induced by `f : X ⟶ Y`**: a map
`cwApproximation X x ⟶ cwApproximation Y y` whose composite with the approximation map of `Y` is
homotopic to the composite of the approximation map of `X` with `f`
(`TauCeti.cwApproximationMap_comp_cwApproximationLift_homotopic`). It is unique up to homotopy
(`TauCeti.homotopic_cwApproximationLift_iff`). -/
def cwApproximationLift : cwApproximation X x ⟶ cwApproximation Y y :=
  TopCat.ofHom (X := cwApproximation X x) (Y := cwApproximation Y y)
    ((isWeakHomotopyEquivalence_cwApproximationMap Y y).exists_comp_homotopic
    (f.hom.comp (cwApproximationMap X x).hom)).choose

/-- **CW approximation is natural up to homotopy** (Hatcher, Proposition 4.18): the lift of `f`
commutes with the approximation maps up to homotopy. -/
theorem cwApproximationMap_comp_cwApproximationLift_homotopic :
    ((cwApproximationMap Y y).hom.comp (cwApproximationLift f x y).hom).Homotopic
      (f.hom.comp (cwApproximationMap X x).hom) := by
  rw [cwApproximationLift, TopCat.hom_ofHom]
  exact ((isWeakHomotopyEquivalence_cwApproximationMap Y y).exists_comp_homotopic _).choose_spec

/-- **The lift to CW approximations is unique up to homotopy** (Hatcher, Proposition 4.18): a map
`g` of CW approximations is homotopic to the lift of `f` exactly when its composite with the
approximation map of `Y` is homotopic to the composite of the approximation map of `X` with `f`. -/
theorem homotopic_cwApproximationLift_iff {g : C(cwApproximation X x, cwApproximation Y y)} :
    g.Homotopic (cwApproximationLift f x y).hom ↔
      ((cwApproximationMap Y y).hom.comp g).Homotopic
        (f.hom.comp (cwApproximationMap X x).hom) := by
  rw [← (isWeakHomotopyEquivalence_cwApproximationMap Y y).comp_homotopic_comp_iff]
  exact ⟨fun h ↦ h.trans (cwApproximationMap_comp_cwApproximationLift_homotopic f x y),
    fun h ↦ h.trans (cwApproximationMap_comp_cwApproximationLift_homotopic f x y).symm⟩

/-- Homotopic maps have homotopic lifts to CW approximations. -/
theorem cwApproximationLift_homotopic_of_homotopic {f₀ f₁ : X ⟶ Y}
    (h : f₀.hom.Homotopic f₁.hom) :
    (cwApproximationLift f₀ x y).hom.Homotopic (cwApproximationLift f₁ x y).hom :=
  (homotopic_cwApproximationLift_iff f₁ x y).2
    ((cwApproximationMap_comp_cwApproximationLift_homotopic f₀ x y).trans
      (h.comp (ContinuousMap.Homotopic.refl _)))

end Lift

/-- The lift of the identity to the CW approximation is homotopic to the identity. -/
theorem cwApproximationLift_id_homotopic [PathConnectedSpace X] :
    (cwApproximationLift (𝟙 X) x x).hom.Homotopic (ContinuousMap.id _) := by
  refine ((homotopic_cwApproximationLift_iff (𝟙 X) x x).2 ?_).symm
  rw [TopCat.hom_id, ContinuousMap.comp_id, ContinuousMap.id_comp]

/-- The lift of a composite to CW approximations is homotopic to the composite of the lifts. -/
theorem cwApproximationLift_comp_homotopic [PathConnectedSpace Y] [PathConnectedSpace Z]
    (g : Y ⟶ Z) (z : Z) :
    (cwApproximationLift (f ≫ g) x z).hom.Homotopic
      ((cwApproximationLift g y z).hom.comp (cwApproximationLift f x y).hom) := by
  refine ((homotopic_cwApproximationLift_iff (f ≫ g) x z).2 ?_).symm
  -- `p_Z ∘ g̃ ∘ f̃ ≃ g ∘ p_Y ∘ f̃ ≃ g ∘ f ∘ p_X`, for the approximation maps `p`.
  have h₁ := (cwApproximationMap_comp_cwApproximationLift_homotopic g y z).comp
    (ContinuousMap.Homotopic.refl (cwApproximationLift f x y).hom)
  have h₂ := (ContinuousMap.Homotopic.refl g.hom).comp
    (cwApproximationMap_comp_cwApproximationLift_homotopic f x y)
  rw [TopCat.hom_comp, ← ContinuousMap.comp_assoc, ContinuousMap.comp_assoc g.hom]
  rw [ContinuousMap.comp_assoc g.hom] at h₁
  exact h₁.trans h₂

variable [PathConnectedSpace X] [PathConnectedSpace Y]

/-- The lift of `f` to CW approximations is a weak homotopy equivalence exactly when `f` is. -/
theorem isWeakHomotopyEquivalence_cwApproximationLift_iff :
    (cwApproximationLift f x y).hom.IsWeakHomotopyEquivalence ↔
      f.hom.IsWeakHomotopyEquivalence := by
  have hX := isWeakHomotopyEquivalence_cwApproximationMap X x
  have hY := isWeakHomotopyEquivalence_cwApproximationMap Y y
  have h := cwApproximationMap_comp_cwApproximationLift_homotopic f x y
  exact ⟨fun hf ↦ hX.of_precomp ((hY.comp hf).of_homotopic h),
    fun hf ↦ hY.of_postcomp ((hf.comp hX).of_homotopic h.symm)⟩

/-- **The lift of a weak homotopy equivalence to CW approximations, as a homotopy equivalence**
(Hatcher, Corollary 4.19). For `f` the identity of `X`, this identifies the CW approximations of `X`
built from two base points. -/
def cwApproximationHomotopyEquiv (hf : f.hom.IsWeakHomotopyEquivalence) :
    ContinuousMap.HomotopyEquiv (cwApproximation X x) (cwApproximation Y y) :=
  ((isWeakHomotopyEquivalence_cwApproximationLift_iff f x y).2 hf).homotopyEquiv

/-- The homotopy equivalence of CW approximations induced by a weak homotopy equivalence `f` is the
lift of `f`. -/
@[simp]
theorem cwApproximationHomotopyEquiv_toFun (hf : f.hom.IsWeakHomotopyEquivalence) :
    (cwApproximationHomotopyEquiv f x y hf).toFun = (cwApproximationLift f x y).hom :=
  ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv_toFun _

end TauCeti
