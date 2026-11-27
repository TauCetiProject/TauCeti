/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Inner

/-!
# The inclusion of a point into the circle is not a Serre fibration

The exact homotopy sequence of a map `p : E → B` with fibre `F = p⁻¹(b)`,

`π₁(F) → π₁(E) → π₁(B) → π₀(F)`,

needs `p` to be a Serre fibration. This file shows that the hypothesis cannot be dropped, on the
smallest example: the inclusion `{1} → S¹` of the base point of the unit circle
(`Circle.inclusionOne`).

* It is not a Serre fibration (`Circle.notMem_serreFibrations_inclusionOne`): a Serre fibration
  lifts paths, but the loop `t ↦ e^{2πit}` at `1` has no lift, since a lift would make it
  constant at `1`, while it passes through `-1` at `t = 1/2`.
* Its would-be sequence is not exact at `π₁(S¹)`
  (`Circle.range_homotopyGroupMap_inclusionOne_ne_preimage`). The fibre over `1` is `{1}`, so
  `π₀(F)` is a point and every map `∂ : π₁(S¹, 1) → π₀(F)` sends all of `π₁(S¹, 1) ≅ ℤ` to its
  base point, while the image of `π₁({1}) → π₁(S¹, 1)` is trivial. For a Serre fibration the
  image is exactly the kernel of the boundary map
  (`TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq`).
* Equivalently, `π₁({1}) → π₁(S¹, 1)` is not surjective although `π₀(F)` is trivial
  (`Circle.not_surjective_homotopyGroupMap_inclusionOne`), so
  `TauCeti.TopCat.surjective_homotopyGroupMap_of_subsingleton` fails without its fibration
  hypothesis.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2, Theorem 4.41.
-/

public section

noncomputable section

open CategoryTheory unitInterval

namespace Circle

/-- The inclusion `{1} → S¹` of the base point of the unit circle, as a morphism of `TopCat`. -/
def inclusionOne : TopCat.of ({1} : Set Circle) ⟶ TopCat.of Circle :=
  TopCat.ofHom (ContinuousMap.subtypeVal {1})

@[simp]
theorem inclusionOne_apply (x : ({1} : Set Circle)) : inclusionOne x = x :=
  (rfl)

/-- **The inclusion of `1` into the circle is not a Serre fibration.** A Serre fibration lifts
paths, but the loop `t ↦ e^{2πit}` at `1` has no lift to `{1}`: a lift would make the loop
constant at `1`, while it passes through `-1` at `t = 1/2`. -/
theorem notMem_serreFibrations_inclusionOne :
    ¬ TauCeti.TopCat.serreFibrations inclusionOne := by
  intro hp
  obtain ⟨Γ, -, hΓ⟩ := TauCeti.TopCat.exists_path_lift_of_mem_serreFibrations hp
    (e := (⟨1, rfl⟩ : ({1} : Set Circle))) (expLoop.cast (inclusionOne_apply _) rfl)
  let t : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht : 2 * Real.pi * t = Real.pi := by simp only [t]; ring
  have h := congrFun hΓ t
  rw [Function.comp_apply, inclusionOne_apply, Set.mem_singleton_iff.1 (Γ t).property,
    Path.cast_coe, expLoop_apply, ht, exp_pi] at h
  have h1 := congrArg (fun z : Circle ↦ (z : ℂ).re) h
  norm_num at h1

/-- **The inclusion of `1` is not surjective on `π₁`.** The map `π₁({1}) → π₁(S¹, 1)` induced by
`{1} → S¹` is not surjective, although `π₀` of its fibre over `1` is trivial: its source is
trivial, while `π₁(S¹, 1) ≅ ℤ` is not. Hence the fibration hypothesis of
`TauCeti.TopCat.surjective_homotopyGroupMap_of_subsingleton` cannot be dropped. -/
theorem not_surjective_homotopyGroupMap_inclusionOne (e : inclusionOne.fiber 1) :
    ¬ Function.Surjective
      (HomotopyGroup.map (N := Option (Fin 0)) inclusionOne.hom
        (Set.mem_singleton_iff.1 e.property)) := by
  intro h
  have := nontrivial_fundamentalGroup 1
  have : Nontrivial (HomotopyGroup (Option (Fin 0)) (TopCat.of Circle) 1) :=
    (homotopyGroupEquivFundamentalGroupOfUnique (Option (Fin 0))).nontrivial
  exact not_subsingleton _ h.subsingleton

/-- **The homotopy sequence of `{1} → S¹` is not exact at `π₁(S¹)`.** For every map
`d : π₁(S¹, 1) → π₀(F)` to the path components of the fibre `F = {1}` over `1`, the classes sent by
`d` to the base point are not the image of `π₁({1}) → π₁(S¹, 1)`: since `π₀(F)` is a point they
are all of `π₁(S¹, 1) ≅ ℤ`, while the image is trivial. For a Serre fibration and its boundary map
they agree (`TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq`). -/
theorem range_homotopyGroupMap_inclusionOne_ne_preimage (e : inclusionOne.fiber 1)
    (d : HomotopyGroup (Option (Fin 0)) (TopCat.of Circle) 1 →
      HomotopyGroup (Fin 0) (inclusionOne.fiber 1) e) :
    Set.range (HomotopyGroup.map (N := Option (Fin 0)) inclusionOne.hom
        (Set.mem_singleton_iff.1 e.property)) ≠ d ⁻¹' {⟦GenLoop.const⟧} := by
  have : Nonempty (inclusionOne.fiber 1) := ⟨e⟩
  refine fun h ↦ not_surjective_homotopyGroupMap_inclusionOne e (Set.range_eq_univ.1 ?_)
  exact h.trans (Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _)

end Circle
