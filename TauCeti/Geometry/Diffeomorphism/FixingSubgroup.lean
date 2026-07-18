/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Topology.Algebra.Homeomorph.Action
public import TauCeti.Algebra.GroupAction.FixingSubgroup

/-!
# Diffeomorphisms fixing a subset pointwise

The geometric-topology roadmap's relative diffeomorphism groups, such as `Diff(M, ∂M)`, are
subgroups of the self-diffeomorphism group whose elements fix a specified subset pointwise. Mathlib
already provides the generic pointwise fixing subgroup `fixingSubgroup` for any group
action; this file specializes that construction to the tautological action of the diffeomorphism
group on its manifold.

This is the algebraic substrate for the layer-3 target in
`TauCetiRoadmap/GeometricTopology/README.md`, "diffeomorphism groups with the C^∞ topology", where
`Diff(M, ∂M)` is the subgroup fixing the boundary pointwise. The topology and the proof that the
relative subgroup is closed are deliberately left to the later `C^∞`-topology buildout.

## Main definitions

* `TauCeti.Diffeomorph.fixingSubgroup s`: self-diffeomorphisms fixing every point of `s`.
* `TauCeti.RelativeDiff I M n s`: the corresponding relative diffeomorphism group,
  as a type abbreviation for that subgroup.

## Main results

* `mem_fixingSubgroup_iff`: membership is the pointwise equation `∀ x ∈ s, f x = x`.
* `fixingSubgroup_empty` / `fixingSubgroup_univ`: the empty-set fixer is all of `Diff(M)`, and
  the whole-space fixer is trivial.
* `fixingSubgroup_antitone`: fixing a larger set gives a smaller subgroup.
* `fixingSubgroup_le_stabilizer`: pointwise fixing a subset implies stabilizing it setwise.
* `toHomeomorph_mem_fixingSubgroup`: forgetting smoothness sends a relative diffeomorphism to the
  corresponding relative homeomorphism.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The relative diffeomorphism group fixing the subset `s` pointwise. -/
abbrev RelativeDiff (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (n : ℕ∞ω) (s : Set M) : Type _ :=
  _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) s

namespace Diffeomorph

/-- The subgroup of self-diffeomorphisms fixing every point of `s`.

This is Mathlib's generic `fixingSubgroup`, specialized to the tautological action of
`M ≃ₘ^n⟮I, I⟯ M` on `M`. For a boundary set this is the algebraic part of the relative
diffeomorphism group `Diff(M, ∂M)`. -/
abbrev fixingSubgroup (s : Set M) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) s

/-- Membership in the pointwise fixing subgroup is the pointwise fixedness equation on `s`. -/
@[simp]
theorem mem_fixingSubgroup_iff {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ fixingSubgroup (I := I) (n := n) s ↔ ∀ x ∈ s, f x = x := by
  simp [fixingSubgroup, _root_.mem_fixingSubgroup_iff]

/-- A member of `fixingSubgroup s` fixes each point of `s`. -/
theorem apply_eq_of_mem_fixingSubgroup {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ fixingSubgroup (I := I) (n := n) s) {x : M} (hx : x ∈ s) : f x = x :=
  (mem_fixingSubgroup_iff.mp hf) x hx

/-- To prove that a diffeomorphism lies in the pointwise fixing subgroup, prove it fixes each
point of the subset. -/
theorem mem_fixingSubgroup_of_forall {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : ∀ x ∈ s, f x = x) : f ∈ fixingSubgroup (I := I) (n := n) s :=
  mem_fixingSubgroup_iff.mpr hf

/-- The relative diffeomorphism group fixing the empty set is the full diffeomorphism group. -/
theorem fixingSubgroup_empty :
    fixingSubgroup (I := I) (M := M) (n := n) (∅ : Set M) = ⊤ := by
  exact _root_.fixingSubgroup_empty (M := M ≃ₘ^n⟮I, I⟯ M) (α := M)

/-- The relative diffeomorphism group fixing all points is trivial. -/
theorem fixingSubgroup_univ :
    fixingSubgroup (I := I) (M := M) (n := n) (Set.univ : Set M) = ⊥ := by
  exact TauCeti.fixingSubgroup_univ (G := M ≃ₘ^n⟮I, I⟯ M) (α := M)

/-- Fixing a larger set pointwise gives a smaller subgroup. -/
theorem fixingSubgroup_antitone {s t : Set M} (hst : s ⊆ t) :
    fixingSubgroup (I := I) (n := n) t ≤ fixingSubgroup (I := I) (n := n) s := by
  exact _root_.fixingSubgroup_antitone (M ≃ₘ^n⟮I, I⟯ M) M hst

/-- Pointwise fixing is invariant under replacing the subset by an equal subset. -/
theorem fixingSubgroup_congr {s t : Set M} (hst : s = t) :
    fixingSubgroup (I := I) (n := n) s = fixingSubgroup (I := I) (n := n) t := by
  subst t
  rfl

/-- The pointwise fixer of a subset is contained in its setwise stabilizer. -/
theorem fixingSubgroup_le_stabilizer (s : Set M) :
    fixingSubgroup (I := I) (n := n) s ≤
      MulAction.stabilizer (M ≃ₘ^n⟮I, I⟯ M) s := by
  exact MulAction.fixingSubgroup_le_stabilizer (M ≃ₘ^n⟮I, I⟯ M) s

/-- Fixing `s ∪ t` pointwise is the same as fixing both `s` and `t` pointwise. -/
@[simp]
theorem fixingSubgroup_union (s t : Set M) :
    fixingSubgroup (I := I) (n := n) (s ∪ t) =
      fixingSubgroup (I := I) (n := n) s ⊓ fixingSubgroup (I := I) (n := n) t := by
  exact _root_.fixingSubgroup_union (M := M ≃ₘ^n⟮I, I⟯ M) (α := M)

/-- The forgetful homomorphism to homeomorphisms sends a relative diffeomorphism to a homeomorphism
fixing the same subset pointwise. -/
theorem toHomeomorph_mem_fixingSubgroup {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ fixingSubgroup (I := I) (n := n) s) :
    f.toHomeomorph ∈ _root_.fixingSubgroup (M ≃ₜ M) s := by
  rw [_root_.mem_fixingSubgroup_iff]
  intro x hx
  exact apply_eq_of_mem_fixingSubgroup hf hx

/-- Forgetting smoothness maps the relative diffeomorphism group into the corresponding relative
homeomorphism group. -/
def toRelativeHomeomorphHom (s : Set M) :
    fixingSubgroup (I := I) (n := n) s →*
      _root_.fixingSubgroup (M ≃ₜ M) s :=
  (toHomeomorphHom (I := I) (n := n)).restrict (fixingSubgroup (I := I) (n := n) s)
    |>.codRestrict (_root_.fixingSubgroup (M ≃ₜ M) s) fun f => by
      rw [MonoidHom.restrict_apply, toHomeomorphHom_apply]
      exact toHomeomorph_mem_fixingSubgroup f.property

/-- Applying the forgetful homomorphism to a relative diffeomorphism is its underlying
homeomorphism. -/
@[simp]
theorem toRelativeHomeomorphHom_apply (s : Set M)
    (f : fixingSubgroup (I := I) (n := n) s) :
    (toRelativeHomeomorphHom (M := M) s f : M ≃ₜ M) =
      (f : M ≃ₘ^n⟮I, I⟯ M).toHomeomorph := by
  ext x
  simp [toRelativeHomeomorphHom, toHomeomorphHom_apply]

end Diffeomorph

/-- A relative diffeomorphism fixes every point of the subset defining it. -/
@[simp]
theorem RelativeDiff.apply_eq {s : Set M}
    (f : RelativeDiff (𝕜 := 𝕜) (I := I) M n s) {x : M} (hx : x ∈ s) :
    (f : M ≃ₘ^n⟮I, I⟯ M) x = x :=
  Diffeomorph.apply_eq_of_mem_fixingSubgroup f.property hx

/-- The relative diffeomorphism group inherits pointwise continuity of its action on `M`. -/
abbrev RelativeDiff.continuousConstSMul (s : Set M) :
    ContinuousConstSMul (RelativeDiff (𝕜 := 𝕜) (I := I) M n s) M :=
  inferInstance

end TauCeti
