/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless

/-!
# Lie groups in vector-space-valued charts

A boundaryless group manifold modeled on `I : ModelWithCorners 𝕜 E H` can be viewed as a Lie
group modeled directly on `E`, even when the range of `I` is not all of `E`.
`TauCeti.BoundarylessModel I G` retains the original group and topology. Its identity
topological multiplicative equivalence is smooth in both directions at every regularity
supported by the original group.

## Main definitions and results

* `TauCeti.BoundarylessModel.continuousMulEquiv`: the identity topological multiplicative
  equivalence.
* `TauCeti.BoundarylessModel.contMDiff_continuousMulEquiv` and its inverse: smoothness at any
  regularity.
* `TauCeti.BoundarylessModel.contMDiffMonoidMorphism` and `contMDiffMonoidMorphismSymm`: the
  smooth identity monoid morphisms in both directions, with their coercion lemmas.
* The transported `ContMDiffMul` and `LieGroup` instances, and the additive forms of all APIs.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 7 (Lie Groups), § Basic Definitions and § Lie Group Homomorphisms, pp. 151–153
  (the definitions of Lie groups and Lie-group isomorphisms, and Example 7.3(e)).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.BoundarylessModel

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) (G : Type*) [TopologicalSpace G]

/-- The model copy inherits the original multiplication. -/
@[to_additive /-- The model copy inherits the original addition. -/]
instance instMul [Mul G] : Mul (BoundarylessModel I G) := inferInstanceAs (Mul G)

/-- The model copy inherits the original monoid operations. -/
@[to_additive /-- The model copy inherits the original additive monoid operations. -/]
instance instMonoid [Monoid G] : Monoid (BoundarylessModel I G) := inferInstanceAs (Monoid G)

/-- The model copy inherits the original group operations. -/
@[to_additive /-- The model copy inherits the original additive group operations. -/]
instance instGroup [Group G] : Group (BoundarylessModel I G) := inferInstanceAs (Group G)

section Mul

variable [Mul G]

/-- The identity topological multiplicative equivalence to the vector-model copy. -/
@[to_additive /-- The identity topological additive equivalence to the vector-model copy. -/]
def continuousMulEquiv : G ≃ₜ* BoundarylessModel I G :=
  { homeomorph I G with
    map_mul' x y := by
      -- Present the structure field as the public homeomorphism application.
      change homeomorph I G (x * y) = homeomorph I G x * homeomorph I G y
      rw [homeomorph_apply, homeomorph_apply, homeomorph_apply]
      -- instMul copies G's multiplication definitionally.
      rfl }

/-- The multiplicative equivalence has the identity homeomorphism as its underlying map. -/
@[to_additive (attr := simp)
  /-- The additive equivalence has the identity homeomorphism as its underlying map. -/]
theorem coe_continuousMulEquiv : ⇑(continuousMulEquiv I G) = homeomorph I G :=
  (rfl)

/-- The inverse multiplicative equivalence has the inverse identity homeomorphism as its
underlying map. -/
@[to_additive (attr := simp)
  /-- The inverse additive equivalence has the inverse identity homeomorphism as its map. -/]
theorem coe_continuousMulEquiv_symm : ⇑(continuousMulEquiv I G).symm = (homeomorph I G).symm :=
  (rfl)

variable [ChartedSpace H G] [BoundarylessManifold I G]

/-- The identity multiplicative equivalence is smooth at every regularity. -/
@[to_additive /-- The identity additive equivalence is smooth at every regularity. -/]
theorem contMDiff_continuousMulEquiv (n : ℕ∞ω) :
    ContMDiff I 𝓘(𝕜, E) n (continuousMulEquiv I G) := by
  simpa only [coe_diffeomorph, coe_continuousMulEquiv] using (diffeomorph I (M := G) n).contMDiff

/-- The inverse identity multiplicative equivalence is smooth at every regularity. -/
@[to_additive /-- The inverse identity additive equivalence is smooth at every regularity. -/]
theorem contMDiff_continuousMulEquiv_symm (n : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, E) I n (continuousMulEquiv I G).symm := by
  simpa only [coe_diffeomorph_symm, coe_continuousMulEquiv_symm] using
    (diffeomorph I (M := G) n).symm.contMDiff

/-- Changing to vector-space-valued charts preserves smooth multiplication. -/
@[to_additive /-- Changing to vector-space-valued charts preserves smooth addition. -/]
instance {n : ℕ∞ω} [ContMDiffMul I n G] :
    ContMDiffMul 𝓘(𝕜, E) n (BoundarylessModel I G) where
  contMDiff_mul := by
    have hf := contMDiff_continuousMulEquiv I G n
    have hg := contMDiff_continuousMulEquiv_symm I G n
    exact (hf.comp ((hg.comp contMDiff_fst).mul (hg.comp contMDiff_snd))).congr fun p => by
      simp only [Pi.mul_apply, Function.comp_apply, map_mul,
        ContinuousMulEquiv.apply_symm_apply]

end Mul

section Monoid

variable [Monoid G] [ChartedSpace H G] [BoundarylessManifold I G]

/-- The identity smooth monoid morphism to the vector-model copy. -/
@[to_additive /-- The identity smooth additive monoid morphism to the vector-model copy. -/]
def contMDiffMonoidMorphism (n : ℕ∞ω) :
    ContMDiffMonoidMorphism I 𝓘(𝕜, E) n G (BoundarylessModel I G) where
  toMonoidHom := (continuousMulEquiv I G).toMonoidHom
  contMDiff_toFun := contMDiff_continuousMulEquiv I G n

/-- The identity smooth monoid morphism from the vector-model copy. -/
@[to_additive /-- The identity smooth additive monoid morphism from the vector-model copy. -/]
def contMDiffMonoidMorphismSymm (n : ℕ∞ω) :
    ContMDiffMonoidMorphism 𝓘(𝕜, E) I n (BoundarylessModel I G) G where
  toMonoidHom := (continuousMulEquiv I G).symm.toMonoidHom
  contMDiff_toFun := contMDiff_continuousMulEquiv_symm I G n

/-- The smooth forward morphism has the underlying continuous multiplicative equivalence. -/
@[to_additive (attr := simp)
  /-- The smooth forward additive morphism has the underlying continuous additive equivalence. -/]
theorem coe_contMDiffMonoidMorphism (n : ℕ∞ω) :
    ⇑(contMDiffMonoidMorphism I G n) = continuousMulEquiv I G :=
  (rfl)

/-- The smooth inverse morphism has the inverse continuous multiplicative equivalence. -/
@[to_additive (attr := simp)
  /-- The smooth inverse additive morphism has the inverse continuous additive equivalence. -/]
theorem coe_contMDiffMonoidMorphismSymm (n : ℕ∞ω) :
    ⇑(contMDiffMonoidMorphismSymm I G n) = (continuousMulEquiv I G).symm :=
  (rfl)

end Monoid

variable [Group G] [ChartedSpace H G] [BoundarylessManifold I G]

/-- Changing to vector-space-valued charts preserves the Lie-group structure. -/
@[to_additive /-- Changing to vector-space-valued charts preserves the additive Lie-group
structure. -/]
instance {n : ℕ∞ω} [LieGroup I n G] : LieGroup 𝓘(𝕜, E) n (BoundarylessModel I G) where
  toContMDiffMul := inferInstance
  contMDiff_inv := by
    have hf := contMDiff_continuousMulEquiv I G n
    have hg := contMDiff_continuousMulEquiv_symm I G n
    exact (hf.comp hg.inv).congr fun p => by
      simp only [Function.comp_apply, map_inv, ContinuousMulEquiv.apply_symm_apply]

end TauCeti.BoundarylessModel
