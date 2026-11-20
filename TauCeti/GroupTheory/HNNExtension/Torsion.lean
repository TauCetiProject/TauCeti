/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Torsion
import TauCeti.GroupTheory.GraphOfGroups.OneEdge

/-!
# HNN extensions of torsion-free groups are torsion-free

The HNN extension `⟨G, t | t a t⁻¹ = φ a⟩` of a group `G` along an isomorphism `φ : A ≃* B` of two
subgroups is the fundamental group of the loop of groups with vertex group `G` and edge maps the
inclusion of `A` and `a ↦ φ a`. The fundamental group of a graph of torsion-free groups is
torsion-free (`TauCeti.GraphOfGroups.π₁Tree.isMulTorsionFree`), since its elements of finite order
are conjugate into vertex groups, so an HNN extension of a torsion-free group is torsion-free.

## Main results

* `HNNExtension.instIsMulTorsionFree`: an HNN extension of a torsion-free group is torsion-free.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12 (the Bass–Serre tree and its vertex
  stabilizers).
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Chapter IV, Theorem 2.4 (elements of
  finite order of an HNN extension are conjugate into the base group).
-/

public section

namespace HNNExtension

open TauCeti GraphOfGroups

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The second edge map `A →* G`, `a ↦ φ a`, of the loop of groups of `HNNExtension G A B φ`. -/
private abbrev loopSnd (φ : A ≃* B) : A →* G :=
  B.subtype.comp φ.toMonoidHom

private theorem loopSnd_injective : Function.Injective (loopSnd φ) :=
  B.subtype_injective.comp φ.injective

/-- The HNN extension along the identification `loopEquiv` of the loop of groups with edge maps
`A.subtype` and `loopSnd φ`, which is how `π₁Tree.equivHNNExtension` presents it. -/
private abbrev LoopHNN (φ : A ≃* B) : Type _ :=
  HNNExtension G A.subtype.range (loopSnd φ).range
    (loopEquiv _ _ A.subtype_injective loopSnd_injective)

/-- `HNNExtension G A B φ →* LoopHNN φ`, the identity on `G` and on the stable letter. -/
private noncomputable def toLoopHNN : HNNExtension G A B φ →* LoopHNN φ :=
  lift of t fun a ↦ by
    simpa [MonoidHom.ofInjective_apply] using
      t_mul_of (φ := loopEquiv _ _ A.subtype_injective (loopSnd_injective (φ := φ)))
      (MonoidHom.ofInjective A.subtype_injective a)

/-- `LoopHNN φ →* HNNExtension G A B φ`, the identity on `G` and on the stable letter. -/
private noncomputable def ofLoopHNN : LoopHNN φ →* HNNExtension G A B φ :=
  lift of t fun a ↦ by
    obtain ⟨a, rfl⟩ := (MonoidHom.ofInjective A.subtype_injective).surjective a
    simpa [MonoidHom.ofInjective_apply] using t_mul_of (φ := φ) a

private theorem ofLoopHNN_comp_toLoopHNN :
    (ofLoopHNN (φ := φ)).comp toLoopHNN = MonoidHom.id _ :=
  hom_ext (MonoidHom.ext fun _ ↦ by simp [toLoopHNN, ofLoopHNN]) (by simp [toLoopHNN, ofLoopHNN])

private theorem toLoopHNN_injective : Function.Injective (toLoopHNN (φ := φ)) :=
  Function.LeftInverse.injective (DFunLike.congr_fun ofLoopHNN_comp_toLoopHNN)

/-- **HNN extensions of torsion-free groups are torsion-free.** The HNN extension
`⟨G, t | t a t⁻¹ = φ a⟩` of a torsion-free group `G` along an isomorphism `φ : A ≃* B` of two
subgroups is torsion-free. -/
instance instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree (HNNExtension G A B φ) := by
  let 𝔸 := loop A.subtype (loopSnd φ) A.subtype_injective loopSnd_injective
  have : ∀ b, IsMulTorsionFree (𝔸.vertexGroup b) := fun _ ↦ inferInstanceAs (IsMulTorsionFree G)
  have h := π₁Tree.isMulTorsionFree (𝔸 := 𝔸) (SerreGraph.roseTree Unit)
  rw [SerreGraph.roseTree_darts] at h
  exact Function.Injective.isMulTorsionFree
    ((π₁Tree.equivHNNExtension _ _ _ _).symm.toMonoidHom.comp toLoopHNN)
    ((π₁Tree.equivHNNExtension _ _ _ _).symm.injective.comp toLoopHNN_injective)

end HNNExtension
