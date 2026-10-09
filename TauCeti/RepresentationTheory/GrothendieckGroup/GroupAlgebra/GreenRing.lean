/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
public import TauCeti.RepresentationTheory.RepresentationRing.Induction
import TauCeti.RepresentationTheory.RepresentationRing.Exact

/-!
# The Green ring maps onto the group-algebra Grothendieck ring

The Green ring imposes direct-sum relations, whereas `G₀(k[G])` imposes all short-exact-sequence
relations. The canonical comparison is therefore surjective in every characteristic. It
commutes with restriction and induction, so computations in the Green ring descend to the
exact Grothendieck ring even when representations are not semisimple.

When the group order is invertible in the coefficient field, Maschke's theorem makes the
comparison bijective. No algebraic-closure or characteristic-zero assumption is required.

The construction composes `ExactK0.fromSplitRingHom` with `fdRepK0RingEquiv`. Under the Maschke
hypothesis, `repRingEquivExactK0` identifies split and exact representation classes, so Green-ring
computations can be transported to `G₀(k[G])`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §14.1.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

section Monoid

variable (k G : Type u) [Field k] [Monoid G] [Finite G]

/-- The canonical comparison from the Green ring to `G₀(k[G])`, sending a representation's
split class to the exact class of its group-algebra module. -/
noncomputable def repRingToGroupAlgebraK0 :
    repRing k G →+* ExactK0 (finiteModulesExactStructure k[G]) :=
  (fdRepK0RingEquiv k G).toRingHom.comp
    (ExactK0.fromSplitRingHom (ExactStructure.abelian (FDRep k G)))

variable {k G}

/-- The comparison is the split-to-exact map followed by the representation–module dictionary. -/
theorem repRingToGroupAlgebraK0_apply (x : repRing k G) :
    repRingToGroupAlgebraK0 k G x =
      fdRepK0RingEquiv k G (ExactK0.fromSplit (ExactStructure.abelian (FDRep k G)) x) := by
  unfold repRingToGroupAlgebraK0
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  congr 1
  exact DFunLike.congr_fun (ExactK0.fromSplitRingHom_toAddMonoidHom
    (E := ExactStructure.abelian (FDRep k G))) x

/-- The comparison sends the split class of a representation to its group-algebra class. -/
@[simp]
theorem repRingToGroupAlgebraK0_of (V : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule V.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    repRingToGroupAlgebraK0 k G (SplitK0.of V) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.asModule V.ρ)) := by
  rw [repRingToGroupAlgebraK0_apply, ExactK0.fromSplit_of, fdRepK0RingEquiv_of]

/-- Every exact Grothendieck class is the image of a Green-ring class. -/
theorem repRingToGroupAlgebraK0_surjective :
    Function.Surjective (repRingToGroupAlgebraK0 k G) := by
  intro x
  obtain ⟨y, hy⟩ := ExactK0.fromSplit_surjective (E := ExactStructure.abelian (FDRep k G))
    ((fdRepK0RingEquiv k G).symm x)
  exact ⟨y, by rw [repRingToGroupAlgebraK0_apply, hy, RingEquiv.apply_symm_apply]⟩

/-- The Green-ring comparison commutes with restriction along a monoid homomorphism. -/
@[simp]
theorem repRingToGroupAlgebraK0_repRingRes {H : Type u} [Monoid H] [Finite H]
    (φ : H →* G) (x : repRing k G) :
    repRingToGroupAlgebraK0 k H (repRingRes k φ x) =
      resK0 k φ (repRingToGroupAlgebraK0 k G x) := by
  have h := SplitK0.hom_ext
    (f := (repRingToGroupAlgebraK0 k H).toAddMonoidHom.comp (repRingRes k φ).toAddMonoidHom)
    (g := (resK0 k φ).comp (repRingToGroupAlgebraK0 k G).toAddMonoidHom) fun V ↦ by
      simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_ofClass,
        repRingRes_of, repRingToGroupAlgebraK0_apply, ExactK0.fromSplit_of]
      exact (resK0_fdRepK0RingEquiv_of φ V).symm
  exact DFunLike.congr_fun h x

end Monoid

section Group

variable {k G : Type u} [Field k] [Group G] [Finite G]

/-- The Green-ring comparison commutes with induction from a subgroup. -/
@[simp]
theorem repRingToGroupAlgebraK0_repRingInd (S : Subgroup G) (x : repRing k S) :
    repRingToGroupAlgebraK0 k G (repRingInd k S x) =
      indK0 k S (repRingToGroupAlgebraK0 k S x) := by
  have h := SplitK0.hom_ext
    (f := (repRingToGroupAlgebraK0 k G).toAddMonoidHom.comp (repRingInd k S))
    (g := (indK0 k S).comp (repRingToGroupAlgebraK0 k S).toAddMonoidHom) fun V ↦ by
      simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_ofClass,
        repRingInd_of, repRingToGroupAlgebraK0_apply, ExactK0.fromSplit_of]
      exact (indK0_fdRepK0RingEquiv_of V).symm
  exact DFunLike.congr_fun h x

/-- If the group order is invertible in `k`, the Green ring and `G₀(k[G])` agree. -/
theorem repRingToGroupAlgebraK0_bijective [NeZero (Nat.card G : k)] :
    Function.Bijective (repRingToGroupAlgebraK0 k G) := by
  have h : ⇑(repRingToGroupAlgebraK0 k G) =
      ⇑((repRingEquivExactK0 (k := k) (G := G)).trans (fdRepK0RingEquiv k G)) := by
    funext x
    rw [repRingToGroupAlgebraK0_apply, RingEquiv.trans_apply, repRingEquivExactK0_apply]
  rw [h]
  exact RingEquiv.bijective _

end Group

end TauCeti
