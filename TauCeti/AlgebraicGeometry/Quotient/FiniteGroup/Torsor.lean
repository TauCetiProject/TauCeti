/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Free

/-!
# The torsor square of a free finite-group quotient

For a finite group `G` acting on a commutative ring `A`, the action graphs give a canonical map
from the disjoint union of copies of `Spec A` to `Spec A ×_{Spec Aᴳ} Spec A`. This map is an
isomorphism exactly when the action is free scheme-theoretically: for each `g ≠ 1`, the
differences `g • a - a` generate the unit ideal.

Together with the finite étale surjectivity of the invariant-spectrum projection, this identifies
the quotient as a torsor under the constant group scheme. The pullback square
`isPullback_of_free` records both maps of its action relation, so it can be used for descent
without replacing scheme morphisms by geometric points. In particular, over a disconnected test
scheme the group element relating two lifts can vary between components.

The proof uses the existing Chase–Harrison–Rosenberg isomorphism
`TauCeti.MulSemiringAction.tensorToPi_bijective`, Mathlib's `sigmaSpec`, and `pullbackSpecIso`.
No reducedness, finite-type or invertible-order hypothesis is required.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AffineInvariantQuotient

universe u v

section Group

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A]

/-- On coordinate rings, the action map is the Galois map `a ⊗ b ↦ (a * g • b)_g`,
with the product reindexed in the universe of `A`. -/
private theorem actionMap_eq [Small.{u} G] : actionMap A G =
    (Sigma.reindex (equivShrink.{u} G) (fun _ : Shrink.{u} G ↦ Spec (CommRingCat.of A))).hom ≫
      sigmaSpec (fun _ : Shrink.{u} G ↦ CommRingCat.of A) ≫
      Spec.map (CommRingCat.ofHom
        ((RingEquiv.piCongrLeft' (fun _ : G ↦ A) (equivShrink.{u} G)).toRingHom.comp
          (MulSemiringAction.tensorToPi (FixedPoints.subring A G) A G).toRingHom)) ≫
      (pullbackSpecIso (FixedPoints.subring A G) A A).inv ≫
      (pullback.congrHom (projection_def A G) (projection_def A G)).inv := by
  apply Sigma.hom_ext
  intro g
  have hι := Sigma.ι_reindex_hom (equivShrink.{u} G)
    (fun _ : Shrink.{u} G ↦ Spec (CommRingCat.of A)) g
  dsimp only [Function.comp_def] at hι
  rw [← Category.assoc, hι]
  apply pullback.hom_ext
  · simp only [ι_actionMap_assoc, pullback.lift_fst, Category.assoc,
      ι_sigmaSpec_assoc, pullback.congrHom_inv, Category.comp_id,
      pullbackSpecIso_inv_fst, ← Spec.map_comp]
    rw [← Spec.map_id (CommRingCat.of A)]
    congr 1
    ext a
    simp
  · simp only [ι_actionMap_assoc, pullback.lift_snd, Category.assoc,
      ι_sigmaSpec_assoc, pullback.congrHom_inv, Category.comp_id,
      pullbackSpecIso_inv_snd, specComap_def, ← Spec.map_comp]
    congr 1
    ext a
    simp

/-- **The torsor criterion for an affine finite-group quotient.** The action relation is the
kernel pair of the quotient projection exactly when every nonidentity element has empty
scheme-theoretic fixed locus. -/
theorem isIso_actionMap_iff [Finite G] : IsIso (actionMap A G) ↔
    ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤ := by
  have : Finite (Shrink.{u} G) := Finite.of_equiv G (equivShrink.{u} G)
  simp only [actionMap_eq, isIso_comp_left_iff, isIso_comp_right_iff, isIso_SpecMap_iff,
    CommRingCat.hom_ofHom, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [Function.Bijective.of_comp_iff'
    (RingEquiv.piCongrLeft' (fun _ : G ↦ A) (equivShrink.{u} G)).bijective]
  exact ⟨fun h ↦ MulSemiringAction.tensorToPi_surjective_iff.mp h.2,
    fun h ↦ MulSemiringAction.tensorToPi_bijective h⟩

/-- **The torsor square.** For a free finite-group action, the two maps from the disjoint union
of copies of `Spec A` exhibit the kernel pair of the finite étale quotient projection. -/
theorem isPullback_of_free [Finite G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    IsPullback (Sigma.desc (fun _ : G ↦ 𝟙 (Spec (CommRingCat.of A))))
      (Sigma.desc (fun g : G ↦ specComap A G g)) (projection A G) (projection A G) := by
  have := (isIso_actionMap_iff A G).mpr hG
  exact IsPullback.of_iso_pullback ⟨by ext g; simp⟩ (asIso (actionMap A G))
    (actionMap_fst A G) (actionMap_snd A G)

end Group

end TauCeti.AffineInvariantQuotient
