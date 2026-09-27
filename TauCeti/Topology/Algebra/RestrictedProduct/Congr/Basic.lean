/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Right

/-!
# Changing the reference family of a restricted product

Two families of reference subgroups that agree at all but finitely many indices define the same
restricted product up to a coordinatewise-identity isomorphism, which is a homeomorphism for
every pair of families.  This file records that isomorphism, its coordinate formulas in both
directions, its continuity, its coherence laws, its naturality with respect to componentwise
maps, and its identification with the componentwise map induced by the identity homomorphisms.
It is the case of `restrictedProductCongrRight` in which every coordinate equivalence is the
identity.

The isomorphism identifies the ambient restricted products only; it need not carry the
everywhere-integral subgroup of one family onto that of the other, because the coordinate
condition can change at the finitely many indices where the families differ.  The witness
`exists_map_integralSubgroup_ne` records a counterexample to the general preservation claim.
The resulting transport of double-coset spaces is in
`TauCeti.Topology.Algebra.RestrictedProduct.Congr.DoubleCoset`.

The general statements have additive counterparts, such as `addRestrictedProductCongr`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The multiplicative equivalence between the restricted products with respect to two reference
families that agree at all but finitely many indices. It is the identity in every coordinate. -/
@[to_additive addRestrictedProductCongr /-- The additive equivalence between the restricted
products with respect to two reference families that agree at all but finitely many indices. It is
the identity in every coordinate. -/]
def restrictedProductCongr (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) :
    (Πʳ i, [G i, (U i : Set (G i))]) ≃* (Πʳ i, [G i, (U' i : Set (G i))]) :=
  restrictedProductCongrRight U U' (fun i ↦ MulEquiv.refl (G i)) <| by
    filter_upwards [h] with i hi
    simp only [MulEquiv.coe_refl, hi]
    exact Set.bijOn_id _

/-- The change-of-family equivalence is the identity in every coordinate. -/
@[to_additive (attr := simp) addRestrictedProductCongr_apply]
theorem restrictedProductCongr_apply (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (x : Πʳ i, [G i, (U i : Set (G i))]) (i : ι) :
    restrictedProductCongr U U' h x i = x i :=
  restrictedProductCongrRight_apply U U' _ _ x i

/-- The inverse of the change-of-family equivalence is the identity in every coordinate.

Not a `simp` lemma: `simp` proves it from `restrictedProductCongr_symm` and
`restrictedProductCongr_apply`. -/
@[to_additive addRestrictedProductCongr_symm_apply]
theorem restrictedProductCongr_symm_apply (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (y : Πʳ i, [G i, (U' i : Set (G i))]) (i : ι) :
    (restrictedProductCongr U U' h).symm y i = y i :=
  restrictedProductCongrRight_symm_apply U U' _ _ y i

/-- The change-of-family equivalence is continuous, for every pair of reference families. -/
@[to_additive continuous_addRestrictedProductCongr]
theorem continuous_restrictedProductCongr [∀ i, TopologicalSpace (G i)]
    (U U' : ∀ i, Subgroup (G i)) (h : ∀ᶠ i in cofinite, U i = U' i) :
    Continuous (restrictedProductCongr U U' h) :=
  continuous_restrictedProductCongrRight U U' _ _ fun _ ↦ continuous_id

/-- The inverse of the change-of-family equivalence is continuous, for every pair of reference
families. -/
@[to_additive continuous_addRestrictedProductCongr_symm]
theorem continuous_restrictedProductCongr_symm [∀ i, TopologicalSpace (G i)]
    (U U' : ∀ i, Subgroup (G i)) (h : ∀ᶠ i in cofinite, U i = U' i) :
    Continuous (restrictedProductCongr U U' h).symm :=
  continuous_restrictedProductCongrRight_symm U U' _ _ fun _ ↦ continuous_id

/-- The change-of-family equivalence from a family to itself is the identity. -/
@[to_additive (attr := simp) addRestrictedProductCongr_refl]
theorem restrictedProductCongr_refl (U : ∀ i, Subgroup (G i)) :
    restrictedProductCongr U U (.of_forall fun _ ↦ rfl) =
      MulEquiv.refl (Πʳ i, [G i, (U i : Set (G i))]) := by
  ext x i
  simp

/-- The inverse of the change-of-family equivalence is the change-of-family equivalence in the
opposite direction. -/
@[to_additive (attr := simp) addRestrictedProductCongr_symm]
theorem restrictedProductCongr_symm (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) :
    (restrictedProductCongr U U' h).symm =
      restrictedProductCongr U' U (h.mono fun _ hi ↦ hi.symm) := by
  ext x i
  simp [restrictedProductCongr_symm_apply]

/-- Two successive changes of family compose to the change of family between the outer two
families. -/
@[to_additive (attr := simp) addRestrictedProductCongr_trans]
theorem restrictedProductCongr_trans (U U' U'' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) (h' : ∀ᶠ i in cofinite, U' i = U'' i) :
    (restrictedProductCongr U U' h).trans (restrictedProductCongr U' U'' h') =
      restrictedProductCongr U U'' (by
        filter_upwards [h, h'] with i hi hi'
        exact hi.trans hi') := by
  ext x i
  simp

/-- Naturality of the change-of-family equivalence with respect to componentwise maps: changing
the family before or after applying a componentwise map gives the same homomorphism. -/
@[to_additive addRestrictedProductCongr_naturality]
theorem restrictedProductCongr_naturality {H : ι → Type w} [∀ i, Group (H i)]
    (U U' : ∀ i, Subgroup (G i)) (V V' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (V i))
    (h : ∀ᶠ i in cofinite, U i = U' i) (h' : ∀ᶠ i in cofinite, V i = V' i) :
    (restrictedProductCongr V V' h' : _ →* _).comp (restrictedProductMap U V φ hφ) =
      (restrictedProductMap U' V' φ (by
        filter_upwards [hφ, h, h'] with i hi hU hV
        rwa [← hU, ← hV])).comp (restrictedProductCongr U U' h : _ →* _) := by
  ext x i
  simp

/-- As a monoid homomorphism, the change-of-family equivalence is the componentwise map induced
by the identity homomorphisms. -/
@[to_additive coe_addMonoidHom_addRestrictedProductCongr]
theorem coe_monoidHom_restrictedProductCongr (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) :
    (restrictedProductCongr U U' h :
        (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]) =
      restrictedProductMap U U' (fun _ ↦ MonoidHom.id _) (h.mono fun _ hi _ hx ↦ hi ▸ hx) := by
  ext x i
  simp

/-- The change-of-family equivalence need not carry the everywhere-integral subgroup onto the
everywhere-integral subgroup of the new family. The witness is that of
`exists_not_map_integralSubgroup_le`: copies of `Multiplicative ℤ` indexed by `ℕ`, with the first
family everywhere `⊤` and the second family equal to `⊥` at zero and `⊤` elsewhere. -/
theorem exists_map_integralSubgroup_ne :
    ∃ (U U' : ℕ → Subgroup (Multiplicative ℤ)) (h : ∀ᶠ i in cofinite, U i = U' i),
      (integralSubgroup U).map (restrictedProductCongr U U' h) ≠ integralSubgroup U' := by
  obtain ⟨U, U', h, hne⟩ := exists_not_map_integralSubgroup_le
  refine ⟨U, U', h, fun heq ↦ hne ?_⟩
  rw [← coe_monoidHom_restrictedProductCongr U U' h, heq]

end TauCeti
