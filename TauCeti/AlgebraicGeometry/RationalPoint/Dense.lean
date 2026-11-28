/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Dense sets of rational points in scheme products

Over a field, the product of two dense sets of rational points is dense in the scheme fibre
product. This allows a closed condition on a scheme product to be tested on pairs from the
two dense sets.

## References

* The Stacks Project, Lemma [047B](https://stacks.math.columbia.edu/tag/047B).
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.Over

universe u

variable {K : Type u} [Field K]

/-- The points obtained by pairing two dense sets of rational points are dense in the fibre
product of schemes over a field. -/
theorem dense_image_lift_of_dense {X Y : Over (Spec (.of K))}
    {s : Set (𝟙_ (Over (Spec (.of K))) ⟶ X)} {t : Set (𝟙_ (Over (Spec (.of K))) ⟶ Y)}
    (hs : Dense ((fun p ↦ p.left (IsLocalRing.closedPoint K)) '' s))
    (ht : Dense ((fun p ↦ p.left (IsLocalRing.closedPoint K)) '' t)) :
    Dense ((fun p : (𝟙_ (Over (Spec (.of K))) ⟶ X) × (𝟙_ (Over (Spec (.of K))) ⟶ Y) ↦
      (lift p.1 p.2).left (IsLocalRing.closedPoint K)) '' (s ×ˢ t)) := by
  let point : (𝟙_ (Over (Spec (.of K)))).left := IsLocalRing.closedPoint K
  have : UniversallyOpen (snd X Y).left := by
    rw [Over.snd_left]
    infer_instance
  refine dense_iff_inter_open.mpr fun U hU hne ↦ ?_
  obtain ⟨_, ⟨b, hb, rfl⟩, w, hw, hwb⟩ :=
    ht.exists_mem_open ((snd X Y).left.isOpenMap _ hU) (hne.image _)
  -- The fibre over the rational point `b` is the image of the slice of the product at `b`.
  have hwRange : w ∈ Set.range (X ◁ b).left := by
    rw [Over.whiskerLeft_left, Scheme.Pullback.range_map, ← Over.fst_left, ← Over.snd_left]
    exact ⟨⟨(fst X Y).left w, by simp⟩, ⟨point, hwb.symm⟩⟩
  obtain ⟨z, hz⟩ := hwRange
  let slice : X ⟶ X ⊗ Y := (ρ_ X).inv ≫ X ◁ b
  have hslice : (slice.left ⁻¹' U).Nonempty := by
    refine ⟨(ρ_ X).hom.left z, ?_⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Over.comp_left]
    simpa [slice, hz] using hw
  obtain ⟨_, ⟨a, ha, rfl⟩, haU⟩ := hs.exists_mem_open (hU.preimage slice.left.continuous) hslice
  have hab : a ≫ slice = lift a b := by
    ext1 <;> simp [slice]
  refine ⟨(lift a b).left point, ?_, ⟨(a, b), ⟨ha, hb⟩, rfl⟩⟩
  rwa [← hab, Over.comp_left, Scheme.Hom.comp_apply]

end CategoryTheory.Over
