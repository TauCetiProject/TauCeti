/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Basic

/-!
# Fibres of maps of simplicial joins

A lift of `p : X ⟶ K' ⋆ L'` through `join.map f g` amounts to independent lifts of the two
components of its join data through `f` and `g` (`SSet.join.liftEquiv`). The corresponding
bijection on join data commutes with restriction and postcomposition
(`SSet.JoinData.postcompEquiv_precomp`, `SSet.JoinData.postcompEquiv_postcomp`).

The inverse images of the two factors under a map of joins are the corresponding factors.
These results allow one to recover the factors of an iterated join from its projection to a
join of standard simplices, handling the lift problems on each vertex fibre independently.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8 (the simplicial join).
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable {X Y K L K' L' : SSet.{u}}

namespace JoinData

/-- Lifts of join data along postcomposition are pairs of lifts of their two components. -/
noncomputable def postcompEquiv (f : K ⟶ K') (g : L ⟶ L') (d : JoinData X K' L') :
    {e : JoinData X K L // e.postcomp f g = d} ≃
      ({a : (joinFiber d.p 0 : SSet) ⟶ K // a ≫ f = d.left} ×
        {b : (joinFiber d.p 1 : SSet) ⟶ L // b ≫ g = d.right}) := by
  obtain ⟨p, l, r⟩ := d
  let assemble := fun ab :
      ({a : (joinFiber p 0 : SSet) ⟶ K // a ≫ f = l} ×
        {b : (joinFiber p 1 : SSet) ⟶ L // b ≫ g = r}) ↦
    (⟨⟨p, ab.1.val, ab.2.val⟩, by
      rw [postcomp_mk, ab.1.property, ab.2.property]⟩ :
      {e : JoinData X K L // e.postcomp f g = ⟨p, l, r⟩})
  refine (Equiv.ofBijective assemble ⟨?_, ?_⟩).symm
  · intro ab cd h
    have hd := congrArg Subtype.val h
    have hl : ab.1.val = cd.1.val := by
      ext n ⟨x, hx⟩
      exact congr_left_app hd x hx hx
    have hr : ab.2.val = cd.2.val := by
      ext n ⟨x, hx⟩
      exact congr_right_app hd x hx hx
    exact Prod.ext (Subtype.ext hl) (Subtype.ext hr)
  · rintro ⟨⟨q, a, b⟩, h⟩
    obtain rfl : q = p := by simpa only [postcomp_p] using congrArg JoinData.p h
    rw [postcomp_mk] at h
    have ha : a ≫ f = l := by
      ext n ⟨x, hx⟩
      exact congr_left_app h x hx hx
    have hb : b ≫ g = r := by
      ext n ⟨x, hx⟩
      exact congr_right_app h x hx hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext rfl⟩

@[simp]
lemma postcompEquiv_symm_coe (f : K ⟶ K') (g : L ⟶ L') (d : JoinData X K' L')
    (ab : ({a : (joinFiber d.p 0 : SSet) ⟶ K // a ≫ f = d.left} ×
      {b : (joinFiber d.p 1 : SSet) ⟶ L // b ≫ g = d.right})) :
    ((postcompEquiv f g d).symm ab).val = ⟨d.p, ab.1.val, ab.2.val⟩ := by
  cases d
  rfl

/-- The relative universal property commutes with restriction of join data. -/
lemma postcompEquiv_precomp (f : K ⟶ K') (g : L ⟶ L') (d : JoinData X K' L')
    (e : {e : JoinData X K L // e.postcomp f g = d}) (h : Y ⟶ X) :
    postcompEquiv f g (d.precomp h)
      ⟨e.val.precomp h, by rw [← precomp_postcomp, e.property]⟩ =
      (⟨(joinFiber d.p 0).fromPreimage h ≫ (postcompEquiv f g d e).1.val,
          by
            -- Normalize the common source: the fibre of a composite is a preimage.
            simpa only [precomp, joinFiber, Subcomplex.preimage_comp] using
              (Category.assoc ((joinFiber d.p 0).fromPreimage h) _ f).trans
                (congrArg (((joinFiber d.p 0).fromPreimage h) ≫ ·)
                  (postcompEquiv f g d e).1.property)⟩,
        ⟨(joinFiber d.p 1).fromPreimage h ≫ (postcompEquiv f g d e).2.val,
          by
            -- Normalize the common source: the fibre of a composite is a preimage.
            simpa only [precomp, joinFiber, Subcomplex.preimage_comp] using
              (Category.assoc ((joinFiber d.p 1).fromPreimage h) _ g).trans
                (congrArg (((joinFiber d.p 1).fromPreimage h) ≫ ·)
                  (postcompEquiv f g d e).2.property)⟩) := by
  obtain ⟨ab, rfl⟩ := (postcompEquiv f g d).symm.surjective e
  apply (postcompEquiv f g (d.precomp h)).symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, postcompEquiv_symm_coe]
  rfl

/-- The relative universal property commutes with maps of the two lifted factors. -/
lemma postcompEquiv_postcomp {A B : SSet.{u}} (a : K ⟶ A) (b : L ⟶ B)
    (f : A ⟶ K') (g : B ⟶ L') (d : JoinData X K' L')
    (e : {e : JoinData X K L // e.postcomp (a ≫ f) (b ≫ g) = d}) :
    postcompEquiv f g d ⟨e.val.postcomp a b, by rw [postcomp_postcomp, e.property]⟩ =
      (⟨(postcompEquiv (a ≫ f) (b ≫ g) d e).1.val ≫ a,
          by rw [Category.assoc, (postcompEquiv (a ≫ f) (b ≫ g) d e).1.property]⟩,
        ⟨(postcompEquiv (a ≫ f) (b ≫ g) d e).2.val ≫ b,
          by rw [Category.assoc, (postcompEquiv (a ≫ f) (b ≫ g) d e).2.property]⟩) := by
  obtain ⟨ab, rfl⟩ := (postcompEquiv (a ≫ f) (b ≫ g) d).symm.surjective e
  apply (postcompEquiv f g d).symm.injective
  apply Subtype.ext
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, postcompEquiv_symm_coe,
    postcomp_mk]

end JoinData

namespace join

/-- Lifts of a map into a join correspond to independent lifts on its two vertex fibres.
The inverse assembles the two lifts with the original map to `Δ[1]`. -/
noncomputable def liftEquiv (f : K ⟶ K') (g : L ⟶ L') (p : X ⟶ join K' L') :
    {F : X ⟶ join K L // F ≫ map f g = p} ≃
      ({a : (joinFiber (homEquiv p).p 0 : SSet) ⟶ K // a ≫ f = (homEquiv p).left} ×
        {b : (joinFiber (homEquiv p).p 1 : SSet) ⟶ L // b ≫ g = (homEquiv p).right}) :=
  (Equiv.subtypeEquiv homEquiv (fun F ↦ by
    rw [← homEquiv_comp_map, Equiv.apply_eq_iff_eq])).trans
      (JoinData.postcompEquiv f g (homEquiv p))

/-- The inverse of the relative universal property uses the given projection and the two
chosen component lifts as its join data. -/
@[simp]
lemma liftEquiv_symm_coe (f : K ⟶ K') (g : L ⟶ L') (p : X ⟶ join K' L')
    (ab : ({a : (joinFiber (homEquiv p).p 0 : SSet) ⟶ K // a ≫ f = (homEquiv p).left} ×
      {b : (joinFiber (homEquiv p).p 1 : SSet) ⟶ L // b ≫ g = (homEquiv p).right})) :
    ((liftEquiv f g p).symm ab).val = homEquiv.symm ⟨(homEquiv p).p, ab.1.val, ab.2.val⟩ := by
  simp [liftEquiv]

/-- A map of joins pulls the left factor back to the left factor. -/
@[simp]
lemma preimage_range_inl_map (f : K ⟶ K') (g : L ⟶ L') :
    (Subcomplex.range (inl K' L')).preimage (map f g) = Subcomplex.range (inl K L) := by
  simp only [range_inl, joinFiber, ← Subcomplex.preimage_comp, map_π]

/-- A map of joins pulls the right factor back to the right factor. -/
@[simp]
lemma preimage_range_inr_map (f : K ⟶ K') (g : L ⟶ L') :
    (Subcomplex.range (inr K' L')).preimage (map f g) = Subcomplex.range (inr K L) := by
  simp only [range_inr, joinFiber, ← Subcomplex.preimage_comp, map_π]

end join

end SSet
