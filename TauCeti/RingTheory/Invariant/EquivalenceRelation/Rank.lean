/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Local
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.LocalRing.Module

/-!
# The rank of a finite locally free equivalence relation is constant on orbits

Let `s = algebraMap A B` and `t : A →+* B` define an equivalence relation `Spec B ⇉ Spec A`
(`RingHom.IsSpecEquivRel`) with `B` finite flat over `A` through `s`. This file proves that the
rank of `B` over `A` is constant on the orbits of the relation: for every point `r` of `Spec B`,
the rank of `B` at `s⁻¹ r` equals its rank at `t⁻¹ r`
(`RingHom.IsSpecEquivRel.rankAtStalk_comap_eq`).
Geometrically, if `r` relates `u` to `v`, composition with `r` identifies the pairs related to
`u` with the pairs related to `v`, so the fibres of `s` over `u` and over `v` have the same degree.

Algebraically, this identification is an isomorphism between the two base changes
`B ⊗_{s, A, s} B` and `B ⊗_{t, A, s} B` of `s` to `Spec B`: the shear
`((u, v), (u, w)) ↦ ((u, v), (v, w))`, built from transitivity and symmetry of the relation. Hence
the square formed by `s`, `t`, the shear of the first factor and the inclusion of the second
factor into `B ⊗_{s, A, s} B` is a pushout, and the rank of a base change of a finite flat
algebra is computed at the image point (`CommRingCat.finrank_eq_of_isPushout`).

When `B` is finite projective over `A`, the points of `Spec A` with the same image in the
spectrum of the ring of invariants `C = {a : s a = t a}` are related
(`RingHom.IsSpecEquivRel.comap_subtype_eqLocus_eq_iff`), so the rank is constant on the fibres of
`Spec A ⟶ Spec C` (`RingHom.IsSpecEquivRel.rankAtStalk_eq_of_comap_eq`). If moreover `C` is
local, then `A` is semilocal and all its maximal ideals lie over the closed point of `Spec C`, so
`B` has the same rank at every maximal ideal of `A` and is therefore free over `A`
(`RingHom.IsSpecEquivRel.free_of_projective_of_isLocalRing`). This reduces the local case of the
quotient of an affine scheme by a finite locally free equivalence relation (SGA 3, Exposé V,
Théorème 4.1), in which `B` is finite projective over `A`, to the case in which `B` is finite
free over `A`, treated in `TauCeti.RingTheory.Invariant.EquivalenceRelation.Local`.

## Main results

* `RingHom.IsSpecEquivRel.rankAtStalk_comap_eq`: if `B` is finite flat over `A`, its rank at
  `s⁻¹ r` equals its rank at `t⁻¹ r` for every point `r` of `Spec B`.
* `RingHom.IsSpecEquivRel.rankAtStalk_eq_of_comap_eq`: if `B` is finite projective over `A`, its
  rank is constant on the fibres of `Spec A ⟶ Spec C`.
* `RingHom.IsSpecEquivRel.free_of_projective_of_isLocalRing`: if `B` is finite projective over
  `A` and `C` is local, then `B` is free over `A`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

universe u

open CategoryTheory Limits

namespace RingHom.IsSpecEquivRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (h : (algebraMap A B).IsSpecEquivRel t)
include h

/-! ### The shear isomorphism

Write `P₁ = B ⊗_{s, A, s} B` and `P₂ = B ⊗_{t, A, s} B` for the pushouts in `CommRingCat`, with
`i` the inclusion of the first factor and `j` that of the second factor. A point of `P₁` is a
pair `((u, v), (u, w))` of related pairs with a common source, through `j` and `i`
respectively, and a point of `P₂` is a pair `((u, v), (v, w))` of composable related pairs,
through `j` and `i` respectively. The shear `((u, v), (u, w)) ↦ ((u, v), (v, w))` is an
isomorphism `P₁ ≅ P₂` under the second factor. -/

-- the shear from `P₂` to `P₁` on the first factor: the related pair `(v, w)` given by
-- composing `(v, u)`, the inverse of the second factor, with the first factor `(u, w)`
private theorem exists_comp_eq_of_comp_algebraMap_eq {P : Type u} [CommRing P] (i j : B →+* P)
    (hij : i.comp (algebraMap A B) = j.comp (algebraMap A B)) :
    ∃ z : B →+* P, z.comp (algebraMap A B) = j.comp t ∧ z.comp t = i.comp t := by
  obtain ⟨z, hzs, hzt⟩ := h.trans (j.comp (h.inv : B →+* B)) i (by
    ext a
    simpa using congr($hij a).symm)
  refine ⟨z, ?_, hzt⟩
  rw [hzs]
  ext a
  simp

/-- The base changes `B ⊗_{s, A, s} B` and `B ⊗_{t, A, s} B` of `s` to `Spec B` agree: the square
formed by `s`, `t`, the shear `z` of the first factor and the inclusion of the second factor into
`B ⊗_{s, A, s} B` is a pushout in `CommRingCat`. -/
private theorem exists_isPushout :
    ∃ z : CommRingCat.of B ⟶
        pushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)),
      IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom t) z
        (pushout.inr (CommRingCat.ofHom (algebraMap A B))
          (CommRingCat.ofHom (algebraMap A B))) := by
  set S := CommRingCat.ofHom (algebraMap A B)
  set T := CommRingCat.ofHom t
  set i₁ := pushout.inl S S
  set j₁ := pushout.inr S S
  set i₂ := pushout.inl S T
  set j₂ := pushout.inr S T
  have hw₁ : i₁.hom.comp (algebraMap A B) = j₁.hom.comp (algebraMap A B) :=
    congr(CommRingCat.Hom.hom $(pushout.condition (f := S) (g := S)))
  have hw₂ : i₂.hom.comp (algebraMap A B) = j₂.hom.comp t :=
    congr(CommRingCat.Hom.hom $(pushout.condition (f := S) (g := T)))
  obtain ⟨z, hzs, hzt⟩ := h.exists_comp_eq_of_comp_algebraMap_eq i₁.hom j₁.hom hw₁
  -- the shear from `P₁` to `P₂` on the first factor: the related pair `(u, w)` given by
  -- composing the second factor `(u, v)` with the first factor `(v, w)`
  obtain ⟨z', hz's, hz't⟩ := h.trans j₂.hom i₂.hom hw₂.symm
  -- the two shears `ψ : P₂ ⟶ P₁` and `φ : P₁ ⟶ P₂`
  let ψ : pushout S T ⟶ pushout S S :=
    pushout.desc (CommRingCat.ofHom z) j₁ (CommRingCat.hom_ext hzs)
  let φ : pushout S S ⟶ pushout S T :=
    pushout.desc (CommRingCat.ofHom z') j₂ (CommRingCat.hom_ext hz's)
  have hψ₁ : pushout.inl S T ≫ ψ = CommRingCat.ofHom z := pushout.inl_desc _ _ _
  have hψ₂ : j₂ ≫ ψ = j₁ := pushout.inr_desc _ _ _
  have hφ₁ : pushout.inl S S ≫ φ = CommRingCat.ofHom z' := pushout.inl_desc _ _ _
  have hφ₂ : j₁ ≫ φ = j₂ := pushout.inr_desc _ _ _
  -- a composite `y ∘ x` restricted along `f` is determined by `x ∘ f = k ∘ g` and `y ∘ k = m`
  have comp_eq {P Q : Type u} [CommRing P] [CommRing Q] {f g : A →+* B} {x k : B →+* P}
      {y : P →+* Q} {m : B →+* Q} (hx : x.comp f = k.comp g) (hy : y.comp k = m) :
      (y.comp x).comp f = m.comp g := by
    rw [RingHom.comp_assoc, hx, ← RingHom.comp_assoc, hy]
  -- the shear of the first factor of `P₁` is the first factor of `P₂`, and conversely; both
  -- sides are determined by their two images in `Spec A`
  have hzφ : CommRingCat.ofHom z ≫ φ = i₂ :=
    CommRingCat.hom_ext (h.ext ((comp_eq hzs congr($(hφ₂).hom)).trans hw₂.symm)
      ((comp_eq hzt congr($(hφ₁).hom)).trans hz't))
  have hz'ψ : CommRingCat.ofHom z' ≫ ψ = i₁ :=
    CommRingCat.hom_ext (h.ext ((comp_eq hz's congr($(hψ₂).hom)).trans hw₁.symm)
      ((comp_eq hz't congr($(hψ₁).hom)).trans hzt))
  let e : pushout S S ≅ pushout S T :=
    { hom := φ
      inv := ψ
      hom_inv_id := pushout.hom_ext (by rw [reassoc_of% hφ₁, hz'ψ, Category.comp_id])
        (by rw [reassoc_of% hφ₂, hψ₂, Category.comp_id])
      inv_hom_id := pushout.hom_ext (by rw [reassoc_of% hψ₁, hzφ, Category.comp_id])
        (by rw [reassoc_of% hψ₂, hφ₂, Category.comp_id]) }
  exact ⟨CommRingCat.ofHom z,
    .of_iso_pushout ⟨CommRingCat.hom_ext hzs⟩ e hzφ hφ₂⟩

/-! ### Rank on orbits -/

/-- **The rank is constant on orbits.** Let `Spec B ⇉ Spec A` be an equivalence relation with `B`
finite flat over `A` through `s`. For every point `r` of `Spec B`, relating `s⁻¹ r` to `t⁻¹ r`,
the rank of `B` over `A` at `s⁻¹ r` equals its rank at `t⁻¹ r`. -/
theorem rankAtStalk_comap_eq [Module.Finite A B] [Module.Flat A B] (r : PrimeSpectrum B) :
    Module.rankAtStalk B (r.comap (algebraMap A B)) = Module.rankAtStalk B (r.comap t) := by
  obtain ⟨z, hz⟩ := h.exists_isPushout
  have hflat : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hfin : (algebraMap A B).Finite := RingHom.finite_algebraMap.mpr inferInstance
  -- both squares compute the rank of the second factor of `B ⊗_{s, A, s} B` at `r`
  have h₁ := CommRingCat.finrank_eq_of_isPushout
    (.of_hasPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)))
    hflat hfin r
  have h₂ := CommRingCat.finrank_eq_of_isPushout hz hflat hfin r
  simpa using h₁.symm.trans h₂

/-- **The rank is constant on the fibres of the quotient map.** Let `Spec B ⇉ Spec A` be an
equivalence relation with `B` finite projective over `A` through `s`. If two points `q` and `q'`
of `Spec A` have the same image in `Spec C`, for the ring of invariants `C = {a : s a = t a}`, then
`B` has the same rank over `A` at `q` and at `q'`. -/
theorem rankAtStalk_eq_of_comap_eq [Module.Finite A B] [Module.Projective A B]
    {q q' : PrimeSpectrum A}
    (hqq' : q.comap ((algebraMap A B).eqLocus t).subtype =
      q'.comap ((algebraMap A B).eqLocus t).subtype) :
    Module.rankAtStalk B q = Module.rankAtStalk B q' := by
  obtain ⟨r, rfl, rfl⟩ := h.comap_subtype_eqLocus_eq_iff.mp hqq'
  exact h.rankAtStalk_comap_eq r

/-- **Freeness over a local ring of invariants.** Let `Spec B ⇉ Spec A` be an equivalence relation
with `B` finite projective over `A` through `s`, whose ring of invariants `C = {a : s a = t a}` is
local. Then `B` is a free `A`-module: `A` is semilocal, and `B` has the same rank at all maximal
ideals of `A`, since they all lie over the closed point of `Spec C`. -/
theorem free_of_projective_of_isLocalRing [Module.Finite A B] [Module.Projective A B]
    [IsLocalRing ((algebraMap A B).eqLocus t)] : Module.Free A B := by
  set C := (algebraMap A B).eqLocus t
  have := h.finite_maximalSpectrum
  have := h.isIntegral
  -- every maximal ideal of `A` lies over the maximal ideal of `C`
  have hmax (q : MaximalSpectrum A) :
      q.toPrimeSpectrum.comap C.subtype = IsLocalRing.closedPoint C :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under C q.asIdeal))
  rcases isEmpty_or_nonempty (MaximalSpectrum A) with hA | ⟨⟨q₀⟩⟩
  · exact Module.free_of_flat_of_finrank_eq A B 0 fun q ↦ isEmptyElim q
  · exact Module.free_of_flat_of_finrank_eq A B (Module.rankAtStalk B q₀.toPrimeSpectrum)
      fun q ↦ (Module.finrank_quotient_tensorProduct_eq_rankAtStalk B q).trans
        (h.rankAtStalk_eq_of_comap_eq ((hmax q).trans (hmax q₀).symm))

end RingHom.IsSpecEquivRel
