/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import TauCeti.RingTheory.DeltaRing.WittSection

/-!
# The `δ`-structure on a localization

Let `A` be a `δ`-ring, `S` a submonoid of `A` and `B` a localization of `A` at `S`, with structure
map `i = algebraMap A B`. The `δ`-structure of `A` extends to a `δ`-structure on `B` for which `i`
is a `δ`-map if and only if `i (φ s)` is a unit of `B` for every `s ∈ S`, where `φ` is the
Frobenius lift of `A`; the extension is then unique. By `IsLocalization.algebraMap_isUnit_iff`,
the unit condition says that each `φ s` divides an element of `S`. It holds in particular when
`φ` maps `S` into itself.

The denominators really involve `φ s` and not only `s`: if `z = a / s` then
`i s ^ p * i (φ s) * δ z = i s ^ p * i (δ a) - i a ^ p * i (δ s)`. For instance, on the
polynomial ring `ℤ[x]` with `δ x = 1` one has `φ x = x ^ p + p`, which is not a unit of
`ℤ[x, x⁻¹]`, so inverting `x` admits no compatible `δ`-structure. On the integers, where `φ` is
the identity, every localization does; with `p = 2` the rationals get `δ (1 / 3) = 1 / 9`.

Nothing here assumes that `p` is a nonzerodivisor on `A` or `B`, or that `i` is injective. The
construction goes through the length-two Witt section `x ↦ (x, δ x)` of
`TauCeti.DeltaRing.wittSection`: the composite `A → W₂(A) → W₂(B)` sends `s ∈ S` to a vector
whose ghost components `i s` and `i (φ s)` are units, hence to a unit, so it factors through `B`.
The resulting ring homomorphism `B → W₂(B)` is a section of the zeroth coordinate, which is a
`δ`-structure on `B` by `TauCeti.DeltaRing.equivWittSection`.

## Main definitions

* `TauCeti.DeltaRing.localization`: the `δ`-structure on a localization `B` of `A` at `S`, when
  each `i (φ s)` is a unit.

## Main results

* `TauCeti.DeltaRing.isDeltaMap_algebraMap_localization`: the structure map is a `δ`-map.
* `TauCeti.DeltaRing.eq_localization`: it is the only `δ`-structure with this property.
* `TauCeti.DeltaRing.existsUnique_isDeltaMap_algebraMap_iff`: a compatible `δ`-structure on `B`
  exists, and is then unique, if and only if each `i (φ s)` is a unit.
* `TauCeti.DeltaRing.isUnit_algebraMap_frobenius_of_forall_mem`: the unit condition holds when
  `φ` maps `S` into itself.
* `TauCeti.DeltaRing.algebraMap_pow_mul_frobenius_mul_delta_mk'`: the value of `δ` on a fraction.
* `TauCeti.DeltaRing.isDeltaMap_iff_comp_algebraMap` and `TauCeti.DeltaRing.isDeltaMap_lift`:
  the universal property of the localization among `δ`-rings.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Lemma 2.15 and Remark 2.16.
-/

public section

namespace TauCeti.DeltaRing

open TruncatedWittVector

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [DeltaRing p A] {S : Submonoid A}
  {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]

section Compatible

variable [DeltaRing p B]

variable (S) in
/-- If the structure map of a localization `B` of `A` at `S` is a `δ`-map, then it sends `φ s` to
a unit for every `s ∈ S`. -/
theorem isUnit_algebraMap_frobenius (hi : IsDeltaMap p (algebraMap A B)) (s : S) :
    IsUnit (algebraMap A B (frobenius p A s)) := by
  rw [hi.map_frobenius]
  exact (IsLocalization.map_units B s).map _

/-- The value of `δ` on a fraction `z = a / s` in a localization whose structure map `i` is a
`δ`-map: `i s ^ p * i (φ s) * δ z = i s ^ p * i (δ a) - i a ^ p * i (δ s)`. The coefficient of
`δ z` is a unit as soon as `i (φ s)` is, so this determines `δ z` without dividing by `p`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.15). -/
theorem algebraMap_pow_mul_frobenius_mul_delta_mk' (hi : IsDeltaMap p (algebraMap A B)) (a : A)
    (s : S) :
    algebraMap A B s ^ p * algebraMap A B (frobenius p A s) *
        delta p (IsLocalization.mk' B a s) =
      algebraMap A B s ^ p * algebraMap A B (delta p a) -
        algebraMap A B a ^ p * algebraMap A B (delta p (s : A)) := by
  have hz := IsLocalization.mk'_spec B a s
  have h := congr(delta p $hz)
  simp only [delta_mul, ← hi.map_delta] at h
  rw [← hz, frobenius_apply]
  simp only [map_add, map_pow, map_mul, map_natCast]
  linear_combination algebraMap A B s ^ p * h

variable {C : Type*} [CommRing C] [DeltaRing p C]

variable (S) in
include S in
/-- If the structure map of a localization `B` of `A` is a `δ`-map, then a ring homomorphism out
of `B` is a `δ`-map exactly when its restriction to `A` is (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.15). -/
theorem isDeltaMap_iff_comp_algebraMap (hi : IsDeltaMap p (algebraMap A B)) (g : B →+* C) :
    IsDeltaMap p g ↔ IsDeltaMap p (g.comp (algebraMap A B)) := by
  refine ⟨fun hg => hg.comp hi, fun hg => ?_⟩
  rw [isDeltaMap_iff_wittSection_comp] at hi hg ⊢
  apply IsLocalization.ringHom_ext S
  rw [RingHom.comp_assoc, hg, map_comp, RingHom.comp_assoc, RingHom.comp_assoc, hi]

/-- The universal property of the localization among `δ`-rings: if the structure map of `B` is a
`δ`-map, then the ring homomorphism `B → C` induced by a `δ`-map `f : A → C` inverting `S` is a
`δ`-map. It is the unique ring homomorphism extending `f` (`IsLocalization.lift_unique`). -/
theorem isDeltaMap_lift (hi : IsDeltaMap p (algebraMap A B)) {f : A →+* C} (hf : IsDeltaMap p f)
    (hfS : ∀ s : S, IsUnit (f s)) : IsDeltaMap p (IsLocalization.lift hfS : B →+* C) :=
  (isDeltaMap_iff_comp_algebraMap S hi _).mpr (by rwa [IsLocalization.lift_comp])

end Compatible

/-- If `φ` maps `S` into itself, then the structure map of a localization at `S` sends `φ s` to a
unit for every `s ∈ S`. -/
theorem isUnit_algebraMap_frobenius_of_forall_mem (hS : ∀ s ∈ S, frobenius p A s ∈ S) (s : S) :
    IsUnit (algebraMap A B (frobenius p A s)) :=
  IsLocalization.map_units B ⟨_, hS s s.property⟩

section Localization

variable (h : ∀ s : S, IsUnit (algebraMap A B (frobenius p A s)))

include h in
/-- The composite of the Witt section of `A` with the coefficient map to `B` sends `S` to units,
because the ghost components of the image of `s` are `i s` and `i (φ s)`. -/
private theorem isUnit_map_wittSection (s : S) :
    IsUnit (((TruncatedWittVector.map 2 (algebraMap A B)).comp (wittSection p A)) s) := by
  rw [isUnit_iff_isUnit_ghostComponents]
  refine ⟨by simpa using IsLocalization.map_units B s, ?_⟩
  simpa [ghostComponentOne_apply, frobenius_apply] using h s

/-- The Witt section of the localized `δ`-structure: the extension of `A → W₂(A) → W₂(B)` to `B`. -/
private noncomputable def localizationWittSection : B →+* TruncatedWittVector p 2 B :=
  IsLocalization.lift (isUnit_map_wittSection h)

private theorem localizationWittSection_comp :
    (localizationWittSection h).comp (algebraMap A B) =
      (TruncatedWittVector.map 2 (algebraMap A B)).comp (wittSection p A) :=
  IsLocalization.lift_comp _

private theorem constantCoeff_comp_localizationWittSection :
    constantCoeff.comp (localizationWittSection h) = RingHom.id B := by
  apply IsLocalization.ringHom_ext S
  rw [RingHom.comp_assoc, localizationWittSection_comp]
  ext a
  simp [constantCoeff_apply]

/-- The `δ`-structure on a localization `B` of `A` at `S`, for which the structure map
`i : A → B` is a `δ`-map (`isDeltaMap_algebraMap_localization`), when `i (φ s)` is a unit for
every `s ∈ S` (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.15). It is the only
such `δ`-structure (`eq_localization`), and the unit condition is necessary for one to exist
(`existsUnique_isDeltaMap_algebraMap_iff`). -/
@[instance_reducible]
noncomputable def localization : DeltaRing p B :=
  (equivWittSection p B).symm
    ⟨localizationWittSection h, constantCoeff_comp_localizationWittSection h⟩

private theorem wittSection_localization :
    @wittSection p B _ _ (localization h) = localizationWittSection h := by
  rw [← equivWittSection_apply, localization, Equiv.apply_symm_apply]

/-- The structure map of a localization is a `δ`-map for the localized `δ`-structure. -/
theorem isDeltaMap_algebraMap_localization :
    letI := localization h
    IsDeltaMap p (algebraMap A B) := by
  let := localization h
  rw [isDeltaMap_iff_wittSection_comp, wittSection_localization, localizationWittSection_comp]

/-- The localized `δ`-structure extends the `δ`-structure of `A`. -/
theorem delta_localization_algebraMap (a : A) :
    (localization h).delta (algebraMap A B a) = algebraMap A B (delta p a) := by
  let := localization h
  exact ((isDeltaMap_algebraMap_localization h).map_delta a).symm

/-- A `δ`-structure on a localization `B` of `A` for which the structure map is a `δ`-map is the
localized `δ`-structure (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.15). -/
theorem eq_localization (d : DeltaRing p B) (hd : IsDeltaMap p (algebraMap A B)) :
    d = localization h := by
  apply (equivWittSection p B).injective
  apply Subtype.ext
  rw [equivWittSection_apply, equivWittSection_apply, wittSection_localization]
  apply IsLocalization.ringHom_ext S
  rw [localizationWittSection_comp, ← isDeltaMap_iff_wittSection_comp]
  exact hd

end Localization

variable (S B) in
/-- The `δ`-structure of `A` extends to a localization `B` of `A` at `S`, compatibly with the
structure map `i`, if and only if `i (φ s)` is a unit for every `s ∈ S`; the extension is then
unique (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.15). -/
theorem existsUnique_isDeltaMap_algebraMap_iff :
    (∃! _ : DeltaRing p B, IsDeltaMap p (algebraMap A B)) ↔
      ∀ s : S, IsUnit (algebraMap A B (frobenius p A s)) := by
  refine ⟨fun ⟨_, hd, _⟩ => isUnit_algebraMap_frobenius S hd, fun h => ?_⟩
  exact ⟨localization h, isDeltaMap_algebraMap_localization h, eq_localization h⟩

end TauCeti.DeltaRing
