/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.K2

/-!
# Steinberg groups and `K₂` commute with directed colimits of rings

Let `(Gᵢ, fᵢⱼ)` be a directed system of associative unital rings over a nonempty directed
preorder `ι`, with colimit Mathlib's generic `DirectLimit G f` and canonical maps
`DirectLimit.Ring.of G f i : Gᵢ →+* DirectLimit G f`.

The Steinberg group commutes with this colimit, for every index type `κ`
(`TauCeti.IndexedSteinbergGroup.directLimitEquiv`): the canonical comparison from the direct
limit of the groups `St_κ(Gᵢ)` to `St_κ(DirectLimit G f)` is an isomorphism. Its inverse sends a
generator `x_{pq}(a)` to the class of `x_{pq}(a')` for any `a'` in a stage `Gᵢ` representing `a`;
this respects the Steinberg relations because any two elements of the colimit, together with
their sum and their product, are represented in a single stage.

Algebraic `K₂` commutes with the colimit too (`TauCeti.AlgebraicK2.directLimitEquiv`): the direct
limit of the groups `K₂(Gᵢ)` is `K₂(DirectLimit G f)`. Surjectivity uses the Steinberg
isomorphism to represent an element of `K₂` of the colimit by an element `w` of some `St(Gᵢ)`.
The image of `w` in `GL_∞(Gᵢ)` becomes trivial in the colimit, hence already at some later stage
`Gⱼ` (`TauCeti.StableGeneralLinearGroup.exists_map_eq_one_of_map_ringOf_eq_one`), where `w`
therefore lies in `K₂(Gⱼ)`. Injectivity is the corresponding statement for the Steinberg group,
read off from its isomorphism. Both finite-stage statements are recorded separately: every
element of `K₂(DirectLimit G f)` comes from some `K₂(Gᵢ)`
(`TauCeti.AlgebraicK2.exists_map_ringOf_eq`), and an element of `K₂(Gᵢ)` with trivial image in
the colimit is already trivial in some `K₂(Gⱼ)`
(`TauCeti.AlgebraicK2.exists_map_eq_one_of_map_ringOf_eq_one`).

## Main definitions

* `TauCeti.IndexedSteinbergGroup.directLimitEquiv`: `St_κ` commutes with directed colimits of
  rings.
* `TauCeti.AlgebraicK2.directLimitEquiv`: `K₂` commutes with directed colimits of rings.

## Main results

* `TauCeti.IndexedSteinbergGroup.exists_map_ringOf_eq`,
  `TauCeti.IndexedSteinbergGroup.exists_map_eq_one_of_map_ringOf_eq_one`: every element of
  `St_κ(DirectLimit G f)` comes from a stage, and an element of a stage with trivial image in the
  colimit is trivial at a later stage.
* `TauCeti.AlgebraicK2.exists_map_ringOf_eq`,
  `TauCeti.AlgebraicK2.exists_map_eq_one_of_map_ringOf_eq_one`: the same two statements for `K₂`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  for the Steinberg group and `K₂`.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definitions 5.1 and 5.2.
-/

public section

noncomputable section

namespace TauCeti

open _root_.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  (G : ι → Type*) [∀ i, Ring (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
  [DirectedSystem G (f · · ·)]

/-- Every element of the direct limit of a directed system of rings is the image of an element of
a stage. -/
private theorem exists_ringOf (a : _root_.DirectLimit G f) : ∃ i a', Ring.of G f i a' = a := by
  obtain ⟨i, a', rfl⟩ := exists_eq_mk f a
  exact ⟨i, a', Ring.of_apply ..⟩

/-- Two elements of the direct limit of a directed system of rings are the images of two elements
of a single stage. -/
private theorem exists_ringOf₂ (a b : _root_.DirectLimit G f) :
    ∃ i a' b', Ring.of G f i a' = a ∧ Ring.of G f i b' = b := by
  obtain ⟨i, a', b', rfl, rfl⟩ := exists_eq_mk₂ f a b
  exact ⟨i, a', b', Ring.of_apply .., Ring.of_apply ..⟩

namespace IndexedSteinbergGroup

variable {κ : Type*}

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The Steinberg groups of a directed system of rings, along the induced homomorphisms, form a
directed system of groups. -/
instance : DirectedSystem (fun i ↦ IndexedSteinbergGroup κ (G i)) (fun i j h ↦ map (f i j h)) where
  map_self i z := by rw [DirectedSystem.ringHom_self f, map_id, MonoidHom.id_apply]
  map_map k j i hij hjk z := by rw [map_map, DirectedSystem.ringHom_comp]

/-- The direct limit of the Steinberg groups `St_κ(Gᵢ)`. -/
local notation "StLim" => _root_.DirectLimit (fun i ↦ IndexedSteinbergGroup κ (G i))
  (fun i j h ↦ map (f i j h))

/-- The canonical map from `St_κ(Gᵢ)` to the direct limit of the Steinberg groups. -/
local notation "ofLim" => DirectLimit.Monoid.of (fun i ↦ IndexedSteinbergGroup κ (G i))
  (fun i j h ↦ map (f i j h))

/-- The image in the direct limit of the groups `St_κ(Gᵢ)` of the generator `x_{pq}(a)`, for `a`
in the direct limit of the rings, computed from any representative of `a` in a stage. -/
private def genLim {p q : κ} (hpq : p ≠ q) (a : _root_.DirectLimit G f) : StLim :=
  _root_.DirectLimit.lift f (fun i b ↦ ofLim i (x hpq b))
    (fun i j h b ↦ by rw [← DirectLimit.Monoid.of_f h, map_x]) a

private theorem genLim_ringOf {p q : κ} (hpq : p ≠ q) (i : ι) (a : G i) :
    genLim G f hpq (Ring.of G f i a) = ofLim i (x hpq a) := by
  rw [Ring.of_apply, genLim, DirectLimit.lift_def]

/-- The inverse of the comparison `directLimitEquiv`, defined on generators by `genLim`. -/
private def toLim : IndexedSteinbergGroup κ (_root_.DirectLimit G f) →* StLim :=
  lift (fun _ _ hpq a ↦ genLim G f hpq a)
    (fun _ _ hpq a b ↦ by
      obtain ⟨i, a, b, rfl, rfl⟩ := exists_ringOf₂ G f a b
      rw [← map_add, genLim_ringOf, genLim_ringOf, genLim_ringOf, x_add, map_mul])
    (fun _ _ _ _ hpq hrs hqr hsp a b ↦ by
      obtain ⟨i, a, b, rfl, rfl⟩ := exists_ringOf₂ G f a b
      rw [genLim_ringOf, genLim_ringOf]
      exact (commute_x hpq hrs hqr hsp a b).map _)
    (fun _ _ _ hpq hqr hpr a b ↦ by
      obtain ⟨i, a, b, rfl, rfl⟩ := exists_ringOf₂ G f a b
      rw [← map_mul, genLim_ringOf, genLim_ringOf, genLim_ringOf, ← map_commutatorElement,
        commutatorElement_x hpq hqr hpr])

private theorem toLim_x_ringOf {p q : κ} (hpq : p ≠ q) (i : ι) (a : G i) :
    toLim G f (x hpq (Ring.of G f i a)) = ofLim i (x hpq a) :=
  lift_x _ _ _ _ hpq _

variable (κ) in
/-- **The Steinberg group commutes with directed colimits of rings.** For a directed system of
rings `Gᵢ` and any index type `κ`, the homomorphisms `St_κ(Gᵢ) →* St_κ(DirectLimit G f)` induced
by the canonical maps `Gᵢ →+* DirectLimit G f` identify the direct limit of the groups `St_κ(Gᵢ)`
with `St_κ(DirectLimit G f)`. -/
def directLimitEquiv : StLim ≃* IndexedSteinbergGroup κ (_root_.DirectLimit G f) :=
  MonoidHom.toMulEquiv
    (DirectLimit.Monoid.lift _ _ (fun i ↦ map (Ring.of G f i))
      (fun i j h z ↦ by rw [map_map, DirectLimit.Ring.of_comp_f]))
    (toLim G f)
    (DirectLimit.Monoid.hom_ext fun i ↦ hom_ext fun p q hpq a ↦ by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, DirectLimit.Monoid.lift_of, map_x,
        toLim_x_ringOf])
    (hom_ext fun p q hpq a ↦ by
      obtain ⟨i, a, rfl⟩ := exists_ringOf G f a
      rw [MonoidHom.comp_apply, toLim_x_ringOf, DirectLimit.Monoid.lift_of, map_x,
        MonoidHom.id_apply])

variable {G f}

/-- `directLimitEquiv` sends the class of an element of `St_κ(Gᵢ)` to its image under the
homomorphism induced by the canonical map `Gᵢ →+* DirectLimit G f`. -/
theorem directLimitEquiv_of (i : ι) (z : IndexedSteinbergGroup κ (G i)) :
    directLimitEquiv G f κ (ofLim i z) = map (Ring.of G f i) z := by
  rw [directLimitEquiv, MonoidHom.toMulEquiv_apply, DirectLimit.Monoid.lift_of]

/-- `directLimitEquiv` sends the class `⟦⟨i, z⟩⟧` of `z ∈ St_κ(Gᵢ)` to its image under the
homomorphism induced by the canonical map `Gᵢ →+* DirectLimit G f`. -/
@[simp]
theorem directLimitEquiv_mk (i : ι) (z : IndexedSteinbergGroup κ (G i)) :
    directLimitEquiv G f κ ⟦⟨i, z⟩⟧ = map (Ring.of G f i) z := by
  rw [← DirectLimit.Monoid.of_apply, directLimitEquiv_of]

/-- The inverse of `directLimitEquiv` sends the image of an element of `St_κ(Gᵢ)` to its class in
the direct limit. -/
@[simp]
theorem directLimitEquiv_symm_map (i : ι) (z : IndexedSteinbergGroup κ (G i)) :
    (directLimitEquiv G f κ).symm (map (Ring.of G f i) z) = ⟦⟨i, z⟩⟧ := by
  rw [MulEquiv.symm_apply_eq, directLimitEquiv_mk]

/-- The inverse of `directLimitEquiv` sends the generator `x_{pq}(⟦⟨i, a⟩⟧)`, for the class
`⟦⟨i, a⟩⟧` of an element `a` of the stage `Gᵢ`, to the class of the generator `x_{pq}(a)` of
`St_κ(Gᵢ)`. -/
@[simp]
theorem directLimitEquiv_symm_x {p q : κ} (hpq : p ≠ q) (i : ι) (a : G i) :
    (directLimitEquiv G f κ).symm (x hpq ⟦⟨i, a⟩⟧) = ⟦⟨i, x hpq a⟩⟧ := by
  rw [← Ring.of_apply G f i a, ← map_x, directLimitEquiv_symm_map]

/-- Every element of the Steinberg group of a directed colimit of rings comes from the Steinberg
group of some stage. -/
theorem exists_map_ringOf_eq (z : IndexedSteinbergGroup κ (_root_.DirectLimit G f)) :
    ∃ i, ∃ y : IndexedSteinbergGroup κ (G i), map (Ring.of G f i) y = z := by
  obtain ⟨i, y, hy⟩ := exists_eq_mk _ ((directLimitEquiv G f κ).symm z)
  refine ⟨i, y, ?_⟩
  rw [← directLimitEquiv_mk, ← hy, MulEquiv.apply_symm_apply]

/-- An element of the Steinberg group of a stage whose image in the Steinberg group of the
directed colimit is trivial is already trivial in the Steinberg group of some later stage. -/
theorem exists_map_eq_one_of_map_ringOf_eq_one {i : ι} {y : IndexedSteinbergGroup κ (G i)}
    (hy : map (Ring.of G f i) y = 1) : ∃ j, ∃ hij : i ≤ j, map (f i j hij) y = 1 := by
  rw [← directLimitEquiv_mk, MulEquiv.map_eq_one_iff, exists_eq_one] at hy
  exact hy

end IndexedSteinbergGroup

namespace AlgebraicK2

variable {G f}

/-- Every element of `K₂` of a directed colimit of rings comes from `K₂` of some stage. -/
theorem exists_map_ringOf_eq (z : AlgebraicK2 (_root_.DirectLimit G f)) :
    ∃ i, ∃ y : AlgebraicK2 (G i), map (Ring.of G f i) y = z := by
  obtain ⟨i, w, hw⟩ := IndexedSteinbergGroup.exists_map_ringOf_eq z.val
  have hw₁ : StableGeneralLinearGroup.map (Ring.of G f i) (SteinbergGroup.toStableGL _ w) = 1 := by
    rw [← SteinbergGroup.toStableGL_map, hw, toStableGL_coe]
  obtain ⟨j, hij, hj⟩ := StableGeneralLinearGroup.exists_map_eq_one_of_map_ringOf_eq_one hw₁
  refine ⟨j, ⟨IndexedSteinbergGroup.map (f i j hij) w, ?_⟩, Subtype.ext ?_⟩
  · rw [MonoidHom.mem_ker, SteinbergGroup.toStableGL_map, hj]
  · rw [coe_map_apply, IndexedSteinbergGroup.map_map, DirectLimit.Ring.of_comp_f, hw]

/-- An element of `K₂` of a stage whose image in `K₂` of the directed colimit is trivial is
already trivial in `K₂` of some later stage. -/
theorem exists_map_eq_one_of_map_ringOf_eq_one {i : ι} {y : AlgebraicK2 (G i)}
    (hy : map (Ring.of G f i) y = 1) : ∃ j, ∃ hij : i ≤ j, map (f i j hij) y = 1 := by
  rw [Subtype.ext_iff, coe_map_apply, OneMemClass.coe_one] at hy
  obtain ⟨j, hij, hj⟩ := IndexedSteinbergGroup.exists_map_eq_one_of_map_ringOf_eq_one hy
  exact ⟨j, hij, Subtype.ext (by rw [coe_map_apply, hj, OneMemClass.coe_one])⟩

variable (G f)

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The groups `K₂(Gᵢ)` of a directed system of rings, along the induced homomorphisms, form a
directed system of groups. -/
instance : DirectedSystem (fun i ↦ AlgebraicK2 (G i)) (fun i j h ↦ map (f i j h)) where
  map_self i y := by rw [DirectedSystem.ringHom_self f, map_id, MonoidHom.id_apply]
  map_map k j i hij hjk y := by rw [map_map, DirectedSystem.ringHom_comp]

/-- The comparison homomorphism from the direct limit of the groups `K₂(Gᵢ)` to
`K₂(DirectLimit G f)`, induced by the canonical maps `Gᵢ →+* DirectLimit G f`. -/
private def toDirectLimit :
    _root_.DirectLimit (fun i ↦ AlgebraicK2 (G i)) (fun i j h ↦ map (f i j h)) →*
      AlgebraicK2 (_root_.DirectLimit G f) :=
  DirectLimit.Monoid.lift _ _ (fun i ↦ map (Ring.of G f i))
    (fun i j h y ↦ by rw [map_map, DirectLimit.Ring.of_comp_f])

private theorem toDirectLimit_bijective : Function.Bijective (toDirectLimit G f) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun z hz ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨i, y, rfl⟩ := exists_eq_mk _ z
    rw [← DirectLimit.Monoid.of_apply, toDirectLimit, DirectLimit.Monoid.lift_of] at hz
    obtain ⟨j, hij, hj⟩ := exists_map_eq_one_of_map_ringOf_eq_one hz
    exact (exists_eq_one _).2 ⟨j, hij, hj⟩
  · obtain ⟨i, y, rfl⟩ := exists_map_ringOf_eq z
    exact ⟨DirectLimit.Monoid.of _ _ i y, by rw [toDirectLimit, DirectLimit.Monoid.lift_of]⟩

/-- **Algebraic `K₂` commutes with directed colimits of rings.** For a directed system of rings
`Gᵢ`, the homomorphisms `K₂(Gᵢ) →* K₂(DirectLimit G f)` induced by the canonical maps
`Gᵢ →+* DirectLimit G f` identify the direct limit of the groups `K₂(Gᵢ)` with
`K₂(DirectLimit G f)`. -/
def directLimitEquiv :
    _root_.DirectLimit (fun i ↦ AlgebraicK2 (G i)) (fun i j h ↦ map (f i j h)) ≃*
      AlgebraicK2 (_root_.DirectLimit G f) :=
  MulEquiv.ofBijective (toDirectLimit G f) (toDirectLimit_bijective G f)

/-- `directLimitEquiv` sends the class of an element of `K₂(Gᵢ)` to its image under the
homomorphism induced by the canonical map `Gᵢ →+* DirectLimit G f`. -/
theorem directLimitEquiv_of (i : ι) (y : AlgebraicK2 (G i)) :
    directLimitEquiv G f (DirectLimit.Monoid.of _ _ i y) = map (Ring.of G f i) y := by
  rw [directLimitEquiv, MulEquiv.ofBijective_apply, toDirectLimit, DirectLimit.Monoid.lift_of]

/-- `directLimitEquiv` sends the class `⟦⟨i, y⟩⟧` of `y ∈ K₂(Gᵢ)` to its image under the
homomorphism induced by the canonical map `Gᵢ →+* DirectLimit G f`. -/
@[simp]
theorem directLimitEquiv_mk (i : ι) (y : AlgebraicK2 (G i)) :
    directLimitEquiv G f ⟦⟨i, y⟩⟧ = map (Ring.of G f i) y := by
  rw [← DirectLimit.Monoid.of_apply, directLimitEquiv_of]

/-- The inverse of `directLimitEquiv` sends the image of an element of `K₂(Gᵢ)` to its class in
the direct limit. -/
@[simp]
theorem directLimitEquiv_symm_map (i : ι) (y : AlgebraicK2 (G i)) :
    (directLimitEquiv G f).symm (map (Ring.of G f i) y) = ⟦⟨i, y⟩⟧ := by
  rw [MulEquiv.symm_apply_eq, directLimitEquiv_mk]

end AlgebraicK2

end TauCeti
