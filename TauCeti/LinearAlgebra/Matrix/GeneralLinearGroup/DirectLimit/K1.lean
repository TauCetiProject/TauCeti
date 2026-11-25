/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DirectLimit.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Algebraic `K₁` commutes with directed colimits of rings

Let `(Gᵢ, fᵢⱼ)` be a directed system of possibly noncommutative rings over a nonempty directed
preorder `ι`, and let `G_∞ = DirectLimit G f` be its colimit, Mathlib's generic direct limit with
its ring structure and canonical ring homomorphisms `DirectLimit.Ring.of G f i : Gᵢ →+* G_∞`.

Every invertible matrix over `G_∞` comes from some stage, two invertible matrices of a stage with
the same image over `G_∞` agree at a later stage, and an invertible matrix of a stage which becomes
elementary over `G_∞` is elementary at a later stage
(`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/DirectLimit/Basic.lean`).

Since a class of algebraic `K₁` is represented by a single invertible matrix, and is trivial
exactly when some stabilization of that matrix is elementary, the homomorphisms
`K₁(Gᵢ) → K₁(G_∞)` induced by the canonical maps identify `K₁(G_∞)` with the direct limit of the
groups `K₁(Gᵢ)` along the induced homomorphisms `K₁(fᵢⱼ)`:

  `K₁(colim Gᵢ) ≃* colim K₁(Gᵢ)`.

## Main definitions

* `TauCeti.AlgebraicK1.instDirectedSystemMap`: the groups `K₁(Gᵢ)` with the homomorphisms
  `AlgebraicK1.map (f i j h)` form a directed system.
* `TauCeti.AlgebraicK1.directLimitEquiv G f`: the isomorphism from the direct limit of the groups
  `K₁(Gᵢ)` to `K₁(DirectLimit G f)`, induced by the canonical maps.

## Main results

* `TauCeti.AlgebraicK1.exists_map_ringOf_eq`: every class in `K₁` of the colimit comes from `K₁` of
  some stage.
* `TauCeti.AlgebraicK1.exists_map_eq_one_of_map_ringOf_eq_one`: a class in `K₁` of a stage which
  becomes trivial in `K₁` of the colimit is trivial in `K₁` of a later stage.
* `TauCeti.AlgebraicK1.directLimitEquiv_mk`: the isomorphism sends the class of `x ∈ K₁(Gᵢ)` to the
  image of `x` under the homomorphism induced by `DirectLimit.Ring.of G f i`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3,
  for `K₁` as the quotient `GL(R) / E(R)`.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §1, for `K₁` and its functoriality in ring maps.
-/

public section

namespace TauCeti

open _root_.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type*}

namespace AlgebraicK1

variable [∀ i, Ring (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The groups `K₁(Gᵢ)` of a directed system of rings, with the induced homomorphisms of
algebraic `K₁`, form a directed system. -/
instance instDirectedSystemMap :
    DirectedSystem (fun i ↦ AlgebraicK1 (G i)) fun i j h ↦ AlgebraicK1.map (f i j h) where
  map_self i x := by
    have : f i i le_rfl = RingHom.id (G i) :=
      RingHom.ext fun x ↦ DirectedSystem.map_self' (f · · ·) x
    rw [this, map_id, MonoidHom.id_apply]
  map_map k j i hij hjk x := by
    have : (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) :=
      RingHom.ext fun x ↦ DirectedSystem.map_map' (f · · ·) hij hjk x
    rw [map_map, this]

/-- The homomorphisms of algebraic `K₁` induced by the canonical maps into the direct limit of
rings are compatible with the transition maps. -/
theorem map_ringOf_map_f {i j : ι} (hij : i ≤ j) (x : AlgebraicK1 (G i)) :
    AlgebraicK1.map (Ring.of G f j) (AlgebraicK1.map (f i j hij) x) =
      AlgebraicK1.map (Ring.of G f i) x := by
  rw [map_map, DirectLimit.Ring.of_comp_f]

/-- Every class in `K₁` of the direct limit of rings is the image of a class in `K₁` of some
stage. -/
theorem exists_map_ringOf_eq (x : AlgebraicK1 (DirectLimit G f)) :
    ∃ i, ∃ y : AlgebraicK1 (G i), AlgebraicK1.map (Ring.of G f i) y = x := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  obtain ⟨i, v, rfl⟩ := DirectLimit.exists_unitsMap_mapMatrix_eq u
  exact ⟨i, mk (G i) n v, map_mk ..⟩

/-- A class in `K₁` of a stage which becomes trivial in `K₁` of the direct limit of rings is
already trivial in `K₁` of a later stage. -/
theorem exists_map_eq_one_of_map_ringOf_eq_one {i : ι} {y : AlgebraicK1 (G i)}
    (h : AlgebraicK1.map (Ring.of G f i) y = 1) :
    ∃ j, ∃ hij : i ≤ j, AlgebraicK1.map (f i j hij) y = 1 := by
  obtain ⟨n, v, rfl⟩ := exists_mk y
  rw [map_mk, mk_eq_one_iff] at h
  obtain ⟨p, hnp, hp⟩ := h
  rw [stabilizeGL_map] at hp
  obtain ⟨j, hij, hj⟩ := DirectLimit.exists_unitsMap_mapMatrix_mem_elementarySubgroup hp
  refine ⟨j, hij, ?_⟩
  rw [map_mk, mk_eq_one_iff]
  exact ⟨p, hnp, by rwa [stabilizeGL_map]⟩

/-- The homomorphism from the direct limit of the groups `K₁(Gᵢ)` to `K₁(DirectLimit G f)`
induced by the canonical maps is bijective. -/
private theorem bijective_lift_map_ringOf :
    Function.Bijective (DirectLimit.Monoid.lift (fun i ↦ AlgebraicK1 (G i))
      (fun i j h ↦ AlgebraicK1.map (f i j h)) (fun i ↦ AlgebraicK1.map (Ring.of G f i))
      fun _ _ hij x ↦ map_ringOf_map_f hij x) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨i, y, rfl⟩ := exists_eq_mk _ z
    rw [DirectLimit.Monoid.lift_mk] at hz
    obtain ⟨j, hij, hj⟩ := exists_map_eq_one_of_map_ringOf_eq_one hz
    rw [← DirectLimit.Monoid.of_apply, ← DirectLimit.Monoid.of_f hij, hj, map_one]
  · obtain ⟨i, y, rfl⟩ := exists_map_ringOf_eq x
    exact ⟨DirectLimit.Monoid.of _ _ i y, DirectLimit.Monoid.lift_of ..⟩

variable (G f) in
/-- **Algebraic `K₁` commutes with directed colimits of rings.** The homomorphisms
`K₁(Gᵢ) → K₁(DirectLimit G f)` induced by the canonical ring homomorphisms identify the direct
limit of the groups `K₁(Gᵢ)` with `K₁` of the direct limit of the rings `Gᵢ`. -/
noncomputable def directLimitEquiv :
    _root_.DirectLimit (fun i ↦ AlgebraicK1 (G i)) (fun i j h ↦ AlgebraicK1.map (f i j h)) ≃*
      AlgebraicK1 (_root_.DirectLimit G f) :=
  MulEquiv.ofBijective _ bijective_lift_map_ringOf

/-- The isomorphism `directLimitEquiv` sends the class of `x ∈ K₁(Gᵢ)` to the image of `x` under
the homomorphism induced by the canonical map `Gᵢ → DirectLimit G f`. -/
@[simp]
theorem directLimitEquiv_mk (i : ι) (x : AlgebraicK1 (G i)) :
    directLimitEquiv G f ⟦⟨i, x⟩⟧ = AlgebraicK1.map (Ring.of G f i) x :=
  DirectLimit.Monoid.lift_mk ..

/-- The inverse of `directLimitEquiv` sends the image of `x ∈ K₁(Gᵢ)` in `K₁(DirectLimit G f)` to
the class of `x` in the direct limit of the groups `K₁(Gᵢ)`. -/
@[simp]
theorem directLimitEquiv_symm_map (i : ι) (x : AlgebraicK1 (G i)) :
    (directLimitEquiv G f).symm (AlgebraicK1.map (Ring.of G f i) x) = ⟦⟨i, x⟩⟧ := by
  rw [MulEquiv.symm_apply_eq, directLimitEquiv_mk]

end AlgebraicK1

end TauCeti
