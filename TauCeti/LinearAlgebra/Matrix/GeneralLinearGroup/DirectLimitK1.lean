/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.CommonStage
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Algebraic `K₁` commutes with directed colimits of rings

Let `(Gᵢ, fᵢⱼ)` be a directed system of possibly noncommutative rings over a nonempty directed
preorder `ι`, and let `G_∞ = DirectLimit G f` be its colimit, Mathlib's generic direct limit with
its ring structure and canonical ring homomorphisms `DirectLimit.Ring.of G f i : Gᵢ →+* G_∞`.

A matrix involves only finitely many entries, and any finitely many elements of `G_∞` come from a
common stage, where finitely many equations between them already hold. Hence finite matrices,
their inverses and their elementary factorizations all descend to some stage:

* every invertible matrix over `G_∞` is the image of an invertible matrix over some `Gᵢ`;
* two invertible matrices over `Gᵢ` with the same image over `G_∞` agree over some later `Gⱼ`;
* the elementary subgroup `Eₙ(G_∞)` is the directed union of the images of the `Eₙ(Gᵢ)`, so an
  invertible matrix over `Gᵢ` which becomes elementary over `G_∞` is already elementary over
  some later `Gⱼ`.

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

* `TauCeti.DirectLimit.exists_unitsMap_mapMatrix_eq`: every invertible matrix over the colimit
  comes from some stage.
* `TauCeti.DirectLimit.exists_unitsMap_mapMatrix_eq_unitsMap_mapMatrix`: invertible matrices of a
  stage with the same image in the colimit agree at a later stage.
* `TauCeti.DirectLimit.elementarySubgroup_eq_iSup`: the elementary subgroup over the colimit is
  the union of the images of the elementary subgroups of the stages.
* `TauCeti.DirectLimit.exists_unitsMap_mapMatrix_mem_elementarySubgroup`: an invertible matrix of a
  stage which is elementary over the colimit is elementary at a later stage.
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

namespace DirectLimit

section Matrix

variable [∀ i, NonAssocSemiring (G i)] {f : ∀ i j, i ≤ j → G i →+* G j}
  [DirectedSystem G (f · · ·)] {m n : Type*}

/-- Two matrices over a stage with the same image over the direct limit of rings agree over a
later stage. -/
theorem exists_map_eq_of_map_eq [Finite m] [Finite n] {i : ι} {M N : Matrix m n (G i)}
    (h : M.map (Ring.of G f i) = N.map (Ring.of G f i)) :
    ∃ j, ∃ hij : i ≤ j, M.map (f i j hij) = N.map (f i j hij) := by
  obtain ⟨j, hij, hj⟩ := exists_forall_eq_of_forall_eq (t := fun i j h ↦ f i j h)
    (φ := fun i ↦ Ring.of G f i) (fun i _ _ ↦ Ring.exists_eq_of_of_eq)
    (a := fun p : m × n ↦ M p.1 p.2) (b := fun p ↦ N p.1 p.2)
    fun p ↦ congrFun (congrFun h p.1) p.2
  exact ⟨j, hij, Matrix.ext fun a b ↦ hj (a, b)⟩

/-- Applying the canonical map of a stage to the entries of a matrix after a transition map is
applying the canonical map of the earlier stage. -/
theorem map_map_ringOf {i j : ι} (hij : i ≤ j) (M : Matrix m n (G i)) :
    (M.map (f i j hij)).map (Ring.of G f j) = M.map (Ring.of G f i) :=
  Matrix.ext fun _ _ ↦ Ring.of_f hij _

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- Applying two transition maps to the entries of a matrix is applying their composite. -/
theorem map_map_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (M : Matrix m n (G i)) :
    (M.map (f i j hij)).map (f j k hjk) = M.map (f i k (hij.trans hjk)) :=
  Matrix.ext fun _ _ ↦ DirectedSystem.map_map' (f · · ·) hij hjk _

end Matrix

section GeneralLinearGroup

variable [∀ i, Semiring (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Applying the canonical map of a stage to the entries of an invertible matrix after a transition
map is applying the canonical map of the earlier stage. -/
theorem unitsMap_ringOf_unitsMap_f {i j : ι} (hij : i ≤ j) (v : GL n (G i)) :
    Units.map ((Ring.of G f j).mapMatrix (m := n)).toMonoidHom
        (Units.map ((f i j hij).mapMatrix (m := n)).toMonoidHom v) =
      Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom v :=
  Units.ext (map_map_ringOf hij (v : Matrix n n (G i)))

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- Applying two transition maps to the entries of an invertible matrix is applying their
composite. -/
theorem unitsMap_f_unitsMap_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (v : GL n (G i)) :
    Units.map ((f j k hjk).mapMatrix (m := n)).toMonoidHom
        (Units.map ((f i j hij).mapMatrix (m := n)).toMonoidHom v) =
      Units.map ((f i k (hij.trans hjk)).mapMatrix (m := n)).toMonoidHom v :=
  Units.ext (map_map_f hij hjk (v : Matrix n n (G i)))

/-- Two invertible matrices over a stage with the same image over the direct limit of rings agree
over a later stage. -/
theorem exists_unitsMap_mapMatrix_eq_unitsMap_mapMatrix {i : ι} {v w : GL n (G i)}
    (h : Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom v =
      Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom w) :
    ∃ j, ∃ hij : i ≤ j, Units.map ((f i j hij).mapMatrix (m := n)).toMonoidHom v =
      Units.map ((f i j hij).mapMatrix (m := n)).toMonoidHom w := by
  obtain ⟨j, hij, hj⟩ := exists_map_eq_of_map_eq (f := f) (M := (v : Matrix n n (G i)))
    (N := w) (congrArg Units.val h)
  exact ⟨j, hij, Units.ext hj⟩

/-- **Invertible matrices descend.** Every invertible matrix over the direct limit of rings is the
image of an invertible matrix over some stage: its entries and the entries of its inverse come
from a common stage, where the two products with the identity hold after a further transition. -/
theorem exists_unitsMap_mapMatrix_eq (u : GL n (DirectLimit G f)) :
    ∃ i, ∃ v : GL n (G i), Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom v = u := by
  classical
  -- Lift the entries of `u` and of `u⁻¹` to a common stage `i`.
  obtain ⟨i, g, hg⟩ := exists_lift (t := fun i j h ↦ f i j h) (fun _ _ ↦ Ring.of_f)
    Ring.exists_of (Finset.univ.image fun p : Bool × n × n ↦
      (if p.1 then (u : Matrix n n _) else (u⁻¹ : GL n _)) p.2.1 p.2.2)
  set A : Matrix n n (G i) := (u : Matrix n n _).map g
  set B : Matrix n n (G i) := (↑u⁻¹ : Matrix n n _).map g
  have hA : A.map (Ring.of G f i) = u := Matrix.ext fun a b ↦
    hg _ (Finset.mem_image.2 ⟨(true, a, b), Finset.mem_univ _, rfl⟩)
  have hB : B.map (Ring.of G f i) = ↑u⁻¹ := Matrix.ext fun a b ↦
    hg _ (Finset.mem_image.2 ⟨(false, a, b), Finset.mem_univ _, rfl⟩)
  have h1 : ∀ {p q : ι} (h : p ≤ q), (1 : Matrix n n (G p)).map (f p q h) = 1 :=
    fun _ ↦ Matrix.map_one _ (map_zero _) (map_one _)
  -- The products `A * B` and `B * A` become the identity over the colimit, hence at a later stage.
  have hAB : (A * B).map (Ring.of G f i) = (1 : Matrix n n (G i)).map (Ring.of G f i) := by
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨j, hij, hj⟩ := exists_map_eq_of_map_eq hAB
  have hBA : (B.map (f i j hij) * A.map (f i j hij)).map (Ring.of G f j) =
      (1 : Matrix n n (G j)).map (Ring.of G f j) := by
    rw [Matrix.map_mul, map_map_ringOf, map_map_ringOf, hA, hB, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨k, hjk, hk⟩ := exists_map_eq_of_map_eq hBA
  have hAB' : A.map (f i k (hij.trans hjk)) * B.map (f i k (hij.trans hjk)) = 1 := by
    have := congrArg (Matrix.map · (f j k hjk)) hj
    simp only [Matrix.map_mul, map_map_f, h1] at this
    exact this
  rw [Matrix.map_mul, map_map_f, map_map_f, h1] at hk
  exact ⟨k, ⟨_, _, hAB', hk⟩, Units.ext ((map_map_ringOf _ A).trans hA)⟩

end GeneralLinearGroup

section Elementary

variable [∀ i, Ring (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The images of the elementary subgroups of the stages increase along the directed system. -/
theorem directed_map_elementarySubgroup :
    Directed (· ≤ ·) fun i ↦ (elementarySubgroup n (G i)).map
      (Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom) := by
  refine directed_of_isDirected_le fun {i j} hij ↦ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨_, (f i j hij).map_elementarySubgroup_le ⟨v, hv, rfl⟩, unitsMap_ringOf_unitsMap_f hij v⟩

/-- **Elementary matrices descend.** The elementary subgroup over the direct limit of rings is the
union of the images of the elementary subgroups of the stages. -/
theorem elementarySubgroup_eq_iSup :
    elementarySubgroup n (DirectLimit G f) =
      ⨆ i, (elementarySubgroup n (G i)).map
        (Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom) := by
  refine le_antisymm (elementarySubgroup_le_iff.2 fun a b hab x ↦ ?_)
    (iSup_le fun i ↦ (Ring.of G f i).map_elementarySubgroup_le)
  obtain ⟨i, y, rfl⟩ := Ring.exists_of x
  exact Subgroup.mem_iSup_of_mem i ⟨transvectionUnit hab y,
    transvectionUnit_mem_elementarySubgroup hab y,
    (Ring.of G f i).unitsMap_mapMatrix_transvectionUnit hab y⟩

/-- An invertible matrix over a stage which becomes elementary over the direct limit of rings is
elementary over a later stage. -/
theorem exists_unitsMap_mapMatrix_mem_elementarySubgroup {i : ι} {v : GL n (G i)}
    (hv : Units.map ((Ring.of G f i).mapMatrix (m := n)).toMonoidHom v ∈
      elementarySubgroup n (DirectLimit G f)) :
    ∃ j, ∃ hij : i ≤ j,
      Units.map ((f i j hij).mapMatrix (m := n)).toMonoidHom v ∈ elementarySubgroup n (G j) := by
  rw [elementarySubgroup_eq_iSup, Subgroup.mem_iSup_of_directed directed_map_elementarySubgroup]
    at hv
  obtain ⟨k, e, he, hek⟩ := hv
  obtain ⟨l, hil, hkl⟩ := directed_of (· ≤ ·) i k
  obtain ⟨j, hlj, hj⟩ := exists_unitsMap_mapMatrix_eq_unitsMap_mapMatrix (f := f)
    (v := Units.map ((f i l hil).mapMatrix (m := n)).toMonoidHom v)
    (w := Units.map ((f k l hkl).mapMatrix (m := n)).toMonoidHom e)
    (by rw [unitsMap_ringOf_unitsMap_f, unitsMap_ringOf_unitsMap_f, hek])
  refine ⟨j, hil.trans hlj, ?_⟩
  rw [← unitsMap_f_unitsMap_f hil hlj, hj, unitsMap_f_unitsMap_f]
  exact (f k j (hkl.trans hlj)).map_elementarySubgroup_le ⟨e, he, rfl⟩

end Elementary

end DirectLimit

namespace AlgebraicK1

variable [∀ i, Ring (G i)] {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G (f · · ·)]

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
