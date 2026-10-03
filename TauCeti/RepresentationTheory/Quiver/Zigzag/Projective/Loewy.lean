/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Radical

/-!
# The simple factors of zigzag vertex projectives

For a finite simple graph without isolated vertices, the head and socle of the left vertex
projective `P_i = Z e_i` are isomorphic. Its middle Loewy layer is the direct product of the
heads at the neighbours of `i`. These are isomorphisms of modules over the zigzag algebra,
so they identify the simple factors, not merely their dimensions.

With later-factor-first multiplication the arrow `i → j` belongs to `P_i` and carries the
simple at `j` in the middle layer. The head and socle carry the simple at `i`.

## References

* R. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3.
* M. Ehrig and D. Tubbenhauer, *Algebraic properties of zigzag algebras*, equation (2-1)
  and Proposition 2.8.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]
variable (hns : ∀ i : V, ∃ j, G.Adj i j)

local notation "Z" => nonisolatedZigzagQuotient k G
local notation "P" => zigzagProjective k G
local notation "R" => zigzagProjectiveRadicalPower k G
local notation "H" => zigzagProjectiveRadicalLayer k G

-- `Submodule.coe_smul` rewrites the submodule's Z-action. These inclusions also preserve
-- the inherited k-action, where that lemma does not match the scalar type.
private theorem coe_projective_smul (i : V) (c : k) (x : P i) :
    ((c • x : P i) : Z) = c • (x : Z) :=
  ((P i).restrictScalars k).subtype.map_smul c x

private theorem coe_radical_smul (i : V) (n : ℕ) (c : k) (x : R i n) :
    (((c • x : R i n) : P i) : Z) = c • ((x : P i) : Z) :=
  (((P i).restrictScalars k).subtype.comp ((R i n).restrictScalars k).subtype).map_smul c x

private noncomputable def headToSocle (i : V) : R i 0 →ₗ[Z] R i 2 where
  toFun x := ⟨⟨(x.1 : Z) * zigzagVolume k G i,
    (mem_zigzagProjective_iff k G).2 (by
      rw [mul_assoc, zigzagVolume_mul_zigzagMk_vertexIdempotent])⟩,
    (mem_zigzagProjectiveRadicalPower_two_iff hns i _).2 (by
      -- Remove the projective subtype before rewriting its underlying algebra product.
      change (x.1 : Z) * zigzagVolume k G i ∈ zigzagVolumeSpan k G
      rw [mul_zigzagVolume hns]
      exact (zigzagVolumeSpan k G).smul_mem _ (zigzagVolume_mem_zigzagVolumeSpan i))⟩
  map_add' x y := Subtype.ext (Subtype.ext (add_mul _ _ _))
  map_smul' z x := Subtype.ext (Subtype.ext (mul_assoc _ _ _))

private theorem headToSocle_apply (i : V) (x : R i 0) :
    ((headToSocle k G hns i x : P i) : Z) =
      zigzagProjectiveHeadCoeff k G i x.1 • zigzagVolume k G i := by
  -- Expose the underlying multiplication, without depending on subtype proof terms.
  change (x.1 : Z) * zigzagVolume k G i =
    zigzagProjectiveHeadCoeff k G i x.1 • zigzagVolume k G i
  rw [mul_zigzagVolume hns, zigzagProjectiveHeadCoeff_apply,
    zigzagTrivialCoeff_apply_eq_repr hns, Module.Basis.coord_apply]

private theorem headToSocle_ker (i : V) :
    LinearMap.ker (headToSocle k G hns i) = (R i 1).submoduleOf (R i 0) := by
  ext x
  rw [LinearMap.mem_ker]
  have hv := (zigzagVolume_ne_zero k G (hns i).choose_spec)
  have hk := ker_zigzagProjectiveHeadCoeff_eq_restrictScalars_radicalPower_one
    (k := k) (G := G) hns i
  constructor
  · intro hx
    have hc := congrArg (fun y : R i 2 => ((y : P i) : Z)) hx
    rw [headToSocle_apply] at hc
    have hz : zigzagProjectiveHeadCoeff k G i x.1 = 0 :=
      (smul_eq_zero.mp hc).resolve_right hv
    have hm : x.1 ∈ LinearMap.ker (zigzagProjectiveHeadCoeff k G i) := hz
    rwa [hk] at hm
  · intro hx
    have hz : zigzagProjectiveHeadCoeff k G i x.1 = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hk]
      exact hx
    apply Subtype.ext
    apply Subtype.ext
    rw [headToSocle_apply, hz, zero_smul]
    rfl

private theorem headToSocle_surjective (i : V) :
    Function.Surjective (headToSocle k G hns i) := by
  intro x
  have hx : x.1 ∈ zigzagProjectiveVolumeLine k G i := by
    rw [← restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine hns]
    exact x.2
  obtain ⟨c, hc⟩ := (mem_zigzagProjectiveVolumeLine_iff k G i x.1).1 hx
  refine ⟨⟨c • zigzagProjectiveGenerator k G i, by simp⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [headToSocle_apply, map_smul, zigzagProjectiveHeadCoeff_generator, smul_eq_mul,
    mul_one]
  have hcoe := congrArg (fun y : P i => (y : Z)) hc
  rw [coe_projective_smul] at hcoe
  simpa only [coe_zigzagProjectiveVolume] using hcoe

/-- The head `P_i / J P_i` is isomorphic to the socle `J² P_i`. The isomorphism is induced
by right multiplication by the volume at `i`. -/
noncomputable def zigzagProjectiveHeadEquivSocle (i : V) : H i 0 ≃ₗ[Z] R i 2 :=
  (Submodule.quotEquivOfEq _ _ (headToSocle_ker k G hns i).symm).trans
    ((headToSocle k G hns i).quotKerEquivOfSurjective
      (headToSocle_surjective k G hns i))

/-- On a representative, the head-to-socle isomorphism multiplies by the volume class. -/
@[simp]
theorem zigzagProjectiveHeadEquivSocle_mk (i : V) (x : R i 0) :
    (((zigzagProjectiveHeadEquivSocle k G hns i (Submodule.Quotient.mk x) : R i 2) :
      P i) : Z) = zigzagProjectiveHeadCoeff k G i x.1 • zigzagVolume k G i := by
  simp only [zigzagProjectiveHeadEquivSocle, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    headToSocle_apply]

private noncomputable def socleVector (i : V) : R i 2 :=
  ⟨zigzagProjectiveVolume k G i, by
    -- Membership in the restricted submodule has the same carrier.
    change zigzagProjectiveVolume k G i ∈ (R i 2).restrictScalars k
    rw [restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine hns]
    exact (mem_zigzagProjectiveVolumeLine_iff k G i _).2 ⟨1, one_smul _ _⟩⟩

private theorem coe_socleVector (i : V) :
    ((socleVector k G hns i : P i) : Z) = zigzagVolume k G i :=
  coe_zigzagProjectiveVolume k G i

private theorem coord_vertex_of_mem_radical (i : V) (x : R i 1) (j : V) :
    (zigzagBasis k G hns).coord (.inl j) (x.1 : Z) = 0 := by
  exact (mem_zigzagPositiveSpan_iff hns).1
    ((mem_zigzagProjectiveRadicalPower_one_iff hns i x.1).1 x.2) j

private theorem coord_dart_of_ne (i : V) (x : P i) (d : G.Dart) (hd : d.fst ≠ i) :
    (zigzagBasis k G hns).coord (.inr (.inl d)) (x : Z) = 0 := by
  classical
  have hfix := (mem_zigzagProjective_iff k G).1 x.2
  have hm := zigzagBasis_coord_dart_mul hns d (x : Z) (zigzagVertexIdempotent k G i)
  rw [hfix] at hm
  have he : zigzagVertexIdempotent k G i = zigzagBasis k G hns (.inl i) := by
    simp [zigzagVertexIdempotent]
  rw [he] at hm
  simpa only [zigzagBasis_coord_apply, Sum.inl_ne_inr, ↓reduceIte, mul_zero,
    Sum.inl.injEq, Ne.symm hd, add_zero] using hm

private noncomputable def middleToSocles (i : V) :
    R i 1 →ₗ[Z] ((j : G.neighborSet i) → R j.1 2) where
  toFun x j := (zigzagBasis k G hns).coord (.inr (.inl ⟨(i, j.1), j.2⟩))
    (x.1 : Z) • socleVector k G hns j.1
  map_add' x y := by
    ext j
    simp only [Submodule.coe_add, map_add, add_smul, Pi.add_apply]
  map_smul' z x := by
    funext j
    apply Subtype.ext
    apply Subtype.ext
    -- Both subtype actions become multiplication in the ambient zigzag algebra.
    simp only [Pi.smul_apply, RingHom.id_apply, coe_radical_smul,
      Submodule.coe_smul, smul_eq_mul]
    rw [coe_socleVector]
    rw [zigzagBasis_coord_dart_mul hns, coord_vertex_of_mem_radical,
      mul_zero, add_zero, mul_smul_comm, mul_zigzagVolume hns, smul_smul]
    congr 1
    exact mul_comm _ _

private theorem middleToSocles_apply (i : V) (x : R i 1) (j : G.neighborSet i) :
    middleToSocles k G hns i x j =
      (zigzagBasis k G hns).coord (.inr (.inl ⟨(i, j.1), j.2⟩)) (x.1 : Z) •
        socleVector k G hns j.1 :=
  (rfl)

private theorem middleToSocles_ker (i : V) :
    LinearMap.ker (middleToSocles k G hns i) = (R i 2).submoduleOf (R i 1) := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    apply (mem_zigzagProjectiveRadicalPower_two_iff hns i x.1).2
    apply (mem_zigzagVolumeSpan_iff hns).2
    refine ⟨coord_vertex_of_mem_radical k G hns i x, fun d => ?_⟩
    rcases eq_or_ne d.fst i with hdi | hdi
    · let j : G.neighborSet i := ⟨d.snd, hdi ▸ d.adj⟩
      have hj := congrArg (fun f => ((f j : P j.1) : Z)) hx
      rw [middleToSocles_apply, coe_radical_smul,
        coe_socleVector] at hj
      simp only [Pi.zero_apply, Submodule.coe_zero] at hj
      have hvol := zigzagVolume_ne_zero k G j.2.symm
      have hz := (smul_eq_zero.mp hj).resolve_right hvol
      convert hz using 1
      exact congrArg (fun e : G.Dart =>
        (zigzagBasis k G hns).coord (.inr (.inl e)) (x.1 : Z)) (by
          apply SimpleGraph.Dart.ext
          exact Prod.ext hdi rfl)
    · exact coord_dart_of_ne k G hns i x.1 d hdi
  · intro hx
    have hc := (mem_zigzagVolumeSpan_iff hns).1
      ((mem_zigzagProjectiveRadicalPower_two_iff hns i x.1).1 hx)
    funext j
    rw [middleToSocles_apply, Module.Basis.coord_apply, hc.2, zero_smul]
    rfl

private noncomputable def radicalArrow (i : V) (j : G.neighborSet i) : R i 1 :=
  ⟨⟨zigzagMk k G (ofArrow (arrow G j.2)), (mem_zigzagProjective_iff k G).2
      (zigzagMk_ofArrow_mul_vertexIdempotent k G ⟨(i, j.1), j.2⟩)⟩,
    (mem_zigzagProjectiveRadicalPower_one_iff hns i _).2
      (zigzagMk_ofArrow_mem_zigzagPositiveSpan ⟨(i, j.1), j.2⟩)⟩

open scoped Classical in
private theorem middleToSocles_radicalArrow (i : V) (j l : G.neighborSet i) :
    middleToSocles k G hns i (radicalArrow k G hns i j) l =
      if j = l then socleVector k G hns l.1 else 0 := by
  classical
  rw [middleToSocles_apply]
  have ha : (((radicalArrow k G hns i j : R i 1) : P i) : Z) =
      zigzagBasis k G hns (.inr (.inl ⟨(i, j.1), j.2⟩)) := by
    simp [radicalArrow]
  rw [ha, zigzagBasis_coord_apply]
  by_cases h : j = l
  · subst l
    simp
  · have hd : (⟨(i, j.1), j.2⟩ : G.Dart) ≠ ⟨(i, l.1), l.2⟩ := by
      intro hd
      exact h (Subtype.ext (congrArg (fun d : G.Dart => d.snd) hd))
    simp [h, hd]

private theorem middleToSocles_surjective (i : V) :
    Function.Surjective (middleToSocles k G hns i) := by
  classical
  let _ := Fintype.ofFinite (G.neighborSet i)
  intro y
  have hy (j : G.neighborSet i) :
      ∃ c : k, c • socleVector k G hns j.1 = y j := by
    have hj : (y j : P j.1) ∈ zigzagProjectiveVolumeLine k G j.1 := by
      rw [← restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine hns]
      exact (y j).2
    obtain ⟨c, hc⟩ := (mem_zigzagProjectiveVolumeLine_iff k G j.1 _).1 hj
    exact ⟨c, Subtype.ext hc⟩
  choose c hc using hy
  refine ⟨∑ j, c j • radicalArrow k G hns i j, ?_⟩
  funext l
  simp only [map_sum, LinearMap.map_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
    middleToSocles_radicalArrow]
  simpa only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    using hc l

/-- The middle Loewy layer of `P_i` is the product of the simple heads at its neighbours.
The isomorphism sends an outgoing arrow to the generator of the head at its target. -/
noncomputable def zigzagProjectiveMiddleEquivNeighborHeads (i : V) :
    H i 1 ≃ₗ[Z] ((j : G.neighborSet i) → H j.1 0) :=
  ((Submodule.quotEquivOfEq _ _ (middleToSocles_ker k G hns i).symm).trans
    ((middleToSocles k G hns i).quotKerEquivOfSurjective
      (middleToSocles_surjective k G hns i))).trans
    (LinearEquiv.piCongrRight fun j => (zigzagProjectiveHeadEquivSocle k G hns j.1).symm)

/-- The distinguished generator of the simple head of the vertex projective. -/
noncomputable def zigzagProjectiveHeadGenerator (i : V) : H i 0 :=
  Submodule.Quotient.mk ⟨zigzagProjectiveGenerator k G i, by simp⟩

/-- The class of the arrow `i → j` in the middle Loewy layer of `P_i`. -/
noncomputable def zigzagProjectiveMiddleArrow (i : V) (j : G.neighborSet i) : H i 1 :=
  Submodule.Quotient.mk (radicalArrow k G hns i j)

/-- The head generator goes to the volume vector in the socle. -/
@[simp]
theorem zigzagProjectiveHeadEquivSocle_generator (i : V) :
    (zigzagProjectiveHeadEquivSocle k G hns i (zigzagProjectiveHeadGenerator k G i) : P i) =
      zigzagProjectiveVolume k G i := by
  apply Subtype.ext
  simp only [zigzagProjectiveHeadGenerator, zigzagProjectiveHeadEquivSocle_mk,
    zigzagProjectiveHeadCoeff_generator, one_smul, coe_zigzagProjectiveVolume]

/-- On a representative of the middle layer, the component at `j`, identified with its
socle, is the coefficient of the outgoing arrow `i → j` times the volume at `j`. -/
@[simp]
theorem zigzagProjectiveMiddleEquivNeighborHeads_mk (i : V) (x : R i 1)
    (j : G.neighborSet i) :
    (((zigzagProjectiveHeadEquivSocle k G hns j.1
      (zigzagProjectiveMiddleEquivNeighborHeads k G hns i (Submodule.Quotient.mk x) j) :
      R j.1 2) : P j.1) : Z) =
        (zigzagBasis k G hns).coord (.inr (.inl ⟨(i, j.1), j.2⟩)) (x.1 : Z) •
          zigzagVolume k G j.1 := by
  simp only [zigzagProjectiveMiddleEquivNeighborHeads, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    LinearEquiv.piCongrRight_apply, LinearEquiv.apply_symm_apply,
    middleToSocles_apply, coe_radical_smul, coe_socleVector]

open scoped Classical in
/-- An outgoing arrow is the generator of exactly its target's simple-head factor. -/
@[simp]
theorem zigzagProjectiveMiddleEquivNeighborHeads_arrow (i : V) (j l : G.neighborSet i) :
    zigzagProjectiveMiddleEquivNeighborHeads k G hns i
        (zigzagProjectiveMiddleArrow k G hns i j) l =
      if j = l then zigzagProjectiveHeadGenerator k G l.1 else 0 := by
  apply (zigzagProjectiveHeadEquivSocle k G hns l.1).injective
  have hgen : zigzagProjectiveHeadEquivSocle k G hns l.1
      (zigzagProjectiveHeadGenerator k G l.1) = socleVector k G hns l.1 := by
    apply Subtype.ext
    exact zigzagProjectiveHeadEquivSocle_generator k G hns l.1
  simp only [zigzagProjectiveMiddleArrow, zigzagProjectiveMiddleEquivNeighborHeads,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearEquiv.piCongrRight_apply,
    LinearEquiv.apply_symm_apply, middleToSocles_radicalArrow]
  split_ifs <;> simp only [hgen, map_zero]

include hns

/-- Every zigzag algebra element acts on the simple head at `i` by its vertex coefficient
at `i`. In particular, this identifies which vertex simple each Loewy factor carries. -/
theorem zigzagProjectiveHead_smul (i : V) (z : Z) (x : H i 0) :
    z • x = zigzagTrivialCoeff k G z (vertex G i) • x := by
  let e := zigzagProjectiveHeadEquivSocle k G hns i
  apply e.injective
  rw [e.map_smul]
  have hm : e (zigzagTrivialCoeff k G z (vertex G i) • x) =
      zigzagTrivialCoeff k G z (vertex G i) • e x :=
    (e.restrictScalars k).map_smul _ _
  rw [hm]
  apply Subtype.ext
  apply Subtype.ext
  -- The inclusions of the socle and projective are scalar-compatible linear maps.
  change z * ((e x : P i) : Z) =
    (((zigzagTrivialCoeff k G z (vertex G i) • e x : R i 2) : P i) : Z)
  rw [coe_radical_smul]
  have hx : (e x : P i) ∈ zigzagProjectiveVolumeLine k G i := by
    rw [← restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine hns]
    exact (e x).2
  obtain ⟨c, hc⟩ := (mem_zigzagProjectiveVolumeLine_iff k G i _).1 hx
  have hcoe := congrArg (fun y : P i => (y : Z)) hc
  rw [coe_projective_smul, coe_zigzagProjectiveVolume] at hcoe
  rw [← hcoe, mul_smul_comm, mul_zigzagVolume hns, smul_smul, smul_smul,
    zigzagTrivialCoeff_apply_eq_repr hns, Module.Basis.coord_apply, mul_comm]

open scoped Classical in
/-- A vertex idempotent acts as the identity on its own simple head and as zero on every
other vertex's head. -/
@[simp]
theorem zigzagProjectiveHead_vertexIdempotent_smul (i v : V) (x : H i 0) :
    zigzagVertexIdempotent k G v • x = if v = i then x else 0 := by
  rw [zigzagProjectiveHead_smul k G hns]
  simp only [zigzagVertexIdempotent, zigzagTrivialCoeff_vertexIdempotent]
  split_ifs <;> simp_all

/-- Every positive-length path acts by zero on a simple head. This includes arrows after
normalizing their path-algebra generators to paths. -/
@[simp]
theorem zigzagProjectiveHead_ofPath_smul (i : V)
    (p : Quiver.TotalPath (DoubledQuiver G)) (hp : 0 < p.2.2.length) (x : H i 0) :
    zigzagMk k G (ofPath p) • x = 0 := by
  rw [zigzagProjectiveHead_smul k G hns, zigzagTrivialCoeff_zigzagMk,
    PathAlgebra.trivialCoeff_ofPath_of_length_pos hp]
  exact zero_smul k x

end TauCeti
