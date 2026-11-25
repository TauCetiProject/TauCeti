/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# Kneser neighbors

Two integral lattices `L` and `M` on the same rational quadratic space are `p`-neighbors when
their intersection `L ∩ M` has index `p` in each of them. Neighbor steps are the moves of
Kneser's method for exploring a genus. This file defines the relation, proves that it is
symmetric, that `1`-neighbors are equal, and that neighbors have equal determinants: the
determinant of `L ∩ M` is both `p² det L` and `p² det M`. In particular a neighbor of a unimodular
lattice is unimodular.

The intersection `L ∩ M` is the integral lattice `TauCeti.IntegralLattice.inf` from
`TauCeti.LinearAlgebra.IntegralLattice.Restriction`, carrying the form of `L`.

## Main definitions

* `TauCeti.IntegralLattice.IsNeighbor`: Kneser's `p`-neighbor relation.

## Main results

* `TauCeti.IntegralLattice.IsNeighbor.symm`: the neighbor relation is symmetric.
* `TauCeti.IntegralLattice.IsNeighbor.transport`: neighbors transport along rational linear
  equivalences.
* `TauCeti.IntegralLattice.IsNeighbor.transport_symm_of_isometry`: pulling back a neighbor along
  an integral-lattice isometry.
* `TauCeti.IntegralLattice.isNeighbor_one_iff`: `1`-neighbors are equal.
* `TauCeti.IntegralLattice.IsNeighbor.determinant_eq`: neighbors have equal determinants.
* `TauCeti.IntegralLattice.IsNeighbor.isUnimodular_iff`: neighbors are unimodular together.
* `TauCeti.IntegralLattice.IsNeighbor.signature_eq`: neighbors have equal signatures.
* `TauCeti.IntegralLattice.IsNeighbor.orthogonalSum_left`,
  `TauCeti.IntegralLattice.IsNeighbor.orthogonalSum_right`: orthogonal sums preserve neighbors.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* M. Kneser, *Quadratische Formen*, revised with R. Scharlau, Springer (2002), §28.
* J. Voight, *Kneser's method of neighbors*, arXiv:2308.11566.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L M : IntegralLattice V)

/-- **Kneser neighbors.** Integral lattices `L` and `M` on the same rational quadratic space are
`p`-neighbors when their intersection has index `p` in each of them, that is
`[L : L ∩ M] = [M : L ∩ M] = p`. -/
structure IsNeighbor (p : ℕ) : Prop where
  /-- Neighbors carry the same rational form. -/
  form_eq : L.form = M.form
  /-- The intersection has index `p` in `L`. -/
  relIndex_inf_left : (L.carrier ⊓ M.carrier).toAddSubgroup.relIndex L.carrier.toAddSubgroup = p
  /-- The intersection has index `p` in `M`. -/
  relIndex_inf_right : (L.carrier ⊓ M.carrier).toAddSubgroup.relIndex M.carrier.toAddSubgroup = p

variable {L M} {p : ℕ}

/-- The neighbor relation is symmetric. -/
@[symm]
theorem IsNeighbor.symm (h : L.IsNeighbor M p) : M.IsNeighbor L p where
  form_eq := h.form_eq.symm
  relIndex_inf_left := by rw [inf_comm]; exact h.relIndex_inf_right
  relIndex_inf_right := by rw [inf_comm]; exact h.relIndex_inf_left

/-- `M` is a `p`-neighbor of `L` exactly when `L` is a `p`-neighbor of `M`. -/
theorem isNeighbor_comm : L.IsNeighbor M p ↔ M.IsNeighbor L p :=
  ⟨.symm, .symm⟩

/-- **Neighbors transport along rational linear equivalences.** Transporting two `p`-neighbors
along the same equivalence of their ambient spaces gives `p`-neighbors. -/
theorem IsNeighbor.transport {W : Type*} [AddCommGroup W] [Module ℚ W] (h : L.IsNeighbor M p)
    (e : V ≃ₗ[ℚ] W) : (L.transport e).IsNeighbor (M.transport e) p := by
  -- Transport is injective on carriers, so it preserves the relative index of an intersection.
  have hrel (A B : IntegralLattice V) :
      ((A.transport e).carrier ⊓ (B.transport e).carrier).toAddSubgroup.relIndex
        (A.transport e).carrier.toAddSubgroup =
        (A.carrier ⊓ B.carrier).toAddSubgroup.relIndex A.carrier.toAddSubgroup := by
    rw [transport_carrier, transport_carrier, ← Submodule.map_inf _ (e.restrictScalars ℤ).injective,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ (e.restrictScalars ℤ).injective]
  refine ⟨by rw [transport_form, transport_form, h.form_eq], ?_, ?_⟩
  · rw [hrel]
    exact h.relIndex_inf_left
  · rw [inf_comm, hrel, inf_comm]
    exact h.relIndex_inf_right

/-- Pulling back a `p`-neighbor of `M` along an integral-lattice isometry `e : Isometry A L`
yields a `p`-neighbor of `A`. -/
theorem IsNeighbor.transport_symm_of_isometry {W : Type*} [AddCommGroup W] [Module ℚ W]
    {A : IntegralLattice W} (h : L.IsNeighbor M p) (e : Isometry A L) :
    A.IsNeighbor (M.transport (e : W ≃ₗ[ℚ] V).symm) p := by
  simpa only [e.transport_symm_eq] using h.transport (e : W ≃ₗ[ℚ] V).symm

/-- The common index of two neighbors is nonzero, since the intersection of two lattices on the
same rational space has finite index in each. -/
theorem IsNeighbor.ne_zero (h : L.IsNeighbor M p) : p ≠ 0 :=
  h.relIndex_inf_left ▸ Submodule.IsFullLattice.relIndex_ne_zero

/-- Two integral lattices are `1`-neighbors exactly when they are equal. -/
@[simp]
theorem isNeighbor_one_iff : L.IsNeighbor M 1 ↔ L = M := by
  constructor
  · intro h
    have hLM := AddSubgroup.relIndex_eq_one.mp h.relIndex_inf_left
    have hML := AddSubgroup.relIndex_eq_one.mp h.relIndex_inf_right
    refine ext (le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)) h.form_eq
    · exact (hLM hx).2
    · exact (hML hx).1
  · rintro rfl
    refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- **Neighbors have equal determinants.** The intersection `L ∩ M` has determinant
`[L : L ∩ M]² det L = [M : L ∩ M]² det M`, and both indices equal the nonzero integer `p`. -/
theorem IsNeighbor.determinant_eq (h : L.IsNeighbor M p) : L.determinant = M.determinant := by
  have hL := (L.inf M).determinant_eq_mul_relIndex_sq L (inf_form L M)
    ((inf_carrier L M).trans_le inf_le_left)
  have hM := (L.inf M).determinant_eq_mul_relIndex_sq M ((inf_form L M).trans h.form_eq)
    ((inf_carrier L M).trans_le inf_le_right)
  rw [inf_carrier, h.relIndex_inf_left] at hL
  rw [inf_carrier, h.relIndex_inf_right] at hM
  exact mul_right_cancel₀ (pow_ne_zero 2 (Int.natCast_ne_zero.mpr h.ne_zero)) (hL.symm.trans hM)

/-- Neighbors have equal discriminants. -/
theorem IsNeighbor.discriminant_eq (h : L.IsNeighbor M p) : L.discriminant = M.discriminant := by
  rw [discriminant_def, discriminant_def, h.determinant_eq]

/-- **Neighbors of unimodular lattices are unimodular**, since neighbors have equal
discriminants. -/
theorem IsNeighbor.isUnimodular (h : L.IsNeighbor M p) (hL : L.IsUnimodular) :
    M.IsUnimodular := by
  let : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  let : M.IsNondegenerate := ⟨h.form_eq ▸ hL.nondegenerate⟩
  rw [M.isUnimodular_iff_discriminant_eq_one, ← h.discriminant_eq,
    ← L.isUnimodular_iff_discriminant_eq_one]
  exact hL

/-- Two neighbors are unimodular together. -/
theorem IsNeighbor.isUnimodular_iff (h : L.IsNeighbor M p) : L.IsUnimodular ↔ M.IsUnimodular :=
  ⟨h.isUnimodular, h.symm.isUnimodular⟩

/-- Kneser `p`-neighbors share the same ambient rational form and therefore the same signature. -/
theorem IsNeighbor.signature_eq (h : L.IsNeighbor M p) : L.signature = M.signature :=
  signature_eq_of_form_eq h.form_eq

/-- **Kneser `p`-neighbors are preserved by left orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_left {W : Type*} [AddCommGroup W] [Module ℚ W]
    (Y : IntegralLattice W) (h : L.IsNeighbor M p) :
    (Y.orthogonalSum L).IsNeighbor (Y.orthogonalSum M) p := by
  have hrel (B : Submodule ℤ V) : (Y.carrier.prod (L.carrier ⊓ M.carrier)).toAddSubgroup.relIndex
      (Y.carrier.prod B).toAddSubgroup =
      (L.carrier ⊓ M.carrier).toAddSubgroup.relIndex B.toAddSubgroup := by
    let proj : (Y.carrier.prod B).toAddSubgroup →+ B.toAddSubgroup :=
      ⟨⟨fun q ↦ ⟨q.1.2, q.2.2⟩, rfl⟩, fun _ _ ↦ rfl⟩
    have hcomap : ((L.carrier ⊓ M.carrier).toAddSubgroup.addSubgroupOf B.toAddSubgroup).comap proj =
        (Y.carrier.prod (L.carrier ⊓ M.carrier)).toAddSubgroup.addSubgroupOf
          (Y.carrier.prod B).toAddSubgroup :=
      AddSubgroup.ext fun q ↦ ⟨fun hq ↦ ⟨q.2.1, hq⟩, fun hq ↦ hq.2⟩
    rw [AddSubgroup.relIndex, ← hcomap, AddSubgroup.index_comap_of_surjective _
      (fun b ↦ ⟨⟨(0, b.1), ⟨Y.carrier.zero_mem, b.2⟩⟩, rfl⟩), ← AddSubgroup.relIndex]
  have hinf : (Y.orthogonalSum L).carrier ⊓ (Y.orthogonalSum M).carrier =
      Y.carrier.prod (L.carrier ⊓ M.carrier) := Submodule.ext fun x ↦ by
    simp only [Submodule.mem_inf, orthogonalSum_carrier, Submodule.mem_prod]; tauto
  exact ⟨by simp [h.form_eq], by rw [hinf, orthogonalSum_carrier, hrel]; exact h.relIndex_inf_left,
    by rw [hinf, orthogonalSum_carrier, hrel]; exact h.relIndex_inf_right⟩

/-- **Kneser `p`-neighbors are preserved by right orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_right {W : Type*} [AddCommGroup W] [Module ℚ W]
    (h : L.IsNeighbor M p) (Y : IntegralLattice W) :
    (L.orthogonalSum Y).IsNeighbor (M.orthogonalSum Y) p := by
  have hswap := (h.orthogonalSum_left Y).transport (LinearEquiv.prodComm ℚ W V)
  rwa [orthogonalSum_transport_prodComm, orthogonalSum_transport_prodComm] at hswap

end TauCeti.IntegralLattice
