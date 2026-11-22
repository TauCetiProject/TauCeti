/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Quotient
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Positive
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word

/-!
# Intersections of the Borel and positive subgroups with the Weyl subgroup

For a Chevalley datum `D` over an arbitrary commutative ring `A` (including nonreduced rings,
finite fields, `𝔽₂`, and the zero ring), the intersection of `D.borelSubgroup A` with
`D.weylSubgroup A` is the actual weight-lattice torus `(D.torusPoints A).range`, and the positive
subgroup `D.positivePoints A` meets `D.weylSubgroup A` trivially.

When `A` is nontrivial, writing any `g ∈ B(A) ∩ N(A)` as a Weyl word times an actual torus point
puts the Weyl word in `B(A)`. By `ChevalleyDatum.geckWeylWordProd_eq_one_of_mem_borelSubgroup`, the
word spells `1` in `W`, so `D.weylQuotientMulEquiv A` sends `[g]` to `1`. Hence `g ∈ T_D(A)`.
Combining `B(A) ∩ N(A) = T_D(A)` with `U(A) ∩ T_D(A) = ⊥` from `Chevalley.Borel` gives
`U(A) ∩ N(A) = ⊥`, and over fields `D.ker_weylProjection` yields `D.weylProjection K g = 1` for
`g ∈ B(K) ∩ N(K)`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints`:
  `D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range` over any commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.positivePoints_inf_weylSubgroup_eq_bot`:
  `D.positivePoints A ⊓ D.weylSubgroup A = ⊥` over any commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_subgroupOf_weylSubgroup`:
  `(D.borelSubgroup A).subgroupOf (D.weylSubgroup A) =`
  `((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)`.
* `TauCeti.DynkinType.ChevalleyDatum.`
  `mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup`:
  pointwise membership criterion for `B(A) ∩ N(A) = T(A)`.
* `TauCeti.DynkinType.ChevalleyDatum.normal_borelSubgroup_subgroupOf_weylSubgroup`:
  `B(A) ∩ N(A)` is normal in `N(A)`.
* `TauCeti.DynkinType.ChevalleyDatum.weylSubgroup_conj_torusPoints_mem_borelSubgroup`:
  `D.weylSubgroup A` conjugates actual torus points into `D.borelSubgroup A`.
* `TauCeti.DynkinType.ChevalleyDatum.weylProjection_eq_one_of_mem_borelSubgroup`:
  any element of `N(K)` lying in `B(K)` has trivial Weyl projection.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 22 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

/-- Over any nontrivial commutative ring, if a product of pinned simple Weyl representatives
equals an actual torus point times a positive point, then the Weyl word evaluates to `1` in the
Weyl group. -/
theorem geckWeylWordProd_eq_one_of_list_prod_eq_torusPoints_mul_positive [Nontrivial A]
    {l : List (Fin t.rank)} {s : Fin t.rank → Aˣ} {u : D.points A}
    (hu : u ∈ D.positivePoints A)
    (h : (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod =
      D.torusPoints A s * u) :
    t.geckWeylWordProd ht l = 1 :=
  D.geckWeylWordProd_eq_one_of_mem_borelSubgroup A l <| h ▸
    mul_mem (D.range_torusPoints_le_borelSubgroup A ⟨s, rfl⟩)
      (D.positivePoints_le_borelSubgroup A hu)

/-- Conjugating any point of the actual weight-lattice torus by an element of `D.weylSubgroup A`
stays inside `D.borelSubgroup A`. -/
theorem weylSubgroup_conj_torusPoints_mem_borelSubgroup (w : D.weylSubgroup A)
    (s : Fin t.rank → Aˣ) :
    (w : D.points A) * D.torusPoints A s * (w : D.points A)⁻¹ ∈ D.borelSubgroup A :=
  D.range_torusPoints_le_borelSubgroup A <|
    (Subgroup.mem_normalizer_iff.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints A w.property)
      (D.torusPoints A s)).mp ⟨s, rfl⟩

/-- Over any commutative ring, the intersection of the Borel subgroup with the Weyl subgroup is
the actual weight-lattice torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range := by
  rcases subsingleton_or_nontrivial A with _ | _
  · apply le_antisymm
    · rintro g -
      exact ⟨1, Subtype.ext (Subsingleton.elim _ _)⟩
    · exact le_inf (D.range_torusPoints_le_borelSubgroup A) (D.range_torusPoints_le_weylSubgroup A)
  · apply le_antisymm
    · rintro g ⟨hgB, hgW⟩
      obtain ⟨l, s, hls⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp hgW
      have hwB : (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈
          D.borelSubgroup A := by
        have hts : (D.torusPoints A s)⁻¹ ∈ D.borelSubgroup A := by
          rw [← (D.torusPoints A).map_inv]
          exact D.range_torusPoints_le_borelSubgroup A ⟨s⁻¹, rfl⟩
        simpa only [← hls, mul_inv_cancel_right] using Subgroup.mul_mem _ hgB hts
      have hword : t.geckWeylWordProd ht l = 1 :=
        D.geckWeylWordProd_eq_one_of_mem_borelSubgroup A l hwB
      have hsub : (⟨g, hgW⟩ : D.weylSubgroup A) =
          ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A s,
            mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
              (D.torusPoints_mem_weylSubgroup A s)⟩ :=
        Subtype.ext hls.symm
      have hq : D.weylQuotientMulEquiv A (QuotientGroup.mk ⟨g, hgW⟩) = 1 := by
        rw [hsub, D.weylQuotientMulEquiv_list_prod_mul_torusPoints A l s, hword]
      have hmk : (QuotientGroup.mk ⟨g, hgW⟩ :
          D.weylSubgroup A ⧸ ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A)) = 1 :=
        (D.weylQuotientMulEquiv A).injective (hq.trans (map_one _).symm)
      exact (QuotientGroup.eq_one_iff (⟨g, hgW⟩ : D.weylSubgroup A)).mp hmk
    · exact le_inf (D.range_torusPoints_le_borelSubgroup A) (D.range_torusPoints_le_weylSubgroup A)

/-- Over any commutative ring, the intersection of the Weyl subgroup with the Borel subgroup is
the actual weight-lattice torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup_eq_range_torusPoints :
    D.weylSubgroup A ⊓ D.borelSubgroup A = (D.torusPoints A).range := by
  rw [inf_comm, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints A]

/-- Over any commutative ring, the positive subgroup meets the Weyl subgroup trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints A ⊓ D.weylSubgroup A = ⊥ := by
  rw [eq_bot_iff, ← D.positivePoints_inf_range_torusPoints_eq_bot A,
    ← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints A]
  exact le_inf inf_le_left
    (le_inf (inf_le_left.trans (D.positivePoints_le_borelSubgroup A)) inf_le_right)

/-- Over any commutative ring, the Weyl subgroup meets the positive subgroup trivially. -/
@[simp]
theorem weylSubgroup_inf_positivePoints_eq_bot :
    D.weylSubgroup A ⊓ D.positivePoints A = ⊥ := by
  rw [inf_comm, D.positivePoints_inf_weylSubgroup_eq_bot A]

/-- Read inside `D.weylSubgroup A`, the Borel subgroup cuts out the actual weight-lattice torus,
over every commutative ring. -/
@[simp]
theorem borelSubgroup_subgroupOf_weylSubgroup :
    (D.borelSubgroup A).subgroupOf (D.weylSubgroup A) =
      ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A) := by
  rw [Subgroup.subgroupOf_inj, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints,
    inf_eq_left.mpr (D.range_torusPoints_le_weylSubgroup A)]

/-- Over any commutative ring, an element of `D.weylSubgroup A` belongs to `D.borelSubgroup A` if
and only if it lies in the image of the actual torus. -/
theorem mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup
    {n : D.points A} (hn : n ∈ D.weylSubgroup A) :
    n ∈ D.borelSubgroup A ↔ n ∈ (D.torusPoints A).range := by
  rw [← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints A, Subgroup.mem_inf]
  exact (and_iff_left hn).symm

/-- `B ∩ N` is normal in `N`: it is the actual torus, which `N` normalizes. This is the normality
axiom of a Tits system with these subgroups. -/
instance normal_borelSubgroup_subgroupOf_weylSubgroup :
    ((D.borelSubgroup A).subgroupOf (D.weylSubgroup A)).Normal := by
  rw [D.borelSubgroup_subgroupOf_weylSubgroup A]
  infer_instance

/-- Any element of the Weyl subgroup that also belongs to the positive Borel subgroup has trivial
Weyl projection. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup (K : Type v) [Field K]
    {g : D.weylSubgroup K} (hg : (g : D.points K) ∈ D.borelSubgroup K) :
    D.weylProjection K g = 1 :=
  (D.weylProjection_eq_one_iff_mem_range_torusPoints K g).mpr
    ((D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K g.property).mp hg)

end TauCeti.DynkinType.ChevalleyDatum
