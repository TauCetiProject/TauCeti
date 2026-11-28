/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.ClassSum
public import TauCeti.Topology.Algebra.Group.Cocompact

/-!
# Finite class sets of compact quotients

For an open subgroup `K`, a compact set meets only finitely many right `K`-cosets. Consequently,
if `G ⧸ Γ` is compact, the double coset set `Γ \ G / K` is finite. Conversely, when `K` is
compact, finiteness of that class set gives a compact set whose left `Γ`-translates cover `G`.

If `Γ` is discrete, compactness of `K` also makes every stabilizer `Γ ∩ g K g⁻¹` finite.
Thus, for a discrete subgroup and a compact open level, compactness of `G ⧸ Γ` is equivalent to
`TauCeti.HasFiniteType Γ K`. This supplies the finite class sets and stabilizers needed for
weighted class sums on definite groups.

## References

* B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§2, 4.

The finite-type conclusion is the topological step in `New.Space.hasFiniteType_of_isLevel` in
`src/Lib/Adelic/Reduction/DefiniteClassSums.lean` of grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0). The proofs here work for arbitrary topological groups and use the existing
compact images of coset projections.
-/

public section

open Set
open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open level has a finite double coset set when `G ⧸ Γ` is compact. -/
theorem finite_doubleCoset_of_compactSpace_quotient
    (Γ K : Subgroup G) [CompactSpace (G ⧸ Γ)] (hK : IsOpen (K : Set G)) :
    Finite (DoubleCoset.Quotient (Γ : Set G) K) := by
  classical
  -- The open sets which are images of `K g` cover `G ⧸ Γ`. A finite subcover supplies
  -- representatives for the inverse double cosets.
  let U (g : G) : Set (G ⧸ Γ) := QuotientGroup.mk '' ((K : Set G) * {g})
  have hU (g : G) : IsOpen (U g) := QuotientGroup.isOpenMap_coe _ hK.mul_right
  have hcover : (univ : Set (G ⧸ Γ)) ⊆ ⋃ g, U g := by
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact mem_iUnion.mpr ⟨g, g, ⟨1, K.one_mem, g, mem_singleton _, one_mul g⟩, rfl⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have himage : (fun g : G ↦ DoubleCoset.mk Γ K g⁻¹) '' (S : Set G) = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨g, hg, y, hy, hyq⟩ :=
      mem_iUnion₂.mp (hS (mem_univ (QuotientGroup.mk (q.out⁻¹) : G ⧸ Γ)))
    obtain ⟨k, hk, z, hz, hprod⟩ := hy
    have hz' : z = g := mem_singleton_iff.mp hz
    rw [hz'] at hprod
    rw [← hprod] at hyq
    refine ⟨g, hg, ?_⟩
    rw [← DoubleCoset.out_eq' q]
    apply DoubleCoset.eq.mpr
    have hγ : (k * g)⁻¹ * q.out⁻¹ ∈ Γ := QuotientGroup.eq.mp hyq
    refine ⟨((k * g)⁻¹ * q.out⁻¹)⁻¹, Γ.inv_mem hγ, k⁻¹, K.inv_mem hk, ?_⟩
    simp [mul_inv_rev, mul_assoc]
  exact finite_univ_iff.mp (himage ▸ S.finite_toSet.image _)

/-- If `K` is compact and `Γ \ G / K` is finite, a compact set has left `Γ`-translates covering
`G`. No separation, openness or discreteness hypothesis is needed. -/
theorem exists_isCompact_mul_eq_univ_of_finite_doubleCoset (Γ K : Subgroup G)
    (hK : IsCompact (K : Set G)) [Finite (DoubleCoset.Quotient (Γ : Set G) K)] :
    ∃ C : Set G, IsCompact C ∧ (Γ : Set G) * C = univ := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) K)
  refine ⟨⋃ q : DoubleCoset.Quotient (Γ : Set G) K, {q.out} * (K : Set G),
    isCompact_iUnion fun q ↦ isCompact_singleton.mul hK, ?_⟩
  apply eq_univ_of_forall
  intro g
  obtain ⟨γ, hγ, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  refine ⟨γ⁻¹, Γ.inv_mem hγ, γ * g, ?_, inv_mul_cancel_left γ g⟩
  apply mem_iUnion.mpr
  refine ⟨DoubleCoset.mk Γ K g, ?_⟩
  exact ⟨_, mem_singleton _, k⁻¹, K.inv_mem hk, by rw [hout]; simp⟩

/-- For a compact subgroup `K`, finiteness of `Γ \ G / K` implies compactness of `G ⧸ Γ`. -/
theorem compactSpace_quotient_of_finite_doubleCoset
    (Γ K : Subgroup G) (hK : IsCompact (K : Set G))
    [Finite (DoubleCoset.Quotient (Γ : Set G) K)] : CompactSpace (G ⧸ Γ) := by
  obtain ⟨C, hC, hΓC⟩ := exists_isCompact_mul_eq_univ_of_finite_doubleCoset Γ K hK
  have hCΓ : C⁻¹ * (Γ : Set G) = univ := by
    have hinv := congrArg (fun S : Set G ↦ S⁻¹) hΓC
    simpa only [mul_inv_rev, inv_coe_set, inv_univ] using hinv
  have himage := QuotientGroup.image_mk_eq_univ_iff.mpr hCΓ
  exact isCompact_univ_iff.mp (himage ▸ hC.inv.image QuotientGroup.continuous_mk)

/-- A discrete subgroup has finite stabilizers at every compact level. -/
theorem finite_mackeySubgroup_of_isCompact (Γ K : Subgroup G) [DiscreteTopology Γ]
    (hK : IsCompact (K : Set G)) (g : G) : Finite (TauCeti.mackeySubgroup g K Γ) := by
  have hfin := Γ.finite_preimage_coe_of_isCompact
    (((isCompact_singleton (x := g)).mul hK).mul (isCompact_singleton (x := g⁻¹)))
  let f : TauCeti.mackeySubgroup g K Γ →
      {γ : Γ // (γ : G) ∈ ({g} * (K : Set G)) * {g⁻¹}} := fun x ↦
    ⟨⟨x, (TauCeti.mem_mackeySubgroup_iff.mp x.property).1⟩,
      ⟨g * (g⁻¹ * x * g), ⟨g, mem_singleton _, g⁻¹ * x * g,
        (TauCeti.mem_mackeySubgroup_iff.mp x.property).2, rfl⟩,
        g⁻¹, mem_singleton _, by simp [mul_assoc]⟩⟩
  have : Finite {γ : Γ // (γ : G) ∈ ({g} * (K : Set G)) * {g⁻¹}} := hfin.to_subtype
  exact Finite.of_injective f fun x y h ↦ Subtype.ext (congrArg (fun z ↦ (z.val : G)) h)

/-- A discrete subgroup with compact coset space has finite type at every compact open level. -/
theorem hasFiniteType_of_compactSpace_quotient
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (hK_open : IsOpen (K : Set G)) (hK_compact : IsCompact (K : Set G)) :
    TauCeti.HasFiniteType Γ K where
  isOpen := hK_open
  isCompact := hK_compact
  finite_doubleCoset := Γ.finite_doubleCoset_of_compactSpace_quotient K hK_open
  finite_mackeySubgroup := Γ.finite_mackeySubgroup_of_isCompact K hK_compact

end Subgroup

namespace TauCeti.HasFiniteType

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ K : Subgroup G}

/-- A pair of finite type has compact coset space. -/
theorem compactSpace_quotient (h : HasFiniteType Γ K) : CompactSpace (G ⧸ Γ) := by
  let := h.finite_doubleCoset
  exact Γ.compactSpace_quotient_of_finite_doubleCoset K h.isCompact

end TauCeti.HasFiniteType

namespace Subgroup

/-- For a discrete subgroup and a compact open level, finite type is equivalent to compactness
of the coset space. -/
theorem hasFiniteType_iff_compactSpace_quotient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ K : Subgroup G)
    [DiscreteTopology Γ] (hK_open : IsOpen (K : Set G)) (hK_compact : IsCompact (K : Set G)) :
    TauCeti.HasFiniteType Γ K ↔ CompactSpace (G ⧸ Γ) := by
  refine ⟨TauCeti.HasFiniteType.compactSpace_quotient, fun h ↦ ?_⟩
  let := h
  exact Γ.hasFiniteType_of_compactSpace_quotient K hK_open hK_compact

end Subgroup
