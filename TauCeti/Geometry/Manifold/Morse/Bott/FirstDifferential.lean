/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Filtration
import TauCeti.Algebra.Homology.Embedding.Restriction.Sequence
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage

/-!
# The first differential of the critical-value spectral sequence of the Bott complex

Let `B` be Bott chain data whose pushforwards strictly lower a value `v` of the critical components
(`TauCeti.BottChainData.filtration`). For cut values `b₀ ≤ b₁ ≤ b₂`, the components with value in
`Ioc b₀ b₁` form a lower part of those with value in `Ioc b₀ b₂`, with complement the components
with value in `Ioc b₁ b₂`, which gives the short exact sequence of two adjacent bands
`C(Ioc b₀ b₁) → C(Ioc b₀ b₂) → C(Ioc b₁ b₂)` (`TauCeti.BottChainData.adjacentBandSequence`). Its
connecting map sends the class of a cycle `x` of the upper band to the class of the part of its Bott
differential on the lower band, the sum of the trajectory correspondences `F_CD (x C)` from the
components `C` of the upper band to the components `D` of the lower one
(`TauCeti.BottChainData.chainComplexOnShortComplex_δ_homologyπ`).

For monotone cut values `a`, the first page of the critical-value spectral sequence has at `(p, q)`
the homology of the band `Ioc (a q) (a (q + 1))`
(`TauCeti.BottChainData.spectralSequenceFirstPageXIso`). This file shows that, under these
identifications, the differential of the first page from `(p, q + 1)` to `(p + 2, q)` is the
connecting map of the two adjacent bands `Ioc (a q) (a (q + 1))` and `Ioc (a (q + 1)) (a (q + 2))`
(`TauCeti.BottChainData.spectralSequence_first_page_d_eq_δ`). Hence it sends the class of a cycle
of the upper band to the class of the correspondences from that band to the lower one
(`TauCeti.BottChainData.spectralSequence_first_page_d_homologyπ`): the first differential counts
the trajectories between the components of adjacent bands. When the bands are the levels of the
negative-normal rank, so that adjacent bands differ in rank by one, these are the correspondences
`F_CD` with `λ_C - λ_D = 1`, which preserve the chain degree.

## Main definitions

* `TauCeti.BottChainData.adjacentBandSequence`: the short exact sequence of two adjacent bands.

## Main results

* `TauCeti.BottChainData.adjacentBandSequence_shortExact`: it is short exact.
* `TauCeti.BottChainData.spectralSequence_first_page_d_eq_δ`: the first differential of the
  critical-value spectral sequence is the connecting map of adjacent bands.
* `TauCeti.BottChainData.spectralSequence_first_page_d_homologyπ`: the first differential sends the
  class of a cycle of a band to the class of its correspondences to the band below.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.4 (the filtrations of the Morse–Bott complex and their
  spectral sequences).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 (the first differential of the spectral sequence of a filtered complex).
-/

public section

open CategoryTheory Limits HomologicalComplex Set

namespace TauCeti

namespace BottChainData

variable {R : Type*} [Ring R] {ι : Type*} {M : ι → Type*} [∀ C, AddCommGroup (M C)]
  [∀ C, Module R (M C)] [Fintype ι] (B : BottChainData R ι M)
  (v : ι → ℝ) (hv : ∀ C D, v C ≤ v D → B.pushforward C D = 0)
  {S : ∀ C, ℤ → Submodule R (M C)}
  (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
  (hpushforward : ∀ C D j, ∀ x ∈ S C j,
    B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))

variable {a : ℤ → ℝ} (ha : Monotone a)

/-! ### Comparison of the graded pieces with the bands -/

/-- The stage `m` of the critical-value filtration, as an object of the functor of the filtration,
is the regraded Bott complex of the components with value at most `a m`. -/
private noncomputable abbrev stageIso (m : ℤ) :=
  CochainComplex.filtrationFunctorObjIsoOfEqMk _
    (B.monotone_filtration v hv hboundary hpushforward ha)
    (B.filtrationι v hv hboundary hpushforward (a m))
    (B.filtration_eq_mk v hv hboundary hpushforward a m)

/-- Under `stageIso`, the transition maps of the functor of the filtration are the inclusions of
sublevel complexes. -/
@[reassoc]
private theorem filtrationFunctor_map_comp_stageIso_hom (m : ℤ) :
    (CochainComplex.filtrationFunctor _ (B.monotone_filtration v hv hboundary hpushforward ha)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : m = m) rfl)) ≫
      (B.stageIso v hv hboundary hpushforward ha (m + 1)).hom =
    (B.stageIso v hv hboundary hpushforward ha m).hom ≫
      restrictionMap
        (B.sublevelInclusion v hv hboundary hpushforward (ha.imp (Int.le_add_one le_rfl)))
        ComplexShape.embeddingUpIntDownInt :=
  CochainComplex.filtrationFunctor_map_comp_objIsoOfEqMk_hom _ _ _
    (B.filtration_eq_mk v hv hboundary hpushforward a) m _
    (B.restrictionMap_sublevelInclusion_comp_filtrationι v hv hboundary hpushforward _)

/-- The stage `q` of the filtration restricts to zero on the two bands above `a q`. -/
private theorem filtrationFunctor_map_comp_stageIso_hom_comp_eq_zero (q : ℤ) :
    (CochainComplex.filtrationFunctor _ (B.monotone_filtration v hv hboundary hpushforward ha)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl)) ≫
      (CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha)).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q + 1 = q + 1) rfl)) ≫
      (B.stageIso v hv hboundary hpushforward ha (q + 1 + 1)).hom ≫
        restrictionMap (B.bandSequence v hv hboundary hpushforward
          ((ha.imp (Int.le_add_one le_rfl)).trans (ha.imp (Int.le_add_one le_rfl)))).g
          ComplexShape.embeddingUpIntDownInt = 0 := by
  simp only [B.filtrationFunctor_map_comp_stageIso_hom_assoc, ← restrictionMap_comp]
  rw [B.sublevelInclusion_comp_bandSequence_g_eq_zero]
  simp [← ComplexShape.Embedding.restrictionFunctor_map]

/-- The first square of the comparison of the sequence of graded pieces with the regraded sequence
of adjacent bands. -/
private theorem π_filtrationCokernelIso_hom_comp_adjacentBandSequence_f (q : ℤ) :
    cokernel.π ((CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha)).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl))) ≫
      (B.filtrationCokernelIso v hv hboundary hpushforward ha q).hom ≫
        restrictionMap (B.adjacentBandSequence v hv hboundary hpushforward
          (ha.imp (Int.le_add_one le_rfl)) (ha.imp (Int.le_add_one le_rfl))).f
          ComplexShape.embeddingUpIntDownInt =
    (CochainComplex.filtrationFunctor _ (B.monotone_filtration v hv hboundary hpushforward ha)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q + 1 = q + 1) rfl)) ≫
      (B.stageIso v hv hboundary hpushforward ha (q + 1 + 1)).hom ≫
        restrictionMap (B.bandSequence v hv hboundary hpushforward
          ((ha.imp (Int.le_add_one le_rfl)).trans (ha.imp (Int.le_add_one le_rfl)))).g
          ComplexShape.embeddingUpIntDownInt := by
  simp only [π_filtrationCokernelIso_hom_assoc, ← restrictionMap_comp,
    B.filtrationFunctor_map_comp_stageIso_hom_assoc]
  rw [B.bandSequence_g_comp_adjacentBandSequence_f v hv hboundary hpushforward
    (ha.imp (Int.le_add_one le_rfl)) (ha.imp (Int.le_add_one le_rfl))]

/-- The second square of the comparison of the sequence of graded pieces with the regraded
sequence of adjacent bands. -/
private theorem stageIso_hom_comp_adjacentBandSequence_g (q : ℤ) :
    (B.stageIso v hv hboundary hpushforward ha (q + 1 + 1)).hom ≫
        restrictionMap (B.bandSequence v hv hboundary hpushforward
          ((ha.imp (Int.le_add_one le_rfl)).trans (ha.imp (Int.le_add_one le_rfl)))).g
          ComplexShape.embeddingUpIntDownInt ≫
        restrictionMap (B.adjacentBandSequence v hv hboundary hpushforward
          (ha.imp (Int.le_add_one le_rfl)) (ha.imp (Int.le_add_one le_rfl))).g
          ComplexShape.embeddingUpIntDownInt =
    cokernel.π ((CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha)).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q + 1 = q + 1) rfl))) ≫
      (B.filtrationCokernelIso v hv hboundary hpushforward ha (q + 1)).hom := by
  simp only [π_filtrationCokernelIso_hom, ← restrictionMap_comp]
  rw [B.bandSequence_g_comp_adjacentBandSequence_g v hv hboundary hpushforward
    (ha.imp (Int.le_add_one le_rfl)) (ha.imp (Int.le_add_one le_rfl))]

/-! ### The first differential -/

/-- **The first differential of the critical-value spectral sequence is the connecting map of
adjacent bands.** Under the identifications of the first page with the homology of the bands
(`TauCeti.BottChainData.spectralSequenceFirstPageXIso`), the differential of the first page from
`(p, q + 1)` to `(p + 2, q)`, where `p + q + 1 = -(k + 1)`, is the connecting map
`H_(k+1)(C(Ioc (a (q + 1)) (a (q + 2)))) → H_k(C(Ioc (a q) (a (q + 1))))` of the sequence of the
two adjacent bands (`TauCeti.BottChainData.adjacentBandSequence`). -/
theorem spectralSequence_first_page_d_eq_δ (p q k : ℤ) (hn : p + (q + 1) = -(k + 1)) :
    (B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha (p, q + 1) (k + 1) hn).inv ≫
        ((B.spectralSequence v hv hboundary hpushforward ha).page 2).d (p, q + 1) (p + 2, q) ≫
        (B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha (p + 2, q) k
          (by dsimp; lia)).hom =
      (B.adjacentBandSequence_shortExact v hv hboundary hpushforward
        (ha.imp (Int.le_add_one le_rfl)) (ha.imp (Int.le_add_one le_rfl))).δ (k + 1) k
          (by simp) := by
  have hd := CochainComplex.spectralSequence_first_page_d_eq_of_eq
    (CochainComplex.filtrationFunctor _ (B.monotone_filtration v hv hboundary hpushforward ha))
    (p, q + 1) (p + 2, q) (by simp) q (q + 1) (q + 1 + 1) rfl rfl rfl (p + (q + 1)) (p + 2 + q) rfl
    (by lia)
  -- the comparison of the sequence of graded pieces with the regraded sequence of adjacent bands
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := TauCeti.cokernelCompSequence
      ((CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha)).map
          (TauCeti.eIntHomOfLE (show q ≤ q + 1 by lia)))
      ((CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha)).map
          (TauCeti.eIntHomOfLE (show q + 1 ≤ q + 1 + 1 by lia))))
    (S₂ := (B.adjacentBandSequence v hv hboundary hpushforward (ha.imp (Int.le_add_one le_rfl))
      (ha.imp (Int.le_add_one le_rfl))).map
        (ComplexShape.embeddingUpIntDownInt.restrictionFunctor (ModuleCat R)))
    { τ₁ := (B.filtrationCokernelIso v hv hboundary hpushforward ha q).hom
      τ₂ := cokernel.desc _ ((B.stageIso v hv hboundary hpushforward ha (q + 1 + 1)).hom ≫
        restrictionMap (B.bandSequence v hv hboundary hpushforward
          ((ha.imp (Int.le_add_one le_rfl)).trans (ha.imp (Int.le_add_one le_rfl)))).g
          ComplexShape.embeddingUpIntDownInt)
        ((Category.assoc _ _ _).trans
          (B.filtrationFunctor_map_comp_stageIso_hom_comp_eq_zero v hv hboundary hpushforward ha q))
      τ₃ := (B.filtrationCokernelIso v hv hboundary hpushforward ha (q + 1)).hom
      comm₁₂ := by
        apply coequalizer.hom_ext
        simp only [Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc, ShortComplex.map_f,
          ComplexShape.Embedding.restrictionFunctor_map]
        exact B.π_filtrationCokernelIso_hom_comp_adjacentBandSequence_f v hv hboundary hpushforward
          ha q
      comm₂₃ := by
        apply coequalizer.hom_ext
        simp only [Category.assoc, cokernel.π_desc_assoc, Category.id_comp, ShortComplex.map_g,
          ComplexShape.Embedding.restrictionFunctor_map]
        exact B.stageIso_hom_comp_adjacentBandSequence_g v hv hboundary hpushforward ha q }
    (TauCeti.cokernelCompSequence_shortExact _ _)
    ((B.adjacentBandSequence_shortExact v hv hboundary hpushforward _ _).restriction _)
    (p + (q + 1)) (p + 2 + q) (by simp; lia)
  rw [spectralSequenceFirstPageXIso_eq, spectralSequenceFirstPageXIso_eq]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Functor.mapIso_inv, Functor.mapIso_hom]
  rw [hd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, homologyFunctor_map]
  dsimp only at hnat
  rw [reassoc_of% hnat, ← homologyMap_comp_assoc, Iso.inv_hom_id, homologyMap_id,
    Category.id_comp]
  exact (B.adjacentBandSequence_shortExact v hv hboundary hpushforward _ _
    ).moduleCat_restrictionHomologyIso_inv_δ_hom ComplexShape.embeddingUpIntDownInt
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _


/-- **The first differential of the critical-value spectral sequence on classes.** The
differential of the first page from `(p, q + 1)` to `(p + 2, q)`, where `p + q + 1 = -(k + 1)`,
sends the class of a cycle `x` of the band `Ioc (a (q + 1)) (a (q + 2))` in total degree `k + 1`
to the class of the part of its Bott differential on the band `Ioc (a q) (a (q + 1))` below, that is
of the chain `∑_C F_CD (x C)` on the components `D` of the lower band, summed over the components
`C` of the upper band. The cycle `z'` of the lower band is given with this chain as underlying
chain. -/
theorem spectralSequence_first_page_d_homologyπ (p q k : ℤ) (hn : p + (q + 1) = -(k + 1))
    (z : (B.complexOn v hv hboundary hpushforward (Ioc (a (q + 1)) (a (q + 1 + 1)))).cycles (k + 1))
    (z' : (B.complexOn v hv hboundary hpushforward (Ioc (a q) (a (q + 1)))).cycles k)
    (hz' : (((B.complexOn v hv hboundary hpushforward (Ioc (a q) (a (q + 1)))).iCycles k).hom z' :
        (B.restrict (fun C ↦ v C ∈ Ioc (a q) (a (q + 1)))
          (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv _)).totalDegree
            (restrictGrading (fun C ↦ v C ∈ Ioc (a q) (a (q + 1))) S) k).val =
      restrictProj R (fun C ↦ v C ∈ Ioc (a q) (a (q + 1))) (B.differential
        (((B.complexOn v hv hboundary hpushforward
          (Ioc (a (q + 1)) (a (q + 1 + 1)))).iCycles (k + 1)).hom z :
            (B.restrict (fun C ↦ v C ∈ Ioc (a (q + 1)) (a (q + 1 + 1)))
              (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv _)).totalDegree
                (restrictGrading (fun C ↦ v C ∈ Ioc (a (q + 1)) (a (q + 1 + 1))) S) (k + 1)).val)) :
    (B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha (p + 2, q) k
        (by dsimp; lia)).hom.hom
      ((((B.spectralSequence v hv hboundary hpushforward ha).page 2).d (p, q + 1) (p + 2, q)).hom
        ((B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha (p, q + 1) (k + 1)
          hn).inv.hom (((B.complexOn v hv hboundary hpushforward
            (Ioc (a (q + 1)) (a (q + 1 + 1)))).homologyπ (k + 1)).hom z))) =
      ((B.complexOn v hv hboundary hpushforward (Ioc (a q) (a (q + 1)))).homologyπ k).hom z' := by
  have h := congrArg (fun φ ↦ φ.hom (((B.complexOn v hv hboundary hpushforward
    (Ioc (a (q + 1)) (a (q + 1 + 1)))).homologyπ (k + 1)).hom z))
    (B.spectralSequence_first_page_d_eq_δ v hv hboundary hpushforward ha p q k hn)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  exact B.chainComplexOnShortComplex_δ_homologyπ _ _ _ _ _ _ _ _ _ _ k z z' hz'

end BottChainData

end TauCeti
