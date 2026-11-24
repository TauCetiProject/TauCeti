/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.StrongSite.Basic
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Subdomain

import TauCeti.RingTheory.Affinoid.Subdomain.Cover

/-!
# Zariski open covers and idempotents on the strong affinoid site

Following [BGR, §9.1.4, Corollaries 7 and 8], the strong classical affinoid G-topology on
`Sp A = MaximalSpectrum A` is finer than the Zariski topology:

* Every principal Zariski open `D(f) = MaximalSpectrum.basicOpen f` is exhausted by the rational
  domains `R(ϖⁿ / f)` for `0 < ‖ϖ‖ < 1` (`isAffinoidTestRefined_basicOpen_rationalDomain`), making
  `D(f)` strong-admissible open (`StrongAdmissibleOpen.basicOpen`).
* Every Zariski open and Zariski open cover of `Sp A` is strong-admissible
  (`StrongAdmissibleOpen.zariskiContinuousMap`).
* Every idempotent `e ∈ A` yields a strong-admissible clopen cover `{D(e), D(1 - e)}` of `Sp A` by
  the disjoint affinoid subdomains `AffinoidSubdomain.ofIsIdempotentElem`
  (`StrongAdmissibleOpen.covers_ofIsIdempotentElem`).

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §9.1.4,
  Corollary 7 and Corollary 8.
-/

public section

open TopologicalSpace

namespace TauCeti

universe u

section Zariski

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- A principal Zariski open `D(f)` is exhausted by the rational domains `R(ϖⁿ / f)` for any
`‖ϖ‖ < 1`. -/
theorem basicOpen_eq_iUnion_rationalDomain (hA : IsAffinoidAlgebra K A) (f : A)
    {ϖ : K} (hϖ₁ : ‖ϖ‖ < 1) :
    (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A)) =
      ⋃ n : ℕ, rationalDomain K f (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n)) := by
  ext x
  simp only [SetLike.mem_coe, MaximalSpectrum.mem_basicOpen, Set.mem_iUnion,
    mem_rationalDomain, forall_const, pointNorm_algebraMap, norm_pow, ne_eq,
    hA.pointNorm_eq_zero_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨_, hx, _⟩ ↦ hx⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_of_le_of_ne (pointNorm_nonneg f) (Ne.symm (hA.pointNorm_eq_zero_iff.not.mpr hx))) hϖ₁
  exact ⟨n, hx, hn.le⟩

/-- The rational exhaustion `R(ϖⁿ / f)` of `MaximalSpectrum.basicOpen f` is affinoid-test
refined. -/
theorem isAffinoidTestRefined_basicOpen_rationalDomain (f : A) {ϖ : K} (hϖ₁ : ‖ϖ‖ < 1) :
    IsAffinoidTestRefined K (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A))
      (Set.range fun n : ℕ ↦ rationalDomain K f (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n))) := by
  rw [isAffinoidTestRefined_iff]
  intro B _ _ hB φ hφ
  have hunit : IsUnit (φ f) := hB.isUnit_iff_forall_pointNorm_ne_zero.mpr fun y ↦ by
    have hy : hB.maximalSpectrumComap φ y ∈ MaximalSpectrum.basicOpen f := hφ ⟨y, rfl⟩
    rw [MaximalSpectrum.mem_basicOpen, IsAffinoidAlgebra.maximalSpectrumComap_asIdeal,
      Ideal.mem_comap] at hy
    exact hB.pointNorm_eq_zero_iff.not.mpr hy
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖ϖ‖ ^ n * supSeminorm K u ≤ 1 := by
    rcases eq_or_lt_of_le (supSeminorm_nonneg (K := K) u) with h0 | hpos
    · exact ⟨0, by simp [← h0]⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hϖ₁
      exact ⟨n, (inv_mul_cancel₀ hpos.ne' ▸ mul_lt_mul_of_pos_right hn hpos).le⟩
  refine ⟨{AffinoidSubdomain.univ hB}, Set.finite_singleton _, by simp, fun W hW ↦ ?_⟩
  rw [Set.mem_singleton_iff.mp hW, AffinoidSubdomain.coe_univ]
  refine ⟨_, ⟨n, rfl⟩, fun y _ ↦ ?_⟩
  rw [Set.mem_preimage, mem_rationalDomain, hB.pointNorm_maximalSpectrumComap]
  refine ⟨hB.isUnit_iff_forall_pointNorm_ne_zero.mp hunit y, fun _ ↦ ?_⟩
  rw [hB.pointNorm_maximalSpectrumComap, AlgHom.commutes, pointNorm_algebraMap, norm_pow]
  have h1 : 1 ≤ pointNorm K y (φ f) * supSeminorm K u := by
    rw [← pointNorm_one (K := K) (x := y), ← hu, hB.pointNorm_mul]
    exact mul_le_mul_of_nonneg_left (hB.pointNorm_le_supSeminorm y u) (pointNorm_nonneg _)
  calc ‖ϖ‖ ^ n ≤ ‖ϖ‖ ^ n * (pointNorm K y (φ f) * supSeminorm K u) :=
        le_mul_of_one_le_right (pow_nonneg (norm_nonneg _) _) h1
    _ = pointNorm K y (φ f) * (‖ϖ‖ ^ n * supSeminorm K u) := by ring
    _ ≤ pointNorm K y (φ f) := mul_le_of_le_one_right (pointNorm_nonneg _) hn

/-- Any Zariski open cover of a subset `U ⊆ Sp A` is affinoid-test refined. -/
theorem isAffinoidTestRefined_opens_of_subset {U : Set (MaximalSpectrum A)}
    {S : Set (Opens (MaximalSpectrum A))}
    (hUS : U ⊆ ⋃₀ (((↑) : Opens (MaximalSpectrum A) → Set (MaximalSpectrum A)) '' S)) :
    IsAffinoidTestRefined K U
      (((↑) : Opens (MaximalSpectrum A) → Set (MaximalSpectrum A)) '' S) := by
  classical
  rw [isAffinoidTestRefined_iff]
  intro B _ _ hB φ hφ
  let P : Set B :=
    {b | ∃ g : A, ∃ W ∈ S, (MaximalSpectrum.basicOpen g : Set (MaximalSpectrum A)) ⊆ W ∧ φ g = b}
  have hspan : Ideal.span P = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span P) hne
    let y : MaximalSpectrum B := ⟨m, hm⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW⟩ := hUS (hφ ⟨y, rfl⟩)
    obtain ⟨_, ⟨g, rfl⟩, hxg, hgW⟩ :=
      MaximalSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp (W.isOpen.mem_nhds hxW)
    have hxg' : hB.maximalSpectrumComap φ y ∈ MaximalSpectrum.basicOpen g := hxg
    rw [MaximalSpectrum.mem_basicOpen, IsAffinoidAlgebra.maximalSpectrumComap_asIdeal,
      Ideal.mem_comap] at hxg'
    exact hxg' (hle (Ideal.subset_span ⟨g, W, hW, hgW, rfl⟩))
  obtain ⟨F, hFP, hFtop⟩ := (Ideal.span_eq_top_iff_finite P).mp hspan
  let h : Fin F.card → B := fun i ↦ (F.equivFin.symm i).val
  have hrange : Set.range h = (F : Set B) := Set.ext fun b ↦
    ⟨fun ⟨i, hi⟩ ↦ hi ▸ (F.equivFin.symm i).property, fun hb ↦ ⟨F.equivFin ⟨b, hb⟩, by simp [h]⟩⟩
  have htop : Ideal.span (Set.range h) = ⊤ := hrange.symm ▸ hFtop
  have htop_ins (i : Fin F.card) : Ideal.span (insert (h i) (Set.range h)) = ⊤ := by
    simpa only [Set.insert_eq_of_mem (Set.mem_range_self i)] using htop
  refine ⟨Set.range fun i ↦ AffinoidSubdomain.rational hB (htop_ins i), Set.finite_range _, ?_, ?_⟩
  · rw [← Set.range_comp, Set.sUnion_range]
    simpa only [Function.comp_def, AffinoidSubdomain.coe_rational] using
      (hB.iUnion_rationalDomain_self_eq_univ_iff h).mpr htop
  · rintro _ ⟨i, rfl⟩
    obtain ⟨g, W, hW, hgW, hg_eq⟩ := hFP (F.equivFin.symm i).property
    refine ⟨W, ⟨W, hW, rfl⟩, fun y hy ↦ hgW ?_⟩
    rw [AffinoidSubdomain.coe_rational, mem_rationalDomain] at hy
    rw [SetLike.mem_coe, MaximalSpectrum.mem_basicOpen,
      IsAffinoidAlgebra.maximalSpectrumComap_asIdeal, Ideal.mem_comap]
    exact hB.pointNorm_eq_zero_iff.not.mp (hg_eq ▸ hy.1)

namespace StrongAdmissibleOpen

/-- Every principal Zariski open `D(f)` is strong-admissible open [BGR, §9.1.4, Corollary 7]. -/
noncomputable def basicOpen (hA : IsAffinoidAlgebra K A) (f : A) :
    StrongAdmissibleOpen K A where
  carrier := MaximalSpectrum.basicOpen f
  exists_affinoid_cover := by
    obtain ⟨ϖ, hϖ₀, hϖ₁⟩ := NormedField.exists_norm_lt_one K
    have htop (n : ℕ) :
        Ideal.span (insert f (Set.range (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n)))) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
        ((IsUnit.pow n (Ne.isUnit (norm_pos_iff.mp hϖ₀))).map (algebraMap K A))
    let S := Set.range fun n : ℕ ↦ AffinoidSubdomain.rational hA (htop n)
    have himg : ((↑) : AffinoidSubdomain K A → Set (MaximalSpectrum A)) '' S =
        Set.range fun n : ℕ ↦ rationalDomain K f (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n)) := by
      ext; simp [S]
    refine ⟨S, ?_, himg ▸ isAffinoidTestRefined_basicOpen_rationalDomain f hϖ₁⟩
    rw [himg, Set.sUnion_range, ← basicOpen_eq_iUnion_rationalDomain hA f hϖ₁]

@[simp]
theorem coe_basicOpen (hA : IsAffinoidAlgebra K A) (f : A) :
    (basicOpen hA f : Set (MaximalSpectrum A)) = MaximalSpectrum.basicOpen f := (rfl)

private theorem exists_affinoid_cover_opens (hA : IsAffinoidAlgebra K A)
    (U : Opens (MaximalSpectrum A)) :
    ∃ T : Set (AffinoidSubdomain K A),
      ⋃₀ (((↑) : AffinoidSubdomain K A → Set (MaximalSpectrum A)) '' T) = U ∧
        IsAffinoidTestRefined K (U : Set (MaximalSpectrum A))
          (((↑) : AffinoidSubdomain K A → Set (MaximalSpectrum A)) '' T) := by
  let S := basicOpen hA '' {f : A | (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A)) ⊆ U}
  have himg : ((↑) : StrongAdmissibleOpen K A → Set (MaximalSpectrum A)) '' S =
      ((↑) : Opens (MaximalSpectrum A) → Set (MaximalSpectrum A)) ''
        (MaximalSpectrum.basicOpen ''
          {f : A | (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A)) ⊆ U}) := by
    simp only [S, Set.image_image, coe_basicOpen]
  have hSu : ⋃₀ (((↑) : StrongAdmissibleOpen K A → Set (MaximalSpectrum A)) '' S) = U := by
    refine Set.Subset.antisymm (by rintro x ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, hxf⟩; exact hf hxf) ?_
    intro x hx
    obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
      MaximalSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp (U.isOpen.mem_nhds hx)
    exact ⟨MaximalSpectrum.basicOpen f, ⟨basicOpen hA f, ⟨f, hfU, rfl⟩, rfl⟩, hxf⟩
  obtain ⟨W, hWU⟩ := mem_range_of_testRefined hSu
    (himg ▸ isAffinoidTestRefined_opens_of_subset (himg ▸ hSu.ge))
  rw [setEmbedding_apply] at hWU
  obtain ⟨T, hTu, hT⟩ := W.exists_affinoidSubdomain_cover
  exact ⟨T, hTu.trans hWU, hWU ▸ hT⟩

section Site

variable [hA : Fact (IsAffinoidAlgebra K A)]

/-- Every Zariski open subset of `Sp A` is strong-admissible open [BGR, §9.1.4, Corollary 7]. -/
noncomputable def ofOpens (U : Opens (MaximalSpectrum A)) : StrongAdmissibleOpen K A :=
  ⟨U, exists_affinoid_cover_opens hA.out U⟩

@[simp]
theorem coe_ofOpens (U : Opens (MaximalSpectrum A)) :
    (ofOpens (K := K) U : Set (MaximalSpectrum A)) = U := (rfl)

/-- **Admissibility of Zariski opens and Zariski covers** [BGR, §9.1.4, Corollary 7]. -/
noncomputable def zariskiContinuousMap :
    (strongGTopology (K := K) (A := A)).ContinuousMap
      (GTopology.topological (MaximalSpectrum A)) where
  toFun := id
  comap := ofOpens
  coe_comap' _ := by simp
  covers_comap {U S} hS := by
    rw [GTopology.topological_covers_iff] at hS
    refine strongGTopology_covers_iff.mpr ⟨?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact SetLike.coe_subset_coe.mp (hS ▸ Set.subset_sUnion_of_mem ⟨V, hV, rfl⟩)
    · simpa only [Set.image_image, coe_ofOpens] using isAffinoidTestRefined_opens_of_subset hS.ge

@[simp]
theorem coe_zariskiContinuousMap : ⇑(zariskiContinuousMap (K := K) (A := A)) = id := (rfl)

@[simp]
theorem zariskiContinuousMap_comap :
    (zariskiContinuousMap (K := K) (A := A)).comap = ofOpens := (rfl)

/-- Every idempotent `e ∈ A` gives a strong-admissible clopen cover `{D(e), D(1 - e)}` of `Sp A`
by disjoint affinoid subdomains. -/
theorem covers_ofIsIdempotentElem {e : A} (he : IsIdempotentElem e) :
    strongGTopology.Covers ⊤
      {(AffinoidSubdomain.ofIsIdempotentElem hA.out he).toStrongAdmissibleOpen,
        (AffinoidSubdomain.ofIsIdempotentElem hA.out he.one_sub).toStrongAdmissibleOpen} := by
  have hcov : (GTopology.topological (MaximalSpectrum A)).Covers ⊤
      {MaximalSpectrum.basicOpen e, MaximalSpectrum.basicOpen (1 - e)} := by
    rw [GTopology.topological_covers_iff, Set.image_pair, Set.sUnion_pair,
      ← Opens.coe_sup, MaximalSpectrum.basicOpen_sup_basicOpen_one_sub]
  have h := (zariskiContinuousMap (K := K) (A := A)).covers_comap hcov
  rw [GTopology.ContinuousMap.comap_top, zariskiContinuousMap_comap, Set.image_pair] at h
  have he_eq : ofOpens (K := K) (MaximalSpectrum.basicOpen e) =
      (AffinoidSubdomain.ofIsIdempotentElem hA.out he).toStrongAdmissibleOpen :=
    SetLike.coe_injective (by simp)
  have h1e_eq : ofOpens (K := K) (MaximalSpectrum.basicOpen (1 - e)) =
      (AffinoidSubdomain.ofIsIdempotentElem hA.out he.one_sub).toStrongAdmissibleOpen :=
    SetLike.coe_injective (by simp)
  rwa [he_eq, h1e_eq] at h

end Site

end StrongAdmissibleOpen

end Zariski

end TauCeti
