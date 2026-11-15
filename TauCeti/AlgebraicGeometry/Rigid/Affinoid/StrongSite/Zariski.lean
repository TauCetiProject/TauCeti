/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.StrongSite.Basic
public import TauCeti.RingTheory.Affinoid.Subdomain.Cover
public import TauCeti.RingTheory.Spectrum.Maximal.Topology

import TauCeti.RingTheory.Affinoid.QuotientNorm

/-!
# Zariski open covers and idempotents on the strong affinoid site

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`. Following
[BGR, §9.1.4, Corollary 7], the strong classical affinoid G-topology on `Sp A = MaximalSpectrum A`
is finer than the Zariski topology:

* Every rational domain `R(f/g)` with `(g, f₁, …, fₘ) = ⊤` is an `AffinoidSubdomain` with no chosen
  norm on `A` (`AffinoidSubdomain.rational`).
* Every principal Zariski open `D(f) = MaximalSpectrum.basicOpen f` is exhausted by the rational
  domains `R(ϖⁿ / f)` for `0 < ‖ϖ‖ < 1`, and this countable family is affinoid-test refined
  (`isAffinoidTestRefined_basicOpen_rationalDomain`), making `D(f)` strong-admissible open
  (`StrongAdmissibleOpen.basicOpen`).
* Every Zariski open subset and every Zariski open cover of `Sp A` is strong-admissible: the
  identity of `MaximalSpectrum A` is a continuous map of G-topologies from `strongGTopology` to
  `GTopology.topological (MaximalSpectrum A)` (`StrongAdmissibleOpen.zariskiContinuousMap`).
* Every idempotent `e ∈ A` defines a clopen affinoid subdomain `D(e)` represented by the quotient
  `A ⧸ Ideal.span {1 - e}` (`IsAffinoidSubdomainMap.quotient_one_sub_of_isIdempotentElem`), yielding
  a disjoint weak- and strong-admissible cover `{D(e), D(1 - e)}` of `Sp A`, and Zariski
  connectedness of `Sp A` is equivalent to `A` being nontrivial with only trivial idempotents
  (`IsAffinoidAlgebra.connectedSpace_maximalSpectrum_iff_idempotent`).

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §9.1.4,
  Corollary 7 and Corollary 8.
-/

public section

open TopologicalSpace

namespace TauCeti

universe u

section Idempotent

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- For an idempotent `e ∈ A`, the quotient map `A →ₐ[K] A ⧸ Ideal.span {1 - e}` represents the
clopen Zariski subset `MaximalSpectrum.basicOpen e` as an affinoid subdomain. -/
theorem IsAffinoidSubdomainMap.quotient_one_sub_of_isIdempotentElem
    (hA : IsAffinoidAlgebra K A) {e : A} (he : IsIdempotentElem e) :
    IsAffinoidSubdomainMap (Ideal.Quotient.mkₐ K (Ideal.span {1 - e}))
      (MaximalSpectrum.basicOpen e : Set (MaximalSpectrum A)) where
  isAffinoidAlgebra := hA.quotient _
  range_maximalSpectrumComap_subset := by
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, MaximalSpectrum.mem_basicOpen,
      IsAffinoidAlgebra.maximalSpectrumComap_asIdeal]
    intro he_mem
    have h1_sub : 1 - e ∈ Ideal.comap (Ideal.Quotient.mkₐ K (Ideal.span {1 - e})) y.asIdeal := by
      rw [Ideal.mem_comap, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
      exact y.asIdeal.zero_mem
    have h1 : (1 : A) ∈ Ideal.comap (Ideal.Quotient.mkₐ K (Ideal.span {1 - e})) y.asIdeal := by
      simpa only [add_sub_cancel] using add_mem he_mem h1_sub
    exact ((hA.quotient _).comap_isMaximal _ y.asIdeal).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  existsUnique_algHom {C} _ _ hC ψ hψ := by
    -- On `C`, `ψ e` lies in no maximal ideal, hence is a unit; since `ψ e * ψ (1 - e) = 0`,
    -- `ψ (1 - e) = 0`.
    have hunit : IsUnit (ψ e) := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {ψ e})
        (mt Ideal.span_singleton_eq_top.mp hne)
      have hx : hC.maximalSpectrumComap ψ ⟨m, hm⟩ ∈ MaximalSpectrum.basicOpen e :=
        hψ ⟨⟨m, hm⟩, rfl⟩
      rw [MaximalSpectrum.mem_basicOpen, IsAffinoidAlgebra.maximalSpectrumComap_asIdeal,
        Ideal.mem_comap] at hx
      exact hx (hle (Ideal.subset_span (Set.mem_singleton _)))
    have hzero : ψ (1 - e) = 0 := by
      have hmul : ψ e * ψ (1 - e) = 0 := by
        rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero]
      exact hunit.mul_right_eq_zero.mp hmul
    have hker : ∀ a ∈ Ideal.span ({1 - e} : Set A), ψ a = 0 := by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, hzero, zero_mul]
    exact ⟨Ideal.Quotient.liftₐ _ ψ hker, Ideal.Quotient.liftₐ_comp _ ψ hker,
      fun χ hχ ↦ Ideal.Quotient.algHom_ext K (hχ.trans (Ideal.Quotient.liftₐ_comp _ ψ hker).symm)⟩

/-- The clopen affinoid subdomain `D(e)` associated to an idempotent `e ∈ A`. -/
def AffinoidSubdomain.ofIsIdempotentElem (hA : IsAffinoidAlgebra K A) {e : A}
    (he : IsIdempotentElem e) : AffinoidSubdomain K A :=
  AffinoidSubdomain.ofMap (IsAffinoidSubdomainMap.quotient_one_sub_of_isIdempotentElem hA he)

@[simp]
theorem AffinoidSubdomain.coe_ofIsIdempotentElem (hA : IsAffinoidAlgebra K A) {e : A}
    (he : IsIdempotentElem e) :
    (AffinoidSubdomain.ofIsIdempotentElem hA he : Set (MaximalSpectrum A)) =
      MaximalSpectrum.basicOpen e :=
  AffinoidSubdomain.coe_ofMap _

/-- **Zariski connectedness criterion for affinoid spectra.** The classical spectrum `Sp A` of an
affinoid algebra is connected in the Zariski topology if and only if `A` is nontrivial and its only
idempotents are `0` and `1`. -/
theorem IsAffinoidAlgebra.connectedSpace_maximalSpectrum_iff_idempotent
    (hA : IsAffinoidAlgebra K A) :
    ConnectedSpace (MaximalSpectrum A) ↔
      Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  have := hA.isJacobsonRing
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · have : IsEmpty (MaximalSpectrum A) :=
      ⟨fun x ↦ x.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    exact ⟨fun h ↦ False.elim (IsEmpty.false h.toNonempty.some),
      fun ⟨hnt, _⟩ ↦ False.elim ((not_nontrivial_iff_subsingleton.mpr hsub) hnt)⟩
  · simp [hnt, MaximalSpectrum.connectedSpace_iff_idempotent (R := A)]

end Idempotent

section Zariski

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

namespace AffinoidSubdomain

/-- Any rational domain `R(f/g)` with `Ideal.span (insert g (Set.range f)) = ⊤` is an affinoid
subdomain of `Sp A`, with no chosen norm on `A`. -/
noncomputable def rational (hA : IsAffinoidAlgebra K A) {m : ℕ} {g : A} {f : Fin m → A}
    (h : Ideal.span (insert g (Set.range f)) = ⊤) : AffinoidSubdomain K A :=
  let _ : NormedCommRing A := hA.residueNormedCommRing
  let _ : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  ofMap (RationalFraction.isAffinoidSubdomainMap hA h)

@[simp]
theorem coe_rational (hA : IsAffinoidAlgebra K A) {m : ℕ} {g : A} {f : Fin m → A}
    (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    (rational hA h : Set (MaximalSpectrum A)) = rationalDomain K g f := by
  let _ : NormedCommRing A := hA.residueNormedCommRing
  let _ : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  exact coe_ofMap _

end AffinoidSubdomain

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
  have hpos : 0 < pointNorm K x f :=
    lt_of_le_of_ne (pointNorm_nonneg f) (Ne.symm ((hA.pointNorm_eq_zero_iff).not.mpr hx))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hϖ₁
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
    exact (hB.pointNorm_eq_zero_iff).not.mpr hy
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  have hbound : ∃ n : ℕ, ‖ϖ‖ ^ n * supSeminorm K u ≤ 1 := by
    rcases eq_or_lt_of_le (supSeminorm_nonneg (K := K) u) with h0 | hpos
    · exact ⟨0, by simp [← h0]⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hϖ₁
      have hlt := mul_lt_mul_of_pos_right hn hpos
      rw [inv_mul_cancel₀ hpos.ne'] at hlt
      exact ⟨n, hlt.le⟩
  obtain ⟨n, hn⟩ := hbound
  refine ⟨{AffinoidSubdomain.univ hB}, Set.finite_singleton _, by simp, fun W hW ↦ ?_⟩
  rw [Set.mem_singleton_iff.mp hW, AffinoidSubdomain.coe_univ]
  refine ⟨_, ⟨n, rfl⟩, fun y _ ↦ ?_⟩
  rw [Set.mem_preimage, mem_rationalDomain, hB.pointNorm_maximalSpectrumComap]
  refine ⟨hB.isUnit_iff_forall_pointNorm_ne_zero.mp hunit y, fun _ ↦ ?_⟩
  rw [hB.pointNorm_maximalSpectrumComap, AlgHom.commutes, pointNorm_algebraMap, norm_pow]
  have h1 : 1 ≤ pointNorm K y (φ f) * supSeminorm K u := by
    calc
      1 = pointNorm K y (φ f * u) := by rw [hu, pointNorm_one]
      _ = pointNorm K y (φ f) * pointNorm K y u := hB.pointNorm_mul y (φ f) u
      _ ≤ pointNorm K y (φ f) * supSeminorm K u :=
        mul_le_mul_of_nonneg_left (hB.pointNorm_le_supSeminorm y u) (pointNorm_nonneg _)
  calc
    ‖ϖ‖ ^ n ≤ ‖ϖ‖ ^ n * (pointNorm K y (φ f) * supSeminorm K u) :=
      le_mul_of_one_le_right (pow_nonneg (norm_nonneg _) _) h1
    _ = pointNorm K y (φ f) * (‖ϖ‖ ^ n * supSeminorm K u) := by ring
    _ ≤ pointNorm K y (φ f) * 1 := mul_le_mul_of_nonneg_left hn (pointNorm_nonneg _)
    _ = pointNorm K y (φ f) := mul_one _

/-- Any Zariski open cover of a subset `U ⊆ Sp A` is affinoid-test refined. -/
theorem isAffinoidTestRefined_opens_of_subset {U : Set (MaximalSpectrum A)}
    {S : Set (Opens (MaximalSpectrum A))}
    (hUS : U ⊆ ⋃₀ ((fun V : Opens (MaximalSpectrum A) ↦ (V : Set (MaximalSpectrum A))) '' S)) :
    IsAffinoidTestRefined K U
      ((fun V : Opens (MaximalSpectrum A) ↦ (V : Set (MaximalSpectrum A))) '' S) := by
  -- Pull back basic Zariski opens to a unit-ideal family on each test algebra and refine by
  -- standard rational domains (`IsAffinoidAlgebra.iUnion_rationalDomain_self_eq_univ_iff`).
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
    have hφg : φ g ∈ y.asIdeal := hle (Ideal.subset_span ⟨g, W, hW, hgW, rfl⟩)
    have hxg' : hB.maximalSpectrumComap φ y ∈ MaximalSpectrum.basicOpen g := hxg
    rw [MaximalSpectrum.mem_basicOpen, IsAffinoidAlgebra.maximalSpectrumComap_asIdeal,
      Ideal.mem_comap] at hxg'
    exact hxg' hφg
  obtain ⟨c, hcP, hc1⟩ := Submodule.mem_span_set.mp (hspan.ge (Submodule.mem_top : (1 : B) ∈ ⊤))
  let F : Finset B := c.support
  let h : Fin F.card → B := fun i ↦ (F.equivFin.symm i).1
  have hrange : Set.range h = (F : Set B) := by
    ext b
    simp only [h, Set.mem_range]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (F.equivFin.symm i).2,
      fun hb ↦ ⟨F.equivFin ⟨b, hb⟩, by simp⟩⟩
  have htop : Ideal.span (Set.range h) = ⊤ := (Ideal.eq_top_iff_one _).mpr <| by
    rw [hrange, ← hc1, Finsupp.sum]
    exact sum_mem fun b hb ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span hb)
  have htop_ins (i : Fin F.card) : Ideal.span (insert (h i) (Set.range h)) = ⊤ := by
    simpa only [Set.insert_eq_of_mem (Set.mem_range_self i)] using htop
  refine ⟨Set.range fun i ↦ AffinoidSubdomain.rational hB (htop_ins i), Set.finite_range _, ?_, ?_⟩
  · rw [← Set.range_comp, Set.sUnion_range]
    simpa only [Function.comp_def, AffinoidSubdomain.coe_rational] using
      (hB.iUnion_rationalDomain_self_eq_univ_iff h).mpr htop
  · rintro _ ⟨i, rfl⟩
    obtain ⟨g, W, hW, hgW, hg_eq⟩ := hcP (F.equivFin.symm i).2
    refine ⟨W, ⟨W, hW, rfl⟩, ?_⟩
    rw [AffinoidSubdomain.coe_rational]
    intro y hy
    rw [mem_rationalDomain] at hy
    have hyg : φ g ∉ y.asIdeal := (hB.pointNorm_eq_zero_iff).not.mp (hg_eq ▸ hy.1)
    apply hgW
    rw [SetLike.mem_coe, MaximalSpectrum.mem_basicOpen,
      IsAffinoidAlgebra.maximalSpectrumComap_asIdeal, Ideal.mem_comap]
    exact hyg

namespace StrongAdmissibleOpen

/-- Every principal Zariski open `D(f)` is strong-admissible open [BGR, §9.1.4, Corollary 7]. -/
noncomputable def basicOpen (hA : IsAffinoidAlgebra K A) (f : A) :
    StrongAdmissibleOpen K A where
  carrier := MaximalSpectrum.basicOpen f
  exists_affinoid_cover := by
    obtain ⟨ϖ, hϖ₀, hϖ₁⟩ := NormedField.exists_norm_lt_one K
    have hϖ_ne : ϖ ≠ 0 := norm_pos_iff.mp hϖ₀
    have htop (n : ℕ) :
        Ideal.span (insert f (Set.range (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n)))) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
        ((IsUnit.pow n (Ne.isUnit hϖ_ne)).map (algebraMap K A))
    let S : Set (AffinoidSubdomain K A) := Set.range fun n : ℕ ↦
      AffinoidSubdomain.rational hA (htop n)
    have himg : ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' S) =
        Set.range fun n : ℕ ↦ rationalDomain K f (fun _ : Fin 1 ↦ algebraMap K A (ϖ ^ n)) := by
      ext s
      simp only [S, Set.mem_image, Set.mem_range, exists_exists_eq_and,
        AffinoidSubdomain.coe_rational]
    refine ⟨S, ?_, himg ▸ isAffinoidTestRefined_basicOpen_rationalDomain f hϖ₁⟩
    rw [himg, Set.sUnion_range, ← basicOpen_eq_iUnion_rationalDomain hA f hϖ₁]

@[simp]
theorem coe_basicOpen (hA : IsAffinoidAlgebra K A) (f : A) :
    (basicOpen hA f : Set (MaximalSpectrum A)) = MaximalSpectrum.basicOpen f :=
  (rfl)

private theorem exists_affinoid_cover_opens (hA : IsAffinoidAlgebra K A)
    (U : Opens (MaximalSpectrum A)) :
    ∃ T : Set (AffinoidSubdomain K A),
      ⋃₀ ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' T) = U ∧
        IsAffinoidTestRefined K (U : Set (MaximalSpectrum A))
          ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' T) := by
  let S : Set (StrongAdmissibleOpen K A) :=
    (fun f : A ↦ basicOpen hA f) ''
      {f : A | (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A)) ⊆ U}
  have himg : ((fun W : StrongAdmissibleOpen K A ↦ (W : Set (MaximalSpectrum A))) '' S) =
      (fun V : Opens (MaximalSpectrum A) ↦ (V : Set (MaximalSpectrum A))) ''
        (MaximalSpectrum.basicOpen ''
          {f : A | (MaximalSpectrum.basicOpen f : Set (MaximalSpectrum A)) ⊆ U}) := by
    simp only [S, Set.image_image, coe_basicOpen]
  have hSu : ⋃₀ ((fun W : StrongAdmissibleOpen K A ↦ (W : Set (MaximalSpectrum A))) '' S) =
      (U : Set (MaximalSpectrum A)) := by
    apply Set.Subset.antisymm
    · rintro x ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, hxf⟩
      exact hf hxf
    · intro x hx
      obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
        MaximalSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp (U.isOpen.mem_nhds hx)
      exact ⟨MaximalSpectrum.basicOpen f, ⟨basicOpen hA f, ⟨f, hfU, rfl⟩, rfl⟩, hxf⟩
  obtain ⟨W, hWU⟩ := mem_range_of_testRefined hSu
    (himg ▸ isAffinoidTestRefined_opens_of_subset (himg ▸ hSu.ge))
  obtain ⟨T, hTu, hT⟩ := W.exists_affinoid_cover
  have hWU' : (W : Set (MaximalSpectrum A)) = U := (setEmbedding_apply W).symm.trans hWU
  have hTu' : ⋃₀ ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' T) =
      (W : Set (MaximalSpectrum A)) := hTu
  have hT' : IsAffinoidTestRefined K (W : Set (MaximalSpectrum A))
      ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' T) := hT
  exact ⟨T, hTu'.trans hWU', hWU' ▸ hT'⟩

section Site

variable [hA : Fact (IsAffinoidAlgebra K A)]

/-- Every Zariski open subset of `Sp A` is strong-admissible open [BGR, §9.1.4, Corollary 7]. -/
noncomputable def ofOpens (U : Opens (MaximalSpectrum A)) : StrongAdmissibleOpen K A where
  carrier := U
  exists_affinoid_cover := exists_affinoid_cover_opens hA.out U

@[simp]
theorem coe_ofOpens (U : Opens (MaximalSpectrum A)) :
    (ofOpens (K := K) U : Set (MaximalSpectrum A)) = U :=
  (rfl)

/-- **Admissibility of Zariski opens and Zariski covers** [BGR, §9.1.4, Corollary 7].
The identity of `MaximalSpectrum A` is a continuous map of G-topologies from `strongGTopology` to
the G-topology of all Zariski open covers. -/
noncomputable def zariskiContinuousMap :
    (strongGTopology (K := K) (A := A)).ContinuousMap
      (GTopology.topological (MaximalSpectrum A)) where
  toFun := id
  comap := ofOpens
  coe_comap' _ := by simp
  covers_comap {U S} hS := by
    rw [GTopology.topological_covers_iff] at hS
    rw [strongGTopology_covers_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      rw [← SetLike.coe_subset_coe, coe_ofOpens, coe_ofOpens, ← hS]
      exact Set.subset_sUnion_of_mem ⟨V, hV, rfl⟩
    · simpa only [Set.image_image, coe_ofOpens] using
        isAffinoidTestRefined_opens_of_subset hS.ge

@[simp]
theorem coe_zariskiContinuousMap : ⇑(zariskiContinuousMap (K := K) (A := A)) = id :=
  (rfl)

@[simp]
theorem zariskiContinuousMap_comap :
    (zariskiContinuousMap (K := K) (A := A)).comap = ofOpens :=
  (rfl)

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
  have h₁ : ofOpens (K := K) (MaximalSpectrum.basicOpen e) =
      (AffinoidSubdomain.ofIsIdempotentElem hA.out he).toStrongAdmissibleOpen :=
    SetLike.coe_injective (by simp)
  have h₂ : ofOpens (K := K) (MaximalSpectrum.basicOpen (1 - e)) =
      (AffinoidSubdomain.ofIsIdempotentElem hA.out he.one_sub).toStrongAdmissibleOpen :=
    SetLike.coe_injective (by simp)
  rwa [h₁, h₂] at h

end Site

end StrongAdmissibleOpen

end Zariski

end TauCeti
