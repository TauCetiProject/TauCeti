/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Site
public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.Topology.GTopology.SlightlyFiner
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basic

/-!
# Principal Zariski opens in the strong affinoid G-topology

The strong G-topology is the finest slightly finer extension of the weak affinoid
G-topology. Its admissible opens are unions of affinoid subdomains, and its covers
are tested by finite affinoid refinements on every affinoid subdomain.

For a nonzero scalar `c`, the Laurent subdomain `|c| ≤ |f|` is affinoid. If
`0 < |ϖ| < 1`, these subdomains for `c = ϖⁿ` exhaust the principal Zariski open
`D(f)`. More importantly, every affinoid subdomain contained in `D(f)` lies in one
member of the exhaustion: the inverse of the restriction of `f` has bounded
supremum seminorm. Consequently the exhaustion is an admissible cover, not just
a set-theoretic union. No reducedness or norm on the ambient algebra is required.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§7.2.3 and 9.1.4.
-/

public section

namespace TauCeti.AffinoidSubdomain

open TopologicalSpace Topology

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A] [hA : Fact (IsAffinoidAlgebra K A)]

/-- The strong G-topology of an affinoid spectrum, obtained by enhancement of its weak
finite-cover G-topology. -/
noncomputable abbrev strongGTopology : GTopology (GTopology.generatedOpensEmbedding
    (setEmbedding (K := K) (A := A))) :=
  (weakGTopology (K := K) (A := A)).finestSlightlyFiner

/-- The affinoid Laurent subdomain `|c| ≤ |f|`, for a nonzero scalar `c`. -/
noncomputable def principalLaurent (f : A) (c : Kˣ) : AffinoidSubdomain K A where
  carrier := {x | ‖(c : K)‖ ≤ pointNorm K x f}
  exists_representation := by
    let := hA.out.residueNormedCommRing
    let := hA.out.residueNormedAlgebra
    let := hA.out.isUltrametricDist_residueNormedCommRing
    let := hA.out.completeSpace_residueNormedCommRing
    have hspan : Ideal.span (insert f (Set.range fun _ : Fin 1 ↦ algebraMap K A (c : K))) = ⊤ := by
      exact Ideal.eq_top_of_isUnit_mem _
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self 0)))
        (c.isUnit.map (algebraMap K A))
    refine ⟨CommAlgCat.of K (RationalFraction f
      (fun _ : Fin 1 ↦ algebraMap K A (c : K))), IsScalarTower.toAlgHom K A _, ?_⟩
    convert RationalFraction.isAffinoidSubdomainMap hA.out hspan using 1
    ext x
    simp only [Set.mem_ofPred_eq, mem_rationalDomain, pointNorm_algebraMap, Fin.forall_fin_one]
    exact ⟨fun h ↦ ⟨ne_of_gt ((norm_pos_iff.mpr c.ne_zero).trans_le h), h⟩, And.right⟩

/-- The underlying set of the Laurent cutoff is its defining lower bound. -/
@[simp]
theorem coe_principalLaurent (f : A) (c : Kˣ) :
    (principalLaurent f c : Set (MaximalSpectrum A)) =
      {x | ‖(c : K)‖ ≤ pointNorm K x f} := (rfl)

/-- Membership in the Laurent cutoff is its defining lower bound. -/
@[simp]
theorem mem_principalLaurent (f : A) (c : Kˣ) (x : MaximalSpectrum A) :
    x ∈ principalLaurent f c ↔ ‖(c : K)‖ ≤ pointNorm K x f := Iff.rfl

/-- Laurent cutoffs with smaller scalar norm contain those with larger scalar norm. -/
theorem principalLaurent_le {f : A} {c d : Kˣ} (h : ‖(d : K)‖ ≤ ‖(c : K)‖) :
    principalLaurent f c ≤ principalLaurent f d :=
  fun _ hx ↦ h.trans hx

/-- The Laurent cutoffs form an increasing sequence when the scalar norm is at most one. -/
theorem monotone_principalLaurent_pow (f : A) (ϖ : Kˣ) (hϖ : ‖(ϖ : K)‖ ≤ 1) :
    Monotone (fun n : ℕ ↦ principalLaurent f (ϖ ^ n)) := by
  intro m n hmn
  apply principalLaurent_le
  simpa only [Units.val_pow_eq_pow_val, norm_pow] using
    pow_le_pow_of_le_one (norm_nonneg (ϖ : K)) hϖ hmn

/-- The Laurent cutoffs at powers of a scalar of norm less than one exhaust `D(f)`. -/
theorem iUnion_principalLaurent_pow (f : A) (ϖ : Kˣ) (hϖ : ‖(ϖ : K)‖ < 1) :
    (⋃ n : ℕ, (principalLaurent f (ϖ ^ n) : Set (MaximalSpectrum A))) =
      {x | f ∉ x.asIdeal} := by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_principalLaurent,
    Set.mem_ofPred_eq, ← hA.out.pointNorm_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ne_of_gt ((norm_pos_iff.mpr (ϖ ^ n).ne_zero).trans_le hn)
  · intro hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (lt_of_le_of_ne (pointNorm_nonneg _) (Ne.symm hx)) hϖ
    exact ⟨n, by simpa only [mem_principalLaurent, Units.val_pow_eq_pow_val, norm_pow] using hn.le⟩

/-- Every affinoid subdomain avoiding the zero locus of `f` lies in one Laurent cutoff.
This is the finite-refinement property of the principal-open exhaustion. -/
theorem exists_le_principalLaurent_pow (f : A) (ϖ : Kˣ) (hϖ : ‖(ϖ : K)‖ < 1)
    (U : AffinoidSubdomain K A) (hU : ∀ x ∈ U, f ∉ x.asIdeal) :
    ∃ n : ℕ, U ≤ principalLaurent f (ϖ ^ n) := by
  let b := U.toSections f
  have hb : IsUnit b := U.isAffinoidAlgebra.isUnit_iff_forall_pointNorm_ne_zero.mpr fun y ↦ by
    rw [← IsAffinoidAlgebra.pointNorm_maximalSpectrumComap U.isAffinoidAlgebra U.toSections]
    exact hA.out.pointNorm_eq_zero_iff.not.mpr
      (hU _ (U.isAffinoidSubdomainMap.range_maximalSpectrumComap_subset ⟨y, rfl⟩))
  let C := supSeminorm K (Ring.inverse b) + 1
  have hC : 0 < C := lt_add_of_le_of_pos (supSeminorm_nonneg _) zero_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC) hϖ
  have hnC : ‖(ϖ : K)‖ ^ n * C < 1 := (lt_div_iff₀ hC).mp (by simpa using hn)
  refine ⟨n, fun x hx ↦ ?_⟩
  have hx' : x ∈ (U : Set (MaximalSpectrum A)) := hx
  rw [← U.isAffinoidSubdomainMap.range_maximalSpectrumComap hA.out] at hx'
  obtain ⟨y, rfl⟩ := hx'
  have hmul : pointNorm K y b * pointNorm K y (Ring.inverse b) = 1 := by
    rw [← U.isAffinoidAlgebra.pointNorm_mul, Ring.mul_inverse_cancel _ hb, pointNorm_one]
  have hbound := U.isAffinoidAlgebra.pointNorm_le_supSeminorm y (Ring.inverse b)
  have hpos := pointNorm_nonneg (K := K) (x := y) b
  rw [mem_principalLaurent, Units.val_pow_eq_pow_val, norm_pow,
    IsAffinoidAlgebra.pointNorm_maximalSpectrumComap]
  dsimp only [b] at hmul hpos
  dsimp only [C] at hnC
  nlinarith [mul_le_mul_of_nonneg_left hbound hpos]

/-- A principal Zariski open as an admissible open of the strong affinoid G-topology. -/
noncomputable def principalOpen (f : A) : GTopology.GeneratedOpens
    (setEmbedding (K := K) (A := A)) := by
  refine @Opens.mk _ (generateFrom (Set.range (setEmbedding (K := K) (A := A))))
    {x | f ∉ x.asIdeal} ?_
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  let ϖ : Kˣ := Units.mk0 c (norm_pos_iff.mp hc0)
  rw [← iUnion_principalLaurent_pow f ϖ hc1]
  let _ : TopologicalSpace (MaximalSpectrum A) :=
    generateFrom (Set.range (setEmbedding (K := K) (A := A)))
  exact isOpen_iUnion fun n ↦ .basic _ ⟨principalLaurent f (ϖ ^ n), setEmbedding_apply _⟩

/-- The underlying set of the admissible principal open is the Zariski nonvanishing locus. -/
@[simp]
theorem coe_principalOpen (f : A) :
    (principalOpen (K := K) f : Set (MaximalSpectrum A)) = {x | f ∉ x.asIdeal} := (rfl)

/-- A point belongs to the admissible principal open exactly when `f` does not vanish there. -/
@[simp]
theorem mem_principalOpen (f : A) (x : MaximalSpectrum A) :
    x ∈ principalOpen (K := K) f ↔ f ∉ x.asIdeal := Iff.rfl

/-- The zero function has empty nonvanishing locus. -/
@[simp]
theorem principalOpen_zero : principalOpen (K := K) (0 : A) = ⊥ := by
  apply SetLike.coe_injective
  simp only [coe_principalOpen, Ideal.zero_mem, not_true_eq_false, Set.ofPred_false,
    Opens.coe_bot]

/-- The unit function is nonvanishing on the whole spectrum, including for the zero algebra. -/
@[simp]
theorem principalOpen_one : principalOpen (K := K) (1 : A) = ⊤ := by
  apply SetLike.coe_injective
  ext x
  simp only [coe_principalOpen, Set.mem_ofPred_eq, Opens.coe_top, Set.mem_univ, iff_true]
  exact Ideal.one_notMem x.asIdeal

/-- Nonvanishing of a product is simultaneous nonvanishing of its factors. -/
@[simp]
theorem principalOpen_mul (f g : A) :
    principalOpen (K := K) (f * g) = principalOpen f ⊓ principalOpen g := by
  apply SetLike.coe_injective
  ext x
  simp only [coe_principalOpen, Opens.coe_inf, Set.mem_inter_iff, Set.mem_ofPred_eq,
    x.isMaximal.isPrime.mul_mem_iff_mem_or_mem, not_or]

/-- Every Zariski-open subset of the maximal spectrum is an admissible open of the strong
G-topology. This asserts admissibility of the open, not of an arbitrary covering family. -/
theorem isOpen_generateFrom_of_isOpen {V : Set (MaximalSpectrum A)} (hV : IsOpen V) :
    IsOpen[generateFrom (Set.range (setEmbedding (K := K) (A := A)))] V := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  rw [weakGTopology.isOpen_generateFrom_range_iff]
  simp only [setEmbedding_apply]
  intro x hx
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hW x.toPrimeSpectrum hx
  have hopen : IsOpen[generateFrom (Set.range (setEmbedding (K := K) (A := A)))]
      {x : MaximalSpectrum A | f ∉ x.asIdeal} := by
    simpa only [coe_principalOpen] using
      @Opens.isOpen _ (generateFrom _) (principalOpen (K := K) f)
  obtain ⟨U, hxU, hUf⟩ := weakGTopology.isOpen_generateFrom_range_iff.mp hopen x hxf
  simp only [setEmbedding_apply] at hxU hUf
  exact ⟨U, hxU, fun y hy ↦ hfW (hUf hy)⟩

/-- The principal-open exhaustion by Laurent subdomains is admissible for the strong
G-topology. Each affinoid test subdomain is already contained in a single member. -/
theorem strongGTopology_covers_principalOpen (f : A) (ϖ : Kˣ) (hϖ : ‖(ϖ : K)‖ < 1) :
    strongGTopology.Covers (principalOpen f)
      (Set.range fun n : ℕ ↦ GTopology.toGeneratedOpens
        (setEmbedding (K := K) (A := A)) (principalLaurent f (ϖ ^ n))) := by
  rw [GTopology.finestSlightlyFiner_covers_iff]
  refine ⟨?_, fun U hU ↦ ?_⟩
  · simpa only [← Set.range_comp, Function.comp_def, GTopology.coe_toGeneratedOpens,
      setEmbedding_apply, Set.sUnion_range, coe_principalOpen] using
      iUnion_principalLaurent_pow f ϖ hϖ
  · simp only [setEmbedding_apply, coe_principalOpen] at hU
    obtain ⟨n, hn⟩ := exists_le_principalLaurent_pow f ϖ hϖ U hU
    refine ⟨{U}, weakGTopology.identity U, ?_⟩
    rintro W rfl
    exact ⟨_, Set.mem_range_self n, by
      simpa only [GTopology.coe_toGeneratedOpens, setEmbedding_apply] using
        SetLike.coe_subset_coe.mpr hn⟩

end TauCeti.AffinoidSubdomain
