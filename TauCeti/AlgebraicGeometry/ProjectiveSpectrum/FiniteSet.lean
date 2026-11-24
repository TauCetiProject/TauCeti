/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Immersion
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.Algebra.DirectSum.Component
import TauCeti.RingTheory.Ideal.Operations

/-!
# Common affine neighborhoods in projective spectra

A homogeneous ideal not contained in any prime of a finite set contains a positive-degree
homogeneous element avoiding the entire set. Its affine basic open can be chosen inside any
prescribed open. Affine morphisms and locally closed immersions into projective spectra
therefore admit common affine neighbourhoods of finite subsets inside prescribed opens.

No field, finite generation, degree-one generation or nonempty-set hypothesis is required.
The homogeneous prime-avoidance argument raises two sections to a common degree before adding
them, so it applies over finite fields as well.

These neighborhoods supply affine charts around finite divisor supports and the finite
group orbits in projective and quasi-projective quotients.

## Main results

* `ProjectiveSpectrum.exists_homogeneous_mem_notMem_of_finset`: a homogeneous ideal not contained
  in any of finitely many relevant primes contains a positive-degree element avoiding them all.
* `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset`: one positive-degree homogeneous
  section avoiding every point in a finite set.
* `ProjectiveSpectrum.exists_basicOpen_superset_le` and
  `AlgebraicGeometry.Proj.exists_homogeneous_basicOpen_superset_le`: a positive-degree homogeneous
  basic open around a finite set inside a prescribed open.
* `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isAffineHom_proj` and
  `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isImmersion_proj`: common affine
  neighbourhoods inside prescribed source opens for affine morphisms and immersions into `Proj`.

## References

* [The Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY): finite subsets of
  locally closed subschemes of `Proj` have affine neighborhoods. The homogeneous prime-avoidance
  construction here also places the neighborhood inside a prescribed open.
-/

public section

variable {A σ : Type*} [CommRing A] [SetLike σ A]

section

variable [AddSubmonoidClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace ProjectiveSpectrum

/-- A homogeneous ideal missing `x` contains a positive-degree homogeneous element vanishing
at every point of a finite set none of whose primes is contained in the prime of `x`,
while not vanishing at `x`. -/
theorem exists_homogeneous_mem_notMem_of_finset_not_le (x : ProjectiveSpectrum 𝒜)
    (points : Finset (ProjectiveSpectrum 𝒜)) (hsep : ∀ y ∈ points, ¬ y ≤ x)
    {I : HomogeneousIdeal 𝒜} (hI : ¬ I ≤ x.asHomogeneousIdeal) :
    ∃ n > 0, ∃ a ∈ 𝒜 n, a ∈ I ∧
      (∀ y ∈ points, a ∈ y.asHomogeneousIdeal) ∧ a ∉ x.asHomogeneousIdeal := by
  classical
  have hother (y : points) : ∃ n, ∃ a ∈ 𝒜 n,
      a ∈ y.val.asHomogeneousIdeal ∧ a ∉ x.asHomogeneousIdeal :=
    y.val.asHomogeneousIdeal.isHomogeneous.exists_mem_notMem_of_not_subset (by
      simpa only [coe_toIdeal, SetLike.coe_subset_coe,
        ProjectiveSpectrum.as_ideal_le_as_ideal] using hsep y y.property)
  choose d a ha hay hax using hother
  obtain ⟨n, hn, b, hb, hbx⟩ := x.exists_le_mem_notMem 1
  obtain ⟨m, c, hc, hcI, hcx⟩ :=
    I.isHomogeneous.exists_mem_notMem_of_not_subset (q := x.asHomogeneousIdeal.toIdeal)
      (SetLike.coe_subset_coe.not.mpr (toIdeal_le_toIdeal_iff.not.mpr hI))
  let q := b * c * ∏ y ∈ points.attach, a y
  refine ⟨n + m + ∑ y ∈ points.attach, d y, by omega, q, ?_, ?_, ?_, ?_⟩
  · exact SetLike.mul_mem_graded (SetLike.mul_mem_graded hb hc)
      (SetLike.prod_mem_graded _ _ _ (fun y _ ↦ ha y))
  · exact I.toIdeal.mul_mem_right _ (I.toIdeal.mul_mem_left b hcI)
  · intro y hy
    exact Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _
      (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ ⟨y, hy⟩)) (hay ⟨y, hy⟩))
  · apply x.isPrime.mul_notMem (x.isPrime.mul_notMem hbx hcx)
    rw [Ideal.IsPrime.prod_mem_iff (hp := x.isPrime)]
    push Not
    exact fun y _ ↦ hax y

/-- A homogeneous ideal missing each point in a finite set contains one positive-degree
homogeneous element missing all of them. -/
theorem exists_homogeneous_mem_notMem_of_finset {I : HomogeneousIdeal 𝒜}
    (points : Finset (ProjectiveSpectrum 𝒜))
    (hI : ∀ x ∈ points, ¬ I ≤ x.asHomogeneousIdeal) :
    ∃ n > 0, ∃ a ∈ 𝒜 n, a ∈ I ∧ ∀ x ∈ points, a ∉ x.asHomogeneousIdeal := by
  classical
  induction points using Finset.strongInduction with
  | H points ih =>
    rcases points.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, 0, zero_mem _, I.zero_mem, by simp⟩
    obtain ⟨x, hx⟩ := points.exists_minimal hne
    obtain ⟨n, hn, a, ha, haI, havoid⟩ := ih (points.erase x) (Finset.erase_ssubset hx.prop)
      (fun y hy ↦ hI y (Finset.mem_of_mem_erase hy))
    by_cases hax : a ∉ x.asHomogeneousIdeal
    · refine ⟨n, hn, a, ha, haI, fun y hy ↦ ?_⟩
      by_cases hyx : y = x
      · exact hyx ▸ hax
      · exact havoid y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    rw [not_not] at hax
    obtain ⟨m, hm, b, hb, hbI, hbothers, hbx⟩ :=
      x.exists_homogeneous_mem_notMem_of_finset_not_le (points.erase x)
        (fun y hy hyx ↦ (Finset.mem_erase.mp hy).1
          (le_antisymm hyx (hx.2 (Finset.mem_erase.mp hy).2 hyx))) (hI x hx.prop)
    refine ⟨n * m, Nat.mul_pos hn hm, a ^ m + b ^ n, add_mem ?_ ?_,
      I.add_mem (I.toIdeal.pow_mem_of_mem haI m hm) (I.toIdeal.pow_mem_of_mem hbI n hn),
      fun y hy ↦ ?_⟩
    · simpa [mul_comm] using SetLike.pow_mem_graded m ha
    · exact SetLike.pow_mem_graded n hb
    · by_cases hyx : y = x
      · subst y
        exact x.isPrime.pow_add_pow_notMem hax hbx hm
      · have hy' := Finset.mem_erase.mpr ⟨hyx, hy⟩
        rw [add_comm]
        exact y.isPrime.pow_add_pow_notMem (hbothers y hy') (havoid y hy') hn

/-- A finite set of relevant homogeneous primes misses a common homogeneous element of
positive degree. -/
theorem exists_homogeneous_notMem_of_finset (points : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ n > 0, ∃ a ∈ 𝒜 n, ∀ x ∈ points, a ∉ x.asHomogeneousIdeal := by
  obtain ⟨n, hn, a, ha, _, havoid⟩ :=
    exists_homogeneous_mem_notMem_of_finset (I := ⊤) points
      (fun x _ h ↦ x.isPrime.ne_top (by
        rw [top_le_iff.mp h, HomogeneousIdeal.toIdeal_top]))
  exact ⟨n, hn, a, ha, havoid⟩

/-- A finite set in a projective spectrum has a positive-degree homogeneous basic-open
neighbourhood inside any prescribed open containing it. -/
theorem exists_basicOpen_superset_le
    {s : Set (ProjectiveSpectrum 𝒜)}
    {W : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ n > 0, ∃ a ∈ 𝒜 n, s ⊆ basicOpen 𝒜 a ∧ basicOpen 𝒜 a ≤ W := by
  classical
  let I := ProjectiveSpectrum.vanishingIdeal (𝒜 := 𝒜) (W : Set (ProjectiveSpectrum 𝒜))ᶜ
  have hI (x : ProjectiveSpectrum 𝒜) (hx : x ∈ hs.toFinset) :
      ¬ I ≤ x.asHomogeneousIdeal := by
    intro h
    have hxzero := (ProjectiveSpectrum.mem_zeroLocus 𝒜 x (I : Set A)).mpr
      (SetLike.coe_subset_coe.mpr h)
    rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hxzero
    have hxclosure : x ∈ closure ((W : Set (ProjectiveSpectrum 𝒜))ᶜ) := hxzero
    rw [W.isOpen.isClosed_compl.closure_eq] at hxclosure
    exact hxclosure (hsW (hs.mem_toFinset.mp hx))
  obtain ⟨n, hn, a, ha, haI, havoid⟩ :=
    ProjectiveSpectrum.exists_homogeneous_mem_notMem_of_finset hs.toFinset hI
  refine ⟨n, hn, a, ha, ?_, ?_⟩
  · intro x hx
    rw [SetLike.mem_coe, ProjectiveSpectrum.mem_basicOpen]
    exact havoid x (hs.mem_toFinset.mpr hx)
  · intro x hx
    by_contra hxW
    exact (ProjectiveSpectrum.mem_basicOpen 𝒜 a x).mp hx
      ((ProjectiveSpectrum.mem_vanishingIdeal _ _).mp haI x hxW)

end ProjectiveSpectrum

end

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A finite set of `Proj` has a basic-open neighbourhood defined by a homogeneous element
of positive degree inside any prescribed open containing the set. -/
theorem AlgebraicGeometry.Proj.exists_homogeneous_basicOpen_superset_le
    {s : Set (Proj 𝒜)} {W : (Proj 𝒜).Opens} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ n > 0, ∃ a ∈ 𝒜 n, s ⊆ Proj.basicOpen 𝒜 a ∧ Proj.basicOpen 𝒜 a ≤ W :=
  ProjectiveSpectrum.exists_basicOpen_superset_le hs hsW

/-- A finite set in the source of an affine morphism to a projective spectrum lies in a
common affine open inside any prescribed open containing it. The graded ring is arbitrary. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isAffineHom_proj
    {X : Scheme} (f : X ⟶ Proj 𝒜) [IsAffineHom f]
    {s : Set X} {W : X.Opens} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨n, hn, a, ha, hsa, _⟩ := Proj.exists_homogeneous_basicOpen_superset_le
    (hs.image f) (W := ⊤) (fun _ _ ↦ TopologicalSpace.Opens.mem_top _)
  exact f.exists_isAffineOpen_superset_of_isAffineHom hs hsW
    ⟨Proj.basicOpen 𝒜 a, Proj.isAffineOpen_basicOpen 𝒜 a ha hn, hsa⟩

/-- A finite set in a locally closed subscheme of a projective spectrum lies in a common
affine open inside any prescribed open. This includes quasi-projective open subschemes. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isImmersion_proj
    {X : Scheme} (f : X ⟶ Proj 𝒜) [IsImmersion f]
    {s : Set X} {W : X.Opens} (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨n, hn, a, ha, hsa, haV⟩ := Proj.exists_homogeneous_basicOpen_superset_le
    (W := f.coborderRange) (hs.image f) (by
      rintro _ ⟨x, _, rfl⟩
      exact subset_coborder (Set.mem_range_self x))
  exact f.exists_isAffineOpen_superset_of_isImmersion hs hsW
    ⟨Proj.basicOpen 𝒜 a, Proj.isAffineOpen_basicOpen 𝒜 a ha hn, hsa, haV⟩
