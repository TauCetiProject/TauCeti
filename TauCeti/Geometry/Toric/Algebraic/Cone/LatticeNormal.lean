/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Face.Basic
public import TauCeti.Geometry.Toric.Algebraic.Cone.Sublattice

import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Lattice normal vectors of a cone along a facet

Let `τ` be a facet of a lattice-rational cone `σ`, so that the real span of `σ` has one more
dimension than that of `τ`. The quotient `N_σ / N_τ` of the sublattices spanned by the two cones
is then a lattice of rank one, and exactly one of its two generators points into `σ`. A lift
`n_{σ,τ} ∈ N_σ` of that generator is a *lattice normal* of `σ` along `τ`. It is determined
modulo `N_τ`, so every integral character vanishing on `N_τ` takes a well-defined value on it.

Lattice normals are the coefficients of the balancing condition of Minkowski weights on a
complete fan, which describe the operational Chow groups of the toric variety: a weight on the
cones of codimension `j` is balanced at a cone `τ` of codimension `j + 1` when
`∑_{σ ⊃ τ} c(σ) ⟨u, n_{σ,τ}⟩ = 0` for every character `u` vanishing on `τ`.

## Main declarations

* `TauCeti.Toric.IsLatticeNormal`: `n` lies in `N_σ`, generates `N_σ` modulo `N_τ`, and
  points into `σ`: some lattice vector of `σ` is a positive multiple of `n` modulo `N_τ`.
* `TauCeti.Toric.exists_isLatticeNormal`: a lattice-rational cone has a lattice normal along
  every lattice-rational subcone of one dimension less.
* `TauCeti.Toric.IsLatticeNormal.sub_mem`: along a face, a lattice normal is unique modulo `N_τ`.
* `TauCeti.Toric.IsLatticeNormal.apply_eq`: so characters vanishing on `N_τ` take the same value
  on any two lattice normals.
* `TauCeti.Toric.latticeNormal`: a chosen lattice normal, with
  `TauCeti.Toric.isLatticeNormal_latticeNormal` for facets.

## References

* W. Fulton and B. Sturmfels, *Intersection theory on toric varieties*, Topology 36 (1997),
  §1 and §2.
* W. Fulton, *Introduction to Toric Varieties*, §5.1.
-/

public section

open Module

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ τ : PointedCone ℝ V}

/-- A lattice vector `n` is a *lattice normal* of the cone `σ` along `τ` when it lies in the
sublattice `N_σ`, generates `N_σ` modulo `N_τ`, and points into `σ`: some lattice vector of `σ` is
a positive multiple of `n` modulo `N_τ`. When `τ` is a facet of `σ`, the class of `n` is the
generator of the rank-one lattice `N_σ / N_τ` on the side of `σ`. -/
structure IsLatticeNormal (i : N →+ V) (τ σ : PointedCone ℝ V) (n : N) : Prop where
  /-- A lattice normal lies in the sublattice of `σ`. -/
  mem : n ∈ coneSublattice i σ
  /-- A lattice normal generates the sublattice of `σ` modulo that of `τ`. -/
  exists_sub_zsmul_mem : ∀ m ∈ coneSublattice i σ, ∃ k : ℤ, m - k • n ∈ coneSublattice i τ
  /-- A lattice normal points into `σ`. -/
  exists_pos : ∃ g : N, i g ∈ σ ∧ ∃ k : ℤ, 0 < k ∧ g - k • n ∈ coneSublattice i τ

/-- If `τ ≤ σ` are lattice rational and the span of `σ` has one more dimension, the quotient
`N_σ / N_τ` is torsion free of rank one, hence cyclic: some `e ∈ N_σ` generates `N_σ` modulo
`N_τ`. -/
private theorem exists_generator (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ)
    (hτ : IsLatticeRational i τ) (hτσ : τ ≤ σ)
    (hdim : finrank ℝ (Submodule.span ℝ (τ : Set V)) + 1 =
      finrank ℝ (Submodule.span ℝ (σ : Set V))) :
    ∃ e ∈ coneSublattice i σ, ∀ m ∈ coneSublattice i σ,
      ∃ k : ℤ, m - k • e ∈ coneSublattice i τ := by
  have := hi.free
  have := hi.finite
  set L := (coneSublattice i σ).toIntSubmodule
  set L' := (coneSublattice i τ).toIntSubmodule.comap L.subtype
  have hrank : finrank ℤ (L ⧸ L') = 1 := by
    have h := Submodule.finrank_quotient_add_finrank L'
    rw [(Submodule.comapSubtypeEquivOfLe (coneSublattice_mono (i := i) hτσ)).finrank_eq,
      hτ.finrank_coneSublattice hi, hσ.finrank_coneSublattice hi, ← hdim] at h
    omega
  have : IsTorsionFree ℤ (L ⧸ L') := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro k x hkx
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hkx
      rw [or_iff_not_imp_left, Submodule.Quotient.mk_eq_zero]
      exact fun hk ↦ mem_coneSublattice_of_zsmul_mem hk hkx
  -- Lift the generator of the free rank-one quotient.
  let b := Module.finBasisOfFinrankEq ℤ (L ⧸ L') hrank
  obtain ⟨e, he⟩ := Submodule.Quotient.mk_surjective L' (b 0)
  refine ⟨e, e.property, fun m hm ↦ ⟨b.repr (Submodule.Quotient.mk ⟨m, hm⟩) 0, ?_⟩⟩
  have h := b.sum_repr (Submodule.Quotient.mk ⟨m, hm⟩)
  rw [Fin.sum_univ_one, ← he, ← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq] at h
  exact h

/-- If the span of a lattice-rational cone `σ` is not contained in the span of `τ`, some lattice
vector of `σ` lies outside `N_τ`. -/
private theorem exists_mem_notMem_coneSublattice (hσ : IsLatticeRational i σ)
    (h : ¬ Submodule.span ℝ (σ : Set V) ≤ Submodule.span ℝ (τ : Set V)) :
    ∃ g : N, i g ∈ σ ∧ g ∉ coneSublattice i τ := by
  by_contra! hg
  obtain ⟨s, hs⟩ := isLatticeRational_iff.1 hσ
  refine h ?_
  rw [hs, PointedCone.hull, Submodule.span_span_of_tower]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, hn, rfl⟩
  exact mem_coneSublattice.1 (hg n (hs ▸ PointedCone.subset_hull ⟨n, hn, rfl⟩))

/-- A lattice-rational cone `σ` has a lattice normal along every lattice-rational cone `τ ≤ σ`
whose real span has one dimension less: the quotient `N_σ / N_τ` is torsion free of rank one, and
one of its two generators is positive on a lattice vector of `σ` outside `N_τ`. -/
theorem exists_isLatticeNormal (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ)
    (hτ : IsLatticeRational i τ) (hτσ : τ ≤ σ)
    (hdim : finrank ℝ (Submodule.span ℝ (τ : Set V)) + 1 =
      finrank ℝ (Submodule.span ℝ (σ : Set V))) :
    ∃ n, IsLatticeNormal i τ σ n := by
  obtain ⟨e, he, hgen⟩ := exists_generator hi hσ hτ hτσ hdim
  obtain ⟨g, hgσ, hgτ⟩ := exists_mem_notMem_coneSublattice (τ := τ) hσ fun hle ↦ by
    have := hi.finiteDimensional
    have := Submodule.finrank_mono hle
    omega
  -- The sign of the coefficient of `g` decides which of `e` and `-e` points into `σ`.
  obtain ⟨k, hgk⟩ := hgen g (mem_coneSublattice.2 (Submodule.subset_span hgσ))
  have hk : k ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_zero] at hgk
    exact hgτ hgk
  rcases hk.lt_or_gt with hk | hk
  · refine ⟨-e, neg_mem he, fun m hm ↦ ?_, g, hgσ, -k, neg_pos.2 hk, by simpa using hgk⟩
    obtain ⟨l, hl⟩ := hgen m hm
    exact ⟨-l, by simpa using hl⟩
  · exact ⟨e, he, hgen, g, hgσ, k, hk, hgk⟩

namespace IsLatticeNormal

variable {n n' : N}

/-- Two lattice normals pointing in opposite directions modulo `N_τ` lie in `N_τ`: otherwise the
lattice vectors of `σ` witnessing their positivity would add up to a vector of the face `τ`,
forcing them into `τ`. -/
private theorem mem_of_add_mem (hτσ : τ.IsFaceOf σ) (hn : IsLatticeNormal i τ σ n)
    (hn' : IsLatticeNormal i τ σ n') (hadd : n + n' ∈ coneSublattice i τ) :
    n ∈ coneSublattice i τ := by
  obtain ⟨g, hg, k, hk, hgk⟩ := hn.exists_pos
  obtain ⟨g', hg', k', hk', hgk'⟩ := hn'.exists_pos
  have hsum : k' • g + k • g' ∈ coneSublattice i τ := by
    have := add_mem (add_mem (zsmul_mem hgk k') (zsmul_mem hgk' k)) (zsmul_mem hadd (k * k'))
    convert this using 1
    simp only [smul_sub, smul_add, smul_smul, mul_comm k' k]
    abel
  have hmem : (k' : ℝ) • i g + (k : ℝ) • i g' ∈ τ := by
    refine hτσ.mem_of_mem_span (add_mem (σ.smul_mem (by positivity) hg)
      (σ.smul_mem (by positivity) hg')) ?_
    simpa [Int.cast_smul_eq_zsmul] using hsum
  have hgτ : i g ∈ τ := by
    have h := hτσ.mem_of_add_mem_left (σ.smul_mem (by positivity) hg)
      (σ.smul_mem (by positivity) hg') hmem
    simpa [smul_smul, (show (k' : ℝ) ≠ 0 by positivity)] using
      τ.smul_mem (inv_nonneg.2 (show (0 : ℝ) ≤ k' by positivity)) h
  have hkn : k • n ∈ coneSublattice i τ := by
    simpa using sub_mem (mem_coneSublattice.2 (Submodule.subset_span hgτ)) hgk
  exact mem_coneSublattice_of_zsmul_mem hk.ne' hkn

/-- Along a face `τ` of `σ`, a lattice normal is unique modulo the sublattice `N_τ`. -/
theorem sub_mem (hτσ : τ.IsFaceOf σ) (hn : IsLatticeNormal i τ σ n)
    (hn' : IsLatticeNormal i τ σ n') : n - n' ∈ coneSublattice i τ := by
  obtain ⟨a, ha⟩ := hn'.exists_sub_zsmul_mem n hn.mem
  obtain ⟨b, hb⟩ := hn.exists_sub_zsmul_mem n' hn'.mem
  -- If `n` lies in `N_τ`, so does `n'`.
  have hτ : n ∈ coneSublattice i τ → n - n' ∈ coneSublattice i τ := fun h ↦
    _root_.sub_mem h (by simpa using add_mem hb (zsmul_mem h b))
  have hab : (1 - a * b) • n ∈ coneSublattice i τ := by
    convert add_mem ha (zsmul_mem hb a) using 1
    simp only [sub_smul, one_smul, smul_sub, smul_smul]
    abel
  by_cases h1 : a * b = 1
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with rfl | rfl
    · simpa using ha
    · exact hτ (mem_of_add_mem hτσ hn hn' (by simpa using ha))
  · exact hτ (mem_coneSublattice_of_zsmul_mem (sub_ne_zero.2 (Ne.symm h1)) hab)

/-- Along a face `τ` of `σ`, an integral character vanishing on `N_τ` takes the same value on any
two lattice normals. -/
theorem apply_eq (hτσ : τ.IsFaceOf σ) (hn : IsLatticeNormal i τ σ n)
    (hn' : IsLatticeNormal i τ σ n') {u : N →+ ℤ} (hu : coneSublattice i τ ≤ u.ker) :
    u n = u n' := by
  simpa [sub_eq_zero] using hu (hn.sub_mem hτσ hn')

end IsLatticeNormal

/-- A chosen lattice normal of `σ` along `τ`. It satisfies `IsLatticeNormal` whenever some lattice
normal exists, in particular along every facet of a lattice-rational cone
(`isLatticeNormal_latticeNormal`); characters vanishing on `N_τ` do not see the choice
(`IsLatticeNormal.apply_eq`). -/
noncomputable def latticeNormal (i : N →+ V) (τ σ : PointedCone ℝ V) : N :=
  Classical.epsilon (IsLatticeNormal i τ σ)

/-- Along a lattice-rational subcone of one dimension less, the chosen lattice normal is a lattice
normal. -/
theorem isLatticeNormal_latticeNormal (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ)
    (hτ : IsLatticeRational i τ) (hτσ : τ ≤ σ)
    (hdim : finrank ℝ (Submodule.span ℝ (τ : Set V)) + 1 =
      finrank ℝ (Submodule.span ℝ (σ : Set V))) :
    IsLatticeNormal i τ σ (latticeNormal i τ σ) :=
  Classical.epsilon_spec (exists_isLatticeNormal hi hσ hτ hτσ hdim)

end TauCeti.Toric
