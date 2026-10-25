/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
import TauCeti.Analysis.Complex.Fuchsian.Cusp.DirichletDomain
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Thick
import TauCeti.Analysis.Complex.Fuchsian.Systole

/-!
# The non-elliptic thin part of a Dirichlet domain of a cofinite group

Let `Γ ≤ PSL(2, ℝ)` be cofinite, let `p ∈ ℍ` and `ε > 0`. We show that, apart from finitely many
cusp horodiscs, every point of the Dirichlet domain of `Γ` centred at `p` lies in a bounded set or
is moved less than `ε` by a nonidentity element of `Γ` fixing a point of `ℍ`. The horodiscs may be
taken at any common height.

This is the thick-thin decomposition behind Siegel's theorem that the Dirichlet domain of a
cofinite group is a finite-sided polygon, with only the elliptic thin part left open. The proof
combines three results. Take `ε' ≤ ε` below the systole bound
`Subgroup.IsCofinite.exists_pos_exists_smul_eq_or_isParabolic_of_dist_smul_lt`, so that an
element of `Γ` moving a point less than `ε'` is elliptic, parabolic or the identity.

* The `ε'`-thick part of the Dirichlet domain is bounded
  (`Subgroup.IsCofinite.isBounded_dirichletDomain_inter_thickPart`).
* A point moved less than `ε'` by a nonidentity element fixing a point of `ℍ` is elliptic thin.
* A point moved less than `ε'` by a parabolic element lies near a cusp. There are finitely many
  cusp orbits (`Subgroup.IsCofinite.finite_cuspOrbit`); for a cusp datum of each orbit, the
  parabolic thin part of the Dirichlet domain is covered by finitely many translates of a high
  horodisc, apart from a bounded set. This is
  `CuspDatum.exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff`, in the
  namespace `TauCeti.Subgroup`. Each such translate is the horodisc of the transported cusp datum.

Changing the heights of finitely many horodiscs only adds bounded bands of the Dirichlet domain
(`TauCeti.Subgroup.CuspDatum.isBounded_dirichletDomain_inter_horodisc_diff`), so the heights are
arbitrary.

If moreover the elliptic thin part of the Dirichlet domain is bounded, this gives the bounded cusp
truncation consumed by
`Subgroup.exists_convexPolygon_carrier_eq_dirichletDomain_of_isBounded_truncation` and
`Subgroup.compactSpace_compactifiedQuotient_of_isBounded_truncation`.

## Main results

* `Subgroup.IsCofinite.exists_finset_isBounded_dirichletDomain_diff_iUnion_horodisc_diff`: apart
  from finitely many cusp horodiscs of any common height and from its elliptic thin part, a
  Dirichlet domain of a cofinite group is bounded.

## References

* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick-thin decomposition of a finite-volume hyperbolic manifold).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.1 (Dirichlet regions of cofinite groups).
-/

public section

open MulAction Set UpperHalfPlane TauCeti
open scoped MatrixGroups Pointwise

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The non-elliptic thin part of a Dirichlet domain of a cofinite group lies in finitely many
cusp horodiscs of one positive height, apart from a bounded set. -/
private theorem IsCofinite.exists_finset_pos_isBounded_dirichletDomain_diff_iUnion_horodisc_diff
    (hΓ : Γ.IsCofinite) (p : ℍ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Γ.CuspDatum, ∃ A₀ > 0, Bornology.IsBounded
      ((dirichletDomain Γ p \ ⋃ D ∈ s, D.horodisc A₀) \
        {z | ∃ g ∈ Γ, g ≠ 1 ∧ (∃ w : ℍ, g • w = w) ∧ dist (g • z) z < ε}) := by
  classical
  have := hΓ.discreteTopology
  have := hΓ.finite_cuspOrbit
  have := Fintype.ofFinite Γ.CuspOrbit
  obtain ⟨δ, hδ, hshort⟩ := hΓ.exists_pos_exists_smul_eq_or_isParabolic_of_dist_smul_lt
  have hε' : 0 < min ε δ := lt_min hε hδ
  -- the parabolic thin part at each cusp orbit lies in finitely many horodiscs and a bounded set
  choose t ht using fun C : Γ.CuspOrbit ↦
    C.cuspDatum.exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff p hε'
  set A₀ : ℝ := 1 + ∑ C : Γ.CuspOrbit, ((C.cuspDatum.scaling • p).im + C.cuspDatum.width / 2)
  have hnonneg (C : Γ.CuspOrbit) : 0 ≤ (C.cuspDatum.scaling • p).im + C.cuspDatum.width / 2 :=
    add_nonneg (im_pos _).le (half_pos C.cuspDatum.width_pos).le
  have hA₀ (C : Γ.CuspOrbit) : (C.cuspDatum.scaling • p).im + C.cuspDatum.width / 2 ≤ A₀ :=
    (Finset.single_le_sum (fun C _ ↦ hnonneg C) (Finset.mem_univ C)).trans
      (le_add_of_nonneg_left zero_le_one)
  -- the translates of these horodiscs are the horodiscs of the transported cusp data
  have hconj (γ : Γ) : ConjAct.toConjAct (γ : PSL(2, ℝ)) • Γ = Γ := conj_smul_eq_self_of_mem γ.2
  refine ⟨Finset.univ.biUnion fun C ↦ (t C).image fun γ ↦ C.cuspDatum.conj (hconj γ), A₀,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun C _ ↦ hnonneg C),
    ((hΓ.isBounded_dirichletDomain_inter_thickPart p hε').union
      (Bornology.isBounded_iUnion.mpr fun C ↦ ht C A₀ (hA₀ C))).subset ?_⟩
  rintro z ⟨⟨hz, hzA₀⟩, hzE⟩
  by_cases hthick : z ∈ thickPart Γ (min ε δ)
  · exact Or.inl ⟨hz, hthick⟩
  refine Or.inr ?_
  -- otherwise a short element moves `z`, and it is parabolic since `z` is not elliptic thin
  obtain ⟨g, hg1, hgz⟩ : ∃ g : Γ, g ≠ 1 ∧ dist (g • z) z < min ε δ := by
    simpa only [mem_thickPart, not_forall, not_le, exists_prop] using hthick
  have hg1' : (g : PSL(2, ℝ)) ≠ 1 := fun h ↦ hg1 (Subtype.ext h)
  obtain ⟨w, hw⟩ | hpar := hshort g g.2 z (hgz.trans_le (min_le_right ε δ))
  · exact absurd ⟨g, g.2, hg1', ⟨w, hw⟩, hgz.trans_le (min_le_left ε δ)⟩ hzE
  -- its fixed point is `Γ`-equivalent to the cusp of the chosen datum of its cusp orbit
  have hξ := isCuspPoint_iff_exists_parabolicFixedPoint_eq.mpr ⟨g, hpar, rfl⟩
  obtain ⟨D, hD⟩ := hξ.exists_cuspDatum_cusp_eq
  set C := D.cuspOrbit
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, γ • C.cuspDatum.cusp = D.cusp :=
    (D.cuspOrbit_eq_iff C.cuspDatum).mp C.cuspOrbit_cuspDatum.symm
  refine mem_iUnion.mpr ⟨C, ⟨hz, γ, g, mem_stabilizer_iff.mpr ?_, hg1, hgz⟩, fun h ↦ hzA₀ ?_⟩
  · rw [hγ, hD]
    exact hpar.smul_parabolicFixedPoint
  -- a translate of the horodisc of the chosen datum is the horodisc of a transported datum
  obtain ⟨γ', hγ', hzγ'⟩ := mem_iUnion₂.mp h
  refine mem_iUnion₂.mpr ⟨_, Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C,
    Finset.mem_image_of_mem _ hγ'⟩, ?_⟩
  rw [TauCeti.Subgroup.CuspDatum.horodisc_conj]
  exact hzγ'

/-- **The non-elliptic thin part of a Dirichlet domain of a cofinite group.** For a cofinite
`Γ ≤ PSL(2, ℝ)`, a centre `p` and `ε > 0`, there are finitely many cusp data such that, for every
height `A`, the points of the Dirichlet domain centred at `p` outside their horodiscs of height
`A` form a bounded set, apart from the points moved less than `ε` by a nonidentity element of `Γ`
fixing a point of `ℍ`. -/
theorem IsCofinite.exists_finset_isBounded_dirichletDomain_diff_iUnion_horodisc_diff
    (hΓ : Γ.IsCofinite) (p : ℍ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Γ.CuspDatum, ∀ A : ℝ, Bornology.IsBounded
      ((dirichletDomain Γ p \ ⋃ D ∈ s, D.horodisc A) \
        {z | ∃ g ∈ Γ, g ≠ 1 ∧ (∃ w : ℍ, g • w = w) ∧ dist (g • z) z < ε}) := by
  obtain ⟨s, A₀, hA₀, hb⟩ :=
    hΓ.exists_finset_pos_isBounded_dirichletDomain_diff_iUnion_horodisc_diff p hε
  refine ⟨s, fun A ↦ (hb.union ((Bornology.isBounded_biUnion_finset s).mpr fun D _ ↦
    D.isBounded_dirichletDomain_inter_horodisc_diff p hA₀ A)).subset ?_⟩
  -- changing the heights from `A₀` to `A` only adds bounded bands
  rintro z ⟨⟨hz, hzA⟩, hzE⟩
  by_cases hzA₀ : z ∈ ⋃ D ∈ s, D.horodisc A₀
  · obtain ⟨D, hD, hzD⟩ := mem_iUnion₂.mp hzA₀
    exact Or.inr (mem_iUnion₂.mpr ⟨D, hD, ⟨hz, hzD⟩, fun h ↦ hzA (mem_iUnion₂.mpr ⟨D, hD, h⟩)⟩)
  · exact Or.inl ⟨⟨hz, hzA₀⟩, hzE⟩

end Subgroup
