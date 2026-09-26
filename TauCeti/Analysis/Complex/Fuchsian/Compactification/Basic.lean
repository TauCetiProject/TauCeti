/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
import TauCeti.Analysis.Complex.Fuchsian.Covolume

/-!
# The compactified quotient of a Fuchsian group: carrier and topology

Let `Γ ≤ PSL(2, ℝ)`. The *compactified quotient* `Subgroup.CompactifiedQuotient Γ` is the
disjoint union of the coarse orbit space `Γ \ ℍ` and the set `Γ.CuspOrbit` of cusp orbits of `Γ`,
one point being adjoined for each cusp orbit. It is the explicit inductive type with constructors
`ofQuotient` and `ofCusp`, canonically equivalent to the corresponding sum type.

For a discrete `Γ` its topology is the usual one: a set is open when its trace on `Γ \ ℍ` is
open and, for every cusp orbit it contains, it contains the image of a sufficiently high horodisc
at some normalized cusp datum representing that orbit, together with the cusp orbit. The basic
neighbourhoods `cuspNhd D A` of a cusp orbit are exactly these sets, and every cusp datum
representing the orbit, and every lower bound on the height, gives a neighbourhood basis
(`Subgroup.CompactifiedQuotient.nhds_basis_cuspNhd`): the topology is independent of the
choice of representative, scaling, and height. This uses that equivalent cusps have proportional
heights (`TauCeti.Subgroup.CuspDatum.exists_image_quotientMk_horodisc_eq`). Discreteness is
needed for the whole space to be open: it guarantees that every cusp orbit is represented by a
normalized cusp datum (`TauCeti.Subgroup.CuspDatum.cuspOrbit_surjective`), whereas for a
nondiscrete `Γ` a cusp may have a noncyclic stabilizer and no such datum.

The coarse quotient embeds as an open subset (`isOpenEmbedding_ofQuotient`), whose complement is
the closed set of cusp orbits, and is dense. The compactified quotient is Hausdorff and second
countable: two cusps are separated by high horodiscs
(`TauCeti.Subgroup.CuspDatum.disjoint_image_quotientMk_horodisc_iff`), and a point of the orbit
space is separated from a cusp because orbits stay uniformly low near a point
(`TauCeti.Subgroup.CuspDatum.exists_isOpen_mem_disjoint_image_quotientMk_horodisc`).
Compactness for a cofinite group and the complex structure at the cusps are not part of this
file.

## Main declarations

* `Subgroup.CompactifiedQuotient`: the carrier, with its topology for a discrete `Γ`.
* `Subgroup.CompactifiedQuotient.equivSum`: the identification with the sum type.
* `Subgroup.CompactifiedQuotient.cuspNhd`: the basic neighbourhoods of a cusp orbit.
* `Subgroup.CompactifiedQuotient.nhds_basis_cuspNhd`: they form a neighbourhood basis, for
  every cusp datum representing the orbit and every lower bound on the height.
* `Subgroup.CompactifiedQuotient.isOpenEmbedding_ofQuotient` and
  `Subgroup.CompactifiedQuotient.dense_range_ofQuotient`: the coarse quotient is an open dense
  subspace.
* `Subgroup.CompactifiedQuotient.instT2Space` and
  `Subgroup.CompactifiedQuotient.instSecondCountableTopology`: the compactified quotient is
  Hausdorff and second countable.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Chapter 4.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4–2.5.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§18–19.
-/

public section

open Filter MulAction Set Topology TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Subgroup

/-- The compactified quotient of `Γ ≤ PSL(2, ℝ)`: the coarse orbit space `Γ \ ℍ` with one point
adjoined for each cusp orbit of `Γ`. -/
inductive CompactifiedQuotient (Γ : Subgroup PSL(2, ℝ)) where
  /-- A point of the coarse orbit space `Γ \ ℍ`. -/
  | ofQuotient (point : orbitRel.Quotient Γ ℍ)
  /-- The point adjoined for a cusp orbit. -/
  | ofCusp (cusp : Γ.CuspOrbit)

namespace CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The compactified quotient is the sum of the coarse orbit space and the set of cusp orbits. -/
def equivSum (Γ : Subgroup PSL(2, ℝ)) :
    Γ.CompactifiedQuotient ≃ orbitRel.Quotient Γ ℍ ⊕ Γ.CuspOrbit where
  toFun
    | .ofQuotient p => Sum.inl p
    | .ofCusp C => Sum.inr C
  invFun
    | Sum.inl p => .ofQuotient p
    | Sum.inr C => .ofCusp C
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

@[simp]
theorem equivSum_ofQuotient (p : orbitRel.Quotient Γ ℍ) : equivSum Γ (ofQuotient p) = Sum.inl p :=
  (rfl)

@[simp]
theorem equivSum_ofCusp (C : Γ.CuspOrbit) : equivSum Γ (ofCusp C) = Sum.inr C :=
  (rfl)

@[simp]
theorem equivSum_symm_inl (p : orbitRel.Quotient Γ ℍ) :
    (equivSum Γ).symm (Sum.inl p) = ofQuotient p :=
  (rfl)

@[simp]
theorem equivSum_symm_inr (C : Γ.CuspOrbit) : (equivSum Γ).symm (Sum.inr C) = ofCusp C :=
  (rfl)

/-- Injectivity of the coarse-quotient inclusion, in the form consumed by the open-embedding API
(compare `Sum.inl_injective`). -/
theorem ofQuotient_injective : Function.Injective (ofQuotient (Γ := Γ)) :=
  fun _ _ h ↦ ofQuotient.inj h

/-- The cusp orbits are exactly the points outside the coarse orbit space. -/
theorem compl_range_ofQuotient : (range (ofQuotient (Γ := Γ)))ᶜ = range ofCusp := by
  ext x
  cases x <;> simp

/-! ### Cusp neighbourhoods -/

/-- The basic neighbourhood of the cusp orbit of the cusp datum `D` at height `A`: the cusp orbit
together with the image of the horodisc of height `A` at `D`. -/
def cuspNhd (D : Γ.CuspDatum) (A : ℝ) : Set Γ.CompactifiedQuotient :=
  insert (ofCusp D.cuspOrbit) (ofQuotient '' (Quotient.mk (orbitRel Γ ℍ) '' horodisc D A))

variable (D : Γ.CuspDatum) (A : ℝ)

@[simp]
theorem ofQuotient_mem_cuspNhd_iff {p : orbitRel.Quotient Γ ℍ} :
    ofQuotient p ∈ cuspNhd D A ↔ p ∈ Quotient.mk (orbitRel Γ ℍ) '' horodisc D A := by
  simp [cuspNhd]

@[simp]
theorem ofCusp_mem_cuspNhd_iff {C : Γ.CuspOrbit} : ofCusp C ∈ cuspNhd D A ↔ C = D.cuspOrbit := by
  simp [cuspNhd]

theorem ofCusp_mem_cuspNhd : ofCusp D.cuspOrbit ∈ cuspNhd D A :=
  (ofCusp_mem_cuspNhd_iff D A).mpr rfl

@[simp]
theorem preimage_ofQuotient_cuspNhd :
    ofQuotient ⁻¹' cuspNhd D A = Quotient.mk (orbitRel Γ ℍ) '' horodisc D A := by
  ext p
  exact ofQuotient_mem_cuspNhd_iff D A

/-- Cusp neighbourhoods shrink as the height grows. -/
theorem cuspNhd_antitone : Antitone (cuspNhd D) := fun _ _ h ↦
  insert_subset_insert (image_mono (image_mono (horodisc_antitone D h)))

/-- **Independence of the cusp datum.** Two cusp data representing the same cusp orbit have the
same cusp neighbourhoods, up to rescaling the height by a fixed positive factor. -/
theorem exists_cuspNhd_eq {D' : Γ.CuspDatum} (h : D'.cuspOrbit = D.cuspOrbit) :
    ∃ a : ℝ, 0 < a ∧ ∀ A : ℝ, cuspNhd D' (a * A) = cuspNhd D A := by
  obtain ⟨a, ha, hA⟩ :=
    exists_image_quotientMk_horodisc_eq D D' ((D'.cuspOrbit_eq_iff D).mp h)
  exact ⟨a, ha, fun A ↦ by rw [cuspNhd, cuspNhd, h, hA]⟩

/-- Every cusp neighbourhood at a cusp datum contains a cusp neighbourhood at any other cusp datum
representing the same cusp orbit. -/
theorem exists_cuspNhd_subset {D' : Γ.CuspDatum} (h : D'.cuspOrbit = D.cuspOrbit) (A' : ℝ) :
    ∃ A : ℝ, cuspNhd D A ⊆ cuspNhd D' A' := by
  obtain ⟨a, -, hA⟩ := exists_cuspNhd_eq D' h.symm
  exact ⟨a * A', (hA A').le⟩

/-- Cusp neighbourhoods at two cusp data are disjoint as soon as the horodisc images are and the
cusp orbits differ. -/
theorem disjoint_cuspNhd {D' : Γ.CuspDatum} {A' : ℝ} (hC : D.cuspOrbit ≠ D'.cuspOrbit)
    (h : Disjoint (Quotient.mk (orbitRel Γ ℍ) '' horodisc D A)
      (Quotient.mk (orbitRel Γ ℍ) '' horodisc D' A')) :
    Disjoint (cuspNhd D A) (cuspNhd D' A') := by
  rw [disjoint_left]
  rintro x hx hx'
  cases x with
  | ofQuotient p =>
    rw [ofQuotient_mem_cuspNhd_iff] at hx hx'
    exact disjoint_left.mp h hx hx'
  | ofCusp C =>
    rw [ofCusp_mem_cuspNhd_iff] at hx hx'
    exact hC (hx.symm.trans hx')

/-! ### The topology -/

variable [DiscreteTopology Γ]

/-- A set is open when its trace on the coarse orbit space is open and it contains a cusp
neighbourhood, at some cusp datum representing it, of every cusp orbit it contains. Discreteness
provides a cusp datum for every cusp orbit, so that the whole space is open. -/
instance : TopologicalSpace Γ.CompactifiedQuotient where
  IsOpen U := IsOpen (ofQuotient ⁻¹' U) ∧
    ∀ C : Γ.CuspOrbit, ofCusp C ∈ U → ∃ D : Γ.CuspDatum, D.cuspOrbit = C ∧ ∃ A : ℝ, cuspNhd D A ⊆ U
  isOpen_univ := ⟨isOpen_univ, fun C _ ↦
    (CuspDatum.cuspOrbit_surjective C).imp fun _ hD ↦ ⟨hD, 0, subset_univ _⟩⟩
  isOpen_inter U V hU hV := ⟨hU.1.inter hV.1, fun C hC ↦ by
    obtain ⟨D, hD, A, hA⟩ := hU.2 C hC.1
    obtain ⟨D', hD', A', hA'⟩ := hV.2 C hC.2
    obtain ⟨B, hB⟩ := exists_cuspNhd_subset D (hD'.trans hD.symm) A'
    exact ⟨D, hD, max A B, subset_inter ((cuspNhd_antitone D (le_max_left A B)).trans hA)
      ((cuspNhd_antitone D (le_max_right A B)).trans (hB.trans hA'))⟩⟩
  isOpen_sUnion S hS := ⟨by
    rw [preimage_sUnion]
    exact isOpen_biUnion fun U hU ↦ (hS U hU).1, fun C hC ↦ by
    obtain ⟨U, hU, hCU⟩ := mem_sUnion.mp hC
    obtain ⟨D, hD, A, hA⟩ := (hS U hU).2 C hCU
    exact ⟨D, hD, A, hA.trans (subset_sUnion_of_mem hU)⟩⟩

theorem isOpen_iff {U : Set Γ.CompactifiedQuotient} :
    IsOpen U ↔ IsOpen (ofQuotient ⁻¹' U) ∧
      ∀ C : Γ.CuspOrbit, ofCusp C ∈ U →
        ∃ D : Γ.CuspDatum, D.cuspOrbit = C ∧ ∃ A : ℝ, cuspNhd D A ⊆ U :=
  Iff.rfl

theorem continuous_ofQuotient : Continuous (ofQuotient (Γ := Γ)) :=
  continuous_def.mpr fun _ hU ↦ hU.1

theorem isOpenMap_ofQuotient : IsOpenMap (ofQuotient (Γ := Γ)) := fun V hV ↦
  ⟨by rwa [ofQuotient_injective.preimage_image], fun C hC ↦ by
    obtain ⟨p, -, hp⟩ := hC
    cases hp⟩

/-- **The coarse orbit space is an open subspace of the compactified quotient.** -/
theorem isOpenEmbedding_ofQuotient : IsOpenEmbedding (ofQuotient (Γ := Γ)) :=
  .of_continuous_injective_isOpenMap continuous_ofQuotient ofQuotient_injective
    isOpenMap_ofQuotient

@[simp]
theorem isOpen_range_ofQuotient : IsOpen (range (ofQuotient (Γ := Γ))) :=
  isOpenEmbedding_ofQuotient.isOpen_range

/-- The cusp orbits form a closed subset of the compactified quotient. -/
@[simp]
theorem isClosed_range_ofCusp : IsClosed (range (ofCusp (Γ := Γ))) := by
  rw [← compl_range_ofQuotient]
  exact isOpen_range_ofQuotient.isClosed_compl

@[simp]
theorem isOpen_cuspNhd : IsOpen (cuspNhd D A) := by
  refine ⟨?_, fun C hC ↦ ⟨D, ((ofCusp_mem_cuspNhd_iff D A).mp hC).symm, A, subset_rfl⟩⟩
  rw [preimage_ofQuotient_cuspNhd]
  exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ (isOpen_horodisc D A)

@[simp]
theorem cuspNhd_mem_nhds : cuspNhd D A ∈ 𝓝 (ofCusp D.cuspOrbit) :=
  (isOpen_cuspNhd D A).mem_nhds (ofCusp_mem_cuspNhd D A)

/-- **The cusp neighbourhoods form a neighbourhood basis of the cusp orbit**, for every cusp datum
representing that orbit and every lower bound `A₀` on the height. In particular the topology at a
cusp is independent of the choice of representative, scaling, and height. -/
theorem nhds_basis_cuspNhd (A₀ : ℝ) :
    (𝓝 (ofCusp D.cuspOrbit)).HasBasis (fun A : ℝ ↦ A₀ ≤ A) (cuspNhd D) := by
  refine hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, fun ⟨A, _, hA⟩ ↦
    mem_of_superset (cuspNhd_mem_nhds D A) hA⟩
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨D', hD', A', hA'⟩ := hV.2 _ hxV
  obtain ⟨A, hA⟩ := exists_cuspNhd_subset D hD' A'
  exact ⟨max A₀ A, le_max_left _ _,
    (cuspNhd_antitone D (le_max_right A₀ A)).trans (hA.trans (hA'.trans hVU))⟩

theorem mem_nhds_ofCusp_iff {U : Set Γ.CompactifiedQuotient} :
    U ∈ 𝓝 (ofCusp D.cuspOrbit) ↔ ∃ A : ℝ, cuspNhd D A ⊆ U :=
  ⟨fun hU ↦ ((nhds_basis_cuspNhd D 0).mem_iff.mp hU).imp fun _ h ↦ h.2,
    fun ⟨A, hA⟩ ↦ mem_of_superset (cuspNhd_mem_nhds D A) hA⟩

/-- Points of the upper half-plane converge to the cusp orbit in the compactified quotient as
their height above the cusp, in the scaling coordinate of the datum, tends to infinity. -/
theorem tendsto_ofQuotient_quotientMk_nhds_ofCusp :
    Tendsto (fun z : ℍ ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) z))
      (Filter.comap (fun z : ℍ ↦ (D.scaling • z).im) atTop) (𝓝 (ofCusp D.cuspOrbit)) := by
  refine (nhds_basis_cuspNhd D 0).tendsto_right_iff.mpr fun A _ ↦ ?_
  exact mem_of_superset (preimage_mem_comap (Ioi_mem_atTop A)) fun z hz ↦
    Or.inr ⟨_, ⟨z, (mem_horodisc D).mpr hz, rfl⟩, rfl⟩

/-! ### Density, separation and countability -/

/-- **The coarse orbit space is dense in the compactified quotient.** -/
theorem dense_range_ofQuotient : Dense (range (ofQuotient (Γ := Γ))) := by
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ ↦ ?_
  cases x with
  | ofQuotient p => exact ⟨_, hx, p, rfl⟩
  | ofCusp C =>
    obtain ⟨D, -, A, hA⟩ := hU.2 C hx
    obtain ⟨z, hz⟩ := nonempty_horodisc D A
    exact ⟨_, hA (Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩), _, rfl⟩

/-- A point of the coarse orbit space and a cusp orbit have disjoint open neighbourhoods. -/
private theorem exists_isOpen_disjoint_ofQuotient_ofCusp (p : orbitRel.Quotient Γ ℍ)
    (C : Γ.CuspOrbit) :
    ∃ u v : Set Γ.CompactifiedQuotient, IsOpen u ∧ IsOpen v ∧ ofQuotient p ∈ u ∧
      ofCusp C ∈ v ∧ Disjoint u v := by
  obtain ⟨D, rfl⟩ := CuspDatum.cuspOrbit_surjective C
  induction p using Quotient.inductionOn with | h z => ?_
  obtain ⟨S, hS, hz, A, hA⟩ := exists_isOpen_mem_disjoint_image_quotientMk_horodisc D z
  refine ⟨ofQuotient '' (Quotient.mk (orbitRel Γ ℍ) '' S), cuspNhd D A,
    isOpenMap_ofQuotient _ (MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ hS),
    isOpen_cuspNhd D A, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ofCusp_mem_cuspNhd D A, disjoint_left.mpr ?_⟩
  rintro _ ⟨q, hq, rfl⟩ hq'
  rw [ofQuotient_mem_cuspNhd_iff] at hq'
  exact disjoint_left.mp hA hq hq'

/-- **The compactified quotient is Hausdorff.** -/
instance instT2Space : T2Space Γ.CompactifiedQuotient where
  t2 x y hxy := by
    cases x with
    | ofQuotient p =>
      cases y with
      | ofQuotient q =>
        exact separated_by_isOpenEmbedding isOpenEmbedding_ofQuotient
          fun h ↦ hxy (congrArg ofQuotient h)
      | ofCusp C => exact exists_isOpen_disjoint_ofQuotient_ofCusp p C
    | ofCusp C =>
      cases y with
      | ofQuotient q =>
        obtain ⟨u, v, hu, hv, hq, hC, huv⟩ := exists_isOpen_disjoint_ofQuotient_ofCusp q C
        exact ⟨v, u, hv, hu, hC, hq, huv.symm⟩
      | ofCusp C' =>
        obtain ⟨D, rfl⟩ := CuspDatum.cuspOrbit_surjective C
        obtain ⟨D', rfl⟩ := CuspDatum.cuspOrbit_surjective C'
        have hc : D'.cusp ∉ orbit Γ D.cusp := fun h ↦
          hxy (congrArg ofCusp ((D'.cuspOrbit_eq_iff D).mpr h).symm)
        exact ⟨cuspNhd D D.width, cuspNhd D' D'.width, isOpen_cuspNhd D _, isOpen_cuspNhd D' _,
          ofCusp_mem_cuspNhd D _, ofCusp_mem_cuspNhd D' _,
          disjoint_cuspNhd D _ (fun h ↦ hxy (congrArg ofCusp h))
            ((disjoint_image_quotientMk_horodisc_iff D D' D.width_pos.le le_rfl).mpr hc)⟩

/-- **The compactified quotient is second countable**: the coarse orbit space is second
countable, there are countably many cusp orbits, and each has the countable neighbourhood basis of
cusp neighbourhoods at integer heights. -/
instance instSecondCountableTopology : SecondCountableTopology Γ.CompactifiedQuotient := by
  have : SecondCountableTopology (orbitRel.Quotient Γ ℍ) :=
    ContinuousConstSMul.secondCountableTopology
  choose D hD using CuspDatum.cuspOrbit_surjective (Γ := Γ)
  refine TopologicalSpace.IsTopologicalBasis.secondCountableTopology
    (b := (ofQuotient '' ·) '' TopologicalSpace.countableBasis (orbitRel.Quotient Γ ℍ) ∪
      ⋃ C, range fun n : ℕ ↦ cuspNhd (D C) n) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ fun x u hx hu ↦ ?_
    · rintro u (⟨v, hv, rfl⟩ | hu)
      · exact isOpenMap_ofQuotient _ (TopologicalSpace.isOpen_of_mem_countableBasis hv)
      · obtain ⟨C, n, rfl⟩ := mem_iUnion.mp hu
        exact isOpen_cuspNhd _ _
    · cases x with
      | ofQuotient p =>
        obtain ⟨v, hv, hpv, hvu⟩ := (TopologicalSpace.isBasis_countableBasis
          (orbitRel.Quotient Γ ℍ)).exists_subset_of_mem_open hx hu.1
        exact ⟨ofQuotient '' v, Or.inl ⟨v, hv, rfl⟩, ⟨p, hpv, rfl⟩, image_subset_iff.mpr hvu⟩
      | ofCusp C =>
        obtain ⟨D', hD', A', hA'⟩ := hu.2 C hx
        obtain ⟨A, hA⟩ := exists_cuspNhd_subset (D C) (hD'.trans (hD C).symm) A'
        obtain ⟨n, hn⟩ := exists_nat_ge A
        refine ⟨cuspNhd (D C) n, Or.inr (mem_iUnion.mpr ⟨C, n, rfl⟩), ?_,
          (cuspNhd_antitone _ hn).trans (hA.trans hA')⟩
        rw [ofCusp_mem_cuspNhd_iff]
        exact (hD C).symm
  · exact ((TopologicalSpace.countable_countableBasis _).image _).union
      (countable_iUnion fun _ ↦ countable_range _)

end CompactifiedQuotient

end Subgroup
