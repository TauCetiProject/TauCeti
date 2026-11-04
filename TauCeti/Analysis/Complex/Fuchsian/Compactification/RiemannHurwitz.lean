/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Divisor
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Compactness

/-!
# The Riemann–Hurwitz formula for finite-index maps of Fuchsian quotients

Let `Γ ≤ PSL(2, ℝ)` be discrete. Deleting the elliptic orbits and the adjoined cusps from the
compactified quotient `X(Γ)` leaves exactly the orbit space of the free locus of `Γ`, the
points of `ℍ` with trivial stabilizer
(`Subgroup.CompactifiedQuotient.freeLocusQuotientHomeomorph`). When `X(Γ)` is compact, only
finitely many points are deleted.

For a discrete `Δ ≤ Γ` of finite index, the map `X(Δ) → X(Γ)` is ramified only over elliptic
orbits and cusps of `Γ`. Applying the topological branched-cover formula
`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset`
with that finite set of punctures, the degree being the index `[Γ : Δ]`, gives the
Riemann–Hurwitz formula for Fuchsian groups in Euler-characteristic form,

`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - ∑_{interior} (e - 1) - ∑_{cusps} (e - 1)`,

where `e` is the index of the elliptic stabilizer of `Δ` in that of `Γ` at an interior orbit and
the index of the boundary stabilizers at a cusp. Euler characteristics are the finite-CW Euler
characteristics `TauCeti.eulerChar`. The finite-CW-type hypotheses are on the two compactified
quotients and on the free-locus quotient of `Γ`, an object attached to `Γ` alone.

## Main results

* `Subgroup.CompactifiedQuotient.range_ofFreeLocusQuotient`: the free-locus quotient fills the
  compactified quotient outside its elliptic orbits and cusps.
* `Subgroup.CompactifiedQuotient.freeLocusQuotientHomeomorph`: the corresponding homeomorphism.
* `Subgroup.CompactifiedQuotient.finite_ellipticOrbits_union_cusps`: in a compact compactified
  quotient there are finitely many elliptic orbits and cusps.
* `TauCeti.Fuchsian.branchValues_subset_ellipticOrbits_union_cusps`: a finite-index map of
  compactified quotients branches only over elliptic orbits and cusps.
* `TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree`: the
  Riemann–Hurwitz formula `χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R`, with `R` the ramification degree.
* `TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_interior_sub_cusps`: the
  same, with `R` split into elliptic stabilizer indices and cusp stabilizer indices.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §3.1 (the genus of `X(Γ)` from Riemann–Hurwitz).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §17 (the topological Riemann–Hurwitz formula).
-/

public noncomputable section

open Function MulAction Set Topology UpperHalfPlane
open Subgroup Subgroup.CompactifiedQuotient TauCeti TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)}

variable (Γ) in
/-- The orbit of a point of the free locus, as an interior point of the compactified quotient. -/
def ofFreeLocusQuotient : orbitRel.Quotient Γ (freeLocus Γ ℍ) → Γ.CompactifiedQuotient :=
  Quotient.lift (fun z ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) (z : ℍ))) fun a b hab ↦ by
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hab)
    exact congrArg ofQuotient (Quotient.sound (orbitRel_apply.mpr ⟨g, rfl⟩))

/-- The orbit of a free point is its orbit in the coarse quotient. -/
@[simp]
theorem ofFreeLocusQuotient_mk (z : freeLocus Γ ℍ) :
    ofFreeLocusQuotient Γ (Quotient.mk _ z) = ofQuotient (Quotient.mk (orbitRel Γ ℍ) (z : ℍ)) :=
  (rfl)

/-- Two free points in the same orbit of `Γ` on `ℍ` are in the same orbit on the free locus. -/
theorem ofFreeLocusQuotient_injective : Injective (ofFreeLocusQuotient Γ) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact (ofQuotient_injective hab)))
  exact Quotient.sound (orbitRel_apply.mpr ⟨g, Subtype.ext hg⟩)

/-- **The free-locus quotient fills the compactified quotient outside its elliptic orbits and
cusps.** An interior orbit comes from the free locus exactly when it is not elliptic, and no cusp
does. -/
theorem range_ofFreeLocusQuotient :
    range (ofFreeLocusQuotient Γ) = (ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp)ᶜ := by
  ext x
  cases x with
  | ofCusp C => simp [ofFreeLocusQuotient]
  | ofQuotient q =>
    induction q using Quotient.inductionOn with
    | h z =>
      simp only [mem_range, mem_compl_iff, mem_union, mem_image,
        ofQuotient_injective.eq_iff, exists_eq_right, quotientMk_mem_ellipticOrbits_iff,
        not_or, not_not, reduceCtorEq, exists_false, not_false_eq_true, and_true]
      constructor
      · rintro ⟨w, hw⟩
        induction w using Quotient.inductionOn with
        | h w =>
          exact (mem_freeLocus_iff_of_quotientMk_eq Γ ℍ (ofQuotient_injective hw)).mp w.2
      · exact fun hz ↦ ⟨Quotient.mk _ ⟨z, hz⟩, rfl⟩

variable [DiscreteTopology Γ]

/-- The inclusion of the free-locus quotient is continuous. -/
theorem continuous_ofFreeLocusQuotient : Continuous (ofFreeLocusQuotient Γ) :=
  (continuous_ofQuotient.comp (continuous_quotient_mk'.comp continuous_subtype_val)).quotient_lift
    _

/-- The inclusion of the free-locus quotient is open: the free locus is open in `ℍ`, and both
orbit projections and the inclusion of the coarse quotient are open maps. -/
theorem isOpenMap_ofFreeLocusQuotient : IsOpenMap (ofFreeLocusQuotient Γ) := by
  intro U hU
  have hV : IsOpen (Quotient.mk (orbitRel Γ (freeLocus Γ ℍ)) ⁻¹' U) :=
    hU.preimage continuous_quotient_mk'
  have himage : ofFreeLocusQuotient Γ '' U = ofQuotient '' (Quotient.mk (orbitRel Γ ℍ) ''
      ((↑) '' (Quotient.mk (orbitRel Γ (freeLocus Γ ℍ)) ⁻¹' U))) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      induction q using Quotient.inductionOn with
      | h w => exact ⟨_, ⟨_, ⟨w, hq, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, hw, rfl⟩
  rw [himage]
  exact isOpenMap_ofQuotient _ (isOpenMap_quotient_mk'_mul _
    ((isOpen_freeLocus Γ ℍ).isOpenMap_subtype_val _ hV))

/-- The free-locus quotient is an open subspace of the compactified quotient. -/
theorem isOpenEmbedding_ofFreeLocusQuotient : IsOpenEmbedding (ofFreeLocusQuotient Γ) :=
  .of_continuous_injective_isOpenMap continuous_ofFreeLocusQuotient
    ofFreeLocusQuotient_injective isOpenMap_ofFreeLocusQuotient

variable (Γ) in
/-- **The free-locus quotient is the compactified quotient punctured at its elliptic orbits and
cusps.** -/
def freeLocusQuotientHomeomorph :
    orbitRel.Quotient Γ (freeLocus Γ ℍ) ≃ₜ ↥(ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp)ᶜ :=
  isOpenEmbedding_ofFreeLocusQuotient.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_ofFreeLocusQuotient)

/-- The homeomorphism sends a free orbit to its point in the compactified quotient. -/
@[simp]
theorem freeLocusQuotientHomeomorph_apply (q : orbitRel.Quotient Γ (freeLocus Γ ℍ)) :
    (freeLocusQuotientHomeomorph Γ q : Γ.CompactifiedQuotient) = ofFreeLocusQuotient Γ q :=
  (rfl)

/-- A compact compactified quotient has only finitely many elliptic orbits and cusps. -/
theorem finite_ellipticOrbits_union_cusps [CompactSpace Γ.CompactifiedQuotient] :
    (ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp).Finite :=
  have := finite_cuspOrbit (Γ := Γ)
  (Γ.finite_ellipticOrbits.image _).union (finite_range _)

end Subgroup.CompactifiedQuotient

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

variable (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]

/-- **A finite-index map of compactified Fuchsian quotients branches only over elliptic orbits
and cusps.** Over an orbit of points with trivial stabilizer in `Γ`, every elliptic stabilizer
index is one. -/
theorem branchValues_subset_ellipticOrbits_union_cusps :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    (compactifiedQuotientFiniteHolomorphicMap h).branchValues ⊆
      ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro y hy
  obtain ⟨x, rfl, hx⟩ := (FiniteHolomorphicMap.mem_branchValues_iff _ y).mp hy
  rw [coe_compactifiedQuotientFiniteHolomorphicMap] at hx ⊢
  cases x with
  | ofCusp C => exact Or.inr ⟨cuspOrbitMap h C, (compactifiedQuotientMap_ofCusp h C).symm⟩
  | ofQuotient q =>
    induction q using Quotient.inductionOn with
    | h z =>
      rw [localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex] at hx
      refine Or.inl ⟨Quotient.mk (orbitRel Γ ℍ) z, ?_, ?_⟩
      swap
      · rw [compactifiedQuotientMap_ofQuotient]
        rfl
      rw [quotientMk_mem_ellipticOrbits_iff, mem_freeLocus]
      intro hz
      rw [ellipticRamificationIndex_eq_one_of_stabilizer_eq_bot h z hz] at hx
      exact lt_irrefl 1 hx

variable [hcompact : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  CompactSpace Δ.CompactifiedQuotient]
variable [hcw : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  FiniteCWType Δ.CompactifiedQuotient]
variable [FiniteCWType Γ.CompactifiedQuotient] [FiniteCWType (orbitRel.Quotient Γ (freeLocus Γ ℍ))]

/-- **The Riemann–Hurwitz formula for Fuchsian groups.** Let `Δ ≤ Γ` be discrete subgroups of
`PSL(2, ℝ)` of finite index, with `X(Δ)` compact. If the compactified quotients and the
free-locus quotient of `Γ` have finite CW type, then
`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R`, where `R` is the ramification degree of `X(Δ) → X(Γ)`. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        ramificationDegree (compactifiedQuotientMap h) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let f := compactifiedQuotientFiniteHolomorphicMap h
  have : CompactSpace Γ.CompactifiedQuotient :=
    ⟨f.surjective.range_eq ▸ isCompact_range f.holomorphic.continuous⟩
  have := (freeLocusQuotientHomeomorph Γ).symm.finiteCWType
  have hR := f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset
    finite_ellipticOrbits_union_cusps (branchValues_subset_ellipticOrbits_union_cusps h)
  rwa [coe_compactifiedQuotientFiniteHolomorphicMap, degree_compactifiedQuotientMap] at hR

/-- **The Riemann–Hurwitz formula for Fuchsian groups, with explicit ramification.** Under the
hypotheses of
`TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree`,
`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - ∑_q (e_q - 1) - ∑_C (e_C - 1)`. Here `q` runs over the orbits of
`Δ` on `ℍ`, with `e_q` the index of the stabilizer in `Δ` of a representative in its stabilizer
in `Γ`, and `C` runs over the cusp orbits of `Δ`, with `e_C` the index of the boundary
stabilizers at a representative cusp. Both sums have finite support, and the formula holds for
any choice of representatives. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_interior_sub_cusps
    (z : orbitRel.Quotient Δ ℍ → ℍ) (hz : ∀ q, Quotient.mk'' (z q) = q)
    (c : Δ.CuspOrbit → Δ.cuspPoints) (hc : ∀ C, Δ.cuspOrbitMk (c C) = C) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        (∑ᶠ q : orbitRel.Quotient Δ ℍ, (ellipticRamificationIndex h (z q) - 1) : ℕ) -
        (∑ᶠ C : Δ.CuspOrbit,
          ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c C : OnePoint ℝ)) - 1) : ℕ) := by
  rw [eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree h,
    ramificationDegree_eq_interior_add_cusps h z hz c hc]
  push_cast
  ring

end TauCeti.Fuchsian

end
