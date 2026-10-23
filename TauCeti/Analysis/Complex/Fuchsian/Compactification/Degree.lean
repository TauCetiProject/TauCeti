/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.InteriorDegree
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cusp.LocalMultiplicity
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# The degree of a finite-index map of compactified Fuchsian quotients

For a finite-index inclusion `Δ ≤ Γ` of discrete subgroups of `PSL(2, ℝ)`, every fibre of the
induced map of compactified quotients has `[Γ : Δ]` points counted with local multiplicity.
Over an interior point this is
`Subgroup.sum_localMultiplicity_compactifiedQuotientMap_fiber_ofQuotient`.
Over an adjoined cusp, the cosets of `Δ` in `Γ` are partitioned by the cusp orbits of `Δ` they
translate the cusp into; the part belonging to the orbit of `c` has
`[stabilizer Γ c : stabilizer Δ c]` elements, which is the local multiplicity there, the ratio
of cusp widths. Consequently the degree of the map, the supremum of its fibre sums, is the index.
No compactness of the quotients is needed.

The computation follows the degree and ramification count for the projection `X(Γ) → X(1)` in
Diamond and Shurman, *A First Course in Modular Forms*, §3.1.

## Main statements

* `Subgroup.sum_localMultiplicity_compactifiedQuotientMap_fiber_ofCusp`: local multiplicities over
  an adjoined cusp sum to the index.
* `Subgroup.fiberMultiplicitySum_compactifiedQuotientMap`: every fibre sum is the index.
* `Subgroup.degree_compactifiedQuotientMap`: the degree is the index.
-/

public noncomputable section

open MulAction TauCeti.RiemannSurface
open Subgroup.CompactifiedQuotient
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

private theorem sum_localMultiplicity_compactifiedQuotientMap_fiber_cuspOrbitMk
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (c : Γ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∑ᶠ y : {y : Δ.CompactifiedQuotient //
        compactifiedQuotientMap h y = .ofCusp (Γ.cuspOrbitMk c)},
      localMultiplicity (compactifiedQuotientMap h) y.1 =
        (Δ.subgroupOf Γ).index := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let Q := Γ ⧸ Δ.subgroupOf Γ
  let F := {y : Δ.CompactifiedQuotient //
    compactifiedQuotientMap h y = .ofCusp (Γ.cuspOrbitMk c)}
  -- a coset `gΔ` gives the adjoined cusp of the `Δ`-orbit of `g⁻¹ • c`
  let φ : Q → F := fun r =>
    cuspOrbitFiberEquivCompactifiedFiber h _ ((cuspOrbitFiberEquivBoundaryOrbitFiber h _).symm
      ⟨(TauCeti.cosetToOrbitRelMapFiber h (c : OnePoint ℝ) r).1,
        (TauCeti.cosetToOrbitRelMapFiber h (c : OnePoint ℝ) r).2.trans
          (cuspOrbitMk_val c).symm⟩)
  have hφ_eq_iff (r s : Q) :
      φ r = φ s ↔ TauCeti.orbitOfCosetTranslate (c : OnePoint ℝ) r =
        TauCeti.orbitOfCosetTranslate (𝒢 := Δ) (c : OnePoint ℝ) s := by
    simp only [φ, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq,
      TauCeti.cosetToOrbitRelMapFiber_apply]
  have hφ_mk (g : Γ) : (φ (g : Q)).1 = ofCusp (Δ.cuspOrbitMk ⟨g⁻¹ • (c : OnePoint ℝ),
      mem_cuspPoints.mpr (IsCuspPoint.of_isFiniteRelIndex
        ((mem_cuspPoints.mp c.2).smul g⁻¹))⟩) := by
    simp only [φ, cuspOrbitFiberEquivCompactifiedFiber_apply]
    congr 1
    apply Subtype.ext
    rw [← cuspOrbitFiberEquivBoundaryOrbitFiber_apply, Equiv.apply_symm_apply]
    simp [Subgroup.smul_def]
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨D, rfl⟩ := (cuspOrbitFiberEquivCompactifiedFiber h _).surjective y
    obtain ⟨q, rfl⟩ := (cuspOrbitFiberEquivBoundaryOrbitFiber h _).symm.surjective D
    obtain ⟨r, hr⟩ := TauCeti.cosetToOrbitRelMapFiber_surjective h (c : OnePoint ℝ)
      ⟨q.1, q.2.trans (cuspOrbitMk_val c)⟩
    refine ⟨r, ?_⟩
    simp only [φ, hr]
  have : Finite F := finite_fiber_compactifiedQuotientMap h _
  let : Fintype F := Fintype.ofFinite F
  -- each point of the fibre is the image of as many cosets as its local multiplicity
  have hweight (y : F) : Nat.card {r : Q // φ r = y} =
      localMultiplicity (compactifiedQuotientMap h) y.1 := by
    obtain ⟨r, rfl⟩ := hφ_surj y
    induction r using QuotientGroup.induction_on with
    | H g =>
      rw [hφ_mk, localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk,
        ← TauCeti.card_fiber_orbitOfCosetTranslate_eq_relIndex h]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun s => hφ_eq_iff s _)
  -- the cosets are the disjoint union of the fibres of `φ`
  rw [finsum_eq_sum_of_fintype, Subgroup.index_eq_card,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv φ), Nat.card_sigma]
  exact Finset.sum_congr rfl fun y _ => (hweight y).symm

/-- The sum of local multiplicities over the fibre above an adjoined cusp of a finite-index
quotient map is its subgroup index. The fibre consists of the cusp orbits of the smaller group
above the cusp, each counted with its cusp width ratio. -/
theorem sum_localMultiplicity_compactifiedQuotientMap_fiber_ofCusp
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (C : Γ.CuspOrbit) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ∑ᶠ y : {y : Δ.CompactifiedQuotient // compactifiedQuotientMap h y = .ofCusp C},
      localMultiplicity (compactifiedQuotientMap h) y.1 =
        (Δ.subgroupOf Γ).index := by
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  exact sum_localMultiplicity_compactifiedQuotientMap_fiber_cuspOrbitMk h c

/-- Every fibre of a finite-index map of compactified Fuchsian quotients has as many points,
counted with local multiplicity, as the index of the subgroup. -/
@[simp]
theorem fiberMultiplicitySum_compactifiedQuotientMap
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (y : Γ.CompactifiedQuotient) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    fiberMultiplicitySum (compactifiedQuotientMap h) y = (Δ.subgroupOf Γ).index := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  simp only [fiberMultiplicitySum_def, Set.mem_preimage, Set.mem_singleton_iff]
  rw [← finsum_subtype_eq_finsum_cond]
  cases y with
  | ofQuotient p => exact sum_localMultiplicity_compactifiedQuotientMap_fiber_ofQuotient h p
  | ofCusp C => exact sum_localMultiplicity_compactifiedQuotientMap_fiber_ofCusp h C

/-- **The degree of a finite-index map of compactified Fuchsian quotients is the index.** For
`Δ ≤ Γ` discrete of finite index, the map `X(Δ) → X(Γ)` induced by the inclusion has degree
`[Γ : Δ]`. -/
@[simp]
theorem degree_compactifiedQuotientMap
    [DiscreteTopology Γ] (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    degree (compactifiedQuotientMap h) = (Δ.subgroupOf Γ).index := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have : Nonempty Γ.CompactifiedQuotient := ⟨.ofQuotient (Quotient.mk'' UpperHalfPlane.I)⟩
  simp only [degree_def, fiberMultiplicitySum_compactifiedQuotientMap, ciSup_const]

end Subgroup
