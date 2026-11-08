/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Cohomology
import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Aspherical

/-!
# The loop chain algebra of an aspherical space

For a pointed space `(B, b)`, the degree-zero truncation
`C_*(Ω_b B; R) → R[π₁(B, b)]` (`TauCeti.loopChainToGroupAlgebraDGAlgHom`) is a morphism of
differential graded algebras to the group ring with the zero differential. On cohomology it is a
left inverse of the inclusion `R[π₁(B, b)] → H(C_*(Ω_b B; R))` of zeroth homology
(`TauCeti.groupAlgebraToLoopChainCohomology`), which is therefore injective for every space.

When `B` is aspherical at `b`, that is, `π_(n + 2)(B, b)` vanishes for every `n`, each path
component of the Moore loop space is weakly contractible, so the cubical homology of `Ω_b B`
vanishes in positive degrees
(`TauCeti.MooreLoopSpace.isZero_homology_normalizedCubicalChainComplex_of_forall_subsingleton`).
Then the cohomology of `C_*(Ω_b B; R)` is the group ring, concentrated in degree zero
(`TauCeti.groupAlgebraLoopChainCohomologyAlgEquiv`), and the degree-zero truncation is a
quasi-isomorphism of differential graded algebras
(`TauCeti.bijective_cohomologyMap_loopChainToGroupAlgebraDGAlgHom`). So over an aspherical space,
the chain algebra over which DG local systems are modules is quasi-isomorphic to the group ring
of the fundamental group, over which classical local systems are modules. Path-connectedness of
`B` is not needed.

## Main results

* `TauCeti.cohomologyMap_loopChainToGroupAlgebraDGAlgHom_groupAlgebraToLoopChainCohomology`: the
  degree-zero truncation is a left inverse of the inclusion of zeroth homology, on cohomology.
* `TauCeti.groupAlgebraToLoopChainCohomology_injective`: the inclusion of zeroth homology is
  injective.
* `TauCeti.groupAlgebraToLoopChainCohomology_surjective`: for an aspherical space it is
  surjective.
* `TauCeti.groupAlgebraLoopChainCohomologyAlgEquiv`: for an aspherical space,
  `R[π₁(B, b)] ≃ₐ[R] H(C_*(Ω_b B; R))`.
* `TauCeti.bijective_cohomologyMap_loopChainToGroupAlgebraDGAlgHom`: for an aspherical space, the
  degree-zero truncation `C_*(Ω_b B; R) → R[π₁(B, b)]` is a quasi-isomorphism.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 4.21.
-/

public section

noncomputable section

open scoped Topology

universe u

namespace TauCeti

variable (B : Type u) [TopologicalSpace B] (b : B) (R : Type u) [CommRing R]

/-- **The degree-zero truncation inverts the inclusion of zeroth homology.** On cohomology,
`C_*(Ω_b B; R) → R[π₁(B, b)]` sends the class of a group-ring element, included as a class of
zero chains, back to that element. -/
@[simp]
theorem cohomologyMap_loopChainToGroupAlgebraDGAlgHom_groupAlgebraToLoopChainCohomology
    (a : MonoidAlgebra R (FundamentalGroup B b)) :
    (loopChainToGroupAlgebraDGAlgHom B b R).cohomologyMap
        (groupAlgebraToLoopChainCohomology B b R a) =
      algEquivCohomologyOfZero (trivialGrading R (MonoidAlgebra R (FundamentalGroup B b))) a := by
  obtain ⟨c, rfl⟩ := loopZeroChainToGroupAlgebra_surjective (R := R) (x := b) a
  rw [groupAlgebraToLoopChainCohomology_loopZeroChainToGroupAlgebra, DGAlgHom.cohomologyMap_mk,
    algEquivCohomologyOfZero_apply]
  congr 1
  ext
  simp [DGAlgHom.cyclesMap_apply_coe]

/-- The inclusion `R[π₁(B, b)] → H(C_*(Ω_b B; R))` of zeroth homology is injective, for every
space: the degree-zero truncation is a left inverse on cohomology. -/
theorem groupAlgebraToLoopChainCohomology_injective :
    Function.Injective (groupAlgebraToLoopChainCohomology B b R) := fun a a' h ↦ by
  have := congrArg (loopChainToGroupAlgebraDGAlgHom B b R).cohomologyMap h
  rw [cohomologyMap_loopChainToGroupAlgebraDGAlgHom_groupAlgebraToLoopChainCohomology,
    cohomologyMap_loopChainToGroupAlgebraDGAlgHom_groupAlgebraToLoopChainCohomology] at this
  exact (algEquivCohomologyOfZero _).injective this

variable {B b}

/-- Over an aspherical space, the class of a homogeneous cycle of the loop chain algebra is the
class of a zero chain: in dimension zero it is one, and in positive dimension the cycle is a
boundary, since the path components of the Moore loop space are weakly contractible. -/
private theorem quotientMk_mem_range_groupAlgebraToLoopChainCohomology
    (hB : ∀ n : ℕ, Subsingleton (π_ (n + 2) B b)) {i : ℤ} {z : loopChainAlgebra B b R}
    (hz : z ∈ cubicalChainGrading (MooreLoopSpace B b) R i)
    (hzc : z ∈ (loopChain_isDGAlgebra B b R).cycles) :
    Ideal.Quotient.mk (loopChain_isDGAlgebra B b R).boundaries.asIdeal ⟨z, hzc⟩ ∈
      (groupAlgebraToLoopChainCohomology B b R).range := by
  set h := loopChain_isDGAlgebra B b R
  rcases (mem_cubicalChainGrading_iff _ _).1 hz with rfl | ⟨n, y, -, rfl⟩
  · -- The zero cycle has the zero class.
    have h0 : (⟨0, hzc⟩ : h.cycles) = 0 := Subtype.ext (ZeroMemClass.coe_zero h.cycles).symm
    rw [h0, map_zero]
    exact zero_mem _
  cases n with
  | zero =>
    -- A cycle of dimension zero: its class is that of a zero chain.
    exact ⟨loopZeroChainToGroupAlgebra B b R y,
      groupAlgebraToLoopChainCohomology_loopZeroChainToGroupAlgebra B b R y⟩
  | succ k =>
    -- A cycle of positive dimension is a boundary.
    have hd := h.mem_cycles.1 hzc
    rw [cubicalChainDifferential_lof_succ] at hd
    have hdy : NormalizedCubicalChain.boundary (MooreLoopSpace B b) R k y = 0 := by
      simpa [DirectSum.lof_eq_of] using congrArg (fun w ↦ w k) hd
    obtain ⟨y', hy'⟩ :=
      NormalizedCubicalChain.exists_boundary_eq_of_forall_subsingleton_homotopyGroup
        (fun n γ ↦ (MooreLoopSpace.subsingleton_homotopyGroup_succ_iff γ n).2 (hB n)) hdy
    have hz' : (⟨cubicalChainLof (MooreLoopSpace B b) R (k + 1) y, hzc⟩ : h.cycles) =
        ⟨cubicalChainDifferential (MooreLoopSpace B b) R
          (cubicalChainLof (MooreLoopSpace B b) R (k + 2) y'), h.map_mem_cycles _⟩ :=
      Subtype.ext <| (congrArg _ hy'.symm).trans
        (cubicalChainDifferential_lof_succ _ _ (k + 1) y').symm
    rw [hz', h.quotientMk_map_eq_zero]
    exact zero_mem _

/-- **Over an aspherical space, the cohomology of the loop chain algebra is the group ring.** If
`π_(n + 2)(B, b)` vanishes for every `n`, every cohomology class of `C_*(Ω_b B; R)` is the class of
a zero chain. A homogeneous class of nonzero degree is represented by a positive-dimensional cycle
of the Moore loop space, which is a boundary since the path components of the Moore loop space are
weakly contractible. -/
theorem groupAlgebraToLoopChainCohomology_surjective
    (hB : ∀ n : ℕ, Subsingleton (π_ (n + 2) B b)) :
    Function.Surjective (groupAlgebraToLoopChainCohomology B b R) := by
  set h := loopChain_isDGAlgebra B b R
  intro x
  induction x using DirectSum.Decomposition.inductionOn h.cohomologyGrading with
  | zero => exact ⟨0, map_zero _⟩
  | add x x' hx hx' =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hx'
    exact ⟨a + a', map_add _ a a'⟩
  | homogeneous x =>
    obtain ⟨x, hx⟩ := x
    obtain ⟨z, hz, rfl⟩ := h.mem_cohomologyGrading.1 hx
    exact quotientMk_mem_range_groupAlgebraToLoopChainCohomology R hB hz z.2

/-- **The cohomology of the loop chain algebra of an aspherical space.** If `π_(n + 2)(B, b)`
vanishes for every `n`, the inclusion of zeroth homology is an isomorphism
`R[π₁(B, b)] ≃ₐ[R] H(C_*(Ω_b B; R))`: the cohomology is the group ring, concentrated in degree
zero. -/
def groupAlgebraLoopChainCohomologyAlgEquiv (hB : ∀ n : ℕ, Subsingleton (π_ (n + 2) B b)) :
    MonoidAlgebra R (FundamentalGroup B b) ≃ₐ[R] (loopChain_isDGAlgebra B b R).Cohomology :=
  AlgEquiv.ofBijective (groupAlgebraToLoopChainCohomology B b R)
    ⟨groupAlgebraToLoopChainCohomology_injective B b R,
      groupAlgebraToLoopChainCohomology_surjective R hB⟩

@[simp]
theorem groupAlgebraLoopChainCohomologyAlgEquiv_apply
    (hB : ∀ n : ℕ, Subsingleton (π_ (n + 2) B b)) (a : MonoidAlgebra R (FundamentalGroup B b)) :
    groupAlgebraLoopChainCohomologyAlgEquiv R hB a = groupAlgebraToLoopChainCohomology B b R a :=
  (rfl)

/-- **Over an aspherical space, the loop chain algebra is quasi-isomorphic to the group ring.** If
`π_(n + 2)(B, b)` vanishes for every `n`, the degree-zero truncation
`C_*(Ω_b B; R) → R[π₁(B, b)]` induces a bijection on cohomology. -/
theorem bijective_cohomologyMap_loopChainToGroupAlgebraDGAlgHom
    (hB : ∀ n : ℕ, Subsingleton (π_ (n + 2) B b)) :
    Function.Bijective (loopChainToGroupAlgebraDGAlgHom B b R).cohomologyMap := by
  have hcomp : ⇑(loopChainToGroupAlgebraDGAlgHom B b R).cohomologyMap ∘
      ⇑(groupAlgebraLoopChainCohomologyAlgEquiv R hB) =
        ⇑(algEquivCohomologyOfZero (trivialGrading R (MonoidAlgebra R (FundamentalGroup B b)))) :=
    funext (cohomologyMap_loopChainToGroupAlgebraDGAlgHom_groupAlgebraToLoopChainCohomology B b R)
  rw [← (Function.Bijective.of_comp_iff _
    (groupAlgebraLoopChainCohomologyAlgEquiv R hB).bijective), hcomp]
  exact (algEquivCohomologyOfZero _).bijective

end TauCeti
