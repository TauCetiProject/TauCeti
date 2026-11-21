/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.GradedAlgebra

/-!
# The Evens norm in degree zero and its normalization

For a compact open subgroup `U` of finite index `l` in a topological group `G`, the Evens norm
`N_U^G : H⁰(U, 𝔽₂) → H^{l · 0}(G, 𝔽₂)` sends the degree-zero class of `a ∈ 𝔽₂` to the
degree-zero class of `a`: the diagonal tensor `a ⊗ ⋯ ⊗ a` multiplies out to `a ^ l = a`. The
target degree `l · 0` is identified with `0` by `TauCeti.ContinuousCohomology.degreeCast`, as
in the other degree-transported identities of the norm.

In particular the norm satisfies the **normalization** `N_U^G 1 = 1`, where `1` is the unit of
the cup product (`TauCeti.cohomF2.one`). Together with multiplicativity
(`OpenSubgroup.evensNorm_cup`) it says that the norm preserves the unit and the product of the
mod-two cohomology ring, although it is not additive.

## Main results

* `OpenSubgroup.evensNorm_degreeZeroClass`: the norm of the degree-zero class of `a` is the
  degree-zero class of `a`.
* `OpenSubgroup.evensNorm_one`: the normalization `N_U^G 1 = 1`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 5 and 6.
-/

public section

namespace OpenSubgroup

open TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)]

/-- **The Evens norm of a degree-zero class.** The norm of the degree-zero class of `a ∈ 𝔽₂` on
`U` is the degree-zero class of the same element `a` on `G`, in degree `0 = l · 0`. -/
@[simp]
theorem evensNorm_degreeZeroClass (a : (trivialF2 U.toSubgroup).V)
    (ha : ∀ g, (trivialF2 U.toSubgroup).ρ g a = a) :
    U.evensNorm (ContinuousCohomology.degreeZeroClass (trivialF2 U.toSubgroup) a ha) =
      (ContinuousCohomology.degreeCast (trivialF2 G) (Nat.mul_zero _).symm).hom
        (ContinuousCohomology.degreeZeroClass (trivialF2 G)
          ((trivialF2Equiv G).symm (trivialF2Equiv U.toSubgroup a))
          (fun g ↦ trivialF2_ρ_apply_apply G g _)) := by
  obtain ⟨z, hz, hzx⟩ := TopRep.exists_cochainClass_eq
    (ContinuousCohomology.degreeZeroClass (trivialF2 U.toSubgroup) a ha)
  -- A homogeneous `0`-cocycle representing the class of `a` takes the value `a` at `1`.
  have h1 : z.1 1 = a := (ContinuousCohomology.degreeZeroClass_inj _ ha).1
    ((TopRep.cochainClass_eq_degreeZeroClass _ z hz (z.1 1)
      (fun g ↦ trivialF2_ρ_apply_apply _ g _) rfl).symm.trans hzx)
  rw [← hzx, evensNorm_cochainClass U default]
  -- The cocycle-level computation lands in degree `l · 0`; compare it with the transported class
  -- heterogeneously, so that no unfolding of `l · 0` to `0` is needed.
  refine eq_of_heq
    ((heq_of_eq (tensorNormCocycleClass_eq_degreeZeroClass U default z hz)).trans ?_)
  rw [h1]
  exact (ContinuousCohomology.degreeCast_hom_apply_heq _ _).symm

/-- **The normalization of the Evens norm**: `N_U^G 1 = 1`, where `1` is the unit class of the
cup product in degree zero, in degree `0 = l · 0`. -/
@[simp]
theorem evensNorm_one : U.evensNorm (1 : cohomF2 U.toSubgroup 0) =
    (ContinuousCohomology.degreeCast (trivialF2 G) (Nat.mul_zero _).symm).hom
      (1 : cohomF2 G 0) := by
  rw [← cohomF2.one_eq_one, ← cohomF2.one_eq_one, cohomF2.one_def, cohomF2.one_def,
    evensNorm_degreeZeroClass, AddEquiv.apply_symm_apply]

end OpenSubgroup
