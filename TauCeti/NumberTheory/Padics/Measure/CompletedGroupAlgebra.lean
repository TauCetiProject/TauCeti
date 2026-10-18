/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.FiniteAlgebra
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Measures on a compact group in its completed group algebra

For a compact topological group `Γ` and a topological commutative ring `R`, every open normal
subgroup `U` of `Γ` gives a finite discrete quotient `Γ ⧸ U`, and pushing a measure forward along
`Γ → Γ ⧸ U` gives its finite algebra projection in the group algebra `R[Γ ⧸ U]`. These projections
are compatible under the quotient maps `Γ ⧸ U → Γ ⧸ V` for `U ≤ V`, so they assemble, through the
universal property of the inverse limit, into an `R`-algebra homomorphism
`toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` from the convolution algebra of measures to the
completed group algebra. It sends the Dirac measure at `γ` to the group element `γ`.

The coefficients of the projection of `toCompletedGroupAlgebra μ` at level `U` are the measures of
the cosets of `U`, so integrating a function that factors through `Γ ⧸ U` is a finite sum against
them. When `Γ` is profinite such cylinder functions are dense, and hence the comparison map is
injective over every Hausdorff coefficient ring. For normed coefficients it is continuous from
the weak topology on measures to the inverse-limit topology on the completed group algebra.

## Main definitions

* `AbstractMeasure.toCompletedGroupAlgebra`: the `R`-algebra homomorphism
  `D(Γ, R) →ₐ[R] TauCeti.completedGroupAlgebra R Γ` whose projection to every level `R[Γ ⧸ U]` is
  the finite algebra projection along `Γ → Γ ⧸ U`.

## Main results

* `AbstractMeasure.toCompletedGroupAlgebra_dirac`: the Dirac measure at `γ` goes to `γ`.
* `AbstractMeasure.apply_eq_sum_coeff_proj_toCompletedGroupAlgebra`: integration of a function
  factoring through `Γ ⧸ U` is the finite sum of its values against the coefficients at level `U`.
* `AbstractMeasure.toCompletedGroupAlgebra_injective`: for profinite `Γ` and Hausdorff `R`, a
  measure is determined by its image in the completed group algebra.
* `AbstractMeasure.continuous_toCompletedGroupAlgebra`: for normed `R`, the comparison map is
  continuous for the weak topology on measures.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.3,
  Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap TauCeti

namespace AbstractMeasure

variable {Γ R : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

section TopologicalRing

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The finite algebra projections of a measure along the quotient maps `Γ → Γ ⧸ U` are
compatible: for `U ≤ V`, pushing the projection at `U` forward along `Γ ⧸ U → Γ ⧸ V` gives the
projection at `V`. -/
theorem mapDomain_finiteProjectionAlgHom_quotientMk {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V)
    (μ : D(Γ, R)) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV)
        (U.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom μ) =
      V.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom μ := by
  -- The quotient map at `V` is the quotient map at `U` followed by the transition map.
  have hq : (V.toSubgroup.quotientMkContinuousMonoidHom : C(Γ, Γ ⧸ V.toSubgroup)) =
      (⟨QuotientGroup.mapOfLE hUV, continuous_of_discreteTopology⟩ :
        C(Γ ⧸ U.toSubgroup, Γ ⧸ V.toSubgroup)).comp
        U.toSubgroup.quotientMkContinuousMonoidHom := by
    ext
    simp
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_mapDomain, ContinuousMonoidHom.finiteProjectionAlgHom_apply,
    ContinuousMonoidHom.finiteProjectionAlgHom_apply, MonoidAlgebra.coeff_ofCoeff,
    MonoidAlgebra.coeff_ofCoeff, hq, finiteProjection_comp]
  rfl

/-- **Measures in the completed group algebra.** The `R`-algebra homomorphism from measures on a
compact group `Γ` to its completed group algebra `R[[Γ]]` whose projection to every level
`R[Γ ⧸ U]` is the finite algebra projection along the quotient map `Γ → Γ ⧸ U`
(`proj_toCompletedGroupAlgebra`). -/
def toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ :=
  completedGroupAlgebra.lift R Γ
    (fun U ↦ U.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom)
    fun _ _ hUV μ ↦ mapDomain_finiteProjectionAlgHom_quotientMk hUV μ

/-- The projection of `toCompletedGroupAlgebra μ` to the level `R[Γ ⧸ U]` is the finite algebra
projection of `μ` along the quotient map. -/
@[simp]
theorem proj_toCompletedGroupAlgebra (U : OpenNormalSubgroup Γ) (μ : D(Γ, R)) :
    completedGroupAlgebra.proj R Γ U (toCompletedGroupAlgebra μ) =
      U.toSubgroup.quotientMkContinuousMonoidHom.finiteProjectionAlgHom μ :=
  completedGroupAlgebra.proj_lift ..

/-- The Dirac measure at `γ` goes to the group element `γ` of the completed group algebra. -/
@[simp]
theorem toCompletedGroupAlgebra_dirac (γ : Γ) :
    toCompletedGroupAlgebra (dirac R γ) = completedGroupAlgebra.of R Γ γ := by
  ext U
  simp

/-- Integrating a function that factors through `Γ ⧸ U` as `g` is the finite sum of the values
of `g` against the coefficients of the projection of `toCompletedGroupAlgebra μ` at level `U`,
which are the measures of the cosets of `U`. -/
theorem apply_eq_sum_coeff_proj_toCompletedGroupAlgebra {U : OpenNormalSubgroup Γ}
    [Fintype (Γ ⧸ U.toSubgroup)] (μ : D(Γ, R)) {F : C(Γ, R)} {g : Γ ⧸ U.toSubgroup → R}
    (hF : g ∘ (↑) = ⇑F) :
    μ F = ∑ a, g a * (completedGroupAlgebra.proj R Γ U (toCompletedGroupAlgebra μ)).coeff a := by
  have hF' : F = (equivFnOfDiscrete.symm g).comp U.toSubgroup.quotientMkContinuousMonoidHom := by
    ext x
    simp [← hF]
  rw [hF', apply_comp_eq_sum_finiteProjection]
  simp

/-- **Injectivity of the comparison.** Over a Hausdorff coefficient ring, a measure on a
profinite group is determined by its image in the completed group algebra. -/
theorem toCompletedGroupAlgebra_injective [T2Space R] [TotallyDisconnectedSpace Γ] :
    Function.Injective (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ) := by
  intro μ ν h
  -- The two measures agree on the dense set of functions factoring through a finite quotient.
  let := IsTopologicalAddGroup.rightUniformSpace R
  have hEqOn : Set.EqOn μ ν {F : C(Γ, R) |
      ∃ (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup → R), g ∘ (↑) = F} := by
    rintro F ⟨U, g, hF⟩
    let _ := Fintype.ofFinite (Γ ⧸ U.toSubgroup)
    rw [apply_eq_sum_coeff_proj_toCompletedGroupAlgebra μ hF,
      apply_eq_sum_coeff_proj_toCompletedGroupAlgebra ν hF, h]
  exact AbstractMeasure.ext fun F ↦ congrFun
    (Continuous.ext_on (dense_setOf_comp_quotientMk R) μ.continuous ν.continuous hEqOn) F

end TopologicalRing

section Normed

variable [NormedCommRing R]

/-- The comparison map is continuous from the weak topology on measures to the inverse-limit
topology on the completed group algebra: each coefficient of each projection is the measure of
a coset, which depends continuously on the measure. -/
theorem continuous_toCompletedGroupAlgebra :
    @Continuous _ _ (WeakTopology (X := Γ) (R := R) (E := R)) _
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ) := by
  let : TopologicalSpace D(Γ, R) := WeakTopology
  refine completedGroupAlgebra.continuous_iff.mpr fun U a ↦ ?_
  simp only [proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff]
  exact (continuous_apply a).comp (continuous_finiteProjection _)

end Normed

/-! The comparison on products of Dirac measures, and on distinct points of a profinite group. -/

example [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (x y : Γ)
    (U : OpenNormalSubgroup Γ) :
    completedGroupAlgebra.proj R Γ U (toCompletedGroupAlgebra (dirac R x * dirac R y)) =
      MonoidAlgebra.single ((x * y : Γ) : Γ ⧸ U.toSubgroup) 1 := by
  simp [dirac_mul_dirac]

example [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Nontrivial R]
    [TotallyDisconnectedSpace Γ] {x y : Γ} (hxy : x ≠ y) :
    toCompletedGroupAlgebra (dirac R x) ≠ toCompletedGroupAlgebra (dirac R y) := by
  simpa using (completedGroupAlgebra.of_injective R Γ).ne hxy

end AbstractMeasure
