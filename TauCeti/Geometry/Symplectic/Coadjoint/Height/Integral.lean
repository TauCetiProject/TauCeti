/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Perfect
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import TauCeti.Geometry.Manifold.Morse.CWModel
import TauCeti.Geometry.Manifold.Morse.IntegralHomology

/-!
# Integral homology and cohomology of coadjoint orbits of compact Lie groups

Let `G` be a compact Lie group, `ν ∈ 𝔤*` and `O = G ⧸ G_ν` its coadjoint orbit. Every Morse height
`f_X = ⟨μ, X⟩` on `O` has even Morse indices
(`Module.Dual.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply`), and `O` carries a
Morse height (`Module.Dual.exists_isMorse_orbitMap_coadjointRepresentation_apply`). A compact
manifold carrying a Morse function with only even indices has free integral homology, vanishing in
odd degrees (`TauCeti.IsMorse.free_singularHomology_int`,
`TauCeti.IsMorse.isZero_singularHomology_int_of_odd`), and the integral homology of any compact
manifold is finitely generated (`TauCeti.finite_singularHomology_int_of_isManifold`). So:

* the integral homology `Hⱼ(O; ℤ)` vanishes in odd degrees
  (`Module.Dual.isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd`);
* it is a free abelian group of finite rank in every degree
  (`Module.Dual.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation`,
  `Module.Dual.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation`).

Hence coadjoint orbits of compact Lie groups have no torsion in their integral homology, and their
integral homology is concentrated in even degrees. For instance this holds for the complex
projective spaces, the Grassmannians and the flag manifolds `G ⧸ T`.

Since the integral homology is free, hence projective, in every degree
(`Module.Dual.projective_singularHomology_int_quotient_stabilizer_coadjointRepresentation`), the
`Ext¹` terms of the universal coefficient sequence vanish, and the Kronecker map
`TopCat.singularKroneckerEquivOfProjectiveHomology` identifies the cohomology `Hʲ(O; ℤ, M)` with
`Hom(Hⱼ(O; ℤ), M)` for every abelian group `M`. So the same holds for cohomology, by
`TopCat.isZero_singularCohomology_of_projective_homology_lt`,
`TopCat.free_singularCohomology_of_projective_homology_lt` and
`TopCat.finite_singularCohomology_of_projective_homology_lt`:

* `Hʲ(O; ℤ, M)` vanishes in odd degrees, for every abelian group `M`
  (`Module.Dual.isZero_singularCohomology_int_quotient_stabilizer_coadjointRepresentation_of_odd`);
* it is free when `M` is free and finitely generated when `M` is, in every degree
  (`Module.Dual.free_singularCohomology_int_quotient_stabilizer_coadjointRepresentation`,
  `Module.Dual.finite_singularCohomology_int_quotient_stabilizer_coadjointRepresentation`).

In particular the integral cohomology `Hʲ(O; ℤ)` is free of finite rank and concentrated in even
degrees.

## Main results

* `Module.Dual.isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd`:
  the odd-degree integral homology of a coadjoint orbit of a compact Lie group vanishes.
* `Module.Dual.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation`: its integral
  homology is free in every degree.
* `Module.Dual.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation`: and
  finitely generated.
* `Module.Dual.projective_singularHomology_int_quotient_stabilizer_coadjointRepresentation`: so it
  is projective, which makes the universal coefficient theorem an isomorphism.
* `Module.Dual.isZero_singularCohomology_int_quotient_stabilizer_coadjointRepresentation_of_odd`,
  `Module.Dual.free_singularCohomology_int_quotient_stabilizer_coadjointRepresentation`,
  `Module.Dual.finite_singularCohomology_int_quotient_stabilizer_coadjointRepresentation`: the
  integral cohomology vanishes in odd degrees and is free and finitely generated.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, Theorem III (coadjoint orbits have no torsion and no odd-dimensional
  homology).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1, Theorem 3.2
  (the universal coefficient theorem).
-/

public section

open CategoryTheory Limits AlgebraicTopology Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

universe u

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type u} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [CompactSpace G]

namespace Module.Dual

variable (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-- **The integral homology of a coadjoint orbit is finitely generated.** For a coadjoint orbit `O`
of a compact Lie group, `Hⱼ(O; ℤ)` is a finitely generated abelian group in every degree. -/
theorem finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation (j : ℕ) :
    Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  exact finite_singularHomology_int_of_isManifold _
    𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν)) j

/-- **Odd integral homology of coadjoint orbits vanishes.** For a coadjoint orbit `O` of a compact
Lie group, `Hⱼ(O; ℤ) = 0` for every odd `j`. -/
theorem isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd {j : ℕ}
    (hj : Odd j) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  exact hX.isZero_singularHomology_int_of_odd
    (fun _ ↦ ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply) hj

/-- **The integral homology of a coadjoint orbit is free.** For a coadjoint orbit `O` of a compact
Lie group, `Hⱼ(O; ℤ)` is a free abelian group in every degree: it is zero in odd degrees, and in
even degrees it is finitely generated and torsion-free. -/
theorem free_singularHomology_int_quotient_stabilizer_coadjointRepresentation (j : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  exact hX.free_singularHomology_int
    (fun _ ↦ ν.even_manifoldMorseIndex_orbitMap_coadjointRepresentation_apply) j

/-- **The integral homology of a coadjoint orbit is projective.** For a coadjoint orbit `O` of a
compact Lie group, `Hⱼ(O; ℤ)` is a projective object of the category of abelian groups, being
free. This is the hypothesis of the universal coefficient isomorphism
`TopCat.singularKroneckerEquivOfProjectiveHomology`. -/
instance projective_singularHomology_int_quotient_stabilizer_coadjointRepresentation (j : ℕ) :
    CategoryTheory.Projective (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) :=
  have := ν.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  inferInstance

/-! ### Integral cohomology -/

section Cohomology

variable (M : Type u) [AddCommGroup M]

/-- **Odd cohomology of coadjoint orbits vanishes.** For a coadjoint orbit `O` of a compact Lie
group, `Hʲ(O; ℤ, M) = 0` for every odd `j` and every abelian group `M` of coefficients: by the
universal coefficient theorem it is `Hom(Hⱼ(O; ℤ), M)`, and `Hⱼ(O; ℤ) = 0`. -/
theorem isZero_singularCohomology_int_quotient_stabilizer_coadjointRepresentation_of_odd {j : ℕ}
    (hj : Odd j) :
    IsZero ((TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)).singularCohomology
      (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ (ModuleCat.of ℤ M) j) :=
  TopCat.isZero_singularCohomology_of_projective_homology_lt _ _ (fun _ _ ↦ inferInstance)
    (ν.isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd hj)

/-- **The integral cohomology of a coadjoint orbit is free.** For a coadjoint orbit `O` of a
compact Lie group and a free abelian group `M`, `Hʲ(O; ℤ, M)` is free in every degree: by the
universal coefficient theorem it is `Hom(Hⱼ(O; ℤ), M)`, with `Hⱼ(O; ℤ)` free of finite rank. -/
theorem free_singularCohomology_int_quotient_stabilizer_coadjointRepresentation [Module.Free ℤ M]
    (j : ℕ) :
    Module.Free ℤ (TopCat.singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ (ModuleCat.of ℤ M)
      (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) j) :=
  have := ν.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  have := ν.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  TopCat.free_singularCohomology_of_projective_homology_lt _ _ j fun _ _ ↦ inferInstance

/-- **The integral cohomology of a coadjoint orbit is finitely generated.** For a coadjoint orbit
`O` of a compact Lie group and a finitely generated abelian group `M`, `Hʲ(O; ℤ, M)` is finitely
generated in every degree: by the universal coefficient theorem it is `Hom(Hⱼ(O; ℤ), M)`, with
`Hⱼ(O; ℤ)` free of finite rank. -/
theorem finite_singularCohomology_int_quotient_stabilizer_coadjointRepresentation
    [Module.Finite ℤ M] (j : ℕ) :
    Module.Finite ℤ (TopCat.singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ (ModuleCat.of ℤ M)
      (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)) j) :=
  have := ν.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  have := ν.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  TopCat.finite_singularCohomology_of_projective_homology_lt _ _ j fun _ _ ↦ inferInstance

end Cohomology

end Module.Dual
