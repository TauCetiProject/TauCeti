/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
public import TauCeti.AlgebraicTopology.ClassifyingSpace.FirstHomology
public import TauCeti.AlgebraicTopology.Singular.Torus.FirstHomology
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane
public import TauCeti.Topology.CWComplex.Classical.Circle
public import TauCeti.Topology.CWComplex.Classical.Product

/-!
# Finite tori and Milnor's classifying space

A finite product of additive circles of nonzero periods is homotopy equivalent to
`classifyingSpace (ι → Multiplicative ℤ)`. The equivalence realizes the winding-number
identification `AddCircle.piFundamentalGroupMulEquivZero`, so it compares the geometric torus
with Milnor's construction with the same choice of generators of the fundamental group.

The equivalence need not preserve the base point. A specified path from its value at zero to
the classifying-space base point supplies the required basepoint change. In degree one this
change is invisible to homology: the comparison sends the class of the straight loop with
winding vector `n` to the class of `n` in the abelianization. Consequently it agrees with the
existing computation `torusFirstHomologyEquiv` for every homology class. Composing with
`classifyingSpaceFirstHomologyAddEquivGroupHomology` identifies a straight loop with the
corresponding cycle in Mathlib's first group homology.

The construction uses `IsAspherical.exists_homotopyEquiv_classifyingSpace`, the finite CW type
of circles and finite products, and the torus computations in
`TauCeti.AlgebraicTopology.UniversalCover.Torus`.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.B, Theorem 1B.8, and Theorem 2A.1.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy ContinuousMap
open FundamentalGroup CategoryTheory TauCeti.HurewiczOne

namespace TauCeti

section Comparison

universe u

variable {ι : Type u} [Finite ι] (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)

private theorem exists_torusHomotopyEquivClassifyingSpace :
    ∃ (e : (∀ i, AddCircle (p i)) ≃ₕ classifyingSpace (ι → Multiplicative ℤ))
      (γ : Path (e.toFun 0) (classifyingSpaceBasepoint (ι → Multiplicative ℤ))),
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv (ι → Multiplicative ℤ)
        (fundamentalGroupMulEquivOfPath γ (map e.toFun 0 a)) =
          AddCircle.piFundamentalGroupMulEquivZero hp a := by
  let (i : ι) : NeZero (p i) := ⟨hp i⟩
  exact (AddCircle.isAspherical_pi p 0).exists_homotopyEquiv_classifyingSpace
    (AddCircle.piFundamentalGroupMulEquivZero hp)

/-- A finite torus of nonzero periods is homotopy equivalent to Milnor's classifying space of
its integer winding vectors. The equivalence induces the winding-number identification of
fundamental groups, after basepoint change along `torusClassifyingSpaceBasepointPath`. -/
def torusHomotopyEquivClassifyingSpace :
    (∀ i, AddCircle (p i)) ≃ₕ classifyingSpace (ι → Multiplicative ℤ) :=
  (exists_torusHomotopyEquivClassifyingSpace p hp).choose

/-- The path making `torusHomotopyEquivClassifyingSpace` compatible with the standard base
points and the winding-number identification of fundamental groups. -/
def torusClassifyingSpaceBasepointPath :
    Path ((torusHomotopyEquivClassifyingSpace p hp).toFun 0)
      (classifyingSpaceBasepoint (ι → Multiplicative ℤ)) :=
  (exists_torusHomotopyEquivClassifyingSpace p hp).choose_spec.choose

/-- The torus comparison induces the identity on integer winding vectors, using the existing
torus and classifying-space identifications of fundamental groups. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_map_torusHomotopyEquivClassifyingSpace
    (a : FundamentalGroup (∀ i, AddCircle (p i)) 0) :
    classifyingSpaceFundamentalGroupMulEquiv (ι → Multiplicative ℤ)
      (fundamentalGroupMulEquivOfPath (torusClassifyingSpaceBasepointPath p hp)
        (map (torusHomotopyEquivClassifyingSpace p hp).toFun 0 a)) =
      AddCircle.piFundamentalGroupMulEquivZero hp a :=
  (exists_torusHomotopyEquivClassifyingSpace p hp).choose_spec.choose_spec a

end Comparison

variable {ι : Type} [Finite ι] (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)

/-- On integral first homology, the comparison sends a straight torus loop to the
abelianization class of its winding vector. -/
-- Not a simp lemma: singularChainComplexFunctor_obj_map rewrites the chain map first.
theorem classifyingSpaceFirstHomologyAddEquiv_map_torusLoop (n : ι → ℤ) :
    classifyingSpaceFirstHomologyAddEquiv (ι → Multiplicative ℤ)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (torusHomotopyEquivClassifyingSpace p hp).toFun)) 1).hom
          (H₁AddEquivHomology _ (loopClass (torusLoop p n)))) =
      Additive.ofMul (Abelianization.of (fun i ↦ Multiplicative.ofAdd (n i))) := by
  rw [← hurewiczHomologyAddEquiv_ofMul_of_mk,
    homologyMap_hurewiczHomologyAddEquiv, toMul_ofMul, Abelianization.map_of]
  simp only [TopCat.hom_ofHom]
  rw [← hurewiczHomologyAddEquiv_fundamentalGroupMulEquivOfPath
      (torusClassifyingSpaceBasepointPath p hp),
    classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv,
    classifyingSpaceFundamentalGroupMulEquiv_map_torusHomotopyEquivClassifyingSpace,
    AddCircle.piFundamentalGroupMulEquivZero_torusLoop]

/-- The homology map of the torus comparison agrees with the existing winding-vector
calculation `torusFirstHomologyEquiv` on every integral first homology class. -/
theorem classifyingSpaceFirstHomologyAddEquiv_map_torusHomotopyEquivClassifyingSpace
    (x : ((singularChains ℤ).obj (TopCat.of (∀ i, AddCircle (p i)))).homology 1) :
    classifyingSpaceFirstHomologyAddEquiv (ι → Multiplicative ℤ)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (torusHomotopyEquivClassifyingSpace p hp).toFun)) 1).hom x) =
      Additive.ofMul (Abelianization.of
        (fun i ↦ Multiplicative.ofAdd (torusFirstHomologyEquiv p hp x i))) := by
  obtain ⟨n, rfl⟩ := (torusFirstHomologyEquiv p hp).symm.surjective x
  rw [torusFirstHomologyEquiv_symm_apply,
    classifyingSpaceFirstHomologyAddEquiv_map_torusLoop, torusFirstHomologyEquiv_loopClass]

/-- The topological comparison agrees with the algebraic first group homology calculation:
a straight torus loop of winding vector `n` maps to the class of the group-homology cycle
supported at `n` with coefficient one. -/
-- Not a simp lemma: singularChainComplexFunctor_obj_map rewrites the chain map first.
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_map_torusLoop (n : ι → ℤ) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology (ι → Multiplicative ℤ)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (torusHomotopyEquivClassifyingSpace p hp).toFun)) 1).hom
          (H₁AddEquivHomology _ (loopClass (torusLoop p n)))) =
      groupHomology.H1π (Rep.trivial ℤ (ι → Multiplicative ℤ) ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ (ι → Multiplicative ℤ) ℤ)).inv
          (Finsupp.single (fun i ↦ Multiplicative.ofAdd (n i)) 1)) := by
  rw [classifyingSpaceFirstHomologyAddEquivGroupHomology_apply,
    classifyingSpaceFirstHomologyAddEquiv_map_torusLoop]
  exact groupHomology.H1AddEquivOfIsTrivial_symm_tmul
    (A := Rep.trivial ℤ (ι → Multiplicative ℤ) ℤ) _ 1

end TauCeti
