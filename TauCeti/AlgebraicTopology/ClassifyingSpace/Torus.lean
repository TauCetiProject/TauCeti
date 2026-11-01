/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
public import TauCeti.AlgebraicTopology.ClassifyingSpace.FirstHomology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.Singular.Torus.Exterior
public import TauCeti.AlgebraicTopology.Singular.Torus.FirstHomology
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane
public import TauCeti.Topology.CWComplex.Classical.Circle
public import TauCeti.Topology.CWComplex.Classical.Product
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

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

In every degree, the equivalence identifies the singular homology of the torus with coefficients
in a commutative ring `k` with the group homology of `ℤ^ι` with trivial coefficients `k`
(`TauCeti.torusSingularHomologyIsoGroupHomology`). The homology of the torus is the exterior
algebra on its first homology (`TauCeti.torusExteriorPowerEquiv`), so the same holds for the group
homology of `ℤ^ι`: `Hₙ(ℤ^ι, k) ≃ ⋀ⁿ H₁(ℤ^ι, k)`
(`TauCeti.groupHomologyPiMultiplicativeIntExteriorPowerEquiv`). In particular `Hₙ(ℤ^ι, k)` is a
free `k`-module of rank `(card ι choose n)`
(`TauCeti.free_groupHomology_pi_multiplicative_int`,
`TauCeti.finrank_groupHomology_pi_multiplicative_int`), and it vanishes above degree `card ι`
(`TauCeti.isZero_groupHomology_pi_multiplicative_int`).

The construction uses `IsAspherical.exists_homotopyEquiv_classifyingSpace`, the finite CW type
of circles and finite products, and the torus computations in
`TauCeti.AlgebraicTopology.UniversalCover.Torus`.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.B, Theorem 1B.8, and Theorem 2A.1; Section 3.C,
  the Pontryagin ring of a torus.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4, and Section V.6,
  the Pontryagin product and the homology of a free abelian group.
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
    classifyingSpaceFirstHomologyAddEquiv_homologyMap_hurewiczHomologyAddEquiv _
      (torusClassifyingSpaceBasepointPath p hp),
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

/-! ### Homology in every degree -/

section Homology

open MonoidalCategory Limits AlgebraicTopology

universe u

variable (k : Type u) [CommRing k] {ι : Type u} [Finite ι] (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)

/-- **The homology of a torus is the group homology of `ℤ^ι`.** For every commutative ring `k`, the
singular homology `Hₙ(Tⁱ; k)` of a finite torus of nonzero periods is Mathlib's group homology
`Hₙ(ℤ^ι, k)` of the trivial representation: the map induced by
`TauCeti.torusHomotopyEquivClassifyingSpace` followed by
`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`. -/
def torusSingularHomologyIsoGroupHomology (n : ℕ) :
    ((singularChains k).obj (TopCat.of (∀ i, AddCircle (p i)))).homology n ≅
      groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n :=
  (torusHomotopyEquivClassifyingSpace p hp).singularHomologyIso (ModuleCat.of k k) n ≪≫
    classifyingSpaceSingularHomologyIsoGroupHomology k (ι → Multiplicative ℤ) n

/-- The identification `TauCeti.torusSingularHomologyIsoGroupHomology` is the map induced on
homology by `TauCeti.torusHomotopyEquivClassifyingSpace`, followed by
`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`. -/
theorem torusSingularHomologyIsoGroupHomology_hom (n : ℕ) :
    (torusSingularHomologyIsoGroupHomology k p hp n).hom =
      HomologicalComplex.homologyMap ((singularChains k).map
          (TopCat.ofHom (torusHomotopyEquivClassifyingSpace p hp).toFun)) n ≫
        (classifyingSpaceSingularHomologyIsoGroupHomology k (ι → Multiplicative ℤ) n).hom :=
  -- `Iso.trans_hom` does not rewrite here: the two isomorphisms are composed along a
  -- definitional equality of `singularHomologyFunctor` with the homology of `singularChains`.
  congrArg (· ≫ (classifyingSpaceSingularHomologyIsoGroupHomology k (ι → Multiplicative ℤ) n).hom)
    ((torusHomotopyEquivClassifyingSpace p hp).singularHomologyIso_hom (ModuleCat.of k k) n)

variable (ι)

/-- **The homology of the torus `ι → S¹` is the group homology of `ℤ^ι`**, for the torus modelled
on Mathlib's unit circle as in `TauCeti.torusExteriorPowerEquiv`: the homeomorphism of each factor
with the circle `AddCircle 1` of period `1` (`AddCircle.homeomorphCircle`), followed by
`TauCeti.torusSingularHomologyIsoGroupHomology`. -/
def piCircleSingularHomologyIsoGroupHomology (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).obj
        (TopCat.of (ι → ULift.{u} Circle)) ≅
      groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n :=
  ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).mapIso
      (TopCat.isoOfHomeo (Homeomorph.piCongrRight fun _ : ι ↦
        (AddCircle.homeomorphCircle (one_ne_zero (α := ℝ))).trans
          Homeomorph.ulift.{u}.symm)).symm ≪≫
    torusSingularHomologyIsoGroupHomology k (fun _ : ι ↦ (1 : ℝ)) (fun _ ↦ one_ne_zero) n

/-- The identification `TauCeti.piCircleSingularHomologyIsoGroupHomology` is the map induced on
homology by the inverse of the factorwise homeomorphism with the circle of period `1`, followed by
`TauCeti.torusSingularHomologyIsoGroupHomology`. -/
theorem piCircleSingularHomologyIsoGroupHomology_hom (n : ℕ) :
    (piCircleSingularHomologyIsoGroupHomology k ι n).hom =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
          (TopCat.ofHom (Homeomorph.piCongrRight fun _ : ι ↦
            (AddCircle.homeomorphCircle (one_ne_zero (α := ℝ))).trans
              Homeomorph.ulift.{u}.symm).symm) ≫
        (torusSingularHomologyIsoGroupHomology k (fun _ : ι ↦ (1 : ℝ))
          (fun _ ↦ one_ne_zero) n).hom := by
  -- Unfold the unexposed definition; the composite then holds by `rfl`.
  rw [piCircleSingularHomologyIsoGroupHomology]
  rfl

/-- The inverse of `TauCeti.piCircleSingularHomologyIsoGroupHomology` is the inverse of
`TauCeti.torusSingularHomologyIsoGroupHomology`, followed by the map induced on homology by the
factorwise homeomorphism with the circle of period `1`. -/
theorem piCircleSingularHomologyIsoGroupHomology_inv (n : ℕ) :
    (piCircleSingularHomologyIsoGroupHomology k ι n).inv =
      (torusSingularHomologyIsoGroupHomology k (fun _ : ι ↦ (1 : ℝ))
          (fun _ ↦ one_ne_zero) n).inv ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map
          (TopCat.ofHom (Homeomorph.piCongrRight fun _ : ι ↦
            (AddCircle.homeomorphCircle (one_ne_zero (α := ℝ))).trans
              Homeomorph.ulift.{u}.symm)) := by
  -- Unfold the unexposed definition; the composite then holds by `rfl`.
  rw [piCircleSingularHomologyIsoGroupHomology]
  rfl

/-- **The group homology of `ℤ^ι` is the exterior algebra on its first homology.** For every
commutative ring `k` and finite `ι`, `⋀ⁿ H₁(ℤ^ι, k) ≃ Hₙ(ℤ^ι, k)` with trivial coefficients `k`.
Under the identification of group homology with the homology of a torus
(`TauCeti.piCircleSingularHomologyIsoGroupHomology`), it is the Pontryagin product of the torus
`TauCeti.torusExteriorPowerEquiv`, sending `a₁ ∧ ⋯ ∧ aₙ` to `a₁ ⋯ aₙ`
(`TauCeti.groupHomologyPiMultiplicativeIntExteriorPowerEquiv_ιMulti`). -/
def groupHomologyPiMultiplicativeIntExteriorPowerEquiv (n : ℕ) :
    ⋀[k]^n (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) 1) ≃ₗ[k]
      groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n :=
  let e := (piCircleSingularHomologyIsoGroupHomology k ι 1).toLinearEquiv.symm
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
      (exteriorPower.map_bijective e.bijective) ≪≫ₗ
    torusExteriorPowerEquiv k ι n ≪≫ₗ
    (piCircleSingularHomologyIsoGroupHomology k ι n).toLinearEquiv

/-- The equivalence `TauCeti.groupHomologyPiMultiplicativeIntExteriorPowerEquiv` sends
`a₁ ∧ ⋯ ∧ aₙ` to the class corresponding to the Pontryagin product, in the homology of the torus
`ι → S¹`, of the classes corresponding to the `aᵢ`. -/
@[simp]
theorem groupHomologyPiMultiplicativeIntExteriorPowerEquiv_ιMulti (n : ℕ)
    (v : Fin n → groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) 1) :
    groupHomologyPiMultiplicativeIntExteriorPowerEquiv k ι n (exteriorPower.ιMulti k n v) =
      (piCircleSingularHomologyIsoGroupHomology k ι n).hom.hom
        (TopCat.pontryaginMultilinear k (TopCat.of (ι → ULift.{u} Circle)) n
          ((piCircleSingularHomologyIsoGroupHomology k ι 1).inv.hom ∘ v)) := by
  simp [groupHomologyPiMultiplicativeIntExteriorPowerEquiv]

/-- **The group homology of `ℤ^ι` is free**: for every commutative ring `k` and finite `ι`,
`Hₙ(ℤ^ι, k)` with trivial coefficients `k` is a free `k`-module, since it is the homology of a
torus. -/
instance free_groupHomology_pi_multiplicative_int (n : ℕ) :
    Module.Free k (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n) :=
  .of_equiv (piCircleSingularHomologyIsoGroupHomology k ι n).toLinearEquiv

/-- For every commutative ring `k` and finite `ι`, `Hₙ(ℤ^ι, k)` with trivial coefficients `k` is a
finitely generated `k`-module, since it is the homology of a torus. -/
instance finite_groupHomology_pi_multiplicative_int (n : ℕ) :
    Module.Finite k (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · have := Module.subsingleton k (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n)
    infer_instance
  · exact .equiv (piCircleSingularHomologyIsoGroupHomology k ι n).toLinearEquiv

/-- **The rank of the group homology of `ℤ^ι`**: over a nontrivial commutative ring `k`,
`rank Hₙ(ℤ^ι, k) = (card ι choose n)` with trivial coefficients `k`, as for the homology of a
torus. -/
@[simp]
theorem finrank_groupHomology_pi_multiplicative_int [Nontrivial k] (n : ℕ) :
    Module.finrank k (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n) =
      (Nat.card ι).choose n := by
  rw [← (piCircleSingularHomologyIsoGroupHomology k ι n).toLinearEquiv.finrank_eq,
    finrank_singularHomology_pi_circle, ModuleCat.finrank_tensorUnit, mul_one]

variable {ι} in
/-- **The group homology of `ℤ^ι` vanishes above degree `card ι`**, with trivial coefficients in
any commutative ring `k`. -/
theorem isZero_groupHomology_pi_multiplicative_int {n : ℕ} (hn : Nat.card ι < n) :
    IsZero (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · have := Module.subsingleton k (groupHomology (Rep.trivial k (ι → Multiplicative ℤ) k) n)
    exact ModuleCat.isZero_of_subsingleton _
  · have := (Module.finrank_eq_zero_iff_of_free k _).mp
      ((finrank_groupHomology_pi_multiplicative_int k ι n).trans (Nat.choose_eq_zero_of_lt hn))
    exact ModuleCat.isZero_of_subsingleton _

end Homology

end TauCeti
