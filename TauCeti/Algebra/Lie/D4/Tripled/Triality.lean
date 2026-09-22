/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.PointsFunctor
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry

/-!
# Triality on the tripled type-D4 carrier

The order-three symmetry of the Bourbaki-numbered `D₄` diagram, `TauCeti.trialityPermD4`, fixes
the central node and cycles the three outer nodes, and with them the three eight-dimensional
representations `V(ϖ₁)`, `V(ϖ₃)` and `V(ϖ₄)`. On the tripled weight table it is the symmetry
`TauCeti.D4Tripled.trialitySymmetry`, and on the rational tripled module the coordinate
permutation `TauCeti.MinusculeWeightTable.Symmetry.moduleEquiv` of that symmetry intertwines the
represented positive and negative simple-root generators. Every nonzero entry of a raising or
lowering matrix on the tripled weight basis is `1`, so no signs are needed: the lift permutes the
lattice basis with every scaling coefficient equal to one. This file descends that lift to the
tripled carrier through the numbered-symmetry construction on Kostant toral closures.

The resulting automorphism `TauCeti.D4Tripled.trialityAutomorphism` carries each numbered root
subgroup to the subgroup numbered by triality, without changing its additive parameter, and
carries the represented split torus to itself, relabelling its coordinates by the inverse of the
diagram permutation: `weightTorus ≫ γ.hom = relabel σ⁻¹ ≫ weightTorus`, a distinction that
matters for a permutation of order three. It has order dividing three. On matrix-valued points it
is conjugation by the permutation matrix of `TauCeti.DynkinType.d4TripledTrialityPerm`, and that
matrix is compatible with every change of value ring.

No reductivity, maximality of the represented torus, or identification of the carrier with the
pinned simply connected group scheme of type `D₄` is asserted here.

## Main declarations

* `TauCeti.D4Tripled.trialityAutomorphism`: the triality automorphism of the tripled carrier.
* `TauCeti.D4Tripled.rootSubgroup_comp_trialityAutomorphism_hom`: its action on the numbered
  simple-root subgroups, `γ ∘ x_k = x_{σ k}`.
* `TauCeti.D4Tripled.weightTorus_comp_trialityAutomorphism_hom`: its action on the split weight
  torus.
* `TauCeti.D4Tripled.trialityAutomorphism_pow_three`,
  `TauCeti.D4Tripled.trialityAutomorphism_hom_comp_self_comp_self` and
  `TauCeti.D4Tripled.trialityAutomorphism_inv`: its order-three relation on the carrier.
* `TauCeti.D4Tripled.trialityMatrix`: the permutation matrix inducing triality on points, with
  `TauCeti.D4Tripled.map_trialityMatrix` its compatibility with ring homomorphisms.
* `TauCeti.D4Tripled.trialityPoints`: the same automorphism on matrix-valued points.
* `TauCeti.D4Tripled.trialityPoints_rootSubgroupPoints` and
  `TauCeti.D4Tripled.trialityPoints_weightTorusPoints`: its pointwise equations on the numbered
  simple-root subgroups and the represented weight torus.
* `TauCeti.D4Tripled.schemePointsMulEquiv_trialityAutomorphism_comp_carrierι`: the action on
  scheme-valued points is conjugation by `trialityMatrix`.
* `TauCeti.D4Tripled.trialityPoints_pow_three` and `TauCeti.D4Tripled.trialityPoints_symm_apply`:
  its pointwise order-three relation.
* `TauCeti.D4Tripled.pointsMap_comp_trialityPoints`: its naturality in the value ring, and so its
  commutation with every Frobenius map.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* The construction follows the formal template of
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.GraphAutomorphism`, with the signed involution there
  replaced by an unsigned permutation of order three.
* K. Morrison and Claude Code,
  [Tau Ceti PR #6671](https://github.com/TauCetiProject/TauCeti/pull/6671), whose scheme-level
  automorphism, point action, and order-three proofs are adapted here to the current generic
  symmetry API.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra

universe v v'

attribute [local instance high] Algebra.toModule

/-! ## The inputs of the numbered-symmetry construction -/

/-- The coordinate permutation of triality preserves the tripled lattice, in the form consumed by
the numbered-symmetry construction. -/
private theorem trialityModuleEquiv_mem_lattice_iff (v : Fin 24 → ℚ) :
    trialitySymmetry.moduleEquiv v ∈ lattice.toAddSubgroup ↔ v ∈ lattice.toAddSubgroup := by
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, lattice_def]
  exact trialitySymmetry.moduleEquiv_mem_coordinateLattice_iff v

/-- The coordinate permutation of triality intertwines the represented numbered root generators of
the tripled module along the induced root permutation. -/
private theorem trialityModuleEquiv_rep_ι_serreRootGenerator (k : Fin 4 ⊕ Fin 4)
    (v : Fin 24 → ℚ) :
    trialitySymmetry.moduleEquiv
        (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator weightTable.cartanMatrix k)) v) =
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator weightTable.cartanMatrix (trialitySymmetry.rootPerm k)))
        (trialitySymmetry.moduleEquiv v) := by
  rw [rep_def]
  exact trialitySymmetry.moduleEquiv_rep_ι_serreRootGenerator k v

/-- The coordinate permutation of triality permutes the tripled lattice basis along
`d4TripledTrialityPerm`, with every scaling coefficient equal to one. -/
private theorem trialityModuleEquiv_latticeBasis (a : Fin 24) :
    trialitySymmetry.moduleEquiv ((latticeBasis a : lattice) : Fin 24 → ℚ) =
      ((((1 : ℤ) • latticeBasis (d4TripledTrialityPerm a) : lattice)) : Fin 24 → ℚ) := by
  rw [one_smul, coe_latticeBasis, coe_latticeBasis,
    MinusculeWeightTable.Symmetry.moduleEquiv_single, trialitySymmetry_indexPerm]

/-! ## The triality automorphism of the carrier -/

private noncomputable def toralTrialityAutomorphism :
    Aut (kostantToralGroupScheme
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
      d4TripledWeight) :=
  kostantToralNumberedSymmetryIso
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
    trialitySymmetry.rootPerm trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff
    trialityModuleEquiv_rep_ι_serreRootGenerator trialitySymmetry.rootPerm.surjective
    d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis trialityPermD4
    d4TripledWeight_d4TripledTrialityPerm_apply

/-- **The triality automorphism of the tripled type-`D₄` carrier**, characterized on the numbered
simple-root subgroups by `rootSubgroup_comp_trialityAutomorphism_hom` and on the represented
weight torus by `weightTorus_comp_trialityAutomorphism_hom`. -/
noncomputable def trialityAutomorphism : Aut groupScheme :=
  toralTrialityAutomorphism

/-- The triality automorphism renumbers each positive and negative numbered simple-root subgroup
by triality, without changing its additive parameter: `γ ∘ x_k = x_{σ k}`. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_trialityAutomorphism_hom (k : Fin 4 ⊕ Fin 4) :
    rootSubgroup k ≫ trialityAutomorphism.hom = rootSubgroup (trialitySymmetry.rootPerm k) := by
  rw [rootSubgroup_def, trialityAutomorphism, toralTrialityAutomorphism,
    kostantRootSubgroupToToral_comp_numberedSymmetryIso_hom]
  exact (rootSubgroup_def (trialitySymmetry.rootPerm k)).symm

/-- The triality automorphism relabels the represented split weight torus by the inverse of the
diagram permutation. -/
@[reassoc (attr := simp)]
theorem weightTorus_comp_trialityAutomorphism_hom :
    weightTorus ≫ trialityAutomorphism.hom =
      SplitTorus.relabel ℤ trialityPermD4⁻¹ ≫ weightTorus := by
  rw [weightTorus_def, trialityAutomorphism, toralTrialityAutomorphism,
    kostantWeightTorusToToral_comp_numberedSymmetryIso_hom]

/-- **The triality automorphism has order dividing three.** -/
@[simp]
theorem trialityAutomorphism_pow_three : trialityAutomorphism ^ 3 = 1 := by
  rw [trialityAutomorphism, toralTrialityAutomorphism]
  apply kostantToralNumberedSymmetryIso_pow_eq_one
  · rw [← Equiv.Perm.coe_pow, ← MinusculeWeightTable.Symmetry.rootPerm_pow,
      trialitySymmetry_pow_three, MinusculeWeightTable.Symmetry.rootPerm_one,
      Equiv.Perm.coe_one]
  · exact trialityPermD4_pow_three

/-- Applying the triality automorphism three times is the identity on the tripled carrier. -/
@[reassoc (attr := simp)]
theorem trialityAutomorphism_hom_comp_self_comp_self :
    trialityAutomorphism.hom ≫ trialityAutomorphism.hom ≫ trialityAutomorphism.hom =
      𝟙 groupScheme := by
  calc
    trialityAutomorphism.hom ≫ trialityAutomorphism.hom ≫ trialityAutomorphism.hom =
        trialityAutomorphism.hom ≫ (trialityAutomorphism.trans trialityAutomorphism).hom :=
      congrArg (trialityAutomorphism.hom ≫ ·) (Iso.trans_hom _ _).symm
    _ = (trialityAutomorphism.trans (trialityAutomorphism.trans trialityAutomorphism)).hom :=
      (Iso.trans_hom _ _).symm
    _ = (trialityAutomorphism * trialityAutomorphism * trialityAutomorphism).hom := by
      rw [Aut.Aut_mul_def, Aut.Aut_mul_def]
    _ = (trialityAutomorphism ^ 3).hom := by rw [pow_three']
    _ = (1 : Aut groupScheme).hom := by rw [trialityAutomorphism_pow_three]
    _ = 𝟙 groupScheme := Iso.refl_hom groupScheme

/-- The inverse leg of the triality automorphism is the square of its forward leg. -/
@[simp]
theorem trialityAutomorphism_inv :
    trialityAutomorphism.inv = trialityAutomorphism.hom ≫ trialityAutomorphism.hom :=
  ((Iso.hom_comp_eq_id trialityAutomorphism).mp
    trialityAutomorphism_hom_comp_self_comp_self).symm

/-! ## Triality on matrix-valued points -/

/-- The permutation matrix inducing triality on matrix-valued points. -/
noncomputable def trialityMatrix (A : Type v) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin 24) A :=
  kostantNumberedSymmetryMatrix lattice.toAddSubgroup latticeBasis trialitySymmetry.moduleEquiv
    trialityModuleEquiv_mem_lattice_iff A

/-- The triality matrix is the permutation matrix of `d4TripledTrialityPerm`. -/
@[simp]
theorem coe_trialityMatrix_apply (A : Type v) [CommRing A] (i j : Fin 24) :
    (trialityMatrix A : Matrix (Fin 24) (Fin 24) A) i j =
      if i = d4TripledTrialityPerm j then 1 else 0 := by
  rw [trialityMatrix, coe_kostantNumberedSymmetryMatrix_apply_of_monomial lattice.toAddSubgroup
    latticeBasis trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff
    d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis A i j, map_one]

/-- The triality matrix is compatible with every ring homomorphism of value rings. -/
@[simp]
theorem map_trialityMatrix {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f (trialityMatrix A) = trialityMatrix B :=
  map_kostantNumberedSymmetryMatrix lattice.toAddSubgroup latticeBasis
    trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff f

/-- The triality matrix has order dividing three over every commutative ring. -/
@[simp]
theorem trialityMatrix_pow_three (A : Type v) [CommRing A] : trialityMatrix A ^ 3 = 1 := by
  rw [trialityMatrix]
  apply kostantNumberedSymmetryMatrix_pow_eq_one
  intro x
  rw [← MinusculeWeightTable.Symmetry.moduleEquiv_pow, trialitySymmetry_pow_three,
    MinusculeWeightTable.Symmetry.moduleEquiv_one, LinearEquiv.coe_one, id_eq]

/-- Conjugation by the triality matrix preserves the tripled carrier's point subgroup. -/
private theorem map_points_conj_trialityMatrix (A : Type v) [CommRing A] :
    (points A).map (MulAut.conj (trialityMatrix A)).toMonoidHom = points A := by
  rw [points_def, definingIdeal_def, trialityMatrix]
  simpa only [kostantToralPointsSubgroup_def] using
    map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
    trialitySymmetry.rootPerm trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff
    trialityModuleEquiv_rep_ι_serreRootGenerator trialitySymmetry.rootPerm.surjective
    d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis trialityPermD4
    d4TripledWeight_d4TripledTrialityPerm_apply A

/-- **Triality on matrix-valued points of the tripled carrier**, given by conjugation by the
triality permutation matrix. -/
noncomputable def trialityPoints (A : Type v) [CommRing A] : MulAut (points A) :=
  kostantNumberedSymmetryPoints lattice.toAddSubgroup latticeBasis trialitySymmetry.moduleEquiv
    trialityModuleEquiv_mem_lattice_iff A (points A) (map_points_conj_trialityMatrix A)

/-- On matrices, triality on points is conjugation by the triality matrix. -/
@[simp]
theorem coe_trialityPoints (A : Type v) [CommRing A] (g : points A) :
    (trialityPoints A g : Matrix.GeneralLinearGroup (Fin 24) A) =
      trialityMatrix A * g * (trialityMatrix A)⁻¹ :=
  coe_kostantNumberedSymmetryPoints lattice.toAddSubgroup latticeBasis
    trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff A (points A)
    (map_points_conj_trialityMatrix A) g

/-- On matrices, the inverse of triality on points is conjugation by the inverse of the triality
matrix. -/
theorem coe_trialityPoints_symm (A : Type v) [CommRing A] (g : points A) :
    ((trialityPoints A).symm g : Matrix.GeneralLinearGroup (Fin 24) A) =
      (trialityMatrix A)⁻¹ * g * trialityMatrix A :=
  coe_kostantNumberedSymmetryPoints_symm lattice.toAddSubgroup latticeBasis
    trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff A (points A)
    (map_points_conj_trialityMatrix A) g

/-- **Triality on points renumbers every numbered positive and negative simple-root subgroup
without changing its additive parameter**: `γ (x_k(u)) = x_{σ k}(u)`. -/
@[simp]
theorem trialityPoints_rootSubgroupPoints (A : Type v) [CommRing A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    trialityPoints A (rootSubgroupPoints k A u) =
      rootSubgroupPoints (trialitySymmetry.rootPerm k) A u := by
  apply Subtype.ext
  rw [coe_trialityPoints, coe_rootSubgroupPoints, coe_rootSubgroupPoints, trialityMatrix]
  exact kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    trialitySymmetry.rootPerm trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff
    trialityModuleEquiv_rep_ι_serreRootGenerator A k _

/-- Triality on points relabels the coordinates of a represented split-torus point by the inverse
of the diagram permutation. -/
@[simp]
theorem trialityPoints_weightTorusPoints (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) :
    trialityPoints A (weightTorusPoints A s) =
      weightTorusPoints A (fun k => s (trialityPermD4.symm k)) := by
  have hpt : ∀ i,
      torusCharacter s (d4TripledWeight (d4TripledTrialityPerm⁻¹ i)) =
        torusCharacter (fun k => s (trialityPermD4.symm k)) (d4TripledWeight i) := by
    intro i
    have hwt :
        d4TripledWeight (d4TripledTrialityPerm⁻¹ i) = d4TripledWeight i ∘ trialityPermD4 := by
      funext k
      have h := d4TripledWeight_d4TripledTrialityPerm_apply (d4TripledTrialityPerm⁻¹ i) k
      rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h
    rw [hwt, ← torusCharacter_mulEquivArrowCongr trialityPermD4 s (d4TripledWeight i)]
    exact congrArg (fun z => torusCharacter z (d4TripledWeight i))
      (funext fun k => by rw [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply])
  have hconj := kostantNumberedSymmetryMatrix_conj_diagGL
    lattice.toAddSubgroup latticeBasis trialitySymmetry.moduleEquiv
    trialityModuleEquiv_mem_lattice_iff d4TripledTrialityPerm (fun _ => 1)
    trialityModuleEquiv_latticeBasis A (fun i => torusCharacter s (d4TripledWeight i))
  apply Subtype.ext
  rw [coe_trialityPoints, coe_weightTorusPoints, coe_weightTorusPoints, trialityMatrix]
  simpa only [kostantTorusMatrix_apply] using hconj.trans (congrArg diagGL (funext hpt))

/-- **Triality on matrix-valued points is the map induced by the carrier automorphism.** After
inclusion into `GL₂₄`, composing a scheme-valued point with `trialityAutomorphism` is conjugation
by `trialityMatrix`. -/
theorem schemePointsMulEquiv_trialityAutomorphism_comp_carrierι
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ groupScheme.X) :
    GeneralLinear.schemePointsMulEquiv 24 A
        (p ≫ (trialityAutomorphism.hom ≫ carrierι).hom.hom) =
      trialityMatrix A *
          GeneralLinear.schemePointsMulEquiv 24 A (p ≫ carrierι.hom.hom) *
        (trialityMatrix A)⁻¹ := by
  rw [trialityAutomorphism, carrierι_def, trialityMatrix]
  simpa only [toralTrialityAutomorphism, Grp.comp_hom_hom, Category.assoc] using
    schemePointsMulEquiv_kostantToralNumberedSymmetryIso
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
      trialitySymmetry.rootPerm trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff
      trialityModuleEquiv_rep_ι_serreRootGenerator trialitySymmetry.rootPerm.surjective
      d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis trialityPermD4
      d4TripledWeight_d4TripledTrialityPerm_apply A p

/-- **Triality on matrix-valued points is natural in the value ring**: it commutes with the map on
points induced by any ring homomorphism, in particular with every Frobenius map of the carrier. -/
theorem pointsMap_comp_trialityPoints {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (pointsMap f).comp (trialityPoints A).toMonoidHom =
      (trialityPoints B).toMonoidHom.comp (pointsMap f) :=
  comp_kostantNumberedSymmetryPoints lattice.toAddSubgroup latticeBasis
    trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff
    (points A) (map_points_conj_trialityMatrix A) (points B) (map_points_conj_trialityMatrix B) f
    (pointsMap f) (coe_pointsMap f)

/-- **Triality on matrix-valued points has order dividing three.** -/
@[simp]
theorem trialityPoints_pow_three (A : Type v) [CommRing A] : trialityPoints A ^ 3 = 1 :=
  kostantNumberedSymmetryPoints_pow_eq_one lattice.toAddSubgroup latticeBasis
    trialitySymmetry.moduleEquiv trialityModuleEquiv_mem_lattice_iff A (points A)
    (map_points_conj_trialityMatrix A) (trialityMatrix_pow_three A)

/-- Applying triality three times to a matrix-valued point is the identity. -/
@[simp]
theorem trialityPoints_trialityPoints_trialityPoints (A : Type v) [CommRing A] (g : points A) :
    trialityPoints A (trialityPoints A (trialityPoints A g)) = g := by
  have h := congrArg (fun σ : MulAut (points A) => σ g) (trialityPoints_pow_three A)
  simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h

/-- **The inverse of triality on matrix-valued points is the square of triality**, its order
dividing three. -/
@[simp]
theorem trialityPoints_symm_apply (A : Type v) [CommRing A] (g : points A) :
    (trialityPoints A).symm g = trialityPoints A (trialityPoints A g) := by
  apply (trialityPoints A).injective
  rw [MulEquiv.apply_symm_apply, trialityPoints_trialityPoints_trialityPoints]

end TauCeti.D4Tripled
