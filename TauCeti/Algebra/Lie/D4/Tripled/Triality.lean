/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Frobenius
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry

/-!
# Triality on the tripled type-D4 carrier

The order-three symmetry of the Bourbaki-numbered `D₄` diagram, `TauCeti.trialityPermD4`, fixes
the central node and cycles the three outer nodes, and with them the three eight-dimensional
representations `V(ϖ₁)`, `V(ϖ₃)` and `V(ϖ₄)`. On their direct sum it has a monomial lift which
permutes the twenty-four weight-basis vectors and intertwines the represented positive and
negative simple-root generators. Every nonzero entry of a raising or lowering matrix on the
tripled weight basis is `1`, so the lift needs no signs: it is the permutation matrix of
`TauCeti.DynkinType.d4TripledTrialityPerm`. This file constructs that lift and descends it to
the tripled carrier.

The resulting automorphism `TauCeti.D4Tripled.trialityAutomorphism` carries each numbered root
subgroup to the subgroup numbered by triality, without changing its additive parameter, and
carries the represented split torus to itself, relabelling its coordinates by the inverse of the
diagram permutation: `weightTorus ≫ γ.hom = relabel σ⁻¹ ≫ weightTorus`, a distinction that
matters for a permutation of order three. It has order dividing three.
On matrix-valued points it is conjugation by the permutation matrix, it is natural in the value
ring, and in particular it commutes with the Frobenius of the carrier.

No reductivity, maximality of the represented torus, or identification of the carrier with the
pinned simply connected group scheme of type `D₄` is asserted here.

## Main declarations

* `TauCeti.D4Tripled.trialityRootPerm`: triality on the positive and negative simple-root
  indices.
* `TauCeti.D4Tripled.trialityModuleEquiv`: its monomial lift to the tripled module.
* `TauCeti.D4Tripled.trialityAutomorphism`: the induced automorphism of the tripled carrier.
* `TauCeti.D4Tripled.rootSubgroup_comp_trialityAutomorphism_hom`: its action on the numbered
  simple-root subgroups, `γ ∘ x_k = x_{σ k}`.
* `TauCeti.D4Tripled.weightTorus_comp_trialityAutomorphism_hom`: its action on the split weight
  torus.
* `TauCeti.D4Tripled.trialityAutomorphism_pow_three` and
  `TauCeti.D4Tripled.trialityAutomorphism_hom_comp_self_comp_self`: its order-three relation on
  the carrier.
* `TauCeti.D4Tripled.trialityPoints`: the same automorphism on matrix-valued points, with
  `TauCeti.D4Tripled.trialityPoints_symm_apply` its inverse, the square of the forward action.
* `TauCeti.D4Tripled.trialityPoints_rootSubgroupPoints` and
  `TauCeti.D4Tripled.trialityPoints_weightTorusPoints`: its pointwise equations on the numbered
  simple-root subgroups and the represented weight torus.
* `TauCeti.D4Tripled.pointsMap_comp_trialityPoints` and
  `TauCeti.D4Tripled.trialityPoints_frobenius`: its naturality in the value ring, and the
  resulting commutation with Frobenius.
* `TauCeti.D4Tripled.trialityPoints_pow_three`: its pointwise order-three relation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* The construction follows the formal template of
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.GraphAutomorphism`, with the signed involution there
  replaced by an unsigned permutation of order three.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra

universe v v'

attribute [local instance high] Algebra.toModule

/-! ## Triality on the numbered root indices -/

/-- Triality on both the positive and negative simple-root indices. -/
def trialityRootPerm : Equiv.Perm (Fin 4 ⊕ Fin 4) :=
  Equiv.sumCongr trialityPermD4 trialityPermD4

@[simp]
theorem trialityRootPerm_inl (i : Fin 4) : trialityRootPerm (.inl i) = .inl (trialityPermD4 i) :=
  by simp [trialityRootPerm]

@[simp]
theorem trialityRootPerm_inr (i : Fin 4) : trialityRootPerm (.inr i) = .inr (trialityPermD4 i) :=
  by simp [trialityRootPerm]

/-- Applying triality three times fixes every numbered root index. -/
@[simp]
theorem trialityRootPerm_apply_apply_apply (k : Fin 4 ⊕ Fin 4) :
    trialityRootPerm (trialityRootPerm (trialityRootPerm k)) = k := by
  cases k <;> simp only [trialityRootPerm_inl, trialityRootPerm_inr,
    trialityPermD4_apply_apply_apply]

/-- Triality on the numbered root indices has order dividing three. -/
@[simp]
theorem trialityRootPerm_pow_three : trialityRootPerm ^ 3 = 1 := by
  ext k
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    trialityRootPerm_apply_apply_apply]

/-! ## The monomial lift to the tripled module -/

/-- The monomial lift of triality to the tripled module: the transport of coordinate vectors along
`d4TripledTrialityPerm`, which carries the basis vector at `a` to the basis vector at
`d4TripledTrialityPerm a`, so a coordinate vector `v` to `v ∘ d4TripledTrialityPerm⁻¹`. -/
def trialityModuleEquiv : (Fin 24 → ℚ) ≃ₗ[ℚ] (Fin 24 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4TripledTrialityPerm

@[simp]
theorem trialityModuleEquiv_apply (v : Fin 24 → ℚ) (a : Fin 24) :
    trialityModuleEquiv v a = v (d4TripledTrialityPerm.symm a) := by
  rw [trialityModuleEquiv, LinearEquiv.piCongrLeft'_apply]

@[simp]
theorem trialityModuleEquiv_symm_apply (v : Fin 24 → ℚ) (a : Fin 24) :
    trialityModuleEquiv.symm v a = v (d4TripledTrialityPerm a) := by
  have h : trialityModuleEquiv.symm v = fun b => v (d4TripledTrialityPerm b) := by
    apply trialityModuleEquiv.injective
    ext b
    rw [LinearEquiv.apply_symm_apply, trialityModuleEquiv_apply, Equiv.apply_symm_apply]
  exact congrFun h a

/-- The monomial lift of triality has order dividing three. -/
@[simp]
theorem trialityModuleEquiv_apply_apply_apply (v : Fin 24 → ℚ) :
    trialityModuleEquiv (trialityModuleEquiv (trialityModuleEquiv v)) = v := by
  ext a
  simp only [trialityModuleEquiv_apply, d4TripledTrialityPerm_symm_apply_symm_apply_symm_apply]

private theorem eq_reflection_trialityPerm_iff (a b : Fin 24) (i : Fin 4) :
    d4TripledTrialityPerm a = d4TripledReflection (trialityPermD4 i) (d4TripledTrialityPerm b) ↔
      a = d4TripledReflection i b := by
  rw [← d4TripledTrialityPerm_d4TripledReflection]
  exact d4TripledTrialityPerm.injective.eq_iff

private theorem trialityModuleEquiv_rootMatrix_entry
    (target : ℤ) (X : Fin 4 → Matrix (Fin 24) (Fin 24) ℚ)
    (hX : ∀ i a b, X i a b =
      if d4TripledWeight b i = target ∧ a = d4TripledReflection i b then 1 else 0)
    (i : Fin 4) (a b : Fin 24) :
    X i a b = X (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) := by
  rw [hX, hX]
  simp only [d4TripledWeight_d4TripledTrialityPerm, eq_reflection_trialityPerm_iff]

private theorem trialityModuleEquiv_mulVec
    (X : Fin 4 → Matrix (Fin 24) (Fin 24) ℚ)
    (hX : ∀ i a b,
      X i a b = X (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b))
    (i : Fin 4) (v : Fin 24 → ℚ) :
    trialityModuleEquiv (X i *ᵥ v) = X (trialityPermD4 i) *ᵥ trialityModuleEquiv v := by
  ext a
  simp only [trialityModuleEquiv_apply, Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp d4TripledTrialityPerm
    (fun b => X (trialityPermD4 i) a b * v (d4TripledTrialityPerm.symm b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Equiv.symm_apply_apply, hX i (d4TripledTrialityPerm.symm a) b, Equiv.apply_symm_apply]

private theorem trialityModuleEquiv_mulVec_raising (i : Fin 4) (v : Fin 24 → ℚ) :
    trialityModuleEquiv (raisingMatrixQ i *ᵥ v) =
      raisingMatrixQ (trialityPermD4 i) *ᵥ trialityModuleEquiv v :=
  trialityModuleEquiv_mulVec raisingMatrixQ
    (trialityModuleEquiv_rootMatrix_entry (-1) raisingMatrixQ raisingMatrixQ_apply) i v

private theorem trialityModuleEquiv_mulVec_lowering (i : Fin 4) (v : Fin 24 → ℚ) :
    trialityModuleEquiv (loweringMatrixQ i *ᵥ v) =
      loweringMatrixQ (trialityPermD4 i) *ᵥ trialityModuleEquiv v :=
  trialityModuleEquiv_mulVec loweringMatrixQ
    (trialityModuleEquiv_rootMatrix_entry 1 loweringMatrixQ loweringMatrixQ_apply) i v

/-- **The monomial lift of triality intertwines the represented numbered root generators along
`trialityRootPerm`.** -/
theorem trialityModuleEquiv_ι_rep_serreRootGenerator :
    ∀ (k : Fin 4 ⊕ Fin 4) (v : Fin 24 → ℚ),
      trialityModuleEquiv
          (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (TauCeti.serreRootGenerator (CartanMatrix.D 4) k)) v) =
        rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (TauCeti.serreRootGenerator (CartanMatrix.D 4) (trialityRootPerm k)))
          (trialityModuleEquiv v)
  | .inl i, v => by
      rw [TauCeti.serreRootGenerator_inl, rep_ι_apply, rationalSerreRepresentation_serreE,
        trialityRootPerm_inl, TauCeti.serreRootGenerator_inl, rep_ι_apply,
        rationalSerreRepresentation_serreE]
      exact trialityModuleEquiv_mulVec_raising i v
  | .inr i, v => by
      rw [TauCeti.serreRootGenerator_inr, rep_ι_apply, rationalSerreRepresentation_serreF,
        trialityRootPerm_inr, TauCeti.serreRootGenerator_inr, rep_ι_apply,
        rationalSerreRepresentation_serreF]
      exact trialityModuleEquiv_mulVec_lowering i v

/-- The monomial lift of triality preserves the integral coordinate lattice. -/
theorem trialityModuleEquiv_mem_lattice_iff (v : Fin 24 → ℚ) :
    trialityModuleEquiv v ∈ lattice ↔ v ∈ lattice := by
  rw [mem_lattice_iff, mem_lattice_iff]
  constructor
  · intro h a
    obtain ⟨z, hz⟩ := h (d4TripledTrialityPerm a)
    exact ⟨z, by rwa [trialityModuleEquiv_apply, Equiv.symm_apply_apply] at hz⟩
  · intro h a
    obtain ⟨z, hz⟩ := h (d4TripledTrialityPerm.symm a)
    exact ⟨z, by rwa [trialityModuleEquiv_apply]⟩

/-- The monomial lift of triality permutes the lattice basis along `d4TripledTrialityPerm`, with
every scaling coefficient equal to one. -/
theorem trialityModuleEquiv_latticeBasis (a : Fin 24) :
    trialityModuleEquiv (((latticeBasis a : lattice) : Fin 24 → ℚ)) =
      ((((1 : ℤ) • latticeBasis (d4TripledTrialityPerm a) : lattice)) : Fin 24 → ℚ) := by
  rw [one_smul, coe_latticeBasis, coe_latticeBasis]
  ext b
  simp only [trialityModuleEquiv_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-! ## The triality automorphism of the carrier -/

private noncomputable def toralTrialityAutomorphism :
    Aut (kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.D 4))
      (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
      d4TripledWeight) :=
  kostantToralNumberedSymmetryIso
    (TauCeti.serreRootGenerator (CartanMatrix.D 4))
    (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
    trialityRootPerm trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff
    trialityModuleEquiv_ι_rep_serreRootGenerator trialityRootPerm.surjective
    d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis trialityPermD4
    d4TripledWeight_d4TripledTrialityPerm

/-- **The triality automorphism of the tripled type-`D₄` carrier**, characterized on the numbered
simple-root subgroups and represented weight torus. -/
noncomputable def trialityAutomorphism : Aut groupScheme :=
  toralTrialityAutomorphism

/-- The triality automorphism renumbers each positive and negative numbered simple-root subgroup
by triality, without changing its additive parameter: `γ ∘ x_k = x_{σ k}`. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_trialityAutomorphism_hom (k : Fin 4 ⊕ Fin 4) :
    rootSubgroup k ≫ trialityAutomorphism.hom = rootSubgroup (trialityRootPerm k) := by
  rw [rootSubgroup_def, trialityAutomorphism, toralTrialityAutomorphism,
    kostantRootSubgroupToToral_comp_numberedSymmetryIso_hom]
  exact (rootSubgroup_def (trialityRootPerm k)).symm

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
  · funext k
    exact trialityRootPerm_apply_apply_apply k
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

/-- The permutation matrix inducing triality on points. -/
noncomputable def trialityMatrix (A : Type v) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin 24) A :=
  kostantNumberedSymmetryMatrix lattice.toAddSubgroup latticeBasis trialityModuleEquiv
    trialityModuleEquiv_mem_lattice_iff A

/-- The triality matrix is the permutation matrix of `d4TripledTrialityPerm`. -/
theorem coe_trialityMatrix_apply (A : Type v) [CommRing A] (i j : Fin 24) :
    (trialityMatrix A : Matrix (Fin 24) (Fin 24) A) i j =
      if i = d4TripledTrialityPerm j then 1 else 0 := by
  rw [trialityMatrix, coe_kostantNumberedSymmetryMatrix_apply_of_monomial lattice.toAddSubgroup
    latticeBasis trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff d4TripledTrialityPerm
    (fun _ => 1) trialityModuleEquiv_latticeBasis A i j, map_one]

/-- The triality matrix commutes with extension of the value ring. -/
@[simp]
theorem map_trialityMatrix {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f (trialityMatrix A) = trialityMatrix B :=
  map_kostantNumberedSymmetryMatrix lattice.toAddSubgroup latticeBasis trialityModuleEquiv
    trialityModuleEquiv_mem_lattice_iff f

/-- The triality matrix has order dividing three over every commutative ring. -/
@[simp]
theorem trialityMatrix_pow_three (A : Type v) [CommRing A] : trialityMatrix A ^ 3 = 1 := by
  rw [trialityMatrix]
  apply kostantNumberedSymmetryMatrix_pow_eq_one
  intro x
  rw [pow_succ, pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact trialityModuleEquiv_apply_apply_apply x

/-- Conjugation by the triality matrix preserves the tripled carrier's point subgroup. -/
theorem map_points_conj_trialityMatrix (A : Type v) [CommRing A] :
    (points A).map (MulAut.conj (trialityMatrix A)).toMonoidHom = points A := by
  rw [points_def, definingIdeal_def, trialityMatrix]
  simpa only [kostantToralPointsSubgroup_def] using
    map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D 4))
    (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
    trialityRootPerm trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff
    trialityModuleEquiv_ι_rep_serreRootGenerator trialityRootPerm.surjective
    d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis trialityPermD4
    d4TripledWeight_d4TripledTrialityPerm A

/-- **Triality on matrix-valued points of the tripled carrier**, given by conjugation by the
triality permutation matrix. -/
noncomputable def trialityPoints (A : Type v) [CommRing A] : MulAut (points A) :=
  kostantNumberedSymmetryPoints lattice.toAddSubgroup latticeBasis trialityModuleEquiv
    trialityModuleEquiv_mem_lattice_iff A (points A) (map_points_conj_trialityMatrix A)

/-- On matrices, triality on points is conjugation by the triality matrix. -/
@[simp]
theorem coe_trialityPoints (A : Type v) [CommRing A] (g : points A) :
    (trialityPoints A g : Matrix.GeneralLinearGroup (Fin 24) A) =
      trialityMatrix A * g * (trialityMatrix A)⁻¹ :=
  coe_kostantNumberedSymmetryPoints lattice.toAddSubgroup latticeBasis trialityModuleEquiv
    trialityModuleEquiv_mem_lattice_iff A (points A) (map_points_conj_trialityMatrix A) g

/-- **Triality on points renumbers every numbered positive and negative simple-root subgroup
without changing its additive parameter**: `γ (x_k(u)) = x_{σ k}(u)`. -/
@[simp]
theorem trialityPoints_rootSubgroupPoints (A : Type v) [CommRing A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    trialityPoints A (rootSubgroupPoints k A u) =
      rootSubgroupPoints (trialityRootPerm k) A u := by
  apply Subtype.ext
  rw [coe_trialityPoints, coe_rootSubgroupPoints, coe_rootSubgroupPoints, trialityMatrix]
  exact kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D 4))
    (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis trialityRootPerm
    trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff
    trialityModuleEquiv_ι_rep_serreRootGenerator A k _

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
      have h := d4TripledWeight_d4TripledTrialityPerm (d4TripledTrialityPerm⁻¹ i) k
      rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h
    rw [hwt, ← torusCharacter_mulEquivArrowCongr trialityPermD4 s (d4TripledWeight i)]
    exact congrArg (fun z => torusCharacter z (d4TripledWeight i))
      (funext fun k => by rw [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply])
  have hconj := kostantNumberedSymmetryMatrix_conj_diagGL
    lattice.toAddSubgroup latticeBasis trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff
    d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis A
    (fun i => torusCharacter s (d4TripledWeight i))
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
      (TauCeti.serreRootGenerator (CartanMatrix.D 4))
      (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis d4TripledWeight
      trialityRootPerm trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff
      trialityModuleEquiv_ι_rep_serreRootGenerator trialityRootPerm.surjective
      d4TripledTrialityPerm (fun _ => 1) trialityModuleEquiv_latticeBasis trialityPermD4
      d4TripledWeight_d4TripledTrialityPerm A p

/-- Triality on points is natural in the value ring. -/
theorem pointsMap_comp_trialityPoints {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (pointsMap f).comp (trialityPoints A).toMonoidHom =
      (trialityPoints B).toMonoidHom.comp (pointsMap f) :=
  comp_kostantNumberedSymmetryPoints lattice.toAddSubgroup latticeBasis trialityModuleEquiv
    trialityModuleEquiv_mem_lattice_iff
    (points A) (map_points_conj_trialityMatrix A)
    (points B) (map_points_conj_trialityMatrix B) f (pointsMap f) (coe_pointsMap f)

/-- **Triality on points commutes with every iterated Frobenius of the carrier.** -/
theorem trialityPoints_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : points A) :
    trialityPoints A (frobenius p k A g) = frobenius p k A (trialityPoints A g) := by
  apply Subtype.ext
  rw [coe_trialityPoints, coe_frobenius, coe_frobenius, coe_trialityPoints, map_mul, map_mul,
    map_inv, map_trialityMatrix]

/-- **Triality on matrix-valued points has order dividing three.** -/
@[simp]
theorem trialityPoints_pow_three (A : Type v) [CommRing A] : trialityPoints A ^ 3 = 1 :=
  kostantNumberedSymmetryPoints_pow_eq_one lattice.toAddSubgroup latticeBasis
    trialityModuleEquiv trialityModuleEquiv_mem_lattice_iff A (points A)
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

/-- On matrices, the inverse of triality on points is conjugation by the inverse of the triality
matrix. -/
theorem coe_trialityPoints_symm (A : Type v) [CommRing A] (g : points A) :
    ((trialityPoints A).symm g : Matrix.GeneralLinearGroup (Fin 24) A) =
      (trialityMatrix A)⁻¹ * g * trialityMatrix A :=
  coe_kostantNumberedSymmetryPoints_symm lattice.toAddSubgroup latticeBasis trialityModuleEquiv
    trialityModuleEquiv_mem_lattice_iff A (points A) (map_points_conj_trialityMatrix A) g

end TauCeti.D4Tripled
