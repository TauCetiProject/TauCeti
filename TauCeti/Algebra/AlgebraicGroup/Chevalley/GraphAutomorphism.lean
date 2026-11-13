/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Pinned graph automorphisms of Chevalley points

Every numbered diagram symmetry acts on the points of the simply connected Chevalley group
scheme over every commutative ring. The action preserves the positive and negative simple-root
parameters, retains the Chevalley signs at general roots, and relabels fundamental-weight torus
coordinates by the inverse permutation. It is natural in the value ring, so commutes with field
maps and Frobenius.

`chevalleyGraphAut` uses the independently constructed full-weight lattice symmetry
`scToralDiagramAutPoints`. The proved equality
`chevalleyGroup_eq_kostantToralPointsSubgroup` identifies its point interface with the
full-weight Chevalley datum, without changing any underlying matrix. No generation of scheme
points by root subgroups is assumed. This provides the graph factor for Steinberg maps directly
on the same point group as the datum's root and torus maps.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

/-- The pinned graph automorphism on the points of the simply connected Chevalley group,
induced by the integral full-weight lattice symmetry. -/
def chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    MulAut ((t.scChevalleyDatum ht).points A) :=
  MulAut.congr (MulEquiv.subgroupCongr
    (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)).symm
      (t.scToralDiagramAutPoints ht hσ A)

/-- On matrices the graph automorphism is conjugation by the integral lattice symmetry. -/
@[simp]
theorem coe_chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A]
    (g : t.chevalleyGroup ht A) :
    ((t.chevalleyGraphAut ht hσ A g).val :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
          (t.scModuleDiagramEquiv ht hσ)
          (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) A *
        (g : Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) *
        (kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
          (t.scModuleDiagramEquiv ht hσ)
          (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) A)⁻¹ :=
  t.coe_scToralDiagramAutPoints ht hσ A
    (MulEquiv.subgroupCongr (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A) g)

/-- The identity diagram symmetry acts identically. -/
@[simp]
theorem chevalleyGraphAut_one (A : Type v) [CommRing A] :
    t.chevalleyGraphAut ht t.diagramSymmetry.one_mem A = 1 := by
  let e := MulAut.congr (MulEquiv.subgroupCongr
    (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)).symm
  exact (congrArg e (t.scToralDiagramAutPoints_one ht A)).trans e.map_one

/-- Multiplication of numbered symmetries agrees with composition of their graph actions. -/
@[simp]
theorem chevalleyGraphAut_mul (hσ : σ ∈ t.diagramSymmetry)
    (hτ : τ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    t.chevalleyGraphAut ht (t.diagramSymmetry.mul_mem hσ hτ) A =
      t.chevalleyGraphAut ht hσ A * t.chevalleyGraphAut ht hτ A := by
  let e := MulAut.congr (MulEquiv.subgroupCongr
    (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)).symm
  exact (congrArg e (t.scToralDiagramAutPoints_mul ht hσ hτ A)).trans
    (e.map_mul _ _)

/-- The diagram symmetry group acts on the entire Chevalley point group. -/
def chevalleyGraphAutHom (A : Type v) [CommRing A] :
    t.diagramSymmetry →* MulAut ((t.scChevalleyDatum ht).points A) where
  toFun s := t.chevalleyGraphAut ht s.property A
  map_one' := t.chevalleyGraphAut_one ht A
  map_mul' s r := t.chevalleyGraphAut_mul ht s.property r.property A

/-- Evaluation of the bundled diagram action. -/
@[simp]
theorem chevalleyGraphAutHom_apply (A : Type v) [CommRing A] (s : t.diagramSymmetry) :
    t.chevalleyGraphAutHom ht A s = t.chevalleyGraphAut ht s.property A :=
  (rfl)

/-- The inverse diagram symmetry induces the inverse graph automorphism. -/
@[simp]
theorem chevalleyGraphAut_inv (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    t.chevalleyGraphAut ht (t.diagramSymmetry.inv_mem hσ) A =
      (t.chevalleyGraphAut ht hσ A)⁻¹ := by
  simpa only [chevalleyGraphAutHom_apply] using
    map_inv (t.chevalleyGraphAutHom ht A) ⟨σ, hσ⟩

/-- Every order relation of the diagram permutation holds on Chevalley points. -/
theorem chevalleyGraphAut_pow_eq_one (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] {n : ℕ} (hn : σ ^ n = 1) :
    t.chevalleyGraphAut ht hσ A ^ n = 1 := by
  let e := MulAut.congr (MulEquiv.subgroupCongr
    (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)).symm
  exact (map_pow e (t.scToralDiagramAutPoints ht hσ A) n).symm.trans
    ((congrArg e (t.scToralDiagramAutPoints_pow_eq_one ht hσ A hn)).trans e.map_one)

/-- The pinned graph action carries every root subgroup to its diagram image with the sign
of the independently normalized Chevalley root vector. -/
@[simp]
theorem chevalleyGraphAut_rootSubgroupPoints (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) (A : Type v) [CommRing A] (u : A) :
    t.chevalleyGraphAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints α A (Multiplicative.ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A
        (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  apply Subtype.ext
  have h := t.kostantNumberedSymmetryMatrix_conj_chevalleyRootSubgroup ht
    (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
    (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
    (t.isNilpotent_representation_scModule_rootGenerator ht)
    (t.scWeightBasis ht) hσ (t.scModuleDiagramEquiv ht hσ)
    (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    (fun x v => by simpa only [representation_ι_apply] using
      t.scModuleDiagramEquiv_lie ht hσ x v) α A u
  have hg := t.coe_chevalleyGraphAut ht hσ A
    ((t.scChevalleyDatum ht).rootSubgroupPoints α A (Multiplicative.ofAdd u))
  rw [ChevalleyDatum.coe_rootSubgroupPoints] at hg
  exact hg.trans (h.trans
    ((t.scChevalleyDatum ht).coe_rootSubgroupPoints _ A _).symm)

/-- Positive simple-root parameters are unchanged by the pinned graph action. -/
-- Apply the pinning formula before the general-root formula introduces its signed index.
@[simp↓]
theorem chevalleyGraphAut_rootSubgroupPoints_simpleIndex (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank) (A : Type v) [CommRing A] (u : A) :
    t.chevalleyGraphAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht i) A
          (Multiplicative.ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht (σ i)) A
        (Multiplicative.ofAdd u) := by
  simpa only [diagramRootPerm_simpleIndex, chevalleyDiagramSign_simpleIndex, Units.val_one,
    Int.cast_one, one_mul] using
    t.chevalleyGraphAut_rootSubgroupPoints ht hσ (t.simpleIndex ht i) A u

/-- Negative simple-root parameters are unchanged by the pinned graph action. -/
@[simp↓]
theorem chevalleyGraphAut_rootSubgroupPoints_reflectionPerm_simpleIndex
    (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) (A : Type v) [CommRing A] (u : A) :
    t.chevalleyGraphAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
            (t.simpleIndex ht i)) A (Multiplicative.ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht (σ i))
          (t.simpleIndex ht (σ i))) A (Multiplicative.ofAdd u) := by
  have hp := (t.diagramAut ht hσ).toHom.indexEquiv_reflectionPerm
    (t.simpleIndex ht i) (t.simpleIndex ht i)
  simp only [diagramAut_indexEquiv, diagramRootPerm_simpleIndex] at hp
  simpa only [hp, chevalleyDiagramSign_reflectionPerm_self, chevalleyDiagramSign_simpleIndex,
    Units.val_one, Int.cast_one, one_mul] using
    t.chevalleyGraphAut_rootSubgroupPoints ht hσ
      ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
        (t.simpleIndex ht i)) A u

/-- The graph action relabels fundamental-weight torus parameters by the inverse symmetry. -/
@[simp]
theorem chevalleyGraphAut_torusPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.chevalleyGraphAut ht hσ A ((t.scChevalleyDatum ht).torusPoints A s) =
      (t.scChevalleyDatum ht).torusPoints A (fun j => s (σ⁻¹ j)) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (t.scToralDiagramAutPoints_kostantToralWeightTorusPoints ht hσ A s)
  simp only [coe_scToralDiagramAutPoints, coe_kostantToralWeightTorusPoints] at h
  have hg := t.coe_chevalleyGraphAut ht hσ A ((t.scChevalleyDatum ht).torusPoints A s)
  rw [ChevalleyDatum.coe_torusPoints, scChevalleyDatum_coordinateWeight] at hg
  have hT := (t.scChevalleyDatum ht).coe_torusPoints A (fun j => s (σ⁻¹ j))
  rw [scChevalleyDatum_coordinateWeight] at hT
  exact hg.trans (h.trans hT.symm)

/-- The character pullback of the graph action is the inverse diagram datum action. -/
theorem isCharacterMap_chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (t.chevalleyGraphAut ht hσ A).toMonoidHom (t.diagramAut ht hσ)⁻¹.toHom.weightMap := by
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [diagramAut_inv_weightMap, torusPointMap_funCongrLeft]
  exact t.chevalleyGraphAut_torusPoints ht hσ A s

/-- Graph automorphisms are natural under every change of value ring. In particular, they
commute with arbitrary field endomorphisms, including all iterates of Frobenius. -/
theorem map_chevalleyGraphAut (hσ : σ ∈ t.diagramSymmetry)
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B)
    (g : (t.scChevalleyDatum ht).points A) :
    ((t.scChevalleyDatum ht).pointsPresentation A).map
        ((t.scChevalleyDatum ht).pointsPresentation B) f (t.chevalleyGraphAut ht hσ A g) =
      t.chevalleyGraphAut ht hσ B
        (((t.scChevalleyDatum ht).pointsPresentation A).map
          ((t.scChevalleyDatum ht).pointsPresentation B) f g) := by
  apply Subtype.ext
  -- Match the datum dimension with the full-weight basis cardinality in the two point APIs.
  erw [GeneralLinear.IntegralPointsPresentation.coe_map, coe_chevalleyGraphAut,
    coe_chevalleyGraphAut, GeneralLinear.IntegralPointsPresentation.coe_map]
  dsimp +instances only [scChevalleyDatum]
  simp only [map_mul, map_inv, map_kostantNumberedSymmetryMatrix]

end

end TauCeti.DynkinType
