/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.G2.ShortRoot.AdmissibleLattice
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootNormalization
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Killing
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

/-!
# The seven-dimensional Chevalley datum of type G₂

The integral short-root representation gives a faithful representation of the independently
pinned rational Lie algebra of type G₂. Together with its admissible coordinate lattice and
seven weight vectors it defines `TauCeti.G2ShortRoot.chevalleyDatum`. Its weights span the full
weight lattice, so its torus uses fundamental-weight coordinates without an isogeny kernel.
This is the representation-theoretic input for comparing the short-root group with other
simply connected realizations; no comparison of group schemes is asserted here.

The action is transported through `TauCeti.DynkinType.serreLiftEquiv` from
`TauCeti.G2ShortRoot.rep`. Lattice stability and the integral weight vectors come from
`TauCeti.G2ShortRoot.rep_serreKostantForm_apply_mem_lattice` and
`TauCeti.G2ShortRoot.isCartanWeightVector_latticeBasis`. Faithfulness is detected on the
splitting Cartan subalgebra using `TauCeti.isFaithful_of_isFaithful_cartanSubalgebra`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§19 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.G2ShortRoot

open DynkinType
open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

-- Keep the native rank in the source and the explicit rank two in the represented target.
-- Reindexing the Serre generators avoids a dependent cast of the entire Lie equivalence.
private theorem nativeSerreSystem : IsSerreSystem ℚ G2.cartanMatrix.transpose
    (serreH ℚ CartanMatrix.G₂ ∘ Fin.cast rank_G2)
    (serreE ℚ CartanMatrix.G₂ ∘ Fin.cast rank_G2)
    (serreF ℚ CartanMatrix.G₂ ∘ Fin.cast rank_G2) := by
  have h := (isSerreSystem_serre ℚ CartanMatrix.G₂).submatrix
    (f := Fin.cast rank_G2) (Fin.cast_injective _)
  have hCM : CartanMatrix.G₂.submatrix (Fin.cast rank_G2) (Fin.cast rank_G2) =
      G2.cartanMatrix.transpose := by
    ext i j
    dsimp only [rank] at i j ⊢
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, cartanMatrix_G2,
      Fin.cast_eq_self]
  rw [hCM] at h
  exact h

private def pinnedToSerre :
    G2.lieAlgebra valid_G2 →ₗ⁅ℚ⁆ Matrix.ToLieAlgebra ℚ CartanMatrix.G₂ :=
  (_root_.TauCeti.serreLift nativeSerreSystem).comp
    (G2.serreLiftEquiv valid_G2).symm.toLieHom

private theorem pinnedToSerre_h (i : Fin G2.rank) :
    pinnedToSerre ((G2.lieBasis valid_G2).h i) =
      serreH ℚ CartanMatrix.G₂ (Fin.cast rank_G2 i) := by
  rw [pinnedToSerre, LieHom.comp_apply, LieEquiv.coe_coe,
    serreLiftEquiv_symm_lieBasis_h]
  exact _root_.TauCeti.serreLift_serreH nativeSerreSystem i

private theorem pinnedToSerre_e (i : Fin G2.rank) :
    pinnedToSerre ((G2.lieBasis valid_G2).e i) =
      serreE ℚ CartanMatrix.G₂ (Fin.cast rank_G2 i) := by
  rw [pinnedToSerre, LieHom.comp_apply, LieEquiv.coe_coe,
    serreLiftEquiv_symm_lieBasis_e]
  exact _root_.TauCeti.serreLift_serreE nativeSerreSystem i

private theorem pinnedToSerre_f (i : Fin G2.rank) :
    pinnedToSerre ((G2.lieBasis valid_G2).f i) =
      serreF ℚ CartanMatrix.G₂ (Fin.cast rank_G2 i) := by
  rw [pinnedToSerre, LieHom.comp_apply, LieEquiv.coe_coe,
    serreLiftEquiv_symm_lieBasis_f]
  exact _root_.TauCeti.serreLift_serreF nativeSerreSystem i

/-- The seven-dimensional short-root representation of the pinned rational G₂ Lie algebra,
extended to its enveloping algebra. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra valid_G2) →ₐ[ℚ]
      Module.End ℚ (Fin 7 → ℚ) :=
  rep.comp (map ℚ pinnedToSerre)

private theorem pinnedRepresentation_ι (x : G2.lieAlgebra valid_G2) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (pinnedToSerre x)) := by
  rw [pinnedRepresentation, AlgHom.comp_apply, map_ι]

/-- The pinned Cartan generator acts by the diagonal matrix of the seven weights. -/
@[simp↓]
theorem pinnedRepresentation_h (i : Fin G2.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).h i)) =
      Matrix.toLinAlgEquiv' (cartanMatrixRat i) := by
  simp only [pinnedRepresentation_ι, pinnedToSerre_h, rep_ι_eq_toLinAlgEquiv',
    rationalSerreRepresentation_serreH]
  dsimp +instances only [rank] at i ⊢
  simp only [Fin.cast_eq_self]

/-- The pinned raising generator acts by the existing integral raising matrix over ℚ. -/
@[simp↓]
theorem pinnedRepresentation_e (i : Fin G2.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).e i)) =
      Matrix.toLinAlgEquiv' (raisingMatrixRat i) := by
  simp only [pinnedRepresentation_ι, pinnedToSerre_e, rep_ι_eq_toLinAlgEquiv',
    rationalSerreRepresentation_serreE]
  dsimp +instances only [rank] at i ⊢
  simp only [Fin.cast_eq_self]

/-- The pinned lowering generator acts by the existing integral lowering matrix over ℚ. -/
@[simp↓]
theorem pinnedRepresentation_f (i : Fin G2.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).f i)) =
      Matrix.toLinAlgEquiv' (loweringMatrixRat i) := by
  simp only [pinnedRepresentation_ι, pinnedToSerre_f, rep_ι_eq_toLinAlgEquiv',
    rationalSerreRepresentation_serreF]
  dsimp +instances only [rank] at i ⊢
  simp only [Fin.cast_eq_self]

private theorem pinnedRepresentation_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra valid_G2))
    (hu : u ∈ kostantForm (G2.lieBasis valid_G2).rootGenerator (G2.lieBasis valid_G2).h)
    (v : Fin 7 → ℚ) (hv : v ∈ lattice) : pinnedRepresentation u v ∈ lattice := by
  have hmap : map ℚ pinnedToSerre u ∈
      (kostantForm (G2.lieBasis valid_G2).rootGenerator (G2.lieBasis valid_G2).h).map
        (map ℚ pinnedToSerre).toRingHom := Subring.mem_map.mpr ⟨u, hu, rfl⟩
  have he (k : Fin G2.rank ⊕ Fin G2.rank) :
      pinnedToSerre ((G2.lieBasis valid_G2).rootGenerator k) =
        ((1 : ℤˣ) : ℤ) • serreRootGenerator CartanMatrix.G₂
          (Sum.map (Fin.cast rank_G2) (Fin.cast rank_G2) k) := by
    rcases k with i | i
    · rw [LieAlgebra.Basis.rootGenerator_inl, pinnedToSerre_e, Sum.map_inl,
        serreRootGenerator_inl]
      simp only [Units.val_one, one_smul]
    · rw [LieAlgebra.Basis.rootGenerator_inr, pinnedToSerre_f, Sum.map_inr,
        serreRootGenerator_inr]
      simp only [Units.val_one, one_smul]
  have hh (i : Fin G2.rank) : pinnedToSerre ((G2.lieBasis valid_G2).h i) =
      ((1 : ℤˣ) : ℤ) • serreH ℚ CartanMatrix.G₂ (Fin.cast rank_G2 i) := by
    simp [pinnedToSerre_h]
  have hcast : Function.Surjective (Fin.cast rank_G2) :=
    (Fin.rightInverse_cast rank_G2).surjective
  rw [map_kostantForm_of_root_units pinnedToSerre
    (G2.lieBasis valid_G2).rootGenerator (G2.lieBasis valid_G2).h
    (serreRootGenerator CartanMatrix.G₂) (serreH ℚ CartanMatrix.G₂)
    (Sum.map (Fin.cast rank_G2) (Fin.cast rank_G2)) (Fin.cast rank_G2) 1 1
    (Sum.map_surjective.mpr ⟨hcast, hcast⟩) hcast he hh,
    ← serreKostantForm_def] at hmap
  exact rep_serreKostantForm_apply_mem_lattice hmap hv

private theorem pinnedRepresentation_cartan_apply (x : G2.cartanSubalgebra valid_G2)
    (v : Fin 7 → ℚ) (a : Fin 7) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ (x : G2.lieAlgebra valid_G2)) v a =
      ∑ i : Fin G2.rank, (G2.cartanBasis valid_G2).repr x i *
        (weight a i : ℚ) * v a := by
  have hx : (x : G2.lieAlgebra valid_G2) =
      ∑ i, (G2.cartanBasis valid_G2).repr x i • (G2.lieBasis valid_G2).h i := by
    simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, coe_cartanBasis] using
      (congrArg Subtype.val ((G2.cartanBasis valid_G2).sum_repr x)).symm
  rw [hx]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, pinnedRepresentation_h, Matrix.toLinAlgEquiv'_apply,
    Matrix.mulVec, dotProduct]
  dsimp +instances only [rank]
  simp only [cartanMatrixRat_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_assoc]

private theorem pinnedRepresentation_injective : Function.Injective
    (fun x : G2.lieAlgebra valid_G2 =>
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) := by
  let ρ := pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let := LieRingModule.compLieHom (Fin 7 → ℚ) ρ
  let := LieModule.compLieHom (Fin 7 → ℚ) ρ
  have : LieModule.IsFaithful ℚ (G2.cartanSubalgebra valid_G2) (Fin 7 → ℚ) := by
    rw [LieModule.isFaithful_iff']
    intro x hx
    have hweight (a : Fin 7) :
        ∑ i : Fin G2.rank, (G2.cartanBasis valid_G2).repr x i *
          (weight a i : ℚ) = 0 := by
      have h := congrFun (hx (Pi.single a 1)) a
      simp only [LieSubalgebra.coe_bracket_of_module, LieRingModule.compLieHom_apply,
        ρ, LieHom.comp_apply, AlgHom.toLieHom_apply, Module.End.lie_apply,
        Pi.zero_apply, pinnedRepresentation_cartan_apply, Pi.single_eq_same, mul_one] at h
      exact h
    have h0 := hweight 0
    have h1 := hweight 1
    dsimp +instances only [rank] at h0 h1
    rw [Fin.sum_univ_two] at h0 h1
    norm_num [weight_apply] at h0 h1
    rw [h0, neg_zero, zero_add] at h1
    apply (G2.cartanBasis valid_G2).repr.injective
    rw [map_zero, Finsupp.ext_iff]
    exact Fin.forall_fin_two.mpr ⟨h0, h1⟩
  have := isFaithful_of_isFaithful_cartanSubalgebra
    (H := G2.cartanSubalgebra valid_G2) (M := Fin 7 → ℚ)
  intro x y hxy
  apply LieModule.ext_of_isFaithful (R := ℚ) (M := Fin 7 → ℚ)
  intro v
  simpa only [LieRingModule.compLieHom_apply, ρ, LieHom.comp_apply,
    AlgHom.toLieHom_apply, Module.End.lie_apply] using congrArg (fun f => f v) hxy

private theorem pinnedRepresentation_isCartanWeightVector (a : Fin 7) :
    IsCartanWeightVector (G2.lieBasis valid_G2).h pinnedRepresentation
      (weight a) (latticeBasis a : Fin 7 → ℚ) := by
  apply (isCartanWeightVector_iff _ _).mpr
  intro i
  rw [pinnedRepresentation_ι, pinnedToSerre_h]
  dsimp only [rank] at i ⊢
  simpa only [Fin.cast_eq_self] using
    (isCartanWeightVector_iff _ _).mp (isCartanWeightVector_latticeBasis a) i

/-- The full-weight Chevalley datum on the seven-dimensional short-root module of type G₂,
with its integral coordinate lattice and fundamental-weight torus coordinates. -/
-- The carrier, dimension and lattice must compute in the dependent representation and basis API.
@[expose] def chevalleyDatum : ChevalleyDatum G2 valid_G2 where
  carrier := Fin 7 → ℚ
  representation := pinnedRepresentation
  injective_representation_ι := by exact pinnedRepresentation_injective
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := by exact pinnedRepresentation_mem_lattice
  span_lattice_eq_top := by
    have hlattice : lattice = coordinateLattice (Fin 7) := by
      ext v
      simp only [mem_lattice_iff, mem_coordinateLattice_iff]
    simpa only [Submodule.coe_toAddSubgroup, hlattice] using
      (instIsLatticeCoordinateLattice (Fin 7)).span_eq_top
  dim := 7
  basis := latticeBasis
  weight := weight
  isCartanWeightVector_basis := by exact pinnedRepresentation_isCartanWeightVector
  weightLatticeBasis := (Pi.basisFun ℤ (Fin G2.rank)).map
    (LinearEquiv.ofTop _ span_range_weight_eq_top).symm

/-- The datum uses the pinned short-root representation. -/
@[simp] theorem chevalleyDatum_representation :
    chevalleyDatum.representation = pinnedRepresentation := (rfl)

/-- The Cartan generator of the datum is the existing diagonal weight matrix. -/
@[simp↓] theorem chevalleyDatum_representation_h (i : Fin G2.rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).h i)) =
      Matrix.toLinAlgEquiv' (cartanMatrixRat i) := by
  dsimp only [chevalleyDatum]
  exact pinnedRepresentation_h i

/-- The raising generator of the datum is the existing integral raising matrix over ℚ. -/
@[simp↓] theorem chevalleyDatum_representation_e (i : Fin G2.rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).e i)) =
      Matrix.toLinAlgEquiv' (raisingMatrixRat i) := by
  dsimp only [chevalleyDatum]
  exact pinnedRepresentation_e i

/-- The lowering generator of the datum is the existing integral lowering matrix over ℚ. -/
@[simp↓] theorem chevalleyDatum_representation_f (i : Fin G2.rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis valid_G2).f i)) =
      Matrix.toLinAlgEquiv' (loweringMatrixRat i) := by
  dsimp only [chevalleyDatum]
  exact pinnedRepresentation_f i

/-- The datum has seven coordinate basis vectors. -/
theorem chevalleyDatum_dim : chevalleyDatum.dim = 7 := (rfl)

/-- The datum uses the existing integral coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice : chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The datum retains the integral coordinate basis. -/
@[simp] theorem chevalleyDatum_basis : chevalleyDatum.basis = latticeBasis := (rfl)

/-- A datum basis vector is the corresponding rational coordinate vector. -/
@[simp↓] theorem coe_chevalleyDatum_basis (a : Fin 7) :
    ((chevalleyDatum.basis a).val : Fin 7 → ℚ) = Pi.single a 1 :=
  coe_latticeBasis a

/-- The weights of the datum are the native seven short-root weights, in the same numbering. -/
@[simp] theorem chevalleyDatum_weight : chevalleyDatum.weight = weight := (rfl)

/-- The seven weights generate the full weight lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ :=
  chevalleyDatum.weightLattice_def.trans (by
    rw [chevalleyDatum_weight]
    exact span_range_weight_eq_top)

/-- The chosen character basis consists of the fundamental weights. -/
@[simp↓] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin G2.rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin G2.rank → ℤ) = Pi.single i 1 := by
  dsimp +instances only [chevalleyDatum, rank] at i ⊢
  rw [Module.Basis.map_apply]
  simp only [LinearEquiv.coe_ofTop_symm_apply]
  exact Pi.basisFun_apply ℤ (Fin 2) i

/-- The coordinate weights of the datum are its fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateWeight : chevalleyDatum.coordinateWeight = weight := by
  ext a i
  have h := congrFun (chevalleyDatum.sum_coordinateWeight_smul a) i
  simpa only [Finset.sum_apply, Pi.smul_apply, coe_chevalleyDatum_weightLatticeBasis,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, chevalleyDatum_weight] using h

/-- The coordinate roots of the datum are the roots in fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin G2.numRoots) :
    chevalleyDatum.coordinateRoot γ = (G2.simplyConnectedRootDatum valid_G2).root γ := by
  ext i
  have h := congrFun (chevalleyDatum.sum_coordinateRoot_smul γ) i
  simpa only [Finset.sum_apply, Pi.smul_apply, coe_chevalleyDatum_weightLatticeBasis,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] using h

end

end TauCeti.G2ShortRoot
