/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.D4.Tripled.AdmissibleLattice
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The tripled D₄ Chevalley datum

`TauCeti.D4Tripled.chevalleyDatum` equips the rational coordinate space of the natural and
both half-spin representations with an action of the pinned type-D₄ Lie algebra. Its
admissible lattice is the existing coordinate lattice, with the existing twenty-four weights
and their full weight lattice in fundamental-weight coordinates. In particular, no orthogonal
image or single eight-dimensional summand is substituted for the tripled representation.

The action pulls the minuscule weight-table representation back through
`DynkinType.serreLiftEquiv`. Faithfulness is detected on the splitting Cartan subalgebra by
`TauCeti.isFaithful_of_isFaithful_cartanSubalgebra`. Admissibility uses the square-zero
coordinate-lattice criterion
`UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice`.
These data allow Chevalley-datum comparisons to be applied to the tripled model; no comparison
of group schemes or of their points is asserted here.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18, 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.D4Tripled

open DynkinType
open scoped _root_.Matrix
open _root_.UniversalEnvelopingAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem pinnedSerreSystem :
    IsSerreSystem ℚ (DynkinType.D 4).cartanMatrixᵀ
      (fun i => weightTable.cartanGeneratorMatrixQ (Fin.cast (rank_D 4) i))
      (fun i => weightTable.raisingMatrixQ (Fin.cast (rank_D 4) i))
      (fun i => weightTable.loweringMatrixQ (Fin.cast (rank_D 4) i)) := by
  simpa only [cartanMatrix_D, CartanMatrix.D_transpose, rank_D, Fin.cast_eq_self,
    weightTable_cartanMatrix] using weightTable.isSerreSystemQ

private def pinnedAction :
    (DynkinType.D 4).lieAlgebra (by decide) →ₗ⁅ℚ⁆ Module.End ℚ (Fin 24 → ℚ) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toLieHom.comp
    ((TauCeti.serreLift pinnedSerreSystem).comp
      ((DynkinType.D 4).serreLiftEquiv (by decide)).symm.toLieHom)

/-- The enveloping-algebra action of the pinned type-D₄ algebra on the tripled module. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.D 4).lieAlgebra (by decide)) →ₐ[ℚ]
      Module.End ℚ (Fin 24 → ℚ) :=
  lift ℚ pinnedAction

private theorem pinnedRep_ι (x : (DynkinType.D 4).lieAlgebra (by decide)) :
    pinnedRep (ι ℚ x) = pinnedAction x :=
  lift_ι_apply _ _ _

private theorem toLinAlgEquiv'_eq_toLin' (M : Matrix (Fin 24) (Fin 24) ℚ) :
    Matrix.toLinAlgEquiv' M = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

/-- A numbered Cartan generator acts by its existing diagonal weight matrix. -/
@[simp↓]
theorem pinnedRep_h (i : Fin (DynkinType.D 4).rank) :
    pinnedRep (ι ℚ (((DynkinType.D 4).lieBasis (by decide)).h i)) =
      Matrix.toLin' (weightTable.cartanGeneratorMatrixQ (Fin.cast (rank_D 4) i)) := by
  rw [pinnedRep_ι]
  simp only [pinnedAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    serreLiftEquiv_symm_lieBasis_h, TauCeti.serreLift_serreH, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, toLinAlgEquiv'_eq_toLin']

/-- A numbered raising generator acts by the existing tripled raising matrix. -/
@[simp↓]
theorem pinnedRep_e (i : Fin (DynkinType.D 4).rank) :
    pinnedRep (ι ℚ (((DynkinType.D 4).lieBasis (by decide)).e i)) =
      Matrix.toLin' (weightTable.raisingMatrixQ (Fin.cast (rank_D 4) i)) := by
  rw [pinnedRep_ι]
  simp only [pinnedAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    serreLiftEquiv_symm_lieBasis_e, TauCeti.serreLift_serreE, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, toLinAlgEquiv'_eq_toLin']

/-- A numbered lowering generator acts by the existing tripled lowering matrix. -/
@[simp↓]
theorem pinnedRep_f (i : Fin (DynkinType.D 4).rank) :
    pinnedRep (ι ℚ (((DynkinType.D 4).lieBasis (by decide)).f i)) =
      Matrix.toLin' (weightTable.loweringMatrixQ (Fin.cast (rank_D 4) i)) := by
  rw [pinnedRep_ι]
  simp only [pinnedAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    serreLiftEquiv_symm_lieBasis_f, TauCeti.serreLift_serreF, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, toLinAlgEquiv'_eq_toLin']

private theorem pinnedRep_root (k : Fin (DynkinType.D 4).rank ⊕ Fin (DynkinType.D 4).rank) :
    pinnedRep (ι ℚ (((DynkinType.D 4).lieBasis (by decide)).rootGenerator k)) =
      weightTable.rep (ι ℚ (serreRootGenerator weightTable.cartanMatrix
        (Sum.map (Fin.cast (rank_D 4)) (Fin.cast (rank_D 4)) k))) := by
  cases k with
  | inl i =>
    simp only [LieAlgebra.Basis.rootGenerator_inl, pinnedRep_e, Sum.map_inl,
      TauCeti.serreRootGenerator_inl]
    apply LinearMap.ext
    intro v
    rw [weightTable.rep_ι_apply, weightTable.rationalSerreRepresentation_serreE]
    exact Matrix.toLin'_apply _ _
  | inr i =>
    simp only [LieAlgebra.Basis.rootGenerator_inr, pinnedRep_f, Sum.map_inr,
      TauCeti.serreRootGenerator_inr]
    apply LinearMap.ext
    intro v
    rw [weightTable.rep_ι_apply, weightTable.rationalSerreRepresentation_serreF]
    exact Matrix.toLin'_apply _ _

private theorem pinnedRep_weight (a : Fin 24) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector
      ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).h pinnedRep
      (fun i => d4TripledWeight a (Fin.cast (rank_D 4) i))
      (Pi.single a 1) := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  rw [pinnedRep_h, Matrix.toLin'_apply]
  have h := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (weightTable.isCartanWeightVector_single a) (Fin.cast (rank_D 4) i)
  rw [weightTable.rep_ι_apply, weightTable.rationalSerreRepresentation_serreH,
    weightTable_weight] at h
  exact h

private theorem pinnedRep_cartan_single
    (x : (DynkinType.D 4).cartanSubalgebra (valid_D.mpr le_rfl)) (a : Fin 24) :
    pinnedRep (ι ℚ (x : (DynkinType.D 4).lieAlgebra (valid_D.mpr le_rfl)))
        (Pi.single a 1) a =
      ∑ i, ((DynkinType.D 4).cartanBasis (valid_D.mpr le_rfl)).repr x i *
        (d4TripledWeight a (Fin.cast (rank_D 4) i) : ℚ) := by
  let b := (DynkinType.D 4).cartanBasis (valid_D.mpr le_rfl)
  let f := ((DynkinType.D 4).cartanSubalgebra (valid_D.mpr le_rfl)).toSubmodule.subtype
  have hexp : (x : (DynkinType.D 4).lieAlgebra (valid_D.mpr le_rfl)) =
      ∑ i, b.repr x i • ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).h i := by
    calc
      (x : (DynkinType.D 4).lieAlgebra (valid_D.mpr le_rfl)) =
          f (∑ i, b.repr x i • b i) := congrArg f (b.sum_repr x).symm
      _ = _ := by
        simp only [map_sum, map_smul]
        simp only [f, Submodule.subtype_apply, b, coe_cartanBasis]
  rw [hexp]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp (pinnedRep_weight a),
    Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, b]

-- The weights span ℤ⁴, so vanishing on all weight vectors detects every Cartan coordinate.
private theorem pinnedAction_cartan_isFaithful :
    let pinnedLieRingModule := LieRingModule.compLieHom (Fin 24 → ℚ) pinnedAction
    let pinnedLieModule := LieModule.compLieHom (Fin 24 → ℚ) pinnedAction
    LieModule.IsFaithful ℚ ((DynkinType.D 4).cartanSubalgebra (by decide))
      (Fin 24 → ℚ) := by
  rw [LieModule.isFaithful_iff']
  intro x hx
  let c : Fin 4 → ℚ := fun i =>
    ((DynkinType.D 4).cartanBasis (valid_D.mpr le_rfl)).repr x
      (Fin.cast (rank_D 4).symm i)
  have heval (a : Fin 24) : ∑ i, c i * (d4TripledWeight a i : ℚ) = 0 := by
    have h := hx (Pi.single a 1)
    have hact : pinnedRep (ι ℚ (x : (DynkinType.D 4).lieAlgebra (by decide)))
        (Pi.single a 1) = 0 := by
      rw [pinnedRep_ι]
      exact h
    have hscalar := congrFun hact a
    rw [pinnedRep_cartan_single] at hscalar
    exact hscalar
  let f : (Fin 4 → ℤ) →ₗ[ℤ] ℚ :=
    ∑ i, (c i) • ((Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj i))
  have hf (μ : Fin 4 → ℤ) : f μ = ∑ i, c i * (μ i : ℚ) := by
    simp [f]
  have hzero : ∀ μ ∈ Submodule.span ℤ (Set.range d4TripledWeight), f μ = 0 :=
    LinearMap.eqOn_span (f := f) (g := 0) (by rintro _ ⟨a, rfl⟩; simpa [hf] using heval a)
  have hc (i : Fin 4) : c i = 0 := by
    have h := hzero (Pi.single i 1) (by rw [span_range_d4TripledWeight_eq_top]; trivial)
    simpa [hf, Pi.single_apply, Finset.mem_univ] using h
  apply ((DynkinType.D 4).cartanBasis (by decide)).repr.injective
  ext i
  have h := hc (Fin.cast (rank_D 4) i)
  simp only [c, Fin.cast_cast, Fin.cast_eq_self] at h
  simpa only [map_zero, Finsupp.zero_apply] using h

private theorem pinnedRep_injective :
    Function.Injective fun x : (DynkinType.D 4).lieAlgebra (by decide) => pinnedRep (ι ℚ x) := by
  let pinnedLieRingModule := LieRingModule.compLieHom (Fin 24 → ℚ) pinnedAction
  let pinnedLieModule := LieModule.compLieHom (Fin 24 → ℚ) pinnedAction
  have hCartan := pinnedAction_cartan_isFaithful
  have hFaithful : LieModule.IsFaithful ℚ ((DynkinType.D 4).lieAlgebra (valid_D.mpr le_rfl))
      (Fin 24 → ℚ) :=
    isFaithful_of_isFaithful_cartanSubalgebra
      (H := (DynkinType.D 4).cartanSubalgebra (valid_D.mpr le_rfl))
  intro x y hxy
  apply hFaithful.injective_toEnd
  dsimp only at hxy
  rw [pinnedRep_ι, pinnedRep_ι] at hxy
  exact hxy

private theorem pinnedRep_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      ((DynkinType.D 4).lieAlgebra (valid_D.mpr le_rfl)))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).rootGenerator
      ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).h)
    (v : Fin 24 → ℚ) (hv : v ∈ lattice) : pinnedRep u v ∈ lattice := by
  rw [lattice_def] at hv ⊢
  apply UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    _ _ pinnedRep (wt := fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i))
    _ _ pinnedRep_weight hu hv
  · intro k
    rw [pinnedRep_root]
    exact weightTable.rep_serreRootGenerator_pow_two _
  · intro k w hw
    rw [pinnedRep_root]
    exact weightTable.rep_serreRootGenerator_mem_lattice _ hw

/-- The tripled natural and half-spin module as a full-weight Chevalley datum of type D₄.
Its character basis is the standard basis of fundamental weights. -/
-- The carrier, lattice and dimension compute so the dependent basis equations can be stated
-- with the existing coordinate lattice and twenty-four-element index.
@[expose] def chevalleyDatum : ChevalleyDatum (.D 4) (by decide) where
  carrier := Fin 24 → ℚ
  representation := pinnedRep
  injective_representation_ι := by exact pinnedRep_injective
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := by exact pinnedRep_mem_lattice
  span_lattice_eq_top := by
    rw [lattice_def]
    exact Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := 24
  basis := latticeBasis
  weight := fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i)
  isCartanWeightVector_basis a := by
    -- Specify the rational-space coercion: the datum stores the lattice as an additive subgroup.
    rw [show (latticeBasis a : Fin 24 → ℚ) = Pi.single a 1 from coe_latticeBasis a]
    exact pinnedRep_weight a
  weightLatticeBasis := (Pi.basisFun ℤ (Fin 4)).map
    (LinearEquiv.ofTop _ span_range_d4TripledWeight_eq_top).symm

/-- The tripled datum uses the pinned rational action. -/
@[simp] theorem chevalleyDatum_representation : chevalleyDatum.representation = pinnedRep := (rfl)

/-- The tripled datum uses the existing coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice : chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The tripled datum uses the existing coordinate basis. -/
@[simp] theorem chevalleyDatum_basis : chevalleyDatum.basis = latticeBasis := (rfl)

/-- The tripled datum retains the numbered tripled weights. -/
@[simp] theorem chevalleyDatum_weight :
    chevalleyDatum.weight = fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i) := (rfl)

/-- The tripled datum has the full simply connected weight lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ := by
  rw [ChevalleyDatum.weightLattice_def, chevalleyDatum_weight]
  exact span_range_d4TripledWeight_eq_top

/-- The character basis is the standard fundamental-weight basis. -/
@[simp↓] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.D 4).rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin (DynkinType.D 4).rank → ℤ) = Pi.single i 1 := by
  -- Normalize the native rank before applying the basis map's evaluation equation.
  dsimp only [chevalleyDatum]
  have h := Module.Basis.map_apply (Pi.basisFun ℤ (Fin 4))
    (LinearEquiv.ofTop _ span_range_d4TripledWeight_eq_top).symm (Fin.cast (rank_D 4) i)
  refine (congrArg Subtype.val h).trans ?_
  simp only [LinearEquiv.ofTop_symm_apply, Pi.basisFun_apply]
  -- The remaining transport is only the reflexive equality of the native rank with four.
  rfl

/-- The torus coordinates of the tripled datum are its original fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    chevalleyDatum.coordinateWeight = fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i) := by
  ext j i
  have h := congrFun (chevalleyDatum.sum_coordinateWeight_smul j) i
  simpa only [coe_chevalleyDatum_weightLatticeBasis, ← Pi.single_smul', smul_eq_mul,
    mul_one, Finset.univ_sum_single, chevalleyDatum_weight] using h

/-- The coordinate roots are the original roots in fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin (DynkinType.D 4).numRoots) :
    chevalleyDatum.coordinateRoot γ =
      ((DynkinType.D 4).simplyConnectedRootDatum (by decide)).root γ := by
  ext i
  have h := congrFun (chevalleyDatum.sum_coordinateRoot_smul γ) i
  simpa only [coe_chevalleyDatum_weightLatticeBasis, ← Pi.single_smul', smul_eq_mul,
    mul_one, Finset.univ_sum_single] using h

end

end TauCeti.D4Tripled
