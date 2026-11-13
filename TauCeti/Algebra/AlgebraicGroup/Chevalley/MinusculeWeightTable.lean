/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Full-weight Chevalley data from minuscule weight tables

A numbered minuscule weight table whose Cartan matrix is the transpose of the pinned
Dynkin matrix acts on the pinned rational Lie algebra through `DynkinType.serreLiftEquiv`.
If its weights span the full integral weight lattice, this action is faithful and its
coordinate lattice gives a full-weight Chevalley datum.

The construction reuses the table's Serre relations, square-zero root operators and
integral coordinate lattice. Faithfulness is detected on the splitting Cartan subalgebra
by `TauCeti.isFaithful_of_isFaithful_cartanSubalgebra`; the spanning hypothesis detects
all Cartan coordinates. Lattice stability uses
`UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18, 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.MinusculeWeightTable

open DynkinType
open scoped _root_.Matrix
open _root_.UniversalEnvelopingAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {α : Type} [Fintype α] [DecidableEq α]
    (T : MinusculeWeightTable (Fin t.rank) α) (ht : t.Valid)
    (hT : T.cartanMatrix = t.cartanMatrixᵀ)

include hT in
private theorem pinnedSerreSystem :
    IsSerreSystem ℚ t.cartanMatrixᵀ T.cartanGeneratorMatrixQ
      T.raisingMatrixQ T.loweringMatrixQ := by
  rw [← hT]
  exact T.isSerreSystemQ

/-- The table action pulled back to the pinned rational Lie algebra. -/
def pinnedAction : t.lieAlgebra ht →ₗ⁅ℚ⁆ Module.End ℚ (α → ℚ) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toLieHom.comp
    ((TauCeti.serreLift (T.pinnedSerreSystem hT)).comp (t.serreLiftEquiv ht).symm.toLieHom)

/-- The pinned table action extended to the enveloping algebra. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ]
      Module.End ℚ (α → ℚ) :=
  lift ℚ (T.pinnedAction ht hT)

/-- The enveloping representation restricts to the pinned Lie algebra action. -/
-- The generator equations below, rather than the abstract action, are the simp normal forms.
theorem pinnedRep_ι (x : t.lieAlgebra ht) :
    T.pinnedRep ht hT (ι ℚ x) = T.pinnedAction ht hT x :=
  lift_ι_apply _ _ _

private theorem toLinAlgEquiv'_eq_toLin' (M : Matrix α α ℚ) :
    Matrix.toLinAlgEquiv' M = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

/-- A pinned Cartan generator acts by the table's diagonal weight matrix. -/
@[simp↓]
theorem pinnedRep_h (i : Fin t.rank) :
    T.pinnedRep ht hT (ι ℚ ((t.lieBasis ht).h i)) =
      Matrix.toLin' (T.cartanGeneratorMatrixQ i) := by
  rw [pinnedRep_ι]
  simp only [pinnedAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    serreLiftEquiv_symm_lieBasis_h, TauCeti.serreLift_serreH, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, toLinAlgEquiv'_eq_toLin']

/-- A pinned raising generator acts by the table's raising matrix. -/
@[simp↓]
theorem pinnedRep_e (i : Fin t.rank) :
    T.pinnedRep ht hT (ι ℚ ((t.lieBasis ht).e i)) =
      Matrix.toLin' (T.raisingMatrixQ i) := by
  rw [pinnedRep_ι]
  simp only [pinnedAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    serreLiftEquiv_symm_lieBasis_e, TauCeti.serreLift_serreE, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, toLinAlgEquiv'_eq_toLin']

/-- A pinned lowering generator acts by the table's lowering matrix. -/
@[simp↓]
theorem pinnedRep_f (i : Fin t.rank) :
    T.pinnedRep ht hT (ι ℚ ((t.lieBasis ht).f i)) =
      Matrix.toLin' (T.loweringMatrixQ i) := by
  rw [pinnedRep_ι]
  simp only [pinnedAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    serreLiftEquiv_symm_lieBasis_f, TauCeti.serreLift_serreF, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, toLinAlgEquiv'_eq_toLin']

private theorem pinnedRep_root (k : Fin t.rank ⊕ Fin t.rank) :
    T.pinnedRep ht hT (ι ℚ ((t.lieBasis ht).rootGenerator k)) =
      T.rep (ι ℚ (serreRootGenerator T.cartanMatrix k)) := by
  cases k with
  | inl i =>
    simp only [LieAlgebra.Basis.rootGenerator_inl, pinnedRep_e,
      TauCeti.serreRootGenerator_inl]
    apply LinearMap.ext
    intro v
    rw [T.rep_ι_apply, T.rationalSerreRepresentation_serreE]
    exact Matrix.toLin'_apply _ _
  | inr i =>
    simp only [LieAlgebra.Basis.rootGenerator_inr, pinnedRep_f,
      TauCeti.serreRootGenerator_inr]
    apply LinearMap.ext
    intro v
    rw [T.rep_ι_apply, T.rationalSerreRepresentation_serreF]
    exact Matrix.toLin'_apply _ _

/-- Each coordinate vector is a weight vector for the pinned action, with its table weight. -/
theorem pinnedRep_weight (a : α) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (t.lieBasis ht).h
      (T.pinnedRep ht hT) (T.weight a) (Pi.single a 1) := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  rw [pinnedRep_h, Matrix.toLin'_apply]
  have h := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (T.isCartanWeightVector_single a) i
  rw [T.rep_ι_apply, T.rationalSerreRepresentation_serreH] at h
  exact h

private theorem pinnedRep_cartan_single (x : t.cartanSubalgebra ht) (a : α) :
    T.pinnedRep ht hT (ι ℚ (x : t.lieAlgebra ht)) (Pi.single a 1) a =
      ∑ i, (t.cartanBasis ht).repr x i * (T.weight a i : ℚ) := by
  let b := t.cartanBasis ht
  let f := (t.cartanSubalgebra ht).toSubmodule.subtype
  have hexp : (x : t.lieAlgebra ht) = ∑ i, b.repr x i • (t.lieBasis ht).h i := by
    calc
      (x : t.lieAlgebra ht) = f (∑ i, b.repr x i • b i) :=
        congrArg f (b.sum_repr x).symm
      _ = _ := by
        simp only [map_sum, map_smul]
        simp only [f, Submodule.subtype_apply, b, coe_cartanBasis]
  rw [hexp]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp (T.pinnedRep_weight ht hT a),
    Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, b]

/-- Spanning weights detect every Cartan coordinate, so the pinned Cartan action is faithful. -/
theorem pinnedAction_cartan_isFaithful (hspan : Submodule.span ℤ (Set.range T.weight) = ⊤) :
    let pinnedLieRingModule := LieRingModule.compLieHom (α → ℚ) (T.pinnedAction ht hT)
    let pinnedLieModule := LieModule.compLieHom (α → ℚ) (T.pinnedAction ht hT)
    LieModule.IsFaithful ℚ (t.cartanSubalgebra ht) (α → ℚ) := by
  rw [LieModule.isFaithful_iff']
  intro x hx
  let c : Fin t.rank → ℚ := (t.cartanBasis ht).repr x
  have heval (a : α) : ∑ i, c i * (T.weight a i : ℚ) = 0 := by
    have h := hx (Pi.single a 1)
    have hact : T.pinnedRep ht hT (ι ℚ (x : t.lieAlgebra ht)) (Pi.single a 1) = 0 := by
      rw [pinnedRep_ι]
      exact h
    have hscalar := congrFun hact a
    rw [pinnedRep_cartan_single] at hscalar
    exact hscalar
  let f : (Fin t.rank → ℤ) →ₗ[ℤ] ℚ :=
    ∑ i, (c i) • ((Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj i))
  have hf (μ : Fin t.rank → ℤ) : f μ = ∑ i, c i * (μ i : ℚ) := by
    simp [f]
  have hzero : ∀ μ ∈ Submodule.span ℤ (Set.range T.weight), f μ = 0 :=
    LinearMap.eqOn_span (f := f) (g := 0) (by rintro _ ⟨a, rfl⟩; simpa [hf] using heval a)
  have hc (i : Fin t.rank) : c i = 0 := by
    have h := hzero (Pi.single i 1) (by rw [hspan]; trivial)
    simpa [hf, Pi.single_apply, Finset.mem_univ] using h
  apply (t.cartanBasis ht).repr.injective
  ext i
  simpa only [map_zero, Finsupp.zero_apply] using hc i

/-- A table with spanning weights gives a faithful action of the pinned Lie algebra. -/
theorem pinnedRep_injective (hspan : Submodule.span ℤ (Set.range T.weight) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht => T.pinnedRep ht hT (ι ℚ x) := by
  let pinnedLieRingModule := LieRingModule.compLieHom (α → ℚ) (T.pinnedAction ht hT)
  let pinnedLieModule := LieModule.compLieHom (α → ℚ) (T.pinnedAction ht hT)
  have hCartan := T.pinnedAction_cartan_isFaithful ht hT hspan
  have hFaithful : LieModule.IsFaithful ℚ (t.lieAlgebra ht) (α → ℚ) :=
    isFaithful_of_isFaithful_cartanSubalgebra (H := t.cartanSubalgebra ht)
  intro x y hxy
  apply hFaithful.injective_toEnd
  dsimp only at hxy
  rw [pinnedRep_ι, pinnedRep_ι] at hxy
  exact hxy

/-- The pinned representation preserves the coordinate lattice under the Kostant form. -/
theorem pinnedRep_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h) (v : α → ℚ) (hv : v ∈ coordinateLattice α) :
    T.pinnedRep ht hT u v ∈ coordinateLattice α := by
  apply UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    _ _ (T.pinnedRep ht hT) (wt := T.weight) _ _ (T.pinnedRep_weight ht hT) hu hv
  · intro k
    rw [pinnedRep_root]
    exact T.rep_serreRootGenerator_pow_two _
  · intro k w hw
    rw [pinnedRep_root]
    exact T.rep_serreRootGenerator_mem_lattice _ hw

/-- The full-weight Chevalley datum of a numbered minuscule table with spanning weights.
The lattice is the coordinate lattice, and the character basis is the fundamental-weight basis.
Its weight basis is numbered using `Fintype.equivFin`. -/
-- Expose the carrier and dimension so dependent coordinate-space and basis equations compute.
@[expose] def chevalleyDatum (hspan : Submodule.span ℤ (Set.range T.weight) = ⊤) :
    ChevalleyDatum t ht where
  carrier := α → ℚ
  representation := T.pinnedRep ht hT
  injective_representation_ι := T.pinnedRep_injective ht hT hspan
  lattice := (coordinateLattice α).toAddSubgroup
  representation_mem_lattice := by exact T.pinnedRep_mem_lattice ht hT
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := Fintype.card α
  basis := (coordinateLatticeBasis α).reindex (Fintype.equivFin α)
  weight := T.weight ∘ (Fintype.equivFin α).symm
  isCartanWeightVector_basis a := by
    rw [Module.Basis.reindex_apply, coe_coordinateLatticeBasis, Pi.basisFun_apply]
    exact T.pinnedRep_weight ht hT _
  weightLatticeBasis := (Pi.basisFun ℤ (Fin t.rank)).map
    (LinearEquiv.ofTop _ (by simpa only [EquivLike.range_comp] using hspan)).symm

end

end TauCeti.MinusculeWeightTable
