/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Representation

/-!
# Chevalley data from minuscule weight tables

A minuscule weight table for the transposed Cartan matrix of a valid Dynkin type gives a
representation of its pinned rational Lie algebra through `DynkinType.serreLiftEquiv`.
The coordinate lattice is admissible. If the weights span the full weight lattice, this
representation is faithful and defines a full-weight Chevalley datum.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

open DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

section Transport

variable {t : DynkinType} {ι : Type*} [Fintype ι] [DecidableEq ι]
  (T : MinusculeWeightTable (Fin t.rank) ι) (ht : t.Valid)
  (hCM : T.cartanMatrix = t.cartanMatrixᵀ)

/-- The table representation transported to the pinned Lie algebra and extended to its
universal enveloping algebra. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ (ι → ℚ) :=
  DynkinType.serreRepresentation ht hCM T.rep

/-- The pinned action is the Serre transport of the existing table representation. -/
theorem pinnedRepresentation_def :
    T.pinnedRepresentation ht hCM = DynkinType.serreRepresentation ht hCM T.rep := (rfl)

/-- The pinned Cartan generator acts by the table's diagonal weight matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_h_apply (i : Fin t.rank) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).h i)) v = T.cartanGeneratorMatrixQ i *ᵥ v := by
  rw [pinnedRepresentation, serreRepresentation_ι_lieBasis_h, T.rep_ι_apply,
    T.rationalSerreRepresentation_serreH]

/-- The pinned positive generator acts by the table's raising matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_e_apply (i : Fin t.rank) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).e i)) v = T.raisingMatrixQ i *ᵥ v := by
  rw [pinnedRepresentation, serreRepresentation_ι_lieBasis_e, T.rep_ι_apply,
    T.rationalSerreRepresentation_serreE]

/-- The pinned negative generator acts by the table's lowering matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_f_apply (i : Fin t.rank) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).f i)) v = T.loweringMatrixQ i *ᵥ v := by
  rw [pinnedRepresentation, serreRepresentation_ι_lieBasis_f, T.rep_ι_apply,
    T.rationalSerreRepresentation_serreF]

/-- The coordinate basis vectors retain the table's Cartan weights under transport. -/
theorem isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis (a : ι) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (t.lieBasis ht).h
      (T.pinnedRepresentation ht hCM) (T.weight a) (coordinateLatticeBasis ι a : ι → ℚ) :=
  isCartanWeightVector_serreRepresentation ht hCM T.rep
    (T.isCartanWeightVector_coordinateLatticeBasis a)

/-- The transported action of a pinned root generator agrees with its Serre action. -/
theorem pinnedRepresentation_ι_rootGenerator (k : Fin t.rank ⊕ Fin t.rank) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).rootGenerator k)) =
      T.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (serreRootGenerator T.cartanMatrix k)) :=
  serreRepresentation_ι_rootGenerator ht hCM T.rep k

/-- The coordinate lattice is stable under the pinned simple-generator Kostant form. -/
theorem pinnedRepresentation_kostantForm_mem_coordinateLattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h)
    (v : ι → ℚ) (hv : v ∈ coordinateLattice ι) :
    T.pinnedRepresentation ht hCM u v ∈ coordinateLattice ι :=
  serreRepresentation_kostantForm_mem ht hCM T.rep (coordinateLattice ι).toAddSubgroup
    (fun _ hu _ hv => T.rep_serreKostantForm_mem_lattice hu hv) u hu v hv

/-- Weights spanning the rational weight space make the pinned table representation faithful. -/
theorem pinnedRepresentation_ι_injective
    (hspan : Submodule.span ℚ (Set.range fun a i => (T.weight a i : ℚ)) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht =>
      T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ x) :=
  representation_ι_injective_of_span_range_eq_top ht (T.pinnedRepresentation ht hCM)
    (T.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis ht hCM)
    (fun a => by simpa only [coe_coordinateLatticeBasis] using (Pi.basisFun ℚ ι).ne_zero a)
    hspan

/-- Integral spanning of the table's weights also implies faithfulness of the pinned action. -/
theorem pinnedRepresentation_ι_injective_of_span_int
    (hspan : Submodule.span ℤ (Set.range T.weight) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht =>
      T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ x) :=
  representation_ι_injective_of_span_int ht (T.pinnedRepresentation ht hCM)
    (T.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis ht hCM)
    (fun a => by simpa only [coe_coordinateLatticeBasis] using (Pi.basisFun ℚ ι).ne_zero a)
    hspan

end Transport

variable {t : DynkinType} {d : ℕ} (T : MinusculeWeightTable (Fin t.rank) (Fin d))
  (ht : t.Valid) (hCM : T.cartanMatrix = t.cartanMatrixᵀ)
  (hspan : Submodule.span ℤ (Set.range T.weight) = ⊤)

/-- A minuscule table whose weights span the full weight lattice defines a full-weight
Chevalley datum with its integral coordinate lattice and basis. -/
-- The carrier, dimension and lattice must compute in the types of the projection equations.
@[expose] def chevalleyDatum : ChevalleyDatum t ht where
  carrier := Fin d → ℚ
  representation := T.pinnedRepresentation ht hCM
  injective_representation_ι := T.pinnedRepresentation_ι_injective_of_span_int ht hCM hspan
  lattice := (coordinateLattice (Fin d)).toAddSubgroup
  representation_mem_lattice := T.pinnedRepresentation_kostantForm_mem_coordinateLattice ht hCM
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := d
  basis := coordinateLatticeBasis (Fin d)
  weight := T.weight
  isCartanWeightVector_basis :=
    T.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis ht hCM
  weightLatticeBasis := (Pi.basisFun ℤ (Fin t.rank)).map (LinearEquiv.ofTop _ hspan).symm

/-- The table datum has the table's dimension. -/
@[simp] theorem chevalleyDatum_dim : (T.chevalleyDatum ht hCM hspan).dim = d := rfl

/-- The datum's representation is the pinned table representation. -/
@[simp] theorem chevalleyDatum_representation :
    (T.chevalleyDatum ht hCM hspan).representation = T.pinnedRepresentation ht hCM := rfl

/-- The datum's lattice is the integral coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice :
    (T.chevalleyDatum ht hCM hspan).lattice = (coordinateLattice (Fin d)).toAddSubgroup := rfl

/-- The datum uses the standard integral coordinate basis. -/
@[simp] theorem chevalleyDatum_basis :
    (T.chevalleyDatum ht hCM hspan).basis = coordinateLatticeBasis (Fin d) := rfl

/-- The datum retains the table's weights. -/
@[simp] theorem chevalleyDatum_weight : (T.chevalleyDatum ht hCM hspan).weight = T.weight := rfl

/-- The table datum has the full weight lattice. -/
@[simp] theorem chevalleyDatum_weightLattice :
    (T.chevalleyDatum ht hCM hspan).weightLattice = ⊤ := hspan

/-- The chosen weight-lattice basis is the fundamental-weight basis. -/
@[simp↓] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin t.rank) :
    ((T.chevalleyDatum ht hCM hspan).weightLatticeBasis i : Fin t.rank → ℤ) =
      Pi.single i 1 := by
  rw [chevalleyDatum, Module.Basis.map_apply, LinearEquiv.coe_ofTop_symm_apply,
    Pi.basisFun_apply]

/-- The coordinate weights are the table's fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    (T.chevalleyDatum ht hCM hspan).coordinateWeight = T.weight :=
  (T.chevalleyDatum ht hCM hspan).coordinateWeight_eq_weight
    (T.coe_chevalleyDatum_weightLatticeBasis ht hCM hspan)

/-- The coordinate roots are the pinned fundamental-weight coordinates of the roots. -/
@[simp] theorem chevalleyDatum_coordinateRoot :
    (T.chevalleyDatum ht hCM hspan).coordinateRoot = (t.simplyConnectedRootDatum ht).root :=
  (T.chevalleyDatum ht hCM hspan).coordinateRoot_eq_root
    (T.coe_chevalleyDatum_weightLatticeBasis ht hCM hspan)

end

end TauCeti.MinusculeWeightTable
