/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Weights.Basic
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

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

private def tableRepresentation : t.SerreLieAlgebra →ₗ⁅ℚ⁆ Matrix ι ι ℚ :=
  TauCeti.serreLift (by rw [← hCM]; exact T.isSerreSystemQ)

/-- The table representation transported to the pinned Lie algebra and extended to its
universal enveloping algebra. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ (ι → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    ((Matrix.toLinAlgEquiv' (R := ℚ) (n := ι)).toAlgHom.toLieHom.comp
      ((tableRepresentation T hCM).comp (t.serreLiftEquiv ht).symm.toLieHom))

private theorem pinnedRepresentation_ι_apply (x : t.lieAlgebra ht) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      tableRepresentation T hCM ((t.serreLiftEquiv ht).symm x) *ᵥ v := by
  simp only [pinnedRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
    LieHom.comp_apply, LieEquiv.coe_toLieHom, AlgHom.toLieHom_apply,
    AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv'_apply]

/-- The pinned Cartan generator acts by the table's diagonal weight matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_h_apply (i : Fin t.rank) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).h i)) v = T.cartanGeneratorMatrixQ i *ᵥ v := by
  rw [T.pinnedRepresentation_ι_apply, t.serreLiftEquiv_symm_lieBasis_h ht i,
    tableRepresentation, TauCeti.serreLift_serreH]

/-- The pinned positive generator acts by the table's raising matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_e_apply (i : Fin t.rank) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).e i)) v = T.raisingMatrixQ i *ᵥ v := by
  rw [T.pinnedRepresentation_ι_apply, t.serreLiftEquiv_symm_lieBasis_e ht i,
    tableRepresentation, TauCeti.serreLift_serreE]

/-- The pinned negative generator acts by the table's lowering matrix. -/
@[simp↓]
theorem pinnedRepresentation_ι_lieBasis_f_apply (i : Fin t.rank) (v : ι → ℚ) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).f i)) v = T.loweringMatrixQ i *ᵥ v := by
  rw [T.pinnedRepresentation_ι_apply, t.serreLiftEquiv_symm_lieBasis_f ht i,
    tableRepresentation, TauCeti.serreLift_serreF]

/-- The coordinate basis vectors retain the table's Cartan weights under transport. -/
theorem isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis (a : ι) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (t.lieBasis ht).h
      (T.pinnedRepresentation ht hCM) (T.weight a) (coordinateLatticeBasis ι a : ι → ℚ) := by
  refine (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr fun i => ?_
  rw [T.pinnedRepresentation_ι_lieBasis_h_apply]
  simpa only [T.rep_ι_apply, T.rationalSerreRepresentation_serreH] using
    (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
      (T.isCartanWeightVector_coordinateLatticeBasis a) i

/-- The transported action of a pinned root generator agrees with its Serre action. -/
theorem pinnedRepresentation_ι_rootGenerator (k : Fin t.rank ⊕ Fin t.rank) :
    T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((t.lieBasis ht).rootGenerator k)) =
      T.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (serreRootGenerator T.cartanMatrix k)) := by
  apply LinearMap.ext
  intro v
  cases k with
  | inl i =>
    rw [LieAlgebra.Basis.rootGenerator_inl, serreRootGenerator_inl,
      T.pinnedRepresentation_ι_lieBasis_e_apply, T.rep_ι_apply,
      T.rationalSerreRepresentation_serreE]
  | inr i =>
    rw [LieAlgebra.Basis.rootGenerator_inr, serreRootGenerator_inr,
      T.pinnedRepresentation_ι_lieBasis_f_apply, T.rep_ι_apply,
      T.rationalSerreRepresentation_serreF]

/-- The coordinate lattice is stable under the pinned simple-generator Kostant form. -/
theorem pinnedRepresentation_kostantForm_mem_coordinateLattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h)
    (v : ι → ℚ) (hv : v ∈ coordinateLattice ι) :
    T.pinnedRepresentation ht hCM u v ∈ coordinateLattice ι := by
  refine UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice _ _ _
    (wt := T.weight) ?_ ?_ ?_ hu hv
  · intro k
    rw [T.pinnedRepresentation_ι_rootGenerator]
    exact T.rep_serreRootGenerator_pow_two k
  · intro k w hw
    rw [T.pinnedRepresentation_ι_rootGenerator]
    exact T.rep_serreRootGenerator_mem_lattice k hw
  · intro a
    have h := T.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis ht hCM a
    rwa [coe_coordinateLatticeBasis, Pi.basisFun_apply] at h

/-- Weights spanning the rational weight space make the pinned table representation faithful. -/
theorem pinnedRepresentation_ι_injective
    (hspan : Submodule.span ℚ (Set.range fun a i => (T.weight a i : ℚ)) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht =>
      T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  let f := (T.pinnedRepresentation ht hCM).toLieHom.comp
    (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let := LieRingModule.compLieHom (ι → ℚ) f
  let := LieModule.compLieHom (ι → ℚ) f
  let b := t.cartanBasis ht
  let χ := fun a => b.constr ℚ fun i => (T.weight a i : ℚ)
  have hwt (a : ι) : (coordinateLatticeBasis ι a : ι → ℚ) ∈
      LieModule.weightSpace (ι → ℚ) (χ a : t.cartanSubalgebra ht → ℚ) := by
    apply (b.mem_weightSpace_iff_forall_basis _ _).mpr
    intro i
    rw [LieSubalgebra.coe_bracket_of_module, LieRingModule.compLieHom_apply,
      Module.End.lie_apply, LieHom.comp_apply, AlgHom.toLieHom_apply]
    simp only [χ, Module.Basis.constr_basis, b, t.coe_cartanBasis ht]
    exact (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
      (T.isCartanWeightVector_pinnedRepresentation_coordinateLatticeBasis ht hCM a) i
  have hχ : Submodule.span ℚ (Set.range χ) = ⊤ := by
    have hrange : Set.range χ = (b.constr ℚ) ''
        Set.range (fun a i => (T.weight a i : ℚ)) := Set.range_comp _ _
    rw [hrange, Submodule.span_image_linearEquiv, hspan, Submodule.map_top, LinearEquiv.range]
  have : LieModule.IsFaithful ℚ (t.cartanSubalgebra ht) (ι → ℚ) :=
    isFaithful_of_weight_vectors_span hwt
      (fun a => by simpa only [coe_coordinateLatticeBasis] using (Pi.basisFun ℚ ι).ne_zero a) hχ
  have := isFaithful_of_isFaithful_cartanSubalgebra
    (K := ℚ) (L := t.lieAlgebra ht) (M := (ι → ℚ)) (H := t.cartanSubalgebra ht)
  intro x y hxy
  apply LieModule.ext_of_isFaithful (R := ℚ) (ι → ℚ)
  intro v
  simp only [LieRingModule.compLieHom_apply, Module.End.lie_apply, f,
    LieHom.comp_apply, AlgHom.toLieHom_apply]
  exact LinearMap.congr_fun hxy v

/-- Integral spanning of the table's weights also implies faithfulness of the pinned action. -/
theorem pinnedRepresentation_ι_injective_of_span_int
    (hspan : Submodule.span ℤ (Set.range T.weight) = ⊤) :
    Function.Injective fun x : t.lieAlgebra ht =>
      T.pinnedRepresentation ht hCM (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  apply T.pinnedRepresentation_ι_injective ht hCM
  let c : (Fin t.rank → ℤ) →ₗ[ℤ] (Fin t.rank → ℚ) :=
    LinearMap.pi fun i => (Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj i)
  have hc : (fun a i => (T.weight a i : ℚ)) = c ∘ T.weight := by
    funext a i
    rfl
  rw [hc, ← Submodule.span_range_eq_span_range_comp_of_span_eq_top (S := ℚ) hspan c]
  apply top_unique
  rw [← (Pi.basisFun ℚ (Fin t.rank)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  exact ⟨Pi.single i 1, by ext j; simp [c, Pi.single_apply]⟩

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
