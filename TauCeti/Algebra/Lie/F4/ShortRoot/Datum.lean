/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.F4.ShortRoot.AdmissibleLattice
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.CartanDetector

/-!
# The short-root F₄ Chevalley datum

The twenty-six-dimensional short-root representation has twenty-four nonzero weights and a
specified two-dimensional zero-weight space. This file equips its rational coordinate module
with the independently pinned F₄ Lie-algebra action, using `DynkinType.serreLiftEquiv`, and
packages its existing admissible coordinate lattice as `TauCeti.F4ShortRoot.chevalleyDatum`.
Its weights span the full weight lattice, so its torus coordinates are fundamental-weight
coordinates, with no isogeny kernel in the parametrization.

Faithfulness follows from the short-root weights detecting Cartan coordinates and the
splitting-Cartan faithfulness criterion. Admissibility is transported from
`F4ShortRoot.rep_serreKostantForm_apply_mem_lattice`; in particular, the integral divided
squares of the short-root operators and the chosen zero-weight basis are retained. The datum
is an input to comparisons of integral group schemes, not an identification of its reduction
with a group generated over the prime field.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plate VIII, for the numbering.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3, for admissible lattices and
  Chevalley groups attached to representations.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open DynkinType
open scoped BigOperators

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reindex the generators instead of dependently casting the whole presentation; this follows
-- the rank adapter in the G₂ datum (TauCeti PR #39190), with the F₄ Cartan transpose.
private theorem nativeSerreSystem : IsSerreSystem ℚ DynkinType.F4.cartanMatrix.transpose
    (serreH ℚ CartanMatrix.F₄ᵀ ∘ Fin.cast rank_F4)
    (serreE ℚ CartanMatrix.F₄ᵀ ∘ Fin.cast rank_F4)
    (serreF ℚ CartanMatrix.F₄ᵀ ∘ Fin.cast rank_F4) := by
  have h := (isSerreSystem_serre ℚ CartanMatrix.F₄ᵀ).submatrix
    (f := Fin.cast rank_F4) (Fin.cast_injective _)
  have hCM : CartanMatrix.F₄ᵀ.submatrix (Fin.cast rank_F4) (Fin.cast rank_F4) =
      DynkinType.F4.cartanMatrix.transpose := by
    rw [cartanMatrix_F4]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
    have hi : Fin.cast rank_F4 i = i := Fin.ext (Fin.val_cast rank_F4 i)
    have hj : Fin.cast rank_F4 j = j := Fin.ext (Fin.val_cast rank_F4 j)
    rw [hi, hj]
    -- After removing the rank casts, both sides evaluate the same transposed matrix.
    rfl
  rw [hCM] at h
  exact h

private def pinnedToSerre : DynkinType.F4.lieAlgebra (by trivial) →ₗ⁅ℚ⁆
    Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ :=
  (_root_.TauCeti.serreLift nativeSerreSystem).comp
    (DynkinType.serreLiftEquiv .F4 (by trivial)).symm.toLieHom

private theorem pinnedToSerre_h (i : Fin DynkinType.F4.rank) :
    pinnedToSerre ((DynkinType.lieBasis .F4 (by trivial)).h i) =
      serreH ℚ CartanMatrix.F₄ᵀ (Fin.cast rank_F4 i) := by
  rw [pinnedToSerre, LieHom.comp_apply, LieEquiv.coe_coe,
    DynkinType.serreLiftEquiv_symm_lieBasis_h]
  exact _root_.TauCeti.serreLift_serreH nativeSerreSystem i

private theorem pinnedToSerre_e (i : Fin DynkinType.F4.rank) :
    pinnedToSerre ((DynkinType.lieBasis .F4 (by trivial)).e i) =
      serreE ℚ CartanMatrix.F₄ᵀ (Fin.cast rank_F4 i) := by
  rw [pinnedToSerre, LieHom.comp_apply, LieEquiv.coe_coe,
    DynkinType.serreLiftEquiv_symm_lieBasis_e]
  exact _root_.TauCeti.serreLift_serreE nativeSerreSystem i

private theorem pinnedToSerre_f (i : Fin DynkinType.F4.rank) :
    pinnedToSerre ((DynkinType.lieBasis .F4 (by trivial)).f i) =
      serreF ℚ CartanMatrix.F₄ᵀ (Fin.cast rank_F4 i) := by
  rw [pinnedToSerre, LieHom.comp_apply, LieEquiv.coe_coe,
    DynkinType.serreLiftEquiv_symm_lieBasis_f]
  exact _root_.TauCeti.serreLift_serreF nativeSerreSystem i

/-- The short-root action of the pinned rational F₄ Lie algebra, extended to its enveloping
algebra. The underlying module and its ordered coordinates are unchanged. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ (DynkinType.F4.lieAlgebra (by trivial)) →ₐ[ℚ]
      Module.End ℚ (Fin 26 → ℚ) :=
  rep.comp (UniversalEnvelopingAlgebra.map ℚ pinnedToSerre)

private theorem pinnedRepresentation_ι (x : DynkinType.F4.lieAlgebra (by trivial)) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Matrix.toLinAlgEquiv' (rationalSerreRepresentation (pinnedToSerre x)) := by
  rw [pinnedRepresentation, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι, rep_ι]

/-- The numbered Cartan generators act by the native Cartan matrices. -/
@[simp↓]
theorem pinnedRepresentation_ι_h (i : Fin DynkinType.F4.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 (by trivial)).h i)) =
      Matrix.toLinAlgEquiv' (cartanMatrixRat (Fin.cast rank_F4 i)) := by
  rw [pinnedRepresentation_ι, pinnedToSerre_h,
    rationalSerreRepresentation_serreH]

/-- The numbered positive simple generators act by the native raising matrices. -/
@[simp↓]
theorem pinnedRepresentation_ι_e (i : Fin DynkinType.F4.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 (by trivial)).e i)) =
      Matrix.toLinAlgEquiv' (raisingMatrixRat (Fin.cast rank_F4 i)) := by
  rw [pinnedRepresentation_ι, pinnedToSerre_e,
    rationalSerreRepresentation_serreE]

/-- The numbered negative simple generators act by the native lowering matrices. -/
@[simp↓]
theorem pinnedRepresentation_ι_f (i : Fin DynkinType.F4.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 (by trivial)).f i)) =
      Matrix.toLinAlgEquiv' (loweringMatrixRat (Fin.cast rank_F4 i)) := by
  rw [pinnedRepresentation_ι, pinnedToSerre_f,
    rationalSerreRepresentation_serreF]

/-- A positive root generator acts by the corresponding raising matrix. -/
@[simp↓] theorem pinnedRepresentation_ι_rootGenerator_inl (i : Fin DynkinType.F4.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).rootGenerator (.inl i))) =
      Matrix.toLinAlgEquiv' (raisingMatrixRat (Fin.cast rank_F4 i)) := by
  rw [LieAlgebra.Basis.rootGenerator_inl, pinnedRepresentation_ι_e]

/-- A negative root generator acts by the corresponding lowering matrix. -/
@[simp↓] theorem pinnedRepresentation_ι_rootGenerator_inr (i : Fin DynkinType.F4.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).rootGenerator (.inr i))) =
      Matrix.toLinAlgEquiv' (loweringMatrixRat (Fin.cast rank_F4 i)) := by
  rw [LieAlgebra.Basis.rootGenerator_inr, pinnedRepresentation_ι_f]

/-- The sum-indexed simple root generators act by the native root matrices. -/
@[simp↓ low] theorem pinnedRepresentation_ι_rootGenerator
    (k : Fin DynkinType.F4.rank ⊕ Fin DynkinType.F4.rank) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).rootGenerator k)) =
      Matrix.toLinAlgEquiv' (rootMatrixRat (k.map (Fin.cast rank_F4) (Fin.cast rank_F4))) := by
  cases k <;> simp only [Sum.map_inl, Sum.map_inr, rootMatrixRat_inl, rootMatrixRat_inr,
    pinnedRepresentation_ι_rootGenerator_inl, pinnedRepresentation_ι_rootGenerator_inr]

private theorem pinnedRepresentation_cartan_apply
    (x : DynkinType.F4.cartanSubalgebra (by trivial)) (v : Fin 26 → ℚ) (a : Fin 26) :
    pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (x : DynkinType.F4.lieAlgebra (by trivial))) v a =
      ∑ i : Fin DynkinType.F4.rank, (DynkinType.cartanBasis .F4 (by trivial)).repr x i *
        (f4ShortRootWeight a (Fin.cast rank_F4 i) : ℚ) * v a := by
  let f := (pinnedRepresentation.toLinearMap.comp
    (_root_.UniversalEnvelopingAlgebra.ι ℚ).toLinearMap).comp
      (DynkinType.F4.cartanSubalgebra valid_F4).subtype
  have hx := congrArg (fun T : Module.End ℚ (Fin 26 → ℚ) => T v a)
    (congrArg f ((DynkinType.cartanBasis .F4 valid_F4).sum_repr x))
  -- Evaluate a linear map on the Cartan basis instead of unfolding the matrix Lie algebra.
  simp only [map_sum, map_smul] at hx
  simp only [f, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    Submodule.subtype_apply, AlgHom.toLinearMap_apply, coe_cartanBasis,
    pinnedRepresentation_ι_h] at hx
  simpa [Matrix.mulVec, dotProduct, mul_assoc] using hx.symm

/-- The pinned short-root action is faithful on the rational Lie algebra. -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective (fun x : DynkinType.F4.lieAlgebra (by trivial) =>
      pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) := by
  let ρ := pinnedRepresentation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let := LieRingModule.compLieHom (Fin 26 → ℚ) ρ
  let := LieModule.compLieHom (Fin 26 → ℚ) ρ
  have hbracket (y : DynkinType.F4.lieAlgebra valid_F4) (v : Fin 26 → ℚ) :
      ⁅y, v⁆ = pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ y) v := by
    simp only [ρ, LieRingModule.compLieHom_apply, LieHom.comp_apply,
      AlgHom.toLieHom_apply, Module.End.lie_apply]
  have : LieModule.IsFaithful ℚ (DynkinType.F4.cartanSubalgebra (by trivial))
      (Fin 26 → ℚ) := by
    rw [LieModule.isFaithful_iff']
    intro x hx
    have hc : (fun i : Fin 4 =>
        (DynkinType.cartanBasis .F4 (by trivial)).repr x (Fin.cast rank_F4.symm i)) = 0 := by
      apply eq_zero_of_f4ShortRootWeight_smul_eq_zero
      intro a
      have ha := hx (Pi.single a 1)
      rw [LieSubalgebra.coe_bracket_of_module, hbracket] at ha
      have ha := congrFun ha a
      simp only [Pi.zero_apply] at ha
      rw [pinnedRepresentation_cartan_apply] at ha
      have hsum := Fintype.sum_equiv (finCongr rank_F4)
        (fun i => (DynkinType.cartanBasis .F4 (by trivial)).repr x i *
          (f4ShortRootWeight a (Fin.cast rank_F4 i) : ℚ))
        (fun i => (f4ShortRootWeight a i : ℚ) *
          (DynkinType.cartanBasis .F4 (by trivial)).repr x (Fin.cast rank_F4.symm i))
        (by intro i; simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq, mul_comm])
      simp only [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
      simpa only [Pi.single_eq_same, mul_one, ← Finset.sum_mul, hsum] using ha
    apply (DynkinType.cartanBasis .F4 valid_F4).repr.injective
    simp only [map_zero]
    ext i
    have hi := congrFun hc (Fin.cast rank_F4 i)
    simpa only [Fin.cast_cast, Fin.cast_refl, id_eq, Pi.zero_apply, Finsupp.zero_apply] using hi
  have := isFaithful_of_isFaithful_cartanSubalgebra
    (H := DynkinType.F4.cartanSubalgebra valid_F4) (M := Fin 26 → ℚ)
  have haction : LieModule.toEnd ℚ (DynkinType.F4.lieAlgebra valid_F4) (Fin 26 → ℚ) =
      fun y => pinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ y) := by
    funext y
    exact LinearMap.ext fun v => (LieModule.toEnd_apply_apply ℚ _ _ y v).trans (hbracket y v)
  rw [← haction]
  exact LieModule.IsFaithful.injective_toEnd (R := ℚ)
    (L := DynkinType.F4.lieAlgebra valid_F4) (M := Fin 26 → ℚ)

private theorem pinnedRepresentation_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (DynkinType.F4.lieAlgebra valid_F4)}
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      (LieAlgebra.Basis.rootGenerator (DynkinType.lieBasis .F4 valid_F4))
      (DynkinType.lieBasis .F4 valid_F4).h) {v : Fin 26 → ℚ} (hv : v ∈ lattice) :
    pinnedRepresentation u v ∈ lattice := by
  rw [pinnedRepresentation, AlgHom.comp_apply]
  apply rep_serreKostantForm_apply_mem_lattice (hv := hv)
  have hmap : UniversalEnvelopingAlgebra.map ℚ pinnedToSerre u ∈
      (UniversalEnvelopingAlgebra.kostantForm
        (DynkinType.lieBasis .F4 (by trivial)).rootGenerator
        (DynkinType.lieBasis .F4 (by trivial)).h).map
          (UniversalEnvelopingAlgebra.map ℚ pinnedToSerre).toRingHom := ⟨u, hu, rfl⟩
  rw [UniversalEnvelopingAlgebra.map_kostantForm] at hmap
  apply (UniversalEnvelopingAlgebra.kostantForm_le_iff _ _ _).mpr ?_ hmap
  constructor
  · rintro (i | i) n <;>
      simp only [LieAlgebra.Basis.rootGenerator_inl, LieAlgebra.Basis.rootGenerator_inr,
        pinnedToSerre_e, pinnedToSerre_f]
    · exact dividedPower_serreE_mem CartanMatrix.F₄ᵀ (Fin.cast rank_F4 i) n
    · exact dividedPower_serreF_mem CartanMatrix.F₄ᵀ (Fin.cast rank_F4 i) n
  · intro i n
    rw [pinnedToSerre_h]
    exact ringChoose_serreH_mem CartanMatrix.F₄ᵀ (Fin.cast rank_F4 i) n

private theorem isCartanWeightVector_pinned (a : Fin 26) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector
      (DynkinType.lieBasis .F4 valid_F4).h pinnedRepresentation
      (fun i => f4ShortRootWeight a (Fin.cast rank_F4 i))
      ((latticeBasis a : lattice) : Fin 26 → ℚ) := by
  rw [UniversalEnvelopingAlgebra.isCartanWeightVector_iff]
  intro i
  rw [pinnedRepresentation_ι_h]
  have h := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_latticeBasis a) (Fin.cast rank_F4 i)
  simpa only [rep_ι, rationalSerreRepresentation_serreH] using h

private theorem span_range_pinnedWeight_eq_top :
    Submodule.span ℤ (Set.range (fun (a : Fin 26) (i : Fin DynkinType.F4.rank) =>
      f4ShortRootWeight a (Fin.cast rank_F4 i))) = ⊤ := by
  let e := LinearEquiv.funCongrLeft ℤ ℤ (finCongr rank_F4)
  have hrange : Set.range (fun (a : Fin 26) (i : Fin DynkinType.F4.rank) =>
      f4ShortRootWeight a (Fin.cast rank_F4 i)) = e '' Set.range f4ShortRootWeight := by
    have he (a : Fin 26) : e (f4ShortRootWeight a) =
        fun i => f4ShortRootWeight a (Fin.cast rank_F4 i) := by
      ext i
      simp only [e, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, finCongr_apply]
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a => (he a).symm)
  rw [hrange, Submodule.span_image_linearEquiv, span_range_f4ShortRootWeight_eq_top,
    Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

/-- The full-weight Chevalley datum on the twenty-six-dimensional short-root module, with its
specified integral coordinate basis, including the two zero-weight vectors. -/
-- This concrete datum is reducible so that its carrier and module instances compute when
-- applying the native coordinate endomorphisms and basis; a merely exposed definition leaves
-- those dependent applications stuck at implicit transparency.
abbrev chevalleyDatum : DynkinType.ChevalleyDatum .F4 (by trivial) where
  carrier := Fin 26 → ℚ
  representation := pinnedRepresentation
  injective_representation_ι := pinnedRepresentation_ι_injective
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := by exact fun _ hu _ hv => pinnedRepresentation_mem_lattice hu hv
  span_lattice_eq_top := by
    apply top_unique
    rw [← (Pi.basisFun ℚ (Fin 26)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact mem_lattice_iff.mpr fun j => ⟨if j = a then 1 else 0, by
      simp [Pi.basisFun_apply, Pi.single_apply]⟩
  dim := 26
  basis := latticeBasis
  weight a i := f4ShortRootWeight a (Fin.cast rank_F4 i)
  isCartanWeightVector_basis := by exact isCartanWeightVector_pinned
  weightLatticeBasis := (Pi.basisFun ℤ (Fin DynkinType.F4.rank)).map
    (LinearEquiv.ofTop _ (by exact span_range_pinnedWeight_eq_top)).symm

/-- The datum's Cartan generator acts by the native diagonal matrix. -/
@[simp↓] theorem chevalleyDatum_representation_h (i : Fin DynkinType.F4.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).h i)) =
      Matrix.toLinAlgEquiv' (cartanMatrixRat (Fin.cast rank_F4 i)) :=
  pinnedRepresentation_ι_h i

/-- The datum's positive simple generator acts by the native raising matrix. -/
@[simp↓] theorem chevalleyDatum_representation_e (i : Fin DynkinType.F4.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).e i)) =
      Matrix.toLinAlgEquiv' (raisingMatrixRat (Fin.cast rank_F4 i)) :=
  pinnedRepresentation_ι_e i

/-- The datum's negative simple generator acts by the native lowering matrix. -/
@[simp↓] theorem chevalleyDatum_representation_f (i : Fin DynkinType.F4.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).f i)) =
      Matrix.toLinAlgEquiv' (loweringMatrixRat (Fin.cast rank_F4 i)) :=
  pinnedRepresentation_ι_f i

/-- The datum's positive root generator acts by the native raising matrix. -/
@[simp↓] theorem chevalleyDatum_representation_rootGenerator_inl
    (i : Fin DynkinType.F4.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).rootGenerator (.inl i))) =
      Matrix.toLinAlgEquiv' (raisingMatrixRat (Fin.cast rank_F4 i)) :=
  pinnedRepresentation_ι_rootGenerator_inl i

/-- The datum's negative root generator acts by the native lowering matrix. -/
@[simp↓] theorem chevalleyDatum_representation_rootGenerator_inr
    (i : Fin DynkinType.F4.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).rootGenerator (.inr i))) =
      Matrix.toLinAlgEquiv' (loweringMatrixRat (Fin.cast rank_F4 i)) :=
  pinnedRepresentation_ι_rootGenerator_inr i

/-- The datum's sum-indexed root generators act by the native root matrices. -/
@[simp↓ low] theorem chevalleyDatum_representation_rootGenerator
    (k : Fin DynkinType.F4.rank ⊕ Fin DynkinType.F4.rank) :
    chevalleyDatum.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
      ((DynkinType.lieBasis .F4 valid_F4).rootGenerator k)) =
      Matrix.toLinAlgEquiv' (rootMatrixRat (k.map (Fin.cast rank_F4) (Fin.cast rank_F4))) :=
  pinnedRepresentation_ι_rootGenerator k

/-- A datum basis vector is the corresponding rational coordinate vector. -/
@[simp↓] theorem coe_chevalleyDatum_basis (a : Fin 26) :
    ((chevalleyDatum.basis a).val : Fin 26 → ℚ) = Pi.single a 1 :=
  coe_latticeBasis a

/-- The chosen character basis consists of the fundamental weights. -/
@[simp↓] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin DynkinType.F4.rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin DynkinType.F4.rank → ℤ) = Pi.single i 1 := by
  rw [chevalleyDatum, Module.Basis.map_apply]
  simp only [LinearEquiv.coe_ofTop_symm_apply, Pi.basisFun_apply]

/-- The weights of the short-root datum span the full weight lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ :=
  chevalleyDatum.weightLattice_def.trans span_range_pinnedWeight_eq_top

/-- The actual torus coordinates of the datum are the native fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    chevalleyDatum.coordinateWeight = fun a i => f4ShortRootWeight a (Fin.cast rank_F4 i) := by
  ext a i
  have h := chevalleyDatum.sum_coordinateWeight_smul a
  conv_lhs at h =>
    arg 2
    ext j
    rw [coe_chevalleyDatum_weightLatticeBasis]
  simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single] at h
  exact congrFun h i

/-- Root characters use the pinned root datum's fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin DynkinType.F4.numRoots) :
    chevalleyDatum.coordinateRoot γ =
      (DynkinType.F4.simplyConnectedRootDatum valid_F4).root γ := by
  ext i
  have h := chevalleyDatum.sum_coordinateRoot_smul γ
  conv_lhs at h =>
    arg 2
    ext j
    rw [coe_chevalleyDatum_weightLatticeBasis]
  simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single] at h
  exact congrFun h i

end

end TauCeti.F4ShortRoot
