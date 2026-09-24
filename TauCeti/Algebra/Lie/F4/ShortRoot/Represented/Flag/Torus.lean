/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Flag.Span
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# Weight-torus stability of the represented modular F4 flag

The short-root weight torus preserves the represented ideal and range in matrix coordinates.
Transporting those two facts through the cotangent-dual matrix equivalence makes its adjoint
coefficient matrix block triangular for the adapted weights `2, 1, 0`.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- Local adjoint comodule on the cotangent dual of `GL₂₆`. -/
local instance : Comodule 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
    f4ShortRootCotangentDual :=
  Derivation.adjointComodule
    (R := 𝔽₂) (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

private theorem f4ShortRootWeightTorusConj_mem_range_generator
    (s : Fin 4 → Aˣ) (k : f4ChevalleyIndex) :
    f4ShortRootWeightTorusConjLinearMap s
        (f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularChevalleyBasis k)) ∈
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  rcases k with α | r
  · let a := f4PinnedRootIndex α
    have hα : f4ModularChevalleyBasis (Sum.inl α) = f4ModularRootVector a := by
      rw [f4ModularRootVector_eq_basis]
      simp only [a, f4KillingRootLabel_f4PinnedRootIndex]
    have hgen :
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularRootVector a) ∈
          f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
      rw [← hα]
      exact f4ShortRootRepresentedRangeMatrixBaseChange_mem_basis (Sum.inl α)
    rw [f4ShortRootWeightTorusConjLinearMap_apply, hα,
      f4ShortRootWeightTorusGL_conj_root]
    exact Submodule.smul_mem _ _ hgen
  · let a : Fin F4.rank := (F4.lieBasis valid_F4).baseSupportEquiv.symm r
    have hr : f4ModularChevalleyBasis (Sum.inr r) = f4ModularSimpleCoroot a := by
      rw [f4ModularSimpleCoroot_eq_basis]
      simp only [a, Equiv.apply_symm_apply]
    have hgen :
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularSimpleCoroot a) ∈
          f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
      rw [← hr]
      exact f4ShortRootRepresentedRangeMatrixBaseChange_mem_basis (Sum.inr r)
    rw [f4ShortRootWeightTorusConjLinearMap_apply, hr,
      f4ShortRootWeightTorusGL_conj_simpleCoroot]
    exact hgen

/-- The base-changed represented range is preserved by every short-root weight-torus point. -/
theorem f4ShortRootWeightTorusConj_mem_representedRange
    (s : Fin 4 → Aˣ) {X : Matrix (Fin 26) (Fin 26) A}
    (hX : X ∈ f4ShortRootRepresentedRangeMatrixBaseChange (A := A)) :
    f4ShortRootWeightTorusConjLinearMap s X ∈
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  have hX' : X ∈ Submodule.span A (Set.range fun k : f4ChevalleyIndex =>
      f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularChevalleyBasis k)) :=
    (f4ShortRootRepresentedRangeMatrixBaseChange_eq_span_basis (A := A)) ▸ hX
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hX'
  · rintro _ ⟨k, rfl⟩
    exact f4ShortRootWeightTorusConj_mem_range_generator s k
  · intro X Y _ _ hX hY
    rw [map_add]
    exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    rw [map_smul]
    exact Submodule.smul_mem _ c hX

private theorem f4ShortRootWeightTorusConj_mem_ideal_generator
    (s : Fin 4 → Aˣ) (i : Fin 26) :
    f4ShortRootWeightTorusConjLinearMap s
        (f4ShortRootAdjointMatrixBaseChange (A := A)
          (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra)) ∈
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  have hgen :
      f4ShortRootAdjointMatrixBaseChange (A := A)
          (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra) ∈
        f4ShortRootRepresentedIdealMatrixBaseChange (A := A) :=
    f4ShortRootRepresentedIdealMatrixBaseChange_mem_basis i
  rcases hi : f4ShortRootWeightIndexEquiv i with α | k
  · have hi' := congrArg f4ShortRootWeightIndexEquiv.symm hi
    simp only [Equiv.symm_apply_apply] at hi'
    have hroot :
        (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra) =
          f4ModularRootVector α := by
      rw [hi', coe_f4ShortRootLieIdealBasis_symm_inl]
    rw [f4ShortRootWeightTorusConjLinearMap_apply, hroot,
      f4ShortRootWeightTorusGL_conj_root]
    exact Submodule.smul_mem _ _ (hroot ▸ hgen)
  · fin_cases k
    · have hi' : i = 12 :=
        (f4ShortRootWeightIndexEquiv_apply_eq_inr_zero_iff i).mp (by simpa using hi)
      subst i
      have hgen' :
          f4ShortRootAdjointMatrixBaseChange (A := A)
              (f4ModularSimpleCoroot (Fin.cast rank_F4.symm (2 : Fin 4))) ∈
            f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
        simpa only [coe_f4ShortRootLieIdealBasis_twelve] using hgen
      rw [f4ShortRootWeightTorusConjLinearMap_apply,
        coe_f4ShortRootLieIdealBasis_twelve,
        f4ShortRootWeightTorusGL_conj_simpleCoroot]
      exact hgen'
    · have hi' : i = 13 :=
        (f4ShortRootWeightIndexEquiv_apply_eq_inr_one_iff i).mp (by simpa using hi)
      subst i
      have hgen' :
          f4ShortRootAdjointMatrixBaseChange (A := A)
              (f4ModularSimpleCoroot (Fin.cast rank_F4.symm (3 : Fin 4))) ∈
            f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
        simpa only [coe_f4ShortRootLieIdealBasis_thirteen] using hgen
      rw [f4ShortRootWeightTorusConjLinearMap_apply,
        coe_f4ShortRootLieIdealBasis_thirteen,
        f4ShortRootWeightTorusGL_conj_simpleCoroot]
      exact hgen'

/-- The base-changed represented ideal is preserved by every short-root weight-torus point. -/
theorem f4ShortRootWeightTorusConj_mem_representedIdeal
    (s : Fin 4 → Aˣ) {X : Matrix (Fin 26) (Fin 26) A}
    (hX : X ∈ f4ShortRootRepresentedIdealMatrixBaseChange (A := A)) :
    f4ShortRootWeightTorusConjLinearMap s X ∈
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  have hX' : X ∈ Submodule.span A (Set.range fun i : Fin 26 =>
      f4ShortRootAdjointMatrixBaseChange (A := A)
        (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra)) :=
    (f4ShortRootRepresentedIdealMatrixBaseChange_eq_span_basis (A := A)) ▸ hX
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hX'
  · rintro _ ⟨i, rfl⟩
    exact f4ShortRootWeightTorusConj_mem_ideal_generator s i
  · intro X Y _ _ hX hY
    rw [map_add]
    exact Submodule.add_mem _ hX hY
  · intro c X _ hX
    rw [map_smul]
    exact Submodule.smul_mem _ c hX


private theorem torus_endOfPoint_mem_ideal
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26 g = f4ShortRootWeightTorusGL s)
    {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual}
    (hx : x ∈ cotangentFlagIdeal (A := A)) :
    Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
      cotangentFlagIdeal (A := A) := by
  let e := f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
  refine e.mem_of_preserves_map
    (cotangentFlagIdeal (A := A))
    (f4ShortRootRepresentedIdealMatrixBaseChange (A := A))
    (f4ShortRootCotangentFlagIdeal_map (A := A))
    (fun y => Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv y)
    (f4ShortRootWeightTorusConjLinearMap s) ?_ ?_ hx
  · intro y
    rw [f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_adjointComodule_endOfPoint,
      hg, f4ShortRootWeightTorusConjLinearMap_apply,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply]
  · intro Y hY
    exact f4ShortRootWeightTorusConj_mem_representedIdeal s hY

private theorem torus_endOfPoint_mem_range
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26 g = f4ShortRootWeightTorusGL s)
    {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual}
    (hx : x ∈ cotangentFlagRange (A := A)) :
    Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
      cotangentFlagRange (A := A) := by
  let e := f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
  refine e.mem_of_preserves_map
    (cotangentFlagRange (A := A))
    (f4ShortRootRepresentedRangeMatrixBaseChange (A := A))
    (f4ShortRootCotangentFlagRange_map (A := A))
    (fun y => Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv y)
    (f4ShortRootWeightTorusConjLinearMap s) ?_ ?_ hx
  · intro y
    rw [f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_adjointComodule_endOfPoint,
      hg, f4ShortRootWeightTorusConjLinearMap_apply,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply]
  · intro Y hY
    exact f4ShortRootWeightTorusConj_mem_representedRange s hY

/-- A point acts block triangularly on the adapted represented flag if it preserves its two
nontrivial steps. -/
theorem f4ShortRoot_adjoint_blockTriangular_of_preserves_flag
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (hIdeal : ∀ {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual},
      x ∈ cotangentFlagIdeal (A := A) →
        Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
          cotangentFlagIdeal (A := A))
    (hRange : ∀ {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual},
      x ∈ cotangentFlagRange (A := A) →
        Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
          cotangentFlagRange (A := A)) :
    ((Comodule.coefficientMatrix
        (C := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
        f4ShortRootCotangentFlagBasis).map g.ofConv).BlockTriangular
      (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) := by
  intro i j hij
  rw [← Comodule.toMatrix_endOfPoint, LinearMap.toMatrix_apply]
  have hweight : f4ShortRootCotangentFlagWeight i <
      f4ShortRootCotangentFlagWeight j := OrderDual.toDual_lt_toDual.mp hij
  by_cases hjIdeal : j.val < f4ShortRootRepresentedIdealRank
  · let j' : Fin f4ShortRootRepresentedIdealRank := ⟨j.val, hjIdeal⟩
    have hj : j = Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 j') :=
      Fin.ext rfl
    have hjmem : f4ShortRootCotangentFlagBasis.baseChange A j ∈
        cotangentFlagIdeal (A := A) := by
      rw [cotangentFlagIdeal_eq_span_basis (A := A)]
      exact Submodule.subset_span ⟨j', by rw [hj]⟩
    have hmap := hIdeal hjmem
    rw [cotangentFlagIdeal_eq_span_basis (A := A)] at hmap
    apply Module.Basis.repr_eq_zero_of_mem_span_range
      (f4ShortRootCotangentFlagBasis.baseChange A)
      (fun i : Fin f4ShortRootRepresentedIdealRank =>
        Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)) hmap
    rintro ⟨i', hi'⟩
    have hiIdeal : i.val < f4ShortRootRepresentedIdealRank := by
      rw [← hi']
      exact i'.isLt
    simp only [f4ShortRootCotangentFlagWeight, hjIdeal, hiIdeal, ↓reduceIte] at hweight
    omega
  · by_cases hjRange : j.val < f4ShortRootRepresentedIdealRank + 26
    · let j' : Fin (f4ShortRootRepresentedIdealRank + 26) := ⟨j.val, hjRange⟩
      have hj : j = Fin.castAdd f4ShortRootRepresentedComplementRank j' := Fin.ext rfl
      have hjmem : f4ShortRootCotangentFlagBasis.baseChange A j ∈
          cotangentFlagRange (A := A) := by
        rw [cotangentFlagRange_eq_span_basis (A := A)]
        exact Submodule.subset_span ⟨j', by rw [hj]⟩
      have hmap := hRange hjmem
      rw [cotangentFlagRange_eq_span_basis (A := A)] at hmap
      apply Module.Basis.repr_eq_zero_of_mem_span_range
        (f4ShortRootCotangentFlagBasis.baseChange A)
        (fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
          Fin.castAdd f4ShortRootRepresentedComplementRank i) hmap
      rintro ⟨i', hi'⟩
      have hiRange : i.val < f4ShortRootRepresentedIdealRank + 26 := by
        rw [← hi']
        exact i'.isLt
      have hjWeight : f4ShortRootCotangentFlagWeight j = 1 := by
        simp [f4ShortRootCotangentFlagWeight, hjIdeal, hjRange]
      have hiWeight : 1 ≤ f4ShortRootCotangentFlagWeight i := by
        by_cases hiIdeal : i.val < f4ShortRootRepresentedIdealRank
        · simp [f4ShortRootCotangentFlagWeight, hiIdeal]
        · simp [f4ShortRootCotangentFlagWeight, hiIdeal, hiRange]
      omega
    · have hjWeight : f4ShortRootCotangentFlagWeight j = 0 := by
        simp [f4ShortRootCotangentFlagWeight, hjIdeal, hjRange]
      have hiNonneg : 0 ≤ f4ShortRootCotangentFlagWeight i := by
        by_cases hiIdeal : i.val < f4ShortRootRepresentedIdealRank
        · simp [f4ShortRootCotangentFlagWeight, hiIdeal]
        · by_cases hiRange : i.val < f4ShortRootRepresentedIdealRank + 26
          · simp [f4ShortRootCotangentFlagWeight, hiIdeal, hiRange]
          · simp [f4ShortRootCotangentFlagWeight, hiIdeal, hiRange]
      omega

/-- Every short-root weight-torus point acts block triangularly on the adapted represented flag. -/
theorem f4ShortRootWeightTorus_adjoint_blockTriangular
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26 g = f4ShortRootWeightTorusGL s) :
    ((Comodule.coefficientMatrix
        (C := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
        f4ShortRootCotangentFlagBasis).map g.ofConv).BlockTriangular
      (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) :=
  f4ShortRoot_adjoint_blockTriangular_of_preserves_flag g
    (torus_endOfPoint_mem_ideal g s hg) (torus_endOfPoint_mem_range g s hg)

end

end TauCeti.DynkinType
