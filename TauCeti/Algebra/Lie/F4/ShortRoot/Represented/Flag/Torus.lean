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

/-- The cotangent-dual adjoint module of `GL₂₆` over `ZMod 2`. -/
abbrev f4ShortRootCotangentDual :=
  Module.Dual 𝔽₂
    (Bialgebra.CotangentSpace 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26))

local instance : Comodule 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
    f4ShortRootCotangentDual :=
  Derivation.adjointComodule
    (R := 𝔽₂) (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

@[expose] noncomputable def cotangentFlagIdeal :
    Submodule A (TensorProduct 𝔽₂ A f4ShortRootCotangentDual) :=
  Submodule.span A <| Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
    f4ShortRootCotangentFlagBasis.baseChange A
      (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i))

@[expose] noncomputable def cotangentFlagRange :
    Submodule A (TensorProduct 𝔽₂ A f4ShortRootCotangentDual) :=
  Submodule.span A <| Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
    f4ShortRootCotangentFlagBasis.baseChange A
      (Fin.castAdd f4ShortRootRepresentedComplementRank i)

omit [Algebra 𝔽₂ A] in
private theorem mem_of_equiv_mem_map
    {V W : Type*} [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
    (e : V ≃ₗ[A] W) (p : Submodule A V) {x : V}
    (hx : e x ∈ p.map e.toLinearMap) : x ∈ p := by
  obtain ⟨y, hy, hey⟩ := Submodule.mem_map.mp hx
  exact e.injective hey ▸ hy

private theorem basis_repr_eq_zero_of_mem_span_range
    {R V ι κ : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis ι R V) (e : κ → ι) {x : V} {i : ι}
    (hx : x ∈ Submodule.span R (Set.range fun k => b (e k)))
    (hi : i ∉ Set.range e) : b.repr x i = 0 := by
  have hset : Set.range (fun k => b (e k)) = b '' Set.range e := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e k, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  have hx' : x ∈ Submodule.span R (b '' Set.range e) := by
    rw [← hset]
    exact hx
  have hsupp := b.mem_span_image.mp hx'
  exact Finsupp.notMem_support_iff.mp fun himem => hi (hsupp himem)

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
  have hex : e x ∈ f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
    rw [← f4ShortRootCotangentFlagIdeal_map]
    exact Submodule.mem_map_of_mem hx
  have hstable := f4ShortRootWeightTorusConj_mem_representedIdeal s hex
  have heq :
      e (Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x) =
        f4ShortRootWeightTorusConjLinearMap s (e x) := by
    rw [f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_adjointComodule_endOfPoint,
      hg, f4ShortRootWeightTorusConjLinearMap_apply,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply]
  have hmap : (cotangentFlagIdeal (A := A)).map e.toLinearMap =
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
    simpa only [cotangentFlagIdeal, e] using
      (f4ShortRootCotangentFlagIdeal_map (A := A))
  apply mem_of_equiv_mem_map e (cotangentFlagIdeal (A := A))
  rw [heq, hmap]
  exact hstable

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
  have hex : e x ∈ f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
    rw [← f4ShortRootCotangentFlagRange_map]
    exact Submodule.mem_map_of_mem hx
  have hstable := f4ShortRootWeightTorusConj_mem_representedRange s hex
  have heq :
      e (Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x) =
        f4ShortRootWeightTorusConjLinearMap s (e x) := by
    rw [f4ShortRootCotangentBaseChangeMatrixEquiv_apply,
      GeneralLinear.tangentMatrix_adjointComodule_endOfPoint,
      hg, f4ShortRootWeightTorusConjLinearMap_apply,
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply]
  have hmap : (cotangentFlagRange (A := A)).map e.toLinearMap =
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
    simpa only [cotangentFlagRange, e] using
      (f4ShortRootCotangentFlagRange_map (A := A))
  apply mem_of_equiv_mem_map e (cotangentFlagRange (A := A))
  rw [heq, hmap]
  exact hstable

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
      exact Submodule.subset_span ⟨j', by rw [hj]⟩
    have hmap := hIdeal hjmem
    apply basis_repr_eq_zero_of_mem_span_range
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
        exact Submodule.subset_span ⟨j', by rw [hj]⟩
      have hmap := hRange hjmem
      apply basis_repr_eq_zero_of_mem_span_range
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
