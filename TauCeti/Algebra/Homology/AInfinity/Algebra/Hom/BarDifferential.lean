/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.LinearAlgebra.TensorCoalgebra.BlockWord

/-!
# Morphisms and the unary-higher bar differential split

A strict morphism commutes separately with the unary and higher parts of the bar differential, so
it respects the perturbation of the letterwise differential used in homological transfer. For an
arbitrary `A∞` morphism `f : ℬ ⟶ 𝒜`, evaluating `𝒜.higherTaylor ∘ f.barMap` on a pure tensor word
of length `n` expands over all compositions of `n` into at least two blocks
(`TauCeti.AInfinityAlgebra.higherTaylor_barMap_of_tprod`).
-/

public section

open scoped BigOperators

namespace TauCeti

open ReducedTensorWords

universe uR uA uB

namespace AInfinityAlgebra

/-- Evaluating `𝒜.higherTaylor` after the bar map of any `A∞` morphism `f : ℬ ⟶ 𝒜` on a pure
tensor word of positive length expands over all compositions of `n` into at least two blocks,
applying `f.suspendedComponent` on each block and `𝒜.suspendedM` at the root. -/
theorem higherTaylor_barMap_of_tprod {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (𝒜 : AInfinityAlgebra R A) {ℬ : AInfinityAlgebra R B} (f : AInfinityHom ℬ 𝒜)
    {n : ℕ} (hn : 0 < n) (x : Fin n → B) :
    𝒜.higherTaylor (f.barMap (of R B ⟨n, hn⟩ (PiTensorProduct.tprod R x))) =
      ∑ d : {d : Composition n // 2 ≤ d.length},
        𝒜.suspendedM d.val.length
          (fun i ↦ f.suspendedComponent (d.val.blocksFun i) (x ∘ d.val.embedding i)) := by
  rw [f.barMap_eq_coalgHom, coalgHom_of_tprod_eq_sum_composition f.taylor hn x, map_sum]
  refine Finset.sum_congr_set {d : Composition n | 2 ≤ d.length} _ _ (fun d hd ↦ ?_) fun d hd ↦ ?_
  · have hsc (i : Fin d.length) :=
      (f.suspendedComponent_apply (d.blocksFun i) (d.one_le_blocksFun i) (x ∘ d.embedding i)).symm
    simp_rw [hsc]
    exact 𝒜.higherTaylor_of_tprod_eq_suspendedM hd _
  · have hpos := d.length_pos_of_pos hn
    have hd1 : d.length = 1 := by simp only [Set.mem_ofPred_eq] at hd; omega
    have hone {m : ℕ} (hm : 0 < m) (hm1 : m = 1) (z : Fin m → A) :
        of R A ⟨m, hm⟩ (PiTensorProduct.tprod R z) = ofLetter R A (z ⟨0, hm⟩) := by
      subst hm1; exact of_one_tprod R A z
    rw [hone hpos hd1, 𝒜.higherTaylor_ofLetter]

end AInfinityAlgebra

namespace AInfinityStrictHom

variable {R : Type uR} [CommRing R]
  {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- A strict morphism intertwines the unary bar differentials. -/
theorem unaryBarDifferential_comp_barMap (f : AInfinityStrictHom 𝒜 ℬ) :
    ℬ.unaryBarDifferential ∘ₗ f.barMap = f.barMap ∘ₗ 𝒜.unaryBarDifferential := by
  have hF : IsCoalgHom R f.barMap := by
    rw [barMap_def]
    exact isCoalgHom_map f.toLinearMap
  refine hF.comp_eq_comp_of_letter_comp_eq
    f.isHomogeneous_barMap 𝒜.isGradedCoderivation_unaryBarDifferential
      ℬ.isGradedCoderivation_unaryBarDifferential ?_
  simp only [← LinearMap.comp_assoc]
  rw [AInfinityAlgebra.letter_comp_unaryBarDifferential, barMap_def, letter_comp_map]
  simp only [LinearMap.comp_assoc]
  rw [AInfinityAlgebra.letter_comp_unaryBarDifferential]
  apply LinearMap.ext
  intro x
  have hℓ := LinearMap.congr_fun (letter_comp_map (R := R) f.toLinearMap) x
  simp only [LinearMap.comp_apply] at hℓ
  simp only [LinearMap.comp_apply, AInfinityAlgebra.taylor_ofLetter, hℓ, coe_toLinearMap]
  exact (f.map_m_one (letter R A x)).symm

/-- A strict morphism intertwines the higher bar perturbations. -/
theorem higherBarDifferential_comp_barMap (f : AInfinityStrictHom 𝒜 ℬ) :
    ℬ.higherBarDifferential ∘ₗ f.barMap = f.barMap ∘ₗ 𝒜.higherBarDifferential := by
  have h := f.barDifferential_comp_barMap
  have h₁ := f.unaryBarDifferential_comp_barMap
  simp only [AInfinityAlgebra.barDifferential_eq_unary_add_higher,
    LinearMap.add_comp, LinearMap.comp_add, h₁] at h
  apply LinearMap.ext
  intro x
  exact add_left_cancel (LinearMap.congr_fun h x)

end AInfinityStrictHom

end TauCeti
