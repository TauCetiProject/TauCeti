/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.Algebra.Lie.Basis.Cartan
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.Basis.Root
import TauCeti.Algebra.Lie.Weights.Basic
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Faithfulness from spanning weights

A representation of a rational Killing Lie algebra with a Lie-algebra basis is faithful if it
has nonzero weight vectors whose weights span the rational weight space. In particular, integral
weights spanning the full weight lattice suffice. The Cartan basis identifies the coordinate
weights with characters, so `TauCeti.isFaithful_of_mem_weightSpace_of_span_range_eq_top` and
`TauCeti.isFaithful_of_isFaithful_cartanSubalgebra` give faithfulness on the whole Lie algebra.
-/

public section

namespace LieAlgebra.Basis

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι L : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra.IsKilling ℚ L] [FiniteDimensional ℚ L] {H : LieSubalgebra ℚ L}

/-- Nonzero integral weight vectors whose weights span the rational weight space detect every
element of a rational Killing Lie algebra with a Lie-algebra basis. -/
theorem representation_ι_injective_of_isCartanWeightVector
    (b : LieAlgebra.Basis ι H) {V η : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    {v : η → V} {wt : η → ι → ℤ} (hv : ∀ a, v a ≠ 0)
    (hwt : ∀ a, TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector b.h ρ (wt a) (v a))
    (hspan : Submodule.span ℚ (Set.range fun a i => (wt a i : ℚ)) = ⊤) :
    Function.Injective fun x : L => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  let action := ρ.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)
  let := LieRingModule.compLieHom V action
  let := LieModule.compLieHom V action
  let χ := fun a => b.cartanBasis.constr ℚ fun i => (wt a i : ℚ)
  have hweight (a : η) : v a ∈ LieModule.weightSpace V (χ a : H → ℚ) := by
    apply (b.cartanBasis.mem_weightSpace_iff_forall_basis _ _).mpr
    intro i
    rw [LieSubalgebra.coe_bracket_of_module, LieRingModule.compLieHom_apply,
      Module.End.lie_apply, LieHom.comp_apply, AlgHom.toLieHom_apply]
    simp only [χ, Module.Basis.constr_basis, coe_cartanBasis]
    exact (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp (hwt a) i
  have hχ : Submodule.span ℚ (Set.range χ) = ⊤ := by
    have hrange : Set.range χ = (b.cartanBasis.constr ℚ) ''
        Set.range (fun a i => (wt a i : ℚ)) := Set.range_comp _ _
    rw [hrange, Submodule.span_image_linearEquiv, hspan, Submodule.map_top, LinearEquiv.range]
  have : LieModule.IsFaithful ℚ H V :=
    TauCeti.isFaithful_of_mem_weightSpace_of_span_range_eq_top hweight hv hχ
  have := TauCeti.isFaithful_of_isFaithful_cartanSubalgebra (K := ℚ) (L := L) (M := V) (H := H)
  intro x y hxy
  apply LieModule.IsFaithful.injective_toEnd (R := ℚ) (M := V)
  ext m
  simpa only [LieModule.toEnd_apply_apply, LieRingModule.compLieHom_apply,
    Module.End.lie_apply, action, LieHom.comp_apply, AlgHom.toLieHom_apply] using
      DFunLike.congr_fun hxy m

/-- Nonzero weight vectors spanning the full integral weight lattice give a faithful
representation of a rational Killing Lie algebra with a Lie-algebra basis. -/
theorem representation_ι_injective_of_isCartanWeightVector_of_span_int
    (b : LieAlgebra.Basis ι H) {V η : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    {v : η → V} {wt : η → ι → ℤ} (hv : ∀ a, v a ≠ 0)
    (hwt : ∀ a, TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector b.h ρ (wt a) (v a))
    (hspan : Submodule.span ℤ (Set.range wt) = ⊤) :
    Function.Injective fun x : L => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  apply b.representation_ι_injective_of_isCartanWeightVector ρ hv hwt
  let cast := (Int.castAddHom ℚ).toIntLinearMap.compLeft ι
  have hcast : Submodule.span ℚ (Set.range cast) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℚ ι).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [cast, Pi.basisFun_apply, Pi.single_apply]
  exact (Submodule.span_range_eq_span_range_comp_of_span_eq_top
    (S := ℚ) hspan cast).symm.trans hcast

end LieAlgebra.Basis
