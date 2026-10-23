/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.LinearAlgebra.Unimodular
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Matrix coefficients detect Chevalley-line cosets

Two algebra-valued points carry a unimodular vector to generators of the same line
exactly when all their matrix coefficients differ by one common unit. For the exterior
line realizing a closed subgroup as a stabilizer, this is precisely equality of left
cosets. The criterion holds over arbitrary commutative value rings, including nonreduced
rings; checking only field-valued points would lose the infinitesimal fiber relation.

The construction uses `HopfIdeal.exists_finite_subcomodule_exteriorPower_line_stabilizer`,
`Comodule.pointsAction`, and scalar-extended dual evaluation. It supplies the algebraic
fiber relation used to compare a projective orbit with a homogeneous quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and §§7.d–7.f.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

variable {R H M A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M] [Module.Free R M]
  [CommSemiring A] [Algebra R A]

/-- Equality of translated lines is equivalent to proportionality of all matrix coefficients
by a common unit of the value algebra. No field or reducedness assumption is needed on it. -/
theorem span_pointsAction_eq_iff_exists_units_matrixCoefficient
    (m : M) (hm : Module.IsUnimodular R m) (g h : WithConv (H →ₐ[R] A)) :
    A ∙ pointsAction M g (1 ⊗ₜ[R] m) = A ∙ pointsAction M h (1 ⊗ₜ[R] m) ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual R M,
        h.ofConv (matrixCoefficient (C := H) φ m) =
          c * g.ofConv (matrixCoefficient (C := H) φ m) := by
  have hgm : Module.IsUnimodular A (pointsAction M g (1 ⊗ₜ[R] m)) := by
    obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp (hm.one_tmul (S := A))
    exact Module.isUnimodular_of_apply_eq_one
      (f := f.comp (pointsAction M g).symm.toLinearMap) (by simpa using hf)
  have heval (a : WithConv (H →ₐ[R] A)) (φ : Module.Dual R M) :
      Module.Dual.baseChange A φ (pointsAction M a (1 ⊗ₜ[R] m)) =
        a.ofConv (matrixCoefficient (C := H) φ m) := by
    rw [← TauCeti.Module.Dual.baseChangeEvaluation_one_tmul,
      ← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap]
    simpa only [one_mul] using baseChangeEvaluation_endOfPoint_tmul a.ofConv 1 1 φ m
  rw [hgm.span_singleton_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun φ ↦ ?_⟩
    have heq := congrArg (Module.Dual.baseChange A φ) hc
    simpa only [Units.smul_def, map_smul, smul_eq_mul, heval] using heq.symm
  · rintro ⟨c, hc⟩
    refine ⟨c, TauCeti.Module.Dual.eq_of_baseChange_eq fun φ ↦ ?_⟩
    simpa only [Units.smul_def, map_smul, smul_eq_mul, heval] using (hc φ).symm

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

universe u v w x

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}
  {M : Type w} [AddCommGroup M] [Module R M] [Comodule R H M] [Module.Free R M]

/-- If a closed subgroup is the stabilizer of a unimodular line, equality of left cosets
is detected by unit proportionality of the line generator's matrix coefficients. -/
theorem coset_eq_iff_exists_units_matrixCoefficient (I : HopfIdeal R H)
    (m : M) (hm : Module.IsUnimodular R m) (A : CommAlgCat.{x} R)
    (hstab : ∀ a : HopfAlgebra.points (R := R) (H := H) A,
      a ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
        ((R ∙ m).baseChange A).map (Comodule.endOfPoint M a.ofConv) =
          (R ∙ m).baseChange A)
    (g h : HopfAlgebra.points (R := R) (H := H) A) :
    (QuotientGroup.mk g : HopfAlgebra.points (R := R) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual R M,
        h.ofConv (Comodule.matrixCoefficient (C := H) φ m) =
          c * g.ofConv (Comodule.matrixCoefficient (C := H) φ m) := by
  rw [QuotientGroup.eq, hstab]
  simp only [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply,
    ← Comodule.pointsAction_toLinearMap, Submodule.map_span, Set.image_singleton]
  rw [← (Submodule.map_injective_of_injective (Comodule.pointsAction M g).injective).eq_iff]
  simp only [Submodule.map_span, Set.image_singleton]
  have hmul : Comodule.pointsAction M g
      (Comodule.pointsAction M (g⁻¹ * h) (1 ⊗ₜ[R] m)) =
        Comodule.pointsAction M h (1 ⊗ₜ[R] m) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
  simp only [LinearEquiv.coe_coe]
  rw [hmul, eq_comm]
  exact Comodule.span_pointsAction_eq_iff_exists_units_matrixCoefficient m hm g h

attribute [local instance] Comodule.exteriorPower

/-- **Chevalley's coset criterion.** A closed subgroup with finitely generated defining ideal
admits a finite exterior-power representation and a unimodular vector whose matrix coefficients
detect its left cosets over every commutative value algebra, including nonreduced algebras. -/
theorem exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient
    {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}
    (I : HopfIdeal k H) (hI : I.toIdeal.FG) :
    ∃ (V : Subcomodule k H H) (n : ℕ), Module.Finite k V.toSubmodule ∧
      let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
      ∃ m : ⋀[k]^n V, Module.IsUnimodular k m ∧
        ∀ (A : CommAlgCat.{x} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
          (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
              CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
            ∃ c : Aˣ, ∀ φ : Module.Dual k (⋀[k]^n V),
              h.ofConv (Comodule.matrixCoefficient (C := H) φ m) =
                c * g.ofConv (Comodule.matrixCoefficient (C := H) φ m) := by
  obtain ⟨V, n, hV, L, hL, _, hstab⟩ :=
    I.exists_finite_subcomodule_exteriorPower_line_stabilizer hI
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup (⋀[k]^n V) := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup k
  obtain ⟨m, hm, hgen⟩ := (finrank_eq_one_iff' (K := k) (V := L)).mp hL
  have hspan : L = k ∙ (m : ⋀[k]^n V) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨c, hc⟩ := hgen ⟨z, hz⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr m.property)
  have huni : Module.IsUnimodular k (m : ⋀[k]^n V) :=
    Module.isUnimodular_iff.mpr
      (Module.Projective.exists_dual_eq_one k (Subtype.coe_injective.ne hm))
  refine ⟨V, n, hV, m, huni, fun A g h ↦ ?_⟩
  exact I.coset_eq_iff_exists_units_matrixCoefficient (m : ⋀[k]^n V) huni A
    (fun a ↦ by simpa only [hspan] using hstab A a) g h

end TauCeti.HopfIdeal
