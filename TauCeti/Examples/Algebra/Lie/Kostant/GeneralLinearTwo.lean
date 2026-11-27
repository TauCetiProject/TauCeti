/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RankOne
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Datum

/-!
# Full-toral Kostant normal forms for the diagonal root datum of GL₂

These examples use a supplied Chevalley constant table on the native GL₂ diagonal root
indices. The two standard diagonal cocharacters remain separate: the opposite-root
commutator is their difference, rather than a new toral basis element. In particular
this application uses a rank-two toral lattice for a rank-one root system.
-/

public section

open Module RootPairing.ChevalleyLieAlgebra TauCeti.UniversalEnvelopingAlgebra
open scoped TensorProduct

namespace TauCeti.Examples

private def glTwoRoots : Fin 2 ≃ GeneralLinear.DiagonalRootIndex 2 where
  toFun i := if i = 0 then ⟨(ULift.up (1 : Fin 2), ULift.up (0 : Fin 2)), by simp⟩
    else ⟨(ULift.up (0 : Fin 2), ULift.up (1 : Fin 2)), by simp⟩
  invFun p := p.val.2.down
  left_inv i := by fin_cases i <;> simp
  right_inv p := by
    obtain ⟨⟨⟨i⟩, ⟨j⟩⟩, hp⟩ := p
    fin_cases i <;> fin_cases j
    · exact (hp rfl).elim
    · simp
    · simp
    · exact (hp rfl).elim

private theorem glTwoRoots_opposite : glTwoRoots 0 =
    (GeneralLinear.diagonalRootDatum 2).reflectionPerm (glTwoRoots 1) (glTwoRoots 1) := by
  apply (GeneralLinear.diagonalRootDatum 2).root.injective
  ext a
  rcases a with ⟨a⟩
  fin_cases a <;> simp [glTwoRoots]

private noncomputable def glTwoCocharacters :
    Basis (Fin 2) ℤ (ULift (Fin 2) → ℤ) :=
  (Pi.basisFun ℤ (ULift (Fin 2))).reindex Equiv.ulift

/-- The GL₂ integral basis has two toral exponents and two root exponents. -/
theorem nonempty_glTwoKostantBasis
    (c : (GeneralLinear.diagonalRootDatum 2).ChevalleyConstants) :
    Nonempty (Basis ((ℕ × (Fin 2 → ℕ)) × ℕ) ℤ
      (kostantForm (fun i => (1 : ℚ) ⊗ₜ[ℤ] root c i)
        (fun j => (1 : ℚ) ⊗ₜ[ℤ] cartan c
          ((Pi.basisFun ℤ (ULift (Fin 2))).reindex Equiv.ulift j)))) :=
  ⟨rankOneKostantBasis c glTwoCocharacters glTwoRoots glTwoRoots_opposite⟩

attribute [local instance 100] LieRing.ofAssociativeRing

-- EF = FE + H_(1,0) - H_(0,1) in the standard basis of the whole cocharacter lattice.
example (c : (GeneralLinear.diagonalRootDatum 2).ChevalleyConstants) :
    _root_.UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] root c (glTwoRoots 1)) *
        _root_.UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] root c (glTwoRoots 0)) =
      _root_.UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] root c (glTwoRoots 0)) *
        _root_.UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] root c (glTwoRoots 1)) +
      _root_.UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] cartan c (glTwoCocharacters 0)) -
      _root_.UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] cartan c (glTwoCocharacters 1)) := by
  have hcoroot : (GeneralLinear.diagonalRootDatum 2).coroot (glTwoRoots 1) =
      glTwoCocharacters 0 - glTwoCocharacters 1 := by
    ext a
    rcases a with ⟨a⟩
    fin_cases a <;> simp [glTwoRoots, glTwoCocharacters, Pi.basisFun_apply]
  have h := (_root_.UniversalEnvelopingAlgebra.ι ℚ).map_lie
    ((1 : ℚ) ⊗ₜ[ℤ] root c (glTwoRoots 1)) ((1 : ℚ) ⊗ₜ[ℤ] root c (glTwoRoots 0))
  rw [glTwoRoots_opposite, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    root_lie_root_reflectionPerm, hcoroot, map_sub, TensorProduct.tmul_sub, map_sub,
    LieRing.of_associative_ring_bracket] at h
  rw [← glTwoRoots_opposite] at h
  apply (sub_eq_iff_eq_add.mp h.symm).trans
  abel

end TauCeti.Examples
