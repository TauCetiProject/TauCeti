/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation

/-!
# The integral fixed Cartan lattice and its centralizer

The Cartan lattice fixed by a vertex permutation is the image of the fixed coordinate
module under `Matrix.ShellLieAlgebra.cartan`. Transporting
`Equiv.Perm.permutationFixedBasis` gives its integral orbit-sum basis, with coordinates
read at orbit representatives. These constructions require no finiteness of the root shell
or positivity hypothesis on the Gram matrix.

For a positive definite even Gram matrix with nonpositive off-diagonal entries, the Cartan
vectors fixed by a diagram permutation separate every root line of the signed shell Lie
algebra. In fact, one integral Cartan vector suffices: Cramer's rule applied to the constant
vector gives a diagram-invariant vector whose pairing with a root is the determinant times
its height. The height is nonzero because all simple-root coordinates have one sign.

Consequently the centralizer of the fixed Cartan in the integral shell algebra is exactly
the ambient Cartan. Inside the fixed algebra its centralizer is exactly the fixed Cartan.
These statements concern ordinary commuting vectors over the integers, not generalized
weight spaces or arbitrary scalar extensions.

The construction uses the signed shell algebra and its relabelling action from the imported
modules, and Mathlib's `Matrix.cramer` and `Matrix.mulVec_cramer`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.
-/

public section

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] {B : Matrix I I ℤ}

section Lattice

variable (σ : Equiv.Perm I)

variable (B) in
/-- The Cartan lattice fixed by the vertex permutation: the image of its fixed coordinate
module, equivalently the span of the distinct integral Cartan orbit sums. -/
noncomputable def fixedCartanLattice : Submodule ℤ (ShellLieAlgebra B) :=
  (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule.map (cartan B)

/-- The distinct vertex-orbit sums form a basis of the integral fixed Cartan lattice. -/
noncomputable def fixedCartanBasis :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid σ)) ℤ (fixedCartanLattice B σ) :=
  (σ.permutationFixedBasis (R := ℤ)).map
    (Submodule.equivMapOfInjective (cartan B) (cartan_injective B) _)

/-- Each fixed Cartan basis vector is the sum over one vertex orbit, with no multiplicity. -/
@[simp]
theorem coe_fixedCartanBasis [DecidableEq I]
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedCartanBasis (B := B) σ O : ShellLieAlgebra B) =
      ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1) := by
  classical
  -- Reduce the transported basis application through the image equivalence's coercion.
  change cartan B (σ.permutationFixedBasis (R := ℤ) O).val = _
  rw [σ.permutationFixedBasis_eq_sum, map_sum]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Quotient.mk_eq_iff_out (s := Equiv.Perm.SameCycle.setoid σ)]
    rfl
  · intro i _
    rfl

/-- Fixed Cartan coordinates are read at the chosen orbit representatives. -/
@[simp]
theorem fixedCartanBasis_repr (x : fixedCartanLattice B σ)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedCartanBasis (B := B) σ).repr x O = (equivProd B x).1 O.out := by
  let e := Submodule.equivMapOfInjective (cartan B) (cartan_injective B)
    (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule
  have hx := congrArg (fun y : ShellLieAlgebra B ↦ (equivProd B y).1)
    (Submodule.map_equivMapOfInjective_symm_apply (cartan B) (cartan_injective B) _ x)
  simp only [equivProd_cartan] at hx
  -- The transported representation composes the original one with the inverse image map.
  change (σ.permutationFixedBasis (R := ℤ)).repr (e.symm x) O = _
  conv_lhs => rw [← Quotient.out_eq O]
  rw [Equiv.Perm.permutationFixedBasis_repr]
  exact congrFun hx O.out

/-- A vector belongs to the fixed Cartan lattice exactly when its root part vanishes and
its Cartan coordinates are invariant under the vertex permutation. -/
@[simp]
theorem mem_fixedCartanLattice_iff (x : ShellLieAlgebra B) :
    x ∈ fixedCartanLattice B σ ↔
      (equivProd B x).2 = 0 ∧ ∀ i, (equivProd B x).1 (σ i) = (equivProd B x).1 i := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hinv := LinearMap.mem_fixedSubmodule_iff.mp hv
    exact ⟨by simp, fun i ↦ by simpa using congrFun hinv i⟩
  · rintro ⟨hroot, hinv⟩
    refine Submodule.mem_map.mpr ⟨(equivProd B x).1, ?_,
      ((equivProd_snd_eq_zero_iff B x).mp hroot).symm⟩
    exact LinearMap.mem_fixedSubmodule_iff.mpr (funext hinv)

variable [LinearOrder I]

/-- The fixed Cartan lattice is contained in the fixed submodule of the pinned diagram action. -/
theorem fixedCartanLattice_le_fixedSubmodule (hσ : B.reindex σ σ = B) :
    fixedCartanLattice B σ ≤ (reindex σ hσ).toLinearMap.fixedSubmodule := by
  rintro _ ⟨v, hv, rfl⟩
  apply LinearMap.mem_fixedSubmodule_iff.mpr
  rw [LinearEquiv.coe_coe, reindex_cartan]
  have hinv : v ∘ σ = v := LinearMap.mem_fixedSubmodule_iff.mp hv
  exact congrArg (cartan B) (by
    funext i
    simpa using (congrFun hinv (σ.symm i)).symm)

end Lattice

variable [LinearOrder I]

/-- A vector commuting with every diagram-fixed Cartan vector has no root component. The
converse holds without any root-system hypotheses. -/
theorem forall_fixed_cartan_lie_eq_zero_iff (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (x : ShellLieAlgebra B) :
    (∀ h : I → ℤ, h ∘ σ.symm = h → ⁅cartan B h, x⁆ = 0) ↔
      (equivProd B x).2 = 0 := by
  constructor
  · intro hx
    obtain ⟨h, hh, hreg⟩ := hB.exists_invariant_pairing_ne_zero hev hoff σ hσ
    ext a
    have ha := congrArg (fun y ↦ (equivProd B y).2 a) (hx h hh)
    rw [equivProd_cartan_lie_snd] at ha
    have hmul : (h ⬝ᵥ B *ᵥ (a : I → ℤ)) * (equivProd B x).2 a = 0 := by
      simpa using ha
    exact (mul_eq_zero.mp hmul).resolve_left (hreg a)
  · intro hx h _
    have heq := (equivProd_snd_eq_zero_iff B x).mp hx
    rw [heq, cartan_lie_cartan]

/-- The zero-weight part inside the diagram-fixed shell algebra is precisely the fixed Cartan. -/
theorem exists_fixed_cartan_eq_iff (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (x : ShellLieAlgebra B) (hx : reindex σ hσ x = x) :
    (∃ h : I → ℤ, h ∘ σ.symm = h ∧ x = cartan B h) ↔
      ∀ h : I → ℤ, h ∘ σ.symm = h → ⁅cartan B h, x⁆ = 0 := by
  constructor
  · rintro ⟨h, _, rfl⟩ k _
    exact cartan_lie_cartan k h
  · intro hzero
    have hroot := (forall_fixed_cartan_lie_eq_zero_iff hB hev hoff σ hσ x).mp hzero
    have heq := (equivProd_snd_eq_zero_iff B x).mp hroot
    refine ⟨(equivProd B x).1, ?_, heq⟩
    rw [heq, reindex_cartan] at hx
    simpa only [equivProd_cartan] using congrArg (fun y ↦ (equivProd B y).1) hx

end Matrix.ShellLieAlgebra
