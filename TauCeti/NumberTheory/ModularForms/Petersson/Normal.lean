/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Petersson.Hecke
public import TauCeti.NumberTheory.ModularForms.Petersson.Orthogonal
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic

/-!
# Normality of the good Hecke operators

For an index `n` coprime to the level, the Petersson adjoint of `Tₙ` on
`S_k(Γ₁(N))` is `⟨n⟩⁻¹ Tₙ`.  The inverse diamond operator commutes with `Tₙ`, so this adjoint
commutes with `Tₙ`: the good Hecke operator is normal for the Petersson product.

The result is stated without installing a global inner-product-space instance on cusp forms.
Instead, `peterssonInnerCosetsₛₗ.flip` records the Petersson product as a sesquilinear form,
`peterssonInnerCosets_heckeTCuspNat_right` supplies the adjoint formula in the opposite argument,
and `isAdjointPair_heckeTCuspNat` packages both formulas in Mathlib's `LinearMap.IsAdjointPair`
API.  The final commutation theorem is therefore the instance-free form of normality needed for
simultaneous diagonalization.

## Main results

* `HeckeRing.GL2.isAdjointPair_heckeTCuspNat`: `Tₙ` and `⟨n⟩⁻¹ Tₙ` are a Petersson-adjoint pair.
* `HeckeRing.GL2.commute_peterssonAdjoint_heckeTCuspNat`: the Petersson adjoint of `Tₙ`
  commutes with `Tₙ`.
* `HeckeRing.GL2.isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`: on a fixed
  nebentypus space, the adjoint of a good `Tₚ` is the scalar multiple `χ(p)⁻¹ Tₚ`.
* `HeckeRing.GL2.commute_peterssonAdjoint_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`:
  this adjoint commutes with `Tₚ` on the fixed-nebentypus space.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.5.4.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.5.4.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti.CuspForm

variable {N : ℕ} [NeZero N]

/-- The Petersson product restricted to the cusp forms of weight `k` and nebentypus `χ`.

This is a sesquilinear form rather than an `InnerProductSpace` instance: the analytic function
space underlying cusp forms already has a normed structure, and the Petersson norm should not
silently replace it. -/
noncomputable def peterssonInnerCosetsCharSpaceₛₗ (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ →ₗ⋆[ℂ] cuspFormCharSpace k χ →ₗ[ℂ] ℂ :=
  (peterssonInnerCosetsₛₗ (Γ := Gamma1 N) (k := k)).domRestrict₁₂
    (cuspFormCharSpace k χ) (cuspFormCharSpace k χ)

/-- Evaluation of the Petersson product on a nebentypus space. -/
@[simp]
theorem peterssonInnerCosetsCharSpaceₛₗ_apply_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f g : cuspFormCharSpace k χ) :
    peterssonInnerCosetsCharSpaceₛₗ k χ f g =
      _root_.CuspForm.peterssonInnerCosets
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  peterssonInnerCosetsₛₗ_apply_apply _ _

end TauCeti.CuspForm

namespace HeckeRing.GL2

variable {N n : ℕ} [NeZero N] [NeZero n] (k : ℤ)

/-! ### The Petersson-adjoint pair -/

/-- **The Petersson adjoint formula in the second argument.** For `n` coprime to `N`,

`⟪f, Tₙ g⟫ = ⟪⟨n⟩⁻¹ Tₙ f, g⟫`.

This is the Hermitian transpose of
`peterssonInnerCosets_heckeTCuspNat_left`. -/
theorem peterssonInnerCosets_heckeTCuspNat_right (hn : n.Coprime N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets f (heckeTCuspNat k n g) =
      CuspForm.peterssonInnerCosets
        (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTCuspNat k n f)) g := by
  calc
    CuspForm.peterssonInnerCosets f (heckeTCuspNat k n g) =
        starRingEnd ℂ (CuspForm.peterssonInnerCosets (heckeTCuspNat k n g) f) :=
      (CuspForm.peterssonInnerCosets_conj_symm _ _).symm
    _ = starRingEnd ℂ (CuspForm.peterssonInnerCosets g
        (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTCuspNat k n f))) := by
      rw [peterssonInnerCosets_heckeTCuspNat_left k hn]
    _ = CuspForm.peterssonInnerCosets
        (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTCuspNat k n f)) g :=
      CuspForm.peterssonInnerCosets_conj_symm _ _

/-- **The Petersson adjoint of `Tₙ` is `⟨n⟩⁻¹ Tₙ`, as an adjoint pair.**

The Petersson form is flipped because `LinearMap.IsAdjointPair` is formulated for a form linear
in its first argument, while `peterssonInnerCosetsₛₗ` follows the usual mathematical convention
and is conjugate-linear in its first argument. -/
theorem isAdjointPair_heckeTCuspNat (hn : n.Coprime N) :
    LinearMap.IsAdjointPair
      (TauCeti.CuspForm.peterssonInnerCosetsₛₗ (Γ := Gamma1 N) (k := k)).flip
      (TauCeti.CuspForm.peterssonInnerCosetsₛₗ (Γ := Gamma1 N) (k := k)).flip
      (heckeTCuspNat (N := N) k n)
      (diamondOpCusp (N := N) k (ZMod.unitOfCoprime n hn)⁻¹ *
        heckeTCuspNat (N := N) k n) := by
  intro f g
  simp only [LinearMap.flip_apply, TauCeti.CuspForm.peterssonInnerCosetsₛₗ_apply_apply,
    Module.End.mul_apply]
  exact peterssonInnerCosets_heckeTCuspNat_right k hn g f

/-! ### Normality -/

/-- **The good Hecke operator is Petersson-normal.** For `n` coprime to `N`, its Petersson
adjoint `⟨n⟩⁻¹ Tₙ` commutes with `Tₙ`.

Together with `isAdjointPair_heckeTCuspNat`, this is the instance-free statement that `Tₙ` is
a normal operator. It applies on the whole space `S_k(Γ₁(N))`, hence in particular after
restricting to any `Tₙ`-stable nebentypus subspace. -/
theorem commute_peterssonAdjoint_heckeTCuspNat (hn : n.Coprime N) :
    Commute (diamondOpCusp (N := N) k (ZMod.unitOfCoprime n hn)⁻¹ *
        heckeTCuspNat (N := N) k n)
      (heckeTCuspNat (N := N) k n) :=
  (commute_heckeTCuspNat_diamondOpCusp_inv k hn).symm.mul_left
    (Commute.refl (heckeTCuspNat (N := N) k n))

/-! ### Normality on a fixed nebentypus space -/

variable {χ : (ZMod N)ˣ →* ℂˣ} {p : ℕ}

/-- **The Petersson adjoint of a good prime Hecke operator on `S_k(N, χ)`.** If `p` is prime
and coprime to `N`, then the Hecke-ring action of `Tₚ` and its scalar multiple `χ(p)⁻¹ Tₚ`
are an adjoint pair for the Petersson product restricted to the nebentypus space.

The operator is expressed through `heckeRingHomCuspCharSpace`, the canonical action on
`S_k(N, χ)`; `heckeRingHomCuspCharSpace_heckeTGeneratorGamma0` identifies it with the classical
`Tₚ` used by the ambient adjoint theorem. -/
theorem isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
    (hp : p.Prime) (hpN : p.Coprime N) :
    LinearMap.IsAdjointPair
      (TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ k χ).flip
      (TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ k χ).flip
      (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p))
      (((χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹) •
        heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p)) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  intro f g
  simp only [LinearMap.flip_apply,
    TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ_apply_apply]
  rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp,
    Pi.smul_apply, Submodule.coe_smul,
    coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp,
    peterssonInnerCosets_heckeTCuspNat_right k hpN,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ]
  · rw [map_inv, Units.val_inv_eq_inv_val]
  · exact heckeTCuspNat_mem_cuspFormCharSpace k χ hp g.2

/-- **A good prime Hecke operator on `S_k(N, χ)` is Petersson-normal.** Its adjoint
`χ(p)⁻¹ Tₚ` commutes with `Tₚ`, in the canonical Hecke-ring action on the fixed-nebentypus
space. Together with
`isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`, this is the instance-free
normality statement on `S_k(N, χ)`. -/
theorem commute_peterssonAdjoint_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
    (hp : p.Prime) (hpN : p.Coprime N) :
    Commute
      (((χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹) •
        heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p))
      (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p)) := by
  rw [heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp]
  exact (Commute.refl _).smul_left _

end HeckeRing.GL2

end
