/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Basic

/-!
# Transport of crossed products along an algebra equivalence

An equivalence `e : L ≃ₐ[K] M` identifies the automorphism groups by conjugation. If cocycles
`c` and `d` correspond under this identification and the induced map on units, their crossed
products are isomorphic by `x • u_σ ↦ e(x) • u_{e σ e⁻¹}`. The corresponding equality of Brauer
classes over finite Galois fields is in `TauCeti.Algebra.CrossedProduct.BrauerClass`.

In particular, this transports a crossed-product presentation to an isomorphic splitting field.
The coefficient and basis formulas retain the specified algebra equivalence, rather than merely
asserting the existence of an isomorphism of algebras.

The construction uses Mathlib's `AlgEquiv.autCongr` and `Finsupp.lcongr`, and Tau Ceti's
crossed-product universal property `CrossedProduct.lift` and basis.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

noncomputable section

universe u v w

namespace TauCeti.CrossedProduct

variable {K : Type u} [CommSemiring K] {L : Type v} [CommRing L] [Algebra K L]
  {M : Type w} [CommRing M] [Algebra K M]
  (c : TauCeti.TwoCocycle K L) (d : TauCeti.TwoCocycle K M) (e : L ≃ₐ[K] M)

private def congrLinearEquiv : CrossedProduct c ≃ₗ[K] CrossedProduct d :=
  ((basis c).repr.restrictScalars K).trans
    ((Finsupp.lcongr e.autCongr.toEquiv e.toLinearEquiv).trans
      ((basis d).repr.symm.restrictScalars K))

private theorem congrLinearEquiv_smul_basis (σ : L ≃ₐ[K] L) (x : L) :
    congrLinearEquiv c d e (x • basis c σ) = e x • basis d (e.autCongr σ) := by
  simp [congrLinearEquiv, Finsupp.smul_single, smul_eq_mul]

variable (hc : ∀ σ τ, Units.map e.toMonoidHom (c.toFun σ τ) =
  d.toFun (e.autCongr σ) (e.autCongr τ))

private def congrHom : CrossedProduct c →ₐ[K] CrossedProduct d :=
  lift ((inc d).comp e.toAlgHom) (fun σ ↦ basis d (e.autCongr σ))
    (fun σ x ↦ by
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, basis_mul_inc,
        AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply])
    (fun σ τ ↦ by
      have h : e (c.toFun σ τ : L) = (d.toFun (e.autCongr σ) (e.autCongr τ) : M) :=
        congrArg Units.val (hc σ τ)
      simp only [basis_mul_basis, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, h, map_mul])
    (by
      have h : e (c.toFun 1 1 : L) = (d.toFun 1 1 : M) := by
        have h : e (c.toFun 1 1 : L) = (d.toFun (e.autCongr 1) (e.autCongr 1) : M) :=
          congrArg Units.val (hc 1 1)
        simpa only [map_one] using h
      simp only [map_one, basis_one, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, h])

private theorem coe_congrHom : ⇑(congrHom c d e hc) = congrLinearEquiv c d e := by
  funext a
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | smul_basis σ x =>
    rw [congrHom, lift_smul_basis, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      congrLinearEquiv_smul_basis, smul_def]

/-- Transport a crossed product along an equivalence of its coefficient algebras and the
corresponding equality of cocycles. The coefficient of `u_σ` is mapped by `e`, and its index is
conjugated by `e`. -/
def congr : CrossedProduct c ≃ₐ[K] CrossedProduct d :=
  AlgEquiv.ofBijective (congrHom c d e hc) (by
    rw [coe_congrHom]
    exact (congrLinearEquiv c d e).bijective)

private theorem coe_congr : ⇑(congr c d e hc) = congrLinearEquiv c d e := by
  rw [congr, AlgEquiv.coe_ofBijective, coe_congrHom]

/-- The transport conjugates the index of a basis element. -/
@[simp]
theorem congr_basis (σ : L ≃ₐ[K] L) :
    congr c d e hc (basis c σ) = basis d (e.autCongr σ) := by
  simp only [congr, AlgEquiv.ofBijective_apply, congrHom, lift_basis]

/-- The transport maps the embedded coefficient algebra by the specified equivalence. -/
@[simp]
theorem congr_inc (x : L) : congr c d e hc (inc c x) = inc d (e x) := by
  simp only [congr, AlgEquiv.ofBijective_apply, congrHom, lift_inc, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom]

/-- Transport is semilinear for left multiplication by the coefficient algebra. -/
@[simp]
theorem congr_smul (x : L) (a : CrossedProduct c) :
    congr c d e hc (x • a) = e x • congr c d e hc a := by
  rw [smul_def, map_mul, congr_inc, smul_def]

/-- In the transported basis, every coefficient is mapped by `e`. -/
@[simp]
theorem repr_congr (a : CrossedProduct c) (σ : M ≃ₐ[K] M) :
    (basis d).repr (congr c d e hc a) σ = e ((basis c).repr a (e.autCongr.symm σ)) := by
  calc
    _ = (basis d).repr ((basis d).repr.symm
        (Finsupp.lcongr e.autCongr.toEquiv e.toLinearEquiv ((basis c).repr a))) σ := by
      rw [coe_congr, congrLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply]
    _ = Finsupp.lcongr e.autCongr.toEquiv e.toLinearEquiv ((basis c).repr a) σ :=
      congrArg (fun f => f σ) ((basis d).repr.apply_symm_apply _)
    _ = _ := Finsupp.lcongr_apply_apply _ _ _ _

end TauCeti.CrossedProduct
