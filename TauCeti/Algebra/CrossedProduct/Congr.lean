/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.RingCongr

/-!
# Transport of crossed products along an algebra equivalence

An equivalence `e : L ≃ₐ[K] M` identifies the automorphism groups by conjugation. If cocycles
`c` and `d` correspond under this identification and the induced map on units, their crossed
products are isomorphic by `x • u_σ ↦ e(x) • u_{e σ e⁻¹}`. The corresponding equality of Brauer
classes over finite Galois fields is in `TauCeti.Algebra.CrossedProduct.BrauerClass`.

In particular, this transports a crossed-product presentation to an isomorphic splitting field.
The coefficient and basis formulas retain the specified algebra equivalence, rather than merely
asserting the existence of an isomorphism of algebras.

The construction specializes `CrossedProduct.comapRingEquiv` using Mathlib's
`AlgEquiv.autCongr` and the scalar compatibility of the coefficient algebra equivalence.

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

variable (hc : ∀ σ τ, Units.map e.toMonoidHom (c.toFun σ τ) =
  d.toFun (e.autCongr σ) (e.autCongr τ))

private theorem autCongr_symm_compat (g : M ≃ₐ[K] M) (x : L) :
    e (e.autCongr.symm g x) = g (e x) := by
  simp [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]

include hc in
private theorem congr_cocycle_eq : d = c.comap e.autCongr.symm e.toRingEquiv
    (autCongr_symm_compat e) := by
  ext g h
  have hgh := hc (e.autCongr.symm g) (e.autCongr.symm h)
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hgh
  simpa [TwoCocycle.comap_toFun, AlgEquiv.toMulEquiv, AlgEquiv.toEquiv_eq_coe] using
    (congrArg Units.val hgh).symm

-- Isolate equality transport and its computations: after equality elimination the map is
-- the identity, so basis vectors, embedded coefficients and coordinates are unchanged.
private def cocycleEqEquiv {c d : TwoCocycle K M} (h : c = d) :
    CrossedProduct c ≃ₐ[K] CrossedProduct d :=
  h ▸ AlgEquiv.refl

@[simp]
private theorem cocycleEqEquiv_basis {c d : TwoCocycle K M} (h : c = d)
    (σ : M ≃ₐ[K] M) : cocycleEqEquiv h (basis c σ) = basis d σ := by
  subst d
  rfl

@[simp]
private theorem cocycleEqEquiv_inc {c d : TwoCocycle K M} (h : c = d) (x : M) :
    cocycleEqEquiv h (inc c x) = inc d x := by
  subst d
  rfl

@[simp]
private theorem repr_cocycleEqEquiv {c d : TwoCocycle K M} (h : c = d)
    (a : CrossedProduct c) (σ : M ≃ₐ[K] M) :
    (basis d).repr (cocycleEqEquiv h a) σ = (basis c).repr a σ := by
  subst d
  rfl

/-- Transport a crossed product along an equivalence of its coefficient algebras and the
corresponding equality of cocycles. The coefficient of `u_σ` is mapped by `e`, and its index is
conjugated by `e`. -/
def congr : CrossedProduct c ≃ₐ[K] CrossedProduct d :=
  let f := comapRingEquiv c e.toRingEquiv e.autCongr.symm (autCongr_symm_compat e)
  (AlgEquiv.ofRingEquiv (f := f.symm) (by
    intro k
    apply f.injective
    simpa only [RingEquiv.apply_symm_apply, RingHom.id_apply] using
      (comapRingEquiv_algebraMap c e.toRingEquiv e.autCongr.symm
        (autCongr_symm_compat e) (RingHom.id K) e.commutes k).symm)).trans
    (cocycleEqEquiv (congr_cocycle_eq c d e hc).symm)

/-- The transport conjugates the index of a basis element. -/
@[simp]
theorem congr_basis (σ : L ≃ₐ[K] L) :
    congr c d e hc (basis c σ) = basis d (e.autCongr σ) := by
  simp only [congr, AlgEquiv.trans_apply, AlgEquiv.ofRingEquiv_apply,
    comapRingEquiv_symm_basis, MulEquiv.symm_symm, cocycleEqEquiv_basis]

/-- The transport maps the embedded coefficient algebra by the specified equivalence. -/
@[simp]
theorem congr_inc (x : L) : congr c d e hc (inc c x) = inc d (e x) := by
  simp only [congr, AlgEquiv.trans_apply, AlgEquiv.ofRingEquiv_apply,
    comapRingEquiv_symm_inc, cocycleEqEquiv_inc, AlgEquiv.coe_toRingEquiv]

/-- Transport is semilinear for left multiplication by the coefficient algebra. -/
@[simp]
theorem congr_smul (x : L) (a : CrossedProduct c) :
    congr c d e hc (x • a) = e x • congr c d e hc a := by
  rw [smul_def, map_mul, congr_inc, smul_def]

/-- In the transported basis, every coefficient is mapped by `e`. -/
@[simp]
theorem repr_congr (a : CrossedProduct c) (σ : M ≃ₐ[K] M) :
    (basis d).repr (congr c d e hc a) σ = e ((basis c).repr a (e.autCongr.symm σ)) := by
  simp only [congr, AlgEquiv.trans_apply, AlgEquiv.ofRingEquiv_apply,
    repr_cocycleEqEquiv, repr_comapRingEquiv_symm, AlgEquiv.coe_toRingEquiv]

end TauCeti.CrossedProduct
