/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose

/-!
# Unitary matrices over a split coefficient ring

When the involution exchanges the two factors of a product ring, a unitary matrix is determined
by its first component. The second is the inverse transpose in the dual coordinates given by the
Gram matrix. No field or restriction on the residue characteristic is needed.

This is the matrix version of the split unitary group description in Gan, Qiu and Takeda,
*The regularized Siegel–Weil formula (the second term identity) and the Rallis inner product
formula*, §§2.1–2.2. For the basis-free description over a field, see
`TauCeti.SignedHermitianSpace.splitIsometryGroupEquiv`.
-/

public section

namespace Matrix

open GeneralLinearGroup

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S] [StarRing S]

/-- The two components of a unitary matrix over an exchange ring form the graph of inverse
transpose conjugated by the second component of the Hermitian Gram matrix. -/
theorem mem_unitaryGroupOf_iff_snd_eq_inverseTranspose
    (e : S ≃+* R × R) (he : ∀ x, e (star x) = (e x).swap)
    (J : GL n S) (hJ : (J : Matrix n n S).IsHermitian) (g : GL n S) :
    g ∈ unitaryGroupOf (J : Matrix n n S) ↔
      GeneralLinearGroup.map ((RingHom.snd R R).comp e.toRingHom) g =
        (GeneralLinearGroup.map ((RingHom.snd R R).comp e.toRingHom) J)⁻¹ *
          inverseTranspose (GeneralLinearGroup.map ((RingHom.fst R R).comp e.toRingHom) g) *
          GeneralLinearGroup.map ((RingHom.snd R R).comp e.toRingHom) J := by
  let p := @GeneralLinearGroup.map n _ _ S _ R _
  let f := (RingHom.fst R R).comp e.toRingHom
  let s := (RingHom.snd R R).comp e.toRingHom
  have hs (M : Matrix n n S) : (star M).map s = (M.map f)ᵀ := by
    ext i j
    exact congrArg Prod.snd (he (M j i))
  have hf (M : Matrix n n S) : (star M).map f = (M.map s)ᵀ := by
    ext i j
    exact congrArg Prod.fst (he (M j i))
  have hform : ((J : Matrix n n S).map s)ᵀ = (J : Matrix n n S).map f := by
    rw [← hf, star_eq_conjTranspose, hJ.eq]
  have hsuff : g ∈ unitaryGroupOf (J : Matrix n n S) ↔
      inverseTranspose ((p f g)⁻¹) * p s J * p s g = p s J := by
    rw [mem_unitaryGroupOf_iff, Units.ext_iff]
    simp only [Units.val_mul, coe_inverseTranspose, inv_inv]
    have h : (star (g : Matrix n n S) * (J : Matrix n n S) * (g : Matrix n n S)).map s =
        ((p f g : Matrix n n R)ᵀ * (p s J : Matrix n n R) * (p s g : Matrix n n R)) := by
      simp only [Matrix.map_mul, hs]
      rfl
    rw [← h]
    refine ⟨congrArg (fun M : Matrix n n S ↦ M.map s), fun eqS ↦ ?_⟩
    have eqF := congrArg Matrix.transpose eqS
    rw [h] at eqF
    simp only [transpose_mul, transpose_transpose] at eqF
    -- The matrix values of `p s J` and `p f J` are entrywise projections.
    have hJ' : (p s J : Matrix n n R)ᵀ = (p f J : Matrix n n R) := hform
    rw [hJ'] at eqF
    have hf' : (star (g : Matrix n n S) * (J : Matrix n n S) * (g : Matrix n n S)).map f =
        (J : Matrix n n S).map f := by
      rw [Matrix.map_mul, Matrix.map_mul, hf, Matrix.mul_assoc]
      exact eqF
    ext i j
    apply e.injective
    exact Prod.ext (congrFun (congrFun hf' i) j) (congrFun (congrFun eqS i) j)
  rw [hsuff, map_inv]
  -- Write both sides in terms of the projections `f` and `s` before cancelling units.
  change (inverseTranspose (p f g))⁻¹ * p s J * p s g = p s J ↔
    p s g = (p s J)⁻¹ * inverseTranspose (p f g) * p s J
  rw [mul_assoc, inv_mul_eq_iff_eq_mul, mul_assoc ((p s J)⁻¹), eq_inv_mul_iff_mul_eq]

/-- Projection to the first factor identifies the unitary group over an exchange ring with
`GL n R`. The inverse is given by the graph equation for the second component. -/
def unitaryGroupOf.exchangeFstEquiv
    (e : S ≃+* R × R) (he : ∀ x, e (star x) = (e x).swap)
    (J : GL n S) (hJ : (J : Matrix n n S).IsHermitian) :
    unitaryGroupOf (J : Matrix n n S) ≃* GL n R := by
  let E := (Units.mapEquiv (e.mapMatrix (m := n)).toMulEquiv).trans
    (GeneralLinearGroup.prodEquiv n R R)
  let f := (RingHom.fst R R).comp e.toRingHom
  let s := (RingHom.snd R R).comp e.toRingHom
  let C (a : GL n R) := (GeneralLinearGroup.map s J)⁻¹ * inverseTranspose a *
    GeneralLinearGroup.map s J
  have hE (g : GL n S) : E g = (GeneralLinearGroup.map f g, GeneralLinearGroup.map s g) := rfl
  have hm (g : GL n S) : g ∈ unitaryGroupOf (J : Matrix n n S) ↔ (E g).2 = C (E g).1 := by
    rw [hE]
    exact mem_unitaryGroupOf_iff_snd_eq_inverseTranspose e he J hJ g
  exact
    { toFun := fun g ↦ (E g.val).1
      invFun := fun a ↦ ⟨E.symm (a, C a), (hm _).mpr (by simp)⟩
      left_inv := fun g ↦ Subtype.ext (E.injective (by
        rw [MulEquiv.apply_symm_apply]
        exact Prod.ext rfl ((hm _).mp g.property).symm))
      right_inv := fun a ↦ congrArg Prod.fst (E.apply_symm_apply (a, C a))
      map_mul' := fun g h ↦ congrArg Prod.fst (E.map_mul g.val h.val) }

/-- The split unitary equivalence is entrywise projection. -/
@[simp] theorem unitaryGroupOf.exchangeFstEquiv_apply
    (e : S ≃+* R × R) (he : ∀ x, e (star x) = (e x).swap)
    (J : GL n S) (hJ : (J : Matrix n n S).IsHermitian) (g : unitaryGroupOf (J : Matrix n n S)) :
    exchangeFstEquiv e he J hJ g =
      GeneralLinearGroup.map ((RingHom.fst R R).comp e.toRingHom) g.val := (rfl)

end Matrix
