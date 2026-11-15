/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# Differential of multiplication on a projective Weierstrass curve

Over a field, the function field of the projective Weierstrass model is identified with the
function field of its affine equation. This file transports the pullback of Kähler differentials
along the scheme-theoretic multiplication map through that identification. In particular, the
scheme map acts on the transported invariant differential by multiplication by its integer.
-/

/-!
## References

* N. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.5.4.
-/

public section

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

noncomputable section

/-- Pullback along the projective scheme morphism `[n]`, expressed on the affine equation's
function field and transported back to the projective function field. -/
noncomputable def projModelMulByFunctionFieldAlgHom (n : ℤ) [NeZero n] :
    W.projModel.functionField →ₐ[K] W.projModel.functionField :=
  (W.projModelFunctionFieldAlgEquiv).symm.toAlgHom.comp
    ((TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine (NeZero.ne n)).fieldPullback.comp
      W.projModelFunctionFieldAlgEquiv.toAlgHom)

/-- The algebra homomorphism `projModelMulByFunctionFieldAlgHom` is the pullback on function fields
induced by the scheme morphism `[n]`. -/
@[simp]
theorem projModelMulByFunctionFieldAlgHom_toRingHom (n : ℤ) [NeZero n] :
    ↑(W.projModelMulByFunctionFieldAlgHom n) = W.mulByFunctionFieldPullback n := by
  ext x
  apply W.projModelFunctionFieldEquiv.injective
  simp [projModelMulByFunctionFieldAlgHom, ← AlgEquiv.coe_toRingEquiv,
    W.projModelFunctionFieldEquiv_mulByFunctionFieldPullback]

/-- **The scheme-theoretic multiplication map acts on the invariant differential by `n`.**
Transport the invariant differential of the affine equation to the function field of the
projective model. Pullback along the scheme map `[n]` is then multiplication by `n`. -/
@[simp]
theorem mapSemilinear_projModelMulBy_invariantDifferential (n : ℤ) [NeZero n] :
    KaehlerDifferential.mapSemilinear
        (W.projModelMulByFunctionFieldAlgHom n)
        (KaehlerDifferential.mapSemilinear
          (W.projModelFunctionFieldAlgEquiv).symm.toAlgHom
          (W.toAffine.invariantDifferential)) =
      n • KaehlerDifferential.mapSemilinear
        (W.projModelFunctionFieldAlgEquiv).symm.toAlgHom
        (W.toAffine.invariantDifferential) := by
  let e := W.projModelFunctionFieldAlgEquiv
  let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine (NeZero.ne n)
  -- Unfold only the conjugated pullback, folding the comparison and isogeny into `e` and `φ`.
  -- This exposes the composite required by `mapSemilinear_comp_apply` without unfolding them.
  change KaehlerDifferential.mapSemilinear
        (e.symm.toAlgHom.comp (φ.fieldPullback.comp e.toAlgHom))
        (KaehlerDifferential.mapSemilinear e.symm.toAlgHom
          W.toAffine.invariantDifferential) = _
  rw [KaehlerDifferential.mapSemilinear_comp_apply]
  conv_lhs =>
    arg 2
    rw [KaehlerDifferential.mapSemilinear_comp_apply]
  rw [KaehlerDifferential.mapSemilinear_apply_symm_apply]
  rw [← TauCeti.Isogeny.pullbackDifferential_apply,
    TauCeti.Isogeny.pullbackDifferential_mulByIntIsogeny_invariantDifferential]
  · exact (KaehlerDifferential.mapSemilinear e.symm.toAlgHom).toAddMonoidHom.map_zsmul n _

end

end WeierstrassCurve
