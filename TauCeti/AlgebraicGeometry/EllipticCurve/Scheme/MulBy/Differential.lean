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

/-- The algebra structure on the projective function field transported from the affine
function field. -/
instance projModelFunctionFieldAlgebra : Algebra K W.projModel.functionField := by
  let f : K →+* W.projModel.functionField :=
    W.projModelFunctionFieldEquiv.symm.toRingHom.comp (algebraMap K W.toAffine.FunctionField)
  exact f.toAlgebra

/-- The function-field comparison between the projective model and the affine equation, as an
equivalence of `K`-algebras. -/
noncomputable def projModelFunctionFieldAlgEquiv :
    W.projModel.functionField ≃ₐ[K] W.toAffine.FunctionField :=
  AlgEquiv.ofRingEquiv (f := W.projModelFunctionFieldEquiv) (by
    intro x
    -- The transported algebra map is the affine algebra map followed by the inverse comparison.
    -- Expose that composite so the ring equivalence and its inverse cancel by `simp`.
    change W.projModelFunctionFieldEquiv
      (W.projModelFunctionFieldEquiv.symm (algebraMap K W.toAffine.FunctionField x)) = _
    simp)

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
  simp [projModelMulByFunctionFieldAlgHom, projModelFunctionFieldAlgEquiv,
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
  have hcancel (ω : KaehlerDifferential K W.toAffine.FunctionField) :
      KaehlerDifferential.mapSemilinear e.toAlgHom
        (KaehlerDifferential.mapSemilinear e.symm.toAlgHom ω) = ω := by
    rw [← KaehlerDifferential.mapSemilinear_comp_apply, AlgEquiv.comp_symm,
      KaehlerDifferential.mapSemilinear_id_apply]
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
  rw [hcancel]
  rw [← TauCeti.Isogeny.pullbackDifferential_apply,
    TauCeti.Isogeny.pullbackDifferential_mulByIntIsogeny_invariantDifferential]
  · exact (KaehlerDifferential.mapSemilinear e.symm.toAlgHom).toAddMonoidHom.map_zsmul n _

end

end WeierstrassCurve
