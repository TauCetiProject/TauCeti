/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.TorusAction
public import TauCeti.Geometry.Toric.Analytic.Fan.ZeroCone

/-!
# The zero-cone fan and the algebraic–analytic toric comparison

The fan of the zero cone has a single cone, so its toric scheme is the dense torus
(`TauCeti.Toric.Fan.isIso_denseTorusι_ofCone_bot`), the spectrum of the group algebra of the
character lattice `N →+ ℤ`. Every integral character is nonnegative on the zero cone, so each one
defines a global character function on the complex points of this scheme, and the character
functions of `m` and `-m` multiply to `1`. Hence a complex point, a morphism `Spec ℂ ⟶ X` over
`Spec ℂ`, determines a point of the coordinate-free complex torus `ComplexTorus N` by its
character values. This identifies `ComplexTorus N` with the complex points of the toric scheme of
the zero-cone fan, through the canonical dense-torus inclusion.

On the analytic side, `TauCeti.Toric.Fan.analyticZeroConeHomeomorph` identifies the analytic
realization of the same fan with `ComplexTorus N` through its dense-torus inclusion. This file
shows that the algebraic–analytic comparison `TauCeti.Toric.Fan.algebraicAnalyticEquiv` carries
the algebraic identification to the analytic one. Consequently the algebraic identification is a
torus-equivariant homeomorphism for the topology glued from the affine charts, and a
biholomorphism for the complex structure pulled back from the analytic realization and the
complex structure of the torus given by any finite free presentation of its character lattice.

## Main declarations

* `TauCeti.Toric.Fan.zeroConeAlgebraicComplexPointEquiv`: the complex torus is the set of complex
  points of the toric scheme of the zero-cone fan, a complex point corresponding to the torus point
  given by its character values
  (`TauCeti.Toric.Fan.coe_zeroConeAlgebraicComplexPointEquiv_symm_apply`).
* `TauCeti.Toric.Fan.coe_zeroConeAlgebraicComplexPointEquiv_apply`: the complex point of a torus
  point is the corresponding complex point of the dense torus, followed by the dense-torus
  inclusion.
* `TauCeti.Toric.Fan.analyticZeroConeHomeomorph_symm_algebraicAnalyticEquiv`: the
  algebraic–analytic comparison commutes with the identifications of both sides with the complex
  torus.
* `TauCeti.Toric.Fan.zeroConeAlgebraicComplexPointHomeomorph` and
  `TauCeti.Toric.Fan.zeroConeAlgebraicComplexPointDiffeomorph`: the identification is a
  homeomorphism and a biholomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.1, 1.3 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (hi : IsIntegralLattice i)

local notation "Φ₀" => ofCone hi (isToricCone_bot i)
local notation "h₀" => isRegular_ofCone hi (isRegularCone_bot hi)
local notation "z₀" => (Subtype.mk (⊥ : PointedCone ℝ V)
  (Iff.mpr (mem_ofCone_cones hi (isToricCone_bot i))
    (PointedCone.IsFaceOf.refl ⊥)) : Fan.cones Φ₀)

open AlgebraicComplexPoint

/-- The character functions of an integral character and of its negative multiply to `1` on the
complex points of the toric scheme of the zero-cone fan. -/
private theorem character_mul_character_neg (m : IntegralCharacter N)
    (p : (Φ₀).AlgebraicComplexPoint) :
    character Φ₀ m (mem_dualSemigroup_ofCone_bot hi m) p *
        character Φ₀ (-m) (mem_dualSemigroup_ofCone_bot hi (-m)) p = 1 := by
  rw [← character_add]
  simp only [add_neg_cancel, character_zero]

/-- The coordinate-free complex torus is the set of complex points of the toric scheme of the
zero-cone fan: a torus point is sent to its image under the canonical dense-torus inclusion, and a
complex point is recovered as the torus point whose value on an integral character is the value of
its character function. -/
noncomputable def zeroConeAlgebraicComplexPointEquiv :
    ComplexTorus N ≃ (Φ₀).AlgebraicComplexPoint where
  toFun := torusι ⟨z₀⟩
  invFun p :=
    { toFun m := Units.mkOfMulEqOne _ _ (character_mul_character_neg hi m p)
      map_zero_eq_one' := Units.ext (character_zero p)
      map_add_eq_mul' m m' := Units.ext (character_add m m' _ _ p) }
  left_inv t := DFunLike.ext _ _ fun m ↦ Units.ext (character_torusι m _ _ t)
  right_inv p := by
    obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
    rw [torusι_eq_ofAffinePoint _ σ]
    congr 1
    refine AffineSemigroupComplexPoint.ext fun s ↦ ?_
    simp

/-- The complex point of the toric scheme of the zero-cone fan attached to a torus point is its
image under the canonical dense-torus inclusion. -/
@[simp]
theorem zeroConeAlgebraicComplexPointEquiv_apply (t : ComplexTorus N) :
    zeroConeAlgebraicComplexPointEquiv hi t = torusι ⟨z₀⟩ t :=
  (rfl)

/-- The value of the torus point of a complex point of the toric scheme of the zero-cone fan on an
integral character is the value of the character function. -/
@[simp]
theorem coe_zeroConeAlgebraicComplexPointEquiv_symm_apply (p : (Φ₀).AlgebraicComplexPoint)
    (m : IntegralCharacter N) :
    ((zeroConeAlgebraicComplexPointEquiv hi).symm p m : ℂ) =
      character Φ₀ m (mem_dualSemigroup_ofCone_bot hi m) p :=
  (rfl)

/-- As a morphism `Spec ℂ ⟶ X` over `Spec ℂ`, the complex point of the toric scheme of the
zero-cone fan attached to a torus point `t` is `Spec` of the complex point of the dense torus
given by `t`, followed by the dense-torus inclusion, which is an isomorphism. -/
theorem coe_zeroConeAlgebraicComplexPointEquiv_apply (t : ComplexTorus N) :
    (zeroConeAlgebraicComplexPointEquiv hi t).1 =
      Spec.map (CommRingCat.ofHom (t • (default : AffineSemigroupComplexPoint
        (dualSemigroup hi (⊥ : PointedCone ℝ V)))).toRingHom) ≫ (Φ₀).denseTorusι ⟨z₀⟩ := by
  rw [zeroConeAlgebraicComplexPointEquiv_apply, torusι_eq_ofAffinePoint _ z₀,
    coe_ofAffinePoint, denseTorusι_eq_affineToricChartι _ _ z₀.2]

/-- Torus translation of a complex point of the toric scheme of the zero-cone fan multiplies its
torus point. -/
@[simp]
theorem zeroConeAlgebraicComplexPointEquiv_symm_smul (t : ComplexTorus N)
    (p : (Φ₀).AlgebraicComplexPoint) :
    (zeroConeAlgebraicComplexPointEquiv hi).symm (t • p) =
      t * (zeroConeAlgebraicComplexPointEquiv hi).symm p :=
  DFunLike.ext _ _ fun m ↦ Units.ext (by simp)

/-- The algebraic–analytic comparison commutes with the identifications of both sides with the
complex torus: the torus point of the point of the analytic realization corresponding to a complex
point of the toric scheme is the torus point given by its character values. -/
@[simp]
theorem analyticZeroConeHomeomorph_symm_algebraicAnalyticEquiv
    (p : (Φ₀).AlgebraicComplexPoint) :
    (analyticZeroConeHomeomorph hi).symm (algebraicAnalyticEquiv h₀ p) =
      (zeroConeAlgebraicComplexPointEquiv hi).symm p := by
  conv_lhs => rw [← (zeroConeAlgebraicComplexPointEquiv hi).apply_symm_apply p]
  rw [zeroConeAlgebraicComplexPointEquiv_apply, algebraicAnalyticEquiv_torusι,
    analyticZeroConeHomeomorph_symm_analyticTorusι]

/-- The identification of the complex torus with the complex points of the toric scheme of the
zero-cone fan is a homeomorphism, for the topology glued from the affine charts. -/
noncomputable def zeroConeAlgebraicComplexPointHomeomorph :
    ComplexTorus N ≃ₜ (Φ₀).AlgebraicComplexPoint where
  toEquiv := zeroConeAlgebraicComplexPointEquiv hi
  continuous_toFun :=
    ((algebraicAnalyticHomeomorph h₀).symm.continuous.comp
      (analyticZeroConeHomeomorph hi).continuous).congr fun t ↦ by
        rw [Function.comp_apply, coe_algebraicAnalyticHomeomorph_symm,
          analyticZeroConeHomeomorph_apply, algebraicAnalyticEquiv_symm_analyticTorusι,
          Equiv.toFun_as_coe, zeroConeAlgebraicComplexPointEquiv_apply]
  continuous_invFun :=
    ((analyticZeroConeHomeomorph hi).symm.continuous.comp
      (algebraicAnalyticHomeomorph h₀).continuous).congr fun p ↦ by
        rw [Function.comp_apply, coe_algebraicAnalyticHomeomorph,
          analyticZeroConeHomeomorph_symm_algebraicAnalyticEquiv, Equiv.invFun_as_coe]

/-- The homeomorphism is the identification `zeroConeAlgebraicComplexPointEquiv`. -/
@[simp]
theorem coe_zeroConeAlgebraicComplexPointHomeomorph :
    ⇑(zeroConeAlgebraicComplexPointHomeomorph hi) = zeroConeAlgebraicComplexPointEquiv hi :=
  (rfl)

/-- The inverse homeomorphism is the inverse identification. -/
@[simp]
theorem coe_zeroConeAlgebraicComplexPointHomeomorph_symm :
    ⇑(zeroConeAlgebraicComplexPointHomeomorph hi).symm =
      (zeroConeAlgebraicComplexPointEquiv hi).symm :=
  (rfl)

variable {ι : Type*} [Fintype ι] (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

/-- The identification of the complex torus with the complex points of the toric scheme of the
zero-cone fan is a biholomorphism, for the complex structure of the torus given by a finite free
presentation `e` of its character lattice and the complex structure pulled back from the analytic
realization, at every smoothness order. -/
noncomputable def zeroConeAlgebraicComplexPointDiffeomorph (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := algebraicComplexPointChartedSpace h₀
    ComplexTorus N ≃ₘ^n⟮𝓘(ℂ, ι → ℂ), 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)⟯
      (Φ₀).AlgebraicComplexPoint :=
  let _ := complexTorusChartedSpace e
  letI := (Φ₀).analyticChartedSpace h₀
  letI := algebraicComplexPointChartedSpace h₀
  (analyticZeroConeDiffeomorph hi e n).trans (algebraicAnalyticDiffeomorph h₀ n).symm

/-- The biholomorphism is the identification `zeroConeAlgebraicComplexPointEquiv`, the canonical
dense-torus inclusion. -/
@[simp]
theorem coe_zeroConeAlgebraicComplexPointDiffeomorph (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := algebraicComplexPointChartedSpace h₀
    ⇑(zeroConeAlgebraicComplexPointDiffeomorph hi e n) = zeroConeAlgebraicComplexPointEquiv hi := by
  let _ := complexTorusChartedSpace e
  let := (Φ₀).analyticChartedSpace h₀
  let := algebraicComplexPointChartedSpace h₀
  funext t
  rw [zeroConeAlgebraicComplexPointDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    analyticZeroConeDiffeomorph_apply, coe_algebraicAnalyticDiffeomorph_symm,
    algebraicAnalyticEquiv_symm_analyticTorusι, zeroConeAlgebraicComplexPointEquiv_apply]

/-- The inverse biholomorphism is the inverse identification, which reads a complex point through
its character values. -/
@[simp]
theorem coe_zeroConeAlgebraicComplexPointDiffeomorph_symm (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := algebraicComplexPointChartedSpace h₀
    ⇑(zeroConeAlgebraicComplexPointDiffeomorph hi e n).symm =
      (zeroConeAlgebraicComplexPointEquiv hi).symm := by
  let _ := complexTorusChartedSpace e
  let := algebraicComplexPointChartedSpace h₀
  funext p
  apply (zeroConeAlgebraicComplexPointEquiv hi).injective
  rw [← coe_zeroConeAlgebraicComplexPointDiffeomorph hi e n, Diffeomorph.apply_symm_apply,
    coe_zeroConeAlgebraicComplexPointDiffeomorph, Equiv.apply_symm_apply]

end TauCeti.Toric.Fan
