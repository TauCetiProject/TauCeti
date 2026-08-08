/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Isomorphism of point groups induced by a change of variables

Mathlib's affine `Point` API provides the group homomorphism `WeierstrassCurve.Affine.Point.map`
induced by a change of the base field (for a *fixed* Weierstrass curve), but not the isomorphism
of point groups induced by an admissible change of variables between two *different* curves.
This file supplies that: for `C : VariableChange F` and a Weierstrass curve `W` over a field `F`
— no ellipticity hypothesis, matching Mathlib's point group — the admissible change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)` gives a group isomorphism `(C • W).Point ≃+ W.Point`. All
definitions are computable (given decidable equality on `F`): the inverse of the isomorphism is
given explicitly by the change of variables `C⁻¹`, not obtained from bijectivity via choice.

The coordinate-level transformation laws this rests on — for `negY`, `addX`, `addY`, `Equation`,
`Nonsingular` and `slope` — are in
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, stated over a commutative ring
wherever they do not need a field.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapVariableChange`: the group homomorphism
  `(C • W).Point →+ W.Point`, `(x, y) ↦ (u²x + r, u³y + u²sx + t)`.
* `WeierstrassCurve.Affine.Point.equivVariableChange`: the group isomorphism
  `(C • W).Point ≃+ W.Point`, with inverse coming from `C⁻¹` (transported along
  `inv_smul_smul` by Mathlib's `AddEquiv.cast`).

This is the variable-change point isomorphism that the quadratic-twist layer of
`TauCetiRoadmap/EllipticCurves/README.md` (§Layer 5) consumes: the twist point isomorphism
`quadraticTwistPointEquiv` there is assembled from this equivalence and Galois descent.

Adapted from the FLT project's quadratic-twist development (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, FLT PR #1088, merged there as
`bc2fe8ff7396`, Apache 2.0, by Michael Stoll and Claude). Following the repository's convention
for adapted material, the source authorship is credited here rather than in the copyright
header. Ported with the transformation laws generalised from a field to a commutative ring and
the ellipticity hypothesis removed.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### The induced isomorphism of point groups -/

namespace Point

variable [DecidableEq F]

-- `AddEquiv.cast` between point groups sends an affine point to the affine point with the same
-- coordinates. Private: it is transport plumbing for the proofs below, not interface. It is also
-- not a `simp` lemma — `simp` rewrites `AddEquiv.cast h` to a plain `cast` first, so this
-- left-hand side is not in normal form and would never fire.
private lemma cast_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point) h (some x y hns)
      = some x y (h ▸ hns) := by
  subst h; rfl

/-- The group homomorphism `(C • W).Point →+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun P := match P with
    | .zero => .zero
    | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
        ((variableChange_nonsingular W C x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addX,
        variableChange_addY]

/-- `mapVariableChange` sends `(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
@[simp] lemma mapVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := by
  simp only [mapVariableChange]
  rfl

/-- The change of variables is injective on points: it is inverted by the change of variables
`C⁻¹`. Private: it exists to build `equivVariableChange`, which then carries the same
injectivity for users. -/
private lemma mapVariableChange_injective : Function.Injective (mapVariableChange W C) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · rw [← zero_def, (mapVariableChange W C).map_zero, mapVariableChange_some] at h
    exact absurd h.symm (some_ne_zero _)
  · rw [← zero_def, (mapVariableChange W C).map_zero, mapVariableChange_some] at h
    exact absurd h (some_ne_zero _)
  · rw [mapVariableChange_some, mapVariableChange_some] at h
    simp only [some.injEq] at h ⊢
    obtain ⟨hX, hY⟩ := h
    have hx : x₁ = x₂ := (variableChange_X_inj C).mp hX
    exact ⟨hx, (variableChange_Y_inj C hx).mp hY⟩

/-- Applying the change of variables `C⁻¹` (transported along `C⁻¹ • C • W = W`) and then `C`
recovers the original point. -/
private lemma mapVariableChange_mapVariableChange_inv (P : W.toAffine.Point) :
    mapVariableChange W C (mapVariableChange (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P)) = P := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← zero_def, _root_.map_zero]
  · rw [cast_some, mapVariableChange_some, mapVariableChange_some]
    simp only [some.injEq, VariableChange.inv_def, Units.val_inv_eq_inv_val]
    constructor <;> field

/-- **Identity law.** The trivial change of variables induces the transport along
`(1 : VariableChange F) • W = W`. -/
@[simp] lemma mapVariableChange_one :
    mapVariableChange W 1
      = (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (one_smul (VariableChange F) W)).toAddMonoidHom := by
  ext P
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← zero_def, _root_.map_zero]
  · rw [mapVariableChange_some]
    simp only [AddEquiv.coe_toAddMonoidHom, cast_some, some.injEq]
    exact ⟨by simp [VariableChange.one_def], by simp [VariableChange.one_def]⟩

/-- **Cocycle law.** Composing changes of variables composes the induced maps: `C * C'` acts as
`C` into `C' • W` followed by `C'`, transported along `(C * C') • W = C • (C' • W)`. This is
what makes a family of variable changes a descent datum. -/
@[simp] lemma mapVariableChange_mul (C' : VariableChange F) :
    mapVariableChange W (C * C')
      = (mapVariableChange W C').comp ((mapVariableChange (C' • W) C).comp
          (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
            (mul_smul C C' W)).toAddMonoidHom) := by
  ext P
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← zero_def, _root_.map_zero]
  · rw [mapVariableChange_some]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      cast_some, mapVariableChange_some, some.injEq]
    exact ⟨variableChange_X_mul C C' x, variableChange_Y_mul C C' x y⟩

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. It is `mapVariableChange` upgraded to an
equivalence; the inverse is the change of variables `C⁻¹`, not obtained from bijectivity via
choice. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  __ := mapVariableChange W C
  invFun P := mapVariableChange (C • W) C⁻¹
    (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
      (inv_smul_smul C W).symm P)
  left_inv := Function.RightInverse.leftInverse_of_injective
    (mapVariableChange_mapVariableChange_inv W C) (mapVariableChange_injective W C)
  right_inv := mapVariableChange_mapVariableChange_inv W C

/-- `equivVariableChange` is `mapVariableChange` as a bijection: the two agree as functions, so
`mapVariableChange_some` computes both. -/
@[simp] lemma coe_equivVariableChange :
    ⇑(equivVariableChange W C) = ⇑(mapVariableChange W C) := by
  simp only [equivVariableChange]
  rfl

-- The inverse of `equivVariableChange` is literally the change of variables `C⁻¹`, transported
-- along `C⁻¹ • C • W = W`. Private: it exists to prove `equivVariableChange_symm_some`, which is
-- the normal form worth having — as a `simp` lemma this would rewrite that one's left-hand side.
private lemma coe_equivVariableChange_symm :
    ⇑(equivVariableChange W C).symm = fun P ↦ mapVariableChange (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P) := by
  simp only [equivVariableChange]
  rfl

/-- The inverse of `equivVariableChange` acts on an affine point by the inverse change of
variables `C⁻¹`, sending `(x, y)` to `(u⁻²(x - r), u⁻³(y - sx + sr - t))`. -/
@[simp] lemma equivVariableChange_symm_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (equivVariableChange W C).symm (.some x y h)
      = .some ((C⁻¹.u : F) ^ 2 * x + C⁻¹.r)
          ((C⁻¹.u : F) ^ 3 * y + (C⁻¹.u : F) ^ 2 * C⁻¹.s * x + C⁻¹.t)
          ((variableChange_nonsingular (C • W) C⁻¹ x y).mpr
            ((inv_smul_smul C W).symm ▸ h)) := by
  simp only [coe_equivVariableChange_symm, cast_some, mapVariableChange_some]

/-! ### Compatibility with base change -/

section BaseChange

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  (W' : WeierstrassCurve R)
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (D : VariableChange R)

/-- The base-change form of `map_variableChange`: base changing `D • W'` to `A` is changing the
base-changed curve `W'⁄A` by the base-changed variable change `D⁄A`. -/
lemma baseChange_variableChange (A : Type*) [CommRing A] [Algebra R A] :
    (D.baseChange A) • (W'.baseChange A) = (D • W').baseChange A :=
  map_variableChange (W := W') (C := D) (φ := algebraMap R A)

/-- **Naturality in the base field.** Changing variables by `D` and then extending scalars along
`f` agrees with extending scalars and then changing variables by `D`. Both sides are transported
along `baseChange_variableChange`, which identifies the base change of `D • W'` with the change
of variables by `D⁄F` applied to the base change of `W'`.

The transports are spelled as plain `cast`s rather than `AddEquiv.cast`s, since `simp` rewrites
the latter to the former: this way the left-hand side is in `simp` normal form and the lemma
fires. -/
@[simp]
lemma map_mapVariableChange (f : F →ₐ[S] K) (P : ((D • W')⁄F).Point) :
    Point.map f (mapVariableChange (W'⁄F) (D.baseChange F)
        (cast (congrArg (fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (baseChange_variableChange W' D F).symm) P))
      = mapVariableChange (W'⁄K) (D.baseChange K)
          (cast (congrArg (fun V : WeierstrassCurve K ↦ V.toAffine.Point)
            (baseChange_variableChange W' D K).symm) (Point.map f P)) := by
  -- The statement transports with a plain `cast`, which is the `simp`-normal form (see the
  -- module docstring); the proof needs the `AddEquiv.cast` spelling, to which it is definitionally
  -- equal, so that `cast_some` applies.
  change Point.map f (mapVariableChange (W'⁄F) (D.baseChange F)
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (baseChange_variableChange W' D F).symm P))
    = mapVariableChange (W'⁄K) (D.baseChange K)
        (AddEquiv.cast (M := fun V : WeierstrassCurve K ↦ V.toAffine.Point)
          (baseChange_variableChange W' D K).symm (Point.map f P))
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← zero_def, _root_.map_zero]
  · rw [cast_some, mapVariableChange_some, Point.map_some, Point.map_some, cast_some,
      mapVariableChange_some]
    simp only [some.injEq]
    exact ⟨by simpa only [VariableChange.map_baseChange, RingHom.coe_coe] using
        (variableChange_X_map (C := D.baseChange F) (f : F →+* K) x).symm,
      by simpa only [VariableChange.map_baseChange, RingHom.coe_coe] using
        (variableChange_Y_map (C := D.baseChange F) (f : F →+* K) x y).symm⟩

end BaseChange

end Point

end WeierstrassCurve.Affine

end
