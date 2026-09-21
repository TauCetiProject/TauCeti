/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.PolePoints
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PullbackAdd
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# The additive group of morphisms between elliptic curves

The carrier `Isogeny.Hom W₁ W₂` — the isogenies `W₁ → W₂` together with the zero map — is
identified with the point at infinity together with the points of `W₂` over the function field of
`W₁` whose `x`-coordinate has a pole at the place at infinity, and inherits the group law of those
points.

A morphism is determined by its **tautological point**: the point at infinity for the zero map,
and for an isogeny the point of `W₂` over `F(W₁)` cut out by the pulled-back coordinate functions.
That point has a pole at infinity exactly because an isogeny is pointed, and every point with such
a pole arises from a pointed coordinate pullback, so the tautological point is a bijection onto
the subgroup `polePoints W₂ (Place.infinity W₁)`. The addition on `Hom W₁ W₂` is the one making
this bijection additive; the zero and the negation are those the carrier already has.

## Main definitions

* `TauCeti.Isogeny.Hom.tautologicalPoint`: the tautological point of a morphism.
* `TauCeti.Isogeny.Hom.polePointsAddEquiv`: `Hom W₁ W₂ ≃+ polePoints W₂ (Place.infinity W₁)`.
* `TauCeti.Isogeny.Hom.compRightHom`: precomposition by a morphism, as an additive homomorphism;
  `zsmul_comp` and `nsmul_comp` are its `map_zsmul` and `map_nsmul`.
* The `AddCommGroup (Hom W₁ W₂)` instance.

## Main results

* `TauCeti.Isogeny.Hom.ofIsogeny_add_ofIsogeny`: the sum of two isogenies whose tautological
  points do not cancel is the isogeny with pullback `CoordinatePullback.add`.
* `TauCeti.Isogeny.Hom.add_comp`: composition is additive in the outer morphism.

## Provenance

The identification of the morphisms with the pole points is Silverman III.4 read at the generic
point. Its ingredients are the tautological point of a coordinate pullback and its injectivity
(`CoordinatePullback.tautologicalPoint`, `CoordinatePullback.tautologicalPoint_injective`), the sum
of two coordinate pullbacks (`CoordinatePullback.add`), the pole criterion for pointedness
(`CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace`) and the subgroup of points with a pole
at a place (`polePoints`).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

namespace Isogeny

variable [W₂.IsElliptic]

namespace Hom

open scoped Classical in
/-- **The tautological point of a morphism**: the point at infinity for the zero map, and the
tautological point of the coordinate pullback for an isogeny. -/
noncomputable def tautologicalPoint (f : Hom W₁ W₂) : (W₂⁄W₁.FunctionField).toAffine.Point :=
  if hf : f = 0 then 0 else (toIsogeny hf).pullback.tautologicalPoint

@[simp]
theorem tautologicalPoint_zero : (0 : Hom W₁ W₂).tautologicalPoint = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

@[simp]
theorem tautologicalPoint_ofIsogeny (φ : Isogeny W₁ W₂) :
    (ofIsogeny φ).tautologicalPoint = φ.pullback.tautologicalPoint := by
  rw [tautologicalPoint, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

/-- **A morphism vanishes exactly when its tautological point is the point at infinity.** -/
@[simp]
theorem tautologicalPoint_eq_zero_iff {f : Hom W₁ W₂} : f.tautologicalPoint = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact iff_of_true tautologicalPoint_zero rfl
  · exact iff_of_false
      (tautologicalPoint_ofIsogeny φ ▸ CoordinatePullback.tautologicalPoint_ne_zero _)
      (ofIsogeny_ne_zero φ)

/-- **A morphism is determined by its tautological point.** -/
theorem tautologicalPoint_injective :
    Function.Injective (tautologicalPoint (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact (tautologicalPoint_eq_zero_iff.1 (h.symm.trans tautologicalPoint_zero)).symm
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · exact tautologicalPoint_eq_zero_iff.1 (h.trans tautologicalPoint_zero)
  rw [tautologicalPoint_ofIsogeny, tautologicalPoint_ofIsogeny] at h
  rw [Isogeny.ext (CoordinatePullback.tautologicalPoint_injective h)]

/-- **Extensionality: morphisms with the same tautological point are equal.** -/
@[ext]
theorem ext_tautologicalPoint {f g : Hom W₁ W₂} (h : f.tautologicalPoint = g.tautologicalPoint) :
    f = g :=
  tautologicalPoint_injective h

@[simp]
theorem tautologicalPoint_inj {f g : Hom W₁ W₂} :
    f.tautologicalPoint = g.tautologicalPoint ↔ f = g :=
  tautologicalPoint_injective.eq_iff

/-- **The tautological point of `-f` is the negative of that of `f`.** -/
@[simp]
theorem tautologicalPoint_neg (f : Hom W₁ W₂) : (-f).tautologicalPoint = -f.tautologicalPoint := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [Hom.neg_zero, tautologicalPoint_zero, _root_.neg_zero]
  · simp only [neg_ofIsogeny, tautologicalPoint_ofIsogeny, Isogeny.tautologicalPoint_comp,
      negIsogeny_pullback, tautologicalPoint_negPullback, map_neg]
    rw [tautologicalPoint_eq_map_genericPoint]

/-- **The tautological point of a morphism has a pole at infinity**, or is the point at
infinity. -/
theorem tautologicalPoint_mem_polePoints (f : Hom W₁ W₂) :
    f.tautologicalPoint ∈ polePoints W₂ (Place.infinity W₁) := by
  rw [mem_polePoints_iff]
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact Or.inl tautologicalPoint_zero
  · refine Or.inr ?_
    rw [tautologicalPoint_ofIsogeny, Place.valuation_infinity,
      CoordinatePullback.xCoord_tautologicalPoint, ← AdjoinRoot.algebraMap_eq]
    exact Isogeny.one_lt_infinityPlace_pullback_X φ

open scoped Classical in
/-- **The morphism with a given tautological point**: the zero map at the point at infinity, and
otherwise the isogeny whose pullback evaluates the coordinate functions at the point, pointed
because `x` has a pole at infinity there. -/
noncomputable def ofPolePoint (Q : polePoints W₂ (Place.infinity W₁)) : Hom W₁ W₂ :=
  if hQ : (Q : (W₂⁄W₁.FunctionField).toAffine.Point) = 0 then 0 else
    ofIsogeny ⟨CoordinateRing.evalAlgHom (Point.nonsingular_coords hQ).left,
      CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace _ (algebraMap F[X] _ X) (by
        rw [AdjoinRoot.algebraMap_eq, CoordinateRing.evalAlgHom_of_X, ← Place.valuation_infinity]
        exact ((mem_polePoints_iff _ _ _).1 Q.2).resolve_left hQ)⟩

/-- **The tautological point of `ofPolePoint Q` is `Q`.** -/
@[simp]
theorem tautologicalPoint_ofPolePoint (Q : polePoints W₂ (Place.infinity W₁)) :
    (ofPolePoint Q).tautologicalPoint = Q := by
  by_cases hQ : (Q : (W₂⁄W₁.FunctionField).toAffine.Point) = 0
  · rw [ofPolePoint, dite_eq_left_of_eq_true (eq_true hQ), tautologicalPoint_zero, hQ]
  · rw [ofPolePoint, dite_eq_right_of_eq_false (eq_false hQ), tautologicalPoint_ofIsogeny]
    exact Point.eq_of_coords (CoordinatePullback.tautologicalPoint_ne_zero _) hQ
      (by rw [CoordinatePullback.xCoord_tautologicalPoint, CoordinateRing.evalAlgHom_of_X])
      (by rw [CoordinatePullback.yCoord_tautologicalPoint, CoordinateRing.evalAlgHom_root])

/-- **Addition of morphisms**: the morphism whose tautological point is the sum of the
tautological points. -/
noncomputable instance : Add (Hom W₁ W₂) :=
  ⟨fun f g ↦ ofPolePoint (⟨f.tautologicalPoint, tautologicalPoint_mem_polePoints f⟩ +
    ⟨g.tautologicalPoint, tautologicalPoint_mem_polePoints g⟩)⟩

noncomputable instance : Sub (Hom W₁ W₂) := ⟨fun f g ↦ f + -g⟩

noncomputable instance : SMul ℕ (Hom W₁ W₂) := ⟨nsmulRec⟩

noncomputable instance : SMul ℤ (Hom W₁ W₂) := ⟨zsmulRec⟩

/-- **The tautological point of a sum is the sum of the tautological points.** -/
@[simp]
theorem tautologicalPoint_add (f g : Hom W₁ W₂) :
    (f + g).tautologicalPoint = f.tautologicalPoint + g.tautologicalPoint :=
  tautologicalPoint_ofPolePoint _

/-- **The tautological point of a difference is the difference of the tautological points.** -/
@[simp]
theorem tautologicalPoint_sub (f g : Hom W₁ W₂) :
    (f - g).tautologicalPoint = f.tautologicalPoint - g.tautologicalPoint := by
  rw [sub_eq_add_neg, ← tautologicalPoint_neg, ← tautologicalPoint_add]; rfl

/-- **The tautological point of `n • f` is `n • f.tautologicalPoint`.** -/
@[simp]
theorem tautologicalPoint_nsmul (f : Hom W₁ W₂) (n : ℕ) :
    (n • f).tautologicalPoint = n • f.tautologicalPoint := by
  induction n with
  | zero => exact tautologicalPoint_zero.trans (zero_nsmul _).symm
  | succ n ih => rw [succ_nsmul, ← ih, ← tautologicalPoint_add]; rfl

/-- **The tautological point of `n • f` is `n • f.tautologicalPoint`, for an integer `n`.** -/
@[simp]
theorem tautologicalPoint_zsmul (f : Hom W₁ W₂) (n : ℤ) :
    (n • f).tautologicalPoint = n • f.tautologicalPoint := by
  cases n with
  | ofNat n => exact (tautologicalPoint_nsmul f n).trans (natCast_zsmul _ _).symm
  | negSucc n => rw [negSucc_zsmul, ← tautologicalPoint_nsmul, ← tautologicalPoint_neg]; rfl

/-- **The additive group of morphisms**, transported from the points with a pole at infinity
along the tautological point. -/
noncomputable instance : AddCommGroup (Hom W₁ W₂) :=
  Function.Injective.addCommGroup
    (fun f : Hom W₁ W₂ ↦ (⟨f.tautologicalPoint, tautologicalPoint_mem_polePoints f⟩ :
      polePoints W₂ (Place.infinity W₁)))
    (fun _ _ h ↦ tautologicalPoint_injective (congrArg Subtype.val h))
    (Subtype.ext tautologicalPoint_zero)
    (fun _ _ ↦ Subtype.ext (tautologicalPoint_add _ _))
    (fun _ ↦ Subtype.ext (tautologicalPoint_neg _))
    (fun _ _ ↦ Subtype.ext (tautologicalPoint_sub _ _))
    (fun _ _ ↦ Subtype.ext (tautologicalPoint_nsmul _ _))
    (fun _ _ ↦ Subtype.ext (tautologicalPoint_zsmul _ _))

/-- **Morphisms are the point at infinity together with the points with a pole at infinity, as
additive groups.** -/
noncomputable def polePointsAddEquiv : Hom W₁ W₂ ≃+ polePoints W₂ (Place.infinity W₁) where
  toFun f := ⟨f.tautologicalPoint, tautologicalPoint_mem_polePoints f⟩
  invFun := ofPolePoint
  left_inv _ := tautologicalPoint_injective (tautologicalPoint_ofPolePoint _)
  right_inv Q := Subtype.ext (tautologicalPoint_ofPolePoint Q)
  map_add' _ _ := Subtype.ext (tautologicalPoint_add _ _)

/-- The inverse of the additive equivalence is `ofPolePoint`. -/
@[simp]
theorem polePointsAddEquiv_symm_apply (Q : polePoints W₂ (Place.infinity W₁)) :
    polePointsAddEquiv.symm Q = ofPolePoint Q :=
  (rfl)

@[simp]
theorem ofPolePoint_zero : ofPolePoint (0 : polePoints W₂ (Place.infinity W₁)) = 0 := by
  rw [← polePointsAddEquiv_symm_apply, map_zero]

@[simp]
theorem ofPolePoint_add (Q R : polePoints W₂ (Place.infinity W₁)) :
    ofPolePoint (Q + R) = ofPolePoint Q + ofPolePoint R := by
  rw [← polePointsAddEquiv_symm_apply, map_add, polePointsAddEquiv_symm_apply,
    polePointsAddEquiv_symm_apply]

@[simp]
theorem ofPolePoint_neg (Q : polePoints W₂ (Place.infinity W₁)) :
    ofPolePoint (-Q) = -ofPolePoint Q := by
  rw [← polePointsAddEquiv_symm_apply, map_neg, polePointsAddEquiv_symm_apply]

@[simp]
theorem coe_polePointsAddEquiv_apply (f : Hom W₁ W₂) :
    (polePointsAddEquiv f : (W₂⁄W₁.FunctionField).toAffine.Point) = f.tautologicalPoint :=
  (rfl)

/-- **Two isogenies whose tautological points cancel sum to the zero map.** -/
theorem ofIsogeny_add_ofIsogeny_eq_zero {φ ψ : Isogeny W₁ W₂}
    (h : φ.pullback.tautologicalPoint + ψ.pullback.tautologicalPoint = 0) :
    ofIsogeny φ + ofIsogeny ψ = 0 :=
  tautologicalPoint_injective (by
    rw [tautologicalPoint_add, tautologicalPoint_ofIsogeny, tautologicalPoint_ofIsogeny, h,
      tautologicalPoint_zero])

/-- **Addition of morphisms is the sum of coordinate pullbacks** where the latter is defined. -/
theorem ofIsogeny_add_ofIsogeny (φ ψ : Isogeny W₁ W₂)
    (h : φ.pullback.tautologicalPoint + ψ.pullback.tautologicalPoint ≠ 0) :
    ofIsogeny φ + ofIsogeny ψ = ofIsogeny ⟨φ.pullback.add ψ.pullback h,
      CoordinatePullback.mapsInfinity_add _ _ φ.mapsInfinity ψ.mapsInfinity h⟩ :=
  tautologicalPoint_injective (by
    rw [tautologicalPoint_add, tautologicalPoint_ofIsogeny, tautologicalPoint_ofIsogeny,
      tautologicalPoint_ofIsogeny, CoordinatePullback.tautologicalPoint_add])

omit [W₂.IsElliptic] in
/-- The tautological point of a composite with an isogeny is the image of the outer morphism's
tautological point under the isogeny's function-field pullback. -/
@[simp]
theorem tautologicalPoint_comp_ofIsogeny [W₃.IsElliptic] (g : Hom W₂ W₃) (φ : Isogeny W₁ W₂) :
    (g.comp (ofIsogeny φ)).tautologicalPoint = Point.map φ.fieldPullback g.tautologicalPoint := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [zero_comp, tautologicalPoint_zero, tautologicalPoint_zero, map_zero]
  · simp only [ofIsogeny_comp_ofIsogeny, tautologicalPoint_ofIsogeny,
      Isogeny.tautologicalPoint_comp]

omit [W₂.IsElliptic] in
/-- **Composition is additive in the outer morphism.** -/
@[simp]
theorem add_comp [W₃.IsElliptic] (g g' : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g + g').comp f = g.comp f + g'.comp f := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [comp_zero, comp_zero, comp_zero, add_zero]
  · exact tautologicalPoint_injective (by
      simp only [tautologicalPoint_add, tautologicalPoint_comp_ofIsogeny, map_add])

omit [W₂.IsElliptic] in
/-- **Composition respects subtraction in the outer morphism.** -/
@[simp]
theorem sub_comp [W₃.IsElliptic] (g g' : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g - g').comp f = g.comp f - g'.comp f := by
  rw [sub_eq_add_neg, add_comp, neg_comp, sub_eq_add_neg]

omit [W₂.IsElliptic] in
/-- **Precomposition by `f`, as a homomorphism of the additive groups of morphisms.** -/
noncomputable def compRightHom [W₃.IsElliptic] (f : Hom W₁ W₂) : Hom W₂ W₃ →+ Hom W₁ W₃ where
  toFun g := g.comp f
  map_zero' := zero_comp f
  map_add' g g' := add_comp g g' f

omit [W₂.IsElliptic] in
@[simp]
theorem compRightHom_apply [W₃.IsElliptic] (f : Hom W₁ W₂) (g : Hom W₂ W₃) :
    compRightHom f g = g.comp f := (rfl)

omit [W₂.IsElliptic] in
/-- **Composition is `ℤ`-linear in the outer morphism.** -/
@[simp]
theorem zsmul_comp [W₃.IsElliptic] (n : ℤ) (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (n • g).comp f = n • g.comp f :=
  (compRightHom (W₃ := W₃) f).map_zsmul n g

omit [W₂.IsElliptic] in
/-- **Composition is `ℕ`-linear in the outer morphism**, the rule for a natural scalar. -/
@[simp]
theorem nsmul_comp [W₃.IsElliptic] (n : ℕ) (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (n • g).comp f = n • g.comp f :=
  (compRightHom (W₃ := W₃) f).map_nsmul n g

end Hom

end Isogeny

end TauCeti

end
