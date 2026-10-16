/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
public import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
public import TauCeti.AlgebraicGeometry.PicardFunctor.Relative
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The degree-zero subfunctor of the relative Picard presheaf

Let `f : X ⟶ S` be a morphism of schemes and `T` a scheme over `S`, with base change
`X_T = T ×_S X`. A point `ξ : Spec Ω ⟶ T` with values in a field `Ω` has the fibre
`X_ξ = Spec Ω ×_S X`, a scheme over `Ω` mapping to `X_T`. The **fibre degree** of a line-bundle
class `a` on `X_T` at `ξ` is the Euler-characteristic degree `χ(a|_{X_ξ}) - χ(𝒪_{X_ξ})` over `Ω`
of its restriction to `X_ξ` (`LineBundleClass.eulerDegree`). Since every line bundle on `Spec Ω`
is trivial, the fibre degree does not see classes pulled back from `T`, so it is defined on the
relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)` (`relativePicardFiberDegree`). It is natural:
the fibre degree of the pullback of a class along `T' ⟶ T` at `ξ'` is the fibre degree of the
class at the composite point `Spec Ω ⟶ T' ⟶ T` (`relativePicardFiberDegree_map`).

The classes whose fibre degree vanishes at every geometric point, that is at every point with
values in an algebraically closed field, therefore form a subfunctor
`relativePicardDegreeZeroSubfunctor` of the relative Picard presheaf. When `f` is a smooth proper
curve with geometrically connected fibres, this is the functor `Pic⁰_{X/S}` of line bundles of
degree zero on every geometric fibre, before representability.

On a fibre which is a proper integral curve over `Ω` with discrete valuation rings as
codimension-one local rings, the fibre degree is additive (`relativePicardFiberDegree_mul`), by
Riemann–Roch on that curve, and a class has fibre degree zero there exactly when its restriction
lies in `Pic⁰` of the fibre, `LineBundleClass.picZero` (`relativePicardFiberDegree_mk_eq_zero_iff`).
Every field-valued fibre of a smooth proper geometrically connected family of curves is such a
curve, so for such `f` the fibre degree is additive at every point
(`relativePicardFiberDegree_mul_of_smooth`) and the degree-zero subfunctor is closed under
products and inverses (`mul_mem_relativePicardDegreeZeroSubfunctor_obj`,
`inv_mem_relativePicardDegreeZeroSubfunctor_obj`). It is then a presheaf of commutative groups
`relativePicardDegreeZeroFunctor`, with inclusion `relativePicardDegreeZeroFunctorι` into the
relative Picard presheaf. For a scheme over a field which is not a
proper curve, `LineBundleClass.eulerDegree` takes the same junk values as the truncated Euler
characteristic `Scheme.Modules.eulerCharBelow`; the definitions here make sense in general, but
they are only the degree and `Pic⁰` for families of curves. Local constancy of the degree in flat
families and representability are not treated here.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree`: the degree on the fibre over a point
  `Spec Ω ⟶ T` of a section of `T ↦ Pic(X_T) / Pic(T)`;
* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_mk`: its value on the class of a line
  bundle on `X_T`;
* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_map`: its naturality in `T`;
* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_mul`: its additivity on a fibre which is
  a curve;
* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_mk_eq_zero_iff`: on a fibre which is a
  curve, degree zero is membership in `Pic⁰` of the fibre;
* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_mul_of_smooth`: its additivity at every
  point, for a smooth proper geometrically connected family of curves;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroSubfunctor`: the subfunctor of classes of
  degree zero on every geometric fibre;
* `TauCeti.AlgebraicGeometry.mul_mem_relativePicardDegreeZeroSubfunctor_obj`,
  `TauCeti.AlgebraicGeometry.inv_mem_relativePicardDegreeZeroSubfunctor_obj`: for a smooth proper
  geometrically connected family of curves, it is closed under products and inverses.
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctor`: for such a family, `Pic⁰_{X/S}`
  as a presheaf of commutative groups, with inclusion
  `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctorι` into the relative Picard presheaf
  and sections built by `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroFunctor.mk`.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.4.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.5.
-/

public section

open CategoryTheory Limits

namespace TauCeti
namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The Euler-characteristic degree over `Ω` of a line-bundle class on `Spec Ω ×_S X`, for a
morphism `g : Spec Ω ⟶ S`. -/
private def baseChangeEulerDegree {Ω : Type u} [Field Ω] (g : Spec (.of Ω) ⟶ S)
    (a : LineBundleClass (pullback g f)) : ℤ :=
  letI : (pullback g f).Over (Spec (.of Ω)) := ⟨pullback.fst g f⟩
  LineBundleClass.eulerDegree Ω a

/-- The degree on `Spec Ω ×_S X` only depends on the morphism `Spec Ω ⟶ S`, through the
identification of the fibre products along equal morphisms. -/
private lemma baseChangeEulerDegree_congr {Ω : Type u} [Field Ω] {g₁ g₂ : Spec (.of Ω) ⟶ S}
    (h : g₁ = g₂) (a : LineBundleClass (pullback g₁ f)) :
    baseChangeEulerDegree f g₂ (LineBundleClass.pullback (pullback.congrHom h rfl).inv a) =
      baseChangeEulerDegree f g₁ a := by
  subst h
  rw [pullback.congrHom_inv, pullback.map_id, LineBundleClass.pullback_id]

/-- The morphism from the fibre `Spec Ω ×_S X` over a point `ξ : Spec Ω ⟶ T` to the base change
`X_T = T ×_S X`. -/
private abbrev fiberToBaseChange {T : Over S} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.left) : pullback (ξ ≫ T.hom) f ⟶ pullback T.hom f :=
  pullback.map _ _ _ _ ξ (𝟙 X) (𝟙 S) (by simp) (by simp)

/-- The degree of a line-bundle class on `X_T` restricted to the fibre over `ξ : Spec Ω ⟶ T`. -/
private def fiberDegree {T : Over S} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ T.left)
    (a : LineBundleClass (pullback T.hom f)) : ℤ :=
  baseChangeEulerDegree f (ξ ≫ T.hom) (LineBundleClass.pullback (fiberToBaseChange f ξ) a)

/-- The fibre degree does not see line-bundle classes pulled back from the base, because every
line bundle on the spectrum of a field is trivial. -/
private lemma fiberDegree_mul_pullback_fst {T : Over S} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.left) (a : LineBundleClass (pullback T.hom f))
    (b : LineBundleClass T.left) :
    fiberDegree f ξ (a * LineBundleClass.pullback (pullback.fst T.hom f) b) =
      fiberDegree f ξ a := by
  have hb : LineBundleClass.pullback ξ b = 1 := Subsingleton.elim _ _
  rw [fiberDegree, fiberDegree, LineBundleClass.pullback_mul, LineBundleClass.pullback_comp,
    pullback.lift_fst, ← LineBundleClass.pullback_comp, hb, LineBundleClass.pullback_one,
    mul_one]

/-- **The degree on the fibre over a point `ξ : Spec Ω ⟶ T`** of a section of the relative
Picard presheaf `T ↦ Pic(X_T) / Pic(T)`: the Euler-characteristic degree over `Ω` of the
restriction of a representing line-bundle class to the fibre `Spec Ω ×_S X` of `X_T` over `ξ`
(`relativePicardFiberDegree_mk`). It is well defined because line-bundle classes pulled back from
`T` are trivial on the fibre. -/
def relativePicardFiberDegree {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) : (relativePicardPresheaf f).obj T → ℤ :=
  fun c ↦ Quotient.liftOn' (c : LineBundleClass (pullback T.unop.hom f) ⧸
      (LineBundleClass.pullbackHom (pullback.fst T.unop.hom f)).range) (fiberDegree f ξ)
    fun a b hab ↦ by
      obtain ⟨c, hc⟩ := QuotientGroup.leftRel_apply.mp hab
      have hb : b = a * LineBundleClass.pullback (pullback.fst T.unop.hom f) c := by
        rw [← LineBundleClass.pullbackHom_apply, hc, mul_inv_cancel_left]
      rw [hb, fiberDegree_mul_pullback_fst]

/-- The fibre degree of the image in `Pic(X_T) / Pic(T)` of a line-bundle class on `X_T` is the
fibre degree of that class. -/
private lemma relativePicardFiberDegree_mk_eq_fiberDegree {T : (Over S)ᵒᵖ} {Ω : Type u}
    [Field Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left) (a : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardFiberDegree f ξ (QuotientGroup.mk a) = fiberDegree f ξ a :=
  (rfl)

/-- The fibre degree of the class of a line bundle on `X_T` at `ξ : Spec Ω ⟶ T` is the
Euler-characteristic degree over `Ω` of its pullback to the fibre `Spec Ω ×_S X`. -/
@[simp]
lemma relativePicardFiberDegree_mk {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) (a : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardFiberDegree f ξ (QuotientGroup.mk a) =
      letI : (pullback (ξ ≫ T.unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
      LineBundleClass.eulerDegree Ω (LineBundleClass.pullback
        (pullback.map (ξ ≫ T.unop.hom) f T.unop.hom f ξ (𝟙 X) (𝟙 S) (by simp) (by simp)) a) := by
  rw [relativePicardFiberDegree_mk_eq_fiberDegree, fiberDegree, baseChangeEulerDegree,
    fiberToBaseChange]

/-- The identity of `Pic(X_T) / Pic(T)` has degree zero on every fibre. -/
@[simp]
lemma relativePicardFiberDegree_one {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) :
    relativePicardFiberDegree f ξ (1 : (relativePicardPresheaf f).obj T) = 0 := by
  -- The identity of `(relativePicardPresheaf f).obj T` is the image of the trivial class.
  calc relativePicardFiberDegree f ξ (1 : (relativePicardPresheaf f).obj T) =
        relativePicardFiberDegree f ξ (QuotientGroup.mk 1) := rfl
    _ = 0 := by
      rw [relativePicardFiberDegree_mk, LineBundleClass.pullback_one,
        LineBundleClass.eulerDegree_one]

/-- Additivity of the fibre degree at `ξ : Spec Ω ⟶ T` on `Pic(X_T) / Pic(T)` reduces to
additivity of the degree on the fibre `Spec Ω ×_S X`. -/
private lemma relativePicardFiberDegree_mul_of_baseChangeEulerDegree_mul {T : (Over S)ᵒᵖ}
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left)
    (h : ∀ a b : LineBundleClass (pullback (ξ ≫ T.unop.hom) f),
      baseChangeEulerDegree f (ξ ≫ T.unop.hom) (a * b) =
        baseChangeEulerDegree f (ξ ≫ T.unop.hom) a + baseChangeEulerDegree f (ξ ≫ T.unop.hom) b)
    (c d : (relativePicardPresheaf f).obj T) :
    relativePicardFiberDegree f ξ (c * d) =
      relativePicardFiberDegree f ξ c + relativePicardFiberDegree f ξ d := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective d
  -- The product in `(relativePicardPresheaf f).obj T` is the product of the quotient group.
  calc relativePicardFiberDegree f ξ (QuotientGroup.mk a * QuotientGroup.mk b :
          (relativePicardPresheaf f).obj T) =
        relativePicardFiberDegree f ξ (QuotientGroup.mk (a * b)) := rfl
    _ = _ := by
      simp only [relativePicardFiberDegree_mk_eq_fiberDegree, fiberDegree,
        LineBundleClass.pullback_mul, h]

/-- **The fibre degree is additive on a fibre which is a curve.** If the fibre
`X_ξ = Spec Ω ×_S X` over `ξ : Spec Ω ⟶ T` is a proper integral curve over `Ω` whose
codimension-one local rings are discrete valuation rings and whose `H¹(X_ξ, 𝒪)` is
finite-dimensional, then the fibre degree at `ξ` is additive on `Pic(X_T) / Pic(T)`. -/
lemma relativePicardFiberDegree_mul {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) [IsIntegral (pullback (ξ ≫ T.unop.hom) f)]
    [∀ y : CodimensionOnePoint (pullback (ξ ≫ T.unop.hom) f),
      IsDiscreteValuationRing ((pullback (ξ ≫ T.unop.hom) f).presheaf.stalk (y : _))]
    [IsProper (pullback.fst (ξ ≫ T.unop.hom) f)]
    (hX : ∀ y : ↥(pullback (ξ ≫ T.unop.hom) f), Order.coheight y ≤ 1)
    (hH : letI : (pullback (ξ ≫ T.unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
      FiniteDimensional Ω
        (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (pullback (ξ ≫ T.unop.hom) f)).obj 1))
    (c d : (relativePicardPresheaf f).obj T) :
    relativePicardFiberDegree f ξ (c * d) =
      relativePicardFiberDegree f ξ c + relativePicardFiberDegree f ξ d := by
  let _ : (pullback (ξ ≫ T.unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
  have : IsProper (pullback (ξ ≫ T.unop.hom) f ↘ Spec (.of Ω)) :=
    inferInstanceAs (IsProper (pullback.fst (ξ ≫ T.unop.hom) f))
  have : IsLocallyNoetherian (pullback (ξ ≫ T.unop.hom) f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (ξ ≫ T.unop.hom) f)
  exact relativePicardFiberDegree_mul_of_baseChangeEulerDegree_mul f ξ
    (LineBundleClass.eulerDegree_mul Ω hX) c d

/-- **The fibre degree of a family of curves is additive.** For a smooth proper geometrically
connected morphism `f` of relative dimension one, the fibre degree at every point
`ξ : Spec Ω ⟶ T` is additive on `Pic(X_T) / Pic(T)`, since every field-valued fibre of `f` is a
connected smooth proper curve (`LineBundleClass.eulerDegree_mul_fieldValuedBaseChange`). -/
lemma relativePicardFiberDegree_mul_of_smooth [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) (c d : (relativePicardPresheaf f).obj T) :
    relativePicardFiberDegree f ξ (c * d) =
      relativePicardFiberDegree f ξ c + relativePicardFiberDegree f ξ d :=
  relativePicardFiberDegree_mul_of_baseChangeEulerDegree_mul f ξ
    (LineBundleClass.eulerDegree_mul_fieldValuedBaseChange f Ω _) c d

/-- For a smooth proper geometrically connected family of curves, the fibre degree of an inverse
is the negative of the fibre degree. -/
lemma relativePicardFiberDegree_inv_of_smooth [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) (c : (relativePicardPresheaf f).obj T) :
    relativePicardFiberDegree f ξ c⁻¹ = -relativePicardFiberDegree f ξ c := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← relativePicardFiberDegree_mul_of_smooth, mul_inv_cancel,
    relativePicardFiberDegree_one]

/-- **On a fibre which is a curve, degree zero is membership in `Pic⁰` of the fibre.** If the
fibre `X_ξ = Spec Ω ×_S X` over `ξ : Spec Ω ⟶ T` is a proper integral curve over `Ω` whose
codimension-one local rings are discrete valuation rings and whose `H¹(X_ξ, 𝒪)` is
finite-dimensional, then the class of a line bundle on `X_T` has fibre degree zero at `ξ` exactly
when its restriction to `X_ξ` lies in `Pic⁰ X_ξ` (`LineBundleClass.picZero`). -/
lemma relativePicardFiberDegree_mk_eq_zero_iff {T : (Over S)ᵒᵖ} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ T.unop.left) [IsIntegral (pullback (ξ ≫ T.unop.hom) f)]
    [∀ y : CodimensionOnePoint (pullback (ξ ≫ T.unop.hom) f),
      IsDiscreteValuationRing ((pullback (ξ ≫ T.unop.hom) f).presheaf.stalk (y : _))]
    [IsProper (pullback.fst (ξ ≫ T.unop.hom) f)]
    (hX : ∀ y : ↥(pullback (ξ ≫ T.unop.hom) f), Order.coheight y ≤ 1)
    (hH : letI : (pullback (ξ ≫ T.unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
      FiniteDimensional Ω
        (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (pullback (ξ ≫ T.unop.hom) f)).obj 1))
    (a : LineBundleClass (pullback T.unop.hom f)) :
    relativePicardFiberDegree f ξ (QuotientGroup.mk a) = 0 ↔
      letI : (pullback (ξ ≫ T.unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
      haveI : IsProper (pullback (ξ ≫ T.unop.hom) f ↘ Spec (.of Ω)) :=
        inferInstanceAs (IsProper (pullback.fst (ξ ≫ T.unop.hom) f))
      -- A proper scheme over a field is of finite type and quasi-compact, so it is Noetherian.
      haveI : IsNoetherian (pullback (ξ ≫ T.unop.hom) f) :=
        { toIsLocallyNoetherian :=
            LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (ξ ≫ T.unop.hom) f)
          toCompactSpace :=
            (quasiCompact_iff_compactSpace (pullback (ξ ≫ T.unop.hom) f ↘ Spec (.of Ω))).mp
              inferInstance }
      haveI : Fact (∀ y : ↥(pullback (ξ ≫ T.unop.hom) f), Order.coheight y ≤ 1) := ⟨hX⟩
      haveI := hH
      Additive.ofMul (LineBundleClass.pullback
        (pullback.map (ξ ≫ T.unop.hom) f T.unop.hom f ξ (𝟙 X) (𝟙 S) (by simp) (by simp)) a) ∈
        LineBundleClass.picZero Ω (pullback (ξ ≫ T.unop.hom) f) := by
  rw [LineBundleClass.mem_picZero_iff, toMul_ofMul, relativePicardFiberDegree_mk]

/-- **Naturality of the fibre degree.** For a morphism `T' ⟶ T` over `S` and a point
`ξ' : Spec Ω ⟶ T'`, the fibre degree at `ξ'` of the pullback of a section from `T` to `T'` is
its fibre degree at the composite point `Spec Ω ⟶ T' ⟶ T`. -/
lemma relativePicardFiberDegree_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') {Ω : Type u} [Field Ω]
    (ξ' : Spec (.of Ω) ⟶ T'.unop.left) (c : (relativePicardPresheaf f).obj T) :
    relativePicardFiberDegree f ξ' ((relativePicardPresheaf f).map φ c) =
      relativePicardFiberDegree f (ξ' ≫ φ.unop.left) c := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  have h : (ξ' ≫ φ.unop.left) ≫ T.unop.hom = ξ' ≫ T'.unop.hom := by
    rw [Category.assoc, Over.w]
  -- The fibre map of `ξ'` followed by `X_{T'} ⟶ X_T` is the fibre map of the composite point,
  -- up to the identification of the fibre products along the two equal maps to `S`.
  have hmap : fiberToBaseChange f ξ' ≫ ((Over.pullback f).map φ.unop).left =
      (pullback.congrHom h rfl).inv ≫ fiberToBaseChange f (ξ' ≫ φ.unop.left) := by
    apply pullback.hom_ext <;> simp
  rw [relativePicardPresheaf_map_mk, relativePicardFiberDegree_mk_eq_fiberDegree,
    relativePicardFiberDegree_mk_eq_fiberDegree, fiberDegree, fiberDegree,
    LineBundleClass.pullback_comp, hmap, ← LineBundleClass.pullback_comp,
    baseChangeEulerDegree_congr]

/-- **The degree-zero subfunctor `Pic⁰_{X/S}`** of the relative Picard presheaf
`T ↦ Pic(X_T) / Pic(T)` of `f : X ⟶ S`: at a scheme `T` over `S`, the classes whose
fibre degree vanishes at every geometric point `Spec Ω ⟶ T`, with `Ω` algebraically closed. It is
a subfunctor by naturality of the fibre degree (`relativePicardFiberDegree_map`).

The fibre degree is the degree of a line bundle on a fibre that is a proper curve, where it is
additive (`relativePicardFiberDegree_mul`). So this is `Pic⁰_{X/S}` for families of such curves. For
other `f`, the condition inherits the junk values of `LineBundleClass.eulerDegree`. -/
def relativePicardDegreeZeroSubfunctor :
    Subfunctor (relativePicardPresheaf f ⋙ forget CommGrpCat) where
  obj T := {c | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left),
    relativePicardFiberDegree f ξ c = 0}
  map {T T'} φ c hc Ω _ _ ξ' := by
    rw [← hc Ω (ξ' ≫ φ.unop.left)]
    exact relativePicardFiberDegree_map f φ ξ' c

/-- A section of `T ↦ Pic(X_T) / Pic(T)` lies in `Pic⁰_{X/S}` exactly when its fibre degree
vanishes at every geometric point of `T`. -/
@[simp]
lemma mem_relativePicardDegreeZeroSubfunctor_obj_iff {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} :
    c ∈ (relativePicardDegreeZeroSubfunctor f).obj T ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left),
        relativePicardFiberDegree f ξ c = 0 :=
  Iff.rfl

/-- The identity of `Pic(X_T) / Pic(T)` lies in `Pic⁰_{X/S}`. -/
lemma one_mem_relativePicardDegreeZeroSubfunctor_obj (T : (Over S)ᵒᵖ) :
    (1 : (relativePicardPresheaf f).obj T) ∈ (relativePicardDegreeZeroSubfunctor f).obj T :=
  fun _ _ _ ξ ↦ relativePicardFiberDegree_one f ξ

/-- For a smooth proper geometrically connected family of curves, `Pic⁰_{X/S}` is closed under
products in `Pic(X_T) / Pic(T)`. -/
lemma mul_mem_relativePicardDegreeZeroSubfunctor_obj [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] {T : (Over S)ᵒᵖ}
    {c d : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeZeroSubfunctor f).obj T)
    (hd : d ∈ (relativePicardDegreeZeroSubfunctor f).obj T) :
    c * d ∈ (relativePicardDegreeZeroSubfunctor f).obj T := fun Ω _ _ ξ ↦ by
  rw [relativePicardFiberDegree_mul_of_smooth, hc Ω ξ, hd Ω ξ, add_zero]

/-- For a smooth proper geometrically connected family of curves, `Pic⁰_{X/S}` is closed under
inverses in `Pic(X_T) / Pic(T)`. -/
lemma inv_mem_relativePicardDegreeZeroSubfunctor_obj [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeZeroSubfunctor f).obj T) :
    c⁻¹ ∈ (relativePicardDegreeZeroSubfunctor f).obj T := fun Ω _ _ ξ ↦ by
  rw [relativePicardFiberDegree_inv_of_smooth, hc Ω ξ, neg_zero]

section Smooth

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- For a smooth proper geometrically connected family of curves, `Pic⁰_{X/S}(T)` as a subgroup
of `Pic(X_T) / Pic(T)`: the classes of degree zero on every geometric fibre, that is the sections
of `relativePicardDegreeZeroSubfunctor` at `T`. -/
def relativePicardDegreeZeroSubgroup (T : (Over S)ᵒᵖ) :
    Subgroup ((relativePicardPresheaf f).obj T) where
  carrier := (relativePicardDegreeZeroSubfunctor f).obj T
  mul_mem' := mul_mem_relativePicardDegreeZeroSubfunctor_obj f
  one_mem' := one_mem_relativePicardDegreeZeroSubfunctor_obj f T
  inv_mem' := inv_mem_relativePicardDegreeZeroSubfunctor_obj f

/-- A section of `T ↦ Pic(X_T) / Pic(T)` lies in the subgroup `Pic⁰_{X/S}(T)` exactly when it is
a section of the degree-zero subfunctor. -/
@[simp]
lemma mem_relativePicardDegreeZeroSubgroup_iff {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} :
    c ∈ relativePicardDegreeZeroSubgroup f T ↔ c ∈ (relativePicardDegreeZeroSubfunctor f).obj T :=
  Iff.rfl

/-- **The degree-zero Picard functor `Pic⁰_{X/S}`** of a smooth proper geometrically connected
family of curves `f : X ⟶ S`, as a presheaf of commutative groups on schemes over `S`: it sends
`T` to the subgroup `relativePicardDegreeZeroSubgroup f T` of `Pic(X_T) / Pic(T)`, and a morphism
over `S` to the restriction of the pullback map of the relative Picard presheaf. -/
def relativePicardDegreeZeroFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (relativePicardDegreeZeroSubgroup f T)
  map φ := CommGrpCat.ofHom <|
    (((relativePicardPresheaf f).map φ).hom.comp (Subgroup.subtype _)).codRestrict _
      fun c ↦ (relativePicardDegreeZeroSubfunctor f).map φ c.2
  map_id T := CommGrpCat.ext fun c ↦ Subtype.ext <|
    ConcreteCategory.congr_hom ((relativePicardPresheaf f).map_id T) c.1
  map_comp φ ψ := CommGrpCat.ext fun c ↦ Subtype.ext <|
    ConcreteCategory.congr_hom ((relativePicardPresheaf f).map_comp φ ψ) c.1

/-- The value of the degree-zero Picard functor at `T` is the subgroup `Pic⁰_{X/S}(T)` of
`Pic(X_T) / Pic(T)`. -/
lemma relativePicardDegreeZeroFunctor_obj (T : (Over S)ᵒᵖ) :
    (relativePicardDegreeZeroFunctor f).obj T =
      CommGrpCat.of (relativePicardDegreeZeroSubgroup f T) := by
  unfold relativePicardDegreeZeroFunctor; rfl

/-- The section of `Pic⁰_{X/S}` at `T` given by a section of `T ↦ Pic(X_T) / Pic(T)` of degree
zero on every geometric fibre. -/
def relativePicardDegreeZeroFunctor.mk {T : (Over S)ᵒᵖ} (c : (relativePicardPresheaf f).obj T)
    (hc : c ∈ (relativePicardDegreeZeroSubfunctor f).obj T) :
    (relativePicardDegreeZeroFunctor f).obj T :=
  ⟨c, hc⟩

/-- The degree-zero Picard functor `Pic⁰_{X/S}` acts on the section
`relativePicardDegreeZeroFunctor.mk f c hc` by the pullback map of the relative Picard presheaf
`T ↦ Pic(X_T) / Pic(T)`. -/
@[simp]
lemma relativePicardDegreeZeroFunctor_map_mk {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (c : (relativePicardPresheaf f).obj T)
    (hc : c ∈ (relativePicardDegreeZeroSubfunctor f).obj T) :
    (relativePicardDegreeZeroFunctor f).map φ (relativePicardDegreeZeroFunctor.mk f c hc) =
      relativePicardDegreeZeroFunctor.mk f ((relativePicardPresheaf f).map φ c)
        ((relativePicardDegreeZeroSubfunctor f).map φ hc) := by
  unfold relativePicardDegreeZeroFunctor relativePicardDegreeZeroFunctor.mk; rfl

/-- The inclusion of the degree-zero Picard functor `Pic⁰_{X/S}` into the relative Picard
presheaf `T ↦ Pic(X_T) / Pic(T)`, as a morphism of presheaves of commutative groups. -/
def relativePicardDegreeZeroFunctorι :
    relativePicardDegreeZeroFunctor f ⟶ relativePicardPresheaf f where
  app T := CommGrpCat.ofHom (relativePicardDegreeZeroSubgroup f T).subtype

/-- The inclusion `relativePicardDegreeZeroFunctorι` sends the section
`relativePicardDegreeZeroFunctor.mk f c hc` of `Pic⁰_{X/S}` to `c`. -/
@[simp]
lemma relativePicardDegreeZeroFunctorι_app_mk {T : (Over S)ᵒᵖ}
    (c : (relativePicardPresheaf f).obj T)
    (hc : c ∈ (relativePicardDegreeZeroSubfunctor f).obj T) :
    (relativePicardDegreeZeroFunctorι f).app T (relativePicardDegreeZeroFunctor.mk f c hc) = c := by
  unfold relativePicardDegreeZeroFunctorι relativePicardDegreeZeroFunctor.mk; rfl

/-- The inclusion `relativePicardDegreeZeroFunctorι` sends a section of `Pic⁰_{X/S}` to a section
of `T ↦ Pic(X_T) / Pic(T)` of degree zero on every geometric fibre. -/
lemma relativePicardDegreeZeroFunctorι_app_mem {T : (Over S)ᵒᵖ}
    (c : (relativePicardDegreeZeroFunctor f).obj T) :
    (relativePicardDegreeZeroFunctorι f).app T c ∈
      (relativePicardDegreeZeroSubfunctor f).obj T := by
  unfold relativePicardDegreeZeroFunctorι relativePicardDegreeZeroFunctor at *
  exact c.2

/-- The inclusion `relativePicardDegreeZeroFunctorι` is injective on sections. -/
lemma relativePicardDegreeZeroFunctorι_app_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((relativePicardDegreeZeroFunctorι f).app T) := by
  unfold relativePicardDegreeZeroFunctorι relativePicardDegreeZeroFunctor
  exact Subtype.val_injective

end Smooth

end

end AlgebraicGeometry

end TauCeti
