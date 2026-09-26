/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.TensorProduct

/-!
# Every line bundle on a curve is the sheaf of a Weil divisor

Let `X` be a Noetherian integral scheme of dimension at most one whose codimension-one local rings
are discrete valuation rings. This file proves that every line bundle `L` on `X` is isomorphic to
the sheaf `𝒪_X(D)` of a Weil divisor `D`, so that `D ↦ 𝒪_X(D)` identifies the divisor class group
with the isomorphism classes of line bundles: `Cl(X) ≅ Pic(X)`.

The divisor is read off from the rational embedding of `L`. A rank-one trivialization of `L` on a
dense open subset realizes `L` inside the sheaf `𝒦_X` of rational functions
(`Scheme.Modules.rationalTrivializationHom`), and over the domain `V` of any local rank-one
trivialization the image consists of the regular multiples of one nonzero rational function
`f_V`. The classes of the `f_V⁻¹` glue to a Cartier divisor
(`Scheme.Modules.exists_cartierDivisor_restrict_eq`), whose Weil divisor `D` has coefficient
`-ord_y f_V` at each codimension-one point `y ∈ V`. A rational function `g` then lies in the image
of `L` over an open subset of `V` exactly when `g / f_V` has no poles there, which by the algebraic
Hartogs' principle is the order bound defining `𝒪_X(D)`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_coeff_eq_neg_ord`: the Weil divisor of a rationally
  trivialized line bundle;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.isoSheafOfCoeffEq`: the isomorphism `L ≅ 𝒪_X(D)`
  through which the rational embedding of `L` factors (`isoSheafOfCoeffEq_hom_sheafι`);
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.toLineBundleClass_surjective` and
  `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.classGroupToLineBundleClass_surjective`;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.classGroupAddEquivLineBundleClass`, the additive
  equivalence `Cl(X) ≃+ Pic(X)`;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.isUnit_lineBundleClass`: every line-bundle class
  on such a curve is invertible under tensor product.

The argument follows Hartshorne, *Algebraic Geometry*, Proposition II.6.13 and Corollary II.6.16,
and the Stacks Project, *Divisors*, Tag 0BE0. No formalization is vendored.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules in
/-- **The Weil divisor of a rationally trivialized line bundle.** On a Noetherian integral scheme,
a line bundle `M` with a chosen rank-one trivialization on a dense open subset has a Weil divisor
whose coefficient at every codimension-one point `y` is minus the order at `y` of the rational
function of the basis section of any rank-one trivialization defined near `y`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_coeff_eq_neg_ord
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (M : X.Modules) [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) :
    ∃ D : SchemeWeilDivisor X, ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
      (y : CodimensionOnePoint X), (y : X) ∈ V →
      WeilDivisor.coeff D y = -X.ord (trivializationGeneratorRationalUnit M e hU t : _) y := by
  obtain ⟨E, hE⟩ := M.exists_cartierDivisor_restrict_eq e hU
  refine ⟨E.toWeilDivisor, fun V _ t y hy ↦ ?_⟩
  rw [Scheme.CartierDivisor.coeff_toWeilDivisor,
    E.orderAt_eq_of_restrict_eq_rationalUnitClass y V hy _ (hE V t), map_neg,
    SchemeWeilDivisor.orderAt_apply, toMul_ofMul]

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]

section Curve

variable [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  {M : X.Modules} [SheafOfModules.isInvertible X M] {U : X.Opens}
  {e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U}
  {hU : Dense (U : Set X)} {D : SchemeWeilDivisor X}

open Scheme.Modules

/-- If the coefficients of `D` are minus the orders of the local basis sections of `M`, then the
rational function of every section of `M` satisfies the order bound imposed by `D`. -/
theorem rationalTrivializationHom_app_mem_sections
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
      (y : CodimensionOnePoint X), (y : X) ∈ V →
      WeilDivisor.coeff D y = -X.ord (trivializationGeneratorRationalUnit M e hU t : _) y)
    (W : X.Opens) (s : Γ(M, W)) :
    Hom.app (rationalTrivializationHom M e hU) W s ∈ sections D W := by
  refine mem_sections.mpr fun y hy ↦ ?_
  have : Nonempty W := ⟨⟨y, hy⟩⟩
  obtain ⟨V, t, hyV⟩ := M.exists_mem_trivialization (y : X)
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨y, hy, hyV⟩⟩
  rw [rationalFunctionsEquiv_rationalTrivializationHom_app,
    ← rationalFunction_map M e hU (homOfLE inf_le_left : W ⊓ V ⟶ W) s]
  obtain ⟨r, hr⟩ := exists_rationalFunction_eq_mul M e hU t (homOfLE inf_le_right)
    (M.presheaf.map (homOfLE inf_le_left : W ⊓ V ⟶ W).op s)
  rw [hr]
  by_cases h0 : X.germToFunctionField (W ⊓ V) r = 0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    rw [X.ord_mul h0 (Units.ne_zero _), hD V t y hyV, neg_neg]
    exact le_add_of_nonneg_left (Scheme.ord_germToFunctionField_nonneg r ⟨hy, hyV⟩)

variable (hX : ∀ y : X, coheight y ≤ 1)
include hX

/-- If the coefficients of `D` are minus the orders of the local basis sections of `M`, then
every section of `𝒪_X(D)` is the rational function of a section of `M`. Locally the quotient by
a basis section has no poles, hence is regular by the algebraic Hartogs' principle, and the local
preimages glue because `M` embeds into the rational functions. -/
theorem exists_rationalTrivializationHom_app_eq
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
      (y : CodimensionOnePoint X), (y : X) ∈ V →
      WeilDivisor.coeff D y = -X.ord (trivializationGeneratorRationalUnit M e hU t : _) y)
    (W : X.Opens) {q : Γ(Scheme.rationalFunctions X, W)} (hq : q ∈ sections D W) :
    ∃ s : Γ(M, W), Hom.app (rationalTrivializationHom M e hU) W s = q := by
  have hnat {N P : X.Modules} (χ : N ⟶ P) {V W : X.Opens} (i : W ⟶ V) (a : Γ(N, V)) :
      Hom.app χ W (N.presheaf.map i.op a) = P.presheaf.map i.op (Hom.app χ V a) :=
    χ.mapPresheaf.naturality_apply i.op a
  by_cases hW : Nonempty W
  swap
  · have hbot : W = ⊥ := (Opens.not_nonempty_iff_eq_bot W).mp
      fun ⟨x, hx⟩ ↦ hW ⟨⟨x, hx⟩⟩
    have := Scheme.subsingleton_rationalFunctions W hbot
    exact ⟨0, Subsingleton.elim _ _⟩
  choose V t hV using fun x : W ↦ M.exists_mem_trivialization (x : X)
  let W' : W → X.Opens := fun x ↦ W ⊓ V x
  have hW' : ∀ x, Nonempty (W' x) := fun x ↦ ⟨⟨x, x.2, hV x⟩⟩
  have hV' : ∀ x, Nonempty (V x) := fun x ↦ ⟨⟨x, hV x⟩⟩
  -- a local preimage of `q` over each `W' x`
  have hloc : ∀ x : W, ∃ s : Γ(M, W' x),
      Hom.app (rationalTrivializationHom M e hU) (W' x) s =
        (Scheme.rationalFunctions X).presheaf.map (homOfLE inf_le_left : W' x ⟶ W).op q := by
    intro x
    have := hW' x
    have := hV' x
    set c := (trivializationGeneratorRationalUnit M e hU (t x) : X.functionField)
    set qK := Scheme.rationalFunctionsEquiv W q with hqK
    have hord : ∀ y : CodimensionOnePoint X, (y : X) ∈ W' x → 0 ≤ X.ord (qK * c⁻¹) y := by
      intro y hy
      by_cases hq0 : qK = 0
      · simp [hq0]
      · have hb := (mem_sections_iff.mp hq).resolve_left hq0 y hy.1
        rw [← hqK, hD (V x) (t x) y hy.2, neg_neg] at hb
        rw [X.ord_mul hq0 (inv_ne_zero (Units.ne_zero _)), Scheme.ord_inv]
        omega
    obtain ⟨r, hr⟩ := Scheme.exists_germToFunctionField_eq_of_ord_nonneg
      (fun _ _ ↦ inferInstance) (fun y _ ↦ hX y) hord
    refine ⟨r • M.presheaf.map (homOfLE inf_le_right : W' x ⟶ V x).op
      (trivializationGenerator M (t x)), (Scheme.rationalFunctionsEquiv (W' x)).injective ?_⟩
    rw [rationalFunctionsEquiv_rationalTrivializationHom_app, rationalFunction_smul,
      rationalFunction_map, ← coe_trivializationGeneratorRationalUnit, hr,
      Scheme.rationalFunctionsEquiv_map, inv_mul_cancel_right₀ (Units.ne_zero _)]
  choose s hs using hloc
  have hinj := rationalTrivializationHom_app_injective M e hU
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf W' s := by
    intro x z
    apply hinj
    rw [hnat, hnat, hs, hs, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hcover : W ≤ iSup W' := fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, hV ⟨y, hy⟩⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ W' W
    (fun x ↦ homOfLE inf_le_left) hcover s hcompat
  refine ⟨g, TopCat.Sheaf.eq_of_locally_eq' ⟨_, (Scheme.rationalFunctions X).isSheaf⟩ W' W
    (fun x ↦ homOfLE inf_le_left) hcover _ _ fun x ↦ ?_⟩
  exact (hnat (rationalTrivializationHom M e hU)
    (homOfLE inf_le_left : W' x ⟶ W) g).symm.trans <| by rw [hg x, hs x]

/-- **A line bundle is the sheaf of its divisor.** If the coefficients of `D` are minus the
orders of the local basis sections of the line bundle `M`, then the rational embedding of `M`
factors through an isomorphism `M ≅ 𝒪_X(D)`. -/
def isoSheafOfCoeffEq
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
      (y : CodimensionOnePoint X), (y : X) ∈ V →
      WeilDivisor.coeff D y = -X.ord (trivializationGeneratorRationalUnit M e hU t : _) y) :
    M ≅ sheaf D :=
  have : IsIso (sheafLift D _ (rationalTrivializationHom_app_mem_sections hD)) :=
    isIso_sheafLift D _ (rationalTrivializationHom_app_mem_sections hD)
      (rationalTrivializationHom_app_injective M e hU)
      (exists_rationalTrivializationHom_app_eq hX hD)
  asIso (sheafLift D _ (rationalTrivializationHom_app_mem_sections hD))

/-- The isomorphism `isoSheafOfCoeffEq`, followed by the inclusion `𝒪_X(D) ⟶ 𝒦_X`, is the
rational embedding of the line bundle. -/
@[reassoc (attr := simp)]
lemma isoSheafOfCoeffEq_hom_sheafι
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
      (y : CodimensionOnePoint X), (y : X) ∈ V →
      WeilDivisor.coeff D y = -X.ord (trivializationGeneratorRationalUnit M e hU t : _) y) :
    (isoSheafOfCoeffEq hX hD).hom ≫ sheafι D = rationalTrivializationHom M e hU :=
  sheafLift_ι _ _ _

end Curve

section Picard

variable [IsNoetherian X]

variable [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (hX : ∀ y : X, coheight y ≤ 1)
include hX

/-- **Every line bundle on a curve is the sheaf of a Weil divisor.** On a Noetherian integral
scheme of dimension at most one whose codimension-one local rings are discrete valuation rings,
every invertible sheaf is isomorphic to `𝒪_X(D)` for some Weil divisor `D`. -/
theorem exists_nonempty_iso_sheaf (L : InvertibleSheaf X) :
    ∃ D : SchemeWeilDivisor X, Nonempty (L.obj ≅ sheaf D) := by
  obtain ⟨U, -, hU, ⟨e⟩⟩ := TauCeti.SheafOfModules.exists_dense_open_trivialization L.obj
  obtain ⟨D, hD⟩ := L.obj.exists_coeff_eq_neg_ord e hU
  exact ⟨D, ⟨isoSheafOfCoeffEq hX hD⟩⟩

/-- Every line-bundle class on such a curve is the class of `𝒪_X(D)` for a Weil divisor `D`. -/
theorem toLineBundleClass_surjective : Function.Surjective (toLineBundleClass (X := X) hX) := by
  intro a
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  obtain ⟨D, ⟨φ⟩⟩ := exists_nonempty_iso_sheaf hX L
  refine ⟨D, (toLineBundleClass_eq_mk_iff hX).mpr ⟨?_⟩⟩
  rw [toInvertibleSheaf_obj]
  exact φ.symm

/-- **The map from divisor classes to line-bundle classes is surjective.** -/
theorem classGroupToLineBundleClass_surjective :
    Function.Surjective (classGroupToLineBundleClass (X := X) hX) := by
  intro a
  obtain ⟨D, rfl⟩ := toLineBundleClass_surjective hX a
  exact ⟨_, classGroupToLineBundleClass_divisorClass hX D⟩

/-- **Line bundles on a curve are invertible under tensor product.** Every line-bundle class is
the class of some `𝒪_X(D)`, which `𝒪_X(-D)` inverts. -/
theorem isUnit_lineBundleClass (a : LineBundleClass X) : IsUnit a := by
  obtain ⟨D, rfl⟩ := toLineBundleClass_surjective hX a
  exact isUnit_toLineBundleClass hX D

omit hX

variable [hX : Fact (∀ y : X, coheight y ≤ 1)]

/-- Tensor product makes the line-bundle classes into the Picard group of a Noetherian integral
scheme `X` of dimension at most one (`Fact (∀ y : X, coheight y ≤ 1)`) whose codimension-one local
rings are discrete valuation rings. -/
noncomputable instance : CommGroup (LineBundleClass X) :=
  commGroupOfIsUnit (isUnit_lineBundleClass hX.out)

variable (X) in
/-- **`Cl(X) ≅ Pic(X)`.** On a Noetherian integral scheme of dimension at most one whose
codimension-one local rings are discrete valuation rings, `D ↦ 𝒪_X(D)` identifies the divisor
class group with the line-bundle classes under tensor product. -/
def classGroupAddEquivLineBundleClass :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup ≃+ Additive (LineBundleClass X) :=
  AddEquiv.ofBijective (classGroupToLineBundleClassHom hX.out) <| by
    have hfun : ⇑(classGroupToLineBundleClassHom hX.out) = Additive.ofMul ∘
        classGroupToLineBundleClass hX.out :=
      funext (classGroupToLineBundleClassHom_apply hX.out)
    rw [hfun]
    exact Additive.ofMul.bijective.comp
      ⟨classGroupToLineBundleClass_injective hX.out,
        classGroupToLineBundleClass_surjective hX.out⟩

/-- The equivalence `Cl(X) ≃+ Pic(X)` sends a divisor class to the class of its line bundle. -/
@[simp]
lemma classGroupAddEquivLineBundleClass_apply
    (c : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) :
    classGroupAddEquivLineBundleClass X c =
      Additive.ofMul (classGroupToLineBundleClass hX.out c) := by
  simpa only [classGroupAddEquivLineBundleClass, AddEquiv.ofBijective_apply] using
    classGroupToLineBundleClassHom_apply hX.out c

/-- Negating a divisor class gives the inverse line-bundle class in the Picard group. -/
@[simp]
lemma classGroupToLineBundleClass_neg
    (c : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) :
    classGroupToLineBundleClass hX.out (-c) =
      (classGroupToLineBundleClass hX.out c)⁻¹ := by
  simpa only [classGroupAddEquivLineBundleClass_apply, toMul_ofMul, toMul_neg] using
    congrArg Additive.toMul ((classGroupAddEquivLineBundleClass X).map_neg c)

end Picard

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
