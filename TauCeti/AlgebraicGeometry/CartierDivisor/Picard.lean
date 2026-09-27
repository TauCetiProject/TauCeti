/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.RationalTrivialization
public import TauCeti.AlgebraicGeometry.Modules.RationalEmbedding

/-!
# Every line bundle on an integral scheme is the sheaf of a Cartier divisor

Let `X` be an integral scheme. This file proves that every line bundle `L` on `X` is isomorphic
to the sheaf `𝒪_X(D)` of a Cartier divisor `D`, so that `D ↦ 𝒪_X(D)` maps the Cartier divisors
onto the isomorphism classes of line bundles. This is the surjectivity half of the dictionary
`CaCl(X) ≅ Pic(X)` between Cartier divisors modulo principal divisors and line bundles; unlike its
Weil-divisor counterpart on curves, it needs no regularity or dimension hypothesis.

The divisor is read off from the rational embedding of `L`. A rank-one trivialization of `L` on a
dense open subset realizes `L` inside the sheaf `𝒦_X` of rational functions
(`Scheme.Modules.rationalTrivializationHom`), and over the domain `V` of any local rank-one
trivialization the image consists of the regular multiples of one nonzero rational function
`f_V`. On overlaps these functions differ by regular units, so the classes of the `f_V⁻¹` glue to a
Cartier divisor `D`. Since `f_V⁻¹` is an equation of `D` over `V`, the sections of `𝒪_X(D)` over
an open subset of `V` are the rational functions `g` for which `g / f_V` is regular, which are
exactly the rational functions of the sections of `L` there.

## Main declarations

* `Scheme.Modules.exists_cartierDivisor_restrict_eq`: the local basis functions of a rationally
  trivialized line bundle glue to a Cartier divisor;
* `Scheme.CartierDivisor.isoSheafOfRestrictEq`: for such a divisor `D`, the isomorphism
  `L ≅ 𝒪_X(D)` through which the rational embedding of `L` factors
  (`Scheme.CartierDivisor.isoSheafOfRestrictEq_hom_sheafι`);
* `Scheme.CartierDivisor.exists_nonempty_iso_sheaf`: every line bundle is isomorphic to the sheaf
  of a Cartier divisor;
* `Scheme.CartierDivisor.toLineBundleClass`, the class of `𝒪_X(D)`, which is trivial for
  principal divisors (`Scheme.CartierDivisor.toLineBundleClass_principalCartierDivisor`) and
  surjective onto the line-bundle classes (`Scheme.CartierDivisor.toLineBundleClass_surjective`).

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.15.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules in
/-- On a nonempty open subset `W` of the domains of two rank-one trivializations of a sheaf of
modules, the rational functions of their basis sections have the same Cartier-divisor class: they
differ by a regular unit on `W`. -/
theorem
    _root_.AlgebraicGeometry.Scheme.Modules.rationalUnitClass_trivializationGeneratorRationalUnit_eq
    {X : Scheme.{u}}
    [IsIntegral X] (M : X.Modules) {U V₁ V₂ W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) [Nonempty V₁] [Nonempty V₂] [Nonempty W] :
    Scheme.rationalUnitClass X W
        (Additive.ofMul (trivializationGeneratorRationalUnit M e hU t₁)) =
      Scheme.rationalUnitClass X W
        (Additive.ofMul (trivializationGeneratorRationalUnit M e hU t₂)) := by
  obtain ⟨r, hr⟩ := exists_rationalFunction_trivializationGenerator_eq_mul M e hU t₁ t₂ i₁ i₂
  rw [rationalFunction_map, rationalFunction_map] at hr
  have h : trivializationGeneratorRationalUnit M e hU t₁ =
      Units.map (X.germToFunctionField W).hom r * trivializationGeneratorRationalUnit M e hU t₂ :=
    Units.ext (by simpa using hr)
  rw [h, ofMul_mul, map_add, Scheme.rationalUnitClass_germToFunctionField_eq_zero, zero_add]

open _root_.AlgebraicGeometry.Scheme.Modules in
/-- **The Cartier divisor of a rationally trivialized line bundle.** Let `M` be a line bundle on
an integral scheme, with a chosen rank-one trivialization on a dense open subset. There is a
Cartier divisor whose restriction to the domain `V` of every nonempty rank-one trivialization `t`
is the class of the inverse of the rational function of the basis section of `t`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_cartierDivisor_restrict_eq
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) :
    ∃ E : Scheme.CartierDivisor X, ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      E |_ V = Scheme.rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t)) := by
  let ι := {p : Σ V : X.Opens, (SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅
    M.over V) // Nonempty p.1}
  let W : ι → X.Opens := fun p ↦ p.1.1
  let sf : ∀ p : ι, ((Scheme.cartierDivisorSheaf X).obj.obj (op (W p)) : Type u) := fun p ↦
    have := p.2
    Scheme.rationalUnitClass X p.1.1
      (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU p.1.2))
  have hcompat : TopCat.Presheaf.IsCompatible (Scheme.cartierDivisorSheaf X).obj W sf := by
    intro p q
    have := p.2
    have := q.2
    have : Nonempty (W p ⊓ W q : X.Opens) := by
      simpa using nonempty_preirreducible_inter (W p).isOpen (W q).isOpen
        (by simpa using p.2) (by simpa using q.2)
    have hp := Scheme.rationalUnitClass_restrict X (U := W p) (V := W p ⊓ W q) inf_le_left
      (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU p.1.2))
    have hq := Scheme.rationalUnitClass_restrict X (U := W q) (V := W p ⊓ W q) inf_le_right
      (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU q.1.2))
    refine hp.trans (hq.trans ?_).symm
    rw [map_neg, map_neg, rationalUnitClass_trivializationGeneratorRationalUnit_eq M e hU
      p.1.2 q.1.2 (homOfLE inf_le_left) (homOfLE inf_le_right)]
  have hcover : ⊤ ≤ iSup W := fun x _ ↦ by
    obtain ⟨V, t, hx⟩ := M.exists_mem_trivialization x
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, t⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩
  obtain ⟨E, hE, -⟩ := (Scheme.cartierDivisorSheaf X).existsUnique_gluing' W ⊤
    (fun _ ↦ homOfLE le_top) hcover sf hcompat
  exact ⟨E, fun V _ t ↦ hE ⟨⟨V, t⟩, inferInstance⟩⟩

namespace Scheme.CartierDivisor

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} [SheafOfModules.isInvertible X M]
  {U : X.Opens} {e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U}
  {hU : Dense (U : Set X)} {D : CartierDivisor X}

omit [SheafOfModules.isInvertible X M] in
/-- If `D` is the class of the inverse of the rational basis function over the domain of every
rank-one trivialization of `M`, then that inverse is an equation of `D` there. -/
private lemma rationalUnitClass_inv_eq
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t)))
    (V : X.Opens) [Nonempty V]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) :
    rationalUnitClass X V (Additive.ofMul (trivializationGeneratorRationalUnit M e hU t)⁻¹) =
      D |_ V := by
  rw [hD V t, ofMul_inv]

/-- If `D` is the class of the inverse of the rational basis function over the domain of every
rank-one trivialization of `M`, then the rational function of every section of `M` is a section of
`𝒪_X(D)`. -/
private lemma rationalTrivializationHom_app_mem_sections
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t)))
    (W : X.Opens) (s : Γ(M, W)) :
    Hom.app (rationalTrivializationHom M e hU) W s ∈ D.sections W := by
  refine mem_sections_iff_exists.mpr fun x hx ↦ ?_
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  obtain ⟨V, t, hxV⟩ := M.exists_mem_trivialization x
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨x, hx, hxV⟩⟩
  refine ⟨_, isLocalEquationAt_of_rationalUnitClass_eq (rationalUnitClass_inv_eq hD V t) hxV, ?_⟩
  obtain ⟨r, hr⟩ := exists_rationalFunction_eq_mul M e hU t (homOfLE inf_le_right)
    (M.presheaf.map (homOfLE inf_le_left : W ⊓ V ⟶ W).op s)
  rw [rationalFunctionsEquiv_rationalTrivializationHom_app,
    ← rationalFunction_map M e hU (homOfLE inf_le_left : W ⊓ V ⟶ W) s, hr, mul_left_comm,
    Units.inv_mul, mul_one,
    ← _root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X
      (show x ∈ W ⊓ V from ⟨hx, hxV⟩)]
  exact RingHom.mem_range_self _ _

/-- If `D` is the class of the inverse of the rational basis function over the domain of every
rank-one trivialization of `M`, then every section of `𝒪_X(D)` is, near each point, the rational
function of a section of `M`. -/
private lemma exists_rationalTrivializationHom_app_eq_map
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t)))
    {W : X.Opens} {q : Γ(rationalFunctions X, W)} (hq : q ∈ D.sections W) {x : X} (hx : x ∈ W) :
    ∃ (V : X.Opens) (_ : x ∈ V) (i : V ⟶ W) (s : Γ(M, V)),
      Hom.app (rationalTrivializationHom M e hU) V s =
        (rationalFunctions X).presheaf.map i.op q := by
  obtain ⟨V, t, hxV⟩ := M.exists_mem_trivialization x
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨x, hx, hxV⟩⟩
  let i : W ⊓ V ⟶ W := homOfLE inf_le_left
  let j : W ⊓ V ⟶ V := homOfLE inf_le_right
  obtain ⟨a, ha⟩ := (mem_sections_iff_of_rationalUnitClass_eq inf_le_right
    (rationalUnitClass_inv_eq hD V t)).mp (sections_map i hq)
  refine ⟨W ⊓ V, ⟨hx, hxV⟩, i, a • M.presheaf.map j.op (trivializationGenerator M t),
    (rationalFunctionsEquiv (W ⊓ V)).injective ?_⟩
  rw [rationalFunctionsEquiv_rationalTrivializationHom_app, rationalFunction_smul,
    rationalFunction_map, ← coe_trivializationGeneratorRationalUnit, ha, mul_right_comm,
    Units.inv_mul, one_mul]

/-- If `D` is the class of the inverse of the rational basis function over the domain of every
rank-one trivialization of `M`, then the factorization of the rational embedding of `M` through
`𝒪_X(D)` is an isomorphism. -/
private lemma isIso_sheafLift_rationalTrivializationHom
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t))) :
    IsIso (D.sheafLift _ (rationalTrivializationHom_app_mem_sections hD)) := by
  set φ := rationalTrivializationHom M e hU
  set L := D.sheafLift φ (rationalTrivializationHom_app_mem_sections hD)
  have hinj : ∀ V : X.Opens, Function.Injective (Hom.app L V) := fun V a b h ↦
    rationalTrivializationHom_app_injective M e hU V <| by
      rw [← sheafι_app_sheafLift D φ (rationalTrivializationHom_app_mem_sections hD) V a, h,
        sheafι_app_sheafLift]
  -- Local preimages of a section of `𝒪_X(D)` glue, since `L` is injective on stalks.
  have hsurj (V : X.Opens) : Function.Surjective (Hom.app L V) :=
    TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective
      (F := ⟨M.presheaf, M.isSheaf⟩) (G := ⟨D.sheaf.presheaf, D.sheaf.isSheaf⟩)
      (ObjectProperty.homMk L.mapPresheaf) V
      (fun x _ ↦ TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
        (fun W ↦ hinj W) x) fun t x hx ↦ by
        obtain ⟨W, hxW, i, s, hs⟩ :=
          exists_rationalTrivializationHom_app_eq_map hD (sheafι_app_mem D V t) hx
        refine ⟨W, hxW, i, s, ?_⟩
        -- Unfold the `TopCat.Sheaf` wrappers around the sheaves and the morphism `L`.
        change Hom.app L W s = D.sheaf.presheaf.map i.op t
        apply sheafι_app_injective D W
        rw [sheafι_app_sheafLift, hs]
        exact (D.sheafι.mapPresheaf.naturality_apply i.op t).symm
  refine isIso_sheafLift D φ (rationalTrivializationHom_app_mem_sections hD)
    (rationalTrivializationHom_app_injective M e hU) fun V q hq ↦ ?_
  obtain ⟨s, hs⟩ := hsurj V (sectionMk q hq)
  exact ⟨s, by rw [← sheafι_app_sheafLift D φ (rationalTrivializationHom_app_mem_sections hD) V s,
    hs, sheafι_app_sectionMk]⟩

/-- If `D` is the class of the inverse of the rational basis function over the domain of every
rank-one trivialization of `M`, then the rational embedding of `M` factors through an isomorphism
`M ≅ 𝒪_X(D)`. -/
def isoSheafOfRestrictEq
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t))) :
    M ≅ D.sheaf :=
  have := isIso_sheafLift_rationalTrivializationHom hD
  asIso (D.sheafLift _ (rationalTrivializationHom_app_mem_sections hD))

/-- The isomorphism `isoSheafOfRestrictEq`, followed by the inclusion `𝒪_X(D) ⟶ 𝒦_X`, is the
rational embedding of the line bundle. -/
@[reassoc (attr := simp)]
lemma isoSheafOfRestrictEq_hom_sheafι
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t))) :
    (isoSheafOfRestrictEq hD).hom ≫ D.sheafι = rationalTrivializationHom M e hU :=
  sheafLift_ι _ _ _

omit [SheafOfModules.isInvertible X M] in
/-- **Every line bundle on an integral scheme is the sheaf of a Cartier divisor.** -/
theorem exists_nonempty_iso_sheaf (L : InvertibleSheaf X) :
    ∃ D : CartierDivisor X, Nonempty (L.obj ≅ D.sheaf) := by
  obtain ⟨U, -, hU, ⟨e⟩⟩ := TauCeti.SheafOfModules.exists_dense_open_trivialization L.obj
  obtain ⟨D, hD⟩ := L.obj.exists_cartierDivisor_restrict_eq e hU
  exact ⟨D, ⟨isoSheafOfRestrictEq hD⟩⟩

variable (D) in
/-- The isomorphism class of the line bundle `𝒪_X(D)` of a Cartier divisor. -/
def toLineBundleClass : LineBundleClass X :=
  LineBundleClass.mk D.toInvertibleSheaf

/-- The line-bundle class of `D` is the class of `L` exactly when `𝒪_X(D) ≅ L`. -/
lemma toLineBundleClass_eq_mk_iff {L : InvertibleSheaf X} :
    D.toLineBundleClass = LineBundleClass.mk L ↔ Nonempty (D.sheaf ≅ L.obj) := by
  rw [toLineBundleClass, LineBundleClass.mk_eq_mk_iff, toInvertibleSheaf_obj]

/-- **The sheaf of a principal Cartier divisor is trivial as a line bundle.** -/
@[simp]
lemma toLineBundleClass_principalCartierDivisor (f : X.functionFieldˣ) :
    (principalCartierDivisor X f).toLineBundleClass = 1 := by
  rw [← LineBundleClass.mk_trivial, toLineBundleClass_eq_mk_iff, InvertibleSheaf.trivial_obj]
  exact ⟨(unitIsoSheafPrincipalCartierDivisor X f).symm ≪≫
    (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).symm⟩

/-- The zero Cartier divisor has the trivial line-bundle class. -/
@[simp]
lemma toLineBundleClass_zero : (0 : CartierDivisor X).toLineBundleClass = 1 := by
  rw [← principalCartierDivisor_one X, toLineBundleClass_principalCartierDivisor]

/-- **Every line-bundle class on an integral scheme is the class of a Cartier divisor.** -/
theorem toLineBundleClass_surjective :
    Function.Surjective (toLineBundleClass : CartierDivisor X → LineBundleClass X) := by
  intro a
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  obtain ⟨D, ⟨φ⟩⟩ := exists_nonempty_iso_sheaf L
  exact ⟨D, toLineBundleClass_eq_mk_iff.mpr ⟨φ.symm⟩⟩

end Scheme.CartierDivisor

end

end AlgebraicGeometry

end TauCeti
