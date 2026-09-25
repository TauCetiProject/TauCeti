/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Submodule
public import TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# The line bundle of a Cartier divisor

Let `X` be an integral scheme with sheaf of rational functions `𝒦_X`, and let `D` be a Cartier
divisor on `X`, that is, a global section of `𝒦_X^× / 𝒪_X^×`. Near every point `x`, `D` is the
class of a nonzero rational function `f`, a *local equation* of `D` at `x`, well defined up to a
unit of the local ring `𝒪_{X,x}` (`Scheme.CartierDivisor.IsLocalEquationAt`). This file
constructs the sheaf `𝒪_X(D) ⊆ 𝒦_X`,

`Γ(U, 𝒪_X(D)) = {g ∈ K(X) | f g ∈ 𝒪_{X,x} for every x ∈ U and every local equation f at x}`,

so that `𝒪_X(D) = f⁻¹ 𝒪_X` over any open subset on which `f` is an equation of `D`, and proves
that it is a line bundle.

## Main declarations

* `Scheme.CartierDivisor.sections D U`, the displayed submodule of `Γ(𝒦_X, U)`, described through
  a single local equation by `Scheme.CartierDivisor.mem_sections_iff_exists`, and, over an open
  subset on which `f` is an equation of `D`, as `f⁻¹ Γ(X, U)` by
  `Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq`;
* `Scheme.CartierDivisor.sheaf D`, the sheaf `𝒪_X(D)` of `𝒪_X`-modules, with its inclusion
  `Scheme.CartierDivisor.sheafι D : 𝒪_X(D) ⟶ 𝒦_X` (`sheafι_app_mem`, `range_sheafι_app`) and
  the factorization `Scheme.CartierDivisor.sheafLift` through it of a morphism to `𝒦_X` whose
  sections satisfy the defining condition;
* `Scheme.CartierDivisor.sheafOverIsoOfRestrictEq`: divisors that agree on an open subset `V` have
  isomorphic sheaves over `V`;
* `Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor`: the sheaf of the principal divisor
  of `f` is `f⁻¹ 𝒪_X`, trivialized by multiplication by `f`;
* `Scheme.CartierDivisor.isInvertible_sheaf` and `Scheme.CartierDivisor.toInvertibleSheaf`:
  `𝒪_X(D)` is a line bundle.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6, the construction of `𝓛(D)` preceding
  Proposition II.6.13.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierDivisor

/-- The sections of `𝒪_X(D)` over an open subset `U`: the rational functions `g` such that `f g`
lies in the local ring `𝒪_{X,x}` for every point `x ∈ U` and every local equation `f` of `D`
at `x`.

By `IsLocalEquationAt.mul_mem_range_iff` it suffices to test one local equation at each point
(`mem_sections_iff_exists`). -/
def sections (D : CartierDivisor X) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFunctions X, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ), D.IsLocalEquationAt x f →
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    (f : X.functionField) * rationalFunctionsEquiv U s ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range}
  zero_mem' := by
    intro x hx f _
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero, mul_zero]
    exact Subring.zero_mem _
  add_mem' := by
    intro s t hs ht x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add, mul_add]
    exact Subring.add_mem _ (hs x hx f hf) (ht x hx f hf)
  smul_mem' := by
    intro r s hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_smul, ← germ_smul_functionField hx, Algebra.smul_def, mul_left_comm]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) (hs x hx f hf)

/-- Membership in `CartierDivisor.sections`, unfolded. -/
lemma mem_sections {D : CartierDivisor X} {U : X.Opens} {s : Γ(rationalFunctions X, U)} :
    s ∈ D.sections U ↔ ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ),
      D.IsLocalEquationAt x f →
        haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) * rationalFunctionsEquiv U s ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  Iff.rfl

/-- A rational function is a section of `𝒪_X(D)` over `U` as soon as, at every point of `U`, its
product with *some* local equation of `D` lies in the local ring. -/
theorem mem_sections_iff_exists {D : CartierDivisor X} {U : X.Opens}
    {s : Γ(rationalFunctions X, U)} :
    s ∈ D.sections U ↔ ∀ (x : X) (hx : x ∈ U), ∃ f : X.functionFieldˣ,
      D.IsLocalEquationAt x f ∧
        haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) * rationalFunctionsEquiv U s ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · intro hs x hx
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    exact ⟨f, hf, hs x hx f hf⟩
  · intro hs x hx g hg
    obtain ⟨f, hf, hmem⟩ := hs x hx
    exact (hf.mul_mem_range_iff hg _).mp hmem

/-- Restricting to a smaller open subset preserves the sections of `𝒪_X(D)`. -/
lemma sections_map {D : CartierDivisor X} {U V : X.Opens} (i : V ⟶ U)
    {s : Γ(rationalFunctions X, U)} (hs : s ∈ D.sections U) :
    (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := by
  intro x hx f hf
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : Nonempty U := ⟨⟨x, i.le hx⟩⟩
  rw [rationalFunctionsEquiv_map]
  exact hs x (i.le hx) f hf

/-- **The sections of `𝒪_X(D)` over an open subset carrying an equation.** Let `f` be an equation
of `D` over `V`. Over every nonempty open `W ≤ V`, a rational function `g` is a section of
`𝒪_X(D)` exactly when `f g` is regular on `W`; that is, `𝒪_X(D) = f⁻¹ 𝒪_X` over `V`. -/
theorem mem_sections_iff_of_rationalUnitClass_eq {D : CartierDivisor X} {V W : X.Opens}
    [Nonempty V] [Nonempty W] (hWV : W ≤ V) {f : X.functionFieldˣ}
    (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) {s : Γ(rationalFunctions X, W)} :
    s ∈ D.sections W ↔
      ∃ a : Γ(X, W), X.germToFunctionField W a = f * rationalFunctionsEquiv W s := by
  have hfW := rationalUnitClass_eq_of_le hWV hf
  constructor
  · intro hs
    exact exists_germToFunctionField_eq_of_forall_mem_range fun y hy ↦
      hs y hy f (isLocalEquationAt_of_rationalUnitClass_eq hfW hy)
  · rintro ⟨a, ha⟩
    refine mem_sections_iff_exists.mpr fun x hx ↦
      ⟨f, isLocalEquationAt_of_rationalUnitClass_eq hfW hx, ?_⟩
    rw [← ha, ← _root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx]
    exact RingHom.mem_range_self _ _

/-- Divisors that agree on an open subset `V` have the same sections over every open `W ≤ V`. -/
lemma sections_congr {D E : CartierDivisor X} {V W : X.Opens} (h : D |_ V = E |_ V)
    (hWV : W ≤ V) : D.sections W = E.sections W := by
  ext s
  simp only [mem_sections]
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ forall_congr' fun f ↦
    imp_congr_left (isLocalEquationAt_congr h (hWV hx) f)

/-- The `𝒪_X`-submodule `𝒪_X(D)` of the sheaf `𝒦_X` of rational functions. The membership
condition is imposed point by point, so this is a submodule of the *sheaf* `𝒦_X`. -/
def submodule (D : CartierDivisor X) : (rationalFunctions X).Submodule where
  obj U := D.sections U.unop
  map i := fun {_} hs ↦ sections_map i.unop hs
  isSheaf {U} s hs := by
    intro x hx f hf
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    -- `hi` says that the restriction of `s` to `V` lies in the component of the submodule under
    -- construction at `op V`, which is `D.sections V` by definition.
    have hi' : (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := hi
    rw [← rationalFunctionsEquiv_map i s]
    exact hi' x hxV f hf

/-- The component of the submodule `𝒪_X(D) ⊆ 𝒦_X` at an object of the opposite category. -/
@[simp]
lemma submodule_obj (D : CartierDivisor X) (U : (Opens X)ᵒᵖ) :
    D.submodule.toSubmodule.obj U = D.sections U.unop := by
  induction U using Opposite.rec
  rfl

/-- The sheaf `𝒪_X(D)` of `𝒪_X`-modules attached to a Cartier divisor `D`. -/
def sheaf (D : CartierDivisor X) : X.Modules :=
  D.submodule.toSheafOfModules

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X`. -/
def sheafι (D : CartierDivisor X) : D.sheaf ⟶ rationalFunctions X :=
  D.submodule.ι

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X` is injective on sections over every open subset. -/
lemma sheafι_app_injective (D : CartierDivisor X) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app D.sheafι U) :=
  Subtype.val_injective

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X` sends a section of `𝒪_X(D)` over `U` into `sections D U`. -/
lemma sheafι_app_mem (D : CartierDivisor X) (U : X.Opens) (t : Γ(D.sheaf, U)) :
    Scheme.Modules.Hom.app D.sheafι U t ∈ D.sections U :=
  TauCeti.SheafOfModules.ι_val_app_mem D.submodule (op U) t

/-- **The sections of `𝒪_X(D)` over `U` are exactly `sections D U`.** Together with
`sheafι_app_injective` this identifies the sections of `𝒪_X(D)` with the submodule of
`Γ(𝒦_X, U)` which defines it. -/
@[simp]
lemma range_sheafι_app (D : CartierDivisor X) (U : X.Opens) :
    Set.range (Scheme.Modules.Hom.app D.sheafι U) = D.sections U := by
  ext t
  exact ⟨fun ⟨s, hs⟩ ↦ hs ▸ sheafι_app_mem D U s, fun ht ↦ ⟨⟨t, ht⟩, rfl⟩⟩

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X` is a monomorphism. -/
instance (D : CartierDivisor X) : Mono D.sheafι :=
  -- Instance search does not see through `X.Modules` to `SheafOfModules X.ringCatSheaf`, so
  -- Mathlib's instance for the inclusion of a submodule is supplied explicitly.
  SheafOfModules.Submodule.instMonoι D.submodule

/-- A morphism `M ⟶ 𝒦_X` all of whose sections lie in `𝒪_X(D)` factors through `𝒪_X(D)`. -/
def sheafLift {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U) :
    M ⟶ D.sheaf :=
  TauCeti.SheafOfModules.liftToSubmodule D.submodule φ fun U s ↦ hφ U.unop s

/-- `sheafLift` factors `φ` through `𝒪_X(D)`: composing it with the inclusion
`sheafι D : 𝒪_X(D) ⟶ 𝒦_X` recovers `φ`. -/
@[reassoc (attr := simp)]
lemma sheafLift_ι {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U) :
    D.sheafLift φ hφ ≫ D.sheafι = φ :=
  TauCeti.SheafOfModules.liftToSubmodule_ι _ _ _

/-- On sections, `sheafLift` followed by the inclusion into `𝒦_X` is the original morphism. -/
@[simp]
lemma sheafι_app_sheafLift {M : X.Modules} (D : CartierDivisor X)
    (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U)
    (U : X.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app D.sheafι U (Scheme.Modules.Hom.app (D.sheafLift φ hφ) U s) =
      Scheme.Modules.Hom.app φ U s := by
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) (sheafLift_ι D φ hφ)) s

/-- **Divisors agreeing on an open subset have isomorphic sheaves there.** If `D` and `E` have the
same restriction to `V`, then `𝒪_X(D)` and `𝒪_X(E)` have the same sections over every open
subset of `V`, so they are isomorphic over `V`, compatibly with their inclusions into `𝒦_X`
(`sheafOverIsoOfRestrictEq_hom_ι`, `sheafOverIsoOfRestrictEq_inv_ι`). -/
def sheafOverIsoOfRestrictEq (D E : CartierDivisor X) (V : X.Opens) (h : D |_ V = E |_ V) :
    D.sheaf.over V ≅ E.sheaf.over V :=
  D.submodule.overIsoOfEq E.submodule V fun W i ↦
    (D.submodule_obj (op W)).trans ((sections_congr h i.le).trans (E.submodule_obj (op W)).symm)

/-- The isomorphism `sheafOverIsoOfRestrictEq` is compatible with the inclusions into `𝒦_X`. -/
@[reassoc (attr := simp)]
lemma sheafOverIsoOfRestrictEq_hom_ι (D E : CartierDivisor X) (V : X.Opens)
    (h : D |_ V = E |_ V) :
    (sheafOverIsoOfRestrictEq D E V h).hom ≫ E.sheafι.over V = D.sheafι.over V :=
  SheafOfModules.Submodule.overIsoOfEq_hom_ι _ _ _ _

/-- The inverse of `sheafOverIsoOfRestrictEq` is compatible with the inclusions into `𝒦_X`. -/
@[reassoc (attr := simp)]
lemma sheafOverIsoOfRestrictEq_inv_ι (D E : CartierDivisor X) (V : X.Opens)
    (h : D |_ V = E |_ V) :
    (sheafOverIsoOfRestrictEq D E V h).inv ≫ D.sheafι.over V = E.sheafι.over V :=
  SheafOfModules.Submodule.overIsoOfEq_inv_ι _ _ _ _

/-- For a regular function `a` on `U`, the rational function `f⁻¹ a` is a section of the sheaf of
the principal divisor of `f` over `U`. -/
lemma rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections (f : X.functionFieldˣ)
    (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField))
        U (Scheme.Modules.Hom.app (toRationalFunctions X) U a) ∈
      (principalCartierDivisor X f).sections U := by
  rcases isEmpty_or_nonempty U with hU | hU
  · -- Over the empty set the membership condition is vacuous.
    exact mem_sections.mpr fun x hx ↦ hU.elim ⟨x, hx⟩
  · refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl
      (principalCartierDivisor_restrict X f U).symm).mpr ⟨a, ?_⟩
    rw [rationalFunctionsEquiv_rationalFunctionsMul_app,
      rationalFunctionsEquiv_toRationalFunctions_app, ← mul_assoc, Units.mul_inv, one_mul]

variable (X) in
/-- Multiplication by `f⁻¹`, from `𝒪_X` to the sheaf of the principal divisor of `f`: a regular
function `a` goes to the section `f⁻¹ a` of `𝒪_X(div f)`. -/
def unitToSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf)
      (principalCartierDivisor X f).sheaf :=
  (principalCartierDivisor X f).sheafLift
    (toRationalFunctions X ≫ rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField))
    fun U a ↦ rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections f U a

/-- `unitToSheafPrincipalCartierDivisor X f`, read inside `𝒦_X`, is multiplication by `f⁻¹`. -/
@[reassoc]
lemma unitToSheafPrincipalCartierDivisor_ι (f : X.functionFieldˣ) :
    unitToSheafPrincipalCartierDivisor X f ≫ (principalCartierDivisor X f).sheafι =
      toRationalFunctions X ≫
        rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField) :=
  sheafLift_ι _ _ _

/-- Multiplication by `f⁻¹` is an isomorphism from `𝒪_X` to the sheaf `𝒪_X(div f)` of the
principal divisor of `f`; it is packaged as `unitIsoSheafPrincipalCartierDivisor`. -/
instance isIso_unitToSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    IsIso (unitToSheafPrincipalCartierDivisor X f) := by
  have key : ∀ (U : X.Opens) (a : Γ(SheafOfModules.unit X.ringCatSheaf, U)),
      Scheme.Modules.Hom.app (principalCartierDivisor X f).sheafι U
          (Scheme.Modules.Hom.app (unitToSheafPrincipalCartierDivisor X f) U a) =
        Scheme.Modules.Hom.app (rationalFunctionsMul X
          ((f⁻¹ : X.functionFieldˣ) : X.functionField)) U
          (Scheme.Modules.Hom.app (toRationalFunctions X) U a) := fun U a ↦ by
    simpa only [Scheme.Modules.Hom.comp_app (M := SheafOfModules.unit X.ringCatSheaf),
      ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        (congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U) (unitToSheafPrincipalCartierDivisor_ι f)) a
  -- Injectivity comes from that of `𝒪_X ⟶ 𝒦_X`; surjectivity from the description of the
  -- sections of `𝒪_X(div f)` as the rational functions `g` with `f g` regular.
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  -- Multiplication by `f⁻¹` is injective on sections, with left inverse multiplication by `f`.
  have hmul : ∀ c : Γ(rationalFunctions X, U),
      Scheme.Modules.Hom.app (rationalFunctionsMul X ((f : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (rationalFunctionsMul X
          ((f⁻¹ : X.functionFieldˣ) : X.functionField)) U c) = c := fun c ↦ by
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom
        (congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U) (rationalFunctionsMul_inv_comp f)) c
  refine ⟨fun a b hab ↦ toRationalFunctions_app_injective U ?_, fun t ↦ ?_⟩
  · rw [← hmul (Scheme.Modules.Hom.app (toRationalFunctions X) U a),
      ← hmul (Scheme.Modules.Hom.app (toRationalFunctions X) U b), ← key U a, ← key U b, hab]
  · rcases isEmpty_or_nonempty U with hU | hU
    · have hbot : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
      have := subsingleton_rationalFunctions U hbot
      exact ⟨0, sheafι_app_injective _ U (Subsingleton.elim _ _)⟩
    · obtain ⟨a, ha⟩ := (mem_sections_iff_of_rationalUnitClass_eq le_rfl
        (principalCartierDivisor_restrict X f U).symm).mp (sheafι_app_mem _ U t)
      refine ⟨a, sheafι_app_injective _ U ((key U a).trans
        ((rationalFunctionsEquiv U).injective ?_))⟩
      rw [rationalFunctionsEquiv_rationalFunctionsMul_app,
        rationalFunctionsEquiv_toRationalFunctions_app, ha, ← mul_assoc, Units.inv_mul,
        one_mul]

/-- **The sheaf of a principal Cartier divisor is trivial.** Multiplication by `f⁻¹` identifies
`𝒪_X` with `𝒪_X(div f)`. -/
def unitIsoSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    @Iso X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (principalCartierDivisor X f).sheaf :=
  asIso (unitToSheafPrincipalCartierDivisor X f)

/-- The forward map of `unitIsoSheafPrincipalCartierDivisor` is multiplication by `f⁻¹`. -/
@[simp]
lemma unitIsoSheafPrincipalCartierDivisor_hom (f : X.functionFieldˣ) :
    (unitIsoSheafPrincipalCartierDivisor f).hom = unitToSheafPrincipalCartierDivisor X f :=
  (rfl)

/-- The inverse of `unitIsoSheafPrincipalCartierDivisor`, read inside `𝒦_X`, is multiplication by
`f`: it sends a section `g` of `𝒪_X(div f)` to the regular function `f g`. -/
@[reassoc]
lemma unitIsoSheafPrincipalCartierDivisor_inv_toRationalFunctions (f : X.functionFieldˣ) :
    (unitIsoSheafPrincipalCartierDivisor f).inv ≫ toRationalFunctions X =
      (principalCartierDivisor X f).sheafι ≫
        rationalFunctionsMul X ((f : X.functionFieldˣ) : X.functionField) :=
  -- The goal mentions `SheafOfModules.unit X.ringCatSheaf`, which `rw` cannot see to be
  -- type-correct (`TopCat.Sheaf` is not unfolded at instance transparency), so the
  -- associativity steps are chained as terms.
  (Iso.inv_comp_eq (unitIsoSheafPrincipalCartierDivisor f)).mpr <|
    (Category.comp_id _).symm.trans <|
      (congrArg (toRationalFunctions X ≫ ·) (rationalFunctionsMul_inv_comp f).symm).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ rationalFunctionsMul X ((f : X.functionFieldˣ) : X.functionField))
            (unitToSheafPrincipalCartierDivisor_ι f).symm).trans (Category.assoc _ _ _)

/-- A rank-one local trivialization atlas for `𝒪_X(D)`, indexed by the points of `X`: near `x`,
choose an equation `f` of `D` over a neighbourhood `V`; then `𝒪_X(D)` agrees with `𝒪_X(div f)`
over `V`, and the latter is trivialized by multiplication by `f`. -/
private def localTrivializations (D : CartierDivisor X) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} D.sheaf := by
  choose f hf using D.exists_isLocalEquationAt
  choose V hx hV using fun x ↦ isLocalEquationAt_iff.mp (hf x)
  exact
    { I := X
      X := V
      coversTop := (Opens.coversTop_iff (X : Type u) V).mpr
        (IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩))
      iso := fun x ↦
        haveI : Nonempty (V x) := ⟨⟨x, hx x⟩⟩
        TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over (V x)) ≪≫
          (SheafOfModules.overFunctor X.ringCatSheaf (V x)).mapIso
            (unitIsoSheafPrincipalCartierDivisor (f x)) ≪≫
          sheafOverIsoOfRestrictEq _ D (V x)
            ((principalCartierDivisor_restrict X (f x) (V x)).trans (hV x)) }

/-- **The sheaf of a Cartier divisor is a line bundle.** On an integral scheme, `𝒪_X(D)` is
locally free of rank one: over an open subset on which `f` is an equation of `D`, it is
`f⁻¹ 𝒪_X`. -/
theorem isInvertible_sheaf (D : CartierDivisor X) : SheafOfModules.isInvertible X D.sheaf :=
  D.localTrivializations.isInvertible

/-- The line bundle `𝒪_X(D)` attached to a Cartier divisor `D` on an integral scheme. -/
def toInvertibleSheaf (D : CartierDivisor X) : InvertibleSheaf X :=
  ⟨D.sheaf, D.isInvertible_sheaf⟩

/-- The underlying sheaf of the line bundle attached to `D` is `𝒪_X(D)`. -/
@[simp]
lemma toInvertibleSheaf_obj (D : CartierDivisor X) : D.toInvertibleSheaf.obj = D.sheaf :=
  (rfl)

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
