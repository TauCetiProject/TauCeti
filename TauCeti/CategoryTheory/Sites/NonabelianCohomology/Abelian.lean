/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import TauCeti.Algebra.Category.Grp.ForgetCorepresentable
public import TauCeti.Algebra.Category.Grp.Limits
public import TauCeti.CategoryTheory.Sites.EpiMono
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Connecting
public import TauCeti.GroupTheory.FreeAbelianGroup.Degree

/-!
# Torsors under abelian sheaves and injective embeddings

An abelian sheaf `F` on a site `(C, J)` is in particular a sheaf of groups, so it has torsors and
a pointed set `NonabelianH1` of torsor classes. This file shows that these classes are computed
by an embedding of `F` into an injective abelian sheaf, as the derived functor cohomology
`Sheaf.H F 1` is.

The key construction: for an `F`-torsor `P` and a morphism `ι : F ⟶ I` to an injective abelian
sheaf, there is a morphism of sheaves of sets `u : P → I` with `u (a • p) = ι a + u p`. Over each
object `U`, the formal sums `∑ nᵢ [pᵢ]` of degree zero of sections of `P` map to `F(U)` by
`∑ nᵢ [pᵢ] ↦ ∑ nᵢ (pᵢ - p₀)`, which does not depend on the section `p₀`. The composite with `ι`
extends, by injectivity of `I`, from the sheafified formal sums of degree zero to the free abelian
sheaf on `P`, and `u p` is the image of `[p]`.

Two consequences follow.

* A torsor under an injective abelian sheaf is trivial.
* For a short exact sequence `0 → F → I → Q → 0` of abelian sheaves with `I` injective, every
  `F`-torsor is the torsor of lifts of a global section of `Q`, so the connecting map
  `Q(C) → H¹(F)` is surjective. Together with
  `CategoryTheory.Sheaf.NonabelianH1.connecting_eq_connecting_iff`, this identifies the torsor
  classes of `F` with the orbits of the global sections of `I` acting on those of `Q`.

## Main declarations

* `CategoryTheory.abelianSheafToGrpSheaf J`: an abelian sheaf as a sheaf of groups, with
  `CategoryTheory.abelianSheafToGrpSheafObjEquiv` identifying its sections.
* `CategoryTheory.Sheaf.constIntHomMulEquivSections F`: morphisms from the constant integer
  presheaf to `F` are its global sections.
* `CategoryTheory.Sheaf.Torsor.exists_hom_smul_eq_of_injective`: the morphism `u : P → I` above.
* `CategoryTheory.Sheaf.NonabelianH1.subsingleton_of_injective`: torsors under an injective
  abelian sheaf are trivial.
* `CategoryTheory.ShortComplex.ShortExact.isGroupExtension`: a short exact sequence of abelian
  sheaves is an extension of sheaves of groups.
* `CategoryTheory.Sheaf.NonabelianH1.connecting_surjective_of_injective`: the surjectivity of the
  connecting map for an injective middle term.

## References

* [The Stacks project, Lemma 21.4.3 (03AJ)](https://stacks.math.columbia.edu/tag/03AJ), whose
  proof uses the same map from the formal sums of degree zero of sections of a torsor.
-/

public noncomputable section

open CategoryTheory Opposite
open FreeAbelianGroup (degree)

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An abelian sheaf, viewed as a sheaf of groups: its sections are written multiplicatively. -/
def abelianSheafToGrpSheaf : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J GrpCat.{w} :=
  sheafCompose J (forget₂ AddCommGrpCat AddGrpCat) ⋙
    sheafCompose J groupAddGroupEquivalence.inverse

variable {J}

/-- The sections of the sheaf of groups underlying an abelian sheaf `F` are the sections of `F`,
written multiplicatively. -/
def abelianSheafToGrpSheafObjEquiv (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    Multiplicative (F.obj.obj U) ≃* ((abelianSheafToGrpSheaf J).obj F).obj.obj U :=
  MulEquiv.refl _

/-- The restriction maps of the sheaf of groups underlying an abelian sheaf are those of the
abelian sheaf. -/
@[simp]
lemma abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv (F : Sheaf J AddCommGrpCat.{w})
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : Multiplicative (F.obj.obj U)) :
    ((abelianSheafToGrpSheaf J).obj F).obj.map f (abelianSheafToGrpSheafObjEquiv F U a) =
      abelianSheafToGrpSheafObjEquiv F V (.ofAdd (F.obj.map f a.toAdd)) :=
  (rfl)

/-- A morphism of abelian sheaves acts on the sections of the underlying sheaves of groups as on
the sections of the abelian sheaves. -/
@[simp]
lemma abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (U : Cᵒᵖ) (a : Multiplicative (F.obj.obj U)) :
    ((abelianSheafToGrpSheaf J).map φ).hom.app U (abelianSheafToGrpSheafObjEquiv F U a) =
      abelianSheafToGrpSheafObjEquiv G U (.ofAdd (φ.hom.app U a.toAdd)) :=
  (rfl)

namespace Sheaf

/-- A global section of the sheaf of groups underlying an abelian sheaf `F` is compatible with the
restriction maps of `F`. -/
private lemma map_toAdd_symm_sections (F : Sheaf J AddCommGrpCat.{w})
    (s : (((abelianSheafToGrpSheaf J).obj F).obj ⋙ forget GrpCat).sections) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    F.obj.map f ((abelianSheafToGrpSheafObjEquiv F U).symm (s.1 U)).toAdd =
      ((abelianSheafToGrpSheafObjEquiv F V).symm (s.1 V)).toAdd := by
  have h := abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv F f
    ((abelianSheafToGrpSheafObjEquiv F U).symm (s.1 U))
  rw [MulEquiv.apply_symm_apply] at h
  rw [(s.2 f).symm.trans h, MulEquiv.symm_apply_apply, toAdd_ofAdd]

/-- Morphisms from the constant presheaf `ℤ` to an abelian sheaf `F` are the global sections of
`F`, through the image of `1`. -/
def constIntHomMulEquivSections (F : Sheaf J AddCommGrpCat.{w}) :
    Multiplicative ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F.obj) ≃*
      (((abelianSheafToGrpSheaf J).obj F).obj ⋙ forget GrpCat).sections where
  toEquiv := Multiplicative.toAdd.trans
    { toFun ψ := ⟨fun U ↦ abelianSheafToGrpSheafObjEquiv F U (.ofAdd (ψ.app U ⟨1⟩)), fun f ↦
        (abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv F f _).trans
          (congrArg (fun a ↦ abelianSheafToGrpSheafObjEquiv F _ (.ofAdd a))
            (NatTrans.naturality_apply ψ f _).symm)⟩
      invFun s :=
        { app U := (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
            ((abelianSheafToGrpSheafObjEquiv F U).symm (s.1 U)).toAdd
          naturality U V f := by
            refine (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective ?_
            -- Both sides are evaluated at `1`; the section `s` is compatible with restriction.
            simp only [Functor.const_obj_map, Functor.const_obj_obj]
            rw [AddCommGrpCat.uliftZMultiplesAddEquiv_comp,
              AddCommGrpCat.uliftZMultiplesAddEquiv_comp,
              AddEquiv.apply_symm_apply, AddCommGrpCat.uliftZMultiplesAddEquiv_id,
              AddCommGrpCat.uliftZMultiplesAddEquiv_symm_apply_one, map_toAdd_symm_sections] }
      left_inv ψ := NatTrans.ext (funext fun U ↦
        (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm_apply_eq.2 (by
          rw [MulEquiv.symm_apply_apply, toAdd_ofAdd,
            AddCommGrpCat.uliftZMultiplesAddEquiv_apply_eq]))
      right_inv s := Subtype.ext (funext fun U ↦
        (congrArg (fun a ↦ abelianSheafToGrpSheafObjEquiv F U (.ofAdd a))
          ((AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply _)).trans (by simp)) }
  map_mul' ψ φ := Subtype.ext (funext fun U ↦ by
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.coe_fn_mk, GrpCat.sections_mul_val,
      toAdd_mul]
    rw [← map_mul, ← ofAdd_add, NatTrans.app_add, AddCommGrpCat.hom_add_apply])

/-- The section corresponding to a morphism from the constant integer presheaf is its value
at `1`. -/
@[simp]
lemma constIntHomMulEquivSections_apply_coe (F : Sheaf J AddCommGrpCat.{w})
    (ψ : Multiplicative ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F.obj))
    (U : Cᵒᵖ) :
    (constIntHomMulEquivSections F ψ).1 U =
      abelianSheafToGrpSheafObjEquiv F U (.ofAdd (ψ.toAdd.app U ⟨1⟩)) :=
  (rfl)

/-- The morphism from the constant integer presheaf corresponding to a global section `s` is, over
each `U`, the morphism from `ℤ` sending `1` to the value of `s` over `U`. -/
@[simp]
lemma constIntHomMulEquivSections_symm_apply_app (F : Sheaf J AddCommGrpCat.{w})
    (s : (((abelianSheafToGrpSheaf J).obj F).obj ⋙ forget GrpCat).sections) (U : Cᵒᵖ) :
    ((constIntHomMulEquivSections F).symm s).toAdd.app U =
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
        ((abelianSheafToGrpSheafObjEquiv F U).symm (s.1 U)).toAdd :=
  (rfl)

end Sheaf

namespace Sheaf.Torsor

variable {F : Sheaf J AddCommGrpCat.{w}} (P : Torsor ((abelianSheafToGrpSheaf J).obj F))

/-- The difference of two sections of a torsor under an abelian sheaf. -/
private def diff {U : Cᵒᵖ} (p q : P.sheaf.obj.obj U) : F.obj.obj U :=
  ((abelianSheafToGrpSheafObjEquiv F U).symm
    (MulAction.exists_smul_eq (((abelianSheafToGrpSheaf J).obj F).obj.obj U) q p).choose).toAdd

private lemma diff_smul {U : Cᵒᵖ} (p q : P.sheaf.obj.obj U) :
    abelianSheafToGrpSheafObjEquiv F U (.ofAdd (diff P p q)) • q = p :=
  (MulAction.exists_smul_eq (((abelianSheafToGrpSheaf J).obj F).obj.obj U) q p).choose_spec

private lemma diff_eq_of_smul {U : Cᵒᵖ} {p q : P.sheaf.obj.obj U} {a : F.obj.obj U}
    (h : abelianSheafToGrpSheafObjEquiv F U (.ofAdd a) • q = p) : diff P p q = a := by
  have := P.smul_left_injective q ((diff_smul P p q).trans h.symm)
  simpa using this

private lemma diff_add_diff {U : Cᵒᵖ} (p q r : P.sheaf.obj.obj U) :
    diff P p q + diff P q r = diff P p r :=
  (diff_eq_of_smul P (by rw [ofAdd_add, map_mul, mul_smul, diff_smul, diff_smul])).symm

private lemma diff_self {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) : diff P p p = 0 :=
  diff_eq_of_smul P (by simp)

private lemma map_diff {U V : Cᵒᵖ} (f : U ⟶ V) (p q : P.sheaf.obj.obj U) :
    F.obj.map f (diff P p q) = diff P (P.sheaf.obj.map f p) (P.sheaf.obj.map f q) := by
  refine (diff_eq_of_smul P ?_).symm
  rw [← toAdd_ofAdd (diff P p q), ← abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv,
    ← P.map_smul, diff_smul]

private lemma lift_diff {U : Cᵒᵖ} (p₀ p₁ : P.sheaf.obj.obj U) (x : FreeAbelianGroup _) :
    FreeAbelianGroup.lift (diff P · p₀) x =
      FreeAbelianGroup.lift (diff P · p₁) x + degree _ x • diff P p₁ p₀ := by
  rw [← FreeAbelianGroup.lift_const_apply, ← FreeAbelianGroup.lift_add_apply]
  simp only [Pi.add_def, diff_add_diff]

/-- Restriction of formal sums of degree zero along a morphism. -/
private def degZeroMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    (degree (P.sheaf.obj.obj U)).ker →+ (degree (P.sheaf.obj.obj V)).ker :=
  ((FreeAbelianGroup.map (P.sheaf.obj.map f)).comp (degree _).ker.subtype).codRestrict _
    fun x ↦ (FreeAbelianGroup.degree_map _ x.1).trans x.2

private lemma coe_degZeroMap {U V : Cᵒᵖ} (f : U ⟶ V) (x : (degree (P.sheaf.obj.obj U)).ker) :
    (degZeroMap P f x : FreeAbelianGroup (P.sheaf.obj.obj V)) =
      FreeAbelianGroup.map (P.sheaf.obj.map f) x.1 :=
  (rfl)

/-- The presheaf of formal sums of degree zero of sections of a torsor, a subpresheaf of the
free abelian presheaf on the torsor. -/
private def degZero : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (degree (P.sheaf.obj.obj U)).ker
  map f := AddCommGrpCat.ofHom (degZeroMap P f)
  map_id U := by
    ext x
    exact congr(AddCommGrpCat.Hom.hom $((P.sheaf.obj ⋙ AddCommGrpCat.free).map_id U) x.1)
  map_comp f g := by
    ext x
    exact congr(AddCommGrpCat.Hom.hom $((P.sheaf.obj ⋙ AddCommGrpCat.free).map_comp f g) x.1)

/-- The inclusion of the formal sums of degree zero into all formal sums. -/
private def degZeroι : degZero P ⟶ P.sheaf.obj ⋙ AddCommGrpCat.free where
  app U := AddCommGrpCat.ofHom (degree _).ker.subtype

private instance : Mono (degZeroι P) :=
  have (U : Cᵒᵖ) : Mono ((degZeroι P).app U) :=
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  NatTrans.mono_of_mono_app _

open scoped Classical in
/-- The difference map on formal sums of degree zero: `∑ nᵢ pᵢ ↦ ∑ nᵢ (pᵢ - p₀)`, which does not
depend on the base section `p₀`. -/
private def diffHom (U : Cᵒᵖ) : (degree (P.sheaf.obj.obj U)).ker →+ F.obj.obj U :=
  if h : Nonempty (P.sheaf.obj.obj U) then
    (FreeAbelianGroup.lift (diff P · h.some)).comp (degree _).ker.subtype
  else 0

private lemma diffHom_apply {U : Cᵒᵖ} (p₀ : P.sheaf.obj.obj U)
    (x : (degree (P.sheaf.obj.obj U)).ker) :
    diffHom P U x = FreeAbelianGroup.lift (diff P · p₀) x.1 := by
  rw [diffHom, dite_eq_left_of_eq_true (eq_true ⟨p₀⟩), AddMonoidHom.comp_apply,
    lift_diff P _ p₀, AddSubgroup.coe_subtype, x.2, zero_smul, add_zero]

private lemma diffHom_degZeroMap {U V : Cᵒᵖ} (f : U ⟶ V) (x : (degree (P.sheaf.obj.obj U)).ker) :
    diffHom P V (degZeroMap P f x) = F.obj.map f (diffHom P U x) := by
  by_cases h : Nonempty (P.sheaf.obj.obj U)
  · obtain ⟨p₀⟩ := h
    rw [diffHom_apply P (P.sheaf.obj.map f p₀), diffHom_apply P p₀,
      ← FreeAbelianGroup.lift_comp_apply, coe_degZeroMap]
    refine (FreeAbelianGroup.lift_unique _
      ((FreeAbelianGroup.lift _).comp (FreeAbelianGroup.map (P.sheaf.obj.map f))) fun p ↦ ?_).trans
      (congrArg (FreeAbelianGroup.lift · x.1) (funext fun p ↦ (map_diff P f p p₀).symm))
    simp [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
  · have : IsEmpty (P.sheaf.obj.obj U) := not_nonempty_iff.1 h
    obtain rfl : x = 0 := Subtype.ext (Subsingleton.elim _ _)
    simp

/-- The difference map, as a morphism of presheaves. -/
private def degZeroDiff : degZero P ⟶ F.obj where
  app U := AddCommGrpCat.ofHom (diffHom P U)
  naturality U V f := by
    ext x
    exact diffHom_degZeroMap P f x

variable [HasSheafify J AddCommGrpCat.{w}]

/-- A torsor `P` under an abelian sheaf `F` admits, for every morphism `ι : F ⟶ I` to an injective
abelian sheaf, a morphism `u : P → I` with `u (a • p) = ι a + u p`. -/
theorem exists_hom_smul_eq_of_injective {I : Sheaf J AddCommGrpCat.{w}} [Injective I]
    (ι : F ⟶ I) :
    ∃ u : P.sheaf ⟶ (trivial ((abelianSheafToGrpSheaf J).obj I)).sheaf,
      ∀ (U : Cᵒᵖ) (a : ((abelianSheafToGrpSheaf J).obj F).obj.obj U) (p : P.sheaf.obj.obj U),
        u.hom.app U (a • p) = ((abelianSheafToGrpSheaf J).map ι).hom.app U a • u.hom.app U p := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  -- Extend `∑ nᵢ pᵢ ↦ ι (∑ nᵢ (pᵢ - p₀))` from formal sums of degree zero to all formal sums.
  let φ : P.sheaf.obj ⋙ AddCommGrpCat.free ⟶ I.obj := adj.homEquiv _ _
    (Injective.factorThru ((adj.homEquiv _ _).symm (degZeroDiff P ≫ ι.hom))
      ((presheafToSheaf J _).map (degZeroι P)))
  have hφ : degZeroι P ≫ φ = degZeroDiff P ≫ ι.hom := by
    rw [← adj.homEquiv_naturality_left, Injective.comp_factorThru, Equiv.apply_symm_apply]
  -- The extension is a map `ψ : P → I` with `ψ p - ψ q = ι (p - q)`.
  let ψ (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) : I.obj.obj U := φ.app U (FreeAbelianGroup.of p)
  have hψ (U : Cᵒᵖ) (p q : P.sheaf.obj.obj U) : ψ U p - ψ U q = ι.hom.app U (diff P p q) := by
    have := congr(AddCommGrpCat.Hom.hom (NatTrans.app $hφ U)
      (⟨FreeAbelianGroup.of p - FreeAbelianGroup.of q,
        by simp⟩ : (degree (P.sheaf.obj.obj U)).ker))
    -- Both sides of `this` are, by definition, `φ` and `ι ∘ diffHom` applied to `[p] - [q]`.
    refine ((map_sub (φ.app U).hom _ _).symm.trans this).trans
      (congrArg (ι.hom.app U) ((diffHom_apply P q _).trans ?_))
    simp [FreeAbelianGroup.lift_apply_of, diff_self]
  have hψmap {U V : Cᵒᵖ} (f : U ⟶ V) (p : P.sheaf.obj.obj U) :
      ψ V (P.sheaf.obj.map f p) = I.obj.map f (ψ U p) :=
    NatTrans.naturality_apply φ f (FreeAbelianGroup.of p)
  -- The restriction maps of the trivial torsor are those of `I`, written multiplicatively.
  refine ⟨ObjectProperty.homMk
    { app U := ↾fun p ↦ abelianSheafToGrpSheafObjEquiv I U (.ofAdd (ψ U p))
      naturality U V f := by
        ext p
        exact congrArg (fun x ↦ abelianSheafToGrpSheafObjEquiv I V (.ofAdd x)) (hψmap f p) },
    fun U a p ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (abelianSheafToGrpSheafObjEquiv F U).surjective a
  have : ψ U (abelianSheafToGrpSheafObjEquiv F U a • p) = ι.hom.app U a.toAdd + ψ U p := by
    rw [← sub_eq_iff_eq_add, hψ]
    exact congrArg _ (diff_eq_of_smul P (by simp))
  -- The action of `I` on the trivial torsor is multiplication.
  exact (congrArg (fun x ↦ abelianSheafToGrpSheafObjEquiv I U (.ofAdd x)) this).trans
    (by rw [ofAdd_add, map_mul]; rfl)

end Sheaf.Torsor

namespace Sheaf.NonabelianH1

/-- Every torsor under an injective abelian sheaf is trivial. -/
instance subsingleton_of_injective [HasSheafify J AddCommGrpCat.{w}]
    (I : Sheaf J AddCommGrpCat.{w}) [Injective I] :
    Subsingleton (NonabelianH1 ((abelianSheafToGrpSheaf J).obj I)) where
  allEq x y := by
    suffices ∀ x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj I), x = 1 by rw [this x, this y]
    intro x
    induction x using ind with | h P => ?_
    obtain ⟨u, hu⟩ := P.exists_hom_smul_eq_of_injective (𝟙 I)
    -- `u` is a morphism to the trivial torsor, since `𝟙 I` acts as the identity on sections.
    exact mk_eq_mk_of_hom (Q := Torsor.trivial _) ⟨u, hu⟩

end Sheaf.NonabelianH1

namespace ShortComplex.ShortExact

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- A short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves is an extension of the
underlying sheaves of groups. -/
theorem isGroupExtension (hS : S.ShortExact) :
    Sheaf.IsGroupExtension ((abelianSheafToGrpSheaf J).map S.f)
      ((abelianSheafToGrpSheaf J).map S.g) where
  injective U :=
    have := hS.mono_f
    Sheaf.injective_app_of_mono S.f U
  range_eq_ker U := by
    have := hS.mono_f
    -- Taking sections over `U` is left exact.
    have h := (hS.exact.map_of_mono_of_preservesKernel (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U) inferInstance inferInstance).ab_range_eq_ker
    -- The kernel and image of `S.g` and `S.f` on sections, written multiplicatively.
    exact SetLike.ext fun x ↦ SetLike.ext_iff.1 h x.toAdd
  isLocallySurjective := by
    have := hS.epi_g
    have : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 inferInstance
    -- Local surjectivity only involves the underlying sets of sections.
    exact ⟨fun s ↦ Presheaf.imageSieve_mem J S.g.hom s⟩

end ShortComplex.ShortExact

namespace Sheaf.NonabelianH1

variable [HasSheafify J AddCommGrpCat.{w}] {F I Q : Sheaf J AddCommGrpCat.{w}} [Injective I]
  {ι : F ⟶ I} {π : I ⟶ Q}

/-- For an extension `0 → F → I → Q → 0` of abelian sheaves with `I` injective, every `F`-torsor
is the torsor of lifts of a global section of `Q`: the connecting map `Q(C) → H¹(F)` is
surjective. Short exact sequences of abelian sheaves are such extensions by
`CategoryTheory.ShortComplex.ShortExact.isGroupExtension`. -/
theorem connecting_surjective_of_injective
    (hE : IsGroupExtension ((abelianSheafToGrpSheaf J).map ι) ((abelianSheafToGrpSheaf J).map π)) :
    Function.Surjective (connecting hE) := by
  intro x
  induction x using ind with | h P => ?_
  obtain ⟨u, hu⟩ := P.exists_hom_smul_eq_of_injective ι
  exact mk_mem_range_connecting hE u hu

end Sheaf.NonabelianH1

end CategoryTheory
