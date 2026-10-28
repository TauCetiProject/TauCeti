/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.CategoryTheory.Linear.FullSubcategory

/-!
# Cokernels of matrix factorizations

Taking the cokernel of the even-to-odd differential gives an additive functor to finitely
generated modules over the coefficient ring. The projection and its universal property retain
the ordinary categorical cokernel API; on elements, the projection is surjective with kernel the
image of `d₀`. The functor uses Mathlib's
`CategoryTheory.Limits.coker` on the arrows supplied by the differential.

Composing scalar extension with this functor gives cokernels over a target ring with arbitrary
image potential. In particular, reduction modulo the potential gives the finite module used in
hypersurface comparisons; no vanishing condition is required for the cokernel construction.

For a factorization of the zero potential, `d₀ ≫ d₁ = 0`, so `d₁` descends to a map
`coker d₀ ⟶ X₀` (`TauCeti.MatrixFactorization.cokernelDesc`). On cokernels, the boundary of an
odd map `(h₀, h₁)` is this descent followed by `h₀` and the projection
(`TauCeti.MatrixFactorization.cokernelFunctor_map_hom_eq`). The cokernel also carries a
componentwise short exact sequence of such factorizations whose third term is exact at its even
component to a short exact sequence of modules
(`TauCeti.MatrixFactorization.shortExact_map_cokernelFunctor_comp_forget₂`).

This construction requires only commutative rings; it does not assert that its values are maximal
Cohen–Macaulay, which requires additional hypotheses. After reduction modulo the potential, the
cokernel descends to a functor from the homotopy category to a stable module category; that
descent is in `TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Stable`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Section 3.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}

private theorem finite_cokernel (X : MatrixFactorization S w) :
    Module.Finite S (cokernel X.obj.d₀.hom : ModuleCat.{u} S) := by
  exact Module.Finite.of_surjective (cokernel.π X.obj.d₀.hom).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Take the cokernel of the even-to-odd differential. Its finite generation follows from
that of the odd component, without any condition on the potential. -/
def cokernelFunctor : MatrixFactorization S w ⥤ FGModuleCat.{u} S := by
  let G : MatrixFactorization S w ⥤ Arrow (ModuleCat.{u} S) :=
    { obj X := Arrow.mk X.obj.d₀.hom
      map g := Arrow.homMk g.hom.f₀.hom g.hom.f₁.hom
        (congrArg (fun k => k.hom) g.hom.comm₀)
      map_id X := by ext <;> simp
      map_comp g h := by ext <;> simp }
  exact (ModuleCat.isFG S).lift (G ⋙ coker (ModuleCat.{u} S)) finite_cokernel

/-- The underlying module of the finite cokernel functor is the categorical cokernel of the
even differential. This isomorphism permits use of Mathlib's cokernel API without
unfolding the functor. -/
def cokernelFunctorObjIso (X : MatrixFactorization S w) :
    (cokernelFunctor.obj X).obj ≅
      cokernel X.obj.d₀.hom := Iso.refl _

/-- The projection from the odd component onto the finite cokernel, as a map of modules. -/
def cokernelπ (X : MatrixFactorization S w) :
    X.obj.X₁.obj ⟶ (cokernelFunctor.obj X).obj :=
  cokernel.π _

/-- The object comparison carries the projection to the categorical cokernel projection. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_objIso_hom (X : MatrixFactorization S w) :
    cokernelπ X ≫ (cokernelFunctorObjIso X).hom =
      cokernel.π X.obj.d₀.hom := by
  exact Category.comp_id _

/-- The even differential vanishes after projection to the cokernel. -/
@[reassoc (attr := simp)]
theorem d₀_cokernelπ (X : MatrixFactorization S w) :
    X.obj.d₀.hom ≫ cokernelπ X = 0 :=
  cokernel.condition _

/-- The cokernel projection is natural with respect to closed even maps. -/
@[reassoc (attr := simp↓)]
theorem cokernelπ_naturality {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    cokernelπ X ≫ (cokernelFunctor.map g).hom =
      g.hom.f₁.hom ≫ cokernelπ Y := by
  exact cokernel.π_desc _ _ _

/-- On elements, the cokernel projection is natural with respect to closed even maps. -/
theorem cokernelπ_naturality_apply {X Y : MatrixFactorization S w} (g : X ⟶ Y)
    (y : X.obj.X₁.obj) :
    (cokernelFunctor.map g).hom.hom (cokernelπ X y) = cokernelπ Y (g.hom.f₁.hom.hom y) :=
  congrArg (fun k ↦ k.hom y) (cokernelπ_naturality g)

/-- The projection exhibits the underlying finite module as the categorical cokernel.
This supplies the full existence and uniqueness API for maps killing the even differential. -/
def isColimitCokernelπ (X : MatrixFactorization S w) :
    IsColimit (CokernelCofork.ofπ (cokernelπ X) (d₀_cokernelπ X)) :=
  cokernelIsCokernel _

instance cokernelπ_epi (X : MatrixFactorization S w) :
    Epi (cokernelπ X) :=
  epi_of_isColimit_cofork
    (c := CokernelCofork.ofπ (cokernelπ X) (d₀_cokernelπ X))
    (isColimitCokernelπ X)

/-- The cokernel projection is surjective. -/
theorem cokernelπ_surjective (X : MatrixFactorization S w) :
    Function.Surjective (cokernelπ X) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- On elements, the even differential and the cokernel projection form an exact pair: the
kernel of the projection is the image of `d₀`. -/
theorem exact_d₀_cokernelπ (X : MatrixFactorization S w) :
    Function.Exact X.obj.d₀.hom.hom (cokernelπ X).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((ShortComplex.mk _ _ (d₀_cokernelπ X)).exact_of_g_is_cokernel (isColimitCokernelπ X))

/-- Under the object comparisons, a closed even map acts by the map induced on categorical
cokernels by its components. -/
theorem cokernelFunctor_map_objIso_hom {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (cokernelFunctor.map g).hom ≫ (cokernelFunctorObjIso Y).hom =
      (cokernelFunctorObjIso X).hom ≫
        cokernel.map _ _ g.hom.f₀.hom
          g.hom.f₁.hom
          (congrArg (fun k => k.hom) g.hom.comm₀).symm := by
  apply (cancel_epi (cokernelπ X)).mp
  rw [← Category.assoc, cokernelπ_naturality, Category.assoc,
    cokernelπ_objIso_hom, cokernelπ_objIso_hom_assoc]
  exact (cokernel.π_desc _ _ _).symm

/-- The cokernel functor preserves addition of closed even maps. -/
instance cokernelFunctor_additive :
    (cokernelFunctor (S := S) (w := w)).Additive where
  map_add := by
    intro X Y g h
    apply ObjectProperty.hom_ext
    apply (cancel_epi (cokernelπ X)).mp
    simp only [ObjectProperty.add_hom, Preadditive.comp_add, cokernelπ_naturality,
      CurvedDuplex.add_f₁, Preadditive.add_comp]

/-! ### The zero potential

The potential is only assumed to be propositionally zero, so that these results apply to the
base change of a factorization along a ring map killing its potential. -/

/-- For a factorization of a zero potential, `d₀ ≫ d₁ = 0`. -/
private theorem d₀_hom_comp_d₁_hom (hw : w = 0) (X : MatrixFactorization S w) :
    X.obj.d₀.hom ≫ X.obj.d₁.hom = 0 := by
  subst hw
  rw [← ObjectProperty.FullSubcategory.comp_hom, X.obj.d₀_comp_d₁, zero_smul,
    ObjectProperty.zero_hom]

/-- For a factorization of a zero potential, the odd-to-even differential `d₁` kills the image
of `d₀`, so it descends to a map `coker d₀ ⟶ X₀`. -/
def cokernelDesc (hw : w = 0) (X : MatrixFactorization S w) :
    cokernelFunctor.obj X ⟶ X.obj.X₀ :=
  ObjectProperty.homMk
    ((isColimitCokernelπ X).desc (CokernelCofork.ofπ X.obj.d₁.hom (d₀_hom_comp_d₁_hom hw X)))

/-- The descent of `d₁` restricts to `d₁` along the cokernel projection. -/
@[reassoc (attr := simp)]
theorem cokernelπ_cokernelDesc_hom (hw : w = 0) (X : MatrixFactorization S w) :
    cokernelπ X ≫ (cokernelDesc hw X).hom = X.obj.d₁.hom :=
  Cofork.IsColimit.π_desc (isColimitCokernelπ X)

/-- For a zero potential, the cokernel of the boundary `d h + h d` of an odd map `(h₀, h₁)` is
the descent `coker d₀ ⟶ X₀` of `d₁`, followed by `h₀ : X₀ ⟶ Y₁` and the projection
`Y₁ ⟶ coker d₀`. The summand `h₁ ≫ d₀` of the odd component is killed by the projection. -/
theorem cokernelFunctor_map_hom_eq (hw : w = 0) {X Y : MatrixFactorization S w}
    (g : X ⟶ Y) (h₀ : X.obj.X₀ ⟶ Y.obj.X₁) (h₁ : X.obj.X₁ ⟶ Y.obj.X₀)
    (hg : CurvedDuplex.nullHomotopicMap h₀ h₁ = g.hom) :
    (cokernelFunctor.map g).hom = (cokernelDesc hw X).hom ≫ h₀.hom ≫ cokernelπ Y := by
  apply (cancel_epi (cokernelπ X)).mp
  rw [cokernelπ_naturality, cokernelπ_cokernelDesc_hom_assoc, ← hg]
  simp

/-- For factorizations of the zero potential, cokernels of even-to-odd differentials carry a short
complex `X₁ ⟶ X₂ ⟶ X₃` that is short exact in both components to a short exact sequence of
modules, provided `X₃` is exact at its even component (`ker d₀ = im d₁`). The right exactness
is that of cokernels; the injectivity on the left uses the exactness of `X₃`. -/
theorem shortExact_map_cokernelFunctor_comp_forget₂ (hw : w = 0)
    {T : ShortComplex (MatrixFactorization S w)}
    (hf₁ : Function.Injective T.f.hom.f₁.hom.hom)
    (h₀ : Function.Exact T.f.hom.f₀.hom.hom T.g.hom.f₀.hom.hom)
    (h₁ : Function.Exact T.f.hom.f₁.hom.hom T.g.hom.f₁.hom.hom)
    (hg₀ : Function.Surjective T.g.hom.f₀.hom.hom)
    (hg₁ : Function.Surjective T.g.hom.f₁.hom.hom)
    (hX₃ : Function.Exact T.X₃.obj.d₁.hom.hom T.X₃.obj.d₀.hom.hom) :
    (T.map (cokernelFunctor ⋙ forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S))).ShortExact := by
  subst hw
  -- Exactness in the middle: lift along `cokernelπ`, correct by `d₀`, and use exactness of the
  -- odd components.
  have hex :
      Function.Exact (cokernelFunctor.map T.f).hom.hom (cokernelFunctor.map T.g).hom.hom := by
    intro c
    obtain ⟨b, rfl⟩ := cokernelπ_surjective T.X₂ c
    refine ⟨fun hc ↦ ?_, ?_⟩
    · rw [cokernelπ_naturality_apply] at hc
      obtain ⟨a₃, ha₃⟩ := ((exact_d₀_cokernelπ T.X₃) _).1 hc
      obtain ⟨a₂, rfl⟩ := hg₀ a₃
      obtain ⟨b₁, hb₁⟩ := (h₁ (b - T.X₂.obj.d₀.hom.hom a₂)).1 (by
        rw [map_sub, ← comm₀_apply, ha₃, sub_self])
      refine ⟨cokernelπ T.X₁ b₁, ?_⟩
      rw [cokernelπ_naturality_apply, hb₁, map_sub, ((exact_d₀_cokernelπ T.X₂) _).2 ⟨a₂, rfl⟩,
        sub_zero]
    · rintro ⟨c₁, hc₁⟩
      rw [← hc₁]
      simpa only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, T.zero, Functor.map_zero,
        ObjectProperty.zero_hom, ModuleCat.hom_zero, LinearMap.zero_apply] using
        congrArg (fun k ↦ k.hom.hom c₁) (cokernelFunctor.map_comp T.f T.g).symm
  -- Injectivity on the left: the snake-lemma connecting map vanishes because `ker d₀ = im d₁`
  -- in `X₃` and `d₀ d₁ = 0` in `X₂`.
  have hinj : Function.Injective (cokernelFunctor.map T.f).hom.hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨b, rfl⟩ := cokernelπ_surjective T.X₁ c
    rw [cokernelπ_naturality_apply] at hc
    obtain ⟨a₂, ha₂⟩ := ((exact_d₀_cokernelπ T.X₂) _).1 hc
    obtain ⟨b₃, hb₃⟩ := (hX₃ (T.g.hom.f₀.hom.hom a₂)).1 (by
      rw [comm₀_apply, ha₂, h₁.apply_apply_eq_zero])
    obtain ⟨b₂, rfl⟩ := hg₁ b₃
    obtain ⟨a₁, ha₁⟩ := (h₀ (a₂ - T.X₂.obj.d₁.hom.hom b₂)).1 (by
      rw [map_sub, ← hb₃, ← comm₁_apply, sub_self])
    refine ((exact_d₀_cokernelπ T.X₁) _).2 ⟨a₁, hf₁ ?_⟩
    rw [← comm₀_apply, ha₁, map_sub, d₁_comp_d₀_apply, zero_smul, sub_zero, ha₂]
  -- Surjectivity on the right: both `cokernelπ` and the odd component of `T.g` are surjective.
  have hsurj : Function.Surjective (cokernelFunctor.map T.g).hom.hom := by
    intro c
    obtain ⟨b₃, rfl⟩ := cokernelπ_surjective T.X₃ c
    obtain ⟨b₂, rfl⟩ := hg₁ b₃
    exact ⟨cokernelπ T.X₂ b₂, cokernelπ_naturality_apply T.g b₂⟩
  -- Forgetting finite generation does not change the underlying linear maps.
  exact
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hex
      mono_f := (ModuleCat.mono_iff_injective _).2 hinj
      epi_g := (ModuleCat.epi_iff_surjective _).2 hsurj }

end TauCeti.MatrixFactorization
