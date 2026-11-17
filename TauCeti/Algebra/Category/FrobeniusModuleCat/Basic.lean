/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Monoidal.Transport
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Linearized Frobenius modules

Let `S` be a commutative ring and `σ : S →+* S` a ring endomorphism, the "Frobenius" of `S`. No
inverse of `σ` is assumed: the motivating examples are `x ↦ x ^ p` on an `𝔽_p`-algebra and the
Witt vector Frobenius, which need not be surjective. A *linearized Frobenius module* over
`(S, σ)` is an `S`-module `M` together with an `S`-linear isomorphism
`L : S ⊗_{S,σ} M ≅ M`, the *linearization*, from the scalar extension of `M` along `σ`.
Its *Frobenius* is the `σ`-semilinear map `F m = L (1 ⊗ m)`, and `L (s ⊗ m) = s • F m`.

A semilinear map `F` defines a linearized Frobenius module exactly when its linearization
`s ⊗ m ↦ s • F m` is bijective. This is weaker than bijectivity of `F` itself: for the module `S`
with `F = σ`, the linearization is `s ⊗ a ↦ s * σ a`, which is always bijective, while `σ` need
not be surjective. Conversely a nonzero module never carries the zero Frobenius, because the
image of `F` spans `M` over `S`.

The linearized Frobenius modules form the category `TauCeti.FrobeniusModuleCat σ`, whose
morphisms are the module maps intertwining the linearizations, equivalently the Frobenii. It is
the full subcategory of the algebras over the endofunctor `ModuleCat.extendScalars σ` whose
structure map is an isomorphism. Extension of scalars is a monoidal functor, so the category is
monoidal: the tensor product of two linearized Frobenius modules has Frobenius
`m ⊗ n ↦ F m ⊗ F n`, and the unit is the module `S` with Frobenius `σ`.

## Main definitions

* `TauCeti.FrobeniusModuleCat σ`: the category of linearized Frobenius modules over `(S, σ)`.
* `TauCeti.FrobeniusModuleCat.frobenius`: the semilinear Frobenius of a linearized Frobenius
  module.
* `TauCeti.FrobeniusModuleCat.ofFrobenius`: the linearized Frobenius module defined by a
  semilinear map with bijective linearization.
* `TauCeti.FrobeniusModuleCat.forget σ`: the faithful functor to `ModuleCat S`.
* The monoidal structure on `TauCeti.FrobeniusModuleCat σ`, lifting that of `ModuleCat S`.

## Main results

* `TauCeti.FrobeniusModuleCat.linearization_hom_tmul`: `L (s ⊗ m) = s • F m`.
* `TauCeti.FrobeniusModuleCat.map_comp_linearization_hom_iff`: a module map intertwines the
  linearizations exactly when it intertwines the Frobenii.
* `TauCeti.FrobeniusModuleCat.span_range_frobenius`: the image of the Frobenius spans the module.
* `TauCeti.FrobeniusModuleCat.frobenius_eq_zero_iff`: the Frobenius vanishes only on the zero
  module.
* `TauCeti.FrobeniusModuleCat.tensor_frobenius_tmul` and
  `TauCeti.FrobeniusModuleCat.tensorUnit_frobenius_apply`: the Frobenius of a tensor product is
  `F ⊗ F`, and that of the unit is `σ`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Convention 1.5.1.
-/

public section

open CategoryTheory MonoidalCategory TensorProduct

universe u

namespace TauCeti

variable {S : Type u} [CommRing S] (σ : S →+* S)

/-- A *linearized Frobenius module* over a commutative ring `S` with an endomorphism `σ`: an
`S`-module together with an `S`-linear isomorphism `S ⊗_{S,σ} M ≅ M` from its extension of
scalars along `σ`. No inverse of `σ` is required. -/
structure FrobeniusModuleCat where
  /-- The underlying `S`-module. -/
  carrier : ModuleCat.{u} S
  /-- The linearization `S ⊗_{S,σ} M ≅ M`. -/
  linearization : (ModuleCat.extendScalars σ).obj carrier ≅ carrier

namespace FrobeniusModuleCat

variable {σ}

/-- A linearized Frobenius module, as an algebra over the endofunctor
`ModuleCat.extendScalars σ`. Morphisms of linearized Frobenius modules are the morphisms of these
algebras. -/
abbrev toAlgebra (M : FrobeniusModuleCat σ) : Endofunctor.Algebra (ModuleCat.extendScalars σ) :=
  ⟨M.carrier, M.linearization.hom⟩

/-- The morphisms of linearized Frobenius modules are the module maps `f` with
`(1 ⊗ f) ≫ L = L ≫ f`: the full subcategory of the category of algebras over
`ModuleCat.extendScalars σ` on the algebras with invertible structure map. -/
noncomputable instance : Category (FrobeniusModuleCat σ) :=
  inferInstanceAs (Category (InducedCategory _ (toAlgebra (σ := σ))))

variable (σ) in
/-- The forgetful functor from linearized Frobenius modules to modules. -/
@[expose] noncomputable def forget : FrobeniusModuleCat σ ⥤ ModuleCat.{u} S :=
  inducedFunctor (toAlgebra (σ := σ)) ⋙ Endofunctor.Algebra.forget _

/-- A morphism of linearized Frobenius modules from a module map intertwining the
linearizations. -/
noncomputable def homMk {M N : FrobeniusModuleCat σ} (f : M.carrier ⟶ N.carrier)
    (h : (ModuleCat.extendScalars σ).map f ≫ N.linearization.hom = M.linearization.hom ≫ f) :
    M ⟶ N :=
  InducedCategory.homMk ⟨f, h⟩

/-- An isomorphism of linearized Frobenius modules from a module isomorphism intertwining the
linearizations. -/
noncomputable def isoMk {M N : FrobeniusModuleCat σ} (e : M.carrier ≅ N.carrier)
    (h : (ModuleCat.extendScalars σ).map e.hom ≫ N.linearization.hom =
      M.linearization.hom ≫ e.hom) :
    M ≅ N :=
  InducedCategory.isoMk (Endofunctor.Algebra.isoMk e h)

@[simp] theorem forget_obj (M : FrobeniusModuleCat σ) : (forget σ).obj M = M.carrier := (rfl)

@[simp] theorem forget_map {M N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    (forget σ).map f = f.hom.f := (rfl)

@[simp] theorem homMk_hom_f {M N : FrobeniusModuleCat σ} (f : M.carrier ⟶ N.carrier) (h) :
    (homMk f h).hom.f = f := (rfl)

@[simp] theorem isoMk_hom_hom_f {M N : FrobeniusModuleCat σ} (e : M.carrier ≅ N.carrier) (h) :
    (isoMk e h).hom.hom.f = e.hom := (rfl)

@[simp] theorem isoMk_inv_hom_f {M N : FrobeniusModuleCat σ} (e : M.carrier ≅ N.carrier) (h) :
    (isoMk e h).inv.hom.f = e.inv := (rfl)

@[reassoc (attr := simp)]
theorem map_hom_f_comp_linearization_hom {M N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    (ModuleCat.extendScalars σ).map f.hom.f ≫ N.linearization.hom =
      M.linearization.hom ≫ f.hom.f :=
  f.hom.h

/-- Two morphisms of linearized Frobenius modules agree when their underlying module maps
agree. -/
@[ext]
theorem hom_ext {M N : FrobeniusModuleCat σ} {f g : M ⟶ N} (h : f.hom.f = g.hom.f) : f = g :=
  InducedCategory.hom_ext (Endofunctor.Algebra.Hom.ext h)

@[simp] theorem id_hom_f (M : FrobeniusModuleCat σ) : (𝟙 M : M ⟶ M).hom.f = 𝟙 M.carrier :=
  (rfl)

@[simp, reassoc] theorem comp_hom_f {M N P : FrobeniusModuleCat σ} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom.f = f.hom.f ≫ g.hom.f := (rfl)

instance : (forget σ).Faithful where
  map_injective h := hom_ext h

/-- A morphism of linearized Frobenius modules is an isomorphism when its underlying module map
is. -/
instance : (forget σ).ReflectsIsomorphisms :=
  inferInstanceAs
    (inducedFunctor (toAlgebra (σ := σ)) ⋙ Endofunctor.Algebra.forget _).ReflectsIsomorphisms

section Frobenius

variable (M : FrobeniusModuleCat σ)

/-- The *Frobenius* of a linearized Frobenius module: the `σ`-semilinear map
`m ↦ L (1 ⊗ m)`. -/
noncomputable def frobenius : M.carrier →ₛₗ[σ] M.carrier :=
  ModuleCat.extendScalarsHomEquivSemilinearMap σ _ _ M.linearization.hom

theorem frobenius_apply (m : M.carrier) :
    M.frobenius m = M.linearization.hom ((1 : S) ⊗ₜ m) :=
  ModuleCat.extendScalarsHomEquivSemilinearMap_apply σ _ m

/-- The linearization is the linearization of the Frobenius. -/
theorem linearization_hom_eq :
    M.linearization.hom =
      (ModuleCat.extendScalarsHomEquivSemilinearMap σ _ _).symm M.frobenius :=
  ((ModuleCat.extendScalarsHomEquivSemilinearMap σ _ _).symm_apply_apply _).symm

/-- The linearization in terms of the Frobenius: `L (s ⊗ m) = s • F m`. -/
@[simp]
theorem linearization_hom_tmul (s : S) (m : M.carrier) :
    M.linearization.hom (s ⊗ₜ m) = s • M.frobenius m := by
  -- Here `s ⊗ₜ m` uses the module `S` over itself, while the lemma uses its restriction of scalars
  -- along `σ`: the two module structures are equal by definition, but not syntactically, so the
  -- lemma is applied with `exact` rather than rewritten.
  rw [linearization_hom_eq]
  exact ModuleCat.extendScalarsHomEquivSemilinearMap_symm_apply_tmul σ M.frobenius s m

/-- The image of the Frobenius spans the module: the linearization is surjective. -/
theorem span_range_frobenius : Submodule.span S (Set.range M.frobenius) = ⊤ := by
  set N := Submodule.span S (Set.range M.frobenius)
  -- The quotient map by `N` vanishes after the surjective linearization, since it kills `F m`.
  have h : M.linearization.hom ≫ ModuleCat.ofHom N.mkQ = 0 :=
    ModuleCat.ExtendScalars.hom_ext fun m ↦ (Submodule.Quotient.mk_eq_zero N).mpr
      (M.frobenius_apply m ▸ Submodule.subset_span (Set.mem_range_self m))
  have hq : N.mkQ = 0 := congrArg ModuleCat.Hom.hom
    ((cancel_epi M.linearization.hom).mp (h.trans Limits.comp_zero.symm))
  rw [← N.ker_mkQ, hq, LinearMap.ker_zero]

/-- The Frobenius of a linearized Frobenius module vanishes only on the zero module. -/
theorem frobenius_eq_zero_iff : M.frobenius = 0 ↔ Subsingleton M.carrier := by
  refine ⟨fun h ↦ ?_, fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩
  have hbot : Submodule.span S (Set.range M.frobenius) = ⊥ :=
    Submodule.span_eq_bot.mpr fun _ ⟨m, hm⟩ ↦ hm ▸ congrArg (· m) h
  exact (Submodule.subsingleton_iff S).mp
    (subsingleton_iff_bot_eq_top.mp (hbot.symm.trans M.span_range_frobenius))

/-- A module map intertwines the linearizations exactly when it intertwines the Frobenii. -/
theorem map_comp_linearization_hom_iff {M N : FrobeniusModuleCat σ}
    (f : M.carrier ⟶ N.carrier) :
    (ModuleCat.extendScalars σ).map f ≫ N.linearization.hom = M.linearization.hom ≫ f ↔
      ∀ m, f (M.frobenius m) = N.frobenius (f m) := by
  -- Both sides of `h` evaluated at `1 ⊗ m` are, by definition, `L (1 ⊗ f m)` and `f (L (1 ⊗ m))`:
  -- `(extendScalars σ).map f` sends `1 ⊗ m` to `1 ⊗ f m` (`ModuleCat.ExtendScalars.map_tmul`). That
  -- lemma and `ModuleCat.comp_apply` cannot be rewritten with, because `1 ⊗ m` here uses the module
  -- `S` over itself rather than its restriction of scalars along `σ`; so the identifications are
  -- left to definitional unfolding.
  refine ⟨fun h m ↦ ?_, fun h ↦ ModuleCat.ExtendScalars.hom_ext fun m ↦ ?_⟩
  · rw [frobenius_apply, frobenius_apply]
    exact (congrArg (fun φ : (ModuleCat.extendScalars σ).obj M.carrier ⟶ N.carrier ↦
      φ ((1 : S) ⊗ₜ m)) h).symm
  · have := h m
    rw [frobenius_apply, frobenius_apply] at this
    exact this.symm

/-- A morphism of linearized Frobenius modules commutes with the Frobenii. -/
@[simp]
theorem map_frobenius {M N : FrobeniusModuleCat σ} (f : M ⟶ N) (m : M.carrier) :
    f.hom.f (M.frobenius m) = N.frobenius (f.hom.f m) :=
  (map_comp_linearization_hom_iff f.hom.f).mp f.hom.h m

/-- A morphism of linearized Frobenius modules from a module map intertwining the Frobenii. -/
noncomputable def homMkOfFrobenius {M N : FrobeniusModuleCat σ} (f : M.carrier ⟶ N.carrier)
    (h : ∀ m, f (M.frobenius m) = N.frobenius (f m)) : M ⟶ N :=
  homMk f ((map_comp_linearization_hom_iff f).mpr h)

@[simp] theorem homMkOfFrobenius_hom_f {M N : FrobeniusModuleCat σ} (f : M.carrier ⟶ N.carrier)
    (h) : (homMkOfFrobenius f h).hom.f = f := (rfl)

/-- An isomorphism of linearized Frobenius modules from a module isomorphism intertwining the
Frobenii. -/
noncomputable def isoMkOfFrobenius {M N : FrobeniusModuleCat σ} (e : M.carrier ≅ N.carrier)
    (h : ∀ m, e.hom (M.frobenius m) = N.frobenius (e.hom m)) : M ≅ N :=
  isoMk e ((map_comp_linearization_hom_iff e.hom).mpr h)

@[simp] theorem isoMkOfFrobenius_hom_hom_f {M N : FrobeniusModuleCat σ}
    (e : M.carrier ≅ N.carrier) (h) : (isoMkOfFrobenius e h).hom.hom.f = e.hom := (rfl)

@[simp] theorem isoMkOfFrobenius_inv_hom_f {M N : FrobeniusModuleCat σ}
    (e : M.carrier ≅ N.carrier) (h) : (isoMkOfFrobenius e h).inv.hom.f = e.inv := (rfl)

end Frobenius

section OfFrobenius

variable (M : ModuleCat.{u} S) (F : M →ₛₗ[σ] M)
  [IsIso ((ModuleCat.extendScalarsHomEquivSemilinearMap σ M M).symm F)]

/-- The linearized Frobenius module defined by a semilinear map `F` whose linearization
`s ⊗ m ↦ s • F m` is an isomorphism. -/
@[expose] noncomputable def ofFrobenius : FrobeniusModuleCat σ where
  carrier := M
  linearization := asIso ((ModuleCat.extendScalarsHomEquivSemilinearMap σ M M).symm F)

@[simp] theorem ofFrobenius_carrier : (ofFrobenius M F).carrier = M := (rfl)

theorem ofFrobenius_linearization_hom :
    (ofFrobenius M F).linearization.hom =
      (ModuleCat.extendScalarsHomEquivSemilinearMap σ M M).symm F := (rfl)

@[simp] theorem frobenius_ofFrobenius : (ofFrobenius M F).frobenius = F :=
  (ModuleCat.extendScalarsHomEquivSemilinearMap σ M M).apply_symm_apply F

end OfFrobenius

section Monoidal

open Functor.OplaxMonoidal

/-- The tensor product of linearized Frobenius modules, with linearization
`S ⊗_{S,σ} (M ⊗ N) ≅ (S ⊗_{S,σ} M) ⊗ (S ⊗_{S,σ} N) ≅ M ⊗ N`. -/
@[expose] noncomputable def tensorObj (M N : FrobeniusModuleCat σ) : FrobeniusModuleCat σ where
  carrier := M.carrier ⊗ N.carrier
  linearization :=
    (Functor.Monoidal.μIso (ModuleCat.extendScalars σ) _ _).symm ≪≫
      (M.linearization ⊗ᵢ N.linearization)

variable (σ) in
/-- The unit linearized Frobenius module: `S` with linearization `s ⊗ a ↦ s * σ a`. -/
@[expose] noncomputable def tensorUnit : FrobeniusModuleCat σ where
  carrier := 𝟙_ _
  linearization := (Functor.Monoidal.εIso (ModuleCat.extendScalars σ)).symm

private theorem tensorHom_comm {M M' N N' : FrobeniusModuleCat σ} (f : M ⟶ M') (g : N ⟶ N') :
    (ModuleCat.extendScalars σ).map (f.hom.f ⊗ₘ g.hom.f) ≫
        δ (ModuleCat.extendScalars σ) M'.carrier N'.carrier ≫
          (M'.linearization.hom ⊗ₘ N'.linearization.hom) =
      (δ (ModuleCat.extendScalars σ) M.carrier N.carrier ≫
        (M.linearization.hom ⊗ₘ N.linearization.hom)) ≫ (f.hom.f ⊗ₘ g.hom.f) := by
  rw [← δ_natural_assoc, tensorHom_comp_tensorHom, map_hom_f_comp_linearization_hom,
    map_hom_f_comp_linearization_hom, Category.assoc, tensorHom_comp_tensorHom]

/-- The tensor product of morphisms of linearized Frobenius modules. -/
noncomputable def tensorHom {M M' N N' : FrobeniusModuleCat σ} (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M' N' :=
  homMk (f.hom.f ⊗ₘ g.hom.f) (tensorHom_comm f g)

private theorem associator_comm (M N P : FrobeniusModuleCat σ) :
    (ModuleCat.extendScalars σ).map (α_ M.carrier N.carrier P.carrier).hom ≫
        δ (ModuleCat.extendScalars σ) M.carrier (N.carrier ⊗ P.carrier) ≫
          (M.linearization.hom ⊗ₘ (δ (ModuleCat.extendScalars σ) N.carrier P.carrier ≫
            (N.linearization.hom ⊗ₘ P.linearization.hom))) =
      (δ (ModuleCat.extendScalars σ) (M.carrier ⊗ N.carrier) P.carrier ≫
        ((δ (ModuleCat.extendScalars σ) M.carrier N.carrier ≫
          (M.linearization.hom ⊗ₘ N.linearization.hom)) ⊗ₘ P.linearization.hom)) ≫
        (α_ M.carrier N.carrier P.carrier).hom := by
  rw [← whiskerLeft_comp_tensorHom, ← associativity_assoc, ← associator_naturality,
    whiskerRight_comp_tensorHom_assoc, Category.assoc]

private theorem leftUnitor_comm (M : FrobeniusModuleCat σ) :
    (ModuleCat.extendScalars σ).map (λ_ M.carrier).hom ≫ M.linearization.hom =
      (δ (ModuleCat.extendScalars σ) (𝟙_ _) M.carrier ≫
        (η (ModuleCat.extendScalars σ) ⊗ₘ M.linearization.hom)) ≫ (λ_ M.carrier).hom := by
  rw [← left_unitality_hom, Category.assoc, Category.assoc, Category.assoc, tensorHom_def,
    Category.assoc, leftUnitor_naturality]

private theorem rightUnitor_comm (M : FrobeniusModuleCat σ) :
    (ModuleCat.extendScalars σ).map (ρ_ M.carrier).hom ≫ M.linearization.hom =
      (δ (ModuleCat.extendScalars σ) M.carrier (𝟙_ _) ≫
        (M.linearization.hom ⊗ₘ η (ModuleCat.extendScalars σ))) ≫ (ρ_ M.carrier).hom := by
  rw [← right_unitality_hom, Category.assoc, Category.assoc, Category.assoc, tensorHom_def',
    Category.assoc, rightUnitor_naturality]

/-- The associator of linearized Frobenius modules: that of the underlying modules. -/
noncomputable def associator (M N P : FrobeniusModuleCat σ) :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) :=
  isoMk (α_ M.carrier N.carrier P.carrier) (associator_comm M N P)

/-- The left unitor of linearized Frobenius modules: that of the underlying modules. -/
noncomputable def leftUnitor (M : FrobeniusModuleCat σ) : tensorObj (tensorUnit σ) M ≅ M :=
  isoMk (λ_ M.carrier) (leftUnitor_comm M)

/-- The right unitor of linearized Frobenius modules: that of the underlying modules. -/
noncomputable def rightUnitor (M : FrobeniusModuleCat σ) : tensorObj M (tensorUnit σ) ≅ M :=
  isoMk (ρ_ M.carrier) (rightUnitor_comm M)

noncomputable instance : MonoidalCategoryStruct (FrobeniusModuleCat σ) where
  tensorObj := tensorObj
  whiskerLeft M _ _ g := tensorHom (𝟙 M) g
  whiskerRight f N := tensorHom f (𝟙 N)
  tensorHom := tensorHom
  tensorUnit := tensorUnit σ
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

@[simp] theorem tensor_carrier (M N : FrobeniusModuleCat σ) :
    (M ⊗ N).carrier = M.carrier ⊗ N.carrier := (rfl)

@[simp] theorem tensorUnit_carrier : (𝟙_ (FrobeniusModuleCat σ)).carrier = 𝟙_ (ModuleCat S) :=
  (rfl)

/-- The linearization of a tensor product: `S ⊗_{S,σ} (M ⊗ N) → (S ⊗_{S,σ} M) ⊗ (S ⊗_{S,σ} N)`
followed by the tensor product of the linearizations. -/
theorem tensor_linearization_hom (M N : FrobeniusModuleCat σ) :
    (M ⊗ N).linearization.hom =
      δ (ModuleCat.extendScalars σ) M.carrier N.carrier ≫
        (M.linearization.hom ⊗ₘ N.linearization.hom) := (rfl)

/-- The linearization of the unit is the counit `S ⊗_{S,σ} S → S`, `s ⊗ a ↦ s * σ a`, of the
monoidal functor `ModuleCat.extendScalars σ`. -/
theorem tensorUnit_linearization_hom :
    (𝟙_ (FrobeniusModuleCat σ)).linearization.hom = η (ModuleCat.extendScalars σ) := (rfl)

@[simp] theorem tensorHom_hom_f {M M' N N' : FrobeniusModuleCat σ} (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g).hom.f = f.hom.f ⊗ₘ g.hom.f := (rfl)

@[simp] theorem whiskerLeft_hom_f (M : FrobeniusModuleCat σ) {N N' : FrobeniusModuleCat σ}
    (g : N ⟶ N') : (M ◁ g).hom.f = M.carrier ◁ g.hom.f :=
  id_tensorHom _ _

@[simp] theorem whiskerRight_hom_f {M M' : FrobeniusModuleCat σ} (f : M ⟶ M')
    (N : FrobeniusModuleCat σ) : (f ▷ N).hom.f = f.hom.f ▷ N.carrier :=
  tensorHom_id _ _

@[simp] theorem associator_hom_hom_f (M N P : FrobeniusModuleCat σ) :
    (α_ M N P).hom.hom.f = (α_ M.carrier N.carrier P.carrier).hom := (rfl)

@[simp] theorem associator_inv_hom_f (M N P : FrobeniusModuleCat σ) :
    (α_ M N P).inv.hom.f = (α_ M.carrier N.carrier P.carrier).inv := (rfl)

@[simp] theorem leftUnitor_hom_hom_f (M : FrobeniusModuleCat σ) :
    (λ_ M).hom.hom.f = (λ_ M.carrier).hom := (rfl)

@[simp] theorem leftUnitor_inv_hom_f (M : FrobeniusModuleCat σ) :
    (λ_ M).inv.hom.f = (λ_ M.carrier).inv := (rfl)

@[simp] theorem rightUnitor_hom_hom_f (M : FrobeniusModuleCat σ) :
    (ρ_ M).hom.hom.f = (ρ_ M.carrier).hom := (rfl)

@[simp] theorem rightUnitor_inv_hom_f (M : FrobeniusModuleCat σ) :
    (ρ_ M).inv.hom.f = (ρ_ M.carrier).inv := (rfl)

variable (σ) in
/-- The forgetful functor to modules preserves the tensor product, unit and structure
isomorphisms on the nose. -/
noncomputable def forgetInducingFunctorData : Monoidal.InducingFunctorData (forget σ) :=
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _
      -- The identity comparison isomorphisms are typed only up to unfolding `forget`, so `simp`
      -- cannot remove them; on pure tensors both sides reduce to the same element.
      associator_eq _ _ _ := ModuleCat.MonoidalCategory.tensor_ext₃' fun _ _ _ ↦ by
        simp only [forget_map, associator_hom_hom_f]; rfl
      leftUnitor_eq _ := ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ by
        simp only [forget_map, leftUnitor_hom_hom_f]; rfl
      rightUnitor_eq _ := ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ by
        simp only [forget_map, rightUnitor_hom_hom_f]; rfl }

/-- Linearized Frobenius modules form a monoidal category, with the tensor product, unit and
structure isomorphisms of the underlying modules. -/
noncomputable instance : MonoidalCategory (FrobeniusModuleCat σ) :=
  Monoidal.induced (forget σ) (forgetInducingFunctorData σ)

/-- The forgetful functor from linearized Frobenius modules to modules is monoidal. -/
noncomputable instance : (forget σ).Monoidal :=
  Monoidal.fromInducedMonoidal (forget σ) (forgetInducingFunctorData σ)

@[simp] theorem forget_ε : Functor.LaxMonoidal.ε (forget σ) = 𝟙 (𝟙_ (ModuleCat.{u} S)) := (rfl)

@[simp] theorem forget_η : η (forget σ) = 𝟙 (𝟙_ (ModuleCat.{u} S)) := (rfl)

@[simp] theorem forget_μ (M N : FrobeniusModuleCat σ) :
    Functor.LaxMonoidal.μ (forget σ) M N = 𝟙 (M.carrier ⊗ N.carrier) := (rfl)

@[simp] theorem forget_δ (M N : FrobeniusModuleCat σ) :
    δ (forget σ) M N = 𝟙 (M.carrier ⊗ N.carrier) := (rfl)

/-- The Frobenius of a tensor product is the tensor product of the Frobenii. -/
@[simp]
theorem tensor_frobenius_tmul (M N : FrobeniusModuleCat σ) (m : M.carrier) (n : N.carrier) :
    (M ⊗ N).frobenius (m ⊗ₜ n) = M.frobenius m ⊗ₜ N.frobenius n := by
  -- By `tensor_linearization_hom`, `(M ⊗ N).frobenius (m ⊗ n)` is by definition
  -- `(L_M ⊗ L_N) (δ (1 ⊗ (m ⊗ n)))`, and `δ (1 ⊗ (m ⊗ n)) = (1 ⊗ m) ⊗ (1 ⊗ n)`
  -- (`ModuleCat.extendScalars_δ_tmul`). Neither can be rewritten with: the carrier of `M ⊗ N` is
  -- `M.carrier ⊗ N.carrier` only after unfolding the induced monoidal structure, and the lemma is
  -- stated with the change-of-rings tensor product.
  rw [frobenius_apply M, frobenius_apply N]
  exact (frobenius_apply (M ⊗ N) (m ⊗ₜ n)).trans
    (congrArg (M.linearization.hom ⊗ₘ N.linearization.hom)
      (ModuleCat.extendScalars_δ_tmul σ M.carrier N.carrier m n))

/-- The Frobenius of the unit linearized Frobenius module `S` is `σ`. -/
@[simp]
theorem tensorUnit_frobenius_apply (r : S) :
    (𝟙_ (FrobeniusModuleCat σ)).frobenius r = σ r :=
  -- The Frobenius of the unit sends `r` to `η (1 ⊗ r)` (`tensorUnit_linearization_hom`), and
  -- `η` is the multiplication `S ⊗_{S,σ} S → S` (`ModuleCat.extendScalars_η`). Mathlib's
  -- `ModuleCat.restrictScalars_η` computes the adjoint of `η`, the unit `S → S` of restriction
  -- of scalars, as `r ↦ σ r`: that adjoint is by definition `r ↦ η (1 ⊗ r)`, our left side.
  (frobenius_apply (𝟙_ (FrobeniusModuleCat σ)) r).trans (ModuleCat.restrictScalars_η σ r)

end Monoidal

end FrobeniusModuleCat

end TauCeti
