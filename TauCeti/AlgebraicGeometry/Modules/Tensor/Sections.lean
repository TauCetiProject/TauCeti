/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Tensoring sections of `𝒪_X`-modules with a section

Let `F` be an `𝒪_X`-module and `L` an `𝒪_X`-module with a section `e` over an open `U`. Tensoring
with `e` is the `Γ(X, U)`-linear map `Γ(F, U) → Γ(F ⊗ L, U)`, `t ↦ t ⊗ e`
(`Scheme.Modules.tmulRight`), and the tensor powers `eⁿ ∈ Γ(Lⁿ, U)` of `e`
(`Scheme.Modules.tensorPowSection`, with `Lⁿ = TauCeti.tensorPow L n`) give the maps
`t ↦ t ⊗ eⁿ` into `Γ(F ⊗ Lⁿ, U)`. If `e` is a basis of `L` over `U`, that is, on every open
`W ≤ U` every section of `L` is a unique regular multiple of the restriction of `e`, then these
maps are bijective: over `U`, tensoring with `L` does not change the sections.

These maps describe the sections of twists of a module by powers of a line bundle; see
`TauCeti/AlgebraicGeometry/LineBundle/TwistedSections.lean` for their use over the nonvanishing
locus of a section of an invertible sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tmulRight`: the linear map `t ↦ t ⊗ e` on sections.
* `AlgebraicGeometry.Scheme.Modules.tensorPowSection`: the tensor powers `eⁿ ∈ Γ(Lⁿ, U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.bijective_tmulRight` and
  `AlgebraicGeometry.Scheme.Modules.bijective_tmulRight_tensorPowSection`: `t ↦ t ⊗ eⁿ` is bijective
  when `e` is a basis of `L` over `U`.
* `AlgebraicGeometry.Scheme.Modules.bijective_smul_tensorPowSection`: if `e` is a basis of `L`
  over `U`, then `eⁿ` is a basis of `Lⁿ` over `U`.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace TauCeti

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} (F : X.Modules) {L : X.Modules}

/-! ### Tensoring sections with a section of `L` -/

/-- Tensoring with a section `e` of `L` over `U`: the `Γ(X, U)`-linear map
`Γ(F, U) → Γ(F ⊗ L, U)`, `t ↦ t ⊗ e`, through the tensor map of sections
`Γ(F, U) ⊗ Γ(L, U) → Γ(F ⊗ L, U)` of `Scheme.Modules.sectionsFunctor`. -/
def tmulRight {U : X.Opens} (e : Γ(L, U)) : Γ(F, U) →ₗ[Γ(X, U)] Γ(F ⊗ L, U) :=
  (Functor.LaxMonoidal.μ (sectionsFunctor U) F L).hom ∘ₗ
    (TensorProduct.mk Γ(X, U) Γ(F, U) Γ(L, U)).flip e

/-- `tmulRight F e t` is the image of `t ⊗ e` under the tensor map of sections. -/
theorem tmulRight_apply {U : X.Opens} (e : Γ(L, U)) (t : Γ(F, U)) :
    tmulRight F e t = Functor.LaxMonoidal.μ (sectionsFunctor U) F L (t ⊗ₜ e) :=
  (rfl)

/-- Tensoring with `e` is linear in `e`. -/
@[simp]
theorem tmulRight_smul {U : X.Opens} (r : Γ(X, U)) (e : Γ(L, U)) (t : Γ(F, U)) :
    tmulRight F (r • e) t = r • tmulRight F e t := by
  rw [tmulRight, LinearMap.map_smul]
  exact (Functor.LaxMonoidal.μ (sectionsFunctor U) F L).hom.map_smul r _

/-- Tensoring with `e` is additive in `e`. -/
theorem tmulRight_add {U : X.Opens} (e₁ e₂ : Γ(L, U)) (t : Γ(F, U)) :
    tmulRight F (e₁ + e₂) t = tmulRight F e₁ t + tmulRight F e₂ t := by
  rw [tmulRight_apply, tmulRight_apply, tmulRight_apply]
  exact (congrArg _ (TensorProduct.tmul_add t e₁ e₂)).trans (map_add _ _ _)

/-- Tensoring with the zero section gives zero. -/
@[simp]
theorem tmulRight_zero {U : X.Opens} (t : Γ(F, U)) :
    tmulRight F (0 : Γ(L, U)) t = 0 := by
  rw [tmulRight_apply]
  exact (congrArg _ (TensorProduct.tmul_zero _ t)).trans (map_zero _)

/-- Tensoring with `e` commutes with restriction. -/
theorem map_tmulRight {U W : X.Opens} (i : W ⟶ U) (e : Γ(L, U)) (t : Γ(F, U)) :
    (F ⊗ L).presheaf.map i.op (tmulRight F e t) =
      tmulRight F (L.presheaf.map i.op e) (F.presheaf.map i.op t) := by
  let G : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf := SheafOfModules.forget _
  let _ : G.LaxMonoidal := TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The tensor map of sections is the component of the tensor map of the underlying presheaves,
  -- and restriction in the presheaf tensor product acts factorwise on pure tensors.
  exact (PresheafOfModulesOfCommRing.naturality_apply (Functor.LaxMonoidal.μ G F L) i.op
    (t ⊗ₜ e)).symm

/-- A morphism `g : L ⟶ L'` acts on `t ⊗ e` through `e`: `(F ◁ g) (t ⊗ e) = t ⊗ g e`. -/
theorem whiskerLeft_app_tmulRight {L' : X.Modules} (g : L ⟶ L') {U : X.Opens} (e : Γ(L, U))
    (t : Γ(F, U)) : (F ◁ g).app U (tmulRight F e t) = tmulRight F (g.app U e) t := by
  have h := congrArg (fun φ ↦ φ.hom (t ⊗ₜ e))
    (Functor.LaxMonoidal.μ_natural_right (sectionsFunctor U) F g)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- The right unitor `F ⊗ 𝒪_X ≅ F` sends `t ⊗ r` to `r • t`. -/
theorem rightUnitor_hom_app_tmulRight {U : X.Opens} (r : Γ(X, U)) (t : Γ(F, U)) :
    (ρ_ F).hom.app U (tmulRight F (L := 𝟙_ X.Modules) r t) = r • t := by
  have h := congrArg (fun φ ↦ φ.hom (t ⊗ₜ r))
    (Functor.LaxMonoidal.right_unitality (sectionsFunctor U) F)
  simp only [sectionsFunctor_ε, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- The inverse right unitor `F ≅ F ⊗ 𝒪_X` sends `t` to `t ⊗ 1`. -/
theorem rightUnitor_inv_app_eq_tmulRight {U : X.Opens} (t : Γ(F, U)) :
    (ρ_ F).inv.app U t = tmulRight F (L := 𝟙_ X.Modules) (1 : Γ(X, U)) t := by
  have h := rightUnitor_hom_app_tmulRight F (1 : Γ(X, U)) t
  rw [one_smul] at h
  conv_lhs => rw [← h]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
  -- The identity of `Γ(F, U)` in `AddCommGrpCat` acts as the identity function.
  rfl

/-- Restriction to an open subscheme commutes with tensoring sections: the tensor map
`F|_Y ⊗ L|_Y ⟶ (F ⊗ L)|_Y` of the restriction along an open immersion `j : Y ⟶ X` sends `t ⊗ e`
to `t ⊗ e`. -/
theorem restrictFunctor_μ_app_tmulRight {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {W : Y.Opens} (e : Γ(L.restrict j, W)) (t : Γ(F.restrict j, W)) :
    (Functor.LaxMonoidal.μ (restrictFunctor j) F L).app W (tmulRight (F.restrict j) e t) =
      tmulRight F (L := L) (U := j ''ᵁ W) e t :=
  TauCeti.SheafOfModules.pushforward_μ_app_tmul (restrictRingCatSheafHom j) F L (op W) t e

/-! ### Bijectivity over a basis section -/

/-- If a global section `s` is a basis of `L` on every open, then tensoring with `s` is bijective
on the sections over every open. -/
private theorem bijective_tmulRight_map_of_forall_bijective (s : Γ(L, ⊤))
    (hs : ∀ W : X.Opens, Function.Bijective fun r : Γ(X, W) ↦ r • L.presheaf.map W.leTop.op s)
    (W : X.Opens) : Function.Bijective (tmulRight F (L.presheaf.map W.leTop.op s)) := by
  let σ : 𝟙_ X.Modules ⟶ L := L.unitHomEquiv.symm (L.sectionsEquivTop.symm s)
  have : IsIso σ :=
    TauCeti.SheafOfModules.isIso_unitHomEquiv_symm (L.sectionsEquivTop.symm s) fun W ↦ by
      rw [PresheafOfModules.sections.eval, sectionsEquivTop_symm_val]
      exact hs W.unop
  -- The isomorphism `F ≅ F ⊗ 𝒪_X ≅ F ⊗ L` acts on sections as `t ↦ t ⊗ s`.
  let φ : F ⟶ F ⊗ L := (ρ_ F).inv ≫ F ◁ σ
  have hφ (t : Γ(F, W)) : φ.app W t = tmulRight F (L.presheaf.map W.leTop.op s) t := by
    simp only [φ, Hom.comp_app, ConcreteCategory.comp_apply, rightUnitor_inv_app_eq_tmulRight]
    refine (whiskerLeft_app_tmulRight F σ _ t).trans ?_
    have h1 : σ.app W (1 : Γ(X, W)) = L.presheaf.map W.leTop.op s := by
      have := TauCeti.SheafOfModules.unitHomEquiv_symm_val_app (L.sectionsEquivTop.symm s) (op W)
        (1 : Γ(X, W))
      rw [PresheafOfModules.sections.eval, sectionsEquivTop_symm_val] at this
      exact this.trans (one_smul (X.ringCatSheaf.obj.obj (op W)) _)
    rw [h1]
  have hb := ConcreteCategory.bijective_of_isIso (φ.app W)
  convert hb using 1
  ext t
  exact (hφ t).symm

/-- **Tensoring with a basis section is bijective.** If `e` is a basis of `L` over `U`, that is,
on every open `W ≤ U` every section of `L` is a unique regular multiple of the restriction of
`e`, then `t ↦ t ⊗ e` is a bijection `Γ(F, U) → Γ(F ⊗ L, U)`. -/
theorem bijective_tmulRight {U : X.Opens} (e : Γ(L, U))
    (he : ∀ (W : X.Opens) (i : W ⟶ U),
      Function.Bijective fun r : Γ(X, W) ↦ r • L.presheaf.map i.op e) :
    Function.Bijective (tmulRight F e) := by
  -- Restrict to the open subscheme `U`, on which `e` becomes a global basis section.
  let j := U.ι
  let s : Γ(L.restrict j, ⊤) := L.presheaf.map (homOfLE (U.ι_image_le ⊤)).op e
  have hmap (W : U.toScheme.Opens) : (L.restrict j).presheaf.map W.leTop.op s =
      L.presheaf.map (homOfLE (U.ι_image_le W)).op e :=
    (ConcreteCategory.congr_hom
      (L.presheaf.map_comp (homOfLE (U.ι_image_le ⊤)).op (j.opensFunctor.map W.leTop).op) e).symm
  have hs (W : U.toScheme.Opens) : Function.Bijective fun r : Γ(U.toScheme, W) ↦
      r • (L.restrict j).presheaf.map W.leTop.op s := by
    -- Scalars act on the sections of `L|_U` through `Γ(U, W) ≅ Γ(X, j ''ᵁ W)`.
    have hfun : (fun r : Γ(U.toScheme, W) ↦ r • (L.restrict j).presheaf.map W.leTop.op s) =
        (fun r ↦ r • L.presheaf.map (homOfLE (U.ι_image_le W)).op e) ∘ (j.appIso W).inv := by
      funext r
      rw [hmap]
      rfl
    rw [hfun]
    exact (he _ _).comp (ConcreteCategory.bijective_of_isIso _)
  have key (W : U.toScheme.Opens) :
      Function.Bijective (tmulRight F (L.presheaf.map (homOfLE (U.ι_image_le W)).op e)) := by
    have hfun : (tmulRight F (L.presheaf.map (homOfLE (U.ι_image_le W)).op e) :
        Γ(F, j ''ᵁ W) → Γ(F ⊗ L, j ''ᵁ W)) =
          (Functor.LaxMonoidal.μ (restrictFunctor j) F L).app W ∘
            tmulRight (F.restrict j) ((L.restrict j).presheaf.map W.leTop.op s) := by
      funext t
      exact (congrArg (fun a ↦ tmulRight F (U := j ''ᵁ W) a t) (hmap W)).symm.trans
        (restrictFunctor_μ_app_tmulRight F j _ t).symm
    rw [hfun]
    exact (ConcreteCategory.bijective_of_isIso _).comp
      (bijective_tmulRight_map_of_forall_bijective (F.restrict j) s hs W)
  -- Every open `W ≤ U` is the image of an open of the subscheme `U`.
  suffices H : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective (tmulRight F (L.presheaf.map (homOfLE hW).op e)) by
    simpa using H U le_rfl
  intro W hW
  obtain ⟨W', rfl⟩ : ∃ W' : U.toScheme.Opens, j ''ᵁ W' = W :=
    ⟨j ⁻¹ᵁ W, by
      rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.mpr hW]⟩
  exact key W'

/-! ### Tensor powers of a section -/

/-- The tensor powers `eⁿ ∈ Γ(Lⁿ, U)` of a section `e` of `L` over `U`, for the tensor powers
`Lⁿ = TauCeti.tensorPow L n` nested to the right: `e⁰ = 1` and `eⁿ⁺¹ = e ⊗ eⁿ`. -/
def tensorPowSection {U : X.Opens} (e : Γ(L, U)) : (n : ℕ) → Γ(tensorPow L n, U)
  | 0 => (1 : Γ(X, U))
  | n + 1 => tmulRight L (tensorPowSection e n) e

/-- The zeroth tensor power of a section is the unit section `1` of `𝒪_X`. -/
@[simp]
theorem tensorPowSection_zero {U : X.Opens} (e : Γ(L, U)) :
    tensorPowSection e 0 = (1 : Γ(X, U)) :=
  (rfl)

/-- The tensor power `eⁿ⁺¹` is `e ⊗ eⁿ`. -/
theorem tensorPowSection_succ {U : X.Opens} (e : Γ(L, U)) (n : ℕ) :
    tensorPowSection e (n + 1) = tmulRight L (tensorPowSection e n) e :=
  (rfl)

/-- The tensor powers of `r • e` are `(r • e)ⁿ = rⁿ • eⁿ`. -/
theorem tensorPowSection_smul {U : X.Opens} (r : Γ(X, U)) (e : Γ(L, U)) (n : ℕ) :
    tensorPowSection (r • e) n = r ^ n • tensorPowSection e n := by
  induction n with
  | zero => rw [pow_zero, one_smul, tensorPowSection_zero, tensorPowSection_zero]
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ih, tmulRight_smul, LinearMap.map_smul,
      smul_smul, pow_succ]

/-- Tensor powers of sections commute with restriction. -/
theorem map_tensorPowSection {U W : X.Opens} (i : W ⟶ U) (e : Γ(L, U)) (n : ℕ) :
    (tensorPow L n).presheaf.map i.op (tensorPowSection e n) =
      tensorPowSection (L.presheaf.map i.op e) n := by
  induction n with
  -- The restriction maps of the unit `𝒪_X` are those of the structure sheaf, which preserve `1`.
  | zero => exact map_one (X.presheaf.map i.op).hom
  | succ n ih => rw [tensorPowSection_succ, map_tmulRight, ih, tensorPowSection_succ]

/-- Tensoring with `eⁿ` commutes with restriction. -/
theorem map_tmulRight_tensorPowSection {U W : X.Opens} (i : W ⟶ U) (e : Γ(L, U)) (n : ℕ)
    (t : Γ(F, U)) :
    (F ⊗ tensorPow L n).presheaf.map i.op (tmulRight F (tensorPowSection e n) t) =
      tmulRight F (tensorPowSection (L.presheaf.map i.op e) n) (F.presheaf.map i.op t) := by
  rw [map_tmulRight, map_tensorPowSection]

/-- Tensoring with `(r • e)ⁿ` is tensoring with `eⁿ` after multiplication by `rⁿ`. -/
theorem tmulRight_tensorPowSection_smul {U : X.Opens} (r : Γ(X, U)) (e : Γ(L, U)) (n : ℕ)
    (t : Γ(F, U)) :
    tmulRight F (tensorPowSection (r • e) n) t =
      tmulRight F (tensorPowSection e n) (r ^ n • t) := by
  rw [tensorPowSection_smul, tmulRight_smul, LinearMap.map_smul]

/-- If `e` is a basis of `L` over `U`, then `eⁿ` is a basis of `Lⁿ` over `U`. -/
theorem bijective_smul_tensorPowSection {U : X.Opens} (e : Γ(L, U))
    (he : ∀ (W : X.Opens) (i : W ⟶ U),
      Function.Bijective fun r : Γ(X, W) ↦ r • L.presheaf.map i.op e) (n : ℕ)
    (W : X.Opens) (i : W ⟶ U) :
    Function.Bijective fun r : Γ(X, W) ↦ r • (tensorPow L n).presheaf.map i.op
      (tensorPowSection e n) := by
  induction n generalizing W with
  | zero =>
    have hfun : (fun r : Γ(X, W) ↦ r • (tensorPow L 0).presheaf.map i.op
        (tensorPowSection e 0)) = id := by
      funext r
      -- On sections of the unit `𝒪_X`, the scalar action is multiplication of functions.
      exact (congrArg (r • ·) (map_one (X.presheaf.map i.op).hom)).trans (mul_one r)
    rw [hfun]
    exact Function.bijective_id
  | succ n ih =>
    -- `r • (e ⊗ eⁿ) = (r • e) ⊗ eⁿ`, a composite of two bijections.
    have hfun : (fun r : Γ(X, W) ↦ r • (tensorPow L (n + 1)).presheaf.map i.op
        (tensorPowSection e (n + 1))) =
          tmulRight L ((tensorPow L n).presheaf.map i.op (tensorPowSection e n)) ∘
            fun r ↦ r • L.presheaf.map i.op e := by
      funext r
      rw [Function.comp_apply, tensorPowSection_succ, map_tmulRight]
      exact (LinearMap.map_smul _ r _).symm
    rw [hfun]
    refine (bijective_tmulRight L _ fun W' j ↦ ?_).comp (he W i)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact ih W' (j ≫ i)

/-- **Tensoring with a power of a basis section is bijective.** If `e` is a basis of `L` over
`U`, then `t ↦ t ⊗ eⁿ` is a bijection `Γ(F, U) → Γ(F ⊗ Lⁿ, U)` for every `n`. -/
theorem bijective_tmulRight_tensorPowSection {U : X.Opens} (e : Γ(L, U))
    (he : ∀ (W : X.Opens) (i : W ⟶ U),
      Function.Bijective fun r : Γ(X, W) ↦ r • L.presheaf.map i.op e) (n : ℕ) :
    Function.Bijective (tmulRight F (tensorPowSection e n)) :=
  bijective_tmulRight F _ (bijective_smul_tensorPowSection e he n)

end

end AlgebraicGeometry.Scheme.Modules
