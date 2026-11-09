/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.Algebra.Group.Action.Pow
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Sections of a module twisted by powers of a line bundle

Let `F` be an `𝒪_X`-module and `L` an `𝒪_X`-module with a section `e` over an open `U`. Tensoring
with `e` is the `Γ(X, U)`-linear map `Γ(F, U) → Γ(F ⊗ L, U)`, `t ↦ t ⊗ e`
(`Scheme.Modules.tmulRight`), and the tensor powers `eⁿ ∈ Γ(Lⁿ, U)` of `e`
(`Scheme.Modules.tensorPowSection`, with `Lⁿ = TauCeti.tensorPow L n`) give the maps
`t ↦ t ⊗ eⁿ` into `Γ(F ⊗ Lⁿ, U)`. If `e` is a basis of `L` over `U`, for instance if `L` is an
invertible sheaf and `U` lies in the nonvanishing locus of `e`, then these maps are bijective:
over `U`, tensoring with `L` does not change the sections.

For a quasi-coherent `F` and an invertible `L`, this describes the sections of `F` over the
nonvanishing locus `X_s` of a section `s` of `L` over a quasi-compact quasi-separated open `U`
(Hartshorne, Lemma II.5.14; Stacks, Tag 01PW):

* a section `t` of `F` over `U` that vanishes on `X_s` satisfies `t ⊗ sⁿ = 0` for some `n`;
* for every section `t` of `F` over `X_s`, some `t ⊗ sⁿ` extends to a section of `F ⊗ Lⁿ` over
  `U`.

Together with the bijectivity of `t ↦ t ⊗ sⁿ` over `X_s`, these two statements express that
`Γ(X_s, F)` is the colimit of the modules `Γ(U, F ⊗ Lⁿ)` along `t ↦ t ⊗ s`; the colimit itself is
not constructed here. For the structure sheaf in place of `L` this is the localization
`Γ(X_f, F) = Γ(U, F)_f`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`). It is the step
in the proof of Serre's theorem that a coherent sheaf becomes globally generated after twisting by
a high power of an ample line bundle: on projective space, sections of `F` over the standard opens
`D₊(xᵢ)` extend to global sections of the twists `F(n)` after multiplication by `xᵢⁿ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tmulRight`: the linear map `t ↦ t ⊗ e` on sections.
* `AlgebraicGeometry.Scheme.Modules.tensorPowSection`: the tensor powers `eⁿ ∈ Γ(Lⁿ, U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.bijective_tmulRight` and
  `AlgebraicGeometry.Scheme.Modules.bijective_tmulRight_tensorPowSection`: `t ↦ t ⊗ eⁿ` is bijective
  when `e` is a basis of `L` over `U`.
* `AlgebraicGeometry.Scheme.Modules.bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus`:
  for an invertible sheaf `L`, `t ↦ t ⊗ eⁿ` is bijective over the nonvanishing locus of `e`.
* `AlgebraicGeometry.Scheme.Modules.exists_tmulRight_tensorPowSection_eq_zero`: a section over a
  quasi-compact open vanishing on `X_s` is killed by tensoring with a power of `s`.
* `AlgebraicGeometry.Scheme.Modules.exists_map_eq_tmulRight_tensorPowSection`: on a quasi-compact
  quasi-separated open, `t ⊗ sⁿ` extends from `X_s` for every section `t` over `X_s` and large `n`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Lemma II.5.14.
* [The Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW).
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

/-! ### Sections over the nonvanishing locus of a section of a line bundle -/

variable [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]

/-- For an invertible sheaf `L` and a section `e` of `L` over `U` that vanishes nowhere on `U`,
tensoring with `eⁿ` is a bijection `Γ(F, U) → Γ(F ⊗ Lⁿ, U)` for every `n`. -/
theorem bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus {U : X.Opens}
    (e : Γ(L, U)) (h : U ≤ L.nonvanishingLocus e) (n : ℕ) :
    Function.Bijective (tmulRight F (tensorPowSection e n)) :=
  bijective_tmulRight_tensorPowSection F e (fun W i ↦ by
    simpa only [Category.comp_id] using (le_nonvanishingLocus_iff e (𝟙 U)).mp h W i) n

/-- A quasi-compact open `U` is covered by finitely many affine opens `V i ≤ U`, each carrying a
section `e i` of `L` that vanishes nowhere on `V i`. -/
private theorem exists_finite_affine_cover_le_nonvanishingLocus {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens) (e : ∀ i, Γ(L, V i)),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ U) ∧ (∀ i, V i ≤ L.nonvanishingLocus (e i)) ∧
        U ≤ ⨆ i, V i := by
  -- Near each point of `U`, take an affine open inside `U` and inside a trivializing open.
  have H (x : U) : ∃ (A : X.Opens) (e : Γ(L, A)), IsAffineOpen A ∧ (x : X) ∈ A ∧ A ≤ U ∧
      A ≤ L.nonvanishingLocus e := by
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization L x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show (x : X) ∈ ((U ⊓ V : X.Opens) : Set X) from ⟨x.2, hxV⟩) (U ⊓ V).isOpen
    have hAV : A ≤ V := fun y hy ↦ (hAUV hy).2
    refine ⟨A, L.presheaf.map (homOfLE hAV).op (trivializationGenerator L t), hA, hxA,
      fun y hy ↦ (hAUV hy).1, ?_⟩
    rw [nonvanishingLocus_map, nonvanishingLocus_trivializationGenerator]
    exact le_inf le_rfl hAV
  choose A e hA hxA hAU hAe using H
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (A x : Set X)) (fun x ↦ (A x).isOpen)
    fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  refine ⟨t, inferInstance, fun i ↦ A i, fun i ↦ e i, fun i ↦ hA i, fun i ↦ hAU i,
    fun i ↦ hAe i, fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- If `e` vanishes nowhere on `V ≤ U` and `s|_V = f • e`, then `X_s ∩ V` is the basic open set
of `f`. -/
private theorem basicOpen_eq_inf_nonvanishingLocus {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U))
    {e : Γ(L, V)} (he : V ≤ L.nonvanishingLocus e) {f : Γ(X, V)}
    (hf : f • e = L.presheaf.map i.op s) : X.basicOpen f = V ⊓ L.nonvanishingLocus s := by
  rw [← inf_eq_left.mpr ((X.basicOpen_le f).trans he), ← nonvanishingLocus_smul, hf,
    nonvanishingLocus_map]

/-- **Sections vanishing on the nonvanishing locus are killed by a power of the section**
(Hartshorne, Lemma II.5.14(a)). Let `F` be quasi-coherent and `L` invertible, let `s` be a section
of `L` over a quasi-compact open `U`, and let `t` be a section of `F` over `U` that vanishes on the
nonvanishing locus `X_s`. Then `t ⊗ sⁿ = 0` in `Γ(F ⊗ Lⁿ, U)` for some `n`. -/
theorem exists_tmulRight_tensorPowSection_eq_zero [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (s : Γ(L, U)) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t = 0) :
    ∃ n : ℕ, tmulRight F (tensorPowSection s n) t = 0 := by
  obtain ⟨ι, _, V, e, hVa, hVU, hVe, hUV⟩ :=
    exists_finite_affine_cover_le_nonvanishingLocus (L := L) hU
  cases nonempty_fintype ι
  -- On each `V i`, write `s = f i • e i`; then `X_s ∩ V i` is the basic open set of `f i`.
  choose f hf using fun i ↦
    surjective_smul_of_le_nonvanishingLocus (hVe i) (L.presheaf.map (homOfLE (hVU i)).op s)
  beta_reduce at hf
  have hD (i : ι) : X.basicOpen (f i) ≤ L.nonvanishingLocus s :=
    (basicOpen_eq_inf_nonvanishingLocus _ s (hVe i) (hf i)).le.trans inf_le_right
  -- So the restriction of `t` to `V i` is killed by a power of `f i`.
  have H (i : ι) : ∃ n : ℕ, f i ^ n • F.presheaf.map (homOfLE (hVU i)).op t = 0 := by
    refine F.exists_pow_smul_eq_zero_of_isCompact (hVa i).isCompact _ _ ?_
    rw [basicOpenRestrict_apply]
    simpa only [map_zero, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using
      congrArg (F.presheaf.map (homOfLE (hD i)).op) ht
  choose n hn using H
  refine ⟨Finset.univ.sup n, TopCat.Sheaf.eq_of_locally_eq'
    (⟨(F ⊗ tensorPow L _).presheaf, (F ⊗ tensorPow L _).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    V U (fun i ↦ homOfLE (hVU i)) hUV _ _ fun i ↦ ?_⟩
  -- The restriction maps of this sheaf are those of `F ⊗ Lⁿ`.
  change (F ⊗ tensorPow L _).presheaf.map _ _ = (F ⊗ tensorPow L _).presheaf.map _ _
  rw [map_zero, map_tmulRight_tensorPowSection, ← hf i, tmulRight_tensorPowSection_smul,
    pow_smul_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i), map_zero]

/-- On finitely many affine opens `V i`, a section `t` over an open containing the basic open sets
of functions `f i` on `V i` extends to each `V i` after multiplication by a common power of the
`f i`. -/
private theorem exists_pow_smul_eq_map_of_finite [F.IsQuasicoherent] {ι : Type*} [Finite ι]
    {V : ι → X.Opens} (hV : ∀ i, IsAffineOpen (V i)) (f : ∀ i, Γ(X, V i)) {D : X.Opens}
    (hfD : ∀ i, X.basicOpen (f i) ≤ D) (t : Γ(F, D)) :
    ∃ (N : ℕ) (y : ∀ i, Γ(F, V i)), ∀ i,
      F.presheaf.map (homOfLE (X.basicOpen_le (f i))).op (y i) =
        X.presheaf.map (homOfLE (X.basicOpen_le (f i))).op (f i) ^ N •
          F.presheaf.map (homOfLE (hfD i)).op t := by
  cases nonempty_fintype ι
  choose n y hy using fun i ↦ F.exists_pow_smul_eq_map (hV i) (f i) rfl (X.basicOpen_le (f i))
    (F.presheaf.map (homOfLE (hfD i)).op t)
  refine ⟨Finset.univ.sup n, fun i ↦ f i ^ (Finset.univ.sup n - n i) • y i, fun i ↦ ?_⟩
  simp only [F.map_smul, map_pow]
  rw [← hy i, smul_smul, pow_sub_mul_pow _ (Finset.le_sup (f := n) (Finset.mem_univ i))]

/-- Let `f₁` and `f₂` cut out `D` on `V₁` and `V₂`, with `f₂ = u * f₁` on the quasi-compact
overlap `V₁ ⊓ V₂`, and let `y₁`, `y₂` restrict to `f₁ ^ N • t` and `f₂ ^ N • t` on the basic open
sets of `f₁` and `f₂`. Then `u ^ N • y₁` and `y₂` agree on `V₁ ⊓ V₂` after multiplication by a
power of `f₂`. -/
private theorem exists_pow_smul_sub_eq_zero [F.IsQuasicoherent] {V₁ V₂ D : X.Opens}
    (hW : IsCompact ((V₁ ⊓ V₂ : X.Opens) : Set X)) {f₁ : Γ(X, V₁)} {f₂ : Γ(X, V₂)}
    (hf₁ : X.basicOpen f₁ = V₁ ⊓ D) (hf₂ : X.basicOpen f₂ = V₂ ⊓ D) {u : Γ(X, V₁ ⊓ V₂)}
    (hu : X.presheaf.map (homOfLE inf_le_right).op f₂ =
      u * X.presheaf.map (homOfLE inf_le_left).op f₁)
    {N : ℕ} {t : Γ(F, D)} {y₁ : Γ(F, V₁)} {y₂ : Γ(F, V₂)}
    (hy₁ : F.presheaf.map (homOfLE (X.basicOpen_le f₁)).op y₁ =
      X.presheaf.map (homOfLE (X.basicOpen_le f₁)).op f₁ ^ N •
        F.presheaf.map (homOfLE (hf₁.le.trans inf_le_right)).op t)
    (hy₂ : F.presheaf.map (homOfLE (X.basicOpen_le f₂)).op y₂ =
      X.presheaf.map (homOfLE (X.basicOpen_le f₂)).op f₂ ^ N •
        F.presheaf.map (homOfLE (hf₂.le.trans inf_le_right)).op t) :
    ∃ m : ℕ, X.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op f₂ ^ m •
      (u ^ N • F.presheaf.map (homOfLE inf_le_left).op y₁ -
        F.presheaf.map (homOfLE inf_le_right).op y₂) = 0 := by
  refine F.exists_pow_smul_eq_zero_of_isCompact hW _ _ ?_
  -- Restrict everything to the basic open set `B` of `f₂` in `V₁ ⊓ V₂`, which lies in the basic
  -- open sets of `f₁` and `f₂`.
  have hB := X.basicOpen_res f₂ (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op
  have hB₂ : X.basicOpen (X.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op f₂) ≤
      X.basicOpen f₂ := hB.le.trans inf_le_right
  have hB₁ : X.basicOpen (X.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op f₂) ≤
      X.basicOpen f₁ := by
    rw [hB, hf₁, hf₂]
    exact fun x hx ↦ ⟨hx.1.1, hx.2.2⟩
  have h₁ := congrArg (F.presheaf.map (homOfLE hB₁).op) hy₁
  have h₂ := congrArg (F.presheaf.map (homOfLE hB₂).op) hy₂
  have hu' := congrArg (X.presheaf.map (homOfLE (X.basicOpen_le
    (X.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op f₂))).op) hu
  simp only [F.map_smul, map_pow, map_mul, ← Functor.map_comp_apply, ← op_comp,
    homOfLE_comp] at h₁ h₂ hu'
  rw [basicOpenRestrict_apply, map_sub, F.map_smul, map_pow]
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
  rw [h₁, h₂, smul_smul, ← mul_pow, ← hu', sub_self]

/-- **Sections over the nonvanishing locus extend after tensoring with a power of the section**
(Hartshorne, Lemma II.5.14(b)). Let `F` be quasi-coherent and `L` invertible, and let `s` be a
section of `L` over a quasi-compact quasi-separated open `U`. For every section `t` of `F` over the
nonvanishing locus `X_s`, there are `n` and a section of `F ⊗ Lⁿ` over `U` whose restriction to
`X_s` is `t ⊗ sⁿ`. -/
theorem exists_map_eq_tmulRight_tensorPowSection [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (s : Γ(L, U))
    (t : Γ(F, L.nonvanishingLocus s)) :
    ∃ (n : ℕ) (t' : Γ(F ⊗ tensorPow L n, U)),
      (F ⊗ tensorPow L n).presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t' =
        tmulRight F
          (tensorPowSection (L.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op s) n) t := by
  obtain ⟨ι, _, V, e, hVa, hVU, hVe, hUV⟩ :=
    exists_finite_affine_cover_le_nonvanishingLocus (L := L) hU
  cases nonempty_fintype ι
  -- On each `V i`, write `s = f i • e i`; then `X_s ∩ V i` is the basic open set of `f i`.
  choose f hf using fun i ↦
    surjective_smul_of_le_nonvanishingLocus (hVe i) (L.presheaf.map (homOfLE (hVU i)).op s)
  beta_reduce at hf
  have hDf (i : ι) : X.basicOpen (f i) = V i ⊓ L.nonvanishingLocus s :=
    basicOpen_eq_inf_nonvanishingLocus _ s (hVe i) (hf i)
  have hfD (i : ι) : X.basicOpen (f i) ≤ L.nonvanishingLocus s := (hDf i).le.trans inf_le_right
  -- On each affine `V i`, a common power `f i ^ N • t` extends to a section `y' i` over `V i`.
  obtain ⟨N, y', hy'⟩ := exists_pow_smul_eq_map_of_finite F hVa f hfD t
  -- On an overlap `V i ⊓ V j`, the basis sections differ by a function `u`, `e i = u • e j`, and
  -- then `f j = u * f i`.
  have hW (i j : ι) : V i ⊓ V j ≤ L.nonvanishingLocus
      (L.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (e j)) := by
    rw [nonvanishingLocus_map]
    exact le_inf le_rfl (inf_le_right.trans (hVe j))
  choose u hu using fun p : ι × ι ↦ surjective_smul_of_le_nonvanishingLocus (hW p.1 p.2)
    (L.presheaf.map (homOfLE (inf_le_left : V p.1 ⊓ V p.2 ≤ V p.1)).op (e p.1))
  beta_reduce at hu
  have hs (j : ι) {W : X.Opens} (k : W ⟶ V j) :
      X.presheaf.map k.op (f j) • L.presheaf.map k.op (e j) =
        L.presheaf.map (homOfLE (k.le.trans (hVU j))).op s := by
    rw [← L.map_smul, hf, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  have hfu (p : ι × ι) : X.presheaf.map (homOfLE inf_le_right).op (f p.2) =
      u p * X.presheaf.map (homOfLE inf_le_left).op (f p.1) := by
    apply injective_smul_of_le_nonvanishingLocus (hW p.1 p.2)
    beta_reduce
    rw [hs p.2, mul_comm, mul_smul, hu p, hs p.1]
  -- After transport to `e j`, the extensions `y' i` and `y' j` agree on `V i ⊓ V j ∩ X_s`, so
  -- they agree on `V i ⊓ V j` after multiplication by a power of `f j`.
  have hδ (p : ι × ι) := exists_pow_smul_sub_eq_zero F
    (hU' _ _ (hVU p.1) (V p.1).isOpen (hVa p.1).isCompact (hVU p.2) (V p.2).isOpen
      (hVa p.2).isCompact) (hDf p.1) (hDf p.2) (hfu p) (hy' p.1) (hy' p.2)
  choose m hm using hδ
  let M := Finset.univ.sup m
  let y'' (i : ι) : Γ(F, V i) := f i ^ M • y' i
  -- The sections `y'' i ⊗ (e i)^(N + M)` are compatible, so they glue to a section over `U`.
  let z (i : ι) : Γ(F ⊗ tensorPow L (N + M), V i) :=
    tmulRight F (tensorPowSection (e i) (N + M)) (y'' i)
  have hc : TopCat.Presheaf.IsCompatible (F ⊗ tensorPow L (N + M)).presheaf V z := by
    intro i j
    have h := pow_smul_eq_zero_of_le (Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
      (hm (i, j))
    rw [smul_sub, sub_eq_zero] at h
    -- The inclusions of `V i ⊓ V j` in `V i` and `V j` are `homOfLE`.
    change (F ⊗ tensorPow L (N + M)).presheaf.map (homOfLE inf_le_left).op _ =
      (F ⊗ tensorPow L (N + M)).presheaf.map (homOfLE inf_le_right).op _
    simp only [z, map_tmulRight_tensorPowSection]
    rw [← hu (i, j), tmulRight_tensorPowSection_smul]
    congr 1
    simp only [y'', F.map_smul, map_pow]
    rw [← h, hfu (i, j), smul_smul, smul_smul]
    congr 1
    ring
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(F ⊗ tensorPow L (N + M)).presheaf, (F ⊗ tensorPow L (N + M)).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat X) V U (fun i ↦ homOfLE (hVU i)) hUV z hc
  -- On each `X_s ∩ V i`, both sections restrict to `t ⊗ s^(N + M)`.
  refine ⟨N + M, g, TopCat.Sheaf.eq_of_locally_eq'
    (⟨(F ⊗ tensorPow L (N + M)).presheaf, (F ⊗ tensorPow L (N + M)).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat X) (fun i ↦ X.basicOpen (f i)) _ (fun i ↦ homOfLE (hfD i))
    (fun x hx ↦ ?_) _ _ fun i ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hUV (L.nonvanishingLocus_le s hx))
    exact Opens.mem_iSup.mpr ⟨i, (hDf i).ge ⟨hi, hx⟩⟩
  -- The restriction maps of this sheaf are those of `F ⊗ L^(N + M)`.
  change (F ⊗ tensorPow L (N + M)).presheaf.map _ _ = (F ⊗ tensorPow L (N + M)).presheaf.map _ _
  have hg' := congrArg ((F ⊗ tensorPow L (N + M)).presheaf.map
    (homOfLE (X.basicOpen_le (f i))).op) (hg i)
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hg'
  rw [← Functor.map_comp_apply, ← op_comp, homOfLE_comp, hg', map_tmulRight_tensorPowSection,
    map_tmulRight_tensorPowSection]
  simp only [y'', F.map_smul, map_pow, hy', smul_smul, ← pow_add]
  rw [add_comm M N, ← tmulRight_tensorPowSection_smul, hs i]
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]

end

end AlgebraicGeometry.Scheme.Modules
