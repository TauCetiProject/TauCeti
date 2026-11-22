/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.Functor
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.WeakKernels

/-!
# Finitely presented functors on the projectively stable category

Let `E` be an exact structure, and let `E/𝒫` be the quotient of `C` by the ideal `𝒫` of
projectively trivial morphisms (`TauCeti.ExactStructure.projectivelyTrivialIdeal`). When `E` has
enough relative projectives, `𝒫` consists of the morphisms factoring through a relative
projective, so `E/𝒫` is the projectively stable category. In that case `E/𝒫` has weak kernels,
and the category `mod (E/𝒫)` of finitely presented functors `(E/𝒫)ᵒᵖ ⥤ AddCommGrpCat` is
abelian. It has enough projectives, the representable functors
(`TauCeti.projective_modYoneda_obj`). The functors `Ext¹_E(-, A)` are injective in `mod (E/𝒫)`,
and if `E` also has enough relative injectives, then `mod (E/𝒫)` has enough injectives.

A weak kernel of `g : Y ⟶ Z` is the kernel of the deflation `[c, g] : P ⊞ Y ⟶ Z`, followed by the
projection to `Y`, where `c` is a deflation from a relative projective `P`.

For a conflation `X ⟶ Y ⟶ Z`, its *contravariant defect* is the cokernel of `(-, Y) ⟶ (-, Z)` on
`E/𝒫`. Every finitely presented functor is the contravariant defect of some conflation: a
presentation by `f : Y ⟶ Z` does not change when `f` is replaced by the deflation
`[c, f] : P ⊞ Y ⟶ Z`, since `P` is zero in `E/𝒫`. The connecting morphism
`(-, Z) ⟶ Ext¹_E(-, X)`, `u ↦ u^* [X ⟶ Y ⟶ Z]`, makes `(-, Y) ⟶ (-, Z) ⟶ Ext¹_E(-, X)` exact, so
the contravariant defect embeds into `Ext¹_E(-, X)`. When `Y` is relatively injective, the
connecting morphism is an epimorphism, and the contravariant defect is `Ext¹_E(-, X)`.

Injectivity of `Ext¹_E(-, A)` is proved for the contravariant defect of a conflation
`A ⟶ I ⟶ K` with `I` relatively injective, such as an injective presentation. The key step is
that a morphism `a : Y ⟶ K` whose restriction to `X` factors through `I ⟶ K` modulo `𝒫` is, up
to a morphism factoring through `I ⟶ K`, a morphism factoring through `Y ⟶ Z`.

## Main definitions

* `TauCeti.ExactStructure.EnoughProjectives.abelian`: the abelian structure of `mod (E/𝒫)`.
* `TauCeti.ExactStructure.Extension.contravariantDefect`: the contravariant defect of a
  conflation, as a functor on `E/𝒫`, and `TauCeti.ExactStructure.Extension.modContravariantDefect`,
  the same as an object of `mod (E/𝒫)`.
* `TauCeti.ExactStructure.modExt1`: the functor `Ext¹_E(-, A)` on `E/𝒫`
  (`TauCeti.ExactStructure.stableExt1Functor`), as an object of `mod (E/𝒫)`.
* `TauCeti.ExactStructure.Extension.ext1Connecting`: the connecting morphism
  `(-, Z) ⟶ Ext¹_E(-, X)` of a conflation `X ⟶ Y ⟶ Z`.
* `TauCeti.ExactStructure.Extension.contravariantDefectIsoStableExt1Functor`: the contravariant
  defect of a conflation with relatively injective middle term is `Ext¹_E(-, X)`.

## Main results

* `TauCeti.ExactStructure.EnoughProjectives.hasWeakKernels`: with enough projectives, `E/𝒫` has
  weak kernels.
* `TauCeti.ExactStructure.Extension.isFinitelyPresentedFunctor_contravariantDefect`: contravariant
  defects are finitely presented.
* `TauCeti.ExactStructure.EnoughProjectives.exists_iso_contravariantDefect`: every finitely
  presented functor on `E/𝒫` is a contravariant defect.
* `TauCeti.ExactStructure.Extension.exact_ext1Connecting`: exactness of
  `(-, Y) ⟶ (-, Z) ⟶ Ext¹_E(-, X)`.
* `TauCeti.ExactStructure.isFinitelyPresentedFunctor_stableExt1Functor`: `Ext¹_E(-, A)` is
  finitely presented when `A` has an injective presentation.
* `TauCeti.ExactStructure.Extension.exists_eq_add_of_isInjective`: the key lemma above.
* `TauCeti.ExactStructure.EnoughProjectives.injective_modExt1`: with enough projectives,
  `Ext¹_E(-, A)` is injective in `mod (E/𝒫)`.
* `TauCeti.ExactStructure.EnoughProjectives.enoughInjectives`: with enough projectives and
  enough injectives, `mod (E/𝒫)` has enough injectives.

## Implementation notes

The bifunctor `Ext¹_E(-, -)` of a general exact category, its smallness hypothesis
`TauCeti.ExactStructure.HasSmallExt1`, and the descent of `Ext¹_E(-, A)` to `E/𝒫`
(`TauCeti.ExactStructure.stableExt1Functor`) live in
`TauCeti.CategoryTheory.Exact.YonedaExt.Functor`. The groups `Ext¹_E(W, A)` live in
`Type (max u v)`, while `mod (E/𝒫)` consists of functors to `AddCommGrpCat.{v}`, so this file
assumes `E.HasSmallExt1.{v}`. It holds when `E` has enough injectives
(`TauCeti.ExactStructure.EnoughInjectives.hasSmallExt1`) or enough projectives
(`TauCeti.ExactStructure.EnoughProjectives.hasSmallExt1`).

## References

* Haruhisa Enomoto, *Classifications of exact structures and Cohen–Macaulay-finite algebras*,
  Adv. Math. **335** (2018), 838–877, <https://arxiv.org/abs/1705.02163>, Lemma A.8.
* Osamu Iyama, *Auslander correspondence*, Adv. Math. **210** (2007), 51–82. For the injective
  objects, Enomoto refers to the argument of Theorem 2.2.2(1) there.
* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
-/

public section

universe v u u'

open CategoryTheory Limits Opposite

namespace TauCeti

section Yoneda

variable {D : Type u'} [Category.{v} D] [Preadditive D]

/-- **Extending along a monomorphism through representables.** Let `π : (-, Y₀) ⟶ F` be a
cokernel of `(-, f₀)`, let `α : F' ⟶ F` be a monomorphism from a finitely generated functor, and
`φ : F' ⟶ G`. Suppose `y : Y' ⟶ Y₀` is such that every `z : V ⟶ Y₀` for which `(-, z) ≫ π` factors
through `α` factors through `y`, and that `(-, y) ≫ π = γ ≫ α`. Then any `ψ' : (-, Y₀) ⟶ G` with
`(-, y) ≫ ψ' = γ ≫ φ` descends to a morphism `ψ : F ⟶ G` with `α ≫ ψ = φ`. -/
theorem exists_comp_eq_of_mono_of_isColimit {F' F G : Dᵒᵖ ⥤ AddCommGrpCat.{v}} {X₀ Y₀ Y' : D}
    {f₀ : X₀ ⟶ Y₀} {π : preadditiveYoneda.obj Y₀ ⟶ F} {hπ : preadditiveYoneda.map f₀ ≫ π = 0}
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) (hF' : IsFinitelyGeneratedFunctor F')
    (α : F' ⟶ F) [Mono α] (φ : F' ⟶ G) {y : Y' ⟶ Y₀}
    (hy : ∀ ⦃V : D⦄ (z : V ⟶ Y₀) (u : preadditiveYoneda.obj V ⟶ F'),
      u ≫ α = preadditiveYoneda.map z ≫ π → ∃ z' : V ⟶ Y', z' ≫ y = z)
    (γ : preadditiveYoneda.obj Y' ⟶ F') (hγ : γ ≫ α = preadditiveYoneda.map y ≫ π)
    (ψ' : preadditiveYoneda.obj Y₀ ⟶ G) (hψ' : preadditiveYoneda.map y ≫ ψ' = γ ≫ φ) :
    ∃ ψ : F ⟶ G, α ≫ ψ = φ := by
  have : Epi π := Cofork.IsColimit.epi hc
  -- On the image of `(-, y)`, `γ` is determined by `α`, as `α` is a monomorphism.
  have key : ∀ {V : D} (z' : V ⟶ Y') (u : preadditiveYoneda.obj V ⟶ F'),
      u ≫ α = preadditiveYoneda.map (z' ≫ y) ≫ π → preadditiveYoneda.map z' ≫ γ = u :=
    fun z' u hu ↦ by rw [← cancel_mono α, Category.assoc, hγ, hu, Functor.map_comp,
      Category.assoc]
  obtain ⟨f', rfl⟩ := hy f₀ 0 (by rw [zero_comp, hπ])
  obtain ⟨ψ, hψ⟩ := CokernelCofork.IsColimit.desc' hc ψ' (by
    rw [Functor.map_comp, Category.assoc, hψ', ← Category.assoc,
      key f' 0 (by rw [zero_comp, hπ]), zero_comp])
  rw [Cofork.π_ofπ] at hψ
  refine ⟨ψ, ?_⟩
  obtain ⟨Y'', π', _⟩ := isFinitelyGeneratedFunctor_def.1 hF'
  obtain ⟨z, hz⟩ := exists_preadditiveYoneda_map_comp_eq π (π' ≫ α)
  obtain ⟨z', rfl⟩ := hy z π' hz.symm
  rw [← cancel_epi π', ← Category.assoc, ← hz, Category.assoc, hψ, Functor.map_comp,
    Category.assoc, hψ', ← Category.assoc, key z' π' hz.symm]

end Yoneda

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

/-! ### Weak kernels in the projectively stable category -/

/-- **Weak kernels modulo projectively trivial morphisms.** With enough projectives, every
`g : Y ⟶ Z` admits `w : K ⟶ Y` with `w ≫ g` projectively trivial, through which every `u : W ⟶ Y`
with `u ≫ g` projectively trivial factors, already in `C`. Take for `w` the kernel of the
deflation `[c, g] : P ⊞ Y ⟶ Z`, for a deflation `c` from a relative projective, followed by the
projection to `Y`. -/
theorem EnoughProjectives.exists_weakKernel (h : E.EnoughProjectives) {Y Z : C} (g : Y ⟶ Z) :
    ∃ (K : C) (w : K ⟶ Y), w ≫ g ∈ E.projectivelyTrivialIdeal.hom K Z ∧
      ∀ ⦃W : C⦄ (u : W ⟶ Y), u ≫ g ∈ E.projectivelyTrivialIdeal.hom W Z →
        ∃ l : W ⟶ K, l ≫ w = u := by
  let P := h.projectivePresentation Z
  obtain ⟨K, k, hk, hS⟩ :=
    (E.isDeflation_iff _).1 (E.isDeflation_biprod_desc (E.isDeflation_g P.conflation) g)
  refine ⟨K, k ≫ biprod.snd, ?_, fun W u hu ↦ ?_⟩
  · have hw : (k ≫ biprod.snd) ≫ g = (-(k ≫ biprod.fst)) ≫ P.p := by
      rw [Preadditive.neg_comp, eq_neg_iff_add_eq_zero, add_comm, ← hk, biprod.desc_eq]
      simp
    rw [hw]
    exact E.projectivelyTrivialIdeal.comp_mem_left _
      (mem_projectivelyTrivialIdeal_of_isProjective P.isProjective _)
  · obtain ⟨t, ht⟩ := mem_projectivelyTrivialIdeal_iff.1 hu (E.isDeflation_g P.conflation)
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (E.isKernelCokernelPair _ hS).fIsKernel
      (biprod.lift (-t) u) (by simp [ht])
    exact ⟨l, by rw [← Category.assoc, show l ≫ k = _ from hl, biprod.lift_snd]⟩

/-- **The projectively stable category `E/𝒫` has weak kernels**, when `E` has enough projectives
(Enomoto, Lemma A.8). A weak kernel of the class of `g` is the class of the morphism of
`TauCeti.ExactStructure.EnoughProjectives.exists_weakKernel`. -/
theorem EnoughProjectives.hasWeakKernels (h : E.EnoughProjectives) :
    HasWeakKernels E.projectivelyTrivialIdeal.Quotient where
  hasWeakLimit {Y Z} g := by
    obtain ⟨g, rfl⟩ :=
      E.projectivelyTrivialIdeal.quotientFunctor.map_surjective (X := Y.as) (Y := Z.as) g
    obtain ⟨K, w, hw, hl⟩ := h.exists_weakKernel g
    -- A fork `s` is the class of `u := preimage s.ι`, with `u ≫ g` projectively trivial.
    have hug (s : KernelFork (E.projectivelyTrivialIdeal.quotientFunctor.map g)) :
        E.projectivelyTrivialIdeal.quotientFunctor.preimage (X := s.pt.as) (Y := Y.as) s.ι ≫ g ∈
          E.projectivelyTrivialIdeal.hom _ _ := by
      rw [← MorphismIdeal.quotientFunctor_map_eq_zero_iff, Functor.map_comp,
        Functor.map_preimage]
      simp
    refine HasWeakLimit.mk ⟨KernelFork.ofι (E.projectivelyTrivialIdeal.quotientFunctor.map w)
      (by rwa [← Functor.map_comp, MorphismIdeal.quotientFunctor_map_eq_zero_iff]),
      Fork.IsWeakLimit.mk' _ fun s ↦
        ⟨E.projectivelyTrivialIdeal.quotientFunctor.map (hl _ (hug s)).choose, ?_⟩⟩
    rw [Fork.ι_ofι, ← Functor.map_comp, (hl _ (hug s)).choose_spec, Functor.map_preimage]

open ZeroObject in
/-- The quotient `E/𝒫` is nonempty: it contains the class of a zero object. -/
instance : Nonempty E.projectivelyTrivialIdeal.Quotient :=
  ⟨E.projectivelyTrivialIdeal.quotientFunctor.obj 0⟩

/-- **`mod (E/𝒫)` is abelian** when `E` has enough projectives, with kernels and cokernels
computed in the functor category. Since `TauCeti.ExactStructure.EnoughProjectives` is a
proposition rather than a class, this is a definition, to be installed with `letI` where it is
needed; the results of this file about injectives in `mod (E/𝒫)` do not depend on it. -/
@[instance_reducible]
noncomputable def EnoughProjectives.abelian (h : E.EnoughProjectives) :
    Abelian (isFinitelyPresentedFunctor E.projectivelyTrivialIdeal.Quotient).FullSubcategory :=
  have := h.hasWeakKernels
  inferInstance

/-- With enough projectives, every `f : Y ⟶ Z` is a deflation up to projectively trivial
morphisms: there are an extension `e` of `Z` and morphisms `s : Y ⟶ e.obj`, `r : e.obj ⟶ Y` with
`s ≫ e.g = f` and `e.g ≡ r ≫ f` modulo `𝒫`. Take `e.g = [c, f] : P ⊞ Y ⟶ Z`, for a deflation
`c` from a relative projective `P`. -/
theorem EnoughProjectives.exists_extension_of_hom (h : E.EnoughProjectives) {Y Z : C}
    (f : Y ⟶ Z) :
    ∃ (X : C) (e : E.Extension Z X) (s : Y ⟶ e.obj) (r : e.obj ⟶ Y), s ≫ e.g = f ∧
      E.projectivelyTrivialIdeal.quotientFunctor.map e.g =
        E.projectivelyTrivialIdeal.quotientFunctor.map (r ≫ f) := by
  let P := h.projectivePresentation Z
  obtain ⟨X, k, hk, hS⟩ :=
    (E.isDeflation_iff _).1 (E.isDeflation_biprod_desc (E.isDeflation_g P.conflation) f)
  refine ⟨X, ⟨_, k, _, hk, hS⟩, biprod.inr, biprod.snd, biprod.inr_desc _ _, ?_⟩
  rw [MorphismIdeal.quotientFunctor_map_eq_iff]
  have hd : biprod.desc P.p f - biprod.snd ≫ f = biprod.fst ≫ P.p := by
    rw [biprod.desc_eq]
    abel
  rw [hd]
  exact E.projectivelyTrivialIdeal.comp_mem_left _
    (mem_projectivelyTrivialIdeal_of_isProjective P.isProjective _)

/-! ### Contravariant defects -/

namespace Extension

variable {X Z : C}

/-- The **contravariant defect** of a conflation `e : X ⟶ Y ⟶ Z`, on the quotient `E/𝒫` of `C`
by the projectively trivial morphisms: the cokernel of `(-, Y) ⟶ (-, Z)`, that is, pointwise
`coker ((W, Y) ⟶ (W, Z))` with morphisms taken modulo `𝒫`. For an injective presentation
`A ⟶ I ⟶ K` it is `Ext¹_E(-, A)`. -/
noncomputable abbrev contravariantDefect (e : E.Extension Z X) :
    E.projectivelyTrivialIdeal.Quotientᵒᵖ ⥤ AddCommGrpCat.{v} :=
  cokernel (preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map e.g))

/-- The projection `(-, Z) ⟶ e.contravariantDefect` onto the contravariant defect. -/
noncomputable abbrev contravariantDefectπ (e : E.Extension Z X) :
    preadditiveYoneda.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) ⟶
      e.contravariantDefect :=
  cokernel.π _

/-- The contravariant defect of a conflation is finitely presented. -/
theorem isFinitelyPresentedFunctor_contravariantDefect (e : E.Extension Z X) :
    IsFinitelyPresentedFunctor e.contravariantDefect :=
  isFinitelyPresentedFunctor_iff_exists_isColimit.2
    ⟨_, _, _, e.contravariantDefectπ, cokernel.condition _, ⟨cokernelIsCokernel _⟩⟩

/-- The contravariant defect of a conflation, as an object of `mod (E/𝒫)`. -/
noncomputable abbrev modContravariantDefect (e : E.Extension Z X) :
    (isFinitelyPresentedFunctor E.projectivelyTrivialIdeal.Quotient).FullSubcategory :=
  .mk _ e.isFinitelyPresentedFunctor_contravariantDefect

/-- A morphism `u : V ⟶ Z` of `E/𝒫` vanishes in the contravariant defect exactly when it factors
through the deflation of the conflation. -/
theorem contravariantDefectπ_app_eq_zero_iff (e : E.Extension Z X)
    {V : E.projectivelyTrivialIdeal.Quotient}
    (u : V ⟶ E.projectivelyTrivialIdeal.quotientFunctor.obj Z) :
    e.contravariantDefectπ.app (Opposite.op V) u = 0 ↔
      ∃ s : V ⟶ E.projectivelyTrivialIdeal.quotientFunctor.obj e.obj,
        s ≫ E.projectivelyTrivialIdeal.quotientFunctor.map e.g = u := by
  refine ⟨fun hu ↦ (exact_preadditiveYoneda_map_iff _ _ (cokernel.condition _)).1
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) u hu, ?_⟩
  rintro ⟨s, rfl⟩
  rw [← preadditiveYoneda_map_comp_eq_zero_iff, Functor.map_comp, Category.assoc,
    cokernel.condition, comp_zero]

end Extension

/-- **Every finitely presented functor on `E/𝒫` is a contravariant defect**, when `E` has enough
projectives. A presentation by `f : Y ⟶ Z` does not change when `f` is replaced by the deflation
`[c, f] : P ⊞ Y ⟶ Z`, for a deflation `c` from a relative projective `P`. -/
theorem EnoughProjectives.exists_iso_contravariantDefect (h : E.EnoughProjectives)
    {F : E.projectivelyTrivialIdeal.Quotientᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hF : IsFinitelyPresentedFunctor F) :
    ∃ (Z X : C) (e : E.Extension Z X), Nonempty (F ≅ e.contravariantDefect) := by
  obtain ⟨Y, Z, f, p, hfp, ⟨hc⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hF
  obtain ⟨f, rfl⟩ :=
    E.projectivelyTrivialIdeal.quotientFunctor.map_surjective (X := Y.as) (Y := Z.as) f
  obtain ⟨X, e, s, r, hs, hr⟩ := h.exists_extension_of_hom f
  refine ⟨_, X, e, ⟨IsColimit.coconePointUniqueUpToIso
    (CokernelCofork.isColimitOfIsColimitOfIff hc _ (Iso.refl _) fun W φ ↦ ?_)
    (colimit.isColimit _)⟩⟩
  rw [Iso.refl_hom, Category.id_comp]
  refine ⟨fun hφ ↦ ?_, fun hφ ↦ ?_⟩
  · rw [hr, Functor.map_comp, Functor.map_comp, Category.assoc, hφ, comp_zero]
  · rw [← hs, Functor.map_comp, Functor.map_comp, Category.assoc, hφ, comp_zero]

/-- With enough projectives, the kernel of a morphism `β : (-, Z) ⟶ H` to a finitely presented
functor on `E/𝒫` is the image of `(-, Y) ⟶ (-, Z)` for a conflation `X ⟶ Y ⟶ Z` of `E`: the
deflation `Y ⟶ Z` is killed by `β`, and every `z : V ⟶ Z` killed by `β` factors through it in
`E/𝒫`. -/
theorem EnoughProjectives.exists_extension_exact (h : E.EnoughProjectives) {Z : C}
    {H : E.projectivelyTrivialIdeal.Quotientᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hH : IsFinitelyPresentedFunctor H)
    (β : preadditiveYoneda.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) ⟶ H) :
    ∃ (X : C) (e : E.Extension Z X),
      preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map e.g) ≫ β = 0 ∧
      ∀ ⦃V : E.projectivelyTrivialIdeal.Quotient⦄
        (z : V ⟶ E.projectivelyTrivialIdeal.quotientFunctor.obj Z),
        preadditiveYoneda.map z ≫ β = 0 →
          ∃ z' : V ⟶ E.projectivelyTrivialIdeal.quotientFunctor.obj e.obj,
            z' ≫ E.projectivelyTrivialIdeal.quotientFunctor.map e.g = z := by
  have := h.hasWeakKernels
  obtain ⟨W, w, hw, hS⟩ := hH.exists_exact_preadditiveYoneda_map β
  obtain ⟨w, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective (X := W.as) w
  obtain ⟨X, e, s, r, hs, hr⟩ := h.exists_extension_of_hom w
  rw [exact_preadditiveYoneda_map_iff] at hS
  refine ⟨X, e, by rw [hr, Functor.map_comp, Functor.map_comp, Category.assoc, hw, comp_zero],
    fun V z hz ↦ ?_⟩
  obtain ⟨x, hx⟩ := hS z ((preadditiveYoneda_map_comp_eq_zero_iff z β).1 hz)
  exact ⟨x ≫ E.projectivelyTrivialIdeal.quotientFunctor.map s,
    by rw [Category.assoc, ← Functor.map_comp, hs, hx]⟩

/-! ### The connecting morphism to `Ext¹_E(-, X)` on `E/𝒫` -/

namespace Extension

variable {X Z : C} [E.HasSmallExt1.{v}]

/-- The **connecting morphism** `(-, Z) ⟶ Ext¹_E(-, X)` of a conflation `e : X ⟶ Y ⟶ Z`, on
`E/𝒫`: it sends `u : W ⟶ Z` to the base change `u^* [e]`. -/
noncomputable def ext1Connecting (e : E.Extension Z X) :
    preadditiveYoneda.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) ⟶
      E.stableExt1Functor X where
  app W := AddCommGrpCat.ofHom
    ({ toFun u := (E.stableExt1Functor X).map u.op (equivShrink _ (Ext1.mk e))
       map_zero' := by rw [op_zero, Functor.map_zero]; rfl
       map_add' u v := by rw [op_add, Functor.map_add]; rfl } :
      (W.unop ⟶ E.projectivelyTrivialIdeal.quotientFunctor.obj Z) →+ (E.stableExt1Functor X).obj W)
  naturality W W' f := by
    ext (u : W.unop ⟶ _)
    exact ConcreteCategory.congr_hom ((E.stableExt1Functor X).map_comp u.op f) _

/-- The connecting morphism sends the class of `u : W ⟶ Z` to `u^* [e]`. -/
@[simp]
theorem ext1Connecting_app_apply (e : E.Extension Z X) {W : E.projectivelyTrivialIdeal.Quotient}
    (u : W.as ⟶ Z) :
    e.ext1Connecting.app (Opposite.op W)
      (E.projectivelyTrivialIdeal.quotientFunctor.map u : W ⟶ _) =
      equivShrink _ ((Ext1.mk e).pullback u) :=
  (stableExt1Functor_map_apply X u _).trans (by rw [Equiv.symm_apply_apply])

/-- The deflation of a conflation vanishes under its connecting morphism. -/
@[reassoc (attr := simp)]
theorem map_g_comp_ext1Connecting (e : E.Extension Z X) :
    preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map e.g) ≫
      e.ext1Connecting = 0 := by
  rw [preadditiveYoneda_map_comp_eq_zero_iff, ext1Connecting_app_apply,
    show (Ext1.mk e).pullback e.g = 0 from
      (e.exact_comp_g_mk_pullback _ e.g).2 ⟨𝟙 _, Category.id_comp _⟩]
  exact ((Equiv.symm_apply_eq _).1 equivShrink_symm_zero).symm

/-- **Exactness of `(-, Y) ⟶ (-, Z) ⟶ Ext¹_E(-, X)`** on `E/𝒫`, for a conflation
`X ⟶ Y ⟶ Z`: a morphism `u : W ⟶ Z` with `u^* [e] = 0` factors through `Y ⟶ Z`. -/
theorem exact_ext1Connecting (e : E.Extension Z X) :
    (ShortComplex.mk _ _ e.map_g_comp_ext1Connecting).Exact := by
  refine (exact_preadditiveYoneda_map_iff _ _ _).2 fun V z hz ↦ ?_
  obtain ⟨u, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective (X := V.as) z
  have h0 := (Equiv.symm_apply_eq (equivShrink (E.Ext1 V.as X))).1 equivShrink_symm_zero
  obtain ⟨t, rfl⟩ := (e.exact_comp_g_mk_pullback V.as u).1
    ((equivShrink _).injective ((ext1Connecting_app_apply e u).symm.trans (hz.trans h0)))
  exact ⟨E.projectivelyTrivialIdeal.quotientFunctor.map t, (Functor.map_comp _ _ _).symm⟩

/-- The connecting morphism of a conflation with relatively injective middle term is an
epimorphism: every class in `Ext¹_E(W, X)` is a base change of the conflation. -/
theorem epi_ext1Connecting (e : E.Extension Z X) (he : E.isInjective e.obj) :
    Epi e.ext1Connecting := by
  have (W : E.projectivelyTrivialIdeal.Quotientᵒᵖ) : Epi (e.ext1Connecting.app W) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro ξ
    obtain ⟨u, hu⟩ := e.exists_mk_pullback_eq_of_isInjective he
      ((equivShrink (E.Ext1 W.unop.as X)).symm ξ)
    exact ⟨E.projectivelyTrivialIdeal.quotientFunctor.map u,
      (ext1Connecting_app_apply e (W := W.unop) u).trans
        ((congrArg (equivShrink _) hu).trans (Equiv.apply_symm_apply _ _))⟩
  exact NatTrans.epi_of_epi_app _

/-- **The contravariant defect of a conflation with relatively injective middle term is
`Ext¹_E(-, X)`.** For a conflation `X ⟶ Y ⟶ Z` with `Y` relatively injective, the connecting
morphism `(-, Z) ⟶ Ext¹_E(-, X)` induces an isomorphism from the cokernel of
`(-, Y) ⟶ (-, Z)`. -/
noncomputable def contravariantDefectIsoStableExt1Functor (e : E.Extension Z X)
    (he : E.isInjective e.obj) : e.contravariantDefect ≅ E.stableExt1Functor X :=
  have := e.epi_ext1Connecting he
  have := e.exact_ext1Connecting.mono_cokernelDesc
  have : Epi (cokernel.desc _ _ e.map_g_comp_ext1Connecting) :=
    epi_of_epi_fac (cokernel.π_desc _ _ _)
  have := isIso_of_mono_of_epi (cokernel.desc _ _ e.map_g_comp_ext1Connecting)
  asIso (cokernel.desc _ _ e.map_g_comp_ext1Connecting)

/-- The isomorphism `TauCeti.ExactStructure.Extension.contravariantDefectIsoStableExt1Functor` is
induced by the connecting morphism. -/
@[reassoc (attr := simp)]
theorem contravariantDefectπ_comp_contravariantDefectIsoStableExt1Functor_hom
    (e : E.Extension Z X) (he : E.isInjective e.obj) :
    e.contravariantDefectπ ≫ (e.contravariantDefectIsoStableExt1Functor he).hom =
      e.ext1Connecting :=
  cokernel.π_desc _ _ _

end Extension

/-- `Ext¹_E(-, A)` is finitely presented on `E/𝒫` when `A` has an injective presentation. -/
theorem isFinitelyPresentedFunctor_stableExt1Functor {A : C} [E.HasSmallExt1.{v}]
    (hA : Nonempty (E.InjectivePresentation A)) :
    IsFinitelyPresentedFunctor (E.stableExt1Functor A) :=
  let ⟨P⟩ := hA
  (isFinitelyPresentedFunctor _).prop_of_iso
    (P.extension.contravariantDefectIsoStableExt1Functor P.isInjective_extension_obj)
    P.extension.isFinitelyPresentedFunctor_contravariantDefect

variable (E) in
/-- `Ext¹_E(-, A)` as an object of `mod (E/𝒫)`, for `A` with an injective presentation. -/
noncomputable abbrev modExt1 (A : C) [E.HasSmallExt1.{v}]
    (hA : Nonempty (E.InjectivePresentation A)) :
    (isFinitelyPresentedFunctor E.projectivelyTrivialIdeal.Quotient).FullSubcategory :=
  .mk _ (isFinitelyPresentedFunctor_stableExt1Functor hA)

/-! ### Injective objects of `mod (E/𝒫)` -/

namespace Extension

variable {A K X Z : C}

/-- **The key lemma for injectivity of contravariant defects** (Enomoto, Lemma A.8). Let
`d : A ⟶ I ⟶ K` be a conflation with `I` relatively injective and `X ⟶ Y ⟶ Z` a conflation. If
the restriction to `X` of `a : Y ⟶ K` factors through `I ⟶ K` modulo `𝒫`, then `a` is the sum of
a morphism factoring through `Y ⟶ Z` and one factoring through `I ⟶ K`. -/
theorem exists_eq_add_of_isInjective (d : E.Extension K A) (hd : E.isInjective d.obj)
    (e : E.Extension Z X) {a : e.obj ⟶ K} {s : X ⟶ d.obj}
    (h : e.f ≫ a - s ≫ d.g ∈ E.projectivelyTrivialIdeal.hom X K) :
    ∃ (b : Z ⟶ K) (t : e.obj ⟶ d.obj), a = e.g ≫ b + t ≫ d.g := by
  -- The difference factors through the deflation `d.g`, and `I` is relatively injective.
  obtain ⟨s', hs'⟩ : ∃ s' : X ⟶ d.obj, s' ≫ d.g = e.f ≫ a - s ≫ d.g :=
    mem_projectivelyTrivialIdeal_iff.1 h (E.isDeflation_g d.conflation)
  obtain ⟨t, ht⟩ := isInjective_iff.1 hd (E.isInflation_f e.conflation) (s' + s)
  obtain ⟨b, hb⟩ := CokernelCofork.IsColimit.desc' e.isKernelCokernelPair.gIsCokernel
    (a - t ≫ d.g) (by
      change e.f ≫ (a - t ≫ d.g) = 0
      rw [Preadditive.comp_sub, reassoc_of% ht, Preadditive.add_comp, hs']
      abel)
  exact ⟨b, t, by rw [show e.g ≫ b = _ from hb]; abel⟩

/-- A morphism `γ : (-, Y) ⟶ G` to the contravariant defect `G` of a conflation `A ⟶ I ⟶ K` with
`I` relatively injective which kills `(-, X)`, for a conflation `X ⟶ Y ⟶ Z`, factors through
`(-, Y) ⟶ (-, Z)`, by a morphism coming from some `b : Z ⟶ K`. -/
private theorem exists_comp_contravariantDefectπ_eq (d : E.Extension K A)
    (hd : E.isInjective d.obj) (e : E.Extension Z X)
    (γ : preadditiveYoneda.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj e.obj) ⟶
      d.contravariantDefect)
    (hγ : preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map e.f) ≫ γ = 0) :
    ∃ b : Z ⟶ K, preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map e.g) ≫
      preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map b) ≫
        d.contravariantDefectπ = γ := by
  obtain ⟨a, ha⟩ := exists_preadditiveYoneda_map_comp_eq d.contravariantDefectπ γ
  obtain ⟨a, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective a
  rw [← ha, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    preadditiveYoneda_map_comp_eq_zero_iff, Extension.contravariantDefectπ_app_eq_zero_iff] at hγ
  obtain ⟨s, hs⟩ := hγ
  obtain ⟨s, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective s
  obtain ⟨b, t, rfl⟩ := d.exists_eq_add_of_isInjective hd e (a := a) (s := s) (by
    rw [← MorphismIdeal.quotientFunctor_map_eq_iff]
    exact hs.symm.trans (Functor.map_comp _ _ _).symm)
  refine ⟨b, ?_⟩
  rw [← ha, Functor.map_add, Functor.map_add, Preadditive.add_comp, Functor.map_comp,
    Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    cokernel.condition, comp_zero, add_zero]

end Extension

/-- **Contravariant defects of injective conflations extend along monomorphisms of finitely
presented functors**, in the functor category: with `G` the contravariant defect of a conflation
with relatively injective middle term, every morphism `F' ⟶ G` extends along a monomorphism
`F' ⟶ F` of finitely presented functors on `E/𝒫`. -/
private theorem EnoughProjectives.exists_comp_eq_contravariantDefect (h : E.EnoughProjectives)
    {A K : C} (d : E.Extension K A) (hd : E.isInjective d.obj)
    {F' F : E.projectivelyTrivialIdeal.Quotientᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hF' : IsFinitelyPresentedFunctor F') (hF : IsFinitelyPresentedFunctor F) (α : F' ⟶ F)
    [Mono α] (φ : F' ⟶ d.contravariantDefect) :
    ∃ ψ : F ⟶ d.contravariantDefect, α ≫ ψ = φ := by
  obtain ⟨X₀, Y₀, f₀, π, hπ, ⟨hc⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hF
  -- The preimage of `F'` in `(-, Y₀)` is the image of `(-, Y) ⟶ (-, Y₀)` for a conflation
  -- `X ⟶ Y ⟶ Y₀`, which lifts to `γ : (-, Y) ⟶ F'`.
  obtain ⟨X, e, he, hlift⟩ := h.exists_extension_exact (Z := Y₀.as)
    (IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork (cokernelIsCokernel α)
      hF'.isFinitelyGeneratedFunctor hF) (π ≫ cokernel.π α)
  obtain ⟨γ, hγ⟩ := KernelFork.IsLimit.lift' (Abelian.monoIsKernelOfCokernel _
    (cokernelIsCokernel α)) _ (by rw [Category.assoc]; exact he)
  rw [Fork.ι_ofι] at hγ
  have hfγ : preadditiveYoneda.map (E.projectivelyTrivialIdeal.quotientFunctor.map e.f) ≫ γ =
      0 := by
    rw [← cancel_mono α, Category.assoc, hγ, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, e.zero, Functor.map_zero, Functor.map_zero, zero_comp, zero_comp]
  obtain ⟨b, hb⟩ := d.exists_comp_contravariantDefectπ_eq hd e (γ ≫ φ)
    (by rw [← Category.assoc, hfγ, zero_comp])
  exact exists_comp_eq_of_mono_of_isColimit hc hF'.isFinitelyGeneratedFunctor α φ
    (fun V z u hu ↦ hlift z (by rw [← Category.assoc, ← hu]; simp)) γ hγ _ hb

/-- The contravariant defect of a conflation with relatively injective middle term is injective
in `mod (E/𝒫)`. -/
private theorem EnoughProjectives.injective_modContravariantDefect (h : E.EnoughProjectives)
    {A K : C} (d : E.Extension K A) (hd : E.isInjective d.obj) :
    Injective d.modContravariantDefect where
  factors {F' F} φ α _ := by
    have := h.hasWeakKernels
    have := ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (isFinitelyPresentedFunctor E.projectivelyTrivialIdeal.Quotient)
    have : Mono α.hom := inferInstanceAs (Mono ((isFinitelyPresentedFunctor _).ι.map α))
    obtain ⟨ψ, hψ⟩ := h.exists_comp_eq_contravariantDefect d hd F'.property F.property α.hom φ.hom
    exact ⟨ObjectProperty.homMk ψ, ObjectProperty.hom_ext _ hψ⟩

/-- **`Ext¹_E(-, A)` is injective in `mod (E/𝒫)`** when `E` has enough projectives and `A` has an
injective presentation (Enomoto, Lemma A.8): it is the contravariant defect of the
presentation. -/
theorem EnoughProjectives.injective_modExt1 (h : E.EnoughProjectives) (A : C)
    [E.HasSmallExt1.{v}] (hA : Nonempty (E.InjectivePresentation A)) :
    Injective (E.modExt1 A hA) :=
  let ⟨P⟩ := hA
  Injective.of_iso (ObjectProperty.isoMk _
    (P.extension.contravariantDefectIsoStableExt1Functor P.isInjective_extension_obj))
    (h.injective_modContravariantDefect P.extension P.isInjective_extension_obj)

/-! ### Enough injectives in `mod (E/𝒫)` -/

/-- **`mod (E/𝒫)` has enough injectives** when `E` has enough projectives and enough injectives
(Enomoto, Lemma A.8). A finitely presented functor is the contravariant defect of a conflation
`X ⟶ Y ⟶ Z`, which embeds into `Ext¹_E(-, X)` through the connecting morphism
`u ↦ u^* [X ⟶ Y ⟶ Z]`, by exactness of `(-, Y) ⟶ (-, Z) ⟶ Ext¹_E(-, X)`. -/
theorem EnoughProjectives.enoughInjectives (hP : E.EnoughProjectives) (hI : E.EnoughInjectives) :
    CategoryTheory.EnoughInjectives
      (isFinitelyPresentedFunctor E.projectivelyTrivialIdeal.Quotient).FullSubcategory where
  presentation F := by
    obtain ⟨Z, X, e, ⟨φ⟩⟩ := hP.exists_iso_contravariantDefect F.property
    have := hI.hasSmallExt1
    have := e.exact_ext1Connecting.mono_cokernelDesc
    let ι : F ⟶ E.modExt1 X (hI.presentation X) :=
      ObjectProperty.homMk (φ.hom ≫ cokernel.desc _ _ e.map_g_comp_ext1Connecting)
    have : Mono ((isFinitelyPresentedFunctor _).ι.map ι) := mono_comp _ _
    exact ⟨⟨_, hP.injective_modExt1 X (hI.presentation X), ι,
      (isFinitelyPresentedFunctor _).ι.mono_of_mono_map this⟩⟩

end ExactStructure

end TauCeti
