/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Abelian.Refinements
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# The triangle of mapping cones of two monomorphisms, up to quasi-isomorphism

For composable morphisms `a : X ⟶ Y` and `b : Y ⟶ Z` of cochain complexes in an abelian category,
Mathlib's triangle of mapping cones `cone a ⟶ cone (a ≫ b) ⟶ cone b ⟶ (cone a)⟦1⟧`
(`mappingConeCompTriangle a b`) is compared with the sequence of cokernels
`cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b` through the canonical maps
`mappingCone.descShortComplex` from the mapping cones to the cokernels. When `b` is a
monomorphism, the latter sequence is short exact, and the map in cohomology induced by the third
morphism of the triangle is the connecting map of that short exact sequence
(`CochainComplex.mappingCone.shiftMap_mappingConeCompTriangle_mor₃`). This extends Mathlib's
`mappingCone.homologySequenceδ_triangleh`, which is the case `a = 0`.

The file also records a form of Mathlib's `mappingCone.quasiIso_descShortComplex` for maps out of
the mapping cone that are only known to factor through the cokernel: for a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, a map `mappingCone (X₁ ⟶ X₂) ⟶ W` vanishing on `X₁` and given on `X₂` by
`X₂ ⟶ X₃ ⟶ W` for a quasi-isomorphism `X₃ ⟶ W` is a quasi-isomorphism
(`CochainComplex.mappingCone.quasiIso_desc_of_shortExact`). This is how a three-term sequence
which is short exact only up to a quasi-isomorphism, such as a Mayer–Vietoris sequence of singular
chains, is shown to have acyclic total complex. In particular, extension by zero along an
embedding into `ComplexShape.up ℤ` carries a sequence `P₄ ⟶ P₂ ⊞ P₃ ⟶ P₁` of homological
complexes, with monomorphic first map `(f₂, -f₃)` and second map `g₂ + g₃` inducing a
quasi-isomorphism from its cokernel, to one whose Mayer–Vietoris map out of the mapping cone of
`(f₂, f₃)` is a quasi-isomorphism
(`CochainComplex.mappingCone.quasiIso_desc_extendMap_of_quasiIso_cokernelDesc`).

Finally, mapping cones carry short exact sequences to short exact sequences. For a morphism
`φ : S₁ ⟶ S₂` of short exact sequences of cochain complexes, the mapping cones of its three
components, with the maps of mapping cones induced by `S₁` and `S₂`, form a short exact sequence
(`CochainComplex.mappingCone.shortExact_mapShortComplex`): in degree `n` it is the direct sum of
the sequences of `S₁` in degree `n + 1` and of `S₂` in degree `n`. And for `φ : K ⟶ L`, the
inclusion of `L` in the mapping cone of `φ` is followed by the degreewise split epimorphism onto
the mapping cone of `K ⟶ 0`, which is `K` shifted by one
(`CochainComplex.mappingCone.shortExact_inrShortComplex`, from
`HomologicalComplex.homotopyCofiber.coneShortComplex_shortExact`). Objectwise, for a natural
transformation `τ : F ⟶ G` of functors with values in cochain complexes, this gives the short exact
sequence `G ⟶ cone τ ⟶ cone (F ⟶ 0)` of functors
(`CategoryTheory.NatTrans.shortExact_mappingConeInrShortComplex`).
-/

public section

open CategoryTheory Limits HomotopyCategory

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Abelian C] {X Y Z : CochainComplex C ℤ} (a : X ⟶ Y)
  (b : Y ⟶ Z) [Mono b]

/-- The map in cohomology induced by the third morphism `cone b ⟶ (cone a)⟦1⟧` of the triangle of
mapping cones of `a` and `b`, read through the canonical maps `cone a ⟶ cokernel a` and
`cone b ⟶ cokernel b` (the latter a quasi-isomorphism, as `b` is a monomorphism), is the
connecting map of the short exact sequence `cokernel a ⟶ cokernel (a ≫ b) ⟶ cokernel b`. -/
lemma shiftMap_mappingConeCompTriangle_mor₃ (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (mappingConeCompTriangle a b).mor₃ n₀ n₁ h ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence a)) n₁ =
    HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence b)) n₀ ≫
      (TauCeti.cokernelCompSequence_shortExact a b).δ n₀ n₁
        (by simp [← h, add_comm]) := by
  -- The connecting map of the triangle of `b` alone, through `homologySequenceδ_triangleh`.
  have hb := homologySequenceδ_triangleh (TauCeti.cokernelSequence_shortExact b) n₀ n₁ (by lia)
  rw [homologySequenceδ_quotient_mapTriangle_obj] at hb
  have hb' : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (triangle b).mor₃ n₀ n₁ h =
      HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence b)) n₀ ≫
        (TauCeti.cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm]) := by
    have h₁ := (Iso.cancel_iso_hom_left
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₀).app (mappingCone b)) _ _).1 hb
    exact (Iso.cancel_iso_inv_right _ _
      ((homologyFunctorFactors C (ComplexShape.up ℤ) n₁).app Y)).1
        (h₁.trans (Category.assoc _ _ _).symm)
  -- The naturality of connecting maps along `(Y ⟶ Z ⟶ cokernel b) ⟶ (cokernel a ⟶ … )`.
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    (TauCeti.cokernelSequenceToCokernelCompSequence a b) (TauCeti.cokernelSequence_shortExact b)
    (TauCeti.cokernelCompSequence_shortExact a b) n₀ n₁
    (by simp [← h, add_comm])
  simp only [TauCeti.cokernelSequenceToCokernelCompSequence_τ₃,
    TauCeti.cokernelSequenceToCokernelCompSequence_τ₁] at hnat
  have hnat' := hnat.trans ((congrArg (· ≫ _) (HomologicalComplex.homologyMap_id _ n₀)).trans
    (Category.id_comp _))
  -- `Functor.shiftMap_comp`, applied to the third morphism `(triangle b).mor₃ ≫ (inr a)⟦1⟧'`;
  -- `(homologyFunctor 0).shift n₁` is `homologyFunctor n₁` by `homologyFunctor_shift`.
  have hcomp : (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (mappingConeCompTriangle a b).mor₃ n₀ n₁ h =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle b).mor₃ n₀ n₁ h ≫ HomologicalComplex.homologyMap (inr a) n₁ :=
    Functor.shiftMap_comp _ _ _ _ _ _
  have e₁ : HomologicalComplex.homologyMap (inr a) n₁ ≫
      HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence a)) n₁ =
      HomologicalComplex.homologyMap (cokernel.π a) n₁ :=
    (HomologicalComplex.homologyMap_comp _ _ n₁).symm.trans
      (congrArg (HomologicalComplex.homologyMap · n₁)
        (inr_descShortComplex (ShortComplex.cokernelSequence a)))
  rw [hcomp, hb']
  let A := HomologicalComplex.homologyMap (descShortComplex (ShortComplex.cokernelSequence b)) n₀
  let D := (TauCeti.cokernelSequence_shortExact b).δ n₀ n₁ (by simp [← h, add_comm])
  exact (Category.assoc (A ≫ D) _ _).trans <|
    (congrArg (fun t => (A ≫ D) ≫ t) e₁).trans <|
    (Category.assoc A D _).trans (congrArg (fun t => A ≫ t) hnat')

end CochainComplex.mappingCone

namespace CochainComplex.mappingCone

open HomComplex

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex (CochainComplex C ℤ)}

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes and a
quasi-isomorphism `h : X₃ ⟶ W`, the map `mappingCone (X₁ ⟶ X₂) ⟶ W` which vanishes on `X₁` and is
`X₂ ⟶ X₃ ⟶ W` on `X₂` is a quasi-isomorphism: it is `descShortComplex S ≫ h`. -/
lemma quasiIso_desc_of_shortExact (hS : S.ShortExact) {W : CochainComplex C ℤ} (h : S.X₃ ⟶ W)
    [QuasiIso h] {ψ : S.X₂ ⟶ W} (hψ : S.g ≫ h = ψ)
    (eq : δ (-1) 0 (0 : Cochain S.X₁ W (-1)) = Cochain.ofHom (S.f ≫ ψ)) :
    QuasiIso (desc S.f 0 ψ eq) := by
  have := quasiIso_descShortComplex hS
  have hd : desc S.f 0 ψ eq = descShortComplex S ≫ h := by
    subst hψ
    ext n
    apply ext_from _ (n + 1) n rfl <;> simp [descShortComplex]
  rw [hd]
  infer_instance

/-- Extension by zero along `e` carries a three-term sequence `P₄ ⟶ P₂ ⊞ P₃ ⟶ P₁` of homological
complexes, with monomorphic first map `(f₂, -f₃)` and second map `g₂ + g₃` inducing a
quasi-isomorphism from its cokernel, to one whose Mayer–Vietoris map
`mappingCone (E f₂, E f₃) ⟶ E P₁`, given by `(E g₂, -E g₃)` as in
`TopCat.KPresheaf.mayerVietorisDesc`, is a quasi-isomorphism. -/
lemma quasiIso_desc_extendMap_of_quasiIso_cokernelDesc {ι : Type*} {c : ComplexShape ι}
    {P₁ P₂ P₃ P₄ : HomologicalComplex C c} (e : c.Embedding (ComplexShape.up ℤ))
    {f₂ : P₄ ⟶ P₂} {f₃ : P₄ ⟶ P₃} {g₂ : P₂ ⟶ P₁} {g₃ : P₃ ⟶ P₁} {a : P₄ ⟶ P₂ ⊞ P₃}
    {b : P₂ ⊞ P₃ ⟶ P₁} [Mono a]
    (hab : a ≫ b = 0) [QuasiIso (cokernel.desc a b hab)] (ha : a = biprod.lift f₂ (-f₃))
    (hb : b = biprod.desc g₂ g₃)
    (eq : δ (-1) 0 (0 : Cochain _ _ (-1)) = Cochain.ofHom
      (biprod.lift (HomologicalComplex.extendMap f₂ e) (HomologicalComplex.extendMap f₃ e) ≫
        biprod.desc (HomologicalComplex.extendMap g₂ e) (-HomologicalComplex.extendMap g₃ e))) :
    QuasiIso (desc (biprod.lift (HomologicalComplex.extendMap f₂ e)
      (HomologicalComplex.extendMap f₃ e)) 0
      (biprod.desc (HomologicalComplex.extendMap g₂ e) (-HomologicalComplex.extendMap g₃ e))
        eq) := by
  subst hb
  let E := e.extendFunctor C
  -- the twisted comparison `θ` carries `E a` and `E (g₂ + g₃)` to the maps of the conclusion
  let θ := E.mapBiprodNegIso P₂ P₃
  have hφ : E.map a ≫ θ.hom = biprod.lift (E.map f₂) (E.map f₃) := by
    subst ha
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [θ, ← E.map_comp]
  have hψ : (θ.inv ≫ E.map (cokernel.π a)) ≫ E.map (cokernel.desc _ _ hab) =
      biprod.desc (E.map g₂) (-E.map g₃) := by
    rw [Category.assoc, ← E.map_comp, cokernel.π_desc, Iso.inv_comp_eq]
    simp [θ, biprod.desc_eq]
  -- so the sequence of the conclusion is short exact up to `E (cokernel a) ⟶ E P₁`
  let S := ShortComplex.mk (biprod.lift (E.map f₂) (E.map f₃)) (θ.inv ≫ E.map (cokernel.π a))
    (by rw [← hφ]; simp [← E.map_comp])
  have hS : S.ShortExact := ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := (ShortComplex.cokernelSequence a).map E) (Iso.refl _) θ
      (Iso.refl _) ((Category.id_comp _).trans hφ.symm)
      ((θ.hom_inv_id_assoc _).trans (Category.comp_id _).symm))
    ((TauCeti.cokernelSequence_shortExact _).extend e)
  have : QuasiIso (E.map (cokernel.desc _ _ hab)) := by
    simp only [E, ComplexShape.Embedding.extendFunctor_map]
    infer_instance
  exact quasiIso_desc_of_shortExact hS _ hψ eq

end CochainComplex.mappingCone

/-! ### Short exact sequences of mapping cones -/

namespace CochainComplex.mappingCone

open HomComplex

variable {C : Type*} [Category* C] [Abelian C]

section MapShortComplex

variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)

/-- The mapping cones `cone φ.τ₁ ⟶ cone φ.τ₂ ⟶ cone φ.τ₃` of the components of a morphism
`φ : S₁ ⟶ S₂` of short complexes of cochain complexes, with the maps of mapping cones induced by
the maps of `S₁` and `S₂`. -/
@[expose, simps]
noncomputable def mapShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂) (map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃) (by
    have h₁ (p : ℤ) : S₁.f.f p ≫ S₁.g.f p = 0 := by
      rw [← HomologicalComplex.comp_f, S₁.zero, HomologicalComplex.zero_f]
    have h₂ (p : ℤ) : S₂.f.f p ≫ S₂.g.f p = 0 := by
      rw [← HomologicalComplex.comp_f, S₂.zero, HomologicalComplex.zero_f]
    ext n
    apply ext_from _ (n + 1) n rfl <;> simp [reassoc_of% h₁, reassoc_of% h₂])

/-- **Mapping cones of a morphism of short exact sequences form a short exact sequence.** In degree
`n` the sequence of mapping cones is the direct sum of the sequences of `S₁` in degree `n + 1` and
of `S₂` in degree `n`. -/
lemma shortExact_mapShortComplex (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) :
    (mapShortComplex φ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  change (ShortComplex.mk ((map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂).f n)
    ((map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃).f n) _).ShortExact
  have e₁ := (HomologicalComplex.shortExact_iff_degreewise_shortExact S₁).1 h₁ (n + 1)
  have e₂ := (HomologicalComplex.shortExact_iff_degreewise_shortExact S₂).1 h₂ n
  have : Mono (S₁.f.f (n + 1)) := e₁.mono_f
  have : Mono (S₂.f.f n) := e₂.mono_f
  have : Epi (S₁.g.f (n + 1)) := e₁.epi_g
  have : Epi (S₂.g.f n) := e₂.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x₂ (hx₂ : x₂ ≫ (map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃).f n = 0)
    -- lift the two components of `x₂` along `S₁.f` and `S₂.f`, up to refinements
    obtain ⟨A₁, π₁, _, y₁, hy₁⟩ := e₁.exact.exact_up_to_refinements
      (x₂ ≫ (fst φ.τ₂).val.v n (n + 1) rfl) (by simpa using hx₂ =≫ (fst φ.τ₃).val.v n (n + 1) rfl)
    obtain ⟨A₂, π₂, _, y₂, hy₂⟩ := e₂.exact.exact_up_to_refinements
      (π₁ ≫ x₂ ≫ (snd φ.τ₂).v n n (add_zero n))
      (by simpa using π₁ ≫= hx₂ =≫ (snd φ.τ₃).v n n (add_zero n))
    refine ⟨A₂, π₂ ≫ π₁, inferInstance,
      π₂ ≫ y₁ ≫ (inl φ.τ₁).v (n + 1) n (by lia) + y₂ ≫ (inr φ.τ₁).f n, ?_⟩
    apply ext_to φ.τ₂ n (n + 1) rfl
    · simpa using π₂ ≫= hy₁
    · simpa using hy₂
  · rw [Preadditive.mono_iff_cancel_zero]
    intro A x (hx : x ≫ (map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂).f n = 0)
    apply ext_to φ.τ₁ n (n + 1) rfl
    · rw [← cancel_mono (S₁.f.f (n + 1))]
      simpa using hx =≫ (fst φ.τ₂).val.v n (n + 1) rfl
    · rw [← cancel_mono (S₂.f.f n)]
      simpa using hx =≫ (snd φ.τ₂).v n n (add_zero n)
  · rw [epi_iff_surjective_up_to_refinements]
    intro A y
    -- lift the two components of `y` along `S₁.g` and `S₂.g`, up to refinements
    obtain ⟨A₁, π₁, _, a, ha⟩ := surjective_up_to_refinements_of_epi (S₁.g.f (n + 1))
      (y ≫ (fst φ.τ₃).val.v n (n + 1) rfl)
    obtain ⟨A₂, π₂, _, b, hb⟩ := surjective_up_to_refinements_of_epi (S₂.g.f n)
      (π₁ ≫ y ≫ (snd φ.τ₃).v n n (add_zero n))
    refine ⟨A₂, π₂ ≫ π₁, inferInstance,
      π₂ ≫ a ≫ (inl φ.τ₂).v (n + 1) n (by lia) + b ≫ (inr φ.τ₂).f n, ?_⟩
    apply ext_to φ.τ₃ n (n + 1) rfl
    · simpa using π₂ ≫= ha
    · simpa using hb

end MapShortComplex

section Inr

variable {K L Z : CochainComplex C ℤ} (φ : K ⟶ L) (α : K ⟶ Z) (hZ : IsZero Z)

/-- For `φ : K ⟶ L` and a map `α` from `K` to a zero complex, the sequence
`L ⟶ cone φ ⟶ cone α`: the inclusion of `L`, followed by the map of cones which forgets the summand
`L`. The mapping cone `cone α` is `K` shifted by one, with negated differential. -/
@[expose, simps]
noncomputable def inrShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (inr φ) (map φ α (𝟙 K) 0 (by simp [hZ.eq_of_tgt α 0])) (by ext n; simp)

open ZeroObject in
/-- The sequence `L ⟶ cone φ ⟶ cone α` of a mapping cone, for `α` a map from `K` to a zero
complex, is short exact: it is isomorphic to the sequence
`HomologicalComplex.homotopyCofiber.coneShortComplex φ`. -/
lemma shortExact_inrShortComplex : (inrShortComplex φ α hZ).ShortExact := by
  -- the sequence `L ⟶ homotopyCofiber φ ⟶ homotopyCofiber (K ⟶ 0)`, through `cone 0 ≅ cone α`
  have hc : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j := fun j ↦ ⟨j - 1, by simp⟩
  open HomologicalComplex.homotopyCofiber in
  have comm : mapArrowHom φ (0 : K ⟶ 0) hc (Arrow.homMk (𝟙 K) 0) ≫
      mapArrowHom (0 : K ⟶ 0) α hc (Arrow.homMk (𝟙 K) hZ.isoZero.symm.hom (hZ.eq_of_tgt _ _)) =
      mapArrowHom φ α hc (Arrow.homMk (𝟙 K) 0 (by simp [hZ.eq_of_tgt α 0])) := by
    rw [← mapArrowHom_comp]
    congr 1
    exact Arrow.hom_ext _ _ (Category.comp_id _) (hZ.eq_of_tgt _ _)
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := HomologicalComplex.homotopyCofiber.coneShortComplex φ hc)
      (Iso.refl _) (Iso.refl _) (mapIso (Iso.refl K) hZ.isoZero.symm (hZ.eq_of_tgt _ _))
      ((Category.id_comp _).trans (Category.comp_id _).symm)
      (by
        simp only [mapIso_hom, Iso.refl_hom, inrShortComplex_g, map_eq_mapArrowHom _ _ _ _ _ hc]
        exact (Category.id_comp _).trans comm.symm))
    (HomologicalComplex.homotopyCofiber.coneShortComplex_shortExact φ hc)

end Inr

end CochainComplex.mappingCone

namespace CategoryTheory.NatTrans

open CochainComplex Limits ZeroObject

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D]
  {F G : D ⥤ CochainComplex C ℤ} (τ : F ⟶ G)

/-- For a natural transformation `τ : F ⟶ G` of functors with values in cochain complexes, the
sequence `G ⟶ cone τ ⟶ cone (F ⟶ 0)` of functors: objectwise, the inclusion of `G` in the mapping
cone, followed by the map of mapping cones which forgets the summand `G`. -/
@[expose, simps]
noncomputable def mappingConeInrShortComplex : ShortComplex (D ⥤ CochainComplex C ℤ) where
  X₁ := G
  X₂ := mappingConeFunctor τ
  X₃ := mappingConeFunctor (0 : F ⟶ 0)
  f :=
    { app X := mappingCone.inr (τ.app X)
      naturality X X' f := by
        have key : G.map f ≫ mappingCone.inr (τ.app X') =
            mappingCone.inr (τ.app X) ≫
              mappingCone.map (τ.app X) (τ.app X') (F.map f) (G.map f) (τ.naturality f).symm := by
          ext n
          simp
        exact key }
  g :=
    { app X := mappingCone.map (τ.app X) ((0 : F ⟶ 0).app X) (𝟙 _) 0 (by simp)
      naturality X X' f := by
        have key :
            mappingCone.map (τ.app X) (τ.app X') (F.map f) (G.map f) (τ.naturality f).symm ≫
              mappingCone.map (τ.app X') ((0 : F ⟶ 0).app X') (𝟙 _) 0 (by simp) =
            mappingCone.map (τ.app X) ((0 : F ⟶ 0).app X) (𝟙 _) 0 (by simp) ≫
              mappingCone.map ((0 : F ⟶ 0).app X) ((0 : F ⟶ 0).app X') (F.map f)
                ((0 : D ⥤ CochainComplex C ℤ).map f) (by simp) := by
          rw [← mappingCone.map_comp, ← mappingCone.map_comp]
          congr 1 <;> simp
        exact key }
  zero := by
    ext X : 2
    have key : mappingCone.inr (τ.app X) ≫
        mappingCone.map (τ.app X) ((0 : F ⟶ 0).app X) (𝟙 _) 0 (by simp) = 0 := by
      ext n
      simp
    exact key

/-- For a natural transformation `τ : F ⟶ G` of functors with values in cochain complexes, the
sequence `G ⟶ cone τ ⟶ cone (F ⟶ 0)` of functors is short exact: objectwise it is the short exact
sequence `CochainComplex.mappingCone.shortExact_inrShortComplex`. -/
lemma shortExact_mappingConeInrShortComplex : (mappingConeInrShortComplex τ).ShortExact :=
  ShortComplex.shortExact_of_forall_evaluation _ fun X ↦
    mappingCone.shortExact_inrShortComplex (τ.app X) ((0 : F ⟶ 0).app X)
      ((isZero_zero _).obj X)

end CategoryTheory.NatTrans
