/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The Mayer–Vietoris sequence of two closed subschemes

Let `I` and `J` be ideal sheaves on a scheme `X`. The closed subschemes `V(I)` and `V(J)` have the
union `V(I ⊓ J)` and the intersection `V(I ⊔ J)`. Write `𝒪_{V(I)}` for the direct image on `X` of
the structure sheaf of `V(I)`; it is the quotient `𝒪_X ⧸ I`
(`Scheme.IdealSheafData.shortExact_toPushforwardSubscheme`). For `I ≤ J` the restriction
`𝒪_X ⟶ 𝒪_{V(J)}` kills `I`, so it factors through `𝒪_{V(I)}`
(`Scheme.IdealSheafData.pushforwardSubschemeMap`, characterized by
`Scheme.IdealSheafData.toPushforwardSubscheme_pushforwardSubschemeMap`): this is restriction of
functions from `V(I)` to the smaller closed subscheme `V(J)`.

The restrictions give the sequence

`0 ⟶ 𝒪_{V(I ⊓ J)} ⟶ 𝒪_{V(I)} ⊞ 𝒪_{V(J)} ⟶ 𝒪_{V(I ⊔ J)} ⟶ 0`

(`Scheme.IdealSheafData.mayerVietoris`), with a sign on `𝒪_{V(J)}` in the first map, and it is
short exact (`Scheme.IdealSheafData.shortExact_mayerVietoris`). A function vanishing on `V(I)` and
on `V(J)` vanishes on `V(I ⊓ J)`, since the sections of `I ⊓ J` are those of both `I` and `J`
(`Scheme.IdealSheafData.sections_inf`); this makes the first map a monomorphism. Exactness in the
middle and at the end comes from the sections of `I ⊔ J` over an affine open, which are sums of
sections of `I` and of `J`. The proof works with morphisms up to refinements of their sources, as
in an arbitrary abelian category.

This is the sequence through which Euler characteristics, and so degrees of line bundles, on a
union of closed subschemes are computed from those on the pieces and on their intersection. No
hypothesis on `X`, `I` or `J` is needed.

## References

* [The Stacks Project, Lemma 33.4.6, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J): the
  scheme-theoretic union `Y ∪ Z` of two closed subschemes and the short exact sequence
  `0 → 𝒪_{Y ∪ Z} → 𝒪_Y × 𝒪_Z → 𝒪_{Y ∩ Z} → 0`.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The inclusion `I ⟶ 𝒪_X` as a morphism of `X.Modules`. `I.sheafι` is a morphism of
`SheafOfModules X.ringCatSheaf`, whose category structure is not reducibly that of `X.Modules`.
Stated with `I.sheafι`, the sums of composites below find no `Add` instance on morphisms, and `rw`
does not match the composites with morphisms of `X.Modules` such as `toPushforwardSubscheme`. -/
private abbrev sheafι' : I.sheaf ⟶ Scheme.Modules.unit X := I.sheafι

variable {I J}

/-! ### Restriction to a smaller closed subscheme -/

/-- For `I ≤ J`, the restriction `ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(J)}` of functions on `V(I)` to the
smaller closed subscheme `V(J)`. It is the morphism through which the restriction
`𝒪_X ⟶ ι_* 𝒪_{V(J)}` factors (`toPushforwardSubscheme_pushforwardSubschemeMap`). -/
def pushforwardSubschemeMap (h : I ≤ J) : I.pushforwardSubscheme ⟶ J.pushforwardSubscheme :=
  (CokernelCofork.IsColimit.desc' I.shortExact_toPushforwardSubscheme.gIsCokernel
    J.toPushforwardSubscheme (sheafι_toPushforwardSubscheme_of_le h)).val

/-- Restricting functions from `X` to `V(I)` and then to `V(J)` is restricting them to `V(J)`. -/
@[reassoc (attr := simp)]
lemma toPushforwardSubscheme_pushforwardSubschemeMap (h : I ≤ J) :
    I.toPushforwardSubscheme ≫ pushforwardSubschemeMap h = J.toPushforwardSubscheme :=
  (CokernelCofork.IsColimit.desc' I.shortExact_toPushforwardSubscheme.gIsCokernel
    J.toPushforwardSubscheme (sheafι_toPushforwardSubscheme_of_le h)).property

/-- The restriction `ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(J)}` is an epimorphism. -/
instance epi_pushforwardSubschemeMap (h : I ≤ J) : Epi (pushforwardSubschemeMap h) :=
  have : Epi (I.toPushforwardSubscheme ≫ pushforwardSubschemeMap h) := by
    rw [toPushforwardSubscheme_pushforwardSubschemeMap]
    infer_instance
  epi_of_epi I.toPushforwardSubscheme _

variable (I) in
/-- Restricting functions from `V(I)` to `V(I)` is the identity. -/
@[simp]
lemma pushforwardSubschemeMap_refl : pushforwardSubschemeMap (le_refl I) = 𝟙 _ := by
  rw [← cancel_epi I.toPushforwardSubscheme, toPushforwardSubscheme_pushforwardSubschemeMap,
    Category.comp_id]

/-- Restriction from `V(I)` to `V(J)` and then to `V(K)` is restriction to `V(K)`. -/
@[reassoc (attr := simp)]
lemma pushforwardSubschemeMap_comp {K : X.IdealSheafData} (h : I ≤ J) (h' : J ≤ K) :
    pushforwardSubschemeMap h ≫ pushforwardSubschemeMap h' =
      pushforwardSubschemeMap (h.trans h') := by
  rw [← cancel_epi I.toPushforwardSubscheme, toPushforwardSubscheme_pushforwardSubschemeMap_assoc,
    toPushforwardSubscheme_pushforwardSubschemeMap, toPushforwardSubscheme_pushforwardSubschemeMap]

/-! ### The Mayer–Vietoris sequence -/

/-- The sum map `I ⊞ J ⟶ I ⊔ J` of the inclusions. -/
private def sumToSup : I.sheaf ⊞ J.sheaf ⟶ (I ⊔ J).sheaf :=
  biprod.desc ((I ⊔ J).sheafLift I.sheafι fun U s ↦
      sections_mono le_sup_left U (I.sheafι_app_mem U s))
    ((I ⊔ J).sheafLift J.sheafι fun U s ↦ sections_mono le_sup_right U (J.sheafι_app_mem U s))

private lemma inl_sumToSup_sheafι :
    biprod.inl ≫ sumToSup ≫ (I ⊔ J).sheafι' = I.sheafι' :=
  (biprod.inl_desc_assoc _ _ _).trans ((I ⊔ J).sheafLift_ι _ _)

private lemma inr_sumToSup_sheafι :
    biprod.inr ≫ sumToSup ≫ (I ⊔ J).sheafι' = J.sheafι' :=
  (biprod.inr_desc_assoc _ _ _).trans ((I ⊔ J).sheafLift_ι _ _)

private lemma sumToSup_sheafι :
    sumToSup ≫ (I ⊔ J).sheafι' = biprod.fst ≫ I.sheafι' + biprod.snd ≫ J.sheafι' := by
  rw [← biprod.desc_eq]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [inl_sumToSup_sheafι, biprod.inl_desc]
  · rw [inr_sumToSup_sheafι, biprod.inr_desc]

/-- Over an affine open the sections of `I ⊔ J` are sums of sections of `I` and of `J`, so the sum
map `I ⊞ J ⟶ I ⊔ J` is an epimorphism. -/
private lemma epi_sumToSup : Epi (sumToSup (I := I) (J := J)) := by
  refine Scheme.Modules.Hom.epi_of_surjective_on_affineOpens _ fun U hU t ↦ ?_
  -- On the affine open `U` the section `t` of `I ⊔ J` is a sum of sections of `I` and of `J`.
  have ht : _ ∈ I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ :=
    (SetLike.ext_iff.mp ((I ⊔ J).sections_eq_ideal ⟨U, hU⟩) _).mp ((I ⊔ J).sheafι_app_mem U t)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ht
  rw [← I.sections_eq_ideal ⟨U, hU⟩] at ha
  rw [← J.sections_eq_ideal ⟨U, hU⟩] at hb
  refine ⟨Scheme.Modules.Hom.app (biprod.inl : I.sheaf ⟶ I.sheaf ⊞ J.sheaf) U (I.sectionMk a ha) +
    Scheme.Modules.Hom.app (biprod.inr : J.sheaf ⟶ I.sheaf ⊞ J.sheaf) U (J.sectionMk b hb), ?_⟩
  apply (I ⊔ J).sheafι_app_injective U
  have hl : Scheme.Modules.Hom.app (biprod.inl ≫ sumToSup ≫ (I ⊔ J).sheafι') U (I.sectionMk a ha) =
      Scheme.Modules.Hom.app I.sheafι' U (I.sectionMk a ha) := by
    rw [inl_sumToSup_sheafι]
  have hr : Scheme.Modules.Hom.app (biprod.inr ≫ sumToSup ≫ (I ⊔ J).sheafι') U (J.sectionMk b hb) =
      Scheme.Modules.Hom.app J.sheafι' U (J.sectionMk b hb) := by
    rw [inr_sumToSup_sheafι]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hl hr
  rw [map_add, map_add, hl, hr, sheafι_app_sectionMk, sheafι_app_sectionMk]
  exact hab

/-- A regular function restricting to zero on `V(I)` and on `V(J)` restricts to zero on
`V(I ⊓ J)`. -/
private lemma toPushforwardSubscheme_inf_eq_zero {T : X.Modules} (x : T ⟶ Scheme.Modules.unit X)
    (hI : x ≫ I.toPushforwardSubscheme = 0) (hJ : x ≫ J.toPushforwardSubscheme = 0) :
    x ≫ (I ⊓ J).toPushforwardSubscheme = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  have hI' := ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U) hI) t
  have hJ' := ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U) hJ) t
  -- Evaluate the composites and the zero morphisms on `t`.
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_comp,
    AddCommGrpCat.hom_zero, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.zero_apply] at hI' hJ' ⊢
  refine (I ⊓ J).subschemeι_app_eq_zero_iff.mpr ?_
  rw [sections_inf]
  exact ⟨I.subschemeι_app_eq_zero_iff.mp hI', J.subschemeι_app_eq_zero_iff.mp hJ'⟩

variable (I J) in
/-- **The Mayer–Vietoris sequence of two closed subschemes**
`ι_* 𝒪_{V(I ⊓ J)} ⟶ ι_* 𝒪_{V(I)} ⊞ ι_* 𝒪_{V(J)} ⟶ ι_* 𝒪_{V(I ⊔ J)}`, whose maps are the
restrictions of functions, with a sign on `ι_* 𝒪_{V(J)}` in the first map. -/
@[expose] def mayerVietoris : ShortComplex X.Modules where
  f := biprod.lift (pushforwardSubschemeMap inf_le_left) (-pushforwardSubschemeMap inf_le_right)
  g := biprod.desc (pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J))
    (pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J))
  zero := by
    rw [← cancel_epi (I ⊓ J).toPushforwardSubscheme]
    simp

variable (I J) in
/-- The first term of the Mayer–Vietoris sequence is `ι_* 𝒪_{V(I ⊓ J)}`. -/
@[simp]
lemma mayerVietoris_X₁ : (mayerVietoris I J).X₁ = (I ⊓ J).pushforwardSubscheme :=
  rfl

variable (I J) in
/-- The middle term of the Mayer–Vietoris sequence is `ι_* 𝒪_{V(I)} ⊞ ι_* 𝒪_{V(J)}`. -/
@[simp]
lemma mayerVietoris_X₂ :
    (mayerVietoris I J).X₂ = (I.pushforwardSubscheme ⊞ J.pushforwardSubscheme) :=
  rfl

variable (I J) in
/-- The last term of the Mayer–Vietoris sequence is `ι_* 𝒪_{V(I ⊔ J)}`. -/
@[simp]
lemma mayerVietoris_X₃ : (mayerVietoris I J).X₃ = (I ⊔ J).pushforwardSubscheme :=
  rfl

variable (I J) in
/-- The first map of the Mayer–Vietoris sequence is the lift of the two restrictions. -/
@[simp]
lemma mayerVietoris_f : (mayerVietoris I J).f =
    biprod.lift (pushforwardSubschemeMap inf_le_left) (-pushforwardSubschemeMap inf_le_right) :=
  rfl

variable (I J) in
/-- The second map of the Mayer–Vietoris sequence is the sum of the two restrictions. -/
@[simp]
lemma mayerVietoris_g : (mayerVietoris I J).g =
    biprod.desc (pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J))
      (pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J)) :=
  rfl

/-- A regular function vanishing on `V(I ⊔ J)` is, after refining its source, a sum of a section of
`I` and a section of `J`. -/
private lemma exists_eq_add_of_comp_toPushforwardSubscheme_sup_eq_zero {A : X.Modules}
    (y : A ⟶ Scheme.Modules.unit X) (hy : y ≫ (I ⊔ J).toPushforwardSubscheme = 0) :
    ∃ (A' : X.Modules) (π : A' ⟶ A) (_ : Epi π) (c : A' ⟶ I.sheaf) (e : A' ⟶ J.sheaf),
      π ≫ y = c ≫ I.sheafι' + e ≫ J.sheafι' := by
  have hS := (I ⊔ J).shortExact_toPushforwardSubscheme
  have := hS.mono_f
  have := epi_sumToSup (I := I) (J := J)
  -- `y` is a section of `I ⊔ J`, which is a sum after refinement since `I ⊞ J ⟶ I ⊔ J` is epi.
  obtain ⟨A', π, _, d, hd⟩ := surjective_up_to_refinements_of_epi sumToSup (hS.exact.lift _ hy)
  refine ⟨A', π, inferInstance, d ≫ biprod.fst, d ≫ biprod.snd, ?_⟩
  have h := hd =≫ (I ⊔ J).sheafι'
  rw [Category.assoc, hS.exact.lift_f, Category.assoc, sumToSup_sheafι] at h
  simpa only [Category.assoc, Preadditive.comp_add] using h

variable (I J)

/-- The first map of the Mayer–Vietoris sequence is a monomorphism: a function vanishing on `V(I)`
and on `V(J)` vanishes on `V(I ⊓ J)`. -/
private lemma mono_mayerVietoris_f : Mono (mayerVietoris I J).f := by
  dsimp only [mayerVietoris_X₁, mayerVietoris_X₂, mayerVietoris_f]
  refine Preadditive.mono_of_cancel_zero _ fun {T} h hh ↦ ?_
  -- Lift `h` to `𝒪_X` after a refinement of its source.
  obtain ⟨T', π, _, x, hx⟩ :=
    surjective_up_to_refinements_of_epi (I ⊓ J).toPushforwardSubscheme h
  rw [← cancel_epi π, comp_zero, hx]
  have h₁ := π ≫= hh =≫ biprod.fst
  have h₂ := π ≫= hh =≫ biprod.snd
  simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, Preadditive.comp_neg, zero_comp,
    comp_zero, neg_eq_zero] at h₁ h₂
  rw [← Category.assoc, hx, Category.assoc, toPushforwardSubscheme_pushforwardSubschemeMap]
    at h₁ h₂
  exact toPushforwardSubscheme_inf_eq_zero x h₁ h₂

/-- The second map of the Mayer–Vietoris sequence is an epimorphism. -/
private lemma epi_mayerVietoris_g : Epi (mayerVietoris I J).g := by
  dsimp only [mayerVietoris_X₂, mayerVietoris_X₃, mayerVietoris_g]
  have : Epi (biprod.inl ≫ biprod.desc (pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J))
      (pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J))) := by
    rw [biprod.inl_desc]
    infer_instance
  exact epi_of_epi biprod.inl _

/-- The Mayer–Vietoris sequence is exact in the middle. -/
private lemma exact_mayerVietoris : (mayerVietoris I J).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  dsimp only [mayerVietoris_X₁, mayerVietoris_X₂, mayerVietoris_X₃, mayerVietoris_f,
    mayerVietoris_g]
  intro A x₂ hx₂
  -- Lift both components of `x₂` to `𝒪_X` after refining `A`.
  obtain ⟨A₁, π₁, _, a, ha⟩ :=
    surjective_up_to_refinements_of_epi I.toPushforwardSubscheme (x₂ ≫ biprod.fst)
  obtain ⟨A₂, π₂, _, b, hb⟩ :=
    surjective_up_to_refinements_of_epi J.toPushforwardSubscheme (π₁ ≫ x₂ ≫ biprod.snd)
  -- The sum of the lifts vanishes on `V(I ⊔ J)`, so it is a section of `I ⊔ J` ...
  have hx₂' : x₂ ≫ biprod.fst ≫ pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J) +
      x₂ ≫ biprod.snd ≫ pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J) = 0 := by
    rw [← Preadditive.comp_add, ← biprod.desc_eq]
    exact hx₂
  have e₁ : a ≫ (I ⊔ J).toPushforwardSubscheme =
      π₁ ≫ x₂ ≫ biprod.fst ≫ pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J) := by
    rw [reassoc_of% ha, toPushforwardSubscheme_pushforwardSubschemeMap]
  have e₂ : b ≫ (I ⊔ J).toPushforwardSubscheme =
      π₂ ≫ π₁ ≫ x₂ ≫ biprod.snd ≫ pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J) := by
    rw [reassoc_of% hb, toPushforwardSubscheme_pushforwardSubschemeMap]
  have hab : (π₂ ≫ a + b) ≫ (I ⊔ J).toPushforwardSubscheme = 0 := by
    rw [Preadditive.add_comp, Category.assoc, e₁, e₂]
    simpa only [Category.assoc, Preadditive.comp_add, comp_zero] using π₂ ≫= π₁ ≫= hx₂'
  -- ... and, after a further refinement, a sum of a section of `I` and a section of `J`.
  obtain ⟨A₃, π₃, _, c, e, hce⟩ := exists_eq_add_of_comp_toPushforwardSubscheme_sup_eq_zero _ hab
  rw [Preadditive.comp_add] at hce
  refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance,
    (π₃ ≫ π₂ ≫ a - c ≫ I.sheafι') ≫ (I ⊓ J).toPushforwardSubscheme, ?_⟩
  have hb' : π₃ ≫ π₂ ≫ a - c ≫ I.sheafι' = e ≫ J.sheafι' - π₃ ≫ b := by
    rw [sub_eq_sub_iff_add_eq_add, hce, add_comm]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, toPushforwardSubscheme_pushforwardSubschemeMap,
      Preadditive.sub_comp]
    rw [ha, sheafι_toPushforwardSubscheme_of_le le_rfl, comp_zero, sub_zero]
  · rw [hb']
    simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_neg,
      toPushforwardSubscheme_pushforwardSubschemeMap, Preadditive.sub_comp]
    rw [hb, sheafι_toPushforwardSubscheme_of_le le_rfl, comp_zero, neg_zero, zero_sub, neg_neg]

/-- **The Mayer–Vietoris sequence of two closed subschemes is short exact**:
`0 ⟶ ι_* 𝒪_{V(I ⊓ J)} ⟶ ι_* 𝒪_{V(I)} ⊞ ι_* 𝒪_{V(J)} ⟶ ι_* 𝒪_{V(I ⊔ J)} ⟶ 0`. -/
theorem shortExact_mayerVietoris : (mayerVietoris I J).ShortExact where
  mono_f := mono_mayerVietoris_f I J
  epi_g := epi_mayerVietoris_g I J
  exact := exact_mayerVietoris I J

end

end AlgebraicGeometry.Scheme.IdealSheafData
