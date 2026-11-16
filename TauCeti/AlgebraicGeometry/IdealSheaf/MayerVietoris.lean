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
(`Scheme.IdealSheafData.pushforwardSubschemeMap`): this is restriction of functions from `V(I)` to
the smaller closed subscheme `V(J)`.

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

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.6 and the proof of Theorem III.5.2 (the
  exact sequence `0 → 𝒪_{Y ∪ Z} → 𝒪_Y ⊕ 𝒪_Z → 𝒪_{Y ∩ Z} → 0` of closed subschemes).
* [The Stacks Project, Lemma 33.4.6, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J): the
  scheme-theoretic union of two closed subschemes.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The direct image `ι_* 𝒪_{V(I)}` on `X` of the structure sheaf of the closed subscheme
`V(I)`. -/
abbrev pushforwardSubscheme : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)

variable (X) in
/-- The structure sheaf `𝒪_X` as an object of `X.Modules`. -/
private abbrev unitModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` of regular functions to the closed subscheme `V(I)`, as
a morphism of `𝒪_X`-modules. -/
private def toPushforwardSubscheme : unitModule X ⟶ I.pushforwardSubscheme :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- A regular function restricts to zero on `V(I)` exactly when it is a section of `I`. -/
@[simp]
private lemma toPushforwardSubscheme_app_eq_zero_iff {U : X.Opens} {s : Γ(X, U)} :
    Scheme.Modules.Hom.app I.toPushforwardSubscheme U s = 0 ↔ s ∈ I.sections U :=
  I.subschemeι_app_eq_zero_iff

/-- The exact sequence `0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0` of the closed subscheme `V(I)`. -/
private lemma shortExact_sheafι_toPushforwardSubscheme :
    (ShortComplex.mk (C := X.Modules) (X₂ := unitModule X) I.sheafι I.toPushforwardSubscheme
      I.sheafι_toPushforwardSubscheme).ShortExact :=
  I.shortExact_toPushforwardSubscheme

private instance : Epi I.toPushforwardSubscheme :=
  I.shortExact_sheafι_toPushforwardSubscheme.epi_g

/-- The inclusion `I ⟶ 𝒪_X`, with target the structure sheaf as an object of `X.Modules`. -/
private abbrev sheafι' : I.sheaf ⟶ unitModule X := I.sheafι

variable {I J}

/-! ### Restriction to a smaller closed subscheme -/

/-- For `I ≤ J`, a section of `I` restricts to zero on `V(J)`. -/
@[reassoc (attr := simp)]
private lemma sheafι_comp_toPushforwardSubscheme_of_le (h : I ≤ J) :
    I.sheafι' ≫ J.toPushforwardSubscheme = 0 :=
  Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦
    (J.toPushforwardSubscheme_app_eq_zero_iff).mpr (sections_mono h U (I.sheafι_app_mem U t))

/-- For `I ≤ J`, the restriction `ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(J)}` of functions on `V(I)` to the
smaller closed subscheme `V(J)`. It is the morphism through which the restriction
`𝒪_X ⟶ ι_* 𝒪_{V(J)}` factors (`toPushforwardSubscheme_pushforwardSubschemeMap`). -/
def pushforwardSubschemeMap (h : I ≤ J) : I.pushforwardSubscheme ⟶ J.pushforwardSubscheme :=
  (CokernelCofork.IsColimit.desc' I.shortExact_sheafι_toPushforwardSubscheme.gIsCokernel
    J.toPushforwardSubscheme (sheafι_comp_toPushforwardSubscheme_of_le h)).1

/-- Restricting functions from `X` to `V(I)` and then to `V(J)` is restricting them to `V(J)`. -/
@[reassoc (attr := simp)]
private lemma toPushforwardSubscheme_pushforwardSubschemeMap (h : I ≤ J) :
    I.toPushforwardSubscheme ≫ pushforwardSubschemeMap h = J.toPushforwardSubscheme :=
  (CokernelCofork.IsColimit.desc' I.shortExact_sheafι_toPushforwardSubscheme.gIsCokernel
    J.toPushforwardSubscheme (sheafι_comp_toPushforwardSubscheme_of_le h)).2

/-- The restriction `ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(J)}` is an epimorphism. -/
instance epi_pushforwardSubschemeMap (h : I ≤ J) : Epi (pushforwardSubschemeMap h) :=
  have : Epi (I.toPushforwardSubscheme ≫ pushforwardSubschemeMap h) := by
    rw [toPushforwardSubscheme_pushforwardSubschemeMap]
    infer_instance
  epi_of_epi I.toPushforwardSubscheme _

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

/-- Over an affine open the sections of `I ⊔ J` are sums of sections of `I` and of `J`, so the sum
map `I ⊞ J ⟶ I ⊔ J` is an epimorphism. -/
private lemma epi_sumToSup : Epi (sumToSup (I := I) (J := J)) := by
  refine Scheme.Modules.Hom.epi_of_surjective_on_affineOpens _ fun U hU t ↦ ?_
  have hsec : (I ⊔ J).sections U = I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ :=
    (I ⊔ J).sections_eq_ideal ⟨U, hU⟩
  obtain ⟨u, hu⟩ : ∃ u : Γ(X, U), u = Scheme.Modules.Hom.app (I ⊔ J).sheafι U t := ⟨_, rfl⟩
  have ht : u ∈ I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ := hsec ▸ hu ▸ (I ⊔ J).sheafι_app_mem U t
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ht
  have ha : a ∈ I.sections U := (I.sections_eq_ideal ⟨U, hU⟩).symm ▸ ha
  have hb : b ∈ J.sections U := (J.sections_eq_ideal ⟨U, hU⟩).symm ▸ hb
  refine ⟨Scheme.Modules.Hom.app (biprod.inl : I.sheaf ⟶ I.sheaf ⊞ J.sheaf) U (I.sectionMk a ha) +
    Scheme.Modules.Hom.app (biprod.inr : J.sheaf ⟶ I.sheaf ⊞ J.sheaf) U (J.sectionMk b hb), ?_⟩
  apply (I ⊔ J).sheafι_app_injective U
  have hl := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U (I.sectionMk a ha))
    (inl_sumToSup_sheafι (I := I) (J := J))
  have hr := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U (J.sectionMk b hb))
    (inr_sumToSup_sheafι (I := I) (J := J))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hl hr
  rw [map_add, map_add, hl, hr]
  exact (congrArg₂ (· + ·) (I.sheafι_app_sectionMk a ha) (J.sheafι_app_sectionMk b hb)).trans
    (hab.trans hu)

/-- A regular function restricting to zero on `V(I)` and on `V(J)` restricts to zero on
`V(I ⊓ J)`. -/
private lemma toPushforwardSubscheme_inf_eq_zero {T : X.Modules} (x : T ⟶ unitModule X)
    (hI : x ≫ I.toPushforwardSubscheme = 0) (hJ : x ≫ J.toPushforwardSubscheme = 0) :
    x ≫ (I ⊓ J).toPushforwardSubscheme = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  have hI' : Scheme.Modules.Hom.app (x ≫ I.toPushforwardSubscheme) U t = 0 := by rw [hI]; rfl
  have hJ' : Scheme.Modules.Hom.app (x ≫ J.toPushforwardSubscheme) U t = 0 := by rw [hJ]; rfl
  have hIJ : Scheme.Modules.Hom.app x U t ∈ (I ⊓ J).sections U := by
    rw [sections_inf]
    exact ⟨I.toPushforwardSubscheme_app_eq_zero_iff.mp hI',
      J.toPushforwardSubscheme_app_eq_zero_iff.mp hJ'⟩
  exact ((I ⊓ J).toPushforwardSubscheme_app_eq_zero_iff.mpr hIJ).trans rfl

variable (I J) in
/-- **The Mayer–Vietoris sequence of two closed subschemes**
`ι_* 𝒪_{V(I ⊓ J)} ⟶ ι_* 𝒪_{V(I)} ⊞ ι_* 𝒪_{V(J)} ⟶ ι_* 𝒪_{V(I ⊔ J)}`, whose maps are the
restrictions of functions, with a sign on `ι_* 𝒪_{V(J)}` in the first map. -/
abbrev mayerVietoris : ShortComplex X.Modules where
  f := biprod.lift (pushforwardSubschemeMap inf_le_left) (-pushforwardSubschemeMap inf_le_right)
  g := biprod.desc (pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J))
    (pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J))
  zero := by
    rw [← cancel_epi (I ⊓ J).toPushforwardSubscheme]
    simp

/-- A regular function vanishing on `V(I ⊔ J)` is, after refining its source, a sum of a section of
`I` and a section of `J`. -/
private lemma exists_eq_add_of_comp_toPushforwardSubscheme_sup_eq_zero {A : X.Modules}
    (y : A ⟶ unitModule X) (hy : y ≫ (I ⊔ J).toPushforwardSubscheme = 0) :
    ∃ (A' : X.Modules) (π : A' ⟶ A) (_ : Epi π) (c : A' ⟶ I.sheaf) (e : A' ⟶ J.sheaf),
      π ≫ y = c ≫ I.sheafι' + e ≫ J.sheafι' := by
  have hS := (I ⊔ J).shortExact_sheafι_toPushforwardSubscheme
  have := hS.mono_f
  have := epi_sumToSup (I := I) (J := J)
  -- `y` is a section of `I ⊔ J`, which is a sum after refinement since `I ⊞ J ⟶ I ⊔ J` is epi.
  obtain ⟨A', π, _, d, hd⟩ := surjective_up_to_refinements_of_epi sumToSup (hS.exact.lift _ hy)
  refine ⟨A', π, inferInstance, d ≫ biprod.fst, d ≫ biprod.snd, ?_⟩
  have h := hd =≫ (I ⊔ J).sheafι'
  rw [Category.assoc, hS.exact.lift_f, Category.assoc] at h
  rw [Category.assoc, Category.assoc]
  calc π ≫ y = d ≫ sumToSup ≫ (I ⊔ J).sheafι' := h
    _ = d ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ sumToSup ≫
        (I ⊔ J).sheafι' := by rw [biprod.total, Category.id_comp]
    _ = _ := by
      rw [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.assoc,
        inl_sumToSup_sheafι, inr_sumToSup_sheafι]

variable (I J)

/-- The first map of the Mayer–Vietoris sequence is a monomorphism: a function vanishing on `V(I)`
and on `V(J)` vanishes on `V(I ⊓ J)`. -/
private lemma mono_mayerVietoris_f : Mono (mayerVietoris I J).f := by
  refine Preadditive.mono_of_cancel_zero _ fun {T} h hh ↦ ?_
  -- Restate the types through the definition of `mayerVietoris`.
  change T ⟶ (I ⊓ J).pushforwardSubscheme at h
  have hh : h ≫ biprod.lift (pushforwardSubschemeMap inf_le_left)
      (-pushforwardSubschemeMap inf_le_right) = 0 := hh
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
  have : Epi (biprod.inl ≫ biprod.desc (pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J))
      (pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J))) := by
    rw [biprod.inl_desc]
    infer_instance
  exact epi_of_epi biprod.inl _

/-- The Mayer–Vietoris sequence is exact in the middle. -/
private lemma exact_mayerVietoris : (mayerVietoris I J).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  -- Restate the types through the definition of `mayerVietoris`.
  change A ⟶ I.pushforwardSubscheme ⊞ J.pushforwardSubscheme at x₂
  have hx₂ : x₂ ≫ biprod.desc (pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J))
      (pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J)) = 0 := hx₂
  -- Lift both components of `x₂` to `𝒪_X` after refining `A`.
  obtain ⟨A₁, π₁, _, a, ha⟩ :=
    surjective_up_to_refinements_of_epi I.toPushforwardSubscheme (x₂ ≫ biprod.fst)
  obtain ⟨A₂, π₂, _, b, hb⟩ :=
    surjective_up_to_refinements_of_epi J.toPushforwardSubscheme (π₁ ≫ x₂ ≫ biprod.snd)
  -- The sum of the lifts vanishes on `V(I ⊔ J)`, so it is a section of `I ⊔ J` ...
  have hx₂' : x₂ ≫ biprod.fst ≫ pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J) +
      x₂ ≫ biprod.snd ≫ pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J) = 0 := by
    refine Eq.trans ?_ hx₂
    rw [biprod.desc_eq]
    exact (Preadditive.comp_add _ _ _ _ _ _).symm
  have e₁ : a ≫ (I ⊔ J).toPushforwardSubscheme =
      π₁ ≫ x₂ ≫ biprod.fst ≫ pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J) := by
    rw [← toPushforwardSubscheme_pushforwardSubschemeMap (le_sup_left : I ≤ I ⊔ J),
      ← Category.assoc a, ← ha, Category.assoc, Category.assoc]
  have e₂ : b ≫ (I ⊔ J).toPushforwardSubscheme =
      π₂ ≫ π₁ ≫ x₂ ≫ biprod.snd ≫ pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J) := by
    rw [← toPushforwardSubscheme_pushforwardSubschemeMap (le_sup_right : J ≤ I ⊔ J),
      ← Category.assoc b, ← hb]
    rw [Category.assoc, Category.assoc, Category.assoc]
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
  -- `(mayerVietoris I J).f` is the lift of the two restrictions.
  change (π₃ ≫ π₂ ≫ π₁) ≫ x₂ = _ ≫ biprod.lift (pushforwardSubschemeMap inf_le_left)
    (-pushforwardSubschemeMap inf_le_right)
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, toPushforwardSubscheme_pushforwardSubschemeMap,
      Preadditive.sub_comp]
    rw [ha, sheafι_comp_toPushforwardSubscheme_of_le le_rfl, comp_zero, sub_zero]
  · rw [hb']
    simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_neg,
      toPushforwardSubscheme_pushforwardSubschemeMap, Preadditive.sub_comp]
    rw [hb, sheafι_comp_toPushforwardSubscheme_of_le le_rfl, comp_zero, neg_zero, zero_sub, neg_neg]

/-- **The Mayer–Vietoris sequence of two closed subschemes is short exact**:
`0 ⟶ ι_* 𝒪_{V(I ⊓ J)} ⟶ ι_* 𝒪_{V(I)} ⊞ ι_* 𝒪_{V(J)} ⟶ ι_* 𝒪_{V(I ⊔ J)} ⟶ 0`. -/
theorem shortExact_mayerVietoris : (mayerVietoris I J).ShortExact where
  mono_f := mono_mayerVietoris_f I J
  epi_g := epi_mayerVietoris_g I J
  exact := exact_mayerVietoris I J

end

end AlgebraicGeometry.Scheme.IdealSheafData
