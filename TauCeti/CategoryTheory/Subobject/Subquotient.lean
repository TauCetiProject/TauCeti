/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.Lattice
public import TauCeti.CategoryTheory.Subobject.Basic
public import TauCeti.CategoryTheory.Subobject.Image
public import TauCeti.CategoryTheory.Subobject.Limits
import TauCeti.CategoryTheory.Subobject.Pullback

/-!
# Subquotient presentations in abelian categories

A **subquotient presentation** of `X` in `A` (`TauCeti.SubquotientPresentation`) consists of
subobjects `B ≤ Z` of `A` and an isomorphism `cokernel (Subobject.ofLE B Z le) ≅ X`:

* `orderIso : Subobject X ≃o Set.Icc p.B p.Z` (`preimage` / `image`) preserves and reflects GLBs
  and LUBs of nonempty families (`isGLB_preimage_iff`, `isLUB_preimage_iff`).
* `comp` composes presentations strictly associatively and unitally (`comp_assoc`, `id_comp`,
  `comp_id`, `comp_preimage`).
* `mapInduced` constructs morphisms induced by `f : A ⟶ A'` preserving `Z` and `B`, functorially
  in `f` and composition (`mapInduced_id`, `mapInduced_comp`, `mapInduced_comp_presentation`,
  `mapInducedIso`).

## References

* Stacks Project, Tag 011M (Spectral sequences, cycles and boundaries as subobjects of an initial
  page).
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A presentation of `X` as a subquotient `Z / B` of `A`, given by subobjects `B ≤ Z` of `A` and
an isomorphism `cokernel (Subobject.ofLE B Z le) ≅ X`. -/
structure SubquotientPresentation (A X : C) where
  /-- The denominator subobject of `A`. -/
  B : Subobject A
  /-- The numerator subobject of `A`. -/
  Z : Subobject A
  /-- The inclusion `B ≤ Z` in `Subobject A`. -/
  le : B ≤ Z
  /-- The isomorphism identifying `Z / B` with `X`. -/
  iso : cokernel (Subobject.ofLE B Z le) ≅ X

namespace SubquotientPresentation

section Basic

variable {A X Y : C} (p : SubquotientPresentation A X)

/-- The canonical projection `Z ⟶ X` of a subquotient presentation. -/
noncomputable def π : (p.Z : C) ⟶ X := cokernel.π (Subobject.ofLE p.B p.Z p.le) ≫ p.iso.hom

instance : Epi p.π := by dsimp only [π]; infer_instance

@[reassoc (attr := simp)]
theorem ofLE_comp_π : Subobject.ofLE p.B p.Z p.le ≫ p.π = 0 := by simp [π]

/-- The cokernel cofork `B ⟶ Z ⟶ X` of a subquotient presentation is a colimit. -/
noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ p.π p.ofLE_comp_π) :=
  IsColimit.ofIsoColimit (cokernelIsCokernel (Subobject.ofLE p.B p.Z p.le))
    (Cofork.ext p.iso (by simp [π]))

theorem kernelSubobject_π : kernelSubobject p.π = Subobject.mk (Subobject.ofLE p.B p.Z p.le) := by
  rw [π, kernelSubobject_comp_mono, kernelSubobject_cokernel_π]

@[simp]
theorem map_kernelSubobject_π : (Subobject.map p.Z.arrow).obj (kernelSubobject p.π) = p.B := by
  rw [p.kernelSubobject_π, Subobject.map_mk_ofLE]

/-- A morphism out of `p.Z` that vanishes on `p.B` descends uniquely to `X`. -/
noncomputable def desc (f : (p.Z : C) ⟶ Y) (hf : Subobject.ofLE p.B p.Z p.le ≫ f = 0) : X ⟶ Y :=
  p.iso.inv ≫ cokernel.desc (Subobject.ofLE p.B p.Z p.le) f hf

@[reassoc (attr := simp)]
theorem π_desc (f : (p.Z : C) ⟶ Y) (hf : Subobject.ofLE p.B p.Z p.le ≫ f = 0) :
    p.π ≫ p.desc f hf = f := by simp [π, desc]

theorem hom_ext {g₁ g₂ : X ⟶ Y} (h : p.π ≫ g₁ = p.π ≫ g₂) : g₁ = g₂ := (cancel_epi p.π).mp h

/-- Two subquotient presentations of `X` in `A` are equal once they share `Z` and `π`. -/
@[ext (iff := false)]
theorem ext {p q : SubquotientPresentation A X} (hZ : p.Z = q.Z)
    (hπ : p.π = (Subobject.isoOfEq p.Z q.Z hZ).hom ≫ q.π) : p = q := by
  rcases p with ⟨B, Z, le, iso⟩; rcases q with ⟨B', Z', le', iso'⟩
  dsimp only at hZ hπ; subst hZ
  have hiso : (Subobject.isoOfEq Z Z rfl).hom = 𝟙 (Z : C) := by rw [← cancel_mono Z.arrow]; simp
  rw [hiso, Category.id_comp] at hπ
  have hB : B = B' := ((mk B Z le iso).map_kernelSubobject_π.symm.trans
    (congrArg (fun f ↦ (Subobject.map Z.arrow).obj (kernelSubobject f)) hπ)).trans
    (mk B' Z le' iso').map_kernelSubobject_π
  subst hB; congr 1; exact Iso.ext ((cancel_epi (cokernel.π (Subobject.ofLE B Z le))).mp hπ)

/-- The presented object `X` is zero if and only if the denominator equals the numerator. -/
theorem isZero_iff : IsZero X ↔ p.B = p.Z := by
  refine ⟨fun hX ↦ ?_, fun hBZ ↦ ?_⟩
  · rw [← p.map_kernelSubobject_π, hX.eq_of_tgt p.π 0, kernelSubobject_zero, Subobject.map_top,
      Subobject.mk_arrow]
  · have heq : Subobject.ofLE p.B p.Z p.le = (Subobject.isoOfEq p.B p.Z hBZ).hom := by
      rw [← cancel_mono p.Z.arrow]; simp
    have : IsIso (Subobject.ofLE p.B p.Z p.le) := heq ▸ inferInstance
    exact IsZero.of_iso (Limits.isZero_cokernel_of_epi _) p.iso.symm

end Basic

section Constructors

variable {A X Y Z' : C}

-- Constructors are `abbrev` so `.B` and `.Z` reduce at `reducible` transparency in dependent types.

/-- Construct a subquotient presentation from a cokernel colimit cocone `B ⟶ Z ⟶ X`. -/
noncomputable abbrev ofIsColimit {B Z : Subobject A} (h : B ≤ Z) (π : (Z : C) ⟶ X)
    (w : Subobject.ofLE B Z h ≫ π = 0) (hc : IsColimit (CokernelCofork.ofπ π w)) :
    SubquotientPresentation A X where
  B := B; Z := Z; le := h
  iso := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (Subobject.ofLE B Z h)) hc

@[simp]
theorem ofIsColimit_π {B Z : Subobject A} (h : B ≤ Z) (π : (Z : C) ⟶ X)
    (w : Subobject.ofLE B Z h ≫ π = 0) (hc : IsColimit (CokernelCofork.ofπ π w)) :
    (ofIsColimit h π w hc).π = π :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (Subobject.ofLE B Z h))
    hc WalkingParallelPair.one

section OfEpi

variable {B Z : Subobject A} (h : B ≤ Z) (π : (Z : C) ⟶ X) [Epi π]
  (hker : (Subobject.map Z.arrow).obj (kernelSubobject π) = B)

/-- The canonical isomorphism `Z / B ≅ X` induced by an epimorphism `π : Z ⟶ X` with kernel `B`. -/
noncomputable def ofEpiIso : cokernel (Subobject.ofLE B Z h) ≅ X := by
  have hk : kernelSubobject π = Subobject.mk (Subobject.ofLE B Z h) :=
    Subobject.map_obj_injective Z.arrow (by rw [hker, Subobject.map_mk_ofLE])
  let e : (B : C) ≅ kernel π :=
    (Subobject.underlyingIso _).symm ≪≫ (Subobject.isoOfEq _ _ hk).symm ≪≫ kernelSubobjectIso π
  have he : e.hom ≫ kernel.ι π = Subobject.ofLE B Z h := by simp [e]
  have hw : Subobject.ofLE B Z h ≫ π = 0 := by rw [← he, Category.assoc, kernel.condition]; simp
  exact (ofIsColimit h π hw (Abelian.epiIsCokernelOfKernel _ (IsLimit.ofIsoLimit
    (kernelIsKernel π) (Fork.ext (t := KernelFork.ofι (Subobject.ofLE B Z h) hw) e.symm (by
      dsimp only [Fork.ofι_pt, KernelFork.ι_ofι, Iso.symm_hom]
      rw [← he, Iso.inv_hom_id_assoc]; rfl))))).iso

/-- Construct a subquotient presentation from an epimorphism `π : Z ⟶ X` with kernel `B`. -/
noncomputable abbrev ofEpi : SubquotientPresentation A X where
  B := B; Z := Z; le := h; iso := ofEpiIso h π hker

@[simp]
theorem ofEpi_π : (ofEpi h π hker).π = π := by
  dsimp only [SubquotientPresentation.π, ofEpi, ofEpiIso, ofIsColimit]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (Subobject.ofLE B Z h))
    _ WalkingParallelPair.one

end OfEpi

/-- The tautological subquotient presentation of `cokernel (Subobject.ofLE B Z h)` in `A`. -/
noncomputable abbrev ofLE (B Z : Subobject A) (h : B ≤ Z) :
    SubquotientPresentation A (cokernel (Subobject.ofLE B Z h)) where
  B := B; Z := Z; le := h; iso := Iso.refl _

@[simp]
theorem ofLE_π (B Z : Subobject A) (h : B ≤ Z) :
    (ofLE B Z h).π = cokernel.π (Subobject.ofLE B Z h) := Category.comp_id _

/-- The canonical isomorphism `⊤ / ⊥ ≅ A` in `Subobject A`. -/
noncomputable def idIso (A : C) : cokernel (Subobject.ofLE (⊥ : Subobject A) ⊤ bot_le) ≅ A :=
  cokernelIsoOfEq ((IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero).eq_of_src _ 0) ≪≫
    cokernelZeroIsoTarget ≪≫ asIso (⊤ : Subobject A).arrow

/-- The trivial subquotient presentation `⊤ / ⊥ ≅ A` of an object `A` in itself. -/
noncomputable abbrev id (A : C) : SubquotientPresentation A A where
  B := ⊥; Z := ⊤; le := bot_le; iso := idIso A

@[simp]
theorem id_π (A : C) : (id A).π = (⊤ : Subobject A).arrow := by
  simp [π, id, idIso, cokernel.π_desc_assoc]

variable (p : SubquotientPresentation A X)

/-- Transport a subquotient presentation along an isomorphism of the presented object. -/
noncomputable abbrev transIso (e : X ≅ Y) : SubquotientPresentation A Y where
  B := p.B; Z := p.Z; le := p.le; iso := p.iso ≪≫ e

@[reassoc, simp]
theorem transIso_π (e : X ≅ Y) : (p.transIso e).π = p.π ≫ e.hom := by simp [π, transIso]

@[simp]
theorem transIso_refl : p.transIso (Iso.refl X) = p := ext rfl (by simp)

@[simp]
theorem transIso_trans (e₁ : X ≅ Y) (e₂ : Y ≅ Z') :
    (p.transIso e₁).transIso e₂ = p.transIso (e₁ ≪≫ e₂) := ext rfl (by simp)

end Constructors

section Lattice

variable {A X : C} (p : SubquotientPresentation A X)

/-- The preimage of a subobject `S` of `X` in `A`, lying in `Set.Icc p.B p.Z`. -/
noncomputable def preimage (S : Subobject X) : Subobject A :=
  (Subobject.map p.Z.arrow).obj ((Subobject.pullback p.π).obj S)

/-- The image of a subobject `T ≤ p.Z` of `A` in `X`. -/
noncomputable def image (T : Subobject A) (hT : T ≤ p.Z) : Subobject X :=
  imageSubobject (Subobject.ofLE T p.Z hT ≫ p.π)

theorem preimage_mono : Monotone p.preimage := fun _ _ h ↦
  (Subobject.map p.Z.arrow).monotone ((Subobject.pullback p.π).monotone h)

@[simp]
theorem preimage_bot : p.preimage ⊥ = p.B := by
  rw [preimage, Subobject.pullback_bot, p.map_kernelSubobject_π]

@[simp]
theorem preimage_top : p.preimage ⊤ = p.Z := by
  rw [preimage, Subobject.pullback_top, Subobject.map_top, Subobject.mk_arrow]

theorem le_preimage (S : Subobject X) : p.B ≤ p.preimage S :=
  p.preimage_bot ▸ p.preimage_mono bot_le

theorem preimage_le (S : Subobject X) : p.preimage S ≤ p.Z :=
  p.preimage_top ▸ p.preimage_mono le_top

theorem preimage_mem_Icc (S : Subobject X) : p.preimage S ∈ Set.Icc p.B p.Z :=
  ⟨p.le_preimage S, p.preimage_le S⟩

@[simp]
theorem transIso_preimage {Y : C} (e : X ≅ Y) (S : Subobject Y) :
    (p.transIso e).preimage S = p.preimage ((Subobject.pullback e.hom).obj S) := by
  rw [preimage, preimage, transIso_π, Subobject.pullback_comp]

@[simp]
theorem id_preimage (S : Subobject A) : (id A).preimage S = S := by
  rw [preimage, id_π]
  have hS : S = (Subobject.map (⊤ : Subobject A).arrow).obj
      ((Subobject.map (asIso (⊤ : Subobject A).arrow).inv).obj S) :=
    ((Subobject.mapIsoToOrderIso (asIso (⊤ : Subobject A).arrow)).apply_symm_apply S).symm
  conv_lhs => rw [hS]
  rw [Subobject.pullback_map_self]; exact hS.symm

/-- Adjunction between `image` and `preimage` for subobjects contained in `p.Z`. -/
theorem le_preimage_iff {T : Subobject A} (hT : T ≤ p.Z) {S : Subobject X} :
    T ≤ p.preimage S ↔ p.image T hT ≤ S := by
  conv_lhs => rw [← Subobject.map_mk_ofLE hT]
  rw [preimage, ← Subobject.exists_iso_map p.Z.arrow, Subobject.exists_le_exists_iff_of_mono,
    ← (Subobject.existsPullbackAdj p.π).gc.le_iff_le, Subobject.exists_mk_eq_imageSubobject, image]

theorem image_mono {T₁ T₂ : Subobject A} (h₁₂ : T₁ ≤ T₂) (h₂ : T₂ ≤ p.Z) :
    p.image T₁ (h₁₂.trans h₂) ≤ p.image T₂ h₂ :=
  (p.le_preimage_iff (h₁₂.trans h₂)).mp (h₁₂.trans ((p.le_preimage_iff h₂).mpr le_rfl))

@[simp]
theorem image_preimage (S : Subobject X) : p.image (p.preimage S) (p.preimage_le S) = S := by
  have hmk : Subobject.mk (Subobject.ofLE (p.preimage S) p.Z (p.preimage_le S)) =
      (Subobject.pullback p.π).obj S :=
    Subobject.map_obj_injective p.Z.arrow (by rw [Subobject.map_mk_ofLE, preimage])
  rw [image, ← Subobject.exists_mk_eq_imageSubobject, hmk, Subobject.exists_eq_imageSubobject,
    ← (Subobject.isPullback p.π S).w, imageSubobject_comp_eq_of_epi, imageSubobject_mono,
    Subobject.mk_arrow]

@[simp]
theorem preimage_image (T : Subobject A) (hB : p.B ≤ T) (hZ : T ≤ p.Z) :
    p.preimage (p.image T hZ) = T := by
  refine le_antisymm ?_ ((p.le_preimage_iff hZ).mpr le_rfl)
  let q := cokernel.π (Subobject.ofLE T p.Z hZ)
  have hq : Subobject.ofLE p.B p.Z p.le ≫ q = 0 := by
    rw [← Subobject.ofLE_comp_ofLE p.B T p.Z hB hZ, Category.assoc]; simp [q]
  have him : (p.image T hZ).arrow ≫ p.desc q hq = 0 :=
    imageSubobject_arrow_comp_eq_zero (by rw [Category.assoc, p.π_desc]; exact cokernel.condition _)
  refine ((Subobject.map p.Z.arrow).monotone ?_).trans_eq (Subobject.map_mk_ofLE hZ)
  rw [← kernelSubobject_cokernel_π (Subobject.ofLE T p.Z hZ)]
  exact le_kernelSubobject q _ (by
    rw [← p.π_desc q hq, ← Category.assoc, ← (Subobject.isPullback p.π (p.image T hZ)).w,
      Category.assoc, him, comp_zero])

@[simp]
theorem preimage_le_preimage_iff {S₁ S₂ : Subobject X} :
    p.preimage S₁ ≤ p.preimage S₂ ↔ S₁ ≤ S₂ := by
  rw [p.le_preimage_iff (p.preimage_le S₁), p.image_preimage]

theorem preimage_injective : Function.Injective p.preimage := fun _ _ h ↦
  le_antisymm (p.preimage_le_preimage_iff.mp h.le) (p.preimage_le_preimage_iff.mp h.ge)

@[simp]
theorem preimage_eq_Z_iff {S : Subobject X} : p.preimage S = p.Z ↔ S = ⊤ := by
  rw [← p.preimage_top, p.preimage_injective.eq_iff]

@[simp]
theorem preimage_eq_B_iff {S : Subobject X} : p.preimage S = p.B ↔ S = ⊥ := by
  rw [← p.preimage_bot, p.preimage_injective.eq_iff]

/-- The lattice correspondence `Subobject X ≃o Set.Icc p.B p.Z` for a subquotient presentation. -/
noncomputable def orderIso : Subobject X ≃o Set.Icc p.B p.Z where
  toFun S := ⟨p.preimage S, p.preimage_mem_Icc S⟩
  invFun T := p.image T.val T.property.2
  left_inv S := p.image_preimage S
  right_inv T := Subtype.ext (p.preimage_image T.val T.property.1 T.property.2)
  map_rel_iff' := p.preimage_le_preimage_iff

/-- `p.preimage` preserves and reflects GLBs of nonempty families in `Subobject A`. -/
theorem isGLB_preimage_iff {s : Set (Subobject X)} (hs : s.Nonempty) {m : Subobject X} :
    IsGLB (p.preimage '' s) (p.preimage m) ↔ IsGLB s m := by
  refine ⟨fun hm ↦ ⟨fun S hS ↦ p.preimage_le_preimage_iff.mp (hm.1 ⟨S, hS, rfl⟩),
      fun _ hy ↦ p.preimage_le_preimage_iff.mp
        (hm.2 fun _ ⟨_, hS, h⟩ ↦ h ▸ p.preimage_mono (hy hS))⟩,
    fun hm ↦ ⟨fun _ ⟨S, hS, h⟩ ↦ h ▸ p.preimage_mono (hm.1 hS), fun T hT ↦ ?_⟩⟩
  obtain ⟨S₀, hS₀⟩ := hs
  have hsupZ : T ⊔ p.B ≤ p.Z := sup_le ((hT ⟨S₀, hS₀, rfl⟩).trans (p.preimage_le S₀)) p.le
  exact le_sup_left.trans <| (p.preimage_image (T ⊔ p.B) le_sup_right hsupZ).symm.trans_le <|
    p.preimage_mono <| hm.2 fun S hS ↦
      (p.le_preimage_iff hsupZ).mp (sup_le (hT ⟨S, hS, rfl⟩) (p.le_preimage S))

/-- `p.preimage` preserves and reflects LUBs of nonempty families in `Subobject A`. -/
theorem isLUB_preimage_iff {s : Set (Subobject X)} (hs : s.Nonempty) {m : Subobject X} :
    IsLUB (p.preimage '' s) (p.preimage m) ↔ IsLUB s m := by
  refine ⟨fun hm ↦ ⟨fun S hS ↦ p.preimage_le_preimage_iff.mp (hm.1 ⟨S, hS, rfl⟩),
      fun _ hy ↦ p.preimage_le_preimage_iff.mp
        (hm.2 fun _ ⟨_, hS, h⟩ ↦ h ▸ p.preimage_mono (hy hS))⟩,
    fun hm ↦ ⟨fun _ ⟨S, hS, h⟩ ↦ h ▸ p.preimage_mono (hm.1 hS), fun T hT ↦ ?_⟩⟩
  obtain ⟨S₀, hS₀⟩ := hs
  have hBinf : p.B ≤ T ⊓ p.Z := le_inf ((p.le_preimage S₀).trans (hT ⟨S₀, hS₀, rfl⟩)) p.le
  exact (p.preimage_mono <| hm.2 fun S hS ↦ by
      rw [← p.preimage_le_preimage_iff, p.preimage_image (T ⊓ p.Z) hBinf inf_le_right]
      exact le_inf (hT ⟨S, hS, rfl⟩) (p.preimage_le S)).trans <|
    (p.preimage_image (T ⊓ p.Z) hBinf inf_le_right).trans_le inf_le_left

/-- Existence of a GLB for a nonempty family is preserved and reflected by `p.preimage`. -/
theorem exists_isGLB_preimage_iff {s : Set (Subobject X)} (hs : s.Nonempty) :
    (∃ M, IsGLB (p.preimage '' s) M) ↔ ∃ m, IsGLB s m :=
  ⟨fun ⟨M, hM⟩ ↦ let ⟨S₀, hS₀⟩ := hs
    have hMZ : M ≤ p.Z := (hM.1 ⟨S₀, hS₀, rfl⟩).trans (p.preimage_le S₀)
    ⟨p.image M hMZ, (p.isGLB_preimage_iff hs).mp <| by
      rwa [p.preimage_image M (hM.2 fun _ ⟨S, _, h⟩ ↦ h ▸ p.le_preimage S) hMZ]⟩,
   fun ⟨m, hm⟩ ↦ ⟨p.preimage m, (p.isGLB_preimage_iff hs).mpr hm⟩⟩

/-- Existence of a LUB for a nonempty family is preserved and reflected by `p.preimage`. -/
theorem exists_isLUB_preimage_iff {s : Set (Subobject X)} (hs : s.Nonempty) :
    (∃ M, IsLUB (p.preimage '' s) M) ↔ ∃ m, IsLUB s m :=
  ⟨fun ⟨M, hM⟩ ↦ let ⟨S₀, hS₀⟩ := hs
    have hMZ : M ≤ p.Z := hM.2 fun _ ⟨S, _, h⟩ ↦ h ▸ p.preimage_le S
    ⟨p.image M hMZ, (p.isLUB_preimage_iff hs).mp <| by
      rwa [p.preimage_image M ((p.le_preimage S₀).trans (hM.1 ⟨S₀, hS₀, rfl⟩)) hMZ]⟩,
   fun ⟨m, hm⟩ ↦ ⟨p.preimage m, (p.isLUB_preimage_iff hs).mpr hm⟩⟩

end Lattice

section Composition

variable {A X Y Z : C} (p : SubquotientPresentation A X)

private noncomputable def preimageIsoPullback (S : Subobject X) :
    (p.preimage S : C) ≅ ((Subobject.pullback p.π).obj S : C) :=
  Subobject.isoOfEq _ (Subobject.mk (((Subobject.pullback p.π).obj S).arrow ≫ p.Z.arrow))
    (by rw [preimage, ← Subobject.exists_iso_map, Subobject.exists_eq_mk_of_mono]) ≪≫
    Subobject.underlyingIso _

private theorem preimageIsoPullback_hom_comp_arrow (S : Subobject X) :
    (p.preimageIsoPullback S).hom ≫ ((Subobject.pullback p.π).obj S).arrow =
      Subobject.ofLE (p.preimage S) p.Z (p.preimage_le S) := by
  rw [← cancel_mono p.Z.arrow]; simp [preimageIsoPullback]

/-- Restriction of `p.π : p.Z ⟶ X` to `p.preimage S ⟶ S`, fitting in a pullback with `p.π`. -/
noncomputable def preimageπ (S : Subobject X) : (p.preimage S : C) ⟶ (S : C) :=
  (p.preimageIsoPullback S).hom ≫ Subobject.pullbackπ p.π S

instance (S : Subobject X) : Epi (p.preimageπ S) := by dsimp only [preimageπ]; infer_instance

@[reassoc (attr := simp)]
theorem preimageπ_comp_arrow (S : Subobject X) :
    p.preimageπ S ≫ S.arrow = Subobject.ofLE (p.preimage S) p.Z (p.preimage_le S) ≫ p.π := by
  rw [preimageπ, Category.assoc, (Subobject.isPullback p.π S).w,
    reassoc_of% (p.preimageIsoPullback_hom_comp_arrow S)]

theorem isPullback_preimageπ (S : Subobject X) :
    IsPullback (p.preimageπ S) (Subobject.ofLE (p.preimage S) p.Z (p.preimage_le S)) S.arrow p.π :=
  IsPullback.of_iso (Subobject.isPullback p.π S) (p.preimageIsoPullback S).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp [preimageπ])
    (by simp [← p.preimageIsoPullback_hom_comp_arrow S]) (by simp) (by simp)

@[reassoc]
theorem ofLE_comp_preimageπ {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    Subobject.ofLE (p.preimage S₁) (p.preimage S₂) (p.preimage_mono h) ≫ p.preimageπ S₂ =
      p.preimageπ S₁ ≫ Subobject.ofLE S₁ S₂ h := by rw [← cancel_mono S₂.arrow]; simp

/-- A subquotient `K / I` of `X` inherits a presentation in `A` as `p.preimage K / p.preimage I`. -/
noncomputable abbrev subquotient (I K : Subobject X) (hIK : I ≤ K) :
    SubquotientPresentation A (cokernel (Subobject.ofLE I K hIK)) :=
  ofEpi (p.preimage_mono hIK) (p.preimageπ K ≫ cokernel.π (Subobject.ofLE I K hIK)) (by
    rw [← Subobject.pullback_kernelSubobject, kernelSubobject_cokernel_π,
      Subobject.map_arrow_eq_map_ofLE (p.preimage_le K),
      Subobject.map_pullback (p.preimageπ_comp_arrow K) (p.isPullback_preimageπ K).isLimit,
      Subobject.map_mk_ofLE]; rfl)

@[reassoc]
theorem subquotient_π (I K : Subobject X) (hIK : I ≤ K) :
    (p.subquotient I K hIK).π = p.preimageπ K ≫ cokernel.π (Subobject.ofLE I K hIK) := ofEpi_π _ _ _

/-- Composition of subquotient presentations, with denominator `p.preimage q.B` and numerator
`p.preimage q.Z`. -/
noncomputable abbrev comp (q : SubquotientPresentation X Y) : SubquotientPresentation A Y :=
  (p.subquotient q.B q.Z q.le).transIso q.iso

@[reassoc]
theorem comp_π (q : SubquotientPresentation X Y) : (p.comp q).π = p.preimageπ q.Z ≫ q.π := by
  rw [transIso_π, subquotient_π_assoc, π]

theorem comp_preimage (q : SubquotientPresentation X Y) (S : Subobject Y) :
    (p.comp q).preimage S = p.preimage (q.preimage S) := by
  rw [preimage, comp_π, Subobject.pullback_comp, Subobject.map_arrow_eq_map_ofLE (p.preimage_le _),
    Subobject.map_pullback (p.preimageπ_comp_arrow q.Z) (p.isPullback_preimageπ q.Z).isLimit]; rfl

theorem comp_transIso (q : SubquotientPresentation X Y) (e : Y ≅ Z) :
    p.comp (q.transIso e) = (p.comp q).transIso e := ext rfl (by simp)

theorem comp_assoc (q : SubquotientPresentation X Y) (r : SubquotientPresentation Y Z) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  refine ext (p.comp_preimage q r.Z) ?_
  simp only [comp_π, ← Category.assoc]; congr 1; rw [← cancel_mono r.Z.arrow]
  simp only [Category.assoc, preimageπ_comp_arrow, comp_π]
  rw [← p.ofLE_comp_preimageπ_assoc (q.preimage_le r.Z),
    ← Category.assoc ((Subobject.isoOfEq _ _ _).hom)]
  exact congrArg (· ≫ p.preimageπ q.Z ≫ q.π) (by rw [← cancel_mono (p.preimage q.Z).arrow]; simp)

@[simp]
theorem id_comp : (id A).comp p = p := by
  refine ext (id_preimage p.Z) ?_
  rw [comp_π]; congr 1; rw [← cancel_mono p.Z.arrow]; simp [preimageπ_comp_arrow, id_π]

@[simp]
theorem comp_id : p.comp (id X) = p :=
  ext (by simp) (by rw [comp_π, id_π, preimageπ_comp_arrow]; congr 1)

/-- Two-step naturality of `subquotient` for nested subobjects `I ≤ I' ≤ K' ≤ K` of `X`. -/
theorem subquotient_twoStep {I I' K' K : Subobject X} (hI : I ≤ I') (hIK' : I' ≤ K') (hK : K' ≤ K) :
    let q := ofLE I K ((hI.trans hIK').trans hK)
    let I'' := q.image I' (hIK'.trans hK)
    let K'' := q.image K' hK
    (p.subquotient I K ((hI.trans hIK').trans hK)).subquotient I'' K'' (q.image_mono hIK' hK) =
      p.comp (q.subquotient I'' K'' (q.image_mono hIK' hK)) := by
  intro q I'' K''
  have hsub : ∀ {U V : C} (r : SubquotientPresentation U V) (S T : Subobject V) (h : S ≤ T),
      r.subquotient S T h = r.comp (ofLE S T h) := fun _ _ _ _ ↦ by simp [comp, ofLE]
  rw [hsub p, hsub (p.comp q), hsub q, comp_assoc]

end Composition

section MapInduced

variable {A A' A'' X X' X'' Y Y' : C}
  (p : SubquotientPresentation A X) (p' : SubquotientPresentation A' X')

/-- Lift a morphism `f : A ⟶ A'` to `p.Z ⟶ p'.Z` when `(Subobject.exists f).obj p.Z ≤ p'.Z`. -/
noncomputable def liftZ (f : A ⟶ A') (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z) :
    (p.Z : C) ⟶ (p'.Z : C) :=
  factorThruImageSubobject (p.Z.arrow ≫ f) ≫
    Subobject.ofLE _ p'.Z (by rwa [← Subobject.exists_eq_imageSubobject])

@[reassoc (attr := simp)]
theorem liftZ_comp_arrow (f : A ⟶ A') (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z) :
    p.liftZ p' f hZ ≫ p'.Z.arrow = p.Z.arrow ≫ f := by simp [liftZ]

/-- The morphism `X ⟶ X'` induced by `f : A ⟶ A'` sending `p.Z` to `p'.Z` and `p.B` to `p'.B`. -/
noncomputable def mapInduced (f : A ⟶ A') (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z)
    (hB : (Subobject.exists f).obj p.B ≤ p'.B) : X ⟶ X' :=
  p.desc (p.liftZ p' f hZ ≫ p'.π) (by
    let liftB : (p.B : C) ⟶ (p'.B : C) := factorThruImageSubobject (p.B.arrow ≫ f) ≫
      Subobject.ofLE _ p'.B (by rwa [← Subobject.exists_eq_imageSubobject])
    have hsq : Subobject.ofLE p.B p.Z p.le ≫ p.liftZ p' f hZ =
        liftB ≫ Subobject.ofLE p'.B p'.Z p'.le := by rw [← cancel_mono p'.Z.arrow]; simp [liftB]
    rw [reassoc_of% hsq, p'.ofLE_comp_π, comp_zero])

@[reassoc (attr := simp)]
theorem π_comp_mapInduced (f : A ⟶ A') (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z)
    (hB : (Subobject.exists f).obj p.B ≤ p'.B) :
    p.π ≫ p.mapInduced p' f hZ hB = p.liftZ p' f hZ ≫ p'.π := p.π_desc _ _

theorem mapInduced_unique (f : A ⟶ A') (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z)
    (hB : (Subobject.exists f).obj p.B ≤ p'.B) {g : X ⟶ X'}
    (hg : p.π ≫ g = p.liftZ p' f hZ ≫ p'.π) : g = p.mapInduced p' f hZ hB :=
  p.hom_ext (by rw [hg, p.π_comp_mapInduced])

/-- `mapInduced` is invariant under replacing the presentations or the morphism by equal ones. -/
theorem mapInduced_congr {p₁ p₂ : SubquotientPresentation A X}
    {p₁' p₂' : SubquotientPresentation A' X'} {f g : A ⟶ A'} (hp : p₁ = p₂) (hp' : p₁' = p₂')
    (hfg : f = g) (hZ₁ : (Subobject.exists f).obj p₁.Z ≤ p₁'.Z)
    (hB₁ : (Subobject.exists f).obj p₁.B ≤ p₁'.B) (hZ₂ : (Subobject.exists g).obj p₂.Z ≤ p₂'.Z)
    (hB₂ : (Subobject.exists g).obj p₂.B ≤ p₂'.B) :
    p₁.mapInduced p₁' f hZ₁ hB₁ = p₂.mapInduced p₂' g hZ₂ hB₂ := by subst hp hp' hfg; rfl

@[simp]
theorem mapInduced_id (hZ : (Subobject.exists (𝟙 A)).obj p.Z ≤ p.Z := by simp)
    (hB : (Subobject.exists (𝟙 A)).obj p.B ≤ p.B := by simp) :
    p.mapInduced p (𝟙 A) hZ hB = 𝟙 X := by
  have hlift : p.liftZ p (𝟙 A) hZ = 𝟙 (p.Z : C) := by rw [← cancel_mono p.Z.arrow]; simp
  exact (p.mapInduced_unique p (𝟙 A) hZ hB (by rw [hlift, Category.comp_id, Category.id_comp])).symm

@[simp]
theorem id_mapInduced_id (f : A ⟶ A') (hZ : (Subobject.exists f).obj (id A).Z ≤ (id A').Z)
    (hB : (Subobject.exists f).obj (id A).B ≤ (id A').B) :
    (id A).mapInduced (id A') f hZ hB = f :=
  ((id A).mapInduced_unique (id A') f hZ hB (by
    rw [id_π, id_π]; exact ((id A).liftZ_comp_arrow (id A') f hZ).symm)).symm

theorem mapInduced_comp (p'' : SubquotientPresentation A'' X'') (f : A ⟶ A') (g : A' ⟶ A'')
    (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z) (hB : (Subobject.exists f).obj p.B ≤ p'.B)
    (hZ' : (Subobject.exists g).obj p'.Z ≤ p''.Z) (hB' : (Subobject.exists g).obj p'.B ≤ p''.B) :
    p.mapInduced p'' (f ≫ g)
        ((Subobject.exists_comp f g p.Z).symm ▸ ((Subobject.exists g).monotone hZ).trans hZ')
        ((Subobject.exists_comp f g p.B).symm ▸ ((Subobject.exists g).monotone hB).trans hB') =
      p.mapInduced p' f hZ hB ≫ p'.mapInduced p'' g hZ' hB' :=
  (p.mapInduced_unique p'' (f ≫ g) _ _ (by
    rw [p.π_comp_mapInduced_assoc, p'.π_comp_mapInduced, ← Category.assoc]
    congr 1; rw [← cancel_mono p''.Z.arrow]; simp)).symm

theorem mapInduced_transIso (e : X ≅ Y) (e' : X' ≅ Y') (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z) (hB : (Subobject.exists f).obj p.B ≤ p'.B) :
    (p.transIso e).mapInduced (p'.transIso e') f hZ hB =
      e.inv ≫ p.mapInduced p' f hZ hB ≫ e'.hom :=
  ((p.transIso e).mapInduced_unique (p'.transIso e') f hZ hB (by
    rw [transIso_π_assoc, Iso.hom_inv_id_assoc, p.π_comp_mapInduced_assoc, transIso_π]; rfl)).symm

/-- Compatibility of `mapInduced` with preimages. -/
theorem exists_preimage_le_preimage_iff (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z) (hB : (Subobject.exists f).obj p.B ≤ p'.B)
    (S : Subobject X) (S' : Subobject X') :
    (Subobject.exists f).obj (p.preimage S) ≤ p'.preimage S' ↔
      (Subobject.exists (p.mapInduced p' f hZ hB)).obj S ≤ S' := by
  have hleZ' : (Subobject.exists f).obj (p.preimage S) ≤ p'.Z :=
    ((Subobject.exists f).monotone (p.preimage_le S)).trans hZ
  rw [p'.le_preimage_iff hleZ', image]
  conv_rhs => rw [Subobject.exists_eq_imageSubobject]
  let e₁ := factorThruImageSubobject ((p.preimage S).arrow ≫ f) ≫
    (Subobject.isoOfEq _ _ (Subobject.exists_eq_imageSubobject f (p.preimage S)).symm).hom
  have : Epi e₁ := by dsimp only [e₁]; infer_instance
  have hfac : e₁ ≫ Subobject.ofLE _ p'.Z hleZ' =
      Subobject.ofLE (p.preimage S) p.Z (p.preimage_le S) ≫ p.liftZ p' f hZ := by
    rw [← cancel_mono p'.Z.arrow]; simp [e₁]
  rw [← imageSubobject_comp_eq_of_epi e₁, reassoc_of% hfac, ← p.π_comp_mapInduced,
    ← Category.assoc, ← p.preimageπ_comp_arrow S, Category.assoc, imageSubobject_comp_eq_of_epi]

/-- Compatibility of `mapInduced` with composition of subquotient presentations. -/
theorem mapInduced_comp_presentation (q : SubquotientPresentation X Y)
    (q' : SubquotientPresentation X' Y') (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj p.Z ≤ p'.Z) (hB : (Subobject.exists f).obj p.B ≤ p'.B)
    (hZq : (Subobject.exists (p.mapInduced p' f hZ hB)).obj q.Z ≤ q'.Z)
    (hBq : (Subobject.exists (p.mapInduced p' f hZ hB)).obj q.B ≤ q'.B) :
    (p.comp q).mapInduced (p'.comp q') f
        ((p.exists_preimage_le_preimage_iff p' f hZ hB q.Z q'.Z).mpr hZq)
        ((p.exists_preimage_le_preimage_iff p' f hZ hB q.B q'.B).mpr hBq) =
      q.mapInduced q' (p.mapInduced p' f hZ hB) hZq hBq := by
  symm; refine (p.comp q).mapInduced_unique (p'.comp q') f _ _ ?_
  rw [comp_π_assoc, q.π_comp_mapInduced, comp_π, ← Category.assoc, ← Category.assoc]
  congr 1; rw [← cancel_mono q'.Z.arrow]
  simp only [Category.assoc, preimageπ_comp_arrow, liftZ_comp_arrow]
  have hlift : (p.comp q).liftZ (p'.comp q') f
        ((p.exists_preimage_le_preimage_iff p' f hZ hB q.Z q'.Z).mpr hZq) ≫
      Subobject.ofLE (p'.preimage q'.Z) p'.Z (p'.preimage_le q'.Z) =
      Subobject.ofLE (p.preimage q.Z) p.Z (p.preimage_le q.Z) ≫ p.liftZ p' f hZ := by
    rw [← cancel_mono p'.Z.arrow, Category.assoc, Category.assoc, Subobject.ofLE_arrow,
      liftZ_comp_arrow, liftZ_comp_arrow, Subobject.ofLE_arrow_assoc]
  rw [reassoc_of% hlift, ← p.π_comp_mapInduced p' f hZ hB, ← p.preimageπ_comp_arrow_assoc]

/-- An isomorphism `e : A ≅ A'` sending `p.Z` to `p'.Z` and `p.B` to `p'.B` induces `X ≅ X'`. -/
noncomputable def mapInducedIso (e : A ≅ A') (hZ : (Subobject.exists e.hom).obj p.Z = p'.Z)
    (hB : (Subobject.exists e.hom).obj p.B = p'.B) : X ≅ X' where
  hom := p.mapInduced p' e.hom hZ.le hB.le
  inv := p'.mapInduced p e.inv
    (by rw [← hZ, ← Subobject.exists_comp, e.hom_inv_id, Subobject.exists_id])
    (by rw [← hB, ← Subobject.exists_comp, e.hom_inv_id, Subobject.exists_id])
  hom_inv_id := by rw [← mapInduced_comp]; simp only [Iso.hom_inv_id]; exact p.mapInduced_id
  inv_hom_id := by rw [← mapInduced_comp]; simp only [Iso.inv_hom_id]; exact p'.mapInduced_id

@[simp]
theorem mapInducedIso_hom (e : A ≅ A') (hZ : (Subobject.exists e.hom).obj p.Z = p'.Z)
    (hB : (Subobject.exists e.hom).obj p.B = p'.B) :
    (p.mapInducedIso p' e hZ hB).hom = p.mapInduced p' e.hom hZ.le hB.le := by rfl

@[simp]
theorem mapInducedIso_inv (e : A ≅ A') (hZ : (Subobject.exists e.hom).obj p.Z = p'.Z)
    (hB : (Subobject.exists e.hom).obj p.B = p'.B) :
    (p.mapInducedIso p' e hZ hB).inv = p'.mapInduced p e.inv
      (by rw [← hZ, ← Subobject.exists_comp, e.hom_inv_id, Subobject.exists_id])
      (by rw [← hB, ← Subobject.exists_comp, e.hom_inv_id, Subobject.exists_id]) := by rfl

/-- Functoriality of `subquotient` under inclusions: for `I ≤ I'`, `I ≤ K'`, `K' ≤ K`, `I' ≤ K`,
the canonical map `K' / I ⟶ K / I'` coincides with the map induced by `𝟙 A`. -/
theorem subquotient_mapInduced_id {I I' K' K : Subobject X} (hI : I ≤ I') (hIK' : I ≤ K')
    (hI'K : I' ≤ K) (hK : K' ≤ K) :
    (p.subquotient I K' hIK').mapInduced (p.subquotient I' K hI'K) (𝟙 A)
        (by simpa using p.preimage_mono hK) (by simpa using p.preimage_mono hI) =
      cokernel.desc (Subobject.ofLE I K' hIK')
        (Subobject.ofLE K' K hK ≫ cokernel.π (Subobject.ofLE I' K hI'K))
        (by rw [Subobject.ofLE_comp_ofLE_assoc, ← Subobject.ofLE_comp_ofLE I I' K hI hI'K,
          Category.assoc, cokernel.condition, comp_zero]) :=
  ((p.subquotient I K' hIK').mapInduced_unique _ (𝟙 A) _ _ (by
    rw [subquotient_π_assoc, cokernel.π_desc, subquotient_π, ← p.ofLE_comp_preimageπ_assoc hK]
    congr 2
    rw [← cancel_mono (p.preimage K).arrow, Subobject.ofLE_arrow, liftZ_comp_arrow,
      Category.comp_id])).symm

end MapInduced

end SubquotientPresentation

end TauCeti
