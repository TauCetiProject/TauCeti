/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category
public import TauCeti.AlgebraicGeometry.DualNumber

/-!
# Infinitesimal automorphisms of prestable maps

Let `F` be a prestable map to `q : V ⟶ S` and let `p : T ⟶ S` be a morphism with a section
`i : S ⟶ T`. Base change along `i` undoes base change along `p`, so a morphism `F_T ⟶ G_T` between
base changes along `p` *restricts* along `i` to a morphism `F ⟶ G`. On total spaces, the
restriction of `f` is the unique morphism `g` with `g ≫ ι = ι ≫ f`, where `ι : C ⟶ C ×_S T` is the
inclusion of the total space over the section. Restriction is functorial and is a left inverse of
base change along `p`.

In particular every automorphism of `F_T = F.pullback p` restricts to an automorphism of `F`.
Restriction is a surjective group homomorphism `Aut F_T →* Aut F`, split by base change along
`p`. Its kernel consists of the automorphisms of `F_T` that restrict to the identity of `F`, and

`Aut F_T ≃* ker ⋊ Aut F`.

For `S = Spec R`, base change along `Spec R[ε] ⟶ Spec R` with the section `ε ↦ 0` gives the
**infinitesimal automorphisms** of `F`: the automorphisms of the trivial first-order deformation
`F_{R[ε]}` of `F` that reduce to the identity modulo `ε`. Being automorphisms of a prestable map,
they fix every marking and commute with the map to the target. Over an algebraically closed field,
these are the infinitesimal automorphisms of stable-map theory: a stable map has finitely many
automorphisms, and, under a generic separability hypothesis, no infinitesimal ones.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackSectionι`: the inclusion `C ⟶ C ×_S T` of the
  total space of `F` over the section of `p`.
* `TauCeti.AlgebraicGeometry.PrestableMap.restrictHom`: restriction of morphisms of base changes
  along the section.
* `TauCeti.AlgebraicGeometry.PrestableMap.restrictAut`: restriction of automorphisms of `F_T`
  along the section.
* `TauCeti.AlgebraicGeometry.PrestableMap.autPullbackExtension`,
  `TauCeti.AlgebraicGeometry.PrestableMap.autPullbackSplitting`: `Aut F_T` as a split extension
  of `Aut F` by the kernel of restriction.
* `TauCeti.AlgebraicGeometry.PrestableMap.autPullbackMulEquiv`: the resulting decomposition of
  `Aut F_T` as a semidirect product.
* `TauCeti.AlgebraicGeometry.PrestableMap.infinitesimalAut`: the infinitesimal automorphisms of
  a prestable map over `Spec R`.

## Main results

* `TauCeti.AlgebraicGeometry.PrestableMap.restrictHom_eq_iff`,
  `TauCeti.AlgebraicGeometry.PrestableMap.restrictAut_eq_iff`: the restriction is characterized by
  compatibility with `ι`.
* `TauCeti.AlgebraicGeometry.PrestableMap.restrictHom_pullbackMap`,
  `TauCeti.AlgebraicGeometry.PrestableMap.restrictAut_pullbackAut`: restriction is a left inverse
  of base change along `p`.
* `TauCeti.AlgebraicGeometry.PrestableMap.mem_ker_restrictAut_iff`: an automorphism of `F_T`
  restricts to the identity exactly when it fixes the total space of `F` along `ι`.
* `TauCeti.AlgebraicGeometry.PrestableMap.mem_infinitesimalAut_iff`: the same description of
  infinitesimal automorphisms.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, for automorphisms and infinitesimal automorphisms of prestable
  maps.
* R. Hartshorne, *Deformation Theory*, Graduate Texts in Mathematics 257, Springer, 2010,
  Chapter 1, for first-order deformations over the dual numbers.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V S T : Scheme.{u}} {q : V ⟶ S} {n : ℕ} {p : T ⟶ S}

/-! ### The inclusion over the section -/

section SectionInclusion

variable (F : PrestableMap q n) (h : SplitEpi p)

/-- The inclusion `C ⟶ C ×_S T` of the total space of `F` into the total space of its base
change along `p`, over the section of `p`: its projections are `𝟙 C` and `π ≫ i`, where `π` is the
structure morphism of `F` and `i` the section. -/
def pullbackSectionι : F.curve.total ⟶ (F.pullback p).curve.total :=
  -- The ascription presents the total space of the base change as the chosen pullback.
  (Limits.pullback.lift (𝟙 F.curve.total) (F.curve.toBase ≫ h.section_) (by simp) :
    F.curve.total ⟶ Limits.pullback F.curve.toBase p)

@[simp, reassoc]
theorem pullbackSectionι_fst :
    F.pullbackSectionι h ≫ Limits.pullback.fst F.curve.toBase p = 𝟙 F.curve.total :=
  Limits.pullback.lift_fst _ _ _

@[simp, reassoc]
theorem pullbackSectionι_snd :
    F.pullbackSectionι h ≫ Limits.pullback.snd F.curve.toBase p = F.curve.toBase ≫ h.section_ :=
  Limits.pullback.lift_snd _ _ _

/-- The inclusion over the section is a split monomorphism, split by the first projection. -/
instance : IsSplitMono (F.pullbackSectionι h) :=
  .mk' ⟨Limits.pullback.fst F.curve.toBase p, F.pullbackSectionι_fst h⟩

/-- The inclusion over the section carries each marking of `F` to the section followed by the
corresponding marking of the base change. -/
@[reassoc (attr := simp)]
theorem marking_comp_pullbackSectionι (i : Fin n) :
    F.curve.marking i ≫ F.pullbackSectionι h = h.section_ ≫ (F.pullback p).curve.marking i := by
  dsimp only [pullbackSectionι, pullback, PointedPrestableFamily.pullback]
  apply Limits.pullback.hom_ext <;> simp [h.id_assoc]

end SectionInclusion

/-! ### Restriction of morphisms -/

section RestrictHom

variable {F G H : PrestableMap q n} (h : SplitEpi p)

/-- **Restriction along the section.** A morphism `f : F_T ⟶ G_T` of base changes along `p`
restricts, along the section of `p`, to a morphism `F ⟶ G`: on total spaces it is the composite
`C ⟶ C ×_S T ⟶ D ×_S T ⟶ D` of the inclusion over the section, `f` and the first projection. It
is characterized by `restrictHom_eq_iff`. -/
def restrictHom (f : F.pullback p ⟶ G.pullback p) : F ⟶ G where
  curve :=
    { hom := F.pullbackSectionι h ≫ f.curve.hom ≫ Limits.pullback.fst G.curve.toBase p
      hom_comp_toBase := by
        have hf := f.curve.hom_comp_toBase
        dsimp only [pullbackSectionι, pullback, PointedPrestableFamily.pullback] at hf ⊢
        simp [Limits.pullback.condition, reassoc_of% hf]
      marking_comp_hom i := by
        have hf := f.curve.marking_comp_hom i
        rw [marking_comp_pullbackSectionι_assoc]
        dsimp only [pullback, PointedPrestableFamily.pullback] at hf ⊢
        simp [reassoc_of% hf, h.id_assoc] }
  hom_comp_map := by
    have hf := congr($(f.hom_comp_map) ≫ Limits.pullback.fst q p)
    dsimp only [pullbackSectionι, pullback, PointedPrestableFamily.pullback] at hf ⊢
    simp only [Category.assoc, Limits.pullback.lift_fst] at hf ⊢
    rw [hf, Limits.pullback.lift_fst_assoc, Category.id_comp]

/-- The restriction of `f` agrees with `f` along the inclusions over the section. -/
@[reassoc]
theorem restrictHom_hom_comp_pullbackSectionι (f : F.pullback p ⟶ G.pullback p) :
    (restrictHom h f).curve.hom ≫ G.pullbackSectionι h = F.pullbackSectionι h ≫ f.curve.hom := by
  have hf := f.curve.hom_comp_toBase
  dsimp only [restrictHom, pullbackSectionι, pullback, PointedPrestableFamily.pullback] at hf ⊢
  apply Limits.pullback.hom_ext
  · simp
  · simp [Limits.pullback.condition_assoc, hf, reassoc_of% hf, h.id_assoc]

/-- **Characterization of the restriction.** The restriction of `f : F_T ⟶ G_T` is the unique
morphism `g : F ⟶ G` with `g ≫ ι = ι ≫ f` on total spaces, where `ι` denotes the inclusions over
the section. -/
theorem restrictHom_eq_iff (f : F.pullback p ⟶ G.pullback p) (g : F ⟶ G) :
    restrictHom h f = g ↔
      g.curve.hom ≫ G.pullbackSectionι h = F.pullbackSectionι h ≫ f.curve.hom := by
  refine ⟨?_, fun hg ↦ hom_ext (PointedPrestableFamily.hom_ext ?_)⟩
  · rintro rfl
    exact restrictHom_hom_comp_pullbackSectionι h f
  · rw [← cancel_mono (G.pullbackSectionι h), restrictHom_hom_comp_pullbackSectionι, hg]

@[simp]
theorem restrictHom_id : restrictHom h (𝟙 (F.pullback p)) = 𝟙 F := by
  simp [restrictHom_eq_iff]

@[simp]
theorem restrictHom_comp (f : F.pullback p ⟶ G.pullback p) (g : G.pullback p ⟶ H.pullback p) :
    restrictHom h (f ≫ g) = restrictHom h f ≫ restrictHom h g := by
  simp [restrictHom_eq_iff, restrictHom_hom_comp_pullbackSectionι,
    restrictHom_hom_comp_pullbackSectionι_assoc]

/-- Restriction along the section is a left inverse of base change along `p`. -/
@[simp]
theorem restrictHom_pullbackMap (f : F ⟶ G) : restrictHom h (pullbackMap p f) = f := by
  rw [restrictHom_eq_iff, pullbackMap_curve, PointedPrestableFamily.pullbackMap_hom]
  have hf := f.curve.hom_comp_toBase
  dsimp only [pullbackSectionι, pullback, PointedPrestableFamily.pullback]
  apply Limits.pullback.hom_ext <;> simp [reassoc_of% hf]

end RestrictHom

/-! ### Restriction of automorphisms -/

section RestrictAut

variable (F : PrestableMap q n) (h : SplitEpi p)

/-- **Restriction of automorphisms along the section**: an automorphism of the base change
`F.pullback p` restricts, along the section of `p`, to an automorphism of `F`. -/
def restrictAut : Aut (F.pullback p) →* Aut F where
  toFun e := .of
    { hom := restrictHom h e.asIso.hom
      inv := restrictHom h e.asIso.inv
      hom_inv_id := by rw [← restrictHom_comp, Iso.hom_inv_id, restrictHom_id]
      inv_hom_id := by rw [← restrictHom_comp, Iso.inv_hom_id, restrictHom_id] }
  map_one' := Aut.ext (Iso.ext (restrictHom_id h))
  map_mul' e e' := Aut.ext (Iso.ext (restrictHom_comp h _ _))

@[simp]
theorem restrictAut_apply_asIso_hom (e : Aut (F.pullback p)) :
    (F.restrictAut h e).asIso.hom = restrictHom h e.asIso.hom :=
  (rfl)

/-- The restriction of an automorphism `e` of `F.pullback p` is the unique automorphism `g` of
`F` with `g ≫ ι = ι ≫ e` on total spaces, where `ι` is the inclusion over the section. -/
theorem restrictAut_eq_iff (e : Aut (F.pullback p)) (g : Aut F) :
    F.restrictAut h e = g ↔
      g.asIso.hom.curve.hom ≫ F.pullbackSectionι h =
        F.pullbackSectionι h ≫ e.asIso.hom.curve.hom := by
  rw [← restrictHom_eq_iff, ← restrictAut_apply_asIso_hom]
  exact ⟨fun he ↦ he ▸ rfl, fun hg ↦ Aut.ext (Iso.ext hg)⟩

/-- Restriction along the section is a left inverse of base change along `p`. -/
@[simp]
theorem restrictAut_pullbackAut (g : Aut F) :
    F.restrictAut h (F.pullbackAut p g) = g :=
  Aut.ext (Iso.ext (by rw [restrictAut_apply_asIso_hom, pullbackAut_apply_asIso_hom,
    restrictHom_pullbackMap]))

/-- Every automorphism of `F` is the restriction of an automorphism of `F.pullback p`, namely of
its base change. -/
theorem restrictAut_surjective : Function.Surjective (F.restrictAut h) :=
  fun g ↦ ⟨_, F.restrictAut_pullbackAut h g⟩

/-- An automorphism of `F.pullback p` restricts to the identity of `F` exactly when it fixes the
total space of `F`, included over the section. -/
theorem mem_ker_restrictAut_iff (e : Aut (F.pullback p)) :
    e ∈ (F.restrictAut h).ker ↔
      F.pullbackSectionι h ≫ e.asIso.hom.curve.hom = F.pullbackSectionι h := by
  rw [MonoidHom.mem_ker, restrictAut_eq_iff, eq_comm]
  simp

/-! ### The semidirect product decomposition -/

/-- The automorphism group of `F.pullback p` is an extension of the automorphism group of `F` by
the automorphisms restricting to the identity along the section. -/
def autPullbackExtension :
    GroupExtension (F.restrictAut h).ker (Aut (F.pullback p)) (Aut F) where
  inl := (F.restrictAut h).ker.subtype
  rightHom := F.restrictAut h
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := F.restrictAut_surjective h

/-- The kernel inclusion of the automorphism extension is the subgroup inclusion. -/
@[simp]
theorem autPullbackExtension_inl :
    (F.autPullbackExtension h).inl = (F.restrictAut h).ker.subtype :=
  (rfl)

/-- The quotient map of the automorphism extension is restriction along the section. -/
@[simp]
theorem autPullbackExtension_rightHom :
    (F.autPullbackExtension h).rightHom = F.restrictAut h :=
  (rfl)

/-- Base change along `p` splits the extension `autPullbackExtension`. -/
def autPullbackSplitting : (F.autPullbackExtension h).Splitting where
  toMonoidHom := F.pullbackAut p
  rightInverse_rightHom := F.restrictAut_pullbackAut h

/-- The splitting homomorphism is base change of automorphisms. -/
@[simp]
theorem autPullbackSplitting_toMonoidHom :
    (F.autPullbackSplitting h).toMonoidHom = F.pullbackAut p :=
  (rfl)

/-- Applying the splitting is base change of an automorphism. -/
@[simp]
theorem autPullbackSplitting_apply (g : Aut F) :
    (F.autPullbackSplitting h) g = F.pullbackAut p g :=
  (rfl)

/-- The action on the restriction kernel is conjugation by the base-changed automorphism. -/
@[simp]
theorem autPullbackSplitting_conjAct_apply_coe (g : Aut F) (x : (F.restrictAut h).ker) :
    ((F.autPullbackSplitting h).conjAct g x : Aut (F.pullback p)) =
      F.pullbackAut p g * (x : Aut (F.pullback p)) * (F.pullbackAut p g)⁻¹ := by
  simpa only [GroupExtension.Splitting.conjAct, MonoidHom.comp_apply,
    MonoidHom.coe_ofClass, autPullbackSplitting_apply,
    autPullbackExtension_inl, Subgroup.subtype_apply] using
    (F.autPullbackExtension h).inl_conjAct_comm (e := F.pullbackAut p g) (n := x)

/-- The automorphism group of `F.pullback p` is the semidirect product of the automorphisms
restricting to the identity along the section and the base changes of the automorphisms of `F`,
which act by conjugation. -/
def autPullbackMulEquiv :
    (F.restrictAut h).ker ⋊[(F.autPullbackSplitting h).conjAct] Aut F ≃* Aut (F.pullback p) :=
  (F.autPullbackSplitting h).semidirectProductMulEquiv

@[simp]
theorem autPullbackMulEquiv_apply
    (x : (F.restrictAut h).ker ⋊[(F.autPullbackSplitting h).conjAct] Aut F) :
    F.autPullbackMulEquiv h x = x.left * F.pullbackAut p x.right :=
  (rfl)

end RestrictAut

/-! ### Infinitesimal automorphisms -/

section Infinitesimal

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {q : V ⟶ Spec (.of R)}

/-- The **infinitesimal automorphisms** of a prestable map `F` over `Spec R`: the automorphisms of
its base change along `Spec R[ε] ⟶ Spec R` to the dual numbers that reduce to the identity modulo
`ε`, that is, restrict to the identity of `F` along `ε ↦ 0`. As automorphisms of a prestable map,
they fix every marking and commute with the map to the target. -/
def infinitesimalAut (F : PrestableMap q n) :
    Subgroup (Aut (F.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))))) :=
  (F.restrictAut (dualNumberSplitEpi R)).ker

/-- An automorphism of the base change of `F` to the dual numbers is infinitesimal exactly when it
fixes the total space of `F`, included over `ε ↦ 0`. -/
theorem mem_infinitesimalAut_iff (F : PrestableMap q n)
    (e : Aut (F.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))))) :
    e ∈ F.infinitesimalAut ↔
      F.pullbackSectionι (dualNumberSplitEpi R) ≫ e.asIso.hom.curve.hom =
        F.pullbackSectionι (dualNumberSplitEpi R) :=
  F.mem_ker_restrictAut_iff _ e

end Infinitesimal

end PrestableMap

end TauCeti.AlgebraicGeometry
