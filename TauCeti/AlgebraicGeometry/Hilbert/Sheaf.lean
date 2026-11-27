/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Hilbert.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Gluing
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The Hilbert functor is a Zariski sheaf

Compatible finite locally free closed families glue through their defining ideal sheaves.
Finiteness and flatness are local on the parameter scheme, and the degree is preserved
under pullback. Thus the Hilbert functor satisfies the Zariski sheaf condition on schemes
over an arbitrary base.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Hilbert

variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)

private lemma compatible_idealSheaves {T : Over S} {ι : Type*} {Z : ι → Over S}
    (g : ∀ i, Z i ⟶ T) (x : ∀ i, (hilbertFunctor f d).obj (op (Z i)))
    (hx : ∀ i j (W : Over S) (a : W ⟶ Z i) (b : W ⟶ Z j),
      a ≫ g i = b ≫ g j →
        (hilbertFunctor f d).map a.op (x i) = (hilbertFunctor f d).map b.op (x j))
    (i j : ι) {W : Scheme.{u}} (a : W ⟶ pullback (Z i).hom f)
    (b : W ⟶ pullback (Z j).hom f)
    (hab : a ≫ ((Over.pullback f).map (g i)).left =
      b ≫ ((Over.pullback f).map (g j)).left) :
    (x i).val.comap a = (x j).val.comap b := by
  have hfst {A B : Over S} (c : A ⟶ B) :
      ((Over.pullback f).map c).left ≫ pullback.fst B.hom f =
        pullback.fst A.hom f ≫ c.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hsnd {A B : Over S} (c : A ⟶ B) :
      ((Over.pullback f).map c).left ≫ pullback.snd B.hom f = pullback.snd A.hom f := by
    simp only [Over.pullback_map_left, pullback.lift_snd]
  have hab₁ : (a ≫ pullback.fst (Z i).hom f) ≫ (g i).left =
      (b ≫ pullback.fst (Z j).hom f) ≫ (g j).left := by
    simpa only [Category.assoc, hfst] using congrArg (· ≫ pullback.fst T.hom f) hab
  have hab₂ : a ≫ pullback.snd (Z i).hom f = b ≫ pullback.snd (Z j).hom f := by
    simpa only [Category.assoc, hsnd] using congrArg (· ≫ pullback.snd T.hom f) hab
  have hW : (a ≫ pullback.fst (Z i).hom f) ≫ (Z i).hom =
      (b ≫ pullback.fst (Z j).hom f) ≫ (Z j).hom := by
    simpa only [Category.assoc, Over.w] using congrArg (· ≫ T.hom) hab₁
  let V : Over S := Over.mk ((a ≫ pullback.fst (Z i).hom f) ≫ (Z i).hom)
  let a' : V ⟶ Z i := Over.homMk (a ≫ pullback.fst (Z i).hom f)
  let b' : V ⟶ Z j := Over.homMk (b ≫ pullback.fst (Z j).hom f) hW.symm
  have hcomm : a' ≫ g i = b' ≫ g j := Over.OverMorphism.ext hab₁
  have key := congrArg Subtype.val (hx i j V a' b' hcomm)
  simp only [hilbertFunctor_map_val] at key
  let s : W ⟶ pullback V.hom f := pullback.lift (𝟙 W)
    (a ≫ pullback.snd (Z i).hom f) (by simp [V, Category.assoc, pullback.condition])
  have hs₁ : s ≫ ((Over.pullback f).map a').left = a := by
    apply pullback.hom_ext <;> simp [s, a', Over.pullback_map_left]
  have hs₂ : s ≫ ((Over.pullback f).map b').left = b := by
    apply pullback.hom_ext
    · simp [s, b', Over.pullback_map_left]
    · simpa only [Category.assoc, hsnd, s, pullback.lift_snd] using hab₂
  rw [← hs₁, ← hs₂, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  exact congrArg (Scheme.IdealSheafData.comap · s) key

/-- Hilbert families satisfy the sheaf condition for every jointly surjective family of
open immersions of test schemes. -/
theorem isSheafFor_hilbertFunctor_ofArrows (T : Over S) {ι : Type*} {Z : ι → Over S}
    (g : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (g i).left]
    (hcover : ∀ t : T.left, ∃ i z, (g i).left z = t) :
    Presieve.IsSheafFor (hilbertFunctor f d) (Presieve.ofArrows Z g) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let b (i : ι) := ((Over.pullback f).map (g i)).left
  have H (i : ι) :
      IsPullback (pullback.fst (Z i).hom f) (b i) (g i).left (pullback.fst T.hom f) :=
    (Over.isPullback_pullback_map_left f (g i)).flip
  have hb (i : ι) : IsOpenImmersion (b i) :=
    MorphismProperty.of_isPullback (H i) (inferInstanceAs (IsOpenImmersion (g i).left))
  have hbasecover : ⨆ i, ((g i).left).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro t _
    obtain ⟨i, z, rfl⟩ := hcover t
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, z, rfl⟩
  have hbcover : ⨆ i, (b i).opensRange = ⊤ := by
    calc
      (⨆ i, (b i).opensRange) =
          ⨆ i, (pullback.fst T.hom f) ⁻¹ᵁ ((g i).left).opensRange := by
        congr 1
        funext i
        exact (Scheme.preimage_opensRange_of_isPullback (H i)).symm
      _ = ⊤ := (pullback.fst T.hom f).iSup_preimage_eq_top hbasecover
  obtain ⟨J, hJ, huniq⟩ :=
    Scheme.IdealSheafData.existsUnique_comap_eq_of_isOpenImmersion b hbcover
      (fun i ↦ (x i).val) (compatible_idealSheaves f d g x hx)
  have hdegree : J.IsFiniteLocallyFreeOfDegree (pullback.fst T.hom f) d :=
    Scheme.IdealSheafData.IsFiniteLocallyFreeOfDegree.of_openCover f d g hcover J fun i ↦ by
      rw [hJ i]
      exact (mem_hilbertSubfunctor_obj_iff _ _).mp (x i).property
  refine ⟨⟨J, (mem_hilbertSubfunctor_obj_iff _ _).mpr hdegree⟩,
    fun i ↦ Subtype.ext (hJ i), ?_⟩
  intro other hother
  apply Subtype.ext
  exact huniq other.val fun i ↦ congrArg Subtype.val (hother i)

/-- Finite locally free closed subschemes of fixed degree form a sheaf on the big Zariski
site over the base scheme. -/
theorem isSheaf_zariskiTopology_hilbertFunctor :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (hilbertFunctor f d) := by
  rw [isSheaf_iff_isSheaf_of_type, Scheme.zariskiTopology, Scheme.grothendieckTopology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget,
    ← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck, Presieve.isSheaf_pretopology]
  intro T R hR
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  simp only [Precoverage.toPretopology_toPrecoverage, Precoverage.mem_comap_iff,
    Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff, Over.forget_map] at hR
  obtain ⟨hsurj, hopen⟩ := hR
  have (i : ι) : IsOpenImmersion (g i).left := hopen i
  exact isSheafFor_hilbertFunctor_ofArrows f d T g hsurj

end AlgebraicGeometry.Hilbert
