/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import TauCeti.Algebra.Homology.TotalComplex.Homotopy
import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
import TauCeti.Algebra.Homology.TotalComplex.AcyclicAssembly

/-!
# Mapping cones and totalization

Totalizing the horizontal mapping cone gives the mapping cone of the total map. Thus a rowwise
quasi-isomorphism gives a quasi-isomorphism on totals whenever the mapping cone has finite
antidiagonals. The comparison is induced by the standard mapping-cone nullhomotopy through
`Homotopy.totalMap`; the quasi-isomorphism criterion then applies
`HomologicalComplex₂.acyclic_total_of_finite_antidiagonals` to the horizontal mapping cone.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : K ⟶ L)
  [HasHomotopyCofiber φ]

@[reassoc (attr := simp)]
private lemma coneTerm_inl_fst (p q : ℤ) :
    ((mappingCone.inl φ).v (p + 1) p (by omega)).f q ≫
      ((mappingCone.fst φ).val.v p (p + 1) rfl).f q = 𝟙 _ := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    HomologicalComplex.congr_hom (mappingCone.inl_v_fst_v φ (p + 1) p rfl) q

@[reassoc (attr := simp)]
private lemma coneTerm_inl_snd (p q : ℤ) :
    ((mappingCone.inl φ).v (p + 1) p (by omega)).f q ≫
      ((mappingCone.snd φ).v p p (add_zero p)).f q = 0 := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    HomologicalComplex.congr_hom (mappingCone.inl_v_snd_v φ (p + 1) p (by omega)) q

@[reassoc (attr := simp)]
private lemma coneTerm_inr_fst (p q : ℤ) :
    ((mappingCone.inr φ).f p).f q ≫
      ((mappingCone.fst φ).val.v p (p + 1) rfl).f q = 0 := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    HomologicalComplex.congr_hom (mappingCone.inr_f_fst_v φ p (p + 1) rfl) q

@[reassoc (attr := simp)]
private lemma coneTerm_inr_snd (p q : ℤ) :
    ((mappingCone.inr φ).f p).f q ≫
      ((mappingCone.snd φ).v p p (add_zero p)).f q = 𝟙 _ := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    HomologicalComplex.congr_hom (mappingCone.inr_f_snd_v φ p) q

private lemma coneTerm_ext (p q : ℤ) {A : C}
    {f g : ((mappingCone φ).X p).X q ⟶ A}
    (h₁ : ((mappingCone.inl φ).v (p + 1) p (by omega)).f q ≫ f =
      ((mappingCone.inl φ).v (p + 1) p (by omega)).f q ≫ g)
    (h₂ : ((mappingCone.inr φ).f p).f q ≫ f =
      ((mappingCone.inr φ).f p).f q ≫ g) : f = g := by
  have h := HomologicalComplex.congr_hom (mappingCone.id_X φ p (p + 1) rfl) q
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] at h
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = _ := by rw [← h, Preadditive.add_comp, Category.assoc, Category.assoc, h₁, h₂]
    _ = g := by rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, h,
      Category.id_comp]

private lemma isZero_coneTerm (p q : ℤ) (hK : IsZero ((K.X (p + 1)).X q))
    (hL : IsZero ((L.X p).X q)) : IsZero (((mappingCone φ).X p).X q) := by
  rw [IsZero.iff_id_eq_zero]
  have h := HomologicalComplex.congr_hom (mappingCone.id_X φ p (p + 1) rfl) q
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] at h
  rw [← h, hK.eq_of_tgt (((mappingCone.fst φ).val.v p (p + 1) rfl).f q) 0,
    hL.eq_of_tgt (((mappingCone.snd φ).v p p (add_zero p)).f q) 0]
  simp

/-- Horizontal mapping cones preserve finiteness of the support of every antidiagonal. -/
lemma finiteAntidiagonals_mappingCone
    (hK : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}.Finite)
    (hL : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((L.X p).X (n - p))}.Finite) (n : ℤ) :
    {p : ℤ | ¬ IsZero (((mappingCone φ).X p).X (n - p))}.Finite := by
  refine (((hK (n + 1)).preimage (f := fun p : ℤ ↦ p + 1)
    (by intro a _ b _ h; exact add_right_cancel h)).union (hL n)).subset ?_
  intro p hp
  by_contra h
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_not] at h
  apply hp
  apply isZero_coneTerm φ p (n - p) _ h.2
  have heq : n + 1 - (p + 1) = n - p := by omega
  simpa only [heq] using h.1

variable
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
  [HasTotal (mappingCone φ) (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (total.map φ (ComplexShape.up ℤ))]

private def totalConeHomotopy :
    Homotopy (total.map φ (ComplexShape.up ℤ) ≫
      total.map (mappingCone.inr φ) (ComplexShape.up ℤ)) 0 :=
  (Homotopy.ofEq (total.map_comp _ _ _).symm).trans
    (((mappingCone.inrCompHomotopy φ).totalMap (ComplexShape.up ℤ)).trans
      (Homotopy.ofEq (by ext n; simp)))

private def totalConeHom : mappingCone (total.map φ (ComplexShape.up ℤ)) ⟶
    HomologicalComplex₂.total (mappingCone φ) (ComplexShape.up ℤ) :=
  homotopyCofiber.desc _ (total.map (mappingCone.inr φ) (ComplexShape.up ℤ))
    (totalConeHomotopy φ)

@[reassoc (attr := simp)]
private lemma inr_totalConeHom (n : ℤ) :
    (mappingCone.inr (total.map φ (ComplexShape.up ℤ))).f n ≫ (totalConeHom φ).f n =
      (total.map (mappingCone.inr φ) (ComplexShape.up ℤ)).f n := by
  apply homotopyCofiber.inrX_desc_f

@[reassoc]
private lemma ι_inl_totalConeHom (p p' q n : ℤ) (hp : p' + 1 = p)
    (h : p + q = n + 1) :
    K.ιTotal (ComplexShape.up ℤ) p q (n + 1) h ≫
      (mappingCone.inl (total.map φ (ComplexShape.up ℤ))).v (n + 1) n (by omega) ≫
        (totalConeHom φ).f n =
      ((mappingCone.inl φ).v p p' (by omega)).f q ≫
        HomologicalComplex₂.ιTotal (mappingCone φ) (ComplexShape.up ℤ) p' q n
          (by dsimp; omega) := by
  have hinl : (mappingCone.inl (total.map φ (ComplexShape.up ℤ))).v
      (n + 1) n (by omega) ≫ (totalConeHom φ).f n =
        (totalConeHomotopy φ).hom (n + 1) n :=
    homotopyCofiber.inlX_desc_f _ _ _ _ _ (by simp)
  rw [hinl]
  simp only [totalConeHomotopy, Homotopy.trans, Homotopy.ofEq, zero_add, add_zero]
  rw [Homotopy.ι_totalMap_hom,
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk p' p hp),
    HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by dsimp; omega)]
  rw [mappingCone.inrCompHomotopy_hom φ p p' hp]
  simp [ComplexShape.ε₁_def]

private def totalConeInvX (n : ℤ) :
    (HomologicalComplex₂.total (mappingCone φ) (ComplexShape.up ℤ)).X n ⟶
      (mappingCone (total.map φ (ComplexShape.up ℤ))).X n :=
  HomologicalComplex₂.totalDesc (mappingCone φ) fun p q h ↦
    ((mappingCone.fst φ).val.v p (p + 1) rfl).f q ≫
      K.ιTotal (ComplexShape.up ℤ) (p + 1) q (n + 1) (by dsimp at h ⊢; omega) ≫
        (mappingCone.inl (total.map φ (ComplexShape.up ℤ))).v (n + 1) n (by omega) +
    ((mappingCone.snd φ).v p p (add_zero p)).f q ≫
      L.ιTotal (ComplexShape.up ℤ) p q n h ≫
        (mappingCone.inr (total.map φ (ComplexShape.up ℤ))).f n

private lemma totalConeHom_isIso_f (n : ℤ) : IsIso ((totalConeHom φ).f n) := by
  refine ⟨totalConeInvX φ n, ?_, ?_⟩
  · apply mappingCone.ext_from _ (n + 1) n rfl
    · apply total.hom_ext
      intro p q h
      obtain ⟨p, rfl⟩ : ∃ p', p' + 1 = p := ⟨p - 1, by omega⟩
      rw [ι_inl_totalConeHom_assoc φ (p + 1) p q n rfl]
      simp [totalConeInvX]
    · apply total.hom_ext
      intro p q h
      simp [totalConeInvX, ιTotal_map_assoc]
  · apply total.hom_ext
    intro p q h
    apply coneTerm_ext φ p q
    · simpa [totalConeInvX, Category.assoc] using
        (ι_inl_totalConeHom φ (p + 1) p q n rfl (by dsimp at h ⊢; omega))
    · simp [totalConeInvX, Category.assoc]

/-- Totalization commutes with the horizontal mapping cone. -/
def totalMappingConeIso : mappingCone (total.map φ (ComplexShape.up ℤ)) ≅
    HomologicalComplex₂.total (mappingCone φ) (ComplexShape.up ℤ) := by
  have := totalConeHom_isIso_f φ
  have : IsIso (totalConeHom φ) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (totalConeHom φ)

/-- The right inclusion into a horizontal mapping cone is preserved by totalization. -/
@[reassoc (attr := simp)]
lemma totalMappingConeIso_inr :
    mappingCone.inr (total.map φ (ComplexShape.up ℤ)) ≫ (totalMappingConeIso φ).hom =
      total.map (mappingCone.inr φ) (ComplexShape.up ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact inr_totalConeHom φ n

/-- On the shifted source summands, the total mapping-cone comparison is the horizontal
mapping-cone inclusion, without an additional sign. -/
@[reassoc]
lemma totalMappingConeIso_ι_inl (p p' q n : ℤ) (hp : p' + 1 = p)
    (h : p + q = n + 1) :
    K.ιTotal (ComplexShape.up ℤ) p q (n + 1) h ≫
      (mappingCone.inl (total.map φ (ComplexShape.up ℤ))).v (n + 1) n (by omega) ≫
        (totalMappingConeIso φ).hom.f n =
      ((mappingCone.inl φ).v p p' (by omega)).f q ≫
        HomologicalComplex₂.ιTotal (mappingCone φ) (ComplexShape.up ℤ) p' q n
          (by dsimp; omega) :=
  ι_inl_totalConeHom φ p p' q n hp h

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]

/-- A morphism of double cochain complexes with finite antidiagonals that is a
quasi-isomorphism on every row gives a quasi-isomorphism on their total complexes. -/
theorem quasiIso_total_map_of_rows_up_int (φ : K ⟶ L)
    (hK : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}.Finite)
    (hL : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((L.X p).X (n - p))}.Finite)
    (hrows : ∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) :
    QuasiIso (total.map φ (ComplexShape.up ℤ)) := by
  have hfin := finiteAntidiagonals_mappingCone φ hK hL
  have := hasTotal_of_finite_antidiagonals (mappingCone φ) hfin
  rw [CochainComplex.quasiIso_iff_acyclic_mappingCone]
  have hc : (HomologicalComplex₂.total (mappingCone φ) (ComplexShape.up ℤ)).Acyclic := by
    apply acyclic_total_of_finite_antidiagonals _ hfin (Or.inr _)
    intro q
    have h := (CochainComplex.quasiIso_iff_acyclic_mappingCone _).1 (hrows q)
    exact fun p ↦ (h p).of_iso (mappingCone.mapHomologicalComplexIso φ (eval C _ q)).symm
  exact fun n ↦ (hc n).of_iso (totalMappingConeIso φ).symm

end HomologicalComplex₂
