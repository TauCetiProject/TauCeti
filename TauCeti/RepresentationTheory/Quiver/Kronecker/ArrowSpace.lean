/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Irreducible
public import TauCeti.RepresentationTheory.Quiver.Representation.IrreducibleMorphism
import Mathlib.CategoryTheory.Preadditive.Schur

/-!
# The arrow spaces of the `A₂` Auslander--Reiten mesh

For the one-arrow quiver, the space `rad(M, N) / rad²(M, N)` between indecomposables
has dimension one precisely for `S₂ → P₁` and `P₁ → S₁`, and vanishes for every other
pair. Thus the two maps of the almost-split sequence account for the entire mesh,
including their multiplicities. The formula is invariant under isomorphisms of both
representations and holds over every field.

See Assem, Simson and Skowroński, *Elements of the Representation Theory of
Associative Algebras I*, IV.1, for the `A₂` mesh and its arrow spaces.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Quiver.Kronecker

universe u

variable {k : Type u} [Field k] {A : Type} [Unique A]

private noncomputable abbrev S₁ := simpleRep k (Quiver.Kronecker A) src
private noncomputable abbrev S₂ := simpleRep k (Quiver.Kronecker A) tgt
private noncomputable abbrev P₁ := indecProjRep k (Quiver.Kronecker A) src

private instance local_end_P₁ : IsLocalRing (End (P₁ (k := k) (A := A))) :=
  (QuiverRep.indecomposable_iff_isLocalRing_end (M := P₁ (k := k) (A := A))
    (isFinDim_iff.mpr fun v ↦ by cases v <;> exact finiteDimensional_indecProjRep_obj src _)).mp
    (indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic src)

omit [Unique A] in
private theorem not_isIrreducibleMorphism_end_P₁ (f : P₁ (k := k) (A := A) ⟶ P₁) :
    ¬ IsIrreducibleMorphism f := by
  intro hf
  have hd := finrank_end_indecProjRep_of_isAcyclic (k := k) (Q := Quiver.Kronecker A)
    Quiver.Kronecker.isAcyclic src
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 P₁)
    (id_ne_zero_of_finrank_end_eq_one hd)).mp hd f
  have hc : c ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (zero_smul _ _)
  let e : P₁ (k := k) (A := A) ≅ P₁ :=
    { hom := c • 𝟙 _
      inv := c⁻¹ • 𝟙 _
      hom_inv_id := by simp [Linear.comp_smul, smul_smul, hc]
      inv_hom_id := by simp [Linear.comp_smul, smul_smul, hc] }
  exact hf.not_isIso e.isIso_hom

private theorem hom_S₁_P₁_eq_zero (f : S₁ (k := k) (A := A) ⟶ P₁) : f = 0 := by
  apply (simpleRep_hom_eq_zero_iff f).mpr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply indecProjRep_map_arrowPath_injective (default : A)
  have hn := ModuleCat.hom_ext_iff.mp (f.naturality (arrowPath (default : A)))
  simp only [S₁, ← toPath_arrow, simpleRep_map_toPath] at hn
  simpa using (LinearMap.congr_fun hn x).symm

omit [Unique A] in
private theorem hom_P₁_S₂_eq_zero (f : P₁ (k := k) (A := A) ⟶ S₂) : f = 0 := by
  have := finiteDimensional_simpleRep_obj (k := k) (Q := Quiver.Kronecker A) tgt
    ((Paths.of (Quiver.Kronecker A)).obj src)
  have : Module.Finite k (P₁ (k := k) (A := A) ⟶ S₂) :=
    (indecProjRepHomEquiv src S₂).symm.finiteDimensional
  have hd : Module.finrank k (P₁ (k := k) (A := A) ⟶ S₂) = 0 := by
    rw [finrank_hom_indecProjRep, dimVector_simpleRep]
    simp
  have : Subsingleton (P₁ (k := k) (A := A) ⟶ S₂) := (Module.finrank_zero_iff.mp hd)
  exact Subsingleton.elim _ _

private instance local_end_simple (i : Quiver.Kronecker A) :
    IsLocalRing (End (simpleRep k (Quiver.Kronecker A) i)) :=
  (QuiverRep.indecomposable_iff_isLocalRing_end
    (isFinDim_iff.mpr fun v ↦ finiteDimensional_simpleRep_obj i v)).mp
    (indecomposable_of_simple _)

private theorem hom_S₂_P₁_finrank : Module.finrank k (S₂ (k := k) (A := A) ⟶ P₁) = 1 := by
  let ι : S₂ (k := k) (A := A) ⟶ P₁ := (kroneckerARSequence k A).f
  have hsurj : Function.Surjective (Linear.leftComp k P₁ ι) := by
    intro f
    apply (isLeftAlmostSplit_kroneckerARSequence_f k A).factors P₁ f
    intro hs
    have hrad : f ∈ jacobsonRadical S₂ P₁ := by
      have : IsEmpty (S₂ (k := k) (A := A) ≅ P₁) :=
        ⟨fun e ↦ not_nonempty_simpleRep_indecProjRep_iso tgt ⟨e⟩⟩
      rw [jacobsonRadical_eq_top this]
      trivial
    exact (mem_jacobsonRadical_iff_not_isSplitMono.mp hrad) hs
  have hd := finrank_end_indecProjRep_of_isAcyclic (k := k) (Q := Quiver.Kronecker A)
    Quiver.Kronecker.isAcyclic src
  have : Module.Finite k (P₁ (k := k) (A := A) ⟶ P₁) := Module.finite_of_finrank_eq_succ hd
  have : Module.Finite k (S₂ (k := k) (A := A) ⟶ P₁) :=
    Module.Finite.of_surjective _ hsurj
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  have : Nontrivial (S₂ (k := k) (A := A) ⟶ P₁) :=
    nontrivial_of_ne ι 0 (isIrreducibleMorphism_kroneckerARSequence_f (k := k) (A := A)).ne_zero
  have hpos : 0 < Module.finrank k (S₂ (k := k) (A := A) ⟶ P₁) := Module.finrank_pos
  rw [hd] at hle
  omega

omit [Unique A] in
private theorem hom_P₁_S₁_finrank : Module.finrank k (P₁ (k := k) (A := A) ⟶ S₁) = 1 := by
  rw [finrank_hom_indecProjRep, dimVector_simpleRep]
  simp

/-- The irreducible morphism space `S₂ → P₁` is one-dimensional over any field. -/
@[simp]
theorem finrank_irreducibleMorphismSpace_simpleRep_tgt_indecProjRep_src :
    Module.finrank k (irreducibleMorphismSpace k (simpleRep k (Quiver.Kronecker A) tgt)
      (indecProjRep k (Quiver.Kronecker A) src)) = 1 := by
  have : Module.Finite k (S₂ (k := k) (A := A) ⟶ P₁) :=
    Module.finite_of_finrank_eq_succ hom_S₂_P₁_finrank
  have hle := finrank_irreducibleMorphismSpace_le k (S₂ (k := k) (A := A)) P₁
  have hpos := (finrank_irreducibleMorphismSpace_pos_iff k (S₂ (k := k) (A := A)) P₁).mpr
    ⟨_, isIrreducibleMorphism_kroneckerARSequence_f⟩
  rw [hom_S₂_P₁_finrank] at hle
  exact Nat.le_antisymm hle (Nat.succ_le_of_lt hpos)

/-- The irreducible morphism space `P₁ → S₁` is one-dimensional over any field. -/
@[simp]
theorem finrank_irreducibleMorphismSpace_indecProjRep_src_simpleRep_src :
    Module.finrank k (irreducibleMorphismSpace k (indecProjRep k (Quiver.Kronecker A) src)
      (simpleRep k (Quiver.Kronecker A) src)) = 1 := by
  have : Module.Finite k (P₁ (k := k) (A := A) ⟶ S₁) :=
    Module.finite_of_finrank_eq_succ hom_P₁_S₁_finrank
  have hle := finrank_irreducibleMorphismSpace_le k (P₁ (k := k) (A := A)) S₁
  have hpos := (finrank_irreducibleMorphismSpace_pos_iff k (P₁ (k := k) (A := A)) S₁).mpr
    ⟨_, isIrreducibleMorphism_kroneckerARSequence_g⟩
  rw [hom_P₁_S₁_finrank] at hle
  exact Nat.le_antisymm hle (Nat.succ_le_of_lt hpos)

open scoped Classical in
/-- The complete `A₂` arrow-space calculation: between indecomposable representations,
`rad / rad²` has dimension one exactly for the pairs `S₂ → P₁` and `P₁ → S₁`.
All other pairs, including the three diagonal pairs, have dimension zero. -/
@[simp]
theorem finrank_irreducibleMorphismSpace_kronecker
    (M N : QuiverRep k (Quiver.Kronecker A)) (hM : Indecomposable M) (hN : Indecomposable N) :
    Module.finrank k (irreducibleMorphismSpace k M N) =
      if (Nonempty (M ≅ simpleRep k (Quiver.Kronecker A) tgt) ∧
          Nonempty (N ≅ indecProjRep k (Quiver.Kronecker A) src)) ∨
        (Nonempty (M ≅ indecProjRep k (Quiver.Kronecker A) src) ∧
          Nonempty (N ≅ simpleRep k (Quiver.Kronecker A) src)) then 1 else 0 := by
  classical
  by_cases h : (Nonempty (M ≅ S₂) ∧ Nonempty (N ≅ P₁)) ∨
      (Nonempty (M ≅ P₁) ∧ Nonempty (N ≅ S₁))
  · rw [ite_eq_left h]
    rcases h with ⟨⟨eM⟩, ⟨eN⟩⟩ | ⟨⟨eM⟩, ⟨eN⟩⟩
    · exact (irreducibleMorphismSpaceCongr k eM eN).finrank_eq.trans
        finrank_irreducibleMorphismSpace_simpleRep_tgt_indecProjRep_src
    · exact (irreducibleMorphismSpaceCongr k eM eN).finrank_eq.trans
        finrank_irreducibleMorphismSpace_indecProjRep_src_simpleRep_src
  · rw [ite_eq_right h]
    rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
      M hM with hM' | hM' | hM' <;>
      rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
        N hN with hN' | hN' | hN' <;>
      obtain ⟨eM⟩ := hM' <;>
      obtain ⟨eN⟩ := hN' <;>
      rw [(irreducibleMorphismSpaceCongr k eM eN).finrank_eq]
    · have : Subsingleton (irreducibleMorphismSpace k (S₁ (k := k) (A := A)) S₁) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr fun f hf ↦
          hf.not_isIso ((isIso_iff_nonzero f).mpr hf.ne_zero)
      exact Module.finrank_zero_of_subsingleton
    · have : Subsingleton (irreducibleMorphismSpace k (S₁ (k := k) (A := A)) S₂) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr fun f hf ↦
          hf.ne_zero ((simpleRep_hom_eq_zero_iff f).mpr
            ((isZero_simpleRep_obj src_ne_tgt).eq_of_tgt _ _))
      exact Module.finrank_zero_of_subsingleton
    · have : Subsingleton (irreducibleMorphismSpace k (S₁ (k := k) (A := A)) P₁) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr fun f hf ↦ hf.ne_zero (hom_S₁_P₁_eq_zero f)
      exact Module.finrank_zero_of_subsingleton
    · have : Subsingleton (irreducibleMorphismSpace k (S₂ (k := k) (A := A)) S₁) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr fun f hf ↦
          hf.ne_zero ((simpleRep_hom_eq_zero_iff f).mpr
            ((isZero_simpleRep_obj src_ne_tgt.symm).eq_of_tgt _ _))
      exact Module.finrank_zero_of_subsingleton
    · have : Subsingleton (irreducibleMorphismSpace k (S₂ (k := k) (A := A)) S₂) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr fun f hf ↦
          hf.not_isIso ((isIso_iff_nonzero f).mpr hf.ne_zero)
      exact Module.finrank_zero_of_subsingleton
    · exact (h (Or.inl ⟨⟨eM⟩, ⟨eN⟩⟩)).elim
    · exact (h (Or.inr ⟨⟨eM⟩, ⟨eN⟩⟩)).elim
    · have : Subsingleton (irreducibleMorphismSpace k (P₁ (k := k) (A := A)) S₂) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr fun f hf ↦ hf.ne_zero (hom_P₁_S₂_eq_zero f)
      exact Module.finrank_zero_of_subsingleton
    · have : Subsingleton (irreducibleMorphismSpace k (P₁ (k := k) (A := A)) P₁) :=
        subsingleton_irreducibleMorphismSpace_iff.mpr not_isIrreducibleMorphism_end_P₁
      exact Module.finrank_zero_of_subsingleton

end TauCeti
