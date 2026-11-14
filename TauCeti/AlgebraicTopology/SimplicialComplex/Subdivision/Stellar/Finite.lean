/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
public import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction
import Mathlib.Data.Fintype.Card

/-!
# Finite-support compression and relabeling reflection for stellar equivalence

Every stellar move on a simplicial complex with finitely many faces touches only finitely many
ambient vertices, and preserves face finiteness. Consequently, any finite chain of stellar moves
and inverse stellar moves (`PreAbstractSimplicialComplex.StellarEquivalent`) starting from a
finite-face complex takes place entirely inside a finite subset of the ambient vertex type.

Restricting such a chain to a finite vertex set and encoding its fresh vertices into `ℕ` yields
three structural consequences for `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling`
on finite-face complexes:

* **Universal ambient compression** (`of_stellarEquivalent_map`): if injective relabelings into
  *any* ambient vertex type `Ω` make two finite-face complexes stellar equivalent, they are
  already stellar equivalent up to relabeling in `ι ⊕ ℕ`.
* **Single-step normal form** (`stellarEquivalentUpToRelabeling_iff_exists_stellarEquivalent`):
  the equivalence closure in the definition of `StellarEquivalentUpToRelabeling` collapses to a
  single common-relabeling witness in `ι ⊕ ℕ`.
* **Injective relabeling reflection** (`stellarEquivalentUpToRelabeling_map_iff`): an injective
  vertex map both preserves and reflects intrinsic stellar equivalence on finite-face complexes.

## References

* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι κ Ω : Type*}

/-- Every precomplex with finitely many faces is supported on a finite set of ambient vertices. -/
theorem exists_finset_subset_of_finite_faces {K : PreAbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) : ∃ V : Finset ι, ∀ σ ∈ K, σ ⊆ V := by
  classical
  exact ⟨hfin.toFinset.biUnion id, fun σ hσ _ hx =>
    Finset.mem_biUnion.mpr ⟨σ, hfin.mem_toFinset.mpr hσ, hx⟩⟩

/-- A stellar move between two complexes supported in a vertex set `s` restricts to a stellar move
on `s`. -/
theorem IsStellarMove.restrict [DecidableEq Ω] {K L : PreAbstractSimplicialComplex Ω}
    (h : IsStellarMove K L) {s : Set Ω} [DecidableEq s]
    (hK : ∀ τ ∈ K, (τ : Set Ω) ⊆ s) (hL : ∀ τ ∈ L, (τ : Set Ω) ⊆ s) :
    IsStellarMove (K.restrict s) (L.restrict s) := by
  classical
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp h
  have hvL : ({v} : Finset Ω) ∈ stellarSubdivision K σ v :=
    singleton_mem_stellarSubdivision_iff.mpr hσ
  have hvS : v ∈ s := hL {v} hvL (Finset.mem_singleton_self v)
  have hσS : (σ : Set Ω) ⊆ s := hK σ hσ
  let σ' : Finset s := σ.subtype (· ∈ s)
  have hσ' : σ'.image Subtype.val = σ := by
    simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
      Finset.subtype_map_of_mem fun x hx => hσS hx
  refine isStellarMove_iff.mpr ⟨σ', ⟨v, hvS⟩, (mem_restrict_iff_image K s σ').mpr (hσ' ▸ hσ),
    ?_, ?_⟩
  · intro hv'
    apply hv
    simpa only [mem_restrict_iff_image, Finset.image_singleton] using hv'
  · refine map_injective (Subtype.val_injective : Function.Injective (Subtype.val : s → Ω)) ?_
    dsimp only
    rw [map_restrict_eq_of_subset hL, map_stellarSubdivision _ Subtype.val_injective,
      map_restrict_eq_of_subset hK, hσ']

private theorem stellarEquivalent_restrict_mono [DecidableEq Ω]
    {K L : PreAbstractSimplicialComplex Ω} {S T : Finset Ω} (hST : S ⊆ T)
    (hK : ∀ τ ∈ K, τ ⊆ S) (hL : ∀ τ ∈ L, τ ⊆ S)
    (h : StellarEquivalent (K.restrict (S : Set Ω)) (L.restrict (S : Set Ω))) :
    StellarEquivalent (K.restrict (T : Set Ω)) (L.restrict (T : Set Ω)) := by
  have hST' : (S : Set Ω) ⊆ (T : Set Ω) := Finset.coe_subset.mpr hST
  have hK' : ∀ τ ∈ K, (τ : Set Ω) ⊆ (S : Set Ω) := fun τ hτ => Finset.coe_subset.mpr (hK τ hτ)
  have hL' : ∀ τ ∈ L, (τ : Set Ω) ⊆ (S : Set Ω) := fun τ hτ => Finset.coe_subset.mpr (hL τ hτ)
  rw [← map_inclusion_restrict hST' hK', ← map_inclusion_restrict hST' hL']
  exact h.map _ (Set.inclusion_injective hST')

/-- A stellar equivalence starting from a finite-face complex takes place inside some finite
vertex set containing any prescribed finite set `S₀`. -/
theorem StellarEquivalent.exists_finset_restrict [DecidableEq Ω]
    {K L : PreAbstractSimplicialComplex Ω} (h : StellarEquivalent K L)
    (hK : K.faces.Finite) (S₀ : Finset Ω) :
    ∃ S : Finset Ω, S₀ ⊆ S ∧ (∀ τ ∈ K, τ ⊆ S) ∧ (∀ τ ∈ L, τ ⊆ S) ∧
      StellarEquivalent (K.restrict (S : Set Ω)) (L.restrict (S : Set Ω)) := by
  have hmain : (K.faces.Finite ↔ L.faces.Finite) ∧
      (K.faces.Finite → ∃ S : Finset Ω, (∀ τ ∈ K, τ ⊆ S) ∧ (∀ τ ∈ L, τ ⊆ S) ∧
        StellarEquivalent (K.restrict (S : Set Ω)) (L.restrict (S : Set Ω))) := by
    apply h.induction_on
    · intro A B hmove
      refine ⟨hmove.finite_faces_iff, fun hA => ?_⟩
      obtain ⟨VA, hVA⟩ := exists_finset_subset_of_finite_faces hA
      obtain ⟨VB, hVB⟩ := exists_finset_subset_of_finite_faces (hmove.finite_faces_iff.mp hA)
      exact ⟨VA ∪ VB,
        fun τ hτ => (hVA τ hτ).trans Finset.subset_union_left,
        fun τ hτ => (hVB τ hτ).trans Finset.subset_union_right,
        (hmove.restrict
          (fun τ hτ => Finset.coe_subset.mpr ((hVA τ hτ).trans Finset.subset_union_left))
          (fun τ hτ => Finset.coe_subset.mpr ((hVB τ hτ).trans Finset.subset_union_right))
            ).stellarEquivalent⟩
    · intro A
      refine ⟨Iff.rfl, fun hA => ?_⟩
      obtain ⟨VA, hVA⟩ := exists_finset_subset_of_finite_faces hA
      exact ⟨VA, hVA, hVA, .refl _⟩
    · intro A B ⟨hiff, hfwd⟩
      refine ⟨hiff.symm, fun hB => ?_⟩
      obtain ⟨S, hAS, hBS, hS⟩ := hfwd (hiff.mpr hB)
      exact ⟨S, hBS, hAS, hS.symm⟩
    · intro A B C ⟨hiff₁, hfwd₁⟩ ⟨hiff₂, hfwd₂⟩
      refine ⟨hiff₁.trans hiff₂, fun hA => ?_⟩
      obtain ⟨S₁, hAS₁, hBS₁, h₁⟩ := hfwd₁ hA
      obtain ⟨S₂, hBS₂, hCS₂, h₂⟩ := hfwd₂ (hiff₁.mp hA)
      exact ⟨S₁ ∪ S₂,
        fun τ hτ => (hAS₁ τ hτ).trans Finset.subset_union_left,
        fun τ hτ => (hCS₂ τ hτ).trans Finset.subset_union_right,
        (stellarEquivalent_restrict_mono Finset.subset_union_left hAS₁ hBS₁ h₁).trans
          (stellarEquivalent_restrict_mono Finset.subset_union_right hBS₂ hCS₂ h₂)⟩
  obtain ⟨S, hKS, hLS, hSL⟩ := hmain.2 hK
  exact ⟨S ∪ S₀, Finset.subset_union_right,
    fun τ hτ => (hKS τ hτ).trans Finset.subset_union_left,
    fun τ hτ => (hLS τ hτ).trans Finset.subset_union_left,
    stellarEquivalent_restrict_mono Finset.subset_union_left hKS hLS hSL⟩

private noncomputable def compressRelabeling [DecidableEq ι] [DecidableEq Ω]
    (V : Finset ι) (f : ι → Ω) (hf : Function.Injective f)
    {S : Finset Ω} (hVS : V.image f ⊆ S) (enc : (S : Set Ω) ↪ ℕ) : ι ↪ ι ⊕ ℕ where
  toFun x :=
    if hx : x ∈ V then Sum.inr (enc ⟨f x, hVS (Finset.mem_image_of_mem f hx)⟩) else Sum.inl x
  inj' x y hxy := by
    by_cases hx : x ∈ V <;> by_cases hy : y ∈ V <;> simp only [hx, hy, ↓reduceDIte] at hxy
    · exact hf (congrArg Subtype.val (enc.injective (Sum.inr.inj hxy)))
    · exact nomatch hxy
    · exact nomatch hxy
    · exact Sum.inl.inj hxy

private theorem image_compressRelabeling_eq [DecidableEq ι] [DecidableEq Ω]
    {V σ : Finset ι} (hσV : σ ⊆ V) (f : ι → Ω) (hf : Function.Injective f)
    {S : Finset Ω} (hVS : V.image f ⊆ S) (enc : (S : Set Ω) ↪ ℕ) :
    ((σ.image f).subtype (· ∈ (S : Set Ω))).image (Sum.inr ∘ enc) =
      σ.image (compressRelabeling V f hf hVS enc) := by
  ext z
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨y, hyτ, rfl⟩
    obtain ⟨x, hxσ, hfx⟩ := Finset.mem_image.mp (Finset.mem_subtype.mp hyτ)
    have hxV : x ∈ V := hσV hxσ
    have hy_eq : (⟨f x, hVS (Finset.mem_image_of_mem f hxV)⟩ : (S : Set Ω)) = y := Subtype.ext hfx
    exact ⟨x, hxσ, by simp [compressRelabeling, hxV, hy_eq]⟩
  · rintro ⟨x, hxσ, rfl⟩
    have hxV : x ∈ V := hσV hxσ
    exact ⟨⟨f x, hVS (Finset.mem_image_of_mem f hxV)⟩,
      Finset.mem_subtype.mpr (Finset.mem_image_of_mem f hxσ), by simp [compressRelabeling, hxV]⟩

private theorem map_compressRelabeling_eq [DecidableEq ι] [DecidableEq Ω]
    {K : PreAbstractSimplicialComplex ι} {V : Finset ι} (hV : ∀ σ ∈ K, σ ⊆ V)
    (f : ι → Ω) (hf : Function.Injective f)
    {S : Finset Ω} (hVS : V.image f ⊆ S) (enc : (S : Set Ω) ↪ ℕ) :
    K.map (compressRelabeling V f hf hVS enc) =
      ((K.map f).restrict (S : Set Ω)).map (Sum.inr ∘ enc) := by
  have hσS {σ : Finset ι} (hσ : σ ∈ K) : ∀ y ∈ σ.image f, y ∈ (S : Set Ω) := by
    intro y hy
    obtain ⟨x, hxσ, rfl⟩ := Finset.mem_image.mp hy
    exact hVS (Finset.mem_image_of_mem f (hV σ hσ hxσ))
  refine SetLike.ext fun ω => ?_
  rw [mem_map_iff, mem_map_iff]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨(σ.image f).subtype (· ∈ (S : Set Ω)), ?_,
      image_compressRelabeling_eq (hV σ hσ) f hf hVS enc⟩
    rw [mem_restrict_iff_image]
    have heq : ((σ.image f).subtype (· ∈ (S : Set Ω))).image Subtype.val = σ.image f := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem (hσS hσ)
    rw [heq]
    exact mem_map_iff.mpr ⟨σ, hσ, rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    rw [mem_restrict_iff_image, mem_map_iff] at hτ
    obtain ⟨σ, hσ, hστ⟩ := hτ
    have hτeq : τ = (σ.image f).subtype (· ∈ (S : Set Ω)) := by
      apply Finset.image_injective
        (Subtype.val_injective : Function.Injective (Subtype.val : _ → Ω))
      rw [← hστ]
      symm
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem (hσS hσ)
    exact ⟨σ, hσ, hτeq ▸ (image_compressRelabeling_eq (hV σ hσ) f hf hVS enc).symm⟩

/-- If injective relabelings into any ambient vertex type `Ω` make two finite-face complexes
stellar equivalent, then they already admit a single common-relabeling stellar equivalence in
`ι ⊕ ℕ`. -/
theorem exists_stellarEquivalent_of_stellarEquivalent_map [DecidableEq ι] [DecidableEq Ω]
    {P Q : PreAbstractSimplicialComplex ι} (hP : P.faces.Finite)
    {f g : ι → Ω} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : StellarEquivalent (P.map f) (Q.map g)) :
    ∃ f' g' : ι ↪ ι ⊕ ℕ, StellarEquivalent (P.map f') (Q.map g') := by
  have hPf : (P.map f).faces.Finite := (finite_faces_map_iff_of_injective f hf).mpr hP
  have hQ : Q.faces.Finite :=
    (finite_faces_map_iff_of_injective g hg).mp (h.finite_faces_iff.mp hPf)
  obtain ⟨VP, hVP⟩ := exists_finset_subset_of_finite_faces hP
  obtain ⟨VQ, hVQ⟩ := exists_finset_subset_of_finite_faces hQ
  obtain ⟨S, hS₀, -, -, hS⟩ := h.exists_finset_restrict hPf (VP.image f ∪ VQ.image g)
  have hVPS : VP.image f ⊆ S := Finset.subset_union_left.trans hS₀
  have hVQS : VQ.image g ⊆ S := Finset.subset_union_right.trans hS₀
  let enc : (S : Set Ω) ↪ ℕ :=
    (Fintype.equivFin (S : Set Ω)).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
  refine ⟨compressRelabeling VP f hf hVPS enc, compressRelabeling VQ g hg hVQS enc, ?_⟩
  rw [map_compressRelabeling_eq hVP f hf hVPS enc, map_compressRelabeling_eq hVQ g hg hVQS enc]
  exact hS.map (Sum.inr ∘ enc) (Sum.inr_injective.comp enc.injective)

/-- **Universal ambient compression**: a stellar equivalence after injective relabelings into any
ambient vertex type `Ω` yields `StellarEquivalentUpToRelabeling` on finite-face complexes. -/
theorem StellarEquivalentUpToRelabeling.of_stellarEquivalent_map [DecidableEq ι] [DecidableEq Ω]
    {P Q : PreAbstractSimplicialComplex ι} (hP : P.faces.Finite)
    {f g : ι → Ω} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : StellarEquivalent (P.map f) (Q.map g)) :
    StellarEquivalentUpToRelabeling P Q := by
  obtain ⟨f', g', h'⟩ := exists_stellarEquivalent_of_stellarEquivalent_map hP hf hg h
  exact .of_common_relabeling f' g' h'

private theorem glue_stellarEquivalent_rel [DecidableEq ι]
    {A B C : PreAbstractSimplicialComplex ι} (hA : A.faces.Finite) (hB : B.faces.Finite)
    {f₁ g₁ f₂ g₂ : ι ↪ ι ⊕ ℕ}
    (he₁ : StellarEquivalent (A.map f₁) (B.map g₁))
    (he₂ : StellarEquivalent (B.map f₂) (C.map g₂)) :
    ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (A.map f) (C.map g) := by
  classical
  obtain ⟨VB, hVB⟩ := exists_finset_subset_of_finite_faces hB
  -- Glue the two copies of `ι ⊕ ℕ` along the vertices of `B`.
  let j₁ : ι ⊕ ℕ → (ι ⊕ ℕ) ⊕ (ι ⊕ ℕ) := Sum.inl
  let j₂ : ι ⊕ ℕ → (ι ⊕ ℕ) ⊕ (ι ⊕ ℕ) := fun y =>
    if hy : y ∈ VB.image f₂ then
      Sum.inl (g₁ (Classical.choose (Finset.mem_image.mp hy)))
    else
      Sum.inr y
  have hj₂ : Function.Injective j₂ := by
    intro y y' hyy'
    by_cases hy : y ∈ VB.image f₂ <;> by_cases hy' : y' ∈ VB.image f₂ <;>
      simp only [j₂, hy, hy', ↓reduceDIte] at hyy'
    · have hxeq := g₁.injective (Sum.inl.inj hyy')
      have hx := (Classical.choose_spec (Finset.mem_image.mp hy)).2
      have hx' := (Classical.choose_spec (Finset.mem_image.mp hy')).2
      exact hx.symm.trans (congrArg f₂ hxeq |>.trans hx')
    · exact nomatch hyy'
    · exact nomatch hyy'
    · exact Sum.inr.inj hyy'
  have hBglue : (B.map f₂).map j₂ = (B.map g₁).map j₁ := by
    rw [map_map, map_map]
    refine SetLike.ext fun ω => ?_
    rw [mem_map_iff, mem_map_iff]
    refine exists_congr fun σ => and_congr_right fun hσ => ?_
    have himg : σ.image (j₂ ∘ f₂) = σ.image (j₁ ∘ g₁) := by
      refine Finset.image_congr fun x hx => ?_
      have hxVB : x ∈ VB := hVB σ hσ hx
      have hfx : f₂ x ∈ VB.image f₂ := Finset.mem_image_of_mem f₂ hxVB
      have hchoose : Classical.choose (Finset.mem_image.mp hfx) = x :=
        f₂.injective (Classical.choose_spec (Finset.mem_image.mp hfx)).2
      simp only [Function.comp_apply, j₁, j₂, hfx, ↓reduceDIte, hchoose]
    rw [himg]
  have he : StellarEquivalent (A.map (j₁ ∘ f₁)) (C.map (j₂ ∘ g₂)) := by
    rw [← map_map, ← map_map]
    exact (he₁.map j₁ Sum.inl_injective).trans
      (hBglue ▸ he₂.map j₂ hj₂)
  exact exists_stellarEquivalent_of_stellarEquivalent_map hA
    (Sum.inl_injective.comp f₁.injective) (hj₂.comp g₂.injective) he

/-- **Single-step normal form**: on finite-face complexes, `StellarEquivalentUpToRelabeling` is
witnessed by a single pair of injective relabelings into `ι ⊕ ℕ`. -/
theorem stellarEquivalentUpToRelabeling_iff_exists_stellarEquivalent [DecidableEq ι]
    {P Q : PreAbstractSimplicialComplex ι} (hP : P.faces.Finite) :
    StellarEquivalentUpToRelabeling P Q ↔
      ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (P.map f) (Q.map g) := by
  refine ⟨fun h => ?_, fun ⟨f, g, he⟩ => .of_common_relabeling f g he⟩
  have hmain : (P.faces.Finite ↔ Q.faces.Finite) ∧
      (P.faces.Finite → ∃ f g : ι ↪ ι ⊕ ℕ, StellarEquivalent (P.map f) (Q.map g)) := by
    apply h.induction_on
    · intro A B f g he
      exact ⟨(StellarEquivalentUpToRelabeling.of_common_relabeling f g he).finite_faces_iff,
        fun _ => ⟨f, g, he⟩⟩
    · intro A
      exact ⟨Iff.rfl, fun _ =>
        ⟨⟨Sum.inl, Sum.inl_injective⟩, ⟨Sum.inl, Sum.inl_injective⟩, .refl _⟩⟩
    · intro A B ⟨hiff, hfwd⟩
      refine ⟨hiff.symm, fun hB => ?_⟩
      obtain ⟨f, g, he⟩ := hfwd (hiff.mpr hB)
      exact ⟨g, f, he.symm⟩
    · intro A B C ⟨hiff₁, hfwd₁⟩ ⟨hiff₂, hfwd₂⟩
      refine ⟨hiff₁.trans hiff₂, fun hA => ?_⟩
      obtain ⟨f₁, g₁, he₁⟩ := hfwd₁ hA
      obtain ⟨f₂, g₂, he₂⟩ := hfwd₂ (hiff₁.mp hA)
      exact glue_stellarEquivalent_rel hA (hiff₁.mp hA) he₁ he₂
  exact hmain.2 hP

/-- An injective vertex relabeling preserves and reflects `StellarEquivalentUpToRelabeling` on
finite-face complexes. -/
theorem stellarEquivalentUpToRelabeling_map_iff [DecidableEq ι] [DecidableEq κ]
    {P Q : PreAbstractSimplicialComplex ι} (hP : P.faces.Finite)
    {f : ι → κ} (hf : Function.Injective f) :
    StellarEquivalentUpToRelabeling (P.map f) (Q.map f) ↔
      StellarEquivalentUpToRelabeling P Q := by
  refine ⟨fun h => ?_, fun h => h.map f hf⟩
  have hPf : (P.map f).faces.Finite := (finite_faces_map_iff_of_injective f hf).mpr hP
  obtain ⟨a, b, he⟩ :=
    (stellarEquivalentUpToRelabeling_iff_exists_stellarEquivalent hPf).mp h
  rw [map_map, map_map] at he
  exact .of_stellarEquivalent_map hP (a.injective.comp hf) (b.injective.comp hf) he

end PreAbstractSimplicialComplex
