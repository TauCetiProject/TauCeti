/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Homotopy
import Mathlib.Logic.Equiv.Fintype

/-!
# Reflecting balls, spheres, and manifolds along injective vertex maps

An injective map of ambient vertex types not only preserves combinatorial balls and spheres
(`CombinatorialManifold.Map`), it also reflects them, and therefore preserves and reflects
combinatorial manifolds. This lets local models computed after injective vertex tagging — such as
closed stars and closed-star boundaries expressed as joins on `ι ⊕ ι` — be transferred back to the
original complex on `ι` without assuming extra unused ambient vertices in `ι`.

Reflecting a combinatorial `n`-sphere `K.map f` back to `K` requires finding an `(n + 2)`-element
model vertex set in `ι`: `K` has an `(n + 1)`-element face from its dimension, and cannot be
contained in that single simplex because otherwise `K.map f` would be a combinatorial `n`-ball,
contradicting `IsCombinatorialSphere.not_isCombinatorialBall`. Once both endpoints have finite
face sets on `ι`, any chain of common-relabeling stellar equivalences in `κ ⊕ ℕ` uses only
finitely many vertices and compresses into `ι ⊕ ℕ`.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialBall.of_map` and
  `PreAbstractSimplicialComplex.isCombinatorialBall_map_iff`: injective vertex maps reflect
  combinatorial balls.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.of_map` and
  `PreAbstractSimplicialComplex.isCombinatorialSphere_map_iff`: injective vertex maps reflect
  combinatorial spheres.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.map`,
  `PreAbstractSimplicialComplex.IsCombinatorialManifold.of_map`, and
  `PreAbstractSimplicialComplex.isCombinatorialManifold_map_iff`: injective vertex maps preserve
  and reflect combinatorial manifolds.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.isCombinatorialBall_closedStar`: every
  closed vertex star in a combinatorial `n`-manifold is a combinatorial `n`-ball on the original
  vertex type.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

section Transport

private def restrictToFinset {Ω : Type*} [DecidableEq Ω] (P : PreAbstractSimplicialComplex Ω)
    (W : Finset Ω) : PreAbstractSimplicialComplex ↥W where
  faces := {τ | τ.image Subtype.val ∈ P}
  isRelLowerSet_faces := by
    intro τ hτ
    refine ⟨Finset.image_nonempty.mp (P.isRelLowerSet_faces hτ).1, fun {ρ} hρτ hρ => ?_⟩
    exact (P.isRelLowerSet_faces hτ).2 (Finset.image_subset_image hρτ) (hρ.image Subtype.val)

private theorem mem_restrictToFinset {Ω : Type*} [DecidableEq Ω]
    {P : PreAbstractSimplicialComplex Ω} {W : Finset Ω} {τ : Finset ↥W} :
    τ ∈ restrictToFinset P W ↔ τ.image Subtype.val ∈ P :=
  Iff.rfl

private theorem map_restrictToFinset {Ω : Type*} [DecidableEq Ω]
    {P : PreAbstractSimplicialComplex Ω} {W : Finset Ω} (hW : ∀ σ ∈ P, σ ⊆ W) :
    (restrictToFinset P W).map Subtype.val = P := by
  refine SetLike.ext fun σ => ?_
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact hτ
  · intro hσ
    have heq : (σ.subtype (· ∈ W)).image Subtype.val = σ := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem (fun x hx => hW σ hσ hx)
    exact mem_map_iff.mpr ⟨σ.subtype (· ∈ W), mem_restrictToFinset.mpr (heq.symm ▸ hσ), heq⟩

private theorem isStellarMove_exists_finset_injOn {Ω : Type*} [DecidableEq Ω]
    (Ω' : Type*) [DecidableEq Ω']
    {A B : PreAbstractSimplicialComplex Ω} (hA : A.faces.Finite) (hm : IsStellarMove A B) :
    ∃ W : Finset Ω, (∀ σ ∈ A, σ ⊆ W) ∧ (∀ σ ∈ B, σ ⊆ W) ∧
      ∀ (ψ : Ω → Ω'), Set.InjOn ψ (W : Set Ω) → IsStellarMove (A.map ψ) (B.map ψ) := by
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hm
  let W : Finset Ω := insert v (hA.toFinset.biUnion id)
  have hWA : ∀ τ ∈ A, τ ⊆ W := fun τ hτ =>
    (subset_biUnion_of_mem id (hA.mem_toFinset.mpr hτ)).trans (subset_insert v _)
  have hWB : ∀ τ ∈ stellarSubdivision A σ v, τ ⊆ W := by
    intro τ hτ
    rcases mem_stellarSubdivision_iff.mp hτ with ⟨-, hτA, -⟩ | ⟨hvτ, -, hτA⟩
    · exact hWA τ hτA
    · rw [← insert_erase hvτ]
      exact insert_subset (mem_insert_self v _) (subset_union_left.trans (hWA _ hτA))
  refine ⟨W, hWA, hWB, fun ψ hψ => ?_⟩
  let A₀ := restrictToFinset A W
  let σ₀ : Finset ↥W := σ.subtype (· ∈ W)
  let v₀ : ↥W := ⟨v, mem_insert_self v _⟩
  have hσ₀_img : σ₀.image Subtype.val = σ := by
    simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
      Finset.subtype_map_of_mem (fun x hx => hWA σ hσ hx)
  have hv₀ : ({v₀} : Finset ↥W) ∉ A₀ := by
    change ({v₀} : Finset ↥W).image Subtype.val ∉ A
    simpa [v₀] using hv
  have hm₀ : IsStellarMove A₀ (stellarSubdivision A₀ σ₀ v₀) :=
    isStellarMove_stellarSubdivision (mem_restrictToFinset.mpr (hσ₀_img.symm ▸ hσ)) hv₀
  have hψ₀ : Function.Injective (ψ ∘ Subtype.val : ↥W → Ω') :=
    fun x y hxy => Subtype.ext (hψ x.2 y.2 hxy)
  have hm' := hm₀.map (ψ ∘ Subtype.val) hψ₀
  have hAmap : A₀.map (ψ ∘ Subtype.val) = A.map ψ := by
    rw [← map_map, map_restrictToFinset hWA]
  have hBmap : (stellarSubdivision A₀ σ₀ v₀).map (ψ ∘ Subtype.val) =
      (stellarSubdivision A σ v).map ψ := by
    rw [← map_map, map_stellarSubdivision Subtype.val Subtype.val_injective,
      map_restrictToFinset hWA, hσ₀_img]
  rwa [hAmap, hBmap] at hm'

private theorem stellarEquivalent_exists_finset_injOn {Ω : Type*} [DecidableEq Ω]
    (Ω' : Type*) [DecidableEq Ω']
    {P Q : PreAbstractSimplicialComplex Ω} (he : StellarEquivalent P Q) (hP : P.faces.Finite) :
    ∃ W : Finset Ω, (∀ σ ∈ P, σ ⊆ W) ∧ (∀ σ ∈ Q, σ ⊆ W) ∧
      ∀ (ψ : Ω → Ω'), Set.InjOn ψ (W : Set Ω) → StellarEquivalent (P.map ψ) (Q.map ψ) := by
  let Motive : PreAbstractSimplicialComplex Ω → PreAbstractSimplicialComplex Ω → Prop :=
    fun X Y => (X.faces.Finite ↔ Y.faces.Finite) ∧ (X.faces.Finite →
      ∃ W : Finset Ω, (∀ σ ∈ X, σ ⊆ W) ∧ (∀ σ ∈ Y, σ ⊆ W) ∧
        ∀ (ψ : Ω → Ω'), Set.InjOn ψ (W : Set Ω) → StellarEquivalent (X.map ψ) (Y.map ψ))
  suffices h : Motive P Q from h.2 hP
  apply he.induction_on
  · intro A B hm
    refine ⟨hm.finite_faces_iff, fun hA => ?_⟩
    obtain ⟨W, hWA, hWB, hmap⟩ := isStellarMove_exists_finset_injOn Ω' hA hm
    exact ⟨W, hWA, hWB, fun ψ hψ => (hmap ψ hψ).stellarEquivalent⟩
  · refine fun A => ⟨Iff.rfl, fun hA => ⟨hA.toFinset.biUnion id,
      fun σ hσ => subset_biUnion_of_mem id (hA.mem_toFinset.mpr hσ),
      fun σ hσ => subset_biUnion_of_mem id (hA.mem_toFinset.mpr hσ),
      fun _ _ => .refl _⟩⟩
  · intro A B ih
    refine ⟨ih.1.symm, fun hB => ?_⟩
    obtain ⟨W, hWA, hWB, hmap⟩ := ih.2 (ih.1.mpr hB)
    exact ⟨W, hWB, hWA, fun ψ hψ => (hmap ψ hψ).symm⟩
  · intro A B C ih₁ ih₂
    refine ⟨ih₁.1.trans ih₂.1, fun hA => ?_⟩
    obtain ⟨W₁, hWA, _, hmap₁⟩ := ih₁.2 hA
    obtain ⟨W₂, _, hWC, hmap₂⟩ := ih₂.2 (ih₁.1.mp hA)
    refine ⟨W₁ ∪ W₂, fun σ hσ => (hWA σ hσ).trans subset_union_left,
      fun σ hσ => (hWC σ hσ).trans subset_union_right, fun ψ hψ => ?_⟩
    exact (hmap₁ ψ (hψ.mono (by simp))).trans (hmap₂ ψ (hψ.mono (by simp)))

private theorem map_eq_of_eqOn_faces {α β : Type*} [DecidableEq β]
    {P : PreAbstractSimplicialComplex α} {f g : α → β}
    (hfg : ∀ σ ∈ P, ∀ x ∈ σ, f x = g x) : P.map f = P.map g := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_map_iff]
  refine exists_congr fun σ => and_congr_right fun hσ => ?_
  rw [Finset.image_congr (hfg σ hσ)]

private theorem exists_common_relabeling_of_finite_faces {α : Type*} [DecidableEq α]
    {A B : PreAbstractSimplicialComplex α} (h : StellarEquivalentUpToRelabeling A B)
    (hA : A.faces.Finite) :
    ∃ a b : α ↪ α ⊕ ℕ, StellarEquivalent (A.map a) (B.map b) := by
  classical
  let Motive : PreAbstractSimplicialComplex α → PreAbstractSimplicialComplex α → Prop :=
    fun X Y => (X.faces.Finite ↔ Y.faces.Finite) ∧
      (X.faces.Finite → ∃ a b : α ↪ α ⊕ ℕ, StellarEquivalent (X.map a) (Y.map b))
  suffices h' : Motive A B from h'.2 hA
  apply h.induction_on
  · exact fun X Y f g hab =>
      ⟨(StellarEquivalentUpToRelabeling.of_common_relabeling f g hab).finite_faces_iff,
        fun _ => ⟨f, g, hab⟩⟩
  · exact fun X =>
      ⟨Iff.rfl, fun _ => ⟨⟨Sum.inl, Sum.inl_injective⟩, ⟨Sum.inl, Sum.inl_injective⟩, .refl _⟩⟩
  · intro X Y ih
    refine ⟨ih.1.symm, fun hY => ?_⟩
    obtain ⟨a, b, he⟩ := ih.2 (ih.1.mpr hY)
    exact ⟨b, a, he.symm⟩
  · intro X Y Z ih₁ ih₂
    refine ⟨ih₁.1.trans ih₂.1, fun hX => ?_⟩
    have hY : Y.faces.Finite := ih₁.1.mp hX
    obtain ⟨a₁, b₁, he₁⟩ := ih₁.2 hX
    obtain ⟨a₂, b₂, he₂⟩ := ih₂.2 hY
    let S : Finset α := hY.toFinset.biUnion id
    obtain ⟨Φ, hΦ⟩ := Equiv.Perm.exists_extending_pair
      (fun x : ↥S => a₂ x) (fun x : ↥S => b₁ x)
      (a₂.injective.comp Subtype.val_injective) (b₁.injective.comp Subtype.val_injective)
    have hYmap : (Y.map a₂).map Φ = Y.map b₁ := by
      rw [map_map]
      exact map_eq_of_eqOn_faces fun σ hσ x hx =>
        hΦ ⟨x, subset_biUnion_of_mem id (hY.mem_toFinset.mpr hσ) hx⟩
    have he₂' : StellarEquivalent (Y.map b₁) (Z.map (b₂.trans Φ.toEmbedding)) := by
      have hm := he₂.map Φ Φ.injective
      rwa [hYmap, map_map] at hm
    exact ⟨a₁, b₂.trans Φ.toEmbedding, he₁.trans he₂'⟩

private theorem extend_to_sum_injective {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {U : Finset ι} {W' : Finset (κ ⊕ ℕ)} (φ : ↥W' ≃ Fin W'.card)
    {h : ι → κ} (hh : Function.Injective h) {c : κ ↪ κ ⊕ ℕ}
    (hcU : ∀ i ∈ U, c (h i) ∈ W') :
    Function.Injective (fun i : ι =>
      if i ∈ U then
        (if hz : c (h i) ∈ W' then Sum.inr (φ ⟨c (h i), hz⟩).1 else Sum.inr W'.card)
      else Sum.inl i) := by
  intro i j hij
  by_cases hi : i ∈ U <;> by_cases hj : j ∈ U
  · have hiW := hcU i hi
    have hjW := hcU j hj
    simp only [hi, hj, ↓reduceIte, hiW, hjW, ↓reduceDIte, Sum.inr.injEq, Fin.val_inj] at hij
    exact hh (c.injective (congrArg Subtype.val (φ.injective hij)))
  · have hiW := hcU i hi
    simp [hi, hj, hiW] at hij
  · have hjW := hcU j hj
    simp [hi, hj, hjW] at hij
  · simpa [hi, hj] using hij

private theorem stellarEquivalentUpToRelabeling_of_map {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {K L : PreAbstractSimplicialComplex ι} (hK : K.faces.Finite)
    {f g : ι → κ} (hf : Function.Injective f) (hg : Function.Injective g)
    (he : StellarEquivalentUpToRelabeling (K.map f) (L.map g)) :
    StellarEquivalentUpToRelabeling K L := by
  have hKf : (K.map f).faces.Finite := (finite_faces_map_iff_of_injective f hf).mpr hK
  have hL : L.faces.Finite :=
    (finite_faces_map_iff_of_injective g hg).mp (he.finite_faces_iff.mp hKf)
  obtain ⟨a, b, hab⟩ := exists_common_relabeling_of_finite_faces he hKf
  obtain ⟨W, _, _, hWmap⟩ := stellarEquivalent_exists_finset_injOn (ι ⊕ ℕ) hab
    ((finite_faces_map_iff_of_injective a a.injective).mpr hKf)
  let U : Finset ι := hK.toFinset.biUnion id ∪ hL.toFinset.biUnion id
  let W' : Finset (κ ⊕ ℕ) := W ∪ U.image (a ∘ f) ∪ U.image (b ∘ g)
  let φ : ↥W' ≃ Fin W'.card := W'.equivFin
  let ψ : κ ⊕ ℕ → ι ⊕ ℕ := fun z =>
    if hz : z ∈ W' then Sum.inr (φ ⟨z, hz⟩).1 else Sum.inr W'.card
  have hψ : Set.InjOn ψ (W : Set (κ ⊕ ℕ)) := by
    intro x hx y hy hxy
    have hx' : x ∈ W' := subset_union_left (subset_union_left hx)
    have hy' : y ∈ W' := subset_union_left (subset_union_left hy)
    simp only [ψ, hx', hy', ↓reduceDIte, Sum.inr.injEq, Fin.val_inj] at hxy
    exact congrArg Subtype.val (φ.injective hxy)
  let a' : ι → ι ⊕ ℕ := fun i => if i ∈ U then ψ (a (f i)) else Sum.inl i
  let b' : ι → ι ⊕ ℕ := fun i => if i ∈ U then ψ (b (g i)) else Sum.inl i
  have ha' : Function.Injective a' :=
    extend_to_sum_injective φ hf fun i hi =>
      subset_union_left (subset_union_right (mem_image_of_mem _ hi))
  have hb' : Function.Injective b' :=
    extend_to_sum_injective φ hg fun i hi =>
      subset_union_right (mem_image_of_mem _ hi)
  have hKeq : (((K.map f).map a).map ψ) = K.map a' := by
    rw [map_map, map_map]
    exact map_eq_of_eqOn_faces fun σ hσ i hi => by
      have hiU : i ∈ U := subset_union_left (subset_biUnion_of_mem id (hK.mem_toFinset.mpr hσ) hi)
      simp [a', hiU]
  have hLeq : (((L.map g).map b).map ψ) = L.map b' := by
    rw [map_map, map_map]
    exact map_eq_of_eqOn_faces fun σ hσ i hi => by
      have hiU : i ∈ U := subset_union_right (subset_biUnion_of_mem id (hL.mem_toFinset.mpr hσ) hi)
      simp [b', hiU]
  apply StellarEquivalentUpToRelabeling.of_common_relabeling ⟨a', ha'⟩ ⟨b', hb'⟩
  simpa only [Function.Embedding.coeFn_mk, hKeq, hLeq] using hWmap ψ hψ

private theorem exists_injective_image_eq {ι κ : Type*} [DecidableEq κ]
    {f : ι → κ} (hf : Function.Injective f) {V : Finset ι} {W : Finset κ}
    (hcard : V.card = W.card) :
    ∃ g : ι → κ, Function.Injective g ∧ V.image g = W := by
  classical
  obtain ⟨Φ, hΦ⟩ := Equiv.Perm.exists_map_finset_eq (V.image f) W
    (by rwa [card_image_of_injective V hf])
  refine ⟨Φ ∘ f, Φ.injective.comp hf, ?_⟩
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding, Finset.image_image] using hΦ

end Transport

section Map

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {K : PreAbstractSimplicialComplex ι} {n : ℕ}

/-- An injective vertex map reflects combinatorial balls. -/
theorem IsCombinatorialBall.of_map (f : ι → κ) (hf : Function.Injective f)
    (h : IsCombinatorialBall (K.map f) n) : IsCombinatorialBall K n := by
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  have hdim : dimension K = (n : WithBot ℕ∞) := by
    rw [← dimension_map_of_injective f hf, h.dimension_eq]
  obtain ⟨V, -, hVcard⟩ := exists_face_card_eq_of_dimension_eq hdim
  obtain ⟨W, hWcard, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨g, hg, hVimg⟩ := exists_injective_image_eq hf (hVcard.trans hWcard.symm)
  rw [← hVimg, ← map_simplex] at he
  exact isCombinatorialBall_iff.mpr ⟨V, hVcard,
    stellarEquivalentUpToRelabeling_of_map hKfin hf hg he⟩

/-- Injective relabeling preserves and reflects combinatorial balls. -/
@[simp]
theorem isCombinatorialBall_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialBall (K.map f) n ↔ IsCombinatorialBall K n :=
  ⟨IsCombinatorialBall.of_map f hf, fun h => h.map f hf⟩

/-- An injective vertex map reflects combinatorial spheres. -/
theorem IsCombinatorialSphere.of_map (f : ι → κ) (hf : Function.Injective f)
    (h : IsCombinatorialSphere (K.map f) n) : IsCombinatorialSphere K n := by
  have hKfin : K.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp h.finite_faces
  have hdim : dimension K = (n : WithBot ℕ∞) := by
    rw [← dimension_map_of_injective f hf, h.dimension_eq]
  obtain ⟨τ, hτ, hτcard⟩ := exists_face_card_eq_of_dimension_eq hdim
  have hnot_le : ¬ K ≤ simplex τ := by
    intro hle
    have hKeq : K = simplex τ := le_antisymm hle (simplex_le_iff.mpr fun _ => hτ)
    have hball : IsCombinatorialBall (K.map f) n := by
      rw [hKeq, map_simplex]
      exact isCombinatorialBall_simplex (by rw [card_image_of_injective τ hf, hτcard])
    exact h.not_isCombinatorialBall hball
  have hex : ∃ u, ({u} : Finset ι) ∈ K ∧ u ∉ τ := by
    by_contra! hall
    exact hnot_le fun σ hσ => mem_simplex.mpr ⟨(K.isRelLowerSet_faces hσ).1,
      fun u hu => hall u (singleton_mem_of_mem hσ hu)⟩
  obtain ⟨u, -, huτ⟩ := hex
  let V : Finset ι := insert u τ
  have hVcard : V.card = n + 2 := by rw [card_insert_of_notMem huτ, hτcard]
  obtain ⟨W, hWcard, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨g, hg, hVimg⟩ := exists_injective_image_eq hf (hVcard.trans hWcard.symm)
  have hmap : (simplexBoundary V).map g = simplexBoundary W := by
    simpa only [Function.Embedding.coeFn_mk, hVimg] using map_simplexBoundary V ⟨g, hg⟩
  rw [← hmap] at he
  exact isCombinatorialSphere_iff.mpr ⟨V, hVcard,
    stellarEquivalentUpToRelabeling_of_map hKfin hf hg he⟩

/-- Injective relabeling preserves and reflects combinatorial spheres. -/
@[simp]
theorem isCombinatorialSphere_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialSphere (K.map f) n ↔ IsCombinatorialSphere K n :=
  ⟨IsCombinatorialSphere.of_map f hf, fun h => h.map f hf⟩

omit [DecidableEq ι] in
private theorem singleton_mem_map_iff {f : ι → κ} {w : κ} :
    ({w} : Finset κ) ∈ K.map f ↔ ∃ v, ({v} : Finset ι) ∈ K ∧ f v = w := by
  constructor
  · intro hw
    obtain ⟨σ, hσ, hσeq⟩ := mem_map_iff.mp hw
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
    have hfv : f v = w := mem_singleton.mp (hσeq ▸ mem_image_of_mem f hv)
    exact ⟨v, singleton_mem_of_mem hσ hv, hfv⟩
  · rintro ⟨v, hv, rfl⟩
    exact mem_map_iff.mpr ⟨{v}, hv, by simp⟩

/-- Injectively relabeling a combinatorial manifold gives a combinatorial manifold of the same
dimension. -/
theorem IsCombinatorialManifold.map (h : IsCombinatorialManifold K n) (f : ι → κ)
    (hf : Function.Injective f) : IsCombinatorialManifold (K.map f) n := by
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hw
    rw [← image_singleton, ← map_link f hf, isCombinatorialManifold_zero_iff.mp h hv]
    exact eq_bot_iff.mpr fun _ ⟨_, hmem, _⟩ => hmem.elim
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := singleton_mem_map_iff.mp hw
    rw [← image_singleton, ← map_link f hf]
    exact (isCombinatorialManifold_succ_iff.mp h hv).imp
      (fun hs => hs.map f hf) (fun hb => hb.map f hf)

/-- An injective vertex map reflects combinatorial manifolds. -/
theorem IsCombinatorialManifold.of_map (f : ι → κ) (hf : Function.Injective f)
    (h : IsCombinatorialManifold (K.map f) n) : IsCombinatorialManifold K n := by
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun v hv => ?_
    have hfv : ({f v} : Finset κ) ∈ K.map f := mem_map_iff.mpr ⟨{v}, hv, by simp⟩
    have hbot := isCombinatorialManifold_zero_iff.mp h hfv
    rw [← image_singleton, ← map_link f hf] at hbot
    refine eq_bot_iff.mpr fun ρ hρ => ?_
    have hmem : ρ.image f ∈ (link K {v}).map f := mem_map_iff.mpr ⟨ρ, hρ, rfl⟩
    rw [hbot] at hmem
    exact hmem.elim
  | succ n =>
    refine isCombinatorialManifold_succ_iff.mpr fun v hv => ?_
    have hfv : ({f v} : Finset κ) ∈ K.map f := mem_map_iff.mpr ⟨{v}, hv, by simp⟩
    have hlink := isCombinatorialManifold_succ_iff.mp h hfv
    rw [← image_singleton, ← map_link f hf, isCombinatorialSphere_map_iff f hf,
      isCombinatorialBall_map_iff f hf] at hlink
    exact hlink

/-- Injective relabeling preserves and reflects combinatorial manifolds. -/
@[simp]
theorem isCombinatorialManifold_map_iff (f : ι → κ) (hf : Function.Injective f) :
    IsCombinatorialManifold (K.map f) n ↔ IsCombinatorialManifold K n :=
  ⟨IsCombinatorialManifold.of_map f hf, fun h => h.map f hf⟩

end Map

/-- Every closed vertex star in a combinatorial `n`-manifold is a combinatorial `n`-ball on the
original vertex type. -/
theorem IsCombinatorialManifold.isCombinatorialBall_closedStar {ι : Type*} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {n : ℕ}
    (h : IsCombinatorialManifold K n) {v : ι} (hv : ({v} : Finset ι) ∈ K) :
    IsCombinatorialBall (closedStar K {v}) n :=
  IsCombinatorialBall.of_map _ (TauCeti.partitionEmbedding (· ∈ ({v} : Finset ι))).injective
    (h.isCombinatorialBall_map_closedStar hv)

end PreAbstractSimplicialComplex
