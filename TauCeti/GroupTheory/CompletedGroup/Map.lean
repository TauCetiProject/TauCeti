/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.CompletedGroup.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Maps of completed groups

A natural transformation from a reindexed group tower to another tower induces a
homomorphism of completed groups. The reindexing is any monotone map of natural
numbers; it need not be cofinal. Projection computes the map at its prescribed
cutoff, and the resulting homomorphism respects identity and composition.

Enlarging the source cutoffs and precomposing with the tower transitions leaves
the completed map unchanged. In particular, maps inverse to one another up to
such transitions give an equivalence of completed groups. This permits comparison
of completions formed using different but cofinal filtrations.
In particular, `TauCeti.CompletedGroup.congr` sends an isomorphism of towers to an
equivalence of their completions, computed by the isomorphism at each projection.

The construction uses `CompletedGroup.lift`, the compatible-family universal
property of the subgroup obtained from Mathlib's `GrpCat.sectionsSubgroup`.
Tower maps use Mathlib's natural transformations rather than a separate bundle.

Adapted from `yuma-mizuno-lean/Mei`, commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`,
`Mei/GroupTheory/CompletedGroup/Map.lean` (Apache 2.0).
-/

public section

open CategoryTheory CategoryTheory.Functor Opposite

universe u

namespace TauCeti.CompletedGroup

variable {F : ℕᵒᵖ ⥤ GrpCat.{u}} {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  {H : ℕᵒᵖ ⥤ GrpCat.{u}}

/-- The homomorphism of completed groups induced by a map of reindexed towers. -/
def map (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G) :
    completedGroup F →* completedGroup G :=
  lift (fun k => (f.app (op k)).hom.comp (projection (ρ k))) (by
    intro k l h
    ext x
    have hf := ConcreteCategory.congr_hom (f.naturality (homOfLE h).op)
      (projection (ρ l) x)
    have hmap : ρ.toFunctor.map (homOfLE h) = homOfLE (ρ.monotone h) :=
      Subsingleton.elim _ _
    simpa [hmap] using hf.symm)

/-- The order-`k` component uses only the source component at order `ρ k`. -/
@[simp]
theorem projection_map (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (k : ℕ) (x : completedGroup F) :
    projection k (map ρ f x) = f.app (op k) (projection (ρ k) x) :=
  projection_lift _ _ k x

/-- The projection formula uniquely characterizes the induced homomorphism. -/
theorem map_unique (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (g : completedGroup F →* completedGroup G)
    (hg : ∀ k, (projection k).comp g =
      (f.app (op k)).hom.comp (projection (ρ k))) : g = map ρ f :=
  lift_unique _ _ g hg

/-- Any finer source projection computes the same target component. -/
theorem projection_map_of_le (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (k n : ℕ) (h : ρ k ≤ n) (x : completedGroup F) :
    projection k (map ρ f x) =
      f.app (op k) (F.map (homOfLE h).op (projection n x)) := by
  rw [map_projection, projection_map]

/-- The induced homomorphism satisfies the same cutoff estimate on degree filtrations. -/
theorem map_mem_degreeFiltration (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (k : ℕ) {x : completedGroup F}
    (hx : x ∈ degreeFiltration F (ρ k + 1)) :
    map ρ f x ∈ degreeFiltration G (k + 1) := by
  simp only [degreeFiltration_succ, MonoidHom.mem_ker] at hx ⊢
  simp [hx]

/-- The identity transformation with unchanged cutoffs induces the identity. -/
@[simp]
theorem map_id : map (OrderHom.id : ℕ →o ℕ) (𝟙 F) = MonoidHom.id _ := by
  ext x k
  exact (projection_map (F := F) (G := F) OrderHom.id (𝟙 F) k x).trans
    (GrpCat.id_apply _ _)

/-- Successive maps compose their source cutoffs in the order `ρ ∘ μ`. -/
@[simp]
theorem map_comp (ρ μ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (g : μ.toFunctor.op ⋙ G ⟶ H) :
    map (ρ.comp μ) (whiskerLeft μ.toFunctor.op f ≫ g) =
      (map μ g).comp (map ρ f) := by
  ext x k
  simp only [MonoidHom.comp_apply, projection_map]
  exact GrpCat.comp_apply _ _ _

/-- Compare two tower maps by evaluating both at a common finer source cutoff.
The common cutoff can be chosen separately for each target order. -/
theorem map_eq (ρ μ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (g : μ.toFunctor.op ⋙ F ⟶ G)
    (hfg : ∀ k, ∃ n, ∃ (hρ : ρ k ≤ n) (hμ : μ k ≤ n),
      F.map (homOfLE hρ).op ≫ f.app (op k) =
        F.map (homOfLE hμ).op ≫ g.app (op k)) :
    map ρ f = map μ g := by
  ext x k
  obtain ⟨n, hρ, hμ, h⟩ := hfg k
  rw [projection_map_of_le ρ f k n hρ, projection_map_of_le μ g k n hμ]
  exact ConcreteCategory.congr_hom h (projection n x)

/-- Enlarging a cutoff and precomposing with transitions does not change the map. -/
theorem map_eq_of_le (ρ μ : ℕ →o ℕ) (h : ρ ≤ μ)
    (f : ρ.toFunctor.op ⋙ F ⟶ G) (g : μ.toFunctor.op ⋙ F ⟶ G)
    (hfg : ∀ k, F.map (homOfLE (h k)).op ≫ f.app (op k) = g.app (op k)) :
    map ρ f = map μ g := by
  apply map_eq ρ μ f g
  intro k
  refine ⟨μ k, h k, le_rfl, ?_⟩
  simpa using hfg k

/-- A tower map agreeing with identity after passage to finer cutoffs induces identity. -/
theorem map_eq_id (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ F)
    (hf : ∀ k, ∃ n, ∃ (hρ : ρ k ≤ n) (hk : k ≤ n),
      F.map (homOfLE hρ).op ≫ f.app (op k) = F.map (homOfLE hk).op) :
    map ρ f = MonoidHom.id _ := by
  rw [← map_id (F := F)]
  apply map_eq ρ OrderHom.id f (𝟙 F)
  intro k
  obtain ⟨n, hρ, hk, h⟩ := hf k
  exact ⟨n, hρ, hk, h.trans (Category.comp_id _).symm⟩

/-- Inverse tower comparisons after passage to finer cutoffs give inverse completed maps.
No surjectivity hypothesis on either tower is needed. -/
theorem map_leftInverse (ρ μ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
    (g : μ.toFunctor.op ⋙ G ⟶ F)
    (hgf : ∀ k, ∃ n, ∃ (hρ : ρ (μ k) ≤ n) (hk : k ≤ n),
      F.map (homOfLE hρ).op ≫ f.app (op (μ k)) ≫ g.app (op k) =
        F.map (homOfLE hk).op) :
    Function.LeftInverse (map μ g) (map ρ f) := by
  have hm := map_eq_id (ρ.comp μ) (whiskerLeft μ.toFunctor.op f ≫ g) hgf
  intro x
  exact DFunLike.congr_fun ((map_comp ρ μ f g).symm.trans hm) x

section Equiv

variable (ρ μ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G)
  (g : μ.toFunctor.op ⋙ G ⟶ F)
  (hgf : ∀ k, ∃ n, ∃ (hρ : ρ (μ k) ≤ n) (hk : k ≤ n),
    F.map (homOfLE hρ).op ≫ f.app (op (μ k)) ≫ g.app (op k) =
      F.map (homOfLE hk).op)
  (hfg : ∀ k, ∃ n, ∃ (hμ : μ (ρ k) ≤ n) (hk : k ≤ n),
    G.map (homOfLE hμ).op ≫ g.app (op (ρ k)) ≫ f.app (op k) =
      G.map (homOfLE hk).op)

/-- Comparisons inverse after passage to finer cutoffs identify the two completions. -/
def mapEquiv : completedGroup F ≃* completedGroup G :=
  { map ρ f with
    invFun := map μ g
    left_inv := map_leftInverse ρ μ f g hgf
    right_inv := map_leftInverse μ ρ g f hfg }

@[simp]
theorem mapEquiv_apply (x : completedGroup F) :
    mapEquiv ρ μ f g hgf hfg x = map ρ f x :=
  (rfl)

@[simp]
theorem mapEquiv_symm_apply (x : completedGroup G) :
    (mapEquiv ρ μ f g hgf hfg).symm x = map μ g x :=
  (rfl)

end Equiv

/-- An isomorphism of group towers identifies their compatible-family completions. -/
def congr (e : F ≅ G) : completedGroup F ≃* completedGroup G :=
  mapEquiv OrderHom.id OrderHom.id e.hom e.inv
    (fun k => ⟨k, le_rfl, le_rfl, by
      have hid : F.map (homOfLE (le_rfl : k ≤ k)).op = 𝟙 (F.obj (op k)) :=
        (congrArg F.map (Subsingleton.elim _ _)).trans (F.map_id _)
      rw [hid]
      exact (congrArg (fun f => f ≫ e.hom.app (op k) ≫ e.inv.app (op k)) hid).trans
        ((Category.id_comp _).trans (e.hom_inv_id_app (op k)))⟩)
    (fun k => ⟨k, le_rfl, le_rfl, by
      have hid : G.map (homOfLE (le_rfl : k ≤ k)).op = 𝟙 (G.obj (op k)) :=
        (congrArg G.map (Subsingleton.elim _ _)).trans (G.map_id _)
      rw [hid]
      exact (congrArg (fun f => f ≫ e.inv.app (op k) ≫ e.hom.app (op k)) hid).trans
        ((Category.id_comp _).trans (e.inv_hom_id_app (op k)))⟩)

/-- The forward map is induced by the forward tower isomorphism. -/
theorem congr_apply (e : F ≅ G) (x : completedGroup F) :
    congr e x = map OrderHom.id e.hom x := (rfl)

/-- The inverse map is induced by the inverse tower isomorphism. -/
theorem congr_symm_apply (e : F ≅ G) (x : completedGroup G) :
    (congr e).symm x = map OrderHom.id e.inv x := (rfl)

/-- The tower isomorphism computes the induced equivalence at every projection. -/
@[simp]
theorem projection_congr (e : F ≅ G) (k : ℕ) (x : completedGroup F) :
    projection k (congr e x) = e.hom.app (op k) (projection k x) := by
  rw [congr_apply]
  exact projection_map OrderHom.id e.hom k x

/-- The inverse tower isomorphism computes the inverse completed equivalence. -/
@[simp]
theorem projection_congr_symm (e : F ≅ G) (k : ℕ) (x : completedGroup G) :
    projection k ((congr e).symm x) = e.inv.app (op k) (projection k x) := by
  rw [congr_symm_apply]
  exact projection_map OrderHom.id e.inv k x

end TauCeti.CompletedGroup
