/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction

/-!
# Vertex relabelings via stellar moves

Starring a singleton `{u}` of a precomplex `K` at a fresh vertex `v` (`{v} ∉ K`) replaces `u` by
`v` in every face containing `u` and leaves every other face unchanged; that is, it equals
`K.map (Equiv.swap u v)` (including when `{u} ∉ K`, in which case both sides equal `K`).
Consequently, replacing a vertex by an unused one is at most a single stellar move.

When `K` has finitely many faces and its vertices are embedded in the infinite vertex supply
`ι ⊕ ℕ`, any two injective relabelings `K.map f` and `K.map g` are therefore linked by a finite
chain of same-type stellar moves, obtained by routing the finitely many used vertices through a
disjoint block of fresh `ℕ`-indices. This collapses the transitive-relabeling closure
`PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling` on finite complexes to a single
stellar equivalence after `Sum.inl`, and shows that arbitrary injective vertex maps both preserve
and reflect `StellarEquivalentUpToRelabeling` on finite complexes across arbitrary universes.

## Main results

* `PreAbstractSimplicialComplex.stellarSubdivision_singleton`: starring `{u}` at a fresh vertex
  `{v} ∉ K` equals `K.map (Equiv.swap u v)`.
* `PreAbstractSimplicialComplex.stellarEquivalent_map_swap`: swapping any vertex with a fresh
  vertex gives a stellar-equivalent complex.
* `PreAbstractSimplicialComplex.stellarEquivalent_map_of_finite_faces`: any two injective maps of a
  finite complex into `ι ⊕ ℕ` have stellar-equivalent images.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_iff_stellarEquivalent_map_inl`:
  for finite complexes, `StellarEquivalentUpToRelabeling K L` is equivalent to
  `StellarEquivalent (K.map Sum.inl) (L.map Sum.inl)`.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_map_iff`: an injective vertex map
  preserves and reflects `StellarEquivalentUpToRelabeling` on finite complexes.
* `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_simplex_of_card_eq` and
  `PreAbstractSimplicialComplex.stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq`:
  standard simplices or simplex boundaries of equal vertex cardinality are intrinsically stellar
  equivalent.

## References

* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

section Swap

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {u v : ι}

private theorem image_swap_eq_self {s : Finset ι} (hu : u ∉ s) (hv : v ∉ s) :
    s.image (Equiv.swap u v) = s := by
  have h : ∀ x ∈ s, Equiv.swap u v x = x := fun _ hx =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hu (h ▸ hx)) (fun h => hv (h ▸ hx))
  exact (image_congr h).trans image_id'

/-- Starring a singleton `{u}` at a fresh vertex `{v} ∉ K` relabels `u` to `v` via
`Equiv.swap u v` (and leaves `K` unchanged when `{u} ∉ K`). -/
theorem stellarSubdivision_singleton (u : ι) (hv : ({v} : Finset ι) ∉ K) :
    stellarSubdivision K {u} v = K.map (Equiv.swap u v) := by
  refine SetLike.ext fun τ => ?_
  rw [mem_map_iff]
  constructor
  · intro hτ
    by_cases hvτ : v ∈ τ
    · have hτ' : insert v (τ.erase v) ∈ stellarSubdivision K {u} v := by
        rwa [insert_erase hvτ]
      obtain ⟨hunot, hface⟩ := (insert_mem_stellarSubdivision_iff (notMem_erase v τ)).mp hτ'
      have huerase : u ∉ τ.erase v := fun h => hunot (singleton_subset_iff.mpr h)
      refine ⟨τ.erase v ∪ {u}, hface, ?_⟩
      rw [image_union, image_swap_eq_self huerase (notMem_erase v τ), image_singleton,
        Equiv.swap_apply_left, union_singleton, insert_erase hvτ]
    · obtain ⟨hτK, hunot⟩ := (mem_stellarSubdivision_iff_of_notMem hvτ).mp hτ
      exact ⟨τ, hτK, image_swap_eq_self (fun h => hunot (singleton_subset_iff.mpr h)) hvτ⟩
  · rintro ⟨ρ, hρK, rfl⟩
    have hvρ : v ∉ ρ := notMem_of_singleton_notMem hv hρK
    by_cases huρ : u ∈ ρ
    · have hv_erase : v ∉ ρ.erase u := fun h => hvρ (mem_of_mem_erase h)
      have himg : ρ.image (Equiv.swap u v) = insert v (ρ.erase u) := by
        conv_lhs => rw [← insert_erase huρ, image_insert, Equiv.swap_apply_left,
          image_swap_eq_self (notMem_erase u ρ) hv_erase]
      rw [himg]
      refine (insert_mem_stellarSubdivision_iff hv_erase).mpr
        ⟨fun h => notMem_erase u ρ (h (mem_singleton_self u)), ?_⟩
      rwa [union_singleton, insert_erase huρ]
    · rw [image_swap_eq_self huρ hvρ]
      exact (mem_stellarSubdivision_iff_of_notMem hvρ).mpr
        ⟨hρK, fun h => huρ (h (mem_singleton_self u))⟩

/-- Swapping any vertex `u` with a fresh vertex `v` (`{v} ∉ K`) produces a stellar-equivalent
complex: if `{u} ∈ K` it is one stellar move, and otherwise `K` is unchanged. -/
theorem stellarEquivalent_map_swap (u : ι) (hv : ({v} : Finset ι) ∉ K) :
    StellarEquivalent K (K.map (Equiv.swap u v)) := by
  rw [← stellarSubdivision_singleton u hv]
  by_cases hu : ({u} : Finset ι) ∈ K
  · exact stellarEquivalent_stellarSubdivision hu hv
  · rw [stellarSubdivision_eq_self_of_notMem hv (singleton_nonempty u) hu]

end Swap

section FiniteRelabeling

/-- Two vertex maps agreeing on a finset containing all faces of `K` induce the same image
complex. -/
private theorem map_congr_of_subset {α β : Type*} [DecidableEq β]
    {K : PreAbstractSimplicialComplex α} {V : Finset α} (hV : ∀ σ ∈ K, σ ⊆ V)
    {f g : α → β} (hfg : ∀ x ∈ V, f x = g x) : K.map f = K.map g := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_map_iff]
  refine exists_congr fun σ => and_congr_right fun hσ => ?_
  rw [image_congr (fun x hx => hfg x (hV σ hσ hx))]

/-- Replacing `f` by `g` on a subset `s ⊆ V` of vertices whose `g`-images all avoid `V.image f`
yields a stellar-equivalent image complex, one fresh vertex swap at a time. -/
private theorem stellarEquivalent_map_of_disjoint {α β : Type*} [DecidableEq β]
    {K : PreAbstractSimplicialComplex α} {V : Finset α} (hV : ∀ σ ∈ K, σ ⊆ V) :
    ∀ {s : Finset α}, s ⊆ V → ∀ {f g : α → β},
      Set.InjOn f V → Set.InjOn g V →
      (∀ x ∈ V, x ∉ s → f x = g x) →
      (∀ x ∈ s, g x ∉ V.image f) →
      StellarEquivalent (K.map f) (K.map g) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ f g _ _ hfg _
    rw [map_congr_of_subset hV fun x hx => hfg x hx (notMem_empty x)]
  | @insert a s has ih =>
    intro hsV f g hf hg hfg hfresh
    have haV : a ∈ V := hsV (mem_insert_self a s)
    let f' : α → β := Function.update f a (g a)
    have hga_notMem : g a ∉ V.image f := hfresh a (mem_insert_self a s)
    -- Step 1: updating `f` at `a` to the unused vertex `g a` is a swap on `K.map f`.
    have hswap : K.map f' = (K.map f).map (Equiv.swap (f a) (g a)) := by
      rw [map_map]
      refine map_congr_of_subset hV fun x hx => ?_
      by_cases hxa : x = a
      · subst hxa; simp [f']
      · have hfx_fa : f x ≠ f a := fun h => hxa (hf hx haV h)
        have hfx_ga : f x ≠ g a := fun h => hga_notMem (h ▸ mem_image_of_mem f hx)
        dsimp only [f', Function.comp_apply]
        rw [Function.update_of_ne hxa, Equiv.swap_apply_of_ne_of_ne hfx_fa hfx_ga]
    have hv_fresh : ({g a} : Finset β) ∉ K.map f := by
      rintro ⟨σ, hσ, hσimg⟩
      obtain ⟨x, hxσ⟩ := (K.isRelLowerSet_faces hσ).1
      have hfx : f x = g a := mem_singleton.mp (hσimg ▸ mem_image_of_mem f hxσ)
      exact hga_notMem (hfx ▸ mem_image_of_mem f (hV σ hσ hxσ))
    have hstep : StellarEquivalent (K.map f) (K.map f') := by
      rw [hswap]; exact stellarEquivalent_map_swap (f a) hv_fresh
    -- Step 2: `f'` remains injective on `V` and leaves the remaining `g`-targets fresh.
    have hf'_inj : Set.InjOn f' V := by
      intro x hx y hy hxy
      by_cases hxa : x = a <;> by_cases hya : y = a
      · exact hxa.trans hya.symm
      · subst hxa; simp only [f', Function.update_self, Function.update_of_ne hya] at hxy
        exact (hga_notMem (hxy ▸ mem_image_of_mem f hy)).elim
      · subst hya; simp only [f', Function.update_self, Function.update_of_ne hxa] at hxy
        exact (hga_notMem (hxy.symm ▸ mem_image_of_mem f hx)).elim
      · simp only [f', Function.update_of_ne hxa, Function.update_of_ne hya] at hxy
        exact hf hx hy hxy
    refine hstep.trans (ih ((subset_insert a s).trans hsV) hf'_inj hg ?_ ?_)
    · intro x hx hxs
      by_cases hxa : x = a
      · subst hxa; simp [f']
      · simp [f', hxa, hfg x hx (by simp [hxa, hxs])]
    · intro x hxs hmem
      obtain ⟨y, hyV, hy⟩ := mem_image.mp hmem
      by_cases hya : y = a
      · subst hya
        simp only [f', Function.update_self] at hy
        exact has (hg (hsV (mem_insert_of_mem hxs)) haV hy.symm ▸ hxs)
      · simp only [f', Function.update_of_ne hya] at hy
        exact hfresh x (mem_insert_of_mem hxs) (hy ▸ mem_image_of_mem f hyV)

/-- Any two injective maps of a finite-face complex into `ι ⊕ ℕ` produce stellar-equivalent
complexes in `ι ⊕ ℕ`. -/
theorem stellarEquivalent_map_of_finite_faces {α ι : Type*} [DecidableEq ι]
    {K : PreAbstractSimplicialComplex α} (hK : K.faces.Finite) {f g : α → ι ⊕ ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    StellarEquivalent (K.map f) (K.map g) := by
  classical
  let V : Finset α := hK.toFinset.biUnion id
  have hV : ∀ σ ∈ K, σ ⊆ V := fun σ hσ x hx =>
    mem_biUnion.mpr ⟨σ, hK.mem_toFinset.mpr hσ, hx⟩
  let usedNat : Finset ℕ := (V.image f ∪ V.image g).toRight
  let N : ℕ := usedNat.sup id + 1
  let e : V ≃ Fin V.card := V.equivFin
  let h : α → ι ⊕ ℕ := fun x =>
    if hx : x ∈ V then Sum.inr (N + (e ⟨x, hx⟩).1) else Sum.inr 0
  have hh : Set.InjOn h V := by
    intro x hx y hy hxy
    have hx' : x ∈ V := mem_coe.mp hx
    have hy' : y ∈ V := mem_coe.mp hy
    dsimp only [h] at hxy
    simp only [hx', hy', ↓reduceDIte, Sum.inr.injEq, add_right_inj] at hxy
    exact congrArg Subtype.val (e.injective (Fin.ext hxy))
  have hfresh (x : α) (hx : x ∈ V) :
      h x ∉ V.image f ∧ h x ∉ V.image g := by
    have hnot : N + (e ⟨x, hx⟩).1 ∉ usedNat := by
      intro hmem
      have hle : N + (e ⟨x, hx⟩).1 ≤ usedNat.sup id := le_sup (f := id) hmem
      omega
    have hhx : h x = Sum.inr (N + (e ⟨x, hx⟩).1) := by simp [h, hx]
    refine ⟨fun hmem => hnot ?_, fun hmem => hnot ?_⟩
    · exact mem_toRight.mpr (mem_union_left _ (hhx ▸ hmem))
    · exact mem_toRight.mpr (mem_union_right _ (hhx ▸ hmem))
  have hfh := stellarEquivalent_map_of_disjoint hV Subset.rfl hf.injOn hh
    (fun _ hx hnot => (hnot hx).elim) (fun x hx => (hfresh x hx).1)
  have hgh := stellarEquivalent_map_of_disjoint hV Subset.rfl hg.injOn hh
    (fun _ hx hnot => (hnot hx).elim) (fun x hx => (hfresh x hx).2)
  exact hfh.trans hgh.symm

/-- For a complex with finitely many faces, `StellarEquivalentUpToRelabeling K L` collapses to a
single same-type `StellarEquivalent` after embedding into `ι ⊕ ℕ` via `Sum.inl`. -/
theorem stellarEquivalentUpToRelabeling_iff_stellarEquivalent_map_inl
    {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι} (hK : K.faces.Finite) :
    StellarEquivalentUpToRelabeling K L ↔
      StellarEquivalent (K.map (Sum.inl : ι → ι ⊕ ℕ)) (L.map (Sum.inl : ι → ι ⊕ ℕ)) := by
  refine ⟨fun h => ?_, fun h =>
    StellarEquivalentUpToRelabeling.of_common_relabeling
      ⟨Sum.inl, Sum.inl_injective⟩ ⟨Sum.inl, Sum.inl_injective⟩ h⟩
  suffices hboth : (K.faces.Finite ↔ L.faces.Finite) ∧
      (K.faces.Finite →
        StellarEquivalent (K.map (Sum.inl : ι → ι ⊕ ℕ)) (L.map (Sum.inl : ι → ι ⊕ ℕ))) from
    hboth.2 hK
  refine h.induction_on
    (P := fun A B => (A.faces.Finite ↔ B.faces.Finite) ∧
      (A.faces.Finite →
        StellarEquivalent (A.map (Sum.inl : ι → ι ⊕ ℕ)) (B.map (Sum.inl : ι → ι ⊕ ℕ))))
    ?_ (fun _ => ⟨Iff.rfl, fun _ => .refl _⟩)
    (fun _ _ ih => ⟨ih.1.symm, fun hB => (ih.2 (ih.1.mpr hB)).symm⟩)
    (fun _ _ _ ih₁ ih₂ => ⟨ih₁.1.trans ih₂.1, fun hA => (ih₁.2 hA).trans (ih₂.2 (ih₁.1.mp hA))⟩)
  intro A B a b he
  have hiff : A.faces.Finite ↔ B.faces.Finite :=
    (finite_faces_map_iff_of_injective a a.injective).symm.trans
      (he.finite_faces_iff.trans (finite_faces_map_iff_of_injective b b.injective))
  refine ⟨hiff, fun hAfin => ?_⟩
  exact (stellarEquivalent_map_of_finite_faces hAfin Sum.inl_injective a.injective).trans
    (he.trans (stellarEquivalent_map_of_finite_faces (hiff.mp hAfin) b.injective
      Sum.inl_injective))

private theorem restrict_stellarSubdivision {α : Type*} [DecidableEq α]
    {A : PreAbstractSimplicialComplex α} {σ : Finset α} {v : α} {U : Finset α}
    (hvU : v ∈ U) (hAU : ∀ τ ∈ A, (τ : Set α) ⊆ U)
    (hBU : ∀ τ ∈ stellarSubdivision A σ v, (τ : Set α) ⊆ U)
    (hσeq : (σ.subtype (· ∈ (U : Set α))).image Subtype.val = σ) :
    (stellarSubdivision A σ v).restrict (U : Set α) =
      stellarSubdivision (A.restrict (U : Set α)) (σ.subtype (· ∈ (U : Set α))) ⟨v, hvU⟩ := by
  have hmap : ((stellarSubdivision A σ v).restrict (U : Set α)).map Subtype.val =
      (stellarSubdivision (A.restrict (U : Set α))
        (σ.subtype (· ∈ (U : Set α))) ⟨v, hvU⟩).map Subtype.val := by
    rw [map_val_restrict_of_subset _ hBU, map_stellarSubdivision Subtype.val Subtype.val_injective,
      map_val_restrict_of_subset _ hAU, hσeq]
  refine SetLike.ext fun τ => ?_
  have hinj := image_injective (Subtype.val_injective (p := (· ∈ (U : Set α))))
  constructor <;> intro hτ
  · obtain ⟨_, hρ, h⟩ := mem_map_iff.mp (hmap ▸ mem_map_iff.mpr ⟨τ, hτ, rfl⟩)
    exact hinj h ▸ hρ
  · obtain ⟨_, hρ, h⟩ := mem_map_iff.mp (hmap.symm ▸ mem_map_iff.mpr ⟨τ, hτ, rfl⟩)
    exact hinj h ▸ hρ

/-- Every same-type stellar equivalence starting at a finite complex takes place inside some
finite vertex set `U` extending any prescribed finite set `S`. -/
private theorem exists_finset_subset_of_stellarEquivalent {α : Type*} [DecidableEq α]
    {X Y : PreAbstractSimplicialComplex α} (hXY : StellarEquivalent X Y) (hX : X.faces.Finite)
    (S : Finset α) :
    ∃ U : Finset α, S ⊆ U ∧ (∀ σ ∈ X, σ ⊆ U) ∧ (∀ σ ∈ Y, σ ⊆ U) ∧
      StellarEquivalent (X.restrict (U : Set α)) (Y.restrict (U : Set α)) := by
  suffices hboth : (X.faces.Finite ↔ Y.faces.Finite) ∧
      (X.faces.Finite → ∀ S : Finset α, ∃ U : Finset α, S ⊆ U ∧
        (∀ σ ∈ X, σ ⊆ U) ∧ (∀ σ ∈ Y, σ ⊆ U) ∧
        StellarEquivalent (X.restrict (U : Set α)) (Y.restrict (U : Set α))) from hboth.2 hX S
  refine hXY.induction_on
    (P := fun X Y => (X.faces.Finite ↔ Y.faces.Finite) ∧
      (X.faces.Finite → ∀ S : Finset α, ∃ U : Finset α, S ⊆ U ∧
        (∀ σ ∈ X, σ ⊆ U) ∧ (∀ σ ∈ Y, σ ⊆ U) ∧
        StellarEquivalent (X.restrict (U : Set α)) (Y.restrict (U : Set α)))) ?_ ?_ ?_ ?_
  · intro A B hmove
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hmove
    refine ⟨hmove.finite_faces_iff, fun hAfin S => ?_⟩
    let U : Finset α := S ∪ insert v (hAfin.toFinset.biUnion id)
    have hvU : v ∈ U := subset_union_right (mem_insert_self v _)
    have hAU : ∀ τ ∈ A, τ ⊆ U := fun τ hτ x hx =>
      subset_union_right (mem_insert_of_mem
        (mem_biUnion.mpr ⟨τ, hAfin.mem_toFinset.mpr hτ, hx⟩))
    have hBU : ∀ τ ∈ stellarSubdivision A σ v, τ ⊆ U := by
      intro τ hτ x hx
      rcases mem_stellarSubdivision_iff.mp hτ with ⟨-, hτA, -⟩ | ⟨-, -, hτA⟩
      · exact hAU τ hτA hx
      · by_cases hxv : x = v
        · exact hxv ▸ hvU
        · exact hAU _ hτA (mem_union_left _ (mem_erase.mpr ⟨hxv, hx⟩))
    have hσeq : (σ.subtype (· ∈ (U : Set α))).image Subtype.val = σ := by
      simpa only [map_eq_image, Function.Embedding.coe_subtype] using
        subtype_map_of_mem (coe_subset.mpr (hAU σ hσ))
    have hσU : σ.subtype (· ∈ (U : Set α)) ∈ A.restrict (U : Set α) :=
      (mem_restrict_iff A U _).mpr (hσeq.symm ▸ hσ)
    have hvnotU : ({(⟨v, hvU⟩ : (U : Set α))} : Finset (U : Set α)) ∉ A.restrict (U : Set α) := by
      simpa only [mem_restrict_iff, image_singleton] using hv
    refine ⟨U, subset_union_left, hAU, hBU, ?_⟩
    rw [restrict_stellarSubdivision hvU (fun τ hτ => coe_subset.mpr (hAU τ hτ))
      (fun τ hτ => coe_subset.mpr (hBU τ hτ)) hσeq]
    exact stellarEquivalent_stellarSubdivision hσU hvnotU
  · intro A
    refine ⟨Iff.rfl, fun hAfin S => ?_⟩
    let U : Finset α := S ∪ hAfin.toFinset.biUnion id
    have hAU : ∀ τ ∈ A, τ ⊆ U := fun τ hτ x hx =>
      subset_union_right (mem_biUnion.mpr ⟨τ, hAfin.mem_toFinset.mpr hτ, hx⟩)
    exact ⟨U, subset_union_left, hAU, hAU, .refl _⟩
  · intro A B ih
    refine ⟨ih.1.symm, fun hBfin S => ?_⟩
    obtain ⟨U, hSU, hAU, hBU, he⟩ := ih.2 (ih.1.mpr hBfin) S
    exact ⟨U, hSU, hBU, hAU, he.symm⟩
  · intro A B C ih₁ ih₂
    refine ⟨ih₁.1.trans ih₂.1, fun hAfin S => ?_⟩
    obtain ⟨U₁, hSU₁, hAU₁, hBU₁, he₁⟩ := ih₁.2 hAfin S
    obtain ⟨U, hU₁U, _, hCU, he₂⟩ := ih₂.2 (ih₁.1.mp hAfin) U₁
    have hsub : (U₁ : Set α) ⊆ (U : Set α) := coe_subset.mpr hU₁U
    have hinc := he₁.map (Set.inclusion hsub) (Set.inclusion_injective hsub)
    rw [map_inclusion_restrict_of_subset A hsub (fun τ hτ => coe_subset.mpr (hAU₁ τ hτ)),
      map_inclusion_restrict_of_subset B hsub (fun τ hτ => coe_subset.mpr (hBU₁ τ hτ))] at hinc
    exact ⟨U, hSU₁.trans hU₁U, fun τ hτ => (hAU₁ τ hτ).trans hU₁U, hCU, hinc.trans he₂⟩

private theorem image_psi_eq_image_inl {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {V σ : Finset ι} {f : ι → κ} {U : Finset (κ ⊕ ℕ)} {τ : Finset ↥(U : Set (κ ⊕ ℕ))}
    (hVU : V.image (Sum.inl ∘ f) ⊆ U) (hσV : σ ⊆ V)
    (hτval : τ.image Subtype.val = σ.image (Sum.inl ∘ f))
    {ψ : ↥(U : Set (κ ⊕ ℕ)) → ι ⊕ ℕ}
    (hψ_apply : ∀ i (hi : i ∈ V),
      ψ ⟨Sum.inl (f i), hVU (mem_image_of_mem (Sum.inl ∘ f) hi)⟩ = Sum.inl i) :
    τ.image ψ = σ.image (Sum.inl : ι → ι ⊕ ℕ) := by
  have hτeq : τ = σ.attach.image (fun x =>
      (⟨Sum.inl (f x.1), hVU (mem_image_of_mem (Sum.inl ∘ f) (hσV x.2))⟩ :
        ↥(U : Set (κ ⊕ ℕ)))) := by
    apply image_injective (Subtype.val_injective (p := (· ∈ (U : Set (κ ⊕ ℕ)))))
    rw [hτval]
    ext y
    simp only [mem_image, Function.comp_apply, mem_attach, true_and, Subtype.exists,
      Subtype.mk.injEq, exists_prop, exists_eq_right_right, mem_coe]
    exact ⟨fun ⟨x, hx, hxy⟩ =>
      ⟨hxy ▸ hVU (mem_image_of_mem (Sum.inl ∘ f) (hσV hx)), x, hx, hxy⟩, And.right⟩
  rw [hτeq, image_image]
  have hlhs : σ.attach.image
      ((ψ ∘ fun x : {x // x ∈ σ} =>
        (⟨Sum.inl (f x.1), hVU (mem_image_of_mem (Sum.inl ∘ f) (hσV x.2))⟩ :
          ↥(U : Set (κ ⊕ ℕ))))) =
      σ.attach.image (fun x : {x // x ∈ σ} => (Sum.inl x.1 : ι ⊕ ℕ)) :=
    image_congr fun x _ => hψ_apply x.1 (hσV x.2)
  rw [hlhs]
  ext y
  simp

private theorem map_restrict_pullback {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {V : Finset ι} {f : ι → κ} {U : Finset (κ ⊕ ℕ)}
    (hVU : V.image (Sum.inl ∘ f) ⊆ U) {ψ : ↥(U : Set (κ ⊕ ℕ)) → ι ⊕ ℕ}
    (hψ_apply : ∀ i (hi : i ∈ V),
      ψ ⟨Sum.inl (f i), hVU (mem_image_of_mem (Sum.inl ∘ f) hi)⟩ = Sum.inl i)
    (M : PreAbstractSimplicialComplex ι) (hMV : ∀ σ ∈ M, σ ⊆ V)
    (hMU : ∀ τ ∈ (M.map f).map (Sum.inl : κ → κ ⊕ ℕ), τ ⊆ U) :
    (((M.map f).map (Sum.inl : κ → κ ⊕ ℕ)).restrict (U : Set (κ ⊕ ℕ))).map ψ =
      M.map (Sum.inl : ι → ι ⊕ ℕ) := by
  refine SetLike.ext fun ω => ?_
  rw [mem_map_iff, mem_map_iff]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [mem_restrict_iff, map_map, mem_map_iff] at hτ
    obtain ⟨σ, hσM, hσeq⟩ := hτ
    exact ⟨σ, hσM, (image_psi_eq_image_inl hVU (hMV σ hσM) hσeq.symm hψ_apply).symm⟩
  · rintro ⟨σ, hσM, rfl⟩
    let τ : Finset ↥(U : Set (κ ⊕ ℕ)) := (σ.image (Sum.inl ∘ f)).subtype (· ∈ (U : Set (κ ⊕ ℕ)))
    have hmem : σ.image (Sum.inl ∘ f) ∈ (M.map f).map (Sum.inl : κ → κ ⊕ ℕ) := by
      rw [map_map]
      exact mem_map_iff.mpr ⟨σ, hσM, rfl⟩
    have hτval : τ.image Subtype.val = σ.image (Sum.inl ∘ f) := by
      simpa only [τ, map_eq_image, Function.Embedding.coe_subtype] using
        subtype_map_of_mem (coe_subset.mpr (hMU _ hmem))
    exact ⟨τ, (mem_restrict_iff _ _ τ).mpr (hτval.symm ▸ hmem),
      image_psi_eq_image_inl hVU (hMV σ hσM) hτval hψ_apply⟩

/-- An injective vertex map preserves and reflects `StellarEquivalentUpToRelabeling` on finite
complexes, across arbitrary vertex universes. -/
theorem stellarEquivalentUpToRelabeling_map_iff {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {K L : PreAbstractSimplicialComplex ι} (f : ι → κ) (hf : Function.Injective f)
    (hK : K.faces.Finite) :
    StellarEquivalentUpToRelabeling (K.map f) (L.map f) ↔
      StellarEquivalentUpToRelabeling K L := by
  refine ⟨fun h => ?_, fun h => h.map f hf⟩
  have hKf : (K.map f).faces.Finite := (finite_faces_map_iff_of_injective f hf).mpr hK
  have hLf : (L.map f).faces.Finite := h.finite_faces_iff.mp hKf
  have hL : L.faces.Finite := (finite_faces_map_iff_of_injective f hf).mp hLf
  have he := (stellarEquivalentUpToRelabeling_iff_stellarEquivalent_map_inl hKf).mp h
  let V : Finset ι := hK.toFinset.biUnion id ∪ hL.toFinset.biUnion id
  have hKV : ∀ σ ∈ K, σ ⊆ V := fun σ hσ x hx =>
    mem_union_left _ (mem_biUnion.mpr ⟨σ, hK.mem_toFinset.mpr hσ, hx⟩)
  have hLV : ∀ σ ∈ L, σ ⊆ V := fun σ hσ x hx =>
    mem_union_right _ (mem_biUnion.mpr ⟨σ, hL.mem_toFinset.mpr hσ, hx⟩)
  obtain ⟨U, hVU, hXU, hYU, heU⟩ :=
    exists_finset_subset_of_stellarEquivalent he
      ((finite_faces_map_iff_of_injective Sum.inl Sum.inl_injective).mpr hKf)
      (V.image (Sum.inl ∘ f))
  classical
  let eqv : ↥(U : Set (κ ⊕ ℕ)) ≃ Fin U.card := U.equivFin
  let ψ : ↥(U : Set (κ ⊕ ℕ)) → ι ⊕ ℕ := fun u =>
    if hex : ∃ i : ι, Sum.inl (f i) = u.1 then Sum.inl (Classical.choose hex)
    else Sum.inr (eqv u).1
  have hψ : Function.Injective ψ := by
    intro u₁ u₂ h₁₂
    dsimp only [ψ] at h₁₂
    by_cases h₁ : ∃ i : ι, Sum.inl (f i) = u₁.1 <;>
      by_cases h₂ : ∃ i : ι, Sum.inl (f i) = u₂.1
    · simp only [h₁, h₂, ↓reduceDIte, Sum.inl.injEq] at h₁₂
      apply Subtype.ext
      rw [← Classical.choose_spec h₁, ← Classical.choose_spec h₂, h₁₂]
    · simp [h₁, h₂] at h₁₂
    · simp [h₁, h₂] at h₁₂
    · simp only [h₁, h₂, ↓reduceDIte, Sum.inr.injEq] at h₁₂
      exact eqv.injective (Fin.ext h₁₂)
  have hψ_apply (i : ι) (hi : i ∈ V) :
      ψ ⟨Sum.inl (f i), hVU (mem_image_of_mem (Sum.inl ∘ f) hi)⟩ = Sum.inl i := by
    have hex : ∃ j : ι, Sum.inl (f j) = (Sum.inl (f i) : κ ⊕ ℕ) := ⟨i, rfl⟩
    dsimp only [ψ]
    rw [dite_eq_left_of_eq_true (eq_true hex), Sum.inl.injEq]
    exact hf (Sum.inl_injective (Classical.choose_spec hex))
  have hmapped := heU.map ψ hψ
  rw [map_restrict_pullback hVU hψ_apply K hKV hXU,
    map_restrict_pullback hVU hψ_apply L hLV hYU] at hmapped
  exact (stellarEquivalentUpToRelabeling_iff_stellarEquivalent_map_inl hK).mpr hmapped

end FiniteRelabeling

section StandardModels

private noncomputable def finsetIndexEmbedding {ι : Type*} [DecidableEq ι]
    (V : Finset ι) : ι ↪ ι ⊕ ℕ where
  toFun x := if hx : x ∈ V then Sum.inr (V.equivFin ⟨x, hx⟩).1 else Sum.inl x
  inj' x y hxy := by
    dsimp only at hxy
    by_cases hx : x ∈ V <;> by_cases hy : y ∈ V
    · simp only [hx, hy, ↓reduceDIte, Sum.inr.injEq] at hxy
      exact congrArg Subtype.val (V.equivFin.injective (Fin.ext hxy))
    · simp [hx, hy] at hxy
    · simp [hx, hy] at hxy
    · simpa [hx, hy] using hxy

private theorem finsetIndexEmbedding_apply {ι : Type*} [DecidableEq ι]
    (V : Finset ι) (x : ι) :
    finsetIndexEmbedding V x =
      if hx : x ∈ V then Sum.inr (V.equivFin ⟨x, hx⟩).1 else Sum.inl x := rfl

private theorem image_finsetIndexEmbedding {ι : Type*} [DecidableEq ι] (V : Finset ι) :
    V.image (finsetIndexEmbedding V) = (range V.card).image Sum.inr := by
  ext (x | k)
  · simp only [mem_image, finsetIndexEmbedding_apply, reduceCtorEq, and_false, exists_false,
      iff_false]
    rintro ⟨a, ha, h⟩
    simp [ha] at h
  · simp only [mem_image, finsetIndexEmbedding_apply, mem_range, Sum.inr.injEq, exists_eq_right]
    refine ⟨?_, fun hk => ?_⟩
    · rintro ⟨a, ha, h⟩
      simp only [ha, ↓reduceDIte, Sum.inr.injEq] at h
      exact h ▸ (V.equivFin ⟨a, ha⟩).2
    · let a := V.equivFin.symm ⟨k, hk⟩
      refine ⟨a.1, a.2, ?_⟩
      rw [dite_eq_left_of_eq_true (eq_true a.2)]
      simp [a]

/-- Two standard simplices on vertex sets of the same cardinality are stellar equivalent up to
relabeling. -/
theorem stellarEquivalentUpToRelabeling_simplex_of_card_eq {ι : Type*} [DecidableEq ι]
    {V W : Finset ι} (hcard : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplex V) (simplex W) := by
  refine StellarEquivalentUpToRelabeling.of_common_relabeling
    (finsetIndexEmbedding V) (finsetIndexEmbedding W) ?_
  rw [map_simplex, map_simplex, image_finsetIndexEmbedding, image_finsetIndexEmbedding, hcard]

/-- Two standard simplex boundaries on vertex sets of the same cardinality are stellar equivalent up
to relabeling. -/
theorem stellarEquivalentUpToRelabeling_simplexBoundary_of_card_eq {ι : Type*} [DecidableEq ι]
    {V W : Finset ι} (hcard : V.card = W.card) :
    StellarEquivalentUpToRelabeling (simplexBoundary V) (simplexBoundary W) := by
  refine StellarEquivalentUpToRelabeling.of_common_relabeling
    (finsetIndexEmbedding V) (finsetIndexEmbedding W) ?_
  rw [map_simplexBoundary V (finsetIndexEmbedding V),
    map_simplexBoundary W (finsetIndexEmbedding W),
    image_finsetIndexEmbedding, image_finsetIndexEmbedding, hcard]

end StandardModels

end PreAbstractSimplicialComplex
