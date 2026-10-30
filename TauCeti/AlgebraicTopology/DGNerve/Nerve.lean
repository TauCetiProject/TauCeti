/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.AlgebraicTopology.DGNerve.Basic
public import TauCeti.CategoryTheory.DG.ClosedCategory

/-!
# The differential graded nerve and the ordinary nerve

Let `C` be a differential graded category and `Z⁰(C)` its underlying ordinary category, whose
morphisms are the closed degree-zero morphisms (Mathlib's
`ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) C`). A string of composable morphisms of
`Z⁰(C)` is an `n`-simplex of the differential graded nerve `N_dg(C)`: take the morphisms of the
string as the coherences without interior vertices and zero as every higher coherence. This gives a
map of simplicial sets `nerve Z⁰(C) ⟶ N_dg(C)`, which is the identity on vertices.

In general this map is far from surjective, since a simplex of `N_dg(C)` records homotopies and
higher homotopies of negative degree rather than equalities. When the Hom complexes of `C` vanish in
negative degrees there is nothing to record: every higher coherence of a simplex is zero, and a
`2`-simplex says that its long edge is the composite of the two short ones. The map is then an
isomorphism, so the differential graded nerve of a differential graded category with Hom complexes
concentrated in degree zero is the nerve of its underlying category. Nothing is assumed about the
positive degrees, which the differential graded nerve does not see.

## Main definitions

* `TauCeti.DGNerve.Simplex.ofComposableArrows`: the simplex of the differential graded nerve given
  by a string of closed degree-zero morphisms.
* `TauCeti.dgNerve.fromNerve`: the resulting map `nerve Z⁰(C) ⟶ N_dg(C)`.
* `TauCeti.dgNerve.nerveIso`: the isomorphism `nerve Z⁰(C) ≅ N_dg(C)` when the Hom complexes vanish
  in negative degrees.

## Main results

* `TauCeti.DGNerve.Simplex.coh_eq_dgComp_of_coh_eq_zero`: if the homotopy carried by a `2`-face of
  a simplex vanishes, its long edge is the composite of its two short edges.
* `TauCeti.DGNerve.Simplex.composableArrowsEquiv`: when the Hom complexes vanish in negative
  degrees, the `n`-simplices of `N_dg(C)` are the strings of `n` composable morphisms of `Z⁰(C)`.
* `TauCeti.dgNerve.nerveIso_hom`: the isomorphism `TauCeti.dgNerve.nerveIso` is
  `TauCeti.dgNerve.fromNerve`.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Example 1.3.1.8.
-/

public section

open CategoryTheory Finset Simplicial

namespace TauCeti

universe v u

namespace DGNerve

namespace Simplex

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ}

/-! ### Simplices from strings of closed morphisms -/

/-- The coherences of the simplex given by a string of closed degree-zero morphisms: the morphism
of the string when there are no interior vertices, and zero otherwise. -/
noncomputable def cohOfComposableArrows
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n) :
    Coherences R (fun i ↦ ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) (F.obj i)) :=
  fun i j S d hij _ hd ↦
    if hS : S = ∅ then
      castDeg R (by rw [hS, card_empty, Nat.cast_zero, add_zero] at hd; exact hd.symm)
        (dgClosedHom R (F.map hij.hom))
    else 0

private theorem cohOfComposableArrows_of_eq_empty
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} {d : ℤ} {hij : i ≤ j} {hS : S ⊆ Ioo i j}
    {hd : d + #S = 0} (h : S = ∅) :
    cohOfComposableArrows F i j S d hij hS hd =
      castDeg R (by rw [h, card_empty, Nat.cast_zero, add_zero] at hd; exact hd.symm)
        (dgClosedHom R (F.map hij.hom)) :=
  dite_eq_left h

private theorem cohOfComposableArrows_of_ne_empty
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} {d : ℤ} {hij : i ≤ j} {hS : S ⊆ Ioo i j}
    {hd : d + #S = 0} (h : S ≠ ∅) :
    cohOfComposableArrows F i j S d hij hS hd = 0 :=
  dite_eq_right h

/- A composite of two degree transports of degree-zero morphisms is the degree transport of their
composite. -/
private theorem dgComp_castDeg_castDeg {X Y Z : C} {p q r : ℤ} (hp : 0 = p) (hq : 0 = q)
    (e : p + q = r) (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgComp R (castDeg R hp f) (castDeg R hq g) e =
      castDeg R (by omega) (dgComp R f g (zero_add 0)) := by
  subst hp hq e
  simp

/-- The coherences given by a string of closed morphisms satisfy the defining equation of the
differential graded nerve. -/
theorem dgDifferential_cohOfComposableArrows
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) :
    dgDifferential R d (cohOfComposableArrows F i j S d hij hS hd) =
      boundary R (cohOfComposableArrows F) i j S d hij hS hd := by
  by_cases hS₀ : S = ∅
  · -- An edge of the string is closed.
    subst hS₀
    obtain rfl : d = 0 := by simpa using hd
    rw [boundary_empty, cohOfComposableArrows_of_eq_empty F rfl, castDeg_self]
    exact (mem_dgCycles R).1 (dgClosedHom_mem_dgCycles R _)
  rw [cohOfComposableArrows_of_ne_empty F hS₀, map_zero, boundary_def, eq_comm]
  refine sum_eq_zero fun t _ ↦ ?_
  have hlt : {s ∈ S | s < t.1} ⊆ S.erase t.1 := fun s hs ↦ by
    rw [mem_filter] at hs
    exact mem_erase.2 ⟨hs.2.ne, hs.1⟩
  have hgt : {s ∈ S | t.1 < s} ⊆ S.erase t.1 := fun s hs ↦ by
    rw [mem_filter] at hs
    exact mem_erase.2 ⟨hs.2.ne', hs.1⟩
  by_cases ht : S.erase t.1 = ∅
  · -- If `t` is the only interior vertex, the term is the defect of functoriality of `F`.
    have hlt₀ := subset_empty.1 (ht ▸ hlt)
    have hgt₀ := subset_empty.1 (ht ▸ hgt)
    have hsign : ((#{s ∈ S | s < t.1} : ℤ) * #{s ∈ S | t.1 < s}).negOnePow = 1 := by
      rw [hlt₀, card_empty, Nat.cast_zero, zero_mul, Int.negOnePow_zero]
    rw [hsign, one_smul, cohOfComposableArrows_of_eq_empty F ht,
      cohOfComposableArrows_of_eq_empty F hlt₀, cohOfComposableArrows_of_eq_empty F hgt₀,
      dgComp_castDeg_castDeg, ← dgCompZero_def, ← dgClosedHom_comp, ← F.map_comp, homOfLE_comp,
      sub_self, smul_zero]
  · -- Otherwise the face term and one factor of the composite term have interior vertices.
    obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.2 ht
    obtain ⟨hst, hsS⟩ := mem_erase.1 hs
    rw [cohOfComposableArrows_of_ne_empty F ht, zero_sub]
    rcases lt_or_gt_of_ne hst with h | h
    · rw [cohOfComposableArrows_of_ne_empty F
        (nonempty_iff_ne_empty.1 ⟨s, mem_filter.2 ⟨hsS, h⟩⟩), zero_dgComp, smul_zero, neg_zero,
        smul_zero]
    · rw [cohOfComposableArrows_of_ne_empty (S := {s ∈ S | t.1 < s}) F
        (nonempty_iff_ne_empty.1 ⟨s, mem_filter.2 ⟨hsS, h⟩⟩), dgComp_zero, smul_zero, neg_zero,
        smul_zero]

/-- The `n`-simplex of the differential graded nerve given by a string of `n` composable closed
degree-zero morphisms: its coherences without interior vertices are the morphisms of the string,
and all its higher coherences vanish. -/
-- Exposed so that the objects of the simplex reduce to the objects of the string: the types of its
-- coherences depend on them.
@[expose] noncomputable def ofComposableArrows
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n) :
    Simplex R C n where
  obj i := ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) (F.obj i)
  coh := cohOfComposableArrows F
  coh_self i := by
    rw [cohOfComposableArrows_of_eq_empty F rfl, castDeg_self, homOfLE_refl, F.map_id,
      dgClosedHom_id]
  dgDifferential_coh := dgDifferential_cohOfComposableArrows F

@[simp]
theorem ofComposableArrows_obj
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    (i : Fin (n + 1)) :
    (ofComposableArrows F).obj i = ForgetEnrichment.to _ (F.obj i) :=
  (rfl)

private theorem ofComposableArrows_coh
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n) :
    (ofComposableArrows F).coh = cohOfComposableArrows F :=
  (rfl)

/-- The coherence without interior vertices of the simplex given by a string is the morphism of
the string. -/
@[simp]
theorem ofComposableArrows_coh_empty
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (ofComposableArrows F).coh i j ∅ 0 hij (empty_subset _) (by simp) =
      dgClosedHom R (F.map hij.hom) := by
  rw [ofComposableArrows_coh, cohOfComposableArrows_of_eq_empty F rfl, castDeg_self]

/-- The coherences with interior vertices of the simplex given by a string vanish. -/
theorem ofComposableArrows_coh_of_ne_empty
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    {i j : Fin (n + 1)} {S : Finset (Fin (n + 1))} {d : ℤ} {hij : i ≤ j} {hS : S ⊆ Ioo i j}
    {hd : d + #S = 0} (h : S ≠ ∅) :
    (ofComposableArrows F).coh i j S d hij hS hd = 0 :=
  cohOfComposableArrows_of_ne_empty (hS := hS) (hd := hd) F h

/-- Pulling back the simplex of a string along a monotone map gives the simplex of the
reindexed string. -/
theorem map_ofComposableArrows
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n)
    {m : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    (ofComposableArrows F).map α = ofComposableArrows (α.monotone.functor ⋙ F) := by
  refine ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  rw [map_coh, ofComposableArrows_coh]
  -- In each case below, the two sides live in Hom modules between objects that agree by `rfl`
  -- (`map_obj` and `ofComposableArrows_obj`), so they are compared by `rfl` once rewritten.
  by_cases hS₀ : S = ∅
  · -- Both sides are the morphism of the string from `α i` to `α j`; the two morphisms
    -- `α i ⟶ α j` of the preorder agree by proof irrelevance.
    subst hS₀
    rw [mapCoh_eq_coh _ _ (by simp), ofComposableArrows_coh,
      cohOfComposableArrows_of_eq_empty F (image_empty α), cohOfComposableArrows_of_eq_empty _ rfl]
    rfl
  · rw [cohOfComposableArrows_of_ne_empty _ hS₀]
    by_cases hc : #(S.image α) = #S ∧ S.image α ⊆ Ioo (α i) (α j)
    · rw [mapCoh_eq_coh _ _ hc, ofComposableArrows_coh_of_ne_empty F
        (by rwa [Ne, image_eq_empty])]
      rfl
    · rw [mapCoh_eq_zero _ _ hc]
      rfl

/-! ### Simplices without higher homotopies -/

/-- If the homotopy carried by the `2`-face `{i, t, j}` of a simplex vanishes, the edge from `i` to
`j` is the composite of the edges from `i` to `t` and from `t` to `j`. -/
theorem coh_eq_dgComp_of_coh_eq_zero (x : Simplex R C n) {i t j : Fin (n + 1)} (hit : i < t)
    (htj : t < j)
    (h : x.coh i j {t} (-1) (hit.le.trans htj.le) (by simp [hit, htj]) (by simp) = 0) :
    x.coh i j ∅ 0 (hit.le.trans htj.le) (empty_subset _) (by simp) =
      dgComp R (x.coh i t ∅ 0 hit.le (empty_subset _) (by simp))
        (x.coh t j ∅ 0 htj.le (empty_subset _) (by simp)) (zero_add 0) := by
  have key := x.dgDifferential_coh i j {t} (-1) (hit.le.trans htj.le) (by simp [hit, htj])
    (by simp)
  rw [h, map_zero, boundary_def, sum_eq_single_of_mem ⟨t, mem_singleton_self t⟩ (mem_attach _ _)
    fun s _ hs ↦ absurd (Subtype.ext (mem_singleton.1 s.2)) hs] at key
  dsimp only at key
  have hσ : ((#{s ∈ ({t} : Finset (Fin (n + 1))) | t ≤ s} : ℕ) : ℤ).negOnePow = -1 := by
    rw [filter_singleton, ite_eq_left le_rfl, card_singleton, Nat.cast_one, Int.negOnePow_one]
  have hκ : ((#{s ∈ ({t} : Finset (Fin (n + 1))) | s < t} : ℤ) *
      #{s ∈ ({t} : Finset (Fin (n + 1))) | t < s}).negOnePow = 1 := by
    rw [filter_singleton, ite_eq_right (lt_irrefl t), card_empty, Nat.cast_zero, zero_mul,
      Int.negOnePow_zero]
  rw [hσ, hκ, one_smul, Units.neg_smul, one_smul, eq_comm, neg_eq_zero, sub_eq_zero] at key
  exact (Coherences.congr _ (by simp)).trans (key.trans
    (Coherences.dgComp_congr _ (by simp) (by simp) (by simp) (by simp)))

variable (h : ∀ (X Y : C) (d : ℤ), d < 0 → Subsingleton (DGHom R d X Y))
include h

/-- When the Hom complexes vanish in negative degrees, the edge from `i` to `j` of a simplex is the
composite of the edges from `i` to `t` and from `t` to `j`, for all `i ≤ t ≤ j`. -/
theorem coh_eq_dgComp (x : Simplex R C n) {i t j : Fin (n + 1)} (hit : i ≤ t) (htj : t ≤ j) :
    x.coh i j ∅ 0 (hit.trans htj) (empty_subset _) (by simp) =
      dgComp R (x.coh i t ∅ 0 hit (empty_subset _) (by simp))
        (x.coh t j ∅ 0 htj (empty_subset _) (by simp)) (zero_add 0) := by
  rcases hit.lt_or_eq with hit | rfl
  · rcases htj.lt_or_eq with htj | rfl
    · exact x.coh_eq_dgComp_of_coh_eq_zero hit htj
        (@Subsingleton.elim _ (h _ _ (-1) (by decide)) _ _)
    · exact (x.dgComp_coh_of_eq_right rfl).symm
  · exact (x.dgComp_coh_of_eq_left rfl).symm

/-- The string of closed degree-zero morphisms formed by the edges of a simplex of the differential
graded nerve, when the Hom complexes vanish in negative degrees, so that these edges compose. -/
-- Exposed so that the objects of the string reduce to the objects of the simplex.
@[expose] noncomputable def toComposableArrows (x : Simplex R C n) :
    ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n where
  obj i := ForgetEnrichment.of _ (x.obj i)
  map {i j} φ := dgClosedHomOf R (x.coh i j ∅ 0 φ.le (empty_subset _) (by simp))
    (by
      rw [mem_dgCycles, x.dgDifferential_coh]
      exact boundary_empty ..)
  map_id i := by
    apply dgClosedHom_injective R
    rw [dgClosedHom_dgClosedHomOf, dgClosedHom_id]
    exact x.coh_self i
  map_comp {i t j} φ ψ := by
    apply dgClosedHom_injective R
    rw [dgClosedHom_dgClosedHomOf, dgClosedHom_comp, dgClosedHom_dgClosedHomOf,
      dgClosedHom_dgClosedHomOf, dgCompZero_def]
    exact x.coh_eq_dgComp h φ.le ψ.le

@[simp]
theorem toComposableArrows_obj (x : Simplex R C n) (i : Fin (n + 1)) :
    (x.toComposableArrows h).obj i = ForgetEnrichment.of _ (x.obj i) :=
  (rfl)

/-- The morphisms of the string formed by the edges of a simplex are its coherences without
interior vertices. -/
@[simp]
theorem dgClosedHom_toComposableArrows_map (x : Simplex R C n) {i j : Fin (n + 1)}
    (φ : i ⟶ j) :
    dgClosedHom R ((x.toComposableArrows h).map φ) =
      x.coh i j ∅ 0 φ.le (empty_subset _) (by simp) :=
  dgClosedHom_dgClosedHomOf R _ _

theorem toComposableArrows_ofComposableArrows
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n) :
    (ofComposableArrows F).toComposableArrows h = F := by
  -- The objects of the two strings agree by `rfl`, so their morphisms can be compared directly.
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun i j φ ↦ heq_of_eq ?_
  apply dgClosedHom_injective R
  rw [dgClosedHom_toComposableArrows_map, ofComposableArrows_coh_empty]
  exact congrArg (fun ψ ↦ dgClosedHom R (F.map ψ)) (Subsingleton.elim _ _)

theorem ofComposableArrows_toComposableArrows (x : Simplex R C n) :
    ofComposableArrows (x.toComposableArrows h) = x := by
  refine ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  by_cases hS₀ : S = ∅
  · subst hS₀
    obtain rfl : d = 0 := by simpa using hd
    rw [ofComposableArrows_coh_empty, dgClosedHom_toComposableArrows_map]
  · -- A coherence with interior vertices has negative degree.
    have hd₀ : d < 0 := by
      have := card_pos.2 (nonempty_iff_ne_empty.2 hS₀)
      omega
    rw [ofComposableArrows_coh_of_ne_empty _ hS₀]
    exact @Subsingleton.elim _ (h _ _ d hd₀) _ _

/-- When the Hom complexes vanish in negative degrees, the simplices of the differential graded
nerve are the strings of closed degree-zero morphisms. -/
noncomputable def composableArrowsEquiv :
    ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n ≃
      Simplex R C n where
  toFun := ofComposableArrows
  invFun x := x.toComposableArrows h
  left_inv := toComposableArrows_ofComposableArrows h
  right_inv := ofComposableArrows_toComposableArrows h

@[simp]
theorem composableArrowsEquiv_apply
    (F : ComposableArrows (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) n) :
    composableArrowsEquiv h F = ofComposableArrows F :=
  (rfl)

@[simp]
theorem composableArrowsEquiv_symm_apply (x : Simplex R C n) :
    (composableArrowsEquiv h).symm x = x.toComposableArrows h :=
  (rfl)

end Simplex

end DGNerve

open DGNerve

namespace dgNerve

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The map from the nerve of the underlying category of a differential graded category to its
differential graded nerve, sending a string of closed degree-zero morphisms to the simplex whose
edges are its morphisms and whose higher coherences vanish. -/
noncomputable def fromNerve :
    nerve (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) ⟶ dgNerve R C where
  app _ := ↾fun F ↦ Simplex.ofComposableArrows F
  naturality _ _ f := by
    ext F
    exact (Simplex.map_ofComposableArrows F f.unop.toOrderHom).symm

@[simp]
theorem fromNerve_app_apply {Δ : SimplexCategoryᵒᵖ}
    (F : (nerve (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C)).obj Δ) :
    (fromNerve R C).app Δ F = Simplex.ofComposableArrows F :=
  (rfl)

/-- **The differential graded nerve of a differential graded category with Hom complexes
concentrated in degree zero** (or more generally vanishing in negative degrees) is the nerve of its
underlying category of closed degree-zero morphisms. -/
noncomputable def nerveIso (h : ∀ (X Y : C) (d : ℤ), d < 0 → Subsingleton (DGHom R d X Y)) :
    nerve (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) ≅ dgNerve R C :=
  NatIso.ofComponents (fun _ ↦ (Simplex.composableArrowsEquiv h).toIso)
    fun f ↦ (fromNerve R C).naturality f

@[simp]
theorem nerveIso_hom (h : ∀ (X Y : C) (d : ℤ), d < 0 → Subsingleton (DGHom R d X Y)) :
    (nerveIso R C h).hom = fromNerve R C :=
  (rfl)

@[simp]
theorem nerveIso_inv_app_apply (h : ∀ (X Y : C) (d : ℤ), d < 0 → Subsingleton (DGHom R d X Y))
    {Δ : SimplexCategoryᵒᵖ} (x : (dgNerve R C).obj Δ) :
    (nerveIso R C h).inv.app Δ x = Simplex.toComposableArrows h x :=
  (rfl)

end dgNerve

end TauCeti
