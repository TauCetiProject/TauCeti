/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import TauCeti.CategoryTheory.DG.HomotopyCategory
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Finset.Basic

/-!
# The differential graded nerve

The differential graded nerve `N_dg(C)` of a differential graded category `C` is the simplicial
set through which `C` is regarded as an `∞`-category. An `n`-simplex is a string of objects
`X 0, …, X n` together with, for all vertices `i ≤ j` and every set `S` of vertices strictly
between them, a morphism `f i S j : X i ⟶ X j` of cohomological degree `-#S`, such that
`f i ∅ i` is the identity and

`d (f i S j) = ∑_{t ∈ S} (-1) ^ #{s ∈ S | t ≤ s} • (f i (S \ {t}) j - f t S₊ j ∘ f i S₋ t)`,

where `S₋` and `S₊` are the vertices of `S` before and after `t`. Thus the edges are closed
degree-zero morphisms, and a `2`-simplex records a homotopy `d η = g ∘ f - h` between a composite
and a third edge. A monotone map `α` acts by taking the coherence of the images when `α` is
injective on the interior vertices and maps them strictly between the images of the endpoints, and
zero otherwise; in particular a collapsed edge becomes an identity and a larger collapsed coherence
becomes zero.

This is Lurie's construction, transported to the conventions of `TauCeti.DGCategory`. Lurie works
with homological grading; here the morphisms of homological degree `m` are those of cohomological
degree `-m`, so `f i S j` has homological degree `#S`, which is Lurie's `|I| - 2` for
`I = {i} ∪ S ∪ {j}`. Lurie composes in the order `g ∘ f`, whereas `TauCeti.dgComp f g` is `f`
followed by `g`; the two are related by the Koszul sign, `g ∘ f = (-1) ^ (|f| * |g|) • dgComp f g`,
under which the Leibniz rules agree. Including the coherences `f i ∅ i` as identities lets
degenerate edges be treated uniformly with the others.

The main result is that the action of a monotone map preserves the defining equation.

## Main definitions

* `TauCeti.DGNerve.Simplex`: the `n`-simplices of the differential graded nerve.
* `TauCeti.DGNerve.Simplex.map`: the pullback of a simplex along a monotone map.
* `TauCeti.dgNerve`: the differential graded nerve, a simplicial set.
* `TauCeti.dgNerveEquiv`: its vertices are the objects of `C`.
* `TauCeti.dgNerve.edgeEquiv`: its edges from `X` to `Y` are the closed degree-zero morphisms.

## Main results

* `TauCeti.DGNerve.Simplex.dgDifferential_mapCoh`: the pullback of a simplex satisfies the
  defining equation.
* `TauCeti.DGNerve.Simplex.mapCoh_eq_zero_of_collapse`: a coherence collapsed by a monotone map
  vanishes, while `TauCeti.dgNerve.coh_σ_vertex` shows that the degenerate edge at a vertex is its
  identity.
* `TauCeti.DGNerve.Simplex.dgDifferential_coh_two`: a `2`-simplex carries a homotopy between the
  composite of two of its edges and the third.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Example 1.3.1.8.
-/

public section

open CategoryTheory Finset Simplicial

namespace TauCeti

universe v u

namespace DGNerve

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ}

/-- Coherence data on a string of objects `X 0, …, X n` of a differential graded category: for
`i ≤ j` and a set `S` of vertices strictly between `i` and `j`, a morphism `X i ⟶ X j` of
cohomological degree `d = -#S`. The degree is an argument constrained by the last hypothesis,
so that coherences indexed by equal sets can be compared without degree casts. -/
abbrev Coherences (X : Fin (n + 1) → C) : Type v :=
  ∀ (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ), i ≤ j → S ⊆ Ioo i j →
    d + #S = 0 → DGHom R d (X i) (X j)

variable {R}

/-- Coherences indexed by equal sets of interior vertices agree. -/
theorem Coherences.congr {X : Fin (n + 1) → C} (f : Coherences R X) {i j : Fin (n + 1)}
    {S S' : Finset (Fin (n + 1))} {d : ℤ} (h : S = S') {hij : i ≤ j} {hS : S ⊆ Ioo i j}
    {hS' : S' ⊆ Ioo i j} {hd : d + #S = 0} {hd' : d + #S' = 0} :
    f i j S d hij hS hd = f i j S' d hij hS' hd' := by
  subst h
  rfl

/-- Composites of coherences indexed by equal sets of interior vertices agree. -/
theorem Coherences.dgComp_congr {X : Fin (n + 1) → C} (f : Coherences R X)
    {i t j : Fin (n + 1)} {S₁ S₁' S₂ S₂' : Finset (Fin (n + 1))} {p p' q q' r : ℤ}
    (h₁ : S₁ = S₁') (h₂ : S₂ = S₂') (hp : p = p') (hq : q = q') {hit : i ≤ t} {htj : t ≤ j}
    {hS₁ : S₁ ⊆ Ioo i t} {hS₁' : S₁' ⊆ Ioo i t} {hS₂ : S₂ ⊆ Ioo t j} {hS₂' : S₂' ⊆ Ioo t j}
    {hp₁ : p + #S₁ = 0} {hp₁' : p' + #S₁' = 0} {hq₂ : q + #S₂ = 0} {hq₂' : q' + #S₂' = 0}
    {e : p + q = r} {e' : p' + q' = r} :
    dgComp R (f i t S₁ p hit hS₁ hp₁) (f t j S₂ q htj hS₂ hq₂) e =
      dgComp R (f i t S₁' p' hit hS₁' hp₁') (f t j S₂' q' htj hS₂' hq₂') e' := by
  subst h₁ h₂ hp hq
  rfl

variable (R) in
/-- The right-hand side of the equation defining the simplices of the differential graded
nerve. For `i ≤ j` and interior vertices `S`, writing `σ t = (-1) ^ #{s ∈ S | t ≤ s}`, it is
`∑_{t ∈ S} σ t • (f_{S \ {t}} - f_{S>t} ∘ f_{S<t})`, where
`g ∘ f = (-1) ^ (|f| * |g|) • dgComp f g` is composition in Keller's order. -/
noncomputable def boundary {X : Fin (n + 1) → C} (f : Coherences R X) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    DGHom R (d + 1) (X i) (X j) :=
  ∑ t ∈ S.attach, (#{s ∈ S | t.1 ≤ s} : ℤ).negOnePow •
    (f i j (S.erase t) (d + 1) hij ((erase_subset _ _).trans hS)
        (add_one_add_card_erase_eq_zero t.2 hd) -
      (#{s ∈ S | s < t.1} * #{s ∈ S | t.1 < s} : ℤ).negOnePow •
        dgComp R
          (f i t {s ∈ S | s < t.1} _ (mem_Ioo.1 (hS t.2)).1.le (filter_lt_subset_Ioo hS)
            (neg_add_cancel _))
          (f t j {s ∈ S | t.1 < s} _ (mem_Ioo.1 (hS t.2)).2.le (filter_gt_subset_Ioo hS)
            (neg_add_cancel _))
          (neg_card_filter_lt_add_neg_card_filter_gt t.2 hd))

/-- The defining formula of `TauCeti.DGNerve.boundary`. -/
-- The degree and subset proofs are `by` blocks because the lemmas they cite are not part of this
-- module's public interface.
theorem boundary_def {X : Fin (n + 1) → C} (f : Coherences R X) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    boundary R f i j S d hij hS hd =
      ∑ t ∈ S.attach, (#{s ∈ S | t.1 ≤ s} : ℤ).negOnePow •
        (f i j (S.erase t) (d + 1) hij ((erase_subset _ _).trans hS)
            (by exact add_one_add_card_erase_eq_zero t.2 hd) -
          (#{s ∈ S | s < t.1} * #{s ∈ S | t.1 < s} : ℤ).negOnePow •
            dgComp R
              (f i t {s ∈ S | s < t.1} _ (mem_Ioo.1 (hS t.2)).1.le
                (by exact filter_lt_subset_Ioo hS) (neg_add_cancel _))
              (f t j {s ∈ S | t.1 < s} _ (mem_Ioo.1 (hS t.2)).2.le
                (by exact filter_gt_subset_Ioo hS) (neg_add_cancel _))
              (by exact neg_card_filter_lt_add_neg_card_filter_gt t.2 hd)) := by
  rw [boundary]

/-- The right-hand side of the dg nerve equation vanishes on the empty set of interior vertices,
so a coherence without interior vertices is closed. -/
@[simp]
theorem boundary_empty {X : Fin (n + 1) → C} (f : Coherences R X) (i j : Fin (n + 1)) (d : ℤ)
    (hij : i ≤ j) (hS : ∅ ⊆ Ioo i j) (hd : d + #(∅ : Finset (Fin (n + 1))) = 0) :
    boundary R f i j ∅ d hij hS hd = 0 := by
  simp [boundary]

variable (R C) in
/-- An `n`-simplex of the differential graded nerve: objects `X 0, …, X n` with coherences
`f i S j : X i ⟶ X j` of cohomological degree `-#S` for the sets `S` of vertices strictly between
`i ≤ j`, such that `f i ∅ i` is the identity and the differential of each coherence is given by
`TauCeti.DGNerve.boundary`. -/
structure Simplex (n : ℕ) : Type (max u v) where
  /-- The objects at the vertices. -/
  obj : Fin (n + 1) → C
  /-- The coherences between the vertices. -/
  coh : Coherences R obj
  /-- The coherence from a vertex to itself is the identity. -/
  coh_self (i : Fin (n + 1)) :
    coh i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (obj i)
  /-- The differential of each coherence is given by the coherences on smaller sets. -/
  dgDifferential_coh (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j)
    (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    dgDifferential R d (coh i j S d hij hS hd) = boundary R coh i j S d hij hS hd

attribute [simp] Simplex.coh_self

namespace Simplex

variable (x : Simplex R C n)

/-- A coherence between equal vertices is a left unit for composition. -/
theorem dgComp_coh_of_eq_left {i t j : Fin (n + 1)} {S₁ S₂ : Finset (Fin (n + 1))}
    {p q r : ℤ} (h : i = t) {hit : i ≤ t} {hS₁ : S₁ ⊆ Ioo i t} {hp : p + #S₁ = 0}
    {htj : t ≤ j} {hS₂ : S₂ ⊆ Ioo t j} {hq : q + #S₂ = 0} {e : p + q = r} :
    dgComp R (x.coh i t S₁ p hit hS₁ hp) (x.coh t j S₂ q htj hS₂ hq) e =
      x.coh i j S₂ r (hit.trans htj) (hS₂.trans (Ioo_subset_Ioo_left hit))
        (by rw [h, Ioo_self, subset_empty] at hS₁; rw [hS₁, card_empty] at hp; omega) := by
  obtain rfl : S₁ = ∅ := by rwa [h, Ioo_self, subset_empty] at hS₁
  subst h
  obtain rfl : p = 0 := by simpa using hp
  obtain rfl : r = q := by omega
  rw [x.coh_self]
  exact dgId_dgComp R _

/-- A coherence between equal vertices is a right unit for composition. -/
theorem dgComp_coh_of_eq_right {i t j : Fin (n + 1)} {S₁ S₂ : Finset (Fin (n + 1))}
    {p q r : ℤ} (h : t = j) {hit : i ≤ t} {hS₁ : S₁ ⊆ Ioo i t} {hp : p + #S₁ = 0}
    {htj : t ≤ j} {hS₂ : S₂ ⊆ Ioo t j} {hq : q + #S₂ = 0} {e : p + q = r} :
    dgComp R (x.coh i t S₁ p hit hS₁ hp) (x.coh t j S₂ q htj hS₂ hq) e =
      x.coh i j S₁ r (hit.trans htj) (hS₁.trans (Ioo_subset_Ioo_right htj))
        (by rw [h, Ioo_self, subset_empty] at hS₂; rw [hS₂, card_empty] at hq; omega) := by
  obtain rfl : S₂ = ∅ := by rwa [h, Ioo_self, subset_empty] at hS₂
  subst h
  obtain rfl : q = 0 := by simpa using hq
  obtain rfl : r = p := by omega
  rw [x.coh_self]
  exact dgComp_dgId R _

variable {m : ℕ} (α : Fin (m + 1) →o Fin (n + 1))

/-- The coherences of the pullback of a simplex along a monotone map `α`: on interior vertices
on which `α` is injective, with image strictly between the images of the endpoints, the
coherence of the image; otherwise zero. -/
noncomputable def mapCoh : Coherences R (x.obj ∘ α) := fun i j S d hij _ hd ↦
  if h : #(S.image α) = #S ∧ S.image α ⊆ Ioo (α i) (α j) then
    x.coh (α i) (α j) (S.image α) d (α.monotone hij) h.2 (by rw [h.1]; exact hd)
  else 0

/-- Where `α` is injective on the interior vertices with image strictly between the images of the
endpoints, the pulled-back coherence is the coherence of the images. -/
theorem mapCoh_eq_coh {i j : Fin (m + 1)} {S : Finset (Fin (m + 1))} {d : ℤ} {hij : i ≤ j}
    {hS : S ⊆ Ioo i j} {hd : d + #S = 0}
    (h : #(S.image α) = #S ∧ S.image α ⊆ Ioo (α i) (α j)) :
    x.mapCoh α i j S d hij hS hd =
      x.coh (α i) (α j) (S.image α) d (α.monotone hij) h.2 (by rw [h.1]; exact hd) :=
  dite_eq_left h

/-- Otherwise the pulled-back coherence is zero. -/
theorem mapCoh_eq_zero {i j : Fin (m + 1)} {S : Finset (Fin (m + 1))} {d : ℤ}
    {hij : i ≤ j} {hS : S ⊆ Ioo i j} {hd : d + #S = 0}
    (h : ¬ (#(S.image α) = #S ∧ S.image α ⊆ Ioo (α i) (α j))) :
    x.mapCoh α i j S d hij hS hd = 0 :=
  dite_eq_right h

/-- A coherence of the pullback vanishes when `α` collapses two of its vertices `u ≠ v`, at least
one of which is interior. -/
theorem mapCoh_eq_zero_of_collapse {i j u v : Fin (m + 1)} {S : Finset (Fin (m + 1))} {d : ℤ}
    {hij : i ≤ j} {hS : S ⊆ Ioo i j} {hd : d + #S = 0} (hu : u = i ∨ u ∈ S)
    (hv : v = j ∨ v ∈ S) (huv' : u ∈ S ∨ v ∈ S) (huv : u ≠ v) (h : α u = α v) :
    x.mapCoh α i j S d hij hS hd = 0 := by
  refine x.mapCoh_eq_zero α ?_
  rintro ⟨hc, hsub⟩
  rw [card_image_iff] at hc
  have key : ∀ s ∈ S, ∀ t, (t = i ∨ t = j ∨ t ∈ S) → s ≠ t → α s ≠ α t := by
    rintro s hs t (rfl | rfl | ht) hst hα
    · have := mem_Ioo.1 (hsub (mem_image_of_mem α hs))
      exact this.1.ne' hα
    · have := mem_Ioo.1 (hsub (mem_image_of_mem α hs))
      exact this.2.ne hα
    · exact hst (hc hs ht hα)
  rcases huv' with hu' | hv'
  · exact key u hu' v (by tauto) huv h
  · exact key v hv' u (by tauto) huv.symm h.symm

/-- A pulled-back coherence between vertices with equal images is a left unit for
composition. -/
theorem dgComp_mapCoh_of_eq_left {i t j : Fin (m + 1)} {S₁ S₂ : Finset (Fin (m + 1))}
    {p q r : ℤ} (h : α i = α t) (h₁ : S₁ = ∅) {hit : i ≤ t} {hS₁ : S₁ ⊆ Ioo i t}
    {hp : p + #S₁ = 0} {htj : t ≤ j} {hS₂ : S₂ ⊆ Ioo t j} {hq : q + #S₂ = 0}
    {e : p + q = r} :
    dgComp R (x.mapCoh α i t S₁ p hit hS₁ hp) (x.mapCoh α t j S₂ q htj hS₂ hq) e =
      x.mapCoh α i j S₂ r (hit.trans htj) (hS₂.trans (Ioo_subset_Ioo_left hit))
        (by rw [h₁, card_empty] at hp; omega) := by
  subst h₁
  rw [x.mapCoh_eq_coh α (by simp)]
  by_cases hc : #(S₂.image α) = #S₂ ∧ S₂.image α ⊆ Ioo (α t) (α j)
  · rw [x.mapCoh_eq_coh α hc, x.mapCoh_eq_coh α (by rwa [h])]
    exact x.dgComp_coh_of_eq_left h
  · rw [x.mapCoh_eq_zero α hc, x.mapCoh_eq_zero α (by rwa [h]), dgComp_zero]

/-- A pulled-back coherence between vertices with equal images is a right unit for
composition. -/
theorem dgComp_mapCoh_of_eq_right {i t j : Fin (m + 1)} {S₁ S₂ : Finset (Fin (m + 1))}
    {p q r : ℤ} (h : α t = α j) (h₂ : S₂ = ∅) {hit : i ≤ t} {hS₁ : S₁ ⊆ Ioo i t}
    {hp : p + #S₁ = 0} {htj : t ≤ j} {hS₂ : S₂ ⊆ Ioo t j} {hq : q + #S₂ = 0}
    {e : p + q = r} :
    dgComp R (x.mapCoh α i t S₁ p hit hS₁ hp) (x.mapCoh α t j S₂ q htj hS₂ hq) e =
      x.mapCoh α i j S₁ r (hit.trans htj) (hS₁.trans (Ioo_subset_Ioo_right htj))
        (by rw [h₂, card_empty] at hq; omega) := by
  subst h₂
  rw [x.mapCoh_eq_coh α (i := t) (by simp)]
  by_cases hc : #(S₁.image α) = #S₁ ∧ S₁.image α ⊆ Ioo (α i) (α t)
  · rw [x.mapCoh_eq_coh α hc, x.mapCoh_eq_coh α (by rwa [← h])]
    exact x.dgComp_coh_of_eq_right h
  · rw [x.mapCoh_eq_zero α hc, x.mapCoh_eq_zero α (by rwa [← h]), zero_dgComp]

/-- Removing either of two interior vertices with the same image gives the same pulled-back
coherence. -/
theorem mapCoh_erase_eq_mapCoh_erase {i j u v : Fin (m + 1)} {S : Finset (Fin (m + 1))}
    {d : ℤ} (hu : u ∈ S) (hv : v ∈ S) (h : α u = α v) {hij : i ≤ j}
    {hSu : S.erase u ⊆ Ioo i j} {hSv : S.erase v ⊆ Ioo i j} {hdu : d + #(S.erase u) = 0}
    {hdv : d + #(S.erase v) = 0} :
    x.mapCoh α i j (S.erase u) d hij hSu hdu = x.mapCoh α i j (S.erase v) d hij hSv hdv := by
  have himage : (S.erase u).image α = (S.erase v).image α := by
    ext y
    simp only [mem_image, mem_erase]
    constructor
    · rintro ⟨s, ⟨hsu, hs⟩, rfl⟩
      by_cases hsv : s = v
      · subst hsv
        exact ⟨u, ⟨fun huv ↦ hsu huv.symm, hu⟩, h⟩
      · exact ⟨s, ⟨hsv, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hsv, hs⟩, rfl⟩
      by_cases hsu : s = u
      · subst hsu
        exact ⟨v, ⟨fun hvu ↦ hsv hvu.symm, hv⟩, h.symm⟩
      · exact ⟨s, ⟨hsu, hs⟩, rfl⟩
  have hcard : #(S.erase u) = #(S.erase v) := by
    rw [card_erase_of_mem hu, card_erase_of_mem hv]
  by_cases hc : #((S.erase u).image α) = #(S.erase u) ∧ (S.erase u).image α ⊆ Ioo (α i) (α j)
  · have hc' : #((S.erase v).image α) = #(S.erase v) ∧
        (S.erase v).image α ⊆ Ioo (α i) (α j) := by rwa [← himage, ← hcard]
    rw [x.mapCoh_eq_coh α hc, x.mapCoh_eq_coh α hc']
    exact Coherences.congr _ himage
  · have hc' : ¬ (#((S.erase v).image α) = #(S.erase v) ∧
        (S.erase v).image α ⊆ Ioo (α i) (α j)) := by rwa [← himage, ← hcard]
    rw [x.mapCoh_eq_zero α hc, x.mapCoh_eq_zero α hc']

/-- The pullback of a simplex satisfies the dg nerve equation on interior vertices where `α` is
injective with image strictly between the endpoints. -/
private lemma dgDifferential_mapCoh_eq_coh {a b : Fin (m + 1)} {T : Finset (Fin (m + 1))}
    {d : ℤ} (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0)
    (h : #(T.image α) = #T ∧ T.image α ⊆ Ioo (α a) (α b)) :
    dgDifferential R d (x.mapCoh α a b T d hab hT hd) =
      boundary R (x.mapCoh α) a b T d hab hT hd := by
  -- The equation is the reindexing of the one for the original simplex: the terms are matched
  -- by `t ↦ α t`. Since `α` is strictly monotone on `T`, it carries erasing `t` and the vertices
  -- before, after and from `t` to the corresponding operations on the image.
  have hinj : Set.InjOn α T := card_image_iff.1 h.1
  have hmono : StrictMonoOn α T := (α.monotone.monotoneOn _).strictMonoOn_of_injOn hinj
  rw [x.mapCoh_eq_coh α h, x.dgDifferential_coh, boundary, boundary]
  symm
  refine sum_bij (fun t _ ↦ ⟨α t.1, mem_image_of_mem α t.2⟩) (fun _ _ ↦ mem_attach _ _) ?_ ?_ ?_
  · rintro ⟨t₁, h₁⟩ - ⟨t₂, h₂⟩ - he
    exact Subtype.ext (hinj h₁ h₂ (congrArg Subtype.val he))
  · rintro ⟨y, hy⟩ -
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
    exact ⟨⟨t, ht⟩, mem_attach _ _, rfl⟩
  rintro ⟨t, ht⟩ -
  dsimp only
  have hcard (P : Fin (m + 1) → Prop) [DecidablePred P] :
      #({s ∈ T | P s}.image α) = #{s ∈ T | P s} :=
    card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _)))
  have e₁ : (T.erase t).image α = (T.image α).erase (α t) := by
    simpa only [sdiff_singleton_eq_erase, image_singleton] using
      image_sdiff_of_injOn hinj (singleton_subset_iff.2 ht)
  have e₂ : {s ∈ T | s < t}.image α = {y ∈ T.image α | y < α t} := by
    rw [filter_image, filter_congr fun s hs ↦ hmono.lt_iff_lt hs ht]
  have e₃ : {s ∈ T | t < s}.image α = {y ∈ T.image α | α t < y} := by
    rw [filter_image, filter_congr fun s hs ↦ hmono.lt_iff_lt ht hs]
  have e₄ : {s ∈ T | t ≤ s}.image α = {y ∈ T.image α | α t ≤ y} := by
    rw [filter_image, filter_congr fun s hs ↦ hmono.le_iff_le ht hs]
  have h₁ : #((T.erase t).image α) = #(T.erase t) ∧ (T.erase t).image α ⊆ Ioo (α a) (α b) :=
    ⟨card_image_of_injOn (hinj.mono (coe_subset.2 (erase_subset _ _))),
      (image_subset_image (erase_subset _ _)).trans h.2⟩
  have h₂ : #({s ∈ T | s < t}.image α) = #{s ∈ T | s < t} ∧
      {s ∈ T | s < t}.image α ⊆ Ioo (α a) (α t) := by
    refine ⟨hcard _, fun y hy ↦ ?_⟩
    rw [e₂, mem_filter] at hy
    exact mem_Ioo.2 ⟨(mem_Ioo.1 (h.2 hy.1)).1, hy.2⟩
  have h₃ : #({s ∈ T | t < s}.image α) = #{s ∈ T | t < s} ∧
      {s ∈ T | t < s}.image α ⊆ Ioo (α t) (α b) := by
    refine ⟨hcard _, fun y hy ↦ ?_⟩
    rw [e₃, mem_filter] at hy
    exact mem_Ioo.2 ⟨hy.2, (mem_Ioo.1 (h.2 hy.1)).2⟩
  rw [x.mapCoh_eq_coh α h₁, x.mapCoh_eq_coh α h₂, x.mapCoh_eq_coh α h₃]
  refine congrArg₂ (· • ·) ?_ (congrArg₂ (· - ·) ?_ (congrArg₂ (· • ·) ?_ ?_))
  · rw [← e₄, hcard]
  · exact Coherences.congr _ e₁
  · rw [← e₂, ← e₃, hcard, hcard]
  · exact Coherences.dgComp_congr _ e₂ e₃ (by rw [← e₂, hcard]) (by rw [← e₃, hcard])

/-- Removing an interior vertex `t` other than two collapsed vertices `u < v` leaves a collapsed
pair, so the corresponding face term of the dg nerve equation for the pullback vanishes. -/
private lemma mapCoh_erase_eq_zero_of_collapse {a b u v t : Fin (m + 1)}
    {T : Finset (Fin (m + 1))} {d : ℤ} (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0)
    (ht : t ∈ T) (hu : u = a ∨ u ∈ T) (hv : v = b ∨ v ∈ T) (huvT : u ∈ T ∨ v ∈ T) (huv : u < v)
    (hα : α u = α v) (htu : t ≠ u) (htv : t ≠ v) :
    x.mapCoh α a b (T.erase t) (d + 1) hab ((erase_subset _ _).trans hT)
      (add_one_add_card_erase_eq_zero ht hd) = 0 := by
  refine x.mapCoh_eq_zero_of_collapse α (u := u) (v := v) ?_ ?_ ?_ huv.ne hα
  · rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (mem_erase.2 ⟨htu.symm, hu⟩)
  · rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (mem_erase.2 ⟨htv.symm, hv⟩)
  · rcases huvT with huT | hvT
    · exact Or.inl (mem_erase.2 ⟨htu.symm, huT⟩)
    · exact Or.inr (mem_erase.2 ⟨htv.symm, hvT⟩)

/-- For an interior vertex `t` other than two adjacent collapsed vertices `u < v`, the collapsed
pair lies on one side of `t`, so the corresponding composite term of the dg nerve equation for the
pullback vanishes. -/
private lemma dgComp_mapCoh_eq_zero_of_collapse {a b u v t : Fin (m + 1)}
    {T : Finset (Fin (m + 1))} {d : ℤ} (hT : T ⊆ Ioo a b) (hd : d + #T = 0) (ht : t ∈ T)
    (hu : u = a ∨ u ∈ T) (hv : v = b ∨ v ∈ T) (huv : u < v) (hα : α u = α v)
    (hcons : ∀ s ∈ T, ¬ (u < s ∧ s < v)) (htu : t ≠ u) (htv : t ≠ v) :
    dgComp R
      (x.mapCoh α a t {s ∈ T | s < t} _ (mem_Ioo.1 (hT ht)).1.le (filter_lt_subset_Ioo hT)
        (neg_add_cancel _))
      (x.mapCoh α t b {s ∈ T | t < s} _ (mem_Ioo.1 (hT ht)).2.le (filter_gt_subset_Ioo hT)
        (neg_add_cancel _))
      (neg_card_filter_lt_add_neg_card_filter_gt ht hd) = 0 := by
  have hTa := (mem_Ioo.1 (hT ht)).1
  have hTb := (mem_Ioo.1 (hT ht)).2
  rcases lt_or_gt_of_ne htu with htu' | htu'
  · -- `u` and `v` both lie after `t`.
    have huT : u ∈ T := hu.resolve_left (by rintro rfl; exact hTa.not_gt htu')
    rw [x.mapCoh_eq_zero_of_collapse α (i := t) (j := b) (S := {s ∈ T | t < s}) (u := u)
      (v := v) (Or.inr (mem_filter.2 ⟨huT, htu'⟩)) ?_ (Or.inl (mem_filter.2 ⟨huT, htu'⟩))
      huv.ne hα, dgComp_zero]
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (mem_filter.2 ⟨hv, htu'.trans huv⟩)
  · -- `u` and `v` both lie before `t`.
    have hvt : v < t := (lt_or_gt_of_ne htv).resolve_left fun hvt ↦ hcons t ht ⟨htu', hvt⟩
    have hvT : v ∈ T := hv.resolve_left (by rintro rfl; exact hTb.not_gt hvt)
    rw [x.mapCoh_eq_zero_of_collapse α (i := a) (j := t) (S := {s ∈ T | s < t}) (u := u)
      (v := v) ?_ (Or.inr (mem_filter.2 ⟨hvT, hvt⟩)) (Or.inr (mem_filter.2 ⟨hvT, hvt⟩))
      huv.ne hα, zero_dgComp]
    rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (mem_filter.2 ⟨hu, huv.trans hvt⟩)

/-- If `α` identifies an interior vertex `t` with an endpoint and no interior vertex lies between
them, the face and composite parts of the term at `t` of the dg nerve equation for the pullback
cancel. -/
private lemma mapCoh_erase_sub_dgComp_eq_zero {a b t : Fin (m + 1)} {T : Finset (Fin (m + 1))}
    {d : ℤ} (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0) (ht : t ∈ T)
    (h : ({s ∈ T | s < t} = ∅ ∧ α a = α t) ∨ ({s ∈ T | t < s} = ∅ ∧ α t = α b)) :
    x.mapCoh α a b (T.erase t) (d + 1) hab ((erase_subset _ _).trans hT)
        (add_one_add_card_erase_eq_zero ht hd) -
      (#{s ∈ T | s < t} * #{s ∈ T | t < s} : ℤ).negOnePow •
        dgComp R
          (x.mapCoh α a t {s ∈ T | s < t} _ (mem_Ioo.1 (hT ht)).1.le (filter_lt_subset_Ioo hT)
            (neg_add_cancel _))
          (x.mapCoh α t b {s ∈ T | t < s} _ (mem_Ioo.1 (hT ht)).2.le (filter_gt_subset_Ioo hT)
            (neg_add_cancel _))
          (neg_card_filter_lt_add_neg_card_filter_gt ht hd) = 0 := by
  have hκ : (#{s ∈ T | s < t} * #{s ∈ T | t < s} : ℤ).negOnePow = 1 := by
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hsplit : T.erase t = {s ∈ T | s < t} ∪ {s ∈ T | t < s} := by
    ext s
    simp only [mem_erase, mem_union, mem_filter, ne_iff_lt_or_gt]
    tauto
  rw [hκ, one_smul, sub_eq_zero]
  rcases h with ⟨hlt, hα⟩ | ⟨hgt, hα⟩
  · rw [x.dgComp_mapCoh_of_eq_left α hα hlt]
    exact Coherences.congr _ (by rw [hsplit, hlt, empty_union])
  · rw [x.dgComp_mapCoh_of_eq_right α hα hgt]
    exact Coherences.congr _ (by rw [hsplit, hgt, union_empty])

/-- Away from two adjacent collapsed vertices `u < v`, the term at an interior vertex `t` of the dg
nerve equation for the pullback vanishes. -/
private lemma mapCoh_erase_sub_dgComp_eq_zero_of_collapse {a b u v t : Fin (m + 1)}
    {T : Finset (Fin (m + 1))} {d : ℤ} (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0)
    (ht : t ∈ T) (hu : u = a ∨ u ∈ T) (hv : v = b ∨ v ∈ T) (huvT : u ∈ T ∨ v ∈ T) (huv : u < v)
    (hα : α u = α v) (hcons : ∀ s ∈ T, ¬ (u < s ∧ s < v)) (htu : t ≠ u) (htv : t ≠ v) :
    x.mapCoh α a b (T.erase t) (d + 1) hab ((erase_subset _ _).trans hT)
        (add_one_add_card_erase_eq_zero ht hd) -
      (#{s ∈ T | s < t} * #{s ∈ T | t < s} : ℤ).negOnePow •
        dgComp R
          (x.mapCoh α a t {s ∈ T | s < t} _ (mem_Ioo.1 (hT ht)).1.le (filter_lt_subset_Ioo hT)
            (neg_add_cancel _))
          (x.mapCoh α t b {s ∈ T | t < s} _ (mem_Ioo.1 (hT ht)).2.le (filter_gt_subset_Ioo hT)
            (neg_add_cancel _))
          (neg_card_filter_lt_add_neg_card_filter_gt ht hd) = 0 := by
  rw [x.mapCoh_erase_eq_zero_of_collapse α hab hT hd ht hu hv huvT huv hα htu htv,
    x.dgComp_mapCoh_eq_zero_of_collapse α hT hd ht hu hv huv hα hcons htu htv, smul_zero,
    sub_zero]

/-- If `α` collapses two adjacent vertices `u < v`, one of which is an endpoint and the other the
interior vertex `w`, then the right-hand side of the dg nerve equation for the pullback vanishes:
the two parts of the term at `w` cancel, and every other term vanishes. -/
private lemma boundary_mapCoh_eq_zero_of_endpoint {a b u v w : Fin (m + 1)}
    {T : Finset (Fin (m + 1))} {d : ℤ} (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0)
    (hu : u = a ∨ u ∈ T) (hv : v = b ∨ v ∈ T) (huvT : u ∈ T ∨ v ∈ T) (huv : u < v)
    (hα : α u = α v) (hcons : ∀ s ∈ T, ¬ (u < s ∧ s < v))
    (hne : ∀ t ∈ T, t ≠ w → t ≠ u ∧ t ≠ v)
    (hw : ({s ∈ T | s < w} = ∅ ∧ α a = α w) ∨ ({s ∈ T | w < s} = ∅ ∧ α w = α b)) :
    boundary R (x.mapCoh α) a b T d hab hT hd = 0 := by
  refine sum_eq_zero ?_
  rintro ⟨t, ht⟩ -
  dsimp only
  by_cases htw : t = w
  · subst htw
    rw [x.mapCoh_erase_sub_dgComp_eq_zero α hab hT hd ht hw, smul_zero]
  · obtain ⟨htu, htv⟩ := hne t ht htw
    rw [x.mapCoh_erase_sub_dgComp_eq_zero_of_collapse α hab hT hd ht hu hv huvT huv hα hcons htu
      htv, smul_zero]

/-- When `α` collapses two vertices of `a < T < b`, the right-hand side of the dg nerve equation
for the pullback vanishes. -/
private lemma boundary_mapCoh_eq_zero {a b : Fin (m + 1)} {T : Finset (Fin (m + 1))} {d : ℤ}
    (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0)
    (h : ¬ (#(T.image α) = #T ∧ T.image α ⊆ Ioo (α a) (α b))) :
    boundary R (x.mapCoh α) a b T d hab hT hd = 0 := by
  -- The terms of the right-hand side cancel in pairs. Pick adjacent collapsed vertices `u < v`.
  -- All terms away from `u` and `v` vanish. If `u = a`, the face and composite parts of the term
  -- at `v` cancel, the composite being with an identity; symmetrically if `v = b`. If both are
  -- interior, the two face terms at `u` and `v` are equal with opposite signs, and their composite
  -- parts vanish.
  obtain ⟨u, v, huv, hu, hv, huvT, hα, hcons⟩ :=
    exists_adjacent_eq_of_not_card_image_and_image_subset_Ioo α.monotone hT h
  have hTa : ∀ s ∈ T, a < s := fun s hs ↦ (mem_Ioo.1 (hT hs)).1
  have hTb : ∀ s ∈ T, s < b := fun s hs ↦ (mem_Ioo.1 (hT hs)).2
  rcases hu with hua | huT
  · -- `α a = α v` with `v` the first interior vertex.
    refine x.boundary_mapCoh_eq_zero_of_endpoint α hab hT hd (Or.inl hua) hv huvT huv hα hcons
      (fun t ht htv ↦ ⟨by rintro rfl; exact (hTa t ht).ne' hua, htv⟩) (Or.inl
        ⟨filter_eq_empty_iff.2 fun s hs hst ↦ hcons s hs ⟨hua ▸ hTa s hs, hst⟩, hua ▸ hα⟩)
  rcases hv with hvb | hvT
  · -- `α u = α b` with `u` the last interior vertex.
    refine x.boundary_mapCoh_eq_zero_of_endpoint α hab hT hd (Or.inr huT) (Or.inl hvb) huvT huv
      hα hcons (fun t ht htu ↦ ⟨htu, by rintro rfl; exact (hTb t ht).ne hvb⟩) (Or.inr
        ⟨filter_eq_empty_iff.2 fun s hs hts ↦ hcons s hs ⟨hts, hvb ▸ hTb s hs⟩, hvb ▸ hα⟩)
  · -- `u < v` are adjacent interior vertices: the terms for `u` and `v` cancel.
    rw [boundary, sum_eq_add_of_mem ⟨u, huT⟩ ⟨v, hvT⟩ (mem_attach _ _) (mem_attach _ _)
      (fun he ↦ huv.ne (congrArg Subtype.val he)) ?_]
    · dsimp only
      rw [x.mapCoh_eq_zero_of_collapse α (i := u) (j := b) (S := {s ∈ T | u < s}) (u := u)
          (v := v) (Or.inl rfl) (Or.inr (mem_filter.2 ⟨hvT, huv⟩))
          (Or.inr (mem_filter.2 ⟨hvT, huv⟩)) huv.ne hα, dgComp_zero, smul_zero, sub_zero,
        x.mapCoh_eq_zero_of_collapse α (i := a) (j := v) (S := {s ∈ T | s < v}) (u := u)
          (v := v) (Or.inr (mem_filter.2 ⟨huT, huv⟩)) (Or.inl rfl)
          (Or.inl (mem_filter.2 ⟨huT, huv⟩)) huv.ne hα, zero_dgComp, smul_zero, sub_zero]
      have hσ : {s ∈ T | u ≤ s} = insert u {s ∈ T | v ≤ s} := by
        ext s
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨hs, hus⟩
          rcases eq_or_lt_of_le hus with rfl | hus
          · exact Or.inl rfl
          · exact Or.inr ⟨hs, not_lt.1 fun hsv ↦ hcons s hs ⟨hus, hsv⟩⟩
        · rintro (rfl | ⟨hs, hvs⟩)
          · exact ⟨huT, le_rfl⟩
          · exact ⟨hs, huv.le.trans hvs⟩
      rw [hσ, card_insert_of_notMem (fun hu ↦ (mem_filter.1 hu).2.not_gt huv),
        x.mapCoh_erase_eq_mapCoh_erase α huT hvT hα (hSv := (erase_subset _ _).trans hT)
          (hdv := add_one_add_card_erase_eq_zero hvT hd)]
      simp [Int.negOnePow_succ]
    · rintro ⟨t, ht⟩ - hne
      have htu : t ≠ u := fun h ↦ hne.1 (Subtype.ext h)
      have htv : t ≠ v := fun h ↦ hne.2 (Subtype.ext h)
      dsimp only
      rw [x.mapCoh_erase_sub_dgComp_eq_zero_of_collapse α hab hT hd ht (Or.inr huT) (Or.inr hvT)
        huvT huv hα hcons htu htv, smul_zero]

/-- The pulled-back coherences satisfy the dg nerve equation. -/
-- When `α` is injective on the interior vertices the equation is a reindexing of the original
-- one. Otherwise `α` collapses two adjacent vertices of the string, and the terms of the
-- right-hand side cancel in pairs, either two face terms or a face term against a composite with
-- an identity.
theorem dgDifferential_mapCoh {a b : Fin (m + 1)} {T : Finset (Fin (m + 1))} {d : ℤ}
    (hab : a ≤ b) (hT : T ⊆ Ioo a b) (hd : d + #T = 0) :
    dgDifferential R d (x.mapCoh α a b T d hab hT hd) =
      boundary R (x.mapCoh α) a b T d hab hT hd := by
  by_cases h : #(T.image α) = #T ∧ T.image α ⊆ Ioo (α a) (α b)
  · exact x.dgDifferential_mapCoh_eq_coh α hab hT hd h
  · rw [x.mapCoh_eq_zero α h, map_zero, x.boundary_mapCoh_eq_zero α hab hT hd h]

/-- The pullback of a simplex of the differential graded nerve along a monotone map. -/
-- Exposed so that the objects of the pullback reduce to `x.obj ∘ α`: the types of its
-- coherences depend on them.
@[expose] noncomputable def map : Simplex R C m where
  obj := x.obj ∘ α
  coh := x.mapCoh α
  coh_self i := by
    rw [x.mapCoh_eq_coh α (by simp)]
    exact (Coherences.congr _ (image_empty _)).trans (x.coh_self _)
  dgDifferential_coh _ _ _ _ := x.dgDifferential_mapCoh α

/-- The objects of the pullback of a simplex are the objects at the images of the vertices. -/
@[simp]
theorem map_obj : (x.map α).obj = x.obj ∘ α := rfl

/-- The coherences of the pullback of a simplex. -/
theorem map_coh : (x.map α).coh = x.mapCoh α := rfl

/-- Two simplices with the same objects and the same coherences are equal. -/
theorem ext {x y : Simplex R C n} (hobj : x.obj = y.obj)
    (hcoh : ∀ i j S d hij hS hd, x.coh i j S d hij hS hd ≍ y.coh i j S d hij hS hd) :
    x = y := by
  cases x
  cases y
  dsimp only at hobj
  subst hobj
  congr
  funext i j S d hij hS hd
  exact eq_of_heq (hcoh i j S d hij hS hd)

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem map_id : x.map OrderHom.id = x := by
  refine ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  rw [map_coh, x.mapCoh_eq_coh _ (by simpa using hS)]
  exact Coherences.congr _ (by simp)

/-- Pulling back along `α` and then along `β` is pulling back along `α ∘ β`. -/
@[simp]
theorem map_map {k : ℕ} (β : Fin (k + 1) →o Fin (m + 1)) :
    (x.map α).map β = x.map (α.comp β) := by
  refine ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  rw [map_coh, map_coh]
  have hc := card_image_comp_eq_and_image_comp_subset_Ioo_iff α β.monotone hS
  by_cases hβ : #(S.image β) = #S ∧ S.image β ⊆ Ioo (β i) (β j)
  · rw [(x.map α).mapCoh_eq_coh β hβ, map_coh]
    by_cases hα : #((S.image β).image α) = #(S.image β) ∧
        (S.image β).image α ⊆ Ioo (α (β i)) (α (β j))
    · rw [x.mapCoh_eq_coh α hα, x.mapCoh_eq_coh (α.comp β) (hc.2 ⟨hβ, hα⟩)]
      exact Coherences.congr _ (by rw [image_image, OrderHom.comp_coe])
    · rw [x.mapCoh_eq_zero α hα,
        x.mapCoh_eq_zero (α.comp β) fun h ↦ hα (hc.1 h).2]
      -- The two zeros live in hom-modules between `(x.map α).obj (β i)` and
      -- `x.obj (α.comp β i)` (and likewise at `j`), which agree by `map_obj` and
      -- `OrderHom.comp_coe`, both of which hold by `rfl`.
      rfl
  · rw [(x.map α).mapCoh_eq_zero β hβ,
      x.mapCoh_eq_zero (α.comp β) fun h ↦ hβ (hc.1 h).1]
    -- As above, the two zeros agree because `map_obj` and `OrderHom.comp_coe` hold by `rfl`.
    rfl

/-! ### Vertices and low-dimensional simplices -/

/-- The vertex of the differential graded nerve at an object `X`: its only coherence is the
identity of `X`. -/
-- Exposed so that the objects of a vertex reduce to `X`.
@[expose] noncomputable def vertex (X : C) : Simplex R C 0 where
  obj _ := X
  coh _ _ S d _ hS hd :=
    castDeg R (by simpa [Fin.eq_empty_of_subset_Ioo_of_le_two (by decide) hS] using hd.symm)
      (dgId R X)
  coh_self _ := castDeg_self R _ _
  dgDifferential_coh i j S d hij hS hd := by
    obtain rfl := Fin.eq_empty_of_subset_Ioo_of_le_two (by decide) hS
    obtain rfl : d = 0 := by simpa using hd
    simpa [boundary] using dgDifferential_dgId R X

/-- The object of the vertex at `X` is `X`. -/
@[simp]
theorem vertex_obj (X : C) (i : Fin 1) : (vertex X : Simplex R C 0).obj i = X := rfl

/-- A `0`-simplex is determined by its object. -/
theorem ext_zero {x y : Simplex R C 0} (h : x.obj 0 = y.obj 0) : x = y := by
  have hobj : x.obj = y.obj := funext fun i ↦ by rwa [Fin.eq_zero i]
  refine ext hobj fun i j S d hij hS hd ↦ ?_
  obtain rfl := Fin.eq_empty_of_subset_Ioo_of_le_two (by decide) hS
  obtain rfl : d = 0 := by simpa using hd
  obtain rfl := (Fin.eq_zero i).trans (Fin.eq_zero j).symm
  rw [x.coh_self, y.coh_self, hobj]

/-- **The 2-simplex check**: a `2`-simplex with edges `f : X 0 ⟶ X 1`, `g : X 1 ⟶ X 2` and
`h : X 0 ⟶ X 2` carries a degree `-1` morphism `η : X 0 ⟶ X 2` with `d η = g ∘ f - h`, a homotopy
between the composite and `h` rather than an equality. -/
theorem dgDifferential_coh_two (x : Simplex R C 2) :
    dgDifferential R (-1) (x.coh 0 2 {1} (-1) (by decide) (by decide) (by simp)) =
      dgComp R (x.coh 0 1 ∅ 0 (by decide) (empty_subset _) (by simp))
          (x.coh 1 2 ∅ 0 (by decide) (empty_subset _) (by simp)) (by simp) -
        x.coh 0 2 ∅ (-1 + 1) (by decide) (empty_subset _) (by simp) := by
  rw [x.dgDifferential_coh, boundary, sum_eq_single_of_mem ⟨1, mem_singleton_self 1⟩
    (mem_attach _ _) fun t _ ht ↦ absurd (Subtype.ext (mem_singleton.1 t.2)) ht]
  dsimp only
  have hσ : ((#{s ∈ ({1} : Finset (Fin 3)) | 1 ≤ s} : ℕ) : ℤ).negOnePow = -1 := by decide
  have hκ : ((#{s ∈ ({1} : Finset (Fin 3)) | s < 1} : ℕ) *
      (#{s ∈ ({1} : Finset (Fin 3)) | 1 < s} : ℕ) : ℤ).negOnePow = 1 := by decide
  rw [hσ, hκ, one_smul, Units.neg_smul, one_smul, neg_sub]
  exact congrArg₂ (· - ·) (Coherences.dgComp_congr _ (by decide) (by decide) (by simp) (by simp))
    (Coherences.congr _ (by decide))

/-- The edge of the differential graded nerve given by a closed degree-zero morphism
`f : X ⟶ Y`. -/
-- Exposed so that the objects of the edge reduce to `X` and `Y`.
@[expose] noncomputable def edge {X Y : C} (f : dgCycles R X Y) : Simplex R C 1 where
  obj := ![X, Y]
  coh i j S d hij hS hd :=
    castDeg R (by simpa [Fin.eq_empty_of_subset_Ioo_of_le_two (by decide) hS] using hd.symm) <|
      match i, j, hij with
      | 0, 0, _ => dgId R X
      | 0, 1, _ => f.1
      | 1, 1, _ => dgId R Y
  coh_self i := by
    fin_cases i <;> exact castDeg_self R rfl _
  dgDifferential_coh i j S d hij hS hd := by
    obtain rfl := Fin.eq_empty_of_subset_Ioo_of_le_two (by decide) hS
    obtain rfl : d = 0 := by simpa using hd
    simp only [castDeg_self, boundary, attach_empty, sum_empty]
    fin_cases i <;> fin_cases j
    · exact dgDifferential_dgId R X
    · exact (mem_dgCycles R).1 f.2
    · exact absurd hij (by decide)
    · exact dgDifferential_dgId R Y

/-- The objects of the edge at `f : X ⟶ Y` are `X` and `Y`. -/
@[simp]
theorem edge_obj {X Y : C} (f : dgCycles R X Y) : (edge f).obj = ![X, Y] := rfl

/-- The coherence of the edge at a closed morphism `f` is `f`. -/
@[simp]
theorem edge_coh_zero_one {X Y : C} (f : dgCycles R X Y) :
    (edge f).coh 0 1 ∅ 0 (by decide) (empty_subset _) (by simp) = f.1 :=
  castDeg_self R rfl _

/-- The coherence of a `1`-simplex is a closed degree-zero morphism. -/
theorem coh_zero_one_mem_dgCycles (x : Simplex R C 1) :
    x.coh 0 1 ∅ 0 (by decide) (empty_subset _) (by simp) ∈ dgCycles R (x.obj 0) (x.obj 1) := by
  rw [mem_dgCycles, x.dgDifferential_coh]
  simp [boundary]

/-- A `1`-simplex is the edge given by its coherence. -/
theorem eq_edge (x : Simplex R C 1) : x = edge ⟨_, x.coh_zero_one_mem_dgCycles⟩ := by
  have hobj : x.obj = ![x.obj 0, x.obj 1] := by
    ext i
    fin_cases i <;> rfl
  refine ext hobj fun i j S d hij hS hd ↦ ?_
  obtain rfl := Fin.eq_empty_of_subset_Ioo_of_le_two (by decide) hS
  obtain rfl : d = 0 := by simpa using hd
  fin_cases i <;> fin_cases j
  · rw [x.coh_self]
    exact heq_of_eq (castDeg_self R rfl _).symm
  · exact heq_of_eq (castDeg_self R rfl _).symm
  · exact absurd hij (by decide)
  · rw [x.coh_self]
    exact heq_of_eq (castDeg_self R rfl _).symm

/-- Distinct closed morphisms give distinct edges. -/
theorem edge_injective {X Y : C} : Function.Injective (edge : dgCycles R X Y → Simplex R C 1) := by
  intro f g h
  have hh := congr_arg_heq
    (fun x : Simplex R C 1 ↦ x.coh 0 1 ∅ 0 (by decide) (empty_subset _) (by simp)) h
  have := eq_of_heq hh
  rw [edge_coh_zero_one, edge_coh_zero_one] at this
  exact Subtype.ext this

/-- A `1`-simplex from `X` to `Y` is the edge of a closed degree-zero morphism `X ⟶ Y`. -/
theorem exists_edge_eq (x : Simplex R C 1) {X Y : C} (hX : x.obj 0 = X) (hY : x.obj 1 = Y) :
    ∃ f : dgCycles R X Y, edge f = x := by
  subst hX hY
  exact ⟨_, x.eq_edge.symm⟩

end Simplex

end DGNerve

open DGNerve

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The **differential graded nerve** of a differential graded category `C` over `R`: its
`n`-simplices are the strings of objects `X 0, …, X n` with compatible coherences
(`TauCeti.DGNerve.Simplex`), and a monotone map acts by `TauCeti.DGNerve.Simplex.map`. -/
@[expose] noncomputable def dgNerve : SSet.{max u v} where
  obj Δ := Simplex R C Δ.unop.len
  map f := ↾fun x ↦ x.map f.unop.toOrderHom
  map_id Δ := by
    ext x
    exact x.map_id
  map_comp f g := by
    ext x
    exact (x.map_map _ _).symm

/-- A simplicial operator acts on the differential graded nerve by `TauCeti.DGNerve.Simplex.map`. -/
@[simp]
theorem dgNerve_map_apply {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : (dgNerve R C).obj Δ) :
    (dgNerve R C).map f x = Simplex.map x f.unop.toOrderHom :=
  rfl

/-- The vertices of the differential graded nerve are the objects of the differential graded
category. -/
noncomputable def dgNerveEquiv : (dgNerve R C) _⦋0⦌ ≃ C where
  toFun x := Simplex.obj x 0
  invFun X := Simplex.vertex X
  left_inv _ := Simplex.ext_zero rfl
  right_inv _ := rfl

/-- The object of a vertex of the differential graded nerve. -/
@[simp]
theorem dgNerveEquiv_apply (x : (dgNerve R C) _⦋0⦌) : dgNerveEquiv R C x = Simplex.obj x 0 :=
  (rfl)

/-- The vertex of the differential graded nerve at an object. -/
@[simp]
theorem dgNerveEquiv_symm_apply (X : C) :
    (dgNerveEquiv R C).symm X = (Simplex.vertex X : Simplex R C 0) :=
  (rfl)

namespace dgNerve

/-- The edge of the differential graded nerve given by a closed degree-zero morphism. -/
noncomputable def edgeMk {X Y : C} (f : dgCycles R X Y) :
    (dgNerve R C).Edge ((dgNerveEquiv R C).symm X) ((dgNerveEquiv R C).symm Y) :=
  SSet.Edge.mk (Simplex.edge f) (Simplex.ext_zero rfl) (Simplex.ext_zero rfl)

/-- The underlying `1`-simplex of `TauCeti.dgNerve.edgeMk f` is the edge of `f`. -/
@[simp]
theorem edgeMk_edge {X Y : C} (f : dgCycles R X Y) :
    (edgeMk R C f).edge = Simplex.edge f :=
  (rfl)

/-- Every edge between the vertices at `X` and `Y` is the edge of a unique closed degree-zero
morphism `X ⟶ Y`. -/
theorem edgeMk_bijective (X Y : C) : Function.Bijective (edgeMk R C : dgCycles R X Y → _) := by
  refine ⟨fun f g h ↦ Simplex.edge_injective (congrArg SSet.Edge.edge h), fun e ↦ ?_⟩
  obtain ⟨f, hf⟩ := Simplex.exists_edge_eq (R := R) e.edge
    (congrArg (fun x : Simplex R C 0 ↦ x.obj 0) e.src_eq)
    (congrArg (fun x : Simplex R C 0 ↦ x.obj 0) e.tgt_eq)
  exact ⟨f, SSet.Edge.ext hf⟩

/-- **Edges of the differential graded nerve**: the edges from `X` to `Y` are the closed
degree-zero morphisms `X ⟶ Y`. -/
noncomputable def edgeEquiv (X Y : C) :
    dgCycles R X Y ≃ (dgNerve R C).Edge ((dgNerveEquiv R C).symm X) ((dgNerveEquiv R C).symm Y) :=
  Equiv.ofBijective _ (edgeMk_bijective R C X Y)

/-- The edge equivalence is `TauCeti.dgNerve.edgeMk`. -/
@[simp]
theorem edgeEquiv_apply {X Y : C} (f : dgCycles R X Y) : edgeEquiv R C X Y f = edgeMk R C f :=
  (rfl)

/-- The inverse of the edge equivalence recovers a closed morphism from its edge. -/
@[simp]
theorem edgeEquiv_symm_edgeMk {X Y : C} (f : dgCycles R X Y) :
    (edgeEquiv R C X Y).symm (edgeMk R C f) = f :=
  (edgeEquiv R C X Y).symm_apply_apply f

/-- The inverse of the edge equivalence reads the closed morphism off the coherence of the
underlying `1`-simplex. The two sides are heterogeneously equal because the endpoints of that
coherence are `X` and `Y` only propositionally. -/
theorem edgeEquiv_symm_apply_heq {X Y : C}
    (e : (dgNerve R C).Edge ((dgNerveEquiv R C).symm X) ((dgNerveEquiv R C).symm Y)) :
    ((edgeEquiv R C X Y).symm e).1 ≍
      Simplex.coh (R := R) e.edge 0 1 ∅ 0 (by decide) (empty_subset _) (by simp) := by
  obtain ⟨f, rfl⟩ := (edgeEquiv R C X Y).surjective e
  rw [Equiv.symm_apply_apply, edgeEquiv_apply, edgeMk_edge, Simplex.edge_coh_zero_one]
  exact HEq.rfl

/-- **Degeneracy of a vertex**: the degenerate edge at an object `X` is the identity of `X`, not
zero. -/
theorem coh_σ_vertex (X : C) :
    ((dgNerve R C).σ 0 (Simplex.vertex X : Simplex R C 0)).coh 0 1 ∅ 0 (by decide)
      (empty_subset _) (by simp) = dgId R X := by
  -- `σ 0` acts on the nerve through `dgNerve.map`, i.e. by `Simplex.map`. Rewriting with
  -- `SimplicialObject.σ_def` and `dgNerve_map_apply` fails (motive is not type correct): the
  -- right-hand side `dgId R X` has type `DGHom R 0 X X`, whose objects agree with the endpoints of
  -- the coherence only definitionally, so the simplex is replaced by `change` instead.
  change (Simplex.map (Simplex.vertex X) (SimplexCategory.σ 0).toOrderHom).coh 0 1 ∅ 0 _ _ _ = _
  rw [Simplex.map_coh, Simplex.mapCoh_eq_coh _ _ (by simp)]
  exact castDeg_self R rfl _

end dgNerve

end TauCeti
