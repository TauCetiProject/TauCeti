/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import TauCeti.CategoryTheory.DG.HomotopyCategory

/-!
# The differential graded nerve

The differential graded nerve `N_dg(C)` of a differential graded category `C` is the simplicial
set whose `n`-simplices are objects `X₀, …, Xₙ` of `C` together with, for every subset
`I ⊆ [n]` with at least two elements, a coherence `f_I : X_{min I} ⟶ X_{max I}` of homological
degree `#I - 2`, subject to the equations

`d f_I = ∑_{v} (-1) ^ #{w ∈ I | v < w} • (f_{I ∖ {v}} - f_{I_{≥ v}} ∘ f_{I_{≤ v}})`,

the sum running over the interior vertices `v` of `I` (Lurie, *Higher Algebra*,
Construction 1.3.1.6).  It is the quasicategory through which a differential graded category,
for instance a dg model of a derived category, is regarded as an `∞`-category.

Differential graded categories here are cohomologically graded with Mathlib's enriched factor
order (`TauCeti.DGCategory`).  Lurie's homological degree `k` is cohomological degree `-k`, and
his composite `g ∘ f` of homogeneous maps of degrees `|f|` and `|g|` is the Keller-ordered
composite `(-1) ^ (|f| * |g|) • dgComp f g`; with these conventions the equations above are
literally Lurie's.

A subset `I` with minimum `i` and maximum `j` is recorded through its interior `S = I ∖ {i, j}`:
the coherence `coh i j S` has cohomological degree `-#S` (`TauCeti.DGNerve.IsIndex`).  A
monotone map `α` acts on these data as in Lurie's construction: on subsets on which `α` is
injective it reindexes, a two-element subset collapsed by `α` receives the identity, and a larger
collapsed subset receives zero (`TauCeti.DGNerve.Family.pullback`).  That this action preserves
the equations is checked for injective maps directly; for a map collapsing a single pair of
adjacent vertices the surviving terms of each equation cancel; and every map of
`SimplexCategory` is a composite of such maps.

## Main definitions

* `TauCeti.DGNerve.Family`: objects and coherences indexed by a linear order.
* `TauCeti.DGNerve.Family.IsCoherent`: the dg nerve equations.
* `TauCeti.DGNerve.Family.pullback`: the action of monotone maps.
* `TauCeti.dgNerve`: the differential graded nerve, a simplicial set.
* `TauCeti.dgNerveVerticesEquiv`: the vertices of `N_dg(C)` are the objects of `C`.
* `TauCeti.dgNerveEdgesEquiv`: the edges of `N_dg(C)` are the closed degree-zero morphisms.

## Main results

* `TauCeti.DGNerve.Family.IsCoherent.pullback`: monotone maps preserve the dg nerve equations.
* `TauCeti.DGNerve.Family.pullback_coh_of_injOn`, `TauCeti.DGNerve.Family.pullback_coh_of_eq`
  and `TauCeti.DGNerve.Family.pullback_coh_eq_zero`, with `TauCeti.dgNerve_map_val`: the
  coherences of a degenerate simplex; a collapsed edge is an identity and a larger collapsed
  coherence is zero.
* `TauCeti.dgNerveEdgesEquiv_σ_dgNerveVerticesEquiv_symm`: the degenerate edge at an object is
  its identity.
* `TauCeti.dgNerve_d_coh_two`: a `2`-simplex with edges `f`, `g` and `h` carries a degree `-1`
  morphism `η` with `d η = g ∘ f - h`, a homotopy rather than an equality.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Example 1.3.1.8.
* J. Lurie, *Kerodon*, Section 2.5.3 (the differential graded nerve).
-/

public section

open CategoryTheory Opposite Simplicial Finset

namespace TauCeti

namespace DGNerve

universe v u w w'

/-! ### Indices of coherences -/

section Index

variable {ι : Type w} [LinearOrder ι]

/-- `IsIndex i j S m` says that `S` is a finite set of vertices lying strictly between `i < j`
and that `m = -#S`.  It indexes the coherence of a dg nerve simplex on the vertex set
`{i} ∪ S ∪ {j}`, a morphism of cohomological degree `m`. -/
def IsIndex (i j : ι) (S : Finset ι) (m : ℤ) : Prop :=
  i < j ∧ (∀ v ∈ S, i < v ∧ v < j) ∧ m = -(#S : ℤ)

variable {i j v : ι} {S : Finset ι} {m : ℤ}

theorem IsIndex.lt (h : IsIndex i j S m) : i < j := h.1

theorem IsIndex.mem (h : IsIndex i j S m) (hv : v ∈ S) : i < v ∧ v < j := h.2.1 v hv

theorem IsIndex.degree (h : IsIndex i j S m) : m = -(#S : ℤ) := h.2.2

/-- An index with no interior vertices is an edge, of degree zero. -/
theorem isIndex_empty_iff : IsIndex i j ∅ m ↔ i < j ∧ m = 0 := by
  simp [IsIndex]

/-- Removing an interior vertex raises the degree by one. -/
theorem IsIndex.erase (h : IsIndex i j S m) (hv : v ∈ S) : IsIndex i j (S.erase v) (m + 1) := by
  refine ⟨h.lt, fun w hw ↦ h.mem (mem_of_mem_erase hw), ?_⟩
  rw [h.degree, card_erase_of_mem hv, Nat.cast_sub (one_le_card.mpr ⟨v, hv⟩)]
  ring

/-- The interior vertices below an interior vertex `v` index a coherence from `i` to `v`. -/
theorem IsIndex.lower (h : IsIndex i j S m) (hv : v ∈ S) :
    IsIndex i v {w ∈ S | w < v} (-(#{w ∈ S | w < v} : ℤ)) := by
  refine ⟨(h.mem hv).1, fun w hw ↦ ?_, rfl⟩
  rw [mem_filter] at hw
  exact ⟨(h.mem hw.1).1, hw.2⟩

/-- The interior vertices above an interior vertex `v` index a coherence from `v` to `j`. -/
theorem IsIndex.upper (h : IsIndex i j S m) (hv : v ∈ S) :
    IsIndex v j {w ∈ S | v < w} (-(#{w ∈ S | v < w} : ℤ)) := by
  refine ⟨(h.mem hv).2, fun w hw ↦ ?_, rfl⟩
  rw [mem_filter] at hw
  exact ⟨hw.2, (h.mem hw.1).2⟩

/-- An interior vertex splits the remaining interior vertices into those below and above it. -/
theorem card_filter_lt_add_card_filter_gt (hv : v ∈ S) :
    #{w ∈ S | w < v} + #{w ∈ S | v < w} + 1 = #S := by
  have h₁ := card_filter_add_card_filter_not (s := S) (· < v)
  have h₂ := card_filter_add_card_filter_not (s := {w ∈ S | ¬w < v}) (v < ·)
  have h₃ : {w ∈ {w ∈ S | ¬w < v} | ¬v < w} = {v} := by
    ext w
    simp only [mem_filter, not_lt, mem_singleton]
    exact ⟨fun hw ↦ le_antisymm hw.2 hw.1.2, fun hw ↦ by subst hw; exact ⟨⟨hv, le_rfl⟩, le_rfl⟩⟩
  have h₄ : {w ∈ {w ∈ S | ¬w < v} | v < w} = {w ∈ S | v < w} := by
    ext w
    simp only [mem_filter, not_lt]
    exact ⟨fun hw ↦ ⟨hw.1.1, hw.2⟩, fun hw ↦ ⟨⟨hw.1, hw.2.le⟩, hw.2⟩⟩
  rw [h₃, h₄, card_singleton] at h₂
  omega

/-- The degrees of the two factors of a split coherence add up to the degree of the face. -/
theorem IsIndex.degree_add (h : IsIndex i j S m) (hv : v ∈ S) :
    -(#{w ∈ S | w < v} : ℤ) + -(#{w ∈ S | v < w} : ℤ) = m + 1 := by
  have := card_filter_lt_add_card_filter_gt hv
  rw [h.degree]
  omega

/-- The image of an index under a monotone map injective on its vertices is an index of the same
degree. -/
theorem IsIndex.image {κ : Type w'} [LinearOrder κ] {α : κ → ι} {i j : κ} {S : Finset κ}
    (h : IsIndex i j S m) (hα : Monotone α)
    (hinj : Set.InjOn α (insert i (insert j S) : Finset κ)) :
    IsIndex (α i) (α j) (S.image α) m := by
  have hi : i ∈ ((insert i (insert j S) : Finset κ) : Set κ) := by simp
  have hj : j ∈ ((insert i (insert j S) : Finset κ) : Set κ) := by simp
  have hS : ∀ v ∈ S, v ∈ ((insert i (insert j S) : Finset κ) : Set κ) := fun v hv ↦ by
    simp [hv]
  have hlt := (hα.monotoneOn _).strictMonoOn_of_injOn hinj
  refine ⟨hlt hi hj h.lt, fun w hw ↦ ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    exact ⟨hlt hi (hS v hv) (h.mem hv).1, hlt (hS v hv) hj (h.mem hv).2⟩
  · rw [card_image_of_injOn (hinj.mono fun v hv ↦ hS v hv), h.degree]

end Index

/-! ### Families of coherences -/

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The data of a simplex of the differential graded nerve indexed by a linear order `ι`, before
the dg nerve equations are imposed: an object for every vertex and a coherence
`coh i j S m : obj i ⟶ obj j` of cohomological degree `m = -#S` for every index
(`TauCeti.DGNerve.IsIndex`).  The `n`-simplices of `TauCeti.dgNerve` are the families indexed by
`Fin (n + 1)` satisfying `TauCeti.DGNerve.Family.IsCoherent`. -/
structure Family (ι : Type w) [LinearOrder ι] where
  /-- The object at a vertex. -/
  obj : ι → C
  /-- The coherence on the vertex set `{i} ∪ S ∪ {j}`, of cohomological degree `m = -#S`. -/
  coh (i j : ι) (S : Finset ι) (m : ℤ) : IsIndex i j S m → DGHom R m (obj i) (obj j)

namespace Family

variable {R C} {ι : Type w} [LinearOrder ι]

/-- Two families agree when their objects agree and their coherences agree up to the resulting
identification of Hom types. -/
@[ext]
theorem ext {x y : Family R C ι} (hobj : x.obj = y.obj)
    (hcoh : ∀ i j S m h, HEq (x.coh i j S m h) (y.coh i j S m h)) : x = y := by
  cases x with | mk xobj xcoh => ?_
  cases y with | mk yobj ycoh => ?_
  subst hobj
  congr
  funext i j S m h
  exact eq_of_heq (hcoh i j S m h)

variable (x : Family R C ι)

/-- A coherence only depends on its index through the vertex set. -/
theorem coh_congr {i j : ι} {S S' : Finset ι} {m : ℤ} (hS : S = S') (h : IsIndex i j S m)
    (h' : IsIndex i j S' m) : x.coh i j S m h = x.coh i j S' m h' := by
  subst hS
  rfl

/-- The Keller-ordered composite `f_B ∘ f_A` of the coherence on `{i} ∪ A ∪ {v}` and the
coherence on `{v} ∪ B ∪ {j}`, that is `(-1) ^ (p * q) • dgComp f_A f_B`. -/
noncomputable def compTerm {i v j : ι} {A B : Finset ι} {p q n : ℤ} (hA : IsIndex i v A p)
    (hB : IsIndex v j B q) (hn : p + q = n) : DGHom R n (x.obj i) (x.obj j) :=
  (p * q).negOnePow • dgComp R (x.coh i v A p hA) (x.coh v j B q hB) hn

theorem compTerm_def {i v j : ι} {A B : Finset ι} {p q n : ℤ} (hA : IsIndex i v A p)
    (hB : IsIndex v j B q) (hn : p + q = n) :
    x.compTerm hA hB hn = (p * q).negOnePow • dgComp R (x.coh i v A p hA) (x.coh v j B q hB) hn :=
  (rfl)

/-- A composite of coherences only depends on the vertex sets of its two factors. -/
theorem compTerm_congr {i v j : ι} {A A' B B' : Finset ι} {p p' q q' n : ℤ} (hAA' : A = A')
    (hBB' : B = B') (hA : IsIndex i v A p) (hB : IsIndex v j B q) (hn : p + q = n)
    (hA' : IsIndex i v A' p') (hB' : IsIndex v j B' q') (hn' : p' + q' = n) :
    x.compTerm hA hB hn = x.compTerm hA' hB' hn' := by
  subst hAA' hBB'
  obtain rfl : p = p' := hA.degree.trans hA'.degree.symm
  obtain rfl : q = q' := hB.degree.trans hB'.degree.symm
  rfl

/-- The summand of the dg nerve equation at an interior vertex `v`:
`(-1) ^ (#{w ∈ S | v < w} + 1) • (f_{I ∖ {v}} - f_{I_{≥ v}} ∘ f_{I_{≤ v}})`, and zero when `v` is
not an interior vertex. -/
noncomputable def boundaryTerm {i j : ι} {S : Finset ι} {m : ℤ} (h : IsIndex i j S m) (v : ι) :
    DGHom R (m + 1) (x.obj i) (x.obj j) :=
  if hv : v ∈ S then
    ((#{w ∈ S | v < w} : ℤ) + 1).negOnePow •
      (x.coh i j (S.erase v) (m + 1) (h.erase hv) -
        x.compTerm (h.lower hv) (h.upper hv) (h.degree_add hv))
  else 0

theorem boundaryTerm_of_mem {i j : ι} {S : Finset ι} {m : ℤ} (h : IsIndex i j S m) {v : ι}
    (hv : v ∈ S) :
    x.boundaryTerm h v = ((#{w ∈ S | v < w} : ℤ) + 1).negOnePow •
      (x.coh i j (S.erase v) (m + 1) (h.erase hv) -
        x.compTerm (h.lower hv) (h.upper hv) (h.degree_add hv)) :=
  dite_eq_left hv

/-- The right-hand side of the dg nerve equation for the coherence on `{i} ∪ S ∪ {j}`. -/
noncomputable def boundary {i j : ι} {S : Finset ι} {m : ℤ} (h : IsIndex i j S m) :
    DGHom R (m + 1) (x.obj i) (x.obj j) :=
  ∑ v ∈ S, x.boundaryTerm h v

theorem boundary_def {i j : ι} {S : Finset ι} {m : ℤ} (h : IsIndex i j S m) :
    x.boundary h = ∑ v ∈ S, x.boundaryTerm h v :=
  (rfl)

/-- **The dg nerve equations** (Lurie, *Higher Algebra*, Construction 1.3.1.6): the differential
of every coherence `f_I` is
`∑_v (-1) ^ #{w ∈ I | v < w} • (f_{I ∖ {v}} - f_{I_{≥ v}} ∘ f_{I_{≤ v}})`, the sum running over
the interior vertices of `I`. -/
def IsCoherent : Prop :=
  ∀ (i j : ι) (S : Finset ι) (m : ℤ) (h : IsIndex i j S m),
    dgDifferential R m (x.coh i j S m h) = x.boundary h

end Family

/-! ### The action of monotone maps -/

variable {R C}

/-- The identity of `X a`, regarded as a morphism `X a ⟶ X b` of degree `m` along equalities
`a = b` and `m = 0`.  It is the coherence that a monotone map assigns to a collapsed edge. -/
noncomputable def idOfEq {ι : Type w} (X : ι → C) {a b : ι} (hab : a = b) {m : ℤ} (hm : m = 0) :
    DGHom R m (X a) (X b) := by
  subst hab hm
  exact dgId R (X a)

@[simp]
theorem idOfEq_rfl {ι : Type w} (X : ι → C) (a : ι) : idOfEq (R := R) X (rfl : a = a) rfl =
    dgId R (X a) :=
  (rfl)

@[simp]
theorem dgDifferential_idOfEq {ι : Type w} (X : ι → C) {a b : ι} (hab : a = b) {m : ℤ}
    (hm : m = 0) : dgDifferential R m (idOfEq (R := R) X hab hm) = 0 := by
  subst hab hm
  exact dgDifferential_dgId R (X a)

namespace Family

variable {ι : Type w} [LinearOrder ι] {κ : Type w'} [LinearOrder κ]

/-- The action of a monotone map `α : κ → ι` on dg nerve families (Lurie, *Higher Algebra*,
Construction 1.3.1.6): the objects are reindexed along `α`, the coherence on a vertex set on
which `α` is injective is the coherence on its image, a collapsed edge receives the identity,
and every other coherence is zero.

It is reducible so that the objects of a pullback unfold to `x.obj (α a)` when statements about
its coherences are elaborated and rewritten. -/
noncomputable abbrev pullback (x : Family R C ι) (α : κ →o ι) : Family R C κ where
  obj a := x.obj (α a)
  coh i j S m h := by
    classical
    exact if hα : Set.InjOn α (insert i (insert j S) : Finset κ) then
      x.coh (α i) (α j) (S.image α) m (h.image α.monotone hα)
    else if hS : S = ∅ ∧ α i = α j then
      idOfEq x.obj hS.2 (by rw [h.degree, hS.1, card_empty, Nat.cast_zero, neg_zero])
    else 0

variable (x : Family R C ι) (α : κ →o ι)

@[simp]
theorem pullback_obj (a : κ) : (x.pullback α).obj a = x.obj (α a) :=
  (rfl)

/-- On a vertex set on which the map is injective, a coherence of the pullback is the coherence
on the image. -/
theorem pullback_coh_of_injOn {i j : κ} {S : Finset κ} {m : ℤ} (h : IsIndex i j S m)
    (hα : Set.InjOn α (insert i (insert j S) : Finset κ)) :
    (x.pullback α).coh i j S m h = x.coh (α i) (α j) (S.image α) m (h.image α.monotone hα) := by
  simp only [pullback]
  rw [dite_eq_left hα]

/-- An edge collapsed by the map receives the identity. -/
theorem pullback_coh_of_eq {i j : κ} {m : ℤ} (h : IsIndex i j ∅ m) (hij : α i = α j) :
    (x.pullback α).coh i j ∅ m h =
      idOfEq x.obj hij (by rw [h.degree, card_empty, Nat.cast_zero, neg_zero]) := by
  have hα : ¬Set.InjOn α (insert i (insert j ∅) : Finset κ) := fun hα ↦
    h.lt.ne (hα (by simp) (by simp) hij)
  simp only [pullback]
  rw [dite_eq_right hα, dite_eq_left (by simpa using hij)]

/-- A coherence with interior vertices on whose vertex set the map is not injective is zero. -/
theorem pullback_coh_eq_zero {i j : κ} {S : Finset κ} {m : ℤ} (h : IsIndex i j S m)
    (hα : ¬Set.InjOn α (insert i (insert j S) : Finset κ)) (hS : S.Nonempty) :
    (x.pullback α).coh i j S m h = 0 := by
  simp only [pullback]
  rw [dite_eq_right hα, dite_eq_right fun h' ↦ hS.ne_empty h'.1]

/-- The pullback along the identity is the original family. -/
@[simp]
theorem pullback_id : x.pullback OrderHom.id = x := by
  ext i j S m h
  · rfl
  · rw [pullback_coh_of_injOn x _ h Function.injective_id.injOn]
    exact heq_of_eq (x.coh_congr (by simp) _ _)

/-- Pulling back along `α` and then along `β` is pulling back along `α ∘ β`. -/
theorem pullback_pullback {μ : Type*} [LinearOrder μ] (β : μ →o κ) :
    (x.pullback α).pullback β = x.pullback (α.comp β) := by
  ext i j S m h
  · rfl
  apply heq_of_eq
  have himage : ((insert (β i) (insert (β j) (S.image β)) : Finset κ) : Set κ) =
      β '' (insert i (insert j S) : Finset μ) := by
    simp [Set.image_insert_eq]
  by_cases hαβ : Set.InjOn (α.comp β) (insert i (insert j S) : Finset μ)
  · have hαβ' : Set.InjOn (α ∘ β) (insert i (insert j S) : Finset μ) := hαβ
    have hβ : Set.InjOn β (insert i (insert j S) : Finset μ) := hαβ'.of_comp
    have hα : Set.InjOn α (insert (β i) (insert (β j) (S.image β)) : Finset κ) := by
      rw [himage]
      exact hαβ'.image_of_comp
    rw [pullback_coh_of_injOn _ _ h hβ, pullback_coh_of_injOn _ _ _ hα,
      pullback_coh_of_injOn _ _ h hαβ]
    exact x.coh_congr (by rw [image_image]; rfl) _ _
  by_cases hS : S = ∅
  · subst hS
    have hcol : α (β i) = α (β j) := by
      by_contra hne
      exact hαβ (by simpa using fun e ↦ absurd e hne)
    rw [pullback_coh_of_eq _ (α.comp β) h hcol]
    by_cases hβ : β i = β j
    · rw [pullback_coh_of_eq _ _ h hβ]
      have key : ∀ (a b : κ) (hab : a = b),
          idOfEq (R := R) (x.obj ∘ α) hab (m := m) (by rw [h.degree, card_empty]; rfl) =
            idOfEq x.obj (congrArg α hab) (by rw [h.degree, card_empty]; rfl) := by
        rintro a _ rfl
        rfl
      exact key _ _ hβ
    · have hβinj : Set.InjOn β (insert i (insert j ∅) : Finset μ) := by
        simpa using fun e ↦ absurd e hβ
      rw [pullback_coh_of_injOn _ _ h hβinj]
      have h' : IsIndex (β i) (β j) ∅ m := by
        simpa using h.image β.monotone hβinj
      rw [(x.pullback α).coh_congr (image_empty β) _ h', pullback_coh_of_eq _ _ h' hcol]
      rfl
  · have hne : S.Nonempty := nonempty_iff_ne_empty.mpr hS
    rw [pullback_coh_eq_zero _ (α.comp β) h hαβ hne]
    by_cases hβ : Set.InjOn β (insert i (insert j S) : Finset μ)
    · have hα : ¬Set.InjOn α (insert (β i) (insert (β j) (S.image β)) : Finset κ) := by
        rw [himage]
        exact fun hα ↦ hαβ (hα.comp hβ (Set.mapsTo_image _ _))
      rw [pullback_coh_of_injOn _ _ h hβ, pullback_coh_eq_zero _ _ _ hα (hne.image β)]
      rfl
    · rw [pullback_coh_eq_zero _ _ h hβ hne]
      rfl

/-- Pulling back a composite of coherences along a map injective on both vertex sets composes
the coherences on the images. -/
theorem pullback_compTerm_of_injOn {i v j : κ} {A B : Finset κ} {p q n : ℤ}
    (hA : IsIndex i v A p) (hB : IsIndex v j B q) (hn : p + q = n)
    (hαA : Set.InjOn α (insert i (insert v A) : Finset κ))
    (hαB : Set.InjOn α (insert v (insert j B) : Finset κ)) :
    (x.pullback α).compTerm hA hB hn =
      x.compTerm (hA.image α.monotone hαA) (hB.image α.monotone hαB) hn := by
  rw [compTerm_def, compTerm_def, pullback_coh_of_injOn x α hA hαA,
    pullback_coh_of_injOn x α hB hαB]

end Family

/-! ### Monotone maps preserve the dg nerve equations -/

namespace Family

variable {ι : Type w} [LinearOrder ι] {κ : Type w'} [LinearOrder κ]
  {x : Family R C ι}

/-- The dg nerve equation of a pulled-back coherence, on a vertex set on which the map is
injective: it is the reindexed equation of the original family. -/
theorem IsCoherent.pullback_apply_of_injOn (hx : x.IsCoherent) (α : κ →o ι) {i j : κ}
    {S : Finset κ} {m : ℤ} (h : IsIndex i j S m)
    (hα : Set.InjOn α (insert i (insert j S) : Finset κ)) :
    dgDifferential R m ((x.pullback α).coh i j S m h) = (x.pullback α).boundary h := by
  have hiT : i ∈ insert i (insert j S) := mem_insert_self _ _
  have hjT : j ∈ insert i (insert j S) := mem_insert_of_mem (mem_insert_self _ _)
  have hST : S ⊆ insert i (insert j S) := (subset_insert _ _).trans (subset_insert _ _)
  have hSinj : Set.InjOn α S := hα.mono (coe_subset.mpr hST)
  have hlt := (α.monotone.monotoneOn _).strictMonoOn_of_injOn hα
  rw [pullback_coh_of_injOn x α h hα, hx, boundary_def, boundary_def, sum_image hSinj]
  refine sum_congr rfl fun v hv ↦ ?_
  have hvT := hST hv
  -- Since `α` is strictly monotone on the vertex set, it carries the vertices of `S` below and
  -- above `v` to those of `S.image α` below and above `α v`.
  have hlow_image : {w ∈ S.image α | w < α v} = {w ∈ S | w < v}.image α := by
    rw [filter_image]
    exact congrArg _ (filter_congr fun w hw ↦ ⟨fun h ↦ lt_of_not_ge fun h' ↦
      (α.monotone h').not_gt h, hlt (mem_coe.mpr (hST hw)) (mem_coe.mpr hvT)⟩)
  have hup_image : {w ∈ S.image α | α v < w} = {w ∈ S | v < w}.image α := by
    rw [filter_image]
    exact congrArg _ (filter_congr fun w hw ↦ ⟨fun h ↦ lt_of_not_ge fun h' ↦
      (α.monotone h').not_gt h, hlt (mem_coe.mpr hvT) (mem_coe.mpr (hST hw))⟩)
  have herase_image : (S.erase v).image α = (S.image α).erase (α v) := by
    rw [← sdiff_singleton_eq_erase, ← sdiff_singleton_eq_erase,
      image_sdiff_of_injOn hSinj (singleton_subset_iff.mpr hv), image_singleton]
  rw [boundaryTerm_of_mem _ _ (mem_image_of_mem α hv), boundaryTerm_of_mem _ _ hv]
  congr 1
  · rw [hup_image, card_image_of_injOn (hSinj.mono (coe_subset.mpr (filter_subset _ _)))]
  have hlow : Set.InjOn α (insert i (insert v {w ∈ S | w < v}) : Finset κ) :=
    hα.mono (coe_subset.mpr (insert_subset hiT (insert_subset hvT ((filter_subset _ _).trans hST))))
  have hup : Set.InjOn α (insert v (insert j {w ∈ S | v < w}) : Finset κ) :=
    hα.mono (coe_subset.mpr (insert_subset hvT (insert_subset hjT ((filter_subset _ _).trans hST))))
  have herase : Set.InjOn α (insert i (insert j (S.erase v)) : Finset κ) :=
    hα.mono (coe_subset.mpr (insert_subset hiT (insert_subset hjT ((erase_subset _ _).trans hST))))
  rw [pullback_coh_of_injOn x α _ herase, pullback_compTerm_of_injOn x α _ _ _ hlow hup]
  congr 1
  · exact x.coh_congr herase_image.symm _ _
  · exact x.compTerm_congr hlow_image hup_image _ _ _ _ _ _

/-- Injective monotone maps preserve the dg nerve equations. -/
theorem IsCoherent.pullback_of_injective (hx : x.IsCoherent) {α : κ →o ι}
    (hα : Function.Injective α) : (x.pullback α).IsCoherent :=
  fun _ _ _ _ h ↦ hx.pullback_apply_of_injOn α h hα.injOn

/-! #### Maps collapsing one pair of adjacent vertices -/

/-- Precomposing a coherence with a collapsed edge gives the coherence from the source of that
edge. -/
theorem idOfEq_dgComp_coh (x : Family R C ι) {a b c : ι} (hab : a = b) {S : Finset ι}
    {p q n : ℤ} (hp : p = 0) (hb : IsIndex b c S q) (ha : IsIndex a c S n) (hn : p + q = n) :
    dgComp R (idOfEq x.obj hab hp) (x.coh b c S q hb) hn = x.coh a c S n ha := by
  subst hab hp
  obtain rfl : q = n := by omega
  exact dgId_dgComp R _

/-- Postcomposing a coherence with a collapsed edge gives the coherence to the target of that
edge. -/
theorem dgComp_idOfEq_coh (x : Family R C ι) {a b c : ι} (hbc : b = c) {S : Finset ι}
    {p q n : ℤ} (hq : q = 0) (hb : IsIndex a b S p) (hc : IsIndex a c S n) (hn : p + q = n) :
    dgComp R (x.coh a b S p hb) (idOfEq x.obj hbc hq) hn = x.coh a c S n hc := by
  subst hbc hq
  obtain rfl : p = n := by omega
  exact dgComp_dgId R _

/-- A composite of coherences vanishes when its first factor does. -/
theorem compTerm_eq_zero_of_left (x : Family R C ι) {i v j : ι} {A B : Finset ι} {p q n : ℤ}
    (hA : IsIndex i v A p) (hB : IsIndex v j B q) (hn : p + q = n) (h0 : x.coh i v A p hA = 0) :
    x.compTerm hA hB hn = 0 := by
  rw [compTerm_def, h0, zero_dgComp, smul_zero]

/-- A composite of coherences vanishes when its second factor does. -/
theorem compTerm_eq_zero_of_right (x : Family R C ι) {i v j : ι} {A B : Finset ι} {p q n : ℤ}
    (hA : IsIndex i v A p) (hB : IsIndex v j B q) (hn : p + q = n) (h0 : x.coh v j B q hB = 0) :
    x.compTerm hA hB hn = 0 := by
  rw [compTerm_def, h0, dgComp_zero, smul_zero]

/-- A pulled-back composite whose first factor is a collapsed edge is a single coherence. -/
theorem pullback_compTerm_of_eq_left (x : Family R C ι) (α : κ →o ι) {i v j : κ}
    {A B : Finset κ} {p q n : ℤ} (hA : IsIndex i v A p) (hB : IsIndex v j B q) (hn : p + q = n)
    (hA0 : A = ∅) (hiv : α i = α v) (hαB : Set.InjOn α (insert v (insert j B) : Finset κ))
    (h : IsIndex (α i) (α j) (B.image α) n) :
    (x.pullback α).compTerm hA hB hn = x.coh (α i) (α j) (B.image α) n h := by
  subst hA0
  obtain rfl : p = 0 := by rw [hA.degree, card_empty, Nat.cast_zero, neg_zero]
  rw [compTerm_def, pullback_coh_of_eq x α hA hiv, pullback_coh_of_injOn x α hB hαB, zero_mul,
    Int.negOnePow_zero, one_smul]
  exact idOfEq_dgComp_coh x hiv rfl _ h hn

/-- A pulled-back composite whose second factor is a collapsed edge is a single coherence. -/
theorem pullback_compTerm_of_eq_right (x : Family R C ι) (α : κ →o ι) {i v j : κ}
    {A B : Finset κ} {p q n : ℤ} (hA : IsIndex i v A p) (hB : IsIndex v j B q) (hn : p + q = n)
    (hB0 : B = ∅) (hvj : α v = α j) (hαA : Set.InjOn α (insert i (insert v A) : Finset κ))
    (h : IsIndex (α i) (α j) (A.image α) n) :
    (x.pullback α).compTerm hA hB hn = x.coh (α i) (α j) (A.image α) n h := by
  subst hB0
  obtain rfl : q = 0 := by rw [hB.degree, card_empty, Nat.cast_zero, neg_zero]
  rw [compTerm_def, pullback_coh_of_eq x α hB hvj, pullback_coh_of_injOn x α hA hαA, mul_zero,
    Int.negOnePow_zero, one_smul]
  exact dgComp_idOfEq_coh x hvj rfl _ h hn

end Family

section Collapse

variable {ι : Type w} [LinearOrder ι] {κ : Type w'} [LinearOrder κ] {α : κ → ι} {k k' : κ}

omit [LinearOrder ι] in
/-- For a map whose only collapse is `α k = α k'`, injectivity on a vertex set means not
containing both `k` and `k'`. -/
private theorem injOn_iff_of_collapse (hkk' : k < k') (hk : α k = α k')
    (hcol : ∀ a b, a < b → α a = α b → a = k ∧ b = k') (U : Finset κ) :
    Set.InjOn α U ↔ ¬(k ∈ U ∧ k' ∈ U) := by
  refine ⟨fun hU hkU ↦ hkk'.ne (hU (mem_coe.mpr hkU.1) (mem_coe.mpr hkU.2) hk),
    fun hU a ha b hb hab ↦ ?_⟩
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · obtain ⟨rfl, rfl⟩ := hcol a b hlt hab
    exact absurd ⟨ha, hb⟩ hU
  · rfl
  · obtain ⟨rfl, rfl⟩ := hcol b a hgt hab.symm
    exact absurd ⟨hb, ha⟩ hU

/-- The two vertices collapsed by a monotone map with a single collapse are adjacent. -/
private theorem not_between_of_collapse (hα : Monotone α) (hk : α k = α k')
    (hcol : ∀ a b, a < b → α a = α b → a = k ∧ b = k') {c : κ} (hc : k < c) (hc' : c < k') :
    False :=
  hc'.ne (hcol k c hc (le_antisymm (hα hc.le) (hk ▸ hα hc'.le))).2

end Collapse

namespace Family

variable {ι : Type w} [LinearOrder ι] {κ : Type w'} [LinearOrder κ] {x : Family R C ι}

/-- The dg nerve equation of a pulled-back coherence, for a monotone map whose only collapse is
`α k = α k'`.  A collapsed coherence with interior vertices is zero, and in its equation at most
two summands survive: either a single summand whose two parts agree because composing with the
collapsed edge is the identity, or the faces omitting `k` and `k'`, which agree and carry
opposite signs. -/
theorem IsCoherent.pullback_apply_of_collapse (hx : x.IsCoherent) (α : κ →o ι) {k k' : κ}
    (hkk' : k < k') (hk : α k = α k') (hcol : ∀ a b, a < b → α a = α b → a = k ∧ b = k')
    {i j : κ} {S : Finset κ} {m : ℤ} (h : IsIndex i j S m) :
    dgDifferential R m ((x.pullback α).coh i j S m h) = (x.pullback α).boundary h := by
  have hinj := injOn_iff_of_collapse hkk' hk hcol
  have hbtw : ∀ c, k < c → c < k' → False := fun c hc hc' ↦
    not_between_of_collapse α.monotone hk hcol hc hc'
  by_cases hT : Set.InjOn α (insert i (insert j S) : Finset κ)
  · exact hx.pullback_apply_of_injOn α h hT
  obtain ⟨hkT, hk'T⟩ := not_not.mp ((hinj _).not.mp hT)
  -- A pulled-back coherence with interior vertices whose vertex set contains `k` and `k'` is zero.
  have hzero : ∀ {a b : κ} {A : Finset κ} {p : ℤ} (hA : IsIndex a b A p),
      k ∈ insert a (insert b A) → k' ∈ insert a (insert b A) → A.Nonempty →
        (x.pullback α).coh a b A p hA = 0 := fun hA h₁ h₂ hne ↦
    pullback_coh_eq_zero x α hA (fun H ↦ (hinj _).mp H ⟨h₁, h₂⟩) hne
  have hinjOf : ∀ {U : Finset κ}, (k ∉ U ∨ k' ∉ U) → Set.InjOn α U := fun hU ↦
    (hinj _).mpr fun hU' ↦ hU.elim (· hU'.1) (· hU'.2)
  simp only [mem_insert] at hkT hk'T
  have hk'j : k' ≤ j := by
    rcases hk'T with e | e | e
    exacts [e ▸ h.lt.le, e.le, (h.mem e).2.le]
  have hik : i ≤ k := by
    rcases hkT with e | e | e
    exacts [e.ge, e ▸ h.lt.le, (h.mem e).1.le]
  have hkS' : k = i ∨ k ∈ S := by
    rcases hkT with e | e | e
    exacts [Or.inl e, absurd (e ▸ hkk') (not_lt.mpr hk'j), Or.inr e]
  have hk'S' : k' = j ∨ k' ∈ S := by
    rcases hk'T with e | e | e
    exacts [absurd (e ▸ hkk') (not_lt.mpr hik), Or.inl e, Or.inr e]
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hki : k = i := hkS'.resolve_right (notMem_empty k)
    have hk'j : k' = j := hk'S'.resolve_right (notMem_empty k')
    have hij : α i = α j := by rw [← hki, ← hk'j, hk]
    rw [boundary_def, sum_empty, pullback_coh_of_eq x α h hij]
    exact dgDifferential_idOfEq (R := R) x.obj hij _
  rw [pullback_coh_eq_zero x α h hT hne, map_zero, boundary_def]
  refine Eq.symm ?_
  rcases hkS' with hki | hkS <;> rcases hk'S' with hk'j | hk'S
  · obtain ⟨v, hv⟩ := hne
    exact (hbtw v (hki ▸ (h.mem hv).1) (hk'j ▸ (h.mem hv).2)).elim
  · -- `k = i`: the only summand that might survive is at `k'`, where composing with the collapsed
    -- edge from `i` to `k'` is the identity.
    have hS_gt : ∀ w ∈ S, w ≠ k' → k' < w := fun w hw hne ↦
      lt_of_le_of_ne (le_of_not_gt fun hlt ↦ hbtw w (hki ▸ (h.mem hw).1) hlt) (Ne.symm hne)
    refine sum_eq_zero fun v hv ↦ ?_
    rw [boundaryTerm_of_mem _ h hv]
    by_cases hvk' : v = k'
    · subst hvk'
      have hA : {w ∈ S | w < v} = ∅ := filter_eq_empty_iff.mpr fun w hw hlt ↦
        (hS_gt w hw hlt.ne).not_gt hlt
      have hB : {w ∈ S | v < w} = S.erase v := by
        ext w
        simp only [mem_filter, mem_erase]
        exact ⟨fun hw ↦ ⟨hw.2.ne', hw.1⟩, fun hw ↦ ⟨hw.2, hS_gt w hw.2 hw.1⟩⟩
      have hkU : k ∉ insert v (insert j {w ∈ S | v < w}) := by
        simp only [mem_insert, mem_filter, not_or, not_and, not_lt]
        exact ⟨hkk'.ne, (hki ▸ h.lt).ne, fun _ ↦ hkk'.le⟩
      have hvU : v ∉ insert i (insert j (S.erase v)) := by
        simp only [mem_insert, mem_erase, not_or, not_and]
        exact ⟨(h.mem hv).1.ne', (h.mem hv).2.ne, fun e ↦ absurd rfl e⟩
      rw [pullback_coh_of_injOn x α _ (hinjOf (Or.inr hvU)),
        pullback_compTerm_of_eq_left x α _ _ _ hA (by rw [← hki, hk]) (hinjOf (Or.inl hkU))
          (by rw [hB]; exact (h.erase hv).image α.monotone (hinjOf (Or.inr hvU))),
        sub_eq_zero.mpr (x.coh_congr (by rw [hB]) _ _), smul_zero]
    · have hlt : k' < v := hS_gt v hv hvk'
      rw [hzero (h.erase hv) (hki ▸ mem_insert_self _ _)
          (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨Ne.symm hvk', hk'S⟩)))
          ⟨k', mem_erase.mpr ⟨Ne.symm hvk', hk'S⟩⟩,
        compTerm_eq_zero_of_left _ _ _ _ (hzero (h.lower hv) (hki ▸ mem_insert_self _ _)
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hk'S, hlt⟩)))
          ⟨k', mem_filter.mpr ⟨hk'S, hlt⟩⟩), sub_zero, smul_zero]
  · -- `k' = j`: the only summand that might survive is at `k`, where composing with the collapsed
    -- edge from `k` to `j` is the identity.
    have hS_lt : ∀ w ∈ S, w ≠ k → w < k := fun w hw hne ↦
      lt_of_le_of_ne (le_of_not_gt fun hlt ↦ hbtw w hlt (hk'j ▸ (h.mem hw).2)) hne
    refine sum_eq_zero fun v hv ↦ ?_
    rw [boundaryTerm_of_mem _ h hv]
    by_cases hvk : v = k
    · subst hvk
      have hB : {w ∈ S | v < w} = ∅ := filter_eq_empty_iff.mpr fun w hw hlt ↦
        (hS_lt w hw hlt.ne').not_gt hlt
      have hA : {w ∈ S | w < v} = S.erase v := by
        ext w
        simp only [mem_filter, mem_erase]
        exact ⟨fun hw ↦ ⟨hw.2.ne, hw.1⟩, fun hw ↦ ⟨hw.2, hS_lt w hw.2 hw.1⟩⟩
      have hk'U : k' ∉ insert i (insert v {w ∈ S | w < v}) := by
        simp only [mem_insert, mem_filter, not_or, not_and, not_lt]
        exact ⟨(hk'j ▸ h.lt).ne', hkk'.ne', fun _ ↦ hkk'.le⟩
      have hvU : v ∉ insert i (insert j (S.erase v)) := by
        simp only [mem_insert, mem_erase, not_or, not_and]
        exact ⟨(h.mem hv).1.ne', (h.mem hv).2.ne, fun e ↦ absurd rfl e⟩
      rw [pullback_coh_of_injOn x α _ (hinjOf (Or.inl hvU)),
        pullback_compTerm_of_eq_right x α _ _ _ hB (by rw [← hk'j, hk]) (hinjOf (Or.inr hk'U))
          (by rw [hA]; exact (h.erase hv).image α.monotone (hinjOf (Or.inl hvU))),
        sub_eq_zero.mpr (x.coh_congr (by rw [hA]) _ _), smul_zero]
    · have hlt : v < k := hS_lt v hv hvk
      rw [hzero (h.erase hv)
          (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨Ne.symm hvk, hkS⟩)))
          (hk'j ▸ mem_insert_of_mem (mem_insert_self _ _))
          ⟨k, mem_erase.mpr ⟨Ne.symm hvk, hkS⟩⟩,
        compTerm_eq_zero_of_right _ _ _ _ (hzero (h.upper hv)
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hkS, hlt⟩)))
          (hk'j ▸ mem_insert_of_mem (mem_insert_self _ _))
          ⟨k, mem_filter.mpr ⟨hkS, hlt⟩⟩), sub_zero, smul_zero]
  · -- `k` and `k'` are both interior: the faces omitting them agree and carry opposite signs.
    have hS_out : ∀ w ∈ S, w ≠ k → w ≠ k' → w < k ∨ k' < w := fun w hw hwk hwk' ↦ by
      rcases lt_or_gt_of_ne hwk with hlt | hgt
      · exact Or.inl hlt
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (hbtw w hgt)) (Ne.symm hwk'))
    rw [sum_eq_add_of_mem k k' hkS hk'S hkk'.ne fun c hc hck ↦ ?_]
    · have hcard : #{w ∈ S | k < w} = #{w ∈ S | k' < w} + 1 := by
        have : {w ∈ S | k < w} = insert k' {w ∈ S | k' < w} := by
          ext w
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨hw, hkw⟩
            by_cases hwk' : w = k'
            · exact Or.inl hwk'
            · exact Or.inr ⟨hw, (hS_out w hw hkw.ne' hwk').resolve_left hkw.not_gt⟩
          · rintro (rfl | ⟨hw, hk'w⟩)
            exacts [⟨hk'S, hkk'⟩, ⟨hw, hkk'.trans hk'w⟩]
        rw [this, card_insert_of_notMem (by simp)]
      -- Removing either of `k` and `k'` leaves the image of `S` unchanged.
      have himage : (S.erase k).image α = (S.erase k').image α := by
        ext w
        simp only [mem_image, mem_erase]
        constructor
        · rintro ⟨s, ⟨hsk, hsS⟩, rfl⟩
          by_cases hsk' : s = k'
          · exact ⟨k, ⟨hkk'.ne, hkS⟩, hsk' ▸ hk⟩
          · exact ⟨s, ⟨hsk', hsS⟩, rfl⟩
        · rintro ⟨s, ⟨hsk', hsS⟩, rfl⟩
          by_cases hsk : s = k
          · exact ⟨k', ⟨hkk'.ne', hk'S⟩, hsk ▸ hk.symm⟩
          · exact ⟨s, ⟨hsk, hsS⟩, rfl⟩
      have hkU : k ∉ insert i (insert j (S.erase k)) := by
        simp only [mem_insert, mem_erase, not_or, not_and]
        exact ⟨(h.mem hkS).1.ne', (h.mem hkS).2.ne, fun e ↦ absurd rfl e⟩
      have hk'U : k' ∉ insert i (insert j (S.erase k')) := by
        simp only [mem_insert, mem_erase, not_or, not_and]
        exact ⟨(h.mem hk'S).1.ne', (h.mem hk'S).2.ne, fun e ↦ absurd rfl e⟩
      rw [boundaryTerm_of_mem _ h hkS, boundaryTerm_of_mem _ h hk'S,
        compTerm_eq_zero_of_right _ _ _ _ (hzero (h.upper hkS) (mem_insert_self _ _)
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hk'S, hkk'⟩)))
          ⟨k', mem_filter.mpr ⟨hk'S, hkk'⟩⟩),
        compTerm_eq_zero_of_left _ _ _ _ (hzero (h.lower hk'S)
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hkS, hkk'⟩)))
          (mem_insert_of_mem (mem_insert_self _ _)) ⟨k, mem_filter.mpr ⟨hkS, hkk'⟩⟩),
        sub_zero, sub_zero, pullback_coh_of_injOn x α _ (hinjOf (Or.inl hkU)),
        pullback_coh_of_injOn x α _ (hinjOf (Or.inr hk'U)),
        x.coh_congr himage _
          ((h.erase hk'S).image α.monotone (hinjOf (Or.inr hk'U))),
        hcard, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.neg_smul, neg_add_cancel]
    · rw [boundaryTerm_of_mem _ h hc,
        hzero (h.erase hc) (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hck.1.symm, hkS⟩)))
          (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hck.2.symm, hk'S⟩)))
          ⟨k, mem_erase.mpr ⟨hck.1.symm, hkS⟩⟩]
      rcases hS_out c hc hck.1 hck.2 with hlt | hgt
      · rw [compTerm_eq_zero_of_right _ _ _ _ (hzero (h.upper hc)
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hkS, hlt⟩)))
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hk'S, hlt.trans hkk'⟩)))
          ⟨k, mem_filter.mpr ⟨hkS, hlt⟩⟩), sub_zero, smul_zero]
      · rw [compTerm_eq_zero_of_left _ _ _ _ (hzero (h.lower hc)
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hkS, hkk'.trans hgt⟩)))
          (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨hk'S, hgt⟩)))
          ⟨k, mem_filter.mpr ⟨hkS, hkk'.trans hgt⟩⟩), sub_zero, smul_zero]

end Family

/-- A degeneracy map of `SimplexCategory` identifies exactly the two vertices `i` and `i + 1`. -/
private theorem predAbove_eq_predAbove {n : ℕ} (i : Fin (n + 1)) {a b : Fin (n + 2)} (hab : a < b)
    (h : i.predAbove a = i.predAbove b) : a = i.castSucc ∧ b = i.succ := by
  simp only [Fin.predAbove, Fin.ext_iff, Fin.lt_def] at h hab ⊢
  split_ifs at h with h₁ h₂ h₂ <;>
    simp only [Fin.val_pred, Fin.coe_castPred, Fin.val_castSucc] at h h₁ h₂ <;>
    simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

/-- **Monotone maps preserve the dg nerve equations**: the pullback of a coherent family along a
map of `SimplexCategory` is coherent.  A non-injective map factors through a degeneracy, which
collapses a single pair of adjacent vertices. -/
theorem Family.IsCoherent.pullback {n : ℕ} {x : Family R C (Fin (n + 1))} (hx : x.IsCoherent)
    {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : (x.pullback θ.toOrderHom).IsCoherent := by
  induction m with
  | zero => exact hx.pullback_of_injective fun a b _ ↦ Subsingleton.elim (α := Fin 1) a b
  | succ m ih =>
    by_cases hθ : Function.Injective θ.toOrderHom
    · exact hx.pullback_of_injective hθ
    obtain ⟨i, θ', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hθ
    rw [SimplexCategory.comp_toOrderHom, ← Family.pullback_pullback]
    exact fun _ _ _ _ h ↦ (ih θ').pullback_apply_of_collapse _ Fin.castSucc_lt_succ
      (by simp [SimplexCategory.σ]) (fun a b hab e ↦ predAbove_eq_predAbove i hab e) h

end DGNerve

open DGNerve

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- **The differential graded nerve** `N_dg(C)` of a differential graded category `C` (Lurie,
*Higher Algebra*, Construction 1.3.1.6): its `n`-simplices are the families of objects and
coherences indexed by `Fin (n + 1)` satisfying the dg nerve equations, and a map of
`SimplexCategory` acts by `TauCeti.DGNerve.Family.pullback`. -/
noncomputable abbrev dgNerve : SSet.{max u v} where
  obj Δ := {x : Family R C (Fin (Δ.unop.len + 1)) // x.IsCoherent}
  map θ := ↾fun x ↦ ⟨x.1.pullback θ.unop.toOrderHom, x.2.pullback θ.unop⟩
  map_id Δ := by
    ext x : 3
    exact Subtype.ext x.1.pullback_id
  map_comp θ θ' := by
    ext x : 3
    exact Subtype.ext (x.1.pullback_pullback _ _).symm

variable {R C}

/-- The face and degeneracy operators of the dg nerve act by pulling back families. -/
@[simp]
theorem dgNerve_map_val {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') (x : (dgNerve R C).obj Δ) :
    ((dgNerve R C).map θ x).1 = x.1.pullback θ.unop.toOrderHom :=
  (rfl)

/-! ### Vertices, edges and degenerate simplices -/

/-- **The vertices of the dg nerve are the objects** of the dg category. -/
noncomputable def dgNerveVerticesEquiv (R : Type v) [CommRing R] (C : Type u) [DGCategory R C] :
    (dgNerve R C) _⦋0⦌ ≃ C where
  toFun x := x.1.obj 0
  invFun X := ⟨⟨fun _ ↦ X, fun i j _ _ h ↦ absurd h.lt (Subsingleton.elim (α := Fin 1) i j).not_lt⟩,
    fun i j _ _ h ↦ absurd h.lt (Subsingleton.elim (α := Fin 1) i j).not_lt⟩
  left_inv x := by
    refine Subtype.ext (Family.ext (funext fun a ↦ ?_) fun i j _ _ h ↦
      absurd h.lt (Subsingleton.elim (α := Fin 1) i j).not_lt)
    rw [Subsingleton.elim (α := Fin 1) a 0]
  right_inv _ := rfl

@[simp]
theorem dgNerveVerticesEquiv_apply (x : (dgNerve R C) _⦋0⦌) :
    dgNerveVerticesEquiv R C x = x.1.obj 0 :=
  (rfl)

@[simp]
theorem dgNerveVerticesEquiv_symm_apply_obj (X : C) (a : Fin 1) :
    ((dgNerveVerticesEquiv R C).symm X).1.obj a = X :=
  (rfl)

/-- The only index of a `1`-simplex is the edge from `0` to `1`. -/
theorem isIndex_fin_two {i j : Fin 2} {S : Finset (Fin 2)} {m : ℤ} (h : IsIndex i j S m) :
    i = 0 ∧ j = 1 ∧ S = ∅ ∧ m = 0 := by
  have hij := h.lt
  have hi : i = 0 := by omega
  have hj : j = 1 := by omega
  have hS : S = ∅ := eq_empty_of_forall_notMem fun v hv ↦ by
    have := h.mem hv
    omega
  exact ⟨hi, hj, hS, by rw [h.degree, hS, card_empty, Nat.cast_zero, neg_zero]⟩

/-- The family of a `1`-simplex with edge `f : X ⟶ Y`. -/
private noncomputable def edgeFamily {X Y : C} (f : DGHom R 0 X Y) : Family R C (Fin 2) where
  obj := ![X, Y]
  coh i j S m h := by
    obtain ⟨rfl, rfl, -, rfl⟩ := isIndex_fin_two h
    exact f

private theorem edgeFamily_coh {X Y : C} (f : DGHom R 0 X Y) (h : IsIndex (0 : Fin 2) 1 ∅ 0) :
    (edgeFamily f).coh 0 1 ∅ 0 h = f :=
  rfl

private theorem edgeFamily_coh_eq (y : Family R C (Fin 2)) (h : IsIndex (0 : Fin 2) 1 ∅ 0) :
    edgeFamily (y.coh 0 1 ∅ 0 h) = y := by
  refine Family.ext (funext fun a ↦ ?_) fun i j S m h ↦ ?_
  · fin_cases a <;> rfl
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := isIndex_fin_two h
    exact heq_of_eq (edgeFamily_coh _ h)

/-- **The edges of the dg nerve are the closed degree-zero morphisms**: an edge `X ⟶ Y` is a
degree-zero cocycle of `Hom(X, Y)`. -/
noncomputable def dgNerveEdgesEquiv (R : Type v) [CommRing R] (C : Type u) [DGCategory R C] :
    (dgNerve R C) _⦋1⦌ ≃ Σ X Y : C, dgCycles R X Y where
  toFun x := ⟨x.1.obj 0, x.1.obj 1, ⟨x.1.coh 0 1 ∅ 0 (isIndex_empty_iff.mpr ⟨by simp, rfl⟩), by
    rw [mem_dgCycles, x.2, Family.boundary_def, sum_empty]⟩⟩
  invFun f := ⟨edgeFamily f.2.2.1, fun i j S m h ↦ by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := isIndex_fin_two h
    rw [Family.boundary_def, sum_empty]
    exact (mem_dgCycles R).mp f.2.2.2⟩
  left_inv x := Subtype.ext (edgeFamily_coh_eq x.1 _)
  right_inv _ := rfl

@[simp]
theorem dgNerveEdgesEquiv_apply (x : (dgNerve R C) _⦋1⦌) :
    dgNerveEdgesEquiv R C x = ⟨x.1.obj 0, x.1.obj 1,
      ⟨x.1.coh 0 1 ∅ 0 (isIndex_empty_iff.mpr ⟨by simp, rfl⟩), by
        rw [mem_dgCycles, x.2, Family.boundary_def, sum_empty]⟩⟩ :=
  (rfl)

/-- **The degeneracy of a vertex is its identity**: the degenerate edge at an object `X` is the
identity of `X`, not zero. -/
theorem dgNerveEdgesEquiv_σ_dgNerveVerticesEquiv_symm (X : C) :
    dgNerveEdgesEquiv R C ((dgNerve R C).σ 0 ((dgNerveVerticesEquiv R C).symm X)) =
      ⟨X, X, ⟨dgId R X, by rw [mem_dgCycles, dgDifferential_dgId]⟩⟩ := by
  rw [dgNerveEdgesEquiv_apply]
  refine Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))))
  dsimp only
  refine (Family.pullback_coh_of_eq ((dgNerveVerticesEquiv R C).symm X).1
    (SimplexCategory.σ 0).toOrderHom _ (Subsingleton.elim (α := Fin 1) _ _)).trans ?_
  exact idOfEq_rfl (fun _ : Fin 1 ↦ X) 0

/-- **A `2`-simplex records a homotopy**: the coherence `η` of a `2`-simplex with edges
`f : X₀ ⟶ X₁`, `g : X₁ ⟶ X₂` and `h : X₀ ⟶ X₂` is a morphism of degree `-1` with
`d η = g ∘ f - h`. -/
theorem dgNerve_d_coh_two (x : (dgNerve R C) _⦋2⦌) :
    dgDifferential R (-1) (x.1.coh 0 2 {1} (-1) (by simp [IsIndex])) =
      dgComp R (x.1.coh 0 1 ∅ 0 (isIndex_empty_iff.mpr ⟨by simp, rfl⟩))
          (x.1.coh 1 2 ∅ 0 (isIndex_empty_iff.mpr ⟨by simp, rfl⟩)) (by norm_num) -
        x.1.coh 0 2 ∅ (-1 + 1) (isIndex_empty_iff.mpr ⟨by simp, by norm_num⟩) := by
  rw [x.2, Family.boundary_def, sum_singleton,
    Family.boundaryTerm_of_mem _ _ (mem_singleton_self 1),
    x.1.compTerm_congr (A' := ∅) (B' := ∅) (by simp) (by simp) _ _ _
      (isIndex_empty_iff.mpr ⟨by simp, rfl⟩) (isIndex_empty_iff.mpr ⟨by simp, rfl⟩)
      (by norm_num),
    Family.compTerm_def, x.1.coh_congr (S' := ∅) (by simp) _
      (isIndex_empty_iff.mpr ⟨by simp, by norm_num⟩)]
  have : #({w ∈ ({1} : Finset (Fin 3)) | 1 < w}) = 0 := by simp
  rw [this, Nat.cast_zero, zero_add, Int.negOnePow_one, mul_zero, Int.negOnePow_zero, one_smul,
    Units.neg_smul, one_smul, neg_sub]

end TauCeti
