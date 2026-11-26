/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.Data.Finset.Sort

/-!
# The category of finite pointed sets

The category `FinPointed` has one object `⟨n⟩` for each natural number `n`, standing for the
pointed set `Fin (n + 1)` with basepoint `0`, and its morphisms are the pointed maps. Through the
fully faithful functor `FinPointed.toPointed` it is a skeleton of the full subcategory of
`Pointed` spanned by the finite pointed types (`Pointed.exists_iso_finPointed`): this is the
category `Fin_*` over whose nerve symmetric monoidal quasicategories are coCartesian
fibrations.

A pointed map `f : ⟨m⟩ ⟶ ⟨n⟩` is *inert* when every element of `⟨n⟩` other than the basepoint has
exactly one preimage, and *active* when only the basepoint is sent to the basepoint. Every map
factors as an inert map followed by an active map: the inert map collapses the elements which
`f` sends to the basepoint, and the active map is `f` on the remaining ones. For each
`1 ≤ i ≤ n` the inert projection `ρ i : ⟨n⟩ ⟶ ⟨1⟩` sends `i` to `1` and everything else to the
basepoint; these are the maps along which the Segal condition is stated. The fold map
`fold n : ⟨n⟩ ⟶ ⟨1⟩` sending every element other than the basepoint to `1` is the unique active
map to `⟨1⟩`; the multi-operations of an `∞`-operad lie over it. The fibers of a map over the
elements other than the basepoint, listed in increasing order, index the ordered tensor products
in the category of operators of a symmetric monoidal category; the fibers of a composite are, up
to order, the concatenations of fibers.

## Main definitions

* `TauCeti.FinPointed`: the category of the pointed sets `⟨n⟩ = Fin (n + 1)`.
* `TauCeti.FinPointed.toPointed`: its fully faithful functor to `Pointed`.
* `TauCeti.FinPointed.inert`, `TauCeti.FinPointed.active`: the inert and the active maps, both
  closed under composition.
* `TauCeti.FinPointed.Hom.fiber f j`: the fiber of `f` over an element other than the
  basepoint, as an increasing list.
* `TauCeti.FinPointed.ρ i`: the inert projection `⟨n⟩ ⟶ ⟨1⟩` at `i`.
* `TauCeti.FinPointed.fold n`: the fold map `⟨n⟩ ⟶ ⟨1⟩`.
* `TauCeti.FinPointed.inertActiveFactorizationData`: the factorization of a map as an inert map
  followed by an active map.

## Main results

* `CategoryTheory.Pointed.exists_iso_finPointed`: every finite pointed type is isomorphic to some
  `⟨n⟩`.
* `TauCeti.FinPointed.perm_fiber_comp`: the fiber of a composite `f ≫ g` is, up to order, the
  concatenation of the fibers of `f` over the fiber of `g`.
* `TauCeti.FinPointed.isInert_ρ`: the projections `ρ i` are inert.
* `TauCeti.FinPointed.isActive_fold`, `TauCeti.FinPointed.eq_fold_of_isActive`: the fold map is
  the unique active map `⟨n⟩ ⟶ ⟨1⟩`.

## References

* J. Lurie, *Higher Algebra*, Notation 2.0.0.2, Definition 2.1.1.8 and Remark 2.1.2.2.
-/

public section

universe u

open CategoryTheory

namespace TauCeti

/-- The category `Fin_*` of finite pointed sets: an object `⟨n⟩` is a natural number `n`,
standing for the pointed set `Fin (n + 1)` with basepoint `0`. It lives in an arbitrary universe,
so that its nerve is a simplicial set in that universe. -/
@[ext]
structure FinPointed : Type u where
  /-- The object `⟨n⟩` standing for the pointed set `Fin (n + 1)`. -/
  mk ::
  /-- The number of elements of the pointed set other than its basepoint. -/
  len : ℕ

namespace FinPointed

@[simp]
lemma mk_len (n : FinPointed.{u}) : mk n.len = n := rfl

/-- A morphism of `FinPointed` is a map of the underlying finite sets preserving the
basepoint `0`. -/
@[ext]
structure Hom (m n : FinPointed.{u}) : Type u where
  /-- The morphism given by a pointed map of the underlying finite sets. -/
  mk ::
  /-- The underlying map of finite sets. -/
  toFun : Fin (m.len + 1) → Fin (n.len + 1)
  map_zero : toFun 0 = 0

attribute [simp] Hom.map_zero

instance : SmallCategory FinPointed.{u} where
  Hom := Hom
  id _ := ⟨id, rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, by simp⟩

variable {m n k : FinPointed.{u}}

@[ext]
lemma hom_ext {f g : m ⟶ n} (h : ∀ i, f.toFun i = g.toFun i) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_toFun (i : Fin (n.len + 1)) : Hom.toFun (𝟙 n) i = i := rfl

@[simp]
lemma comp_toFun (f : m ⟶ n) (g : n ⟶ k) (i : Fin (m.len + 1)) :
    (f ≫ g).toFun i = g.toFun (f.toFun i) := rfl

/-! ### The comparison with pointed types -/

/-- The functor from `FinPointed` to pointed types, sending `⟨n⟩` to `Fin (n + 1)` pointed at
`0`, lifted to the universe `u`. The body is exposed so that the underlying type of
`toPointed.obj n` is visibly `ULift (Fin (n.len + 1))`. -/
@[expose, simps]
def toPointed : FinPointed.{u} ⥤ Pointed.{u} where
  obj n := Pointed.of (ULift.up 0 : ULift.{u} (Fin (n.len + 1)))
  map f := ⟨ULift.map f.toFun, by simp [ULift.map]⟩

/-- The functor `FinPointed.toPointed` is fully faithful: pointed maps of the underlying pointed
types are the morphisms of `FinPointed`. -/
def fullyFaithfulToPointed : toPointed.{u}.FullyFaithful where
  preimage f := ⟨fun i ↦ (f.toFun ⟨i⟩).down, congrArg ULift.down f.map_point⟩

instance : toPointed.{u}.Full := fullyFaithfulToPointed.full

instance : toPointed.{u}.Faithful := fullyFaithfulToPointed.faithful

/-! ### Fibers -/

/-- The fiber of `f : ⟨m⟩ ⟶ ⟨n⟩` over the element `j.succ` of `⟨n⟩` other than the basepoint:
the list, in increasing order, of the `i : Fin m.len` with `f (i.succ) = j.succ`. Here the elements
of `⟨m⟩` other than the basepoint are numbered `i.succ` by `i : Fin m.len`. -/
def Hom.fiber (f : m ⟶ n) (j : Fin n.len) : List (Fin m.len) :=
  (List.finRange m.len).filter fun i ↦ f.toFun i.succ = j.succ

@[simp]
lemma Hom.mem_fiber {f : m ⟶ n} {j : Fin n.len} {i : Fin m.len} :
    i ∈ f.fiber j ↔ f.toFun i.succ = j.succ := by
  simp [Hom.fiber]

lemma Hom.nodup_fiber (f : m ⟶ n) (j : Fin n.len) : (f.fiber j).Nodup :=
  (List.nodup_finRange _).filter _

/-- The fibers of a map over distinct elements are disjoint. -/
lemma Hom.disjoint_fiber (f : m ⟶ n) {j j' : Fin n.len} (h : j ≠ j') :
    (f.fiber j).Disjoint (f.fiber j') := fun _ hi hi' ↦
  h (Fin.succ_injective _ ((mem_fiber.1 hi).symm.trans (mem_fiber.1 hi')))

/-- The fibers of the identity are the singletons. -/
@[simp]
lemma fiber_id (j : Fin n.len) : Hom.fiber (𝟙 n) j = [j] :=
  List.perm_singleton.1 <| (List.perm_ext_iff_of_nodup (Hom.nodup_fiber _ _)
    (List.nodup_singleton j)).2 fun i ↦ by simp

/-- The fiber of a composite `f ≫ g` over `l` is, up to order, the concatenation of the fibers of
`f` over the elements of the fiber of `g` over `l`. -/
lemma perm_fiber_comp (f : m ⟶ n) (g : n ⟶ k) (l : Fin k.len) :
    ((f ≫ g).fiber l).Perm ((g.fiber l).flatMap f.fiber) := by
  refine (List.perm_ext_iff_of_nodup (Hom.nodup_fiber _ _) (List.nodup_flatMap.2
    ⟨fun j _ ↦ Hom.nodup_fiber f j, (Hom.nodup_fiber g l).pairwise_of_forall_ne
      fun j _ j' _ h ↦ Hom.disjoint_fiber f h⟩)).2 fun i ↦ ?_
  simp only [Hom.mem_fiber, comp_toFun, List.mem_flatMap]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 fun h' : f.toFun i.succ = 0 ↦
      Fin.succ_ne_zero l (by simp [← h, h'])
    exact ⟨j, by rw [hj, h], hj.symm⟩
  · rintro ⟨j, hj, hi⟩
    rw [hi, hj]

/-! ### Inert and active maps -/

/-- A map `f : ⟨m⟩ ⟶ ⟨n⟩` is inert when every element of `⟨n⟩` other than the basepoint has
exactly one preimage. -/
def Hom.IsInert (f : m ⟶ n) : Prop :=
  ∀ j : Fin (n.len + 1), j ≠ 0 → ∃! i, f.toFun i = j

/-- A map `f : ⟨m⟩ ⟶ ⟨n⟩` is active when only the basepoint is sent to the basepoint. -/
def Hom.IsActive (f : m ⟶ n) : Prop :=
  ∀ i : Fin (m.len + 1), f.toFun i = 0 → i = 0

lemma Hom.isInert_iff (f : m ⟶ n) :
    f.IsInert ↔ ∀ j : Fin (n.len + 1), j ≠ 0 → ∃! i, f.toFun i = j :=
  Iff.rfl

lemma Hom.isActive_iff (f : m ⟶ n) :
    f.IsActive ↔ ∀ i : Fin (m.len + 1), f.toFun i = 0 → i = 0 :=
  Iff.rfl

/-- The inert maps of `FinPointed`. -/
def inert : MorphismProperty FinPointed.{u} := fun _ _ f ↦ f.IsInert

/-- The active maps of `FinPointed`. -/
def active : MorphismProperty FinPointed.{u} := fun _ _ f ↦ f.IsActive

@[simp]
lemma inert_iff (f : m ⟶ n) : inert f ↔ f.IsInert := Iff.rfl

@[simp]
lemma active_iff (f : m ⟶ n) : active f ↔ f.IsActive := Iff.rfl

instance : inert.{u}.IsMultiplicative where
  id_mem n j _ := ⟨j, rfl, fun _ h ↦ h⟩
  comp_mem f g hf hg k hk := by
    obtain ⟨j, hj, hj'⟩ := hg k hk
    obtain ⟨i, hi, hi'⟩ := hf j (by rintro rfl; exact hk (by simpa using hj.symm))
    exact ⟨i, by simp [hi, hj], fun i' h ↦ hi' i' (hj' _ h)⟩

instance : active.{u}.IsMultiplicative where
  id_mem _ _ h := h
  comp_mem _ _ hf hg i h := hf i (hg _ h)

/-- The inert projection `ρ i : ⟨n⟩ ⟶ ⟨1⟩` at `1 ≤ i + 1 ≤ n`: it sends `i + 1` to `1` and every
other element to the basepoint. -/
def ρ (i : Fin n.len) : n ⟶ mk 1 :=
  ⟨fun j ↦ if j = i.succ then 1 else 0, by simp [(Fin.succ_ne_zero i).symm]⟩

lemma ρ_toFun (i : Fin n.len) (j : Fin (n.len + 1)) :
    (ρ i).toFun j = if j = i.succ then 1 else 0 :=
  (rfl)

@[simp]
lemma ρ_toFun_self (i : Fin n.len) : (ρ i).toFun i.succ = 1 := by simp [ρ_toFun]

/-- The projection `ρ i` is inert. -/
lemma isInert_ρ (i : Fin n.len) : (ρ i).IsInert := by
  intro j hj
  obtain rfl := Fin.eq_one_of_ne_zero j hj
  refine ⟨i.succ, by simp, fun i' h ↦ ?_⟩
  by_contra h'
  simp [ρ_toFun, h'] at h

/-- The fold map `⟨n⟩ ⟶ ⟨1⟩`, sending every element other than the basepoint to `1`. It is the
unique active map to `⟨1⟩` (`FinPointed.eq_fold_of_isActive`); multi-operations of an
`∞`-operad lie over it. -/
def fold (n : FinPointed.{u}) : n ⟶ mk 1 :=
  ⟨fun j ↦ if j = 0 then 0 else 1, by simp⟩

lemma fold_toFun (j : Fin (n.len + 1)) : (fold n).toFun j = if j = 0 then 0 else 1 :=
  (rfl)

/-- The fold map is active. -/
lemma isActive_fold (n : FinPointed.{u}) : (fold n).IsActive := by
  intro j hj
  by_contra h
  simp [fold_toFun, h] at hj

/-- The fold map is the only active map `⟨n⟩ ⟶ ⟨1⟩`. -/
lemma eq_fold_of_isActive (f : n ⟶ mk 1) (hf : f.IsActive) : f = fold n := by
  ext j
  rw [fold_toFun]
  split_ifs with h
  · rw [h, Hom.map_zero]
  · obtain h' | h' := Fin.eq_zero_or_eq_succ (f.toFun j)
    · exact absurd (hf j h') h
    · obtain ⟨k, hk⟩ := h'
      rw [hk, Fin.fin_one_eq_zero k]
      rfl

/-! ### The inert-active factorization -/

section factorization

variable (f : m ⟶ n)

/-- The elements of `⟨m⟩` which `f` does not send to the basepoint. -/
private abbrev support : Finset (Fin (m.len + 1)) := {i | f.toFun i ≠ 0}

/-- The inert part `⟨m⟩ ⟶ ⟨k⟩` of `f`, where `k` is the number of elements not sent to the
basepoint: it numbers these elements in increasing order and collapses the others. -/
private def inertPart : m ⟶ mk (support f).card :=
  ⟨fun i ↦ if h : i ∈ support f then (((support f).orderIsoOfFin rfl).symm ⟨i, h⟩).succ else 0,
    by simp⟩

/-- The active part `⟨k⟩ ⟶ ⟨n⟩` of `f`: it is `f` on the elements not sent to the basepoint. -/
private def activePart : mk (support f).card ⟶ n :=
  ⟨fun j ↦ Fin.cases 0 (fun j ↦ f.toFun ((support f).orderEmbOfFin rfl j)) j, rfl⟩

private lemma inertPart_toFun_of_mem {i : Fin (m.len + 1)} (h : i ∈ support f) :
    (inertPart f).toFun i = (((support f).orderIsoOfFin rfl).symm ⟨i, h⟩).succ :=
  dite_eq_left_of_eq_true (eq_true h)

private lemma inertPart_toFun_of_notMem {i : Fin (m.len + 1)} (h : i ∉ support f) :
    (inertPart f).toFun i = 0 :=
  dite_eq_right_of_eq_false (eq_false h)

private lemma isInert_inertPart : (inertPart f).IsInert := by
  intro j hj
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
  have hmem : (support f).orderEmbOfFin rfl j ∈ support f := Finset.orderEmbOfFin_mem _ _ _
  refine .intro ((support f).orderEmbOfFin rfl j) ?_ fun i hi ↦ ?_
  · rw [inertPart_toFun_of_mem f hmem, Fin.succ_inj, OrderIso.symm_apply_eq]
    exact Subtype.ext (Finset.coe_orderIsoOfFin_apply _ _ _).symm
  · have h : i ∈ support f := by
      by_contra h
      exact Fin.succ_ne_zero j (hi.symm.trans (inertPart_toFun_of_notMem f h))
    rw [inertPart_toFun_of_mem f h, Fin.succ_inj, OrderIso.symm_apply_eq] at hi
    rw [← Finset.coe_orderIsoOfFin_apply, ← hi]

private lemma isActive_activePart : (activePart f).IsActive := by
  intro j hj
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    have := Finset.orderEmbOfFin_mem (support f) rfl j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact absurd hj this

private lemma inertPart_comp_activePart : inertPart f ≫ activePart f = f := by
  ext i
  by_cases h : i ∈ support f
  · rw [comp_toFun, inertPart_toFun_of_mem f h]
    simp [activePart, ← Finset.coe_orderIsoOfFin_apply]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
    simp [inertPart, activePart, h]

end factorization

/-- Every map of `FinPointed` factors as an inert map followed by an active map. The middle
object is `⟨k⟩`, with `k` the number of elements not sent to the basepoint; the inert map numbers
these elements in increasing order, and the active map is the original map on them. -/
def inertActiveFactorizationData : MorphismProperty.FactorizationData inert.{u} active.{u} :=
  fun f ↦
  { Z := mk (support f).card
    i := inertPart f
    p := activePart f
    fac := inertPart_comp_activePart f
    hi := isInert_inertPart f
    hp := isActive_activePart f }

instance : MorphismProperty.HasFactorization inert.{u} active.{u} :=
  ⟨fun f ↦ ⟨inertActiveFactorizationData f⟩⟩

end FinPointed

end TauCeti

namespace CategoryTheory.Pointed

open TauCeti

/-- Every finite pointed type is isomorphic to `⟨n⟩` for some `n`: `FinPointed` is a skeleton of
the finite pointed types (through `TauCeti.FinPointed.toPointed`). -/
lemma exists_iso_finPointed (X : Pointed.{u}) [Finite X] :
    ∃ n : FinPointed.{u}, Nonempty (X ≅ FinPointed.toPointed.obj n) := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_add_one.2
    (Fin.pos_iff_nonempty.2 ⟨e X.point⟩)
  -- Compose `e` with the transposition exchanging `e X.point` and `0`.
  let e' : X ≃ ULift.{u} (Fin (n + 1)) := (e.trans (Equiv.swap (e X.point) 0)).trans
    Equiv.ulift.symm
  exact ⟨FinPointed.mk n, ⟨Pointed.Iso.mk e' (ULift.ext (Equiv.swap_apply_left _ _))⟩⟩

end CategoryTheory.Pointed
