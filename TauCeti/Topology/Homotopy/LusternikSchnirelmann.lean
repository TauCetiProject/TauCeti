/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Sets.Opens

/-!
# Lusternik–Schnirelmann categorical covers

An open subset `U` of a topological space `X` is *categorical* if its inclusion into `X` is
nullhomotopic. Only the inclusion has to contract inside `X`: `U` itself need not be
contractible. A categorical cover of `A ⊆ X` of size `n` is a family of `n` categorical open
subsets of `X` whose union contains `A` (`TauCeti.LSCategoricalCover`), and the unnormalized
Lusternik–Schnirelmann category `TauCeti.lsCategoryCount X A : ℕ∞` is the least size of such a
cover, or `⊤` if there is none. With this unnormalized convention the empty subset has count `0`
and a contractible space, such as a one-point space, has count `1` on `univ`.

The count is monotone in `A`, subadditive on finite unions, and does not increase under
deformations: if `g : X → X` is homotopic to the identity and maps `A` into `B`, then
`lsCategoryCount X A ≤ lsCategoryCount X B` (`TauCeti.lsCategoryCount_le_of_homotopic_id`). The
general form pulls covers back along any map with a left homotopy inverse
(`TauCeti.LSCategoricalCover.comap`); it gives homotopy invariance of the count of the whole
space and invariance under homeomorphisms. The deformation inequality is what bounds the
category by the number of critical points of a smooth function on a compact manifold: deforming a
sublevel down past a critical level along the gradient flow costs at most one categorical open per
critical point on that level.

## Main declarations

* `TauCeti.LSCategoricalCover X A n`: a cover of `A` by `n` open subsets of `X` with nullhomotopic
  inclusions, with restriction `mono`, concatenation `append`, padding by empty opens `pad`, and
  pullback `comap`.
* `TauCeti.lsCategoryCount X A`: the least size of a categorical cover of `A`, attained when
  finite (`TauCeti.nonempty_lsCategoricalCover_of_lsCategoryCount_eq`).
* `TauCeti.lsCategoryCount_le_iff`: `lsCategoryCount X A ≤ n` exactly when `A` has a categorical
  cover of size at most `n`, and `TauCeti.lsCategoryCount_lt_top_iff`: the count is finite exactly
  when `A` has a categorical cover.
* `TauCeti.lsCategoryCount_union_le` and `TauCeti.lsCategoryCount_biUnion_le`: subadditivity.
* `TauCeti.lsCategoryCount_le_of_homotopic_id`: the deformation inequality.
* `ContinuousMap.HomotopyEquiv.lsCategoryCount_univ_eq` and `Homeomorph.lsCategoryCount_image`:
  invariance under homotopy equivalences and homeomorphisms.
* `TauCeti.lsCategoryCount_eq_zero` and `TauCeti.lsCategoryCount_pos`: the count vanishes exactly
  on the empty set.
* `TauCeti.lsCategoryCount_univ_of_contractibleSpace` and
  `TauCeti.lsCategoryCount_eq_encard`: a contractible space has count `1`, and in a discrete space
  the count of a set is its cardinality.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
-/

public section

open Set ContinuousMap TopologicalSpace

namespace TauCeti

/-- A *categorical cover* of a subset `A` of a topological space `X` of size `n`: `n` open subsets
of `X` covering `A`, each of whose inclusions into `X` is nullhomotopic. The open sets themselves
need not be contractible. -/
@[ext]
structure LSCategoricalCover (X : Type*) [TopologicalSpace X] (A : Set X) (n : ℕ) where
  /-- The open sets of the cover. -/
  opens : Fin n → Opens X
  /-- The open sets of the cover contain `A`. -/
  subset_iUnion : A ⊆ ⋃ i, (opens i : Set X)
  /-- The inclusion of each open set of the cover into `X` is nullhomotopic. -/
  nullhomotopic : ∀ i, (subtypeVal (opens i : Set X)).Nullhomotopic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inclusion of a subset of a singleton is nullhomotopic, since it is constant. -/
theorem nullhomotopic_subtypeVal_of_subset_singleton {U : Set X} {x : X} (h : U ⊆ {x}) :
    (subtypeVal U).Nullhomotopic := by
  rw [show subtypeVal U = const U x from ContinuousMap.ext fun u ↦ h u.2]
  exact nullhomotopic_of_constant x

/-- In a discrete space a set with nullhomotopic inclusion has at most one point: under a
nullhomotopy of the inclusion, the track of a point is a path in a discrete space, hence constant.
-/
theorem exists_subset_singleton_of_nullhomotopic [DiscreteTopology X] {U : Set X}
    (h : (subtypeVal U).Nullhomotopic) : ∃ x, U ⊆ {x} := by
  obtain ⟨x, ⟨H⟩⟩ := h
  refine ⟨x, fun u hu ↦ ?_⟩
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace unitInterval)
    (f := fun t ↦ H (t, ⟨u, hu⟩)) (by fun_prop) (x := 0) (y := 1)
  simp only [Homotopy.apply_zero, Homotopy.apply_one, const_apply] at this
  rwa [subtypeVal_apply] at this

namespace LSCategoricalCover

variable {A B : Set X} {m n : ℕ}

/-- A categorical cover of `B` is a categorical cover of every subset of `B`. -/
def mono (c : LSCategoricalCover X B n) (h : A ⊆ B) : LSCategoricalCover X A n where
  opens := c.opens
  subset_iUnion := h.trans c.subset_iUnion
  nullhomotopic := c.nullhomotopic

@[simp]
theorem mono_opens (c : LSCategoricalCover X B n) (h : A ⊆ B) : (c.mono h).opens = c.opens :=
  (rfl)

/-- The empty cover of the empty set. -/
def empty : LSCategoricalCover X ∅ 0 where
  opens := Fin.elim0
  subset_iUnion := empty_subset _
  nullhomotopic i := i.elim0

/-- A set has a categorical cover of size `0` exactly when it is empty. -/
theorem nonempty_zero_iff : Nonempty (LSCategoricalCover X A 0) ↔ A = ∅ := by
  refine ⟨fun ⟨c⟩ ↦ ?_, fun h ↦ h ▸ ⟨empty⟩⟩
  simpa using c.subset_iUnion

/-- A single open set with nullhomotopic inclusion containing `A` is a categorical cover of `A` of
size `1`. -/
def single (U : Opens X) (hA : A ⊆ U) (hU : (subtypeVal (U : Set X)).Nullhomotopic) :
    LSCategoricalCover X A 1 where
  opens _ := U
  subset_iUnion := subset_iUnion_of_subset 0 hA
  nullhomotopic _ := hU

@[simp]
theorem single_opens (U : Opens X) (hA : A ⊆ U) (hU : (subtypeVal (U : Set X)).Nullhomotopic)
    (i : Fin 1) : (single U hA hU).opens i = U :=
  (rfl)

/-- The concatenation of categorical covers of `A` and `B` is a categorical cover of `A ∪ B`. -/
def append (c : LSCategoricalCover X A m) (d : LSCategoricalCover X B n) :
    LSCategoricalCover X (A ∪ B) (m + n) where
  opens := Fin.append c.opens d.opens
  subset_iUnion := by
    refine union_subset (c.subset_iUnion.trans <| iUnion_subset fun i ↦ ?_)
      (d.subset_iUnion.trans <| iUnion_subset fun i ↦ ?_)
    · exact subset_iUnion_of_subset (Fin.castAdd n i) (by simp)
    · exact subset_iUnion_of_subset (Fin.natAdd m i) (by simp)
  nullhomotopic := Fin.addCases (fun i ↦ by rw [Fin.append_left]; exact c.nullhomotopic i)
    (fun i ↦ by rw [Fin.append_right]; exact d.nullhomotopic i)

@[simp]
theorem append_opens (c : LSCategoricalCover X A m) (d : LSCategoricalCover X B n) :
    (c.append d).opens = Fin.append c.opens d.opens :=
  (rfl)

/-- On a nonempty space a categorical cover can be enlarged to any larger size by adding empty
open sets, whose inclusions are nullhomotopic. -/
def pad [Nonempty X] (c : LSCategoricalCover X A m) (h : m ≤ n) : LSCategoricalCover X A n where
  opens i := if hi : (i : ℕ) < m then c.opens ⟨i, hi⟩ else ⊥
  subset_iUnion := c.subset_iUnion.trans <| iUnion_subset fun i ↦
    subset_iUnion_of_subset (Fin.castLE h i) (by simp)
  nullhomotopic i := by
    -- The `if` occurs in the type of the inclusion, so split it after abstracting the open set.
    have key (U : Opens X) (hU : U = ⊥ ∨ ∃ j, U = c.opens j) :
        (subtypeVal (U : Set X)).Nullhomotopic := by
      obtain rfl | ⟨j, rfl⟩ := hU
      · exact nullhomotopic_subtypeVal_of_subset_singleton (x := Classical.arbitrary X) (by simp)
      · exact c.nullhomotopic j
    apply key
    split_ifs
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl

theorem pad_opens_of_lt [Nonempty X] (c : LSCategoricalCover X A m) (h : m ≤ n) {i : Fin n}
    (hi : (i : ℕ) < m) : (c.pad h).opens i = c.opens ⟨i, hi⟩ := by
  simp [pad, hi]

theorem pad_opens_of_le [Nonempty X] (c : LSCategoricalCover X A m) (h : m ≤ n) {i : Fin n}
    (hi : m ≤ (i : ℕ)) : (c.pad h).opens i = ⊥ := by
  simp [pad, hi.not_gt]

/-- Pullback of categorical covers. Let `g : Y → X` have a left homotopy inverse `r : X → Y`, so
that `r ∘ g` is homotopic to the identity of `Y`. If `g` maps `A ⊆ Y` into `B ⊆ X`, the preimages
under `g` of a categorical cover of `B` form a categorical cover of `A`. -/
def comap {A : Set Y} (c : LSCategoricalCover X B n) (g : C(Y, X)) (r : C(X, Y))
    (hrg : (r.comp g).Homotopic (ContinuousMap.id Y)) (hA : MapsTo g A B) :
    LSCategoricalCover Y A n where
  opens i := Opens.comap g (c.opens i)
  subset_iUnion := by
    intro y hy
    simpa using c.subset_iUnion (hA hy)
  nullhomotopic i := by
    -- The inclusion `j` of `g⁻¹(U)` is homotopic to `r ∘ g ∘ j`, which factors through the
    -- nullhomotopic inclusion of `U`.
    let gU : C(Opens.comap g (c.opens i), c.opens i) :=
      ⟨fun y ↦ ⟨g y, y.2⟩, by fun_prop⟩
    obtain ⟨x, hx⟩ := ((c.nullhomotopic i).comp_left gU).comp_right r
    have hj : r.comp ((subtypeVal _).comp gU) = (r.comp g).comp (subtypeVal _) :=
      ContinuousMap.ext fun _ ↦ rfl
    have := (hrg.symm.comp (.refl (subtypeVal (Opens.comap g (c.opens i) : Set Y)))).trans
      (hj ▸ hx)
    rw [ContinuousMap.id_comp] at this
    exact ⟨x, this⟩

@[simp]
theorem comap_opens {A : Set Y} (c : LSCategoricalCover X B n) (g : C(Y, X)) (r : C(X, Y))
    (hrg : (r.comp g).Homotopic (ContinuousMap.id Y)) (hA : MapsTo g A B) (i : Fin n) :
    (c.comap g r hrg hA).opens i = Opens.comap g (c.opens i) :=
  (rfl)

end LSCategoricalCover

variable (X) in
/-- The unnormalized *Lusternik–Schnirelmann category* of a subset `A` of `X`: the least size of a
categorical cover of `A`, or `⊤` if `A` has no finite categorical cover. The empty set has count
`0`, and a contractible space, such as a one-point space, has count `1` on `univ`. -/
noncomputable def lsCategoryCount (A : Set X) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : Nonempty (LSCategoricalCover X A n)), (n : ℕ∞)

variable {A B : Set X} {n : ℕ}

/-- A categorical cover of size `n` bounds the Lusternik–Schnirelmann count by `n`. -/
theorem LSCategoricalCover.lsCategoryCount_le (c : LSCategoricalCover X A n) :
    lsCategoryCount X A ≤ n :=
  iInf₂_le n ⟨c⟩

/-- A finite Lusternik–Schnirelmann count is attained by a categorical cover. -/
theorem nonempty_lsCategoricalCover_of_lsCategoryCount_eq (h : lsCategoryCount X A = n) :
    Nonempty (LSCategoricalCover X A n) := by
  rw [lsCategoryCount, iInf_subtype'] at h
  cases isEmpty_or_nonempty {k : ℕ // Nonempty (LSCategoricalCover X A k)} with
  | inl _ => simp at h
  | inr _ =>
    obtain ⟨⟨k, hk⟩, hk'⟩ := ENat.exists_eq_iInf fun k : {k // Nonempty (LSCategoricalCover X A k)}
      ↦ (k.1 : ℕ∞)
    rwa [← Nat.cast_inj.mp (hk'.trans h)]

/-- The Lusternik–Schnirelmann count of `A` is at most `n` exactly when `A` has a categorical
cover of size at most `n`. -/
theorem lsCategoryCount_le_iff :
    lsCategoryCount X A ≤ n ↔ ∃ m ≤ n, Nonempty (LSCategoricalCover X A m) := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm, ⟨c⟩⟩ ↦ c.lsCategoryCount_le.trans (by exact_mod_cast hm)⟩
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h.trans_lt (ENat.natCast_lt_top n)).ne
  exact ⟨m, by exact_mod_cast hm ▸ h, nonempty_lsCategoricalCover_of_lsCategoryCount_eq hm.symm⟩

/-- On a nonempty space, `A` has a categorical cover of size `n` exactly when its
Lusternik–Schnirelmann count is at most `n`. On an empty space only the size `0` occurs. -/
theorem nonempty_lsCategoricalCover_iff [Nonempty X] :
    Nonempty (LSCategoricalCover X A n) ↔ lsCategoryCount X A ≤ n := by
  refine ⟨fun ⟨c⟩ ↦ c.lsCategoryCount_le, fun h ↦ ?_⟩
  obtain ⟨m, hm, ⟨c⟩⟩ := lsCategoryCount_le_iff.mp h
  exact ⟨c.pad hm⟩

/-- The Lusternik–Schnirelmann count of `A` is finite exactly when `A` has a categorical cover. -/
theorem lsCategoryCount_lt_top_iff :
    lsCategoryCount X A < ⊤ ↔ ∃ n, Nonempty (LSCategoricalCover X A n) := by
  refine ⟨fun h ↦ ?_, fun ⟨n, ⟨c⟩⟩ ↦ c.lsCategoryCount_le.trans_lt (ENat.natCast_lt_top n)⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h.ne
  exact ⟨n, nonempty_lsCategoricalCover_of_lsCategoryCount_eq hn.symm⟩

/-- The Lusternik–Schnirelmann count of `A` is `⊤` exactly when `A` has no categorical cover. -/
theorem lsCategoryCount_eq_top_iff :
    lsCategoryCount X A = ⊤ ↔ ∀ n, IsEmpty (LSCategoricalCover X A n) := by
  simp only [← not_lt_top_iff, lsCategoryCount_lt_top_iff, not_exists, not_nonempty_iff]

/-- The Lusternik–Schnirelmann count is monotone in the subset. -/
theorem lsCategoryCount_mono (h : A ⊆ B) : lsCategoryCount X A ≤ lsCategoryCount X B :=
  le_iInf₂ fun _ ⟨c⟩ ↦ (c.mono h).lsCategoryCount_le

@[simp]
theorem lsCategoryCount_empty : lsCategoryCount X ∅ = 0 := by
  simpa using LSCategoricalCover.empty.lsCategoryCount_le (X := X)

/-- Only the empty set has Lusternik–Schnirelmann count `0`. -/
@[simp]
theorem lsCategoryCount_eq_zero : lsCategoryCount X A = 0 ↔ A = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ lsCategoryCount_empty⟩
  exact LSCategoricalCover.nonempty_zero_iff.mp
    (nonempty_lsCategoricalCover_of_lsCategoryCount_eq (n := 0) (by simpa using h))

/-- A nonempty set has positive Lusternik–Schnirelmann count. -/
theorem lsCategoryCount_pos : 0 < lsCategoryCount X A ↔ A.Nonempty := by
  rw [pos_iff_ne_zero, Ne, lsCategoryCount_eq_zero, nonempty_iff_ne_empty]

/-- Subadditivity of the Lusternik–Schnirelmann count on unions. -/
theorem lsCategoryCount_union_le :
    lsCategoryCount X (A ∪ B) ≤ lsCategoryCount X A + lsCategoryCount X B := by
  cases ha : lsCategoryCount X A with
  | top => simp
  | coe m =>
    cases hb : lsCategoryCount X B with
    | top => simp
    | coe n =>
      obtain ⟨c⟩ := nonempty_lsCategoricalCover_of_lsCategoryCount_eq ha
      obtain ⟨d⟩ := nonempty_lsCategoricalCover_of_lsCategoryCount_eq hb
      simpa using (c.append d).lsCategoryCount_le

/-- Subadditivity of the Lusternik–Schnirelmann count on finite unions. -/
theorem lsCategoryCount_biUnion_le {ι : Type*} (s : Finset ι) (A : ι → Set X) :
    lsCategoryCount X (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, lsCategoryCount X (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact lsCategoryCount_union_le.trans (add_le_add_right ih _)

/-- Pullback inequality for the Lusternik–Schnirelmann count. If `g : Y → X` has a left homotopy
inverse and maps `A` into `B`, then the count of `A` in `Y` is at most the count of `B` in `X`. -/
theorem lsCategoryCount_le_of_mapsTo {A : Set Y} (g : C(Y, X)) (r : C(X, Y))
    (hrg : (r.comp g).Homotopic (ContinuousMap.id Y)) (hA : MapsTo g A B) :
    lsCategoryCount Y A ≤ lsCategoryCount X B :=
  le_iInf₂ fun _ ⟨c⟩ ↦ (c.comap g r hrg hA).lsCategoryCount_le

/-- The deformation inequality: if `g : X → X` is homotopic to the identity and maps `A` into `B`,
then the Lusternik–Schnirelmann count of `A` is at most that of `B`. -/
theorem lsCategoryCount_le_of_homotopic_id (g : C(X, X))
    (hg : g.Homotopic (ContinuousMap.id X)) (hA : MapsTo g A B) :
    lsCategoryCount X A ≤ lsCategoryCount X B :=
  lsCategoryCount_le_of_mapsTo g (.id X) (by simpa using hg) hA

/-- In a contractible space every open set is categorical, so every subset has count at most `1`.
-/
theorem lsCategoryCount_le_one [ContractibleSpace X] (A : Set X) : lsCategoryCount X A ≤ 1 := by
  have h := (id_nullhomotopic X).comp_left (subtypeVal (⊤ : Opens X))
  rw [ContinuousMap.id_comp] at h
  simpa using (LSCategoricalCover.single (A := A) ⊤ (by simp) h).lsCategoryCount_le

/-- A contractible space, in particular a point, has Lusternik–Schnirelmann count `1`. -/
@[simp]
theorem lsCategoryCount_univ_of_contractibleSpace [ContractibleSpace X] :
    lsCategoryCount X univ = 1 :=
  le_antisymm (lsCategoryCount_le_one _) (Order.one_le_iff_pos.mpr (lsCategoryCount_pos.mpr
    univ_nonempty))

/-- In a discrete space the Lusternik–Schnirelmann count of a set is its cardinality: a categorical
open set has at most one point, and points are open. -/
@[simp]
theorem lsCategoryCount_eq_encard [DiscreteTopology X] (A : Set X) :
    lsCategoryCount X A = A.encard := by
  refine le_antisymm ?_ (le_iInf₂ fun n ⟨c⟩ ↦ ?_)
  · cases A.finite_or_infinite with
    | inr hA => simp [hA.encard_eq]
    | inl hA =>
      have hsingle (x : X) : lsCategoryCount X {x} ≤ 1 :=
        (LSCategoricalCover.single ⟨{x}, isOpen_discrete _⟩ subset_rfl
          (nullhomotopic_subtypeVal_of_subset_singleton (x := x) subset_rfl)).lsCategoryCount_le
      calc lsCategoryCount X A = lsCategoryCount X (⋃ x ∈ hA.toFinset, {x}) := by simp
        _ ≤ ∑ x ∈ hA.toFinset, lsCategoryCount X {x} := lsCategoryCount_biUnion_le _ _
        _ ≤ ∑ x ∈ hA.toFinset, 1 := Finset.sum_le_sum fun x _ ↦ hsingle x
        _ = A.encard := by simp [hA.encard_eq_coe_toFinset_card]
  · choose x hx using fun i ↦ exists_subset_singleton_of_nullhomotopic (c.nullhomotopic i)
    calc A.encard ≤ (range x).encard := encard_le_encard <| c.subset_iUnion.trans <|
          iUnion_subset fun i ↦ (hx i).trans <| singleton_subset_iff.mpr (mem_range_self i)
      _ ≤ (univ : Set (Fin n)).encard := by rw [← image_univ]; exact encard_image_le _ _
      _ = n := by simp

end TauCeti

/-- A homotopy equivalence preserves the Lusternik–Schnirelmann count of the whole space. -/
theorem ContinuousMap.HomotopyEquiv.lsCategoryCount_univ_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) :
    TauCeti.lsCategoryCount X univ = TauCeti.lsCategoryCount Y univ :=
  le_antisymm (TauCeti.lsCategoryCount_le_of_mapsTo e.toFun e.invFun e.left_inv (mapsTo_univ _ _))
    (TauCeti.lsCategoryCount_le_of_mapsTo e.invFun e.toFun e.right_inv (mapsTo_univ _ _))

/-- A homeomorphism preserves the Lusternik–Schnirelmann count of every subset. -/
@[simp]
theorem Homeomorph.lsCategoryCount_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) : TauCeti.lsCategoryCount Y (e '' A) = TauCeti.lsCategoryCount X A :=
  le_antisymm
    (TauCeti.lsCategoryCount_le_of_mapsTo (e.symm : C(Y, X)) e
      (e.toContinuousMap_comp_symm ▸ .refl _)
      (by rintro _ ⟨x, hx, rfl⟩; simpa using hx))
    (TauCeti.lsCategoryCount_le_of_mapsTo (e : C(X, Y)) e.symm
      (e.symm_comp_toContinuousMap ▸ .refl _) (mapsTo_image _ _))
