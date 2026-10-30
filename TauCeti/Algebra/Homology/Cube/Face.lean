/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import TauCeti.Algebra.Homology.Cube.Basic

/-!
# The faces of a cube at its first index and the mapping cone

A commutative cube `F : Finset (Fin (n + 1)) ⥤ C` splits along its first index `0` into two cubes
indexed by `Fin n`: the `0`-face `Functor.cubeZeroFace F`, made of the vertices `F(S)` with
`0 ∉ S`, and the `1`-face `Functor.cubeOneFace F`, made of the vertices `F(S ∪ {0})`. The edges
`F(S) ⟶ F(S ∪ {0})` form a map of cubes `Functor.cubeFaceMap F` from the `0`-face to the `1`-face.

The signed totalization of `F` is assembled from those of its two faces. An edge adding the first
index carries the sign `+1`, while an edge leaving a vertex of the `1`-face carries one sign more
than the corresponding edge of the `1`-face cube, since `0` lies below every other index. Hence
the `1`-face complex, shifted by `-1` so that its differential is negated, is a subcomplex of the
cube complex, with quotient the `0`-face complex: there is a short exact sequence of cochain
complexes `Functor.cubeComplexShortComplex F`

`0 ⟶ (cubeComplex F₁)⟦-1⟧ ⟶ cubeComplex F ⟶ cubeComplex F₀ ⟶ 0`,

split in each degree by the biproduct decomposition (`Functor.cubeComplexShortComplexSplitting`).
Its connecting morphism is the cochain map induced by the face map
(`Functor.homOfDegreewiseSplit_cubeComplexShortComplex`), so that the cube complex is the mapping
cone of the face map up to a shift (`Functor.cubeComplexMappingConeIso`). This identification
carries the sign `-1` on the summands of the `1`-face.

For the cube of resolutions of a link diagram whose first crossing is selected, the two faces are
the cubes of the two resolutions of that crossing, and this is the exact sequence of Khovanov
complexes attached to a crossing; another crossing is moved to the front by
`CategoryTheory.Functor.cubeComplexReindexIso`.

## Main definitions

* `CategoryTheory.Functor.cubeZeroFace F`, `CategoryTheory.Functor.cubeOneFace F`: the faces of
  the cube `F` at its first index, and `CategoryTheory.Functor.cubeFaceMap F` the map between them.
* `CategoryTheory.Functor.cubeComplexShortComplex F`: the short exact sequence of the faces.
* `CategoryTheory.Functor.cubeComplexMappingConeIso F`: the mapping cone of the face map is the
  shifted cube complex.

## Main results

* `CategoryTheory.Functor.cubeComplexZeroFaceι_d`, `CategoryTheory.Functor.cubeComplexOneFaceι_d`:
  the cube differential on the summands of the two faces.
* `CategoryTheory.Functor.cubeComplexShortComplex_shortExact`: the sequence is short exact.
* `CategoryTheory.Functor.homOfDegreewiseSplit_cubeComplexShortComplex`: its connecting morphism
  is induced by the face map.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002).
-/

public section

noncomputable section

open CategoryTheory Limits Finset HomologicalComplex CochainComplex

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Functor

/-! ### The faces at the first index -/

variable {n : ℕ}

private lemma zero_notMem_map_succEmb (S : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∉ S.map (Fin.succEmb n) := by
  simp [Fin.succ_ne_zero]

private lemma card_insert_zero_map_succEmb (S : Finset (Fin n)) :
    #(insert 0 (S.map (Fin.succEmb n))) = #S + 1 := by
  rw [card_insert_of_notMem (zero_notMem_map_succEmb S), card_map]

private lemma map_succEmb_ne_insert_zero (S T : Finset (Fin n)) :
    S.map (Fin.succEmb n) ≠ insert 0 (T.map (Fin.succEmb n)) := fun h ↦
  zero_notMem_map_succEmb S (h ▸ mem_insert_self _ _)

private lemma insert_zero_map_succEmb_inj {S T : Finset (Fin n)} :
    insert 0 (S.map (Fin.succEmb n)) = insert 0 (T.map (Fin.succEmb n)) ↔ S = T := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have := congrArg (fun U ↦ U.erase 0) h
  simpa [erase_insert (zero_notMem_map_succEmb _)] using this

private lemma map_succEmb_subset_insert_zero_iff {S T : Finset (Fin n)} :
    S.map (Fin.succEmb n) ⊆ insert 0 (T.map (Fin.succEmb n)) ↔ S ⊆ T := by
  rw [subset_insert_iff_of_notMem (zero_notMem_map_succEmb S), map_subset_map]

private lemma insert_zero_map_succEmb_subset_iff {S T : Finset (Fin n)} :
    insert 0 (S.map (Fin.succEmb n)) ⊆ insert 0 (T.map (Fin.succEmb n)) ↔ S ⊆ T := by
  rw [insert_subset_insert_iff (zero_notMem_map_succEmb S), map_subset_map]

private lemma not_insert_zero_map_succEmb_subset (S T : Finset (Fin n)) :
    ¬ insert 0 (S.map (Fin.succEmb n)) ⊆ T.map (Fin.succEmb n) := fun h ↦
  zero_notMem_map_succEmb T (h (mem_insert_self _ _))

/-- Every subset of `Fin (n + 1)` is the image of a subset of `Fin n` under `Fin.succ`, with or
without `0` adjoined. -/
private lemma exists_eq_map_succEmb_or (T : Finset (Fin (n + 1))) :
    ∃ S : Finset (Fin n),
      T = S.map (Fin.succEmb n) ∨ T = insert 0 (S.map (Fin.succEmb n)) := by
  refine ⟨univ.filter fun i : Fin n ↦ i.succ ∈ T, ?_⟩
  by_cases h : (0 : Fin (n + 1)) ∈ T
  · refine Or.inr (Finset.ext fun i ↦ ?_)
    cases i using Fin.cases <;> simp [h, Fin.succ_ne_zero]
  · refine Or.inl (Finset.ext fun i ↦ ?_)
    cases i using Fin.cases <;> simp [h, Fin.succ_ne_zero]

private lemma card_filter_lt_succ_map_succEmb (S : Finset (Fin n)) (b : Fin n) :
    #{c ∈ S.map (Fin.succEmb n) | c < b.succ} = #{c ∈ S | c < b} := by
  rw [filter_map, card_map]
  congr 1

private lemma card_filter_lt_succ_insert_zero_map_succEmb (S : Finset (Fin n)) (b : Fin n) :
    #{c ∈ insert 0 (S.map (Fin.succEmb n)) | c < b.succ} = #{c ∈ S | c < b} + 1 := by
  simp only [filter_insert, Fin.succ_pos, ↓reduceIte]
  rw [card_insert_of_notMem, card_filter_lt_succ_map_succEmb]
  exact fun h ↦ zero_notMem_map_succEmb S (mem_filter.1 h).1

private lemma map_succEmb_insert (S : Finset (Fin n)) (b : Fin n) :
    (insert b S).map (Fin.succEmb n) = insert b.succ (S.map (Fin.succEmb n)) := by
  simp [map_insert]

variable (F : Finset (Fin (n + 1)) ⥤ C)

/-- The `0`-face of a cube at its first index: the cube of the vertices `F(S)` with `0 ∉ S`,
indexed by the subsets of the remaining indices. It is reducible, so that its vertices are
those of `F` up to reducible unfolding. -/
abbrev cubeZeroFace : Finset (Fin n) ⥤ C where
  obj S := F.obj (S.map (Fin.succEmb n))
  map h := F.map (homOfLE (map_subset_map.2 (leOfHom h)))
  map_id _ := F.map_id _
  map_comp _ _ := by
    rw [← F.map_comp]
    rfl

/-- The `1`-face of a cube at its first index: the cube of the vertices `F(S ∪ {0})`, indexed by
the subsets of the remaining indices. It is reducible, so that its vertices are those of `F` up to
reducible unfolding. -/
abbrev cubeOneFace : Finset (Fin n) ⥤ C where
  obj S := F.obj (insert 0 (S.map (Fin.succEmb n)))
  map h := F.map (homOfLE (insert_subset_insert _ (map_subset_map.2 (leOfHom h))))
  map_id _ := F.map_id _
  map_comp _ _ := by
    rw [← F.map_comp]
    rfl

@[simp]
lemma cubeZeroFace_obj (S : Finset (Fin n)) :
    F.cubeZeroFace.obj S = F.obj (S.map (Fin.succEmb n)) :=
  rfl

@[simp]
lemma cubeZeroFace_map {S T : Finset (Fin n)} (h : S ⟶ T) :
    F.cubeZeroFace.map h = F.map (homOfLE (map_subset_map.2 (leOfHom h))) :=
  rfl

@[simp]
lemma cubeOneFace_obj (S : Finset (Fin n)) :
    F.cubeOneFace.obj S = F.obj (insert 0 (S.map (Fin.succEmb n))) :=
  rfl

@[simp]
lemma cubeOneFace_map {S T : Finset (Fin n)} (h : S ⟶ T) :
    F.cubeOneFace.map h =
      F.map (homOfLE (insert_subset_insert _ (map_subset_map.2 (leOfHom h)))) :=
  rfl

/-- The map from the `0`-face to the `1`-face of a cube at its first index, made of the edges
`F(S) ⟶ F(S ∪ {0})`. -/
def cubeFaceMap : F.cubeZeroFace ⟶ F.cubeOneFace where
  app S := F.map (homOfLE (subset_insert (0 : Fin (n + 1)) (S.map (Fin.succEmb n))))
  naturality S T h := by
    -- The maps of the two faces are maps of `F`, by definition of the reducible faces.
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    rfl

@[simp]
lemma cubeFaceMap_app (S : Finset (Fin n)) :
    F.cubeFaceMap.app S =
      F.map (homOfLE (subset_insert (0 : Fin (n + 1)) (S.map (Fin.succEmb n)))) :=
  (rfl)

/-! ### The summands of the faces -/

variable [Preadditive C] [HasFiniteBiproducts C]

/-- The inclusion of the summands of the `1`-face of degree `j` into the cube complex in degree
`j + 1`. -/
def cubeComplexOneFaceι {j r : ℤ} (h : j + 1 = r) :
    F.cubeOneFace.cubeComplex.X j ⟶ F.cubeComplex.X r :=
  F.cubeOneFace.cubeComplexDesc fun S ↦ F.cubeComplexι
    ⟨insert 0 (S.1.map (Fin.succEmb n)), by
      rw [card_insert_zero_map_succEmb, Nat.cast_succ, S.2, h]⟩

/-- The projection of the cube complex in degree `j + 1` onto the summands of the `1`-face. -/
def cubeComplexOneFaceπ {j r : ℤ} (h : j + 1 = r) :
    F.cubeComplex.X r ⟶ F.cubeOneFace.cubeComplex.X j :=
  F.cubeOneFace.cubeComplexLift fun S ↦ F.cubeComplexπ
    ⟨insert 0 (S.1.map (Fin.succEmb n)), by
      rw [card_insert_zero_map_succEmb, Nat.cast_succ, S.2, h]⟩

/-- The inclusion of the summands of the `0`-face into the cube complex. -/
def cubeComplexZeroFaceι (r : ℤ) : F.cubeZeroFace.cubeComplex.X r ⟶ F.cubeComplex.X r :=
  F.cubeZeroFace.cubeComplexDesc fun S ↦ F.cubeComplexι
    ⟨S.1.map (Fin.succEmb n), by rw [card_map]; exact S.2⟩

/-- The projection of the cube complex onto the summands of the `0`-face. -/
def cubeComplexZeroFaceπ (r : ℤ) : F.cubeComplex.X r ⟶ F.cubeZeroFace.cubeComplex.X r :=
  F.cubeZeroFace.cubeComplexLift fun S ↦ F.cubeComplexπ
    ⟨S.1.map (Fin.succEmb n), by rw [card_map]; exact S.2⟩

@[reassoc (attr := simp)]
lemma ι_cubeComplexOneFaceι {j r : ℤ} (h : j + 1 = r)
    (S : {S : Finset (Fin n) // (#S : ℤ) = j}) :
    F.cubeOneFace.cubeComplexι S ≫ F.cubeComplexOneFaceι h = F.cubeComplexι
      ⟨insert 0 (S.1.map (Fin.succEmb n)), by
        rw [card_insert_zero_map_succEmb, Nat.cast_succ, S.2, h]⟩ :=
  F.cubeOneFace.ι_cubeComplexDesc _ S

@[reassoc (attr := simp)]
lemma cubeComplexOneFaceπ_π {j r : ℤ} (h : j + 1 = r)
    (S : {S : Finset (Fin n) // (#S : ℤ) = j}) :
    F.cubeComplexOneFaceπ h ≫ F.cubeOneFace.cubeComplexπ S = F.cubeComplexπ
      ⟨insert 0 (S.1.map (Fin.succEmb n)), by
        rw [card_insert_zero_map_succEmb, Nat.cast_succ, S.2, h]⟩ :=
  F.cubeOneFace.cubeComplexLift_π _ S

@[reassoc (attr := simp)]
lemma ι_cubeComplexZeroFaceι {r : ℤ} (S : {S : Finset (Fin n) // (#S : ℤ) = r}) :
    F.cubeZeroFace.cubeComplexι S ≫ F.cubeComplexZeroFaceι r =
      F.cubeComplexι ⟨S.1.map (Fin.succEmb n), by rw [card_map]; exact S.2⟩ :=
  F.cubeZeroFace.ι_cubeComplexDesc _ S

@[reassoc (attr := simp)]
lemma cubeComplexZeroFaceπ_π {r : ℤ} (S : {S : Finset (Fin n) // (#S : ℤ) = r}) :
    F.cubeComplexZeroFaceπ r ≫ F.cubeZeroFace.cubeComplexπ S =
      F.cubeComplexπ ⟨S.1.map (Fin.succEmb n), by rw [card_map]; exact S.2⟩ :=
  F.cubeZeroFace.cubeComplexLift_π _ S

/-- The projection onto the `1`-face vanishes on the vertices of the `0`-face. -/
@[reassoc (attr := simp)]
lemma ι_map_cubeComplexOneFaceπ {j r : ℤ} (h : j + 1 = r) (S : Finset (Fin n))
    (hS : (#(S.map (Fin.succEmb n)) : ℤ) = r) :
    F.cubeComplexι ⟨S.map (Fin.succEmb n), hS⟩ ≫ F.cubeComplexOneFaceπ h = 0 := by
  ext T
  rw [Category.assoc, cubeComplexOneFaceπ_π, zero_comp]
  exact F.cubeComplexι_π_of_ne fun e ↦ map_succEmb_ne_insert_zero _ _ (congrArg Subtype.val e)

/-- The projection onto the `1`-face restricts to the identity on its vertices. -/
@[reassoc (attr := simp)]
lemma ι_insert_cubeComplexOneFaceπ {j r : ℤ} (h : j + 1 = r) (S : Finset (Fin n))
    (hS : (#(insert 0 (S.map (Fin.succEmb n))) : ℤ) = r) :
    F.cubeComplexι ⟨insert 0 (S.map (Fin.succEmb n)), hS⟩ ≫ F.cubeComplexOneFaceπ h =
      F.cubeOneFace.cubeComplexι ⟨S, by
        rw [card_insert_zero_map_succEmb, Nat.cast_succ] at hS; omega⟩ := by
  ext ⟨T, hT⟩
  rw [Category.assoc, cubeComplexOneFaceπ_π]
  by_cases hST : S = T
  · subst hST
    exact (F.cubeComplexι_π_self _).trans (F.cubeOneFace.cubeComplexι_π_self ⟨_, hT⟩).symm
  · have hS' : (#S : ℤ) = j := by rw [card_insert_zero_map_succEmb, Nat.cast_succ] at hS; omega
    exact (F.cubeComplexι_π_of_ne fun e ↦
      hST (insert_zero_map_succEmb_inj.1 (congrArg Subtype.val e))).trans
      (F.cubeOneFace.cubeComplexι_π_of_ne (S := ⟨S, hS'⟩) (T := ⟨T, hT⟩)
        fun e ↦ hST (congrArg Subtype.val e)).symm

/-- The projection onto the `0`-face vanishes on the vertices of the `1`-face. -/
@[reassoc (attr := simp)]
lemma ι_insert_cubeComplexZeroFaceπ {r : ℤ} (S : Finset (Fin n))
    (hS : (#(insert 0 (S.map (Fin.succEmb n))) : ℤ) = r) :
    F.cubeComplexι ⟨insert 0 (S.map (Fin.succEmb n)), hS⟩ ≫ F.cubeComplexZeroFaceπ r = 0 := by
  ext T
  rw [Category.assoc, cubeComplexZeroFaceπ_π, zero_comp]
  exact F.cubeComplexι_π_of_ne fun e ↦
    map_succEmb_ne_insert_zero _ _ (congrArg Subtype.val e).symm

/-- The projection onto the `0`-face restricts to the identity on its vertices. -/
@[reassoc (attr := simp)]
lemma ι_map_cubeComplexZeroFaceπ {r : ℤ} (S : Finset (Fin n))
    (hS : (#(S.map (Fin.succEmb n)) : ℤ) = r) :
    F.cubeComplexι ⟨S.map (Fin.succEmb n), hS⟩ ≫ F.cubeComplexZeroFaceπ r =
      F.cubeZeroFace.cubeComplexι ⟨S, by rwa [card_map] at hS⟩ := by
  ext ⟨T, hT⟩
  rw [Category.assoc, cubeComplexZeroFaceπ_π]
  by_cases hST : S = T
  · subst hST
    exact (F.cubeComplexι_π_self _).trans (F.cubeZeroFace.cubeComplexι_π_self ⟨_, hT⟩).symm
  · have hS' : (#S : ℤ) = r := by rwa [card_map] at hS
    exact (F.cubeComplexι_π_of_ne fun e ↦
      hST (map_inj.1 (congrArg Subtype.val e))).trans
      (F.cubeZeroFace.cubeComplexι_π_of_ne (S := ⟨S, hS'⟩) (T := ⟨T, hT⟩)
        fun e ↦ hST (congrArg Subtype.val e)).symm

/-- The inclusion of the `1`-face is orthogonal to the projection onto a vertex of the
`0`-face. -/
@[reassoc (attr := simp)]
lemma cubeComplexOneFaceι_π_map {j r : ℤ} (h : j + 1 = r) (S : Finset (Fin n))
    (hS : (#(S.map (Fin.succEmb n)) : ℤ) = r) :
    F.cubeComplexOneFaceι h ≫ F.cubeComplexπ ⟨S.map (Fin.succEmb n), hS⟩ = 0 := by
  ext T
  rw [ι_cubeComplexOneFaceι_assoc, comp_zero]
  exact F.cubeComplexι_π_of_ne fun e ↦
    map_succEmb_ne_insert_zero _ _ (congrArg Subtype.val e).symm

/-- The inclusion of the `1`-face followed by the projection onto one of its vertices. -/
@[reassoc (attr := simp)]
lemma cubeComplexOneFaceι_π_insert {j r : ℤ} (h : j + 1 = r) (S : Finset (Fin n))
    (hS : (#(insert 0 (S.map (Fin.succEmb n))) : ℤ) = r) :
    F.cubeComplexOneFaceι h ≫ F.cubeComplexπ ⟨insert 0 (S.map (Fin.succEmb n)), hS⟩ =
      F.cubeOneFace.cubeComplexπ ⟨S, by
        rw [card_insert_zero_map_succEmb, Nat.cast_succ] at hS; omega⟩ := by
  ext ⟨T, hT⟩
  rw [ι_cubeComplexOneFaceι_assoc]
  by_cases hST : T = S
  · subst hST
    exact (F.cubeComplexι_π_self _).trans (F.cubeOneFace.cubeComplexι_π_self ⟨_, hT⟩).symm
  · have hS' : (#S : ℤ) = j := by rw [card_insert_zero_map_succEmb, Nat.cast_succ] at hS; omega
    exact (F.cubeComplexι_π_of_ne fun e ↦
      hST (insert_zero_map_succEmb_inj.1 (congrArg Subtype.val e))).trans
      (F.cubeOneFace.cubeComplexι_π_of_ne (S := ⟨T, hT⟩) (T := ⟨S, hS'⟩)
        fun e ↦ hST (congrArg Subtype.val e)).symm

/-- The inclusion of the `0`-face is orthogonal to the projection onto a vertex of the
`1`-face. -/
@[reassoc (attr := simp)]
lemma cubeComplexZeroFaceι_π_insert {r : ℤ} (S : Finset (Fin n))
    (hS : (#(insert 0 (S.map (Fin.succEmb n))) : ℤ) = r) :
    F.cubeComplexZeroFaceι r ≫ F.cubeComplexπ ⟨insert 0 (S.map (Fin.succEmb n)), hS⟩ = 0 := by
  ext T
  rw [ι_cubeComplexZeroFaceι_assoc, comp_zero]
  exact F.cubeComplexι_π_of_ne fun e ↦ map_succEmb_ne_insert_zero _ _ (congrArg Subtype.val e)

/-- The inclusion of the `0`-face followed by the projection onto one of its vertices. -/
@[reassoc (attr := simp)]
lemma cubeComplexZeroFaceι_π_map {r : ℤ} (S : Finset (Fin n))
    (hS : (#(S.map (Fin.succEmb n)) : ℤ) = r) :
    F.cubeComplexZeroFaceι r ≫ F.cubeComplexπ ⟨S.map (Fin.succEmb n), hS⟩ =
      F.cubeZeroFace.cubeComplexπ ⟨S, by rwa [card_map] at hS⟩ := by
  ext ⟨T, hT⟩
  rw [ι_cubeComplexZeroFaceι_assoc]
  by_cases hST : T = S
  · subst hST
    exact (F.cubeComplexι_π_self _).trans (F.cubeZeroFace.cubeComplexι_π_self ⟨_, hT⟩).symm
  · have hS' : (#S : ℤ) = r := by rwa [card_map] at hS
    exact (F.cubeComplexι_π_of_ne fun e ↦
      hST (map_inj.1 (congrArg Subtype.val e))).trans
      (F.cubeZeroFace.cubeComplexι_π_of_ne (S := ⟨T, hT⟩) (T := ⟨S, hS'⟩)
        fun e ↦ hST (congrArg Subtype.val e)).symm

/-- The summands of the `1`-face are a retract of the cube complex. -/
@[reassoc (attr := simp)]
lemma cubeComplexOneFaceι_cubeComplexOneFaceπ {j r : ℤ} (h : j + 1 = r) :
    F.cubeComplexOneFaceι h ≫ F.cubeComplexOneFaceπ h = 𝟙 _ := by
  refine F.cubeOneFace.cubeComplex_hom_ext fun ⟨S, hS⟩ ↦ ?_
  rw [ι_cubeComplexOneFaceι_assoc, ι_insert_cubeComplexOneFaceπ, Category.comp_id]

/-- The summands of the `0`-face are a retract of the cube complex. -/
@[reassoc (attr := simp)]
lemma cubeComplexZeroFaceι_cubeComplexZeroFaceπ (r : ℤ) :
    F.cubeComplexZeroFaceι r ≫ F.cubeComplexZeroFaceπ r = 𝟙 _ := by
  refine F.cubeZeroFace.cubeComplex_hom_ext fun ⟨S, hS⟩ ↦ ?_
  rw [ι_cubeComplexZeroFaceι_assoc, ι_map_cubeComplexZeroFaceπ, Category.comp_id]

/-- Each term of the cube complex is the biproduct of the summands of its two faces. -/
lemma cubeComplexOneFaceπ_ι_add_cubeComplexZeroFaceπ_ι {j r : ℤ} (h : j + 1 = r) :
    F.cubeComplexOneFaceπ h ≫ F.cubeComplexOneFaceι h +
      F.cubeComplexZeroFaceπ r ≫ F.cubeComplexZeroFaceι r = 𝟙 _ := by
  refine F.cubeComplex_hom_ext fun ⟨T, hT⟩ ↦ ?_
  obtain ⟨S, rfl | rfl⟩ := exists_eq_map_succEmb_or T
  · rw [Preadditive.comp_add, ι_map_cubeComplexOneFaceπ_assoc, ι_map_cubeComplexZeroFaceπ_assoc,
      ι_cubeComplexZeroFaceι, zero_comp, zero_add, Category.comp_id]
  · rw [Preadditive.comp_add, ι_insert_cubeComplexOneFaceπ_assoc,
      ι_insert_cubeComplexZeroFaceπ_assoc, ι_cubeComplexOneFaceι, zero_comp, add_zero,
      Category.comp_id]

/-- The summands of the `0`-face are orthogonal to the projection onto the `1`-face. -/
@[reassoc (attr := simp)]
lemma cubeComplexZeroFaceι_cubeComplexOneFaceπ {j r : ℤ} (h : j + 1 = r) :
    F.cubeComplexZeroFaceι r ≫ F.cubeComplexOneFaceπ h = 0 := by
  refine F.cubeZeroFace.cubeComplex_hom_ext fun ⟨S, hS⟩ ↦ ?_
  rw [ι_cubeComplexZeroFaceι_assoc, ι_map_cubeComplexOneFaceπ, comp_zero]

/-- The summands of the `1`-face are orthogonal to the projection onto the `0`-face. -/
@[reassoc (attr := simp)]
lemma cubeComplexOneFaceι_cubeComplexZeroFaceπ {j r : ℤ} (h : j + 1 = r) :
    F.cubeComplexOneFaceι h ≫ F.cubeComplexZeroFaceπ r = 0 := by
  refine F.cubeOneFace.cubeComplex_hom_ext fun ⟨S, hS⟩ ↦ ?_
  rw [ι_cubeComplexOneFaceι_assoc, ι_insert_cubeComplexZeroFaceπ, comp_zero]

/-! ### The differential on the faces -/

/-- On the summands of the `1`-face the cube differential is the differential of the `1`-face with
the sign `-1`, since every other index lies above the first one. -/
lemma cubeComplexOneFaceι_d {j j' r r' : ℤ} (h : j + 1 = r) (h' : j' + 1 = r') :
    F.cubeComplexOneFaceι h ≫ F.cubeComplex.d r r' =
      -(F.cubeOneFace.cubeComplex.d j j' ≫ F.cubeComplexOneFaceι h') := by
  by_cases hr : r + 1 = r'
  swap
  · rw [F.cubeComplex.shape r r' hr, F.cubeOneFace.cubeComplex.shape j j' (by simp; omega),
      comp_zero, zero_comp, neg_zero]
  subst h h'
  obtain rfl : j' = j + 1 := by omega
  refine F.cubeOneFace.cubeComplex_hom_ext fun ⟨S, hS⟩ ↦
    F.cubeComplex_hom_ext' fun ⟨T, hT⟩ ↦ ?_
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
  obtain ⟨U, rfl | rfl⟩ := exists_eq_map_succEmb_or T
  · rw [cubeComplexOneFaceι_π_map, comp_zero, comp_zero, neg_zero, ι_cubeComplexOneFaceι_assoc,
      cubeComplexι_d_cubeComplexπ_eq_zero _ _ _ (not_insert_zero_map_succEmb_subset _ _)]
  · have hU : (#U : ℤ) = j + 1 := by
      rw [card_insert_zero_map_succEmb, Nat.cast_succ] at hT; omega
    rw [cubeComplexOneFaceι_π_insert, ι_cubeComplexOneFaceι_assoc]
    by_cases hSU : S ⊆ U
    · obtain ⟨b, hb, rfl⟩ := exists_eq_insert_iff.2 ⟨hSU, by omega⟩
      rw [F.cubeComplexι_d_cubeComplexπ rfl _ _ (a := b.succ) (by simpa using hb)
          (by dsimp only; rw [map_succEmb_insert, insert_comm]),
        F.cubeOneFace.cubeComplexι_d_cubeComplexπ rfl ⟨S, hS⟩ ⟨insert b S, hU⟩ hb rfl,
        card_filter_lt_succ_insert_zero_map_succEmb, pow_succ, cubeOneFace_map, mul_neg_one,
        neg_smul]
    · rw [F.cubeOneFace.cubeComplexι_d_cubeComplexπ_eq_zero _ _ hSU, neg_zero,
        F.cubeComplexι_d_cubeComplexπ_eq_zero _ _ (by
          simpa only [insert_zero_map_succEmb_subset_iff] using hSU)]

/-- The projection onto the `0`-face commutes with the differentials: the edges between vertices of
the `0`-face are those of the `0`-face cube, and no edge leaves the `1`-face. -/
@[reassoc]
lemma cubeComplex_d_cubeComplexZeroFaceπ (r r' : ℤ) :
    F.cubeComplex.d r r' ≫ F.cubeComplexZeroFaceπ r' =
      F.cubeComplexZeroFaceπ r ≫ F.cubeZeroFace.cubeComplex.d r r' := by
  by_cases hr : r + 1 = r'
  swap
  · rw [F.cubeComplex.shape r r' hr, F.cubeZeroFace.cubeComplex.shape r r' hr, zero_comp,
      comp_zero]
  subst hr
  refine F.cubeComplex_hom_ext fun ⟨T, hT⟩ ↦ F.cubeZeroFace.cubeComplex_hom_ext' fun ⟨U, hU⟩ ↦ ?_
  simp only [Category.assoc]
  obtain ⟨S, rfl | rfl⟩ := exists_eq_map_succEmb_or T
  · have hS : (#S : ℤ) = r := by rwa [card_map] at hT
    rw [cubeComplexZeroFaceπ_π, ι_map_cubeComplexZeroFaceπ_assoc]
    by_cases hSU : S ⊆ U
    · obtain ⟨b, hb, rfl⟩ := exists_eq_insert_iff.2 ⟨hSU, by omega⟩
      rw [F.cubeComplexι_d_cubeComplexπ rfl _ _ (a := b.succ) (by simpa using hb)
          (map_succEmb_insert S b).symm,
        F.cubeZeroFace.cubeComplexι_d_cubeComplexπ rfl ⟨S, hS⟩ ⟨insert b S, hU⟩ hb rfl,
        card_filter_lt_succ_map_succEmb, cubeZeroFace_map]
    · rw [F.cubeZeroFace.cubeComplexι_d_cubeComplexπ_eq_zero _ _ hSU,
        F.cubeComplexι_d_cubeComplexπ_eq_zero _ _ (by simpa only [map_subset_map] using hSU)]
  · rw [ι_insert_cubeComplexZeroFaceπ_assoc, zero_comp, cubeComplexZeroFaceπ_π,
      cubeComplexι_d_cubeComplexπ_eq_zero _ _ _ (not_insert_zero_map_succEmb_subset _ _)]

/-- The component of the cube differential from the `0`-face to the `1`-face is the cochain map
induced by the face map: the edge `F(S) ⟶ F(S ∪ {0})` carries the sign `+1`. -/
@[reassoc]
lemma cubeComplexZeroFaceι_d_cubeComplexOneFaceπ {p q j : ℤ} (hpq : p + 1 = q) (h : j + 1 = q) :
    F.cubeComplexZeroFaceι p ≫ F.cubeComplex.d p q ≫ F.cubeComplexOneFaceπ h =
      (NatTrans.cubeComplexMap F.cubeFaceMap).f p ≫
        (F.cubeOneFace.cubeComplex.XIsoOfEq (by omega : p = j)).hom := by
  subst hpq
  refine F.cubeZeroFace.cubeComplex_hom_ext fun ⟨S, hS⟩ ↦
    F.cubeOneFace.cubeComplex_hom_ext' fun ⟨U, hU⟩ ↦ ?_
  simp only [Category.assoc]
  rw [ι_cubeComplexZeroFaceι_assoc, cubeComplexOneFaceπ_π, NatTrans.ι_cubeComplexMap_f_assoc,
    cubeComplexι_XIsoOfEq_hom_assoc]
  by_cases hSU : S = U
  · subst hSU
    rw [F.cubeComplexι_d_cubeComplexπ rfl _ _ (a := 0) (zero_notMem_map_succEmb S) rfl,
      cubeComplexι_π_self, Category.comp_id, cubeFaceMap_app]
    simp
  · rw [F.cubeOneFace.cubeComplexι_π_of_ne (by simpa using hSU), comp_zero,
      F.cubeComplexι_d_cubeComplexπ_eq_zero]
    rw [map_succEmb_subset_insert_zero_iff]
    exact fun h ↦ hSU (eq_of_subset_of_card_le h (by omega))

/-- On the summands of the `0`-face the cube differential is the differential of the `0`-face
plus the face map to the `1`-face. -/
lemma cubeComplexZeroFaceι_d {p q : ℤ} (h : p + 1 = q) :
    F.cubeComplexZeroFaceι p ≫ F.cubeComplex.d p q =
      F.cubeZeroFace.cubeComplex.d p q ≫ F.cubeComplexZeroFaceι q +
        (NatTrans.cubeComplexMap F.cubeFaceMap).f p ≫ F.cubeComplexOneFaceι h := by
  rw [← Category.comp_id (F.cubeComplex.d p q),
    ← F.cubeComplexOneFaceπ_ι_add_cubeComplexZeroFaceπ_ι h, Preadditive.comp_add,
    Preadditive.comp_add, cubeComplex_d_cubeComplexZeroFaceπ_assoc,
    cubeComplexZeroFaceι_cubeComplexZeroFaceπ_assoc,
    F.cubeComplexZeroFaceι_d_cubeComplexOneFaceπ_assoc h h, XIsoOfEq_rfl, Iso.refl_hom,
    Category.id_comp]
  exact add_comm _ _

/-! ### The short exact sequence of the faces -/

/-- The inclusion of the `1`-face complex, shifted by `-1`, into the cube complex. The shift
negates the differential of the `1`-face, matching the sign in `Functor.cubeComplexOneFaceι_d`. -/
@[expose]
def cubeComplexOneFaceInclusion : F.cubeOneFace.cubeComplex⟦(-1 : ℤ)⟧ ⟶ F.cubeComplex where
  f r := F.cubeComplexOneFaceι (j := r + -1) (by omega)
  comm' := by
    rintro r _ rfl
    rw [F.cubeComplexOneFaceι_d _ (by omega : r + 1 + -1 + 1 = r + 1), shiftFunctor_obj_d']
    simp [Int.negOnePow_neg, Units.smul_def]

/-- The projection of the cube complex onto the `0`-face complex. -/
@[expose]
def cubeComplexZeroFaceProjection : F.cubeComplex ⟶ F.cubeZeroFace.cubeComplex where
  f r := F.cubeComplexZeroFaceπ r
  comm' r r' _ := (F.cubeComplex_d_cubeComplexZeroFaceπ r r').symm

@[simp]
lemma cubeComplexOneFaceInclusion_f (r : ℤ) :
    F.cubeComplexOneFaceInclusion.f r = F.cubeComplexOneFaceι (j := r + -1) (by omega) :=
  (rfl)

@[simp]
lemma cubeComplexZeroFaceProjection_f (r : ℤ) :
    F.cubeComplexZeroFaceProjection.f r = F.cubeComplexZeroFaceπ r :=
  (rfl)

/-- The short exact sequence `0 ⟶ (cubeComplex F₁)⟦-1⟧ ⟶ cubeComplex F ⟶ cubeComplex F₀ ⟶ 0`
of the faces of a cube at its first index. Its terms are exposed, so that the complexes of the
faces and of the cube can be read off from the short complex. -/
@[expose, simps]
def cubeComplexShortComplex : ShortComplex (CochainComplex C ℤ) where
  f := F.cubeComplexOneFaceInclusion
  g := F.cubeComplexZeroFaceProjection
  zero := by
    ext r : 1
    rw [comp_f, zero_f]
    exact F.cubeComplexOneFaceι_cubeComplexZeroFaceπ (j := r + -1) (by omega)

/-- The splitting in each degree of the short exact sequence of the faces, given by the
biproduct decomposition of the cube complex into the summands of the two faces. -/
@[expose, simps]
def cubeComplexShortComplexSplitting (r : ℤ) :
    (F.cubeComplexShortComplex.map (eval C (ComplexShape.up ℤ) r)).Splitting where
  r := F.cubeComplexOneFaceπ (j := r + -1) (by omega)
  s := F.cubeComplexZeroFaceι r
  f_r := F.cubeComplexOneFaceι_cubeComplexOneFaceπ _
  s_g := F.cubeComplexZeroFaceι_cubeComplexZeroFaceπ r
  id := F.cubeComplexOneFaceπ_ι_add_cubeComplexZeroFaceπ_ι _

/-- The connecting morphism of the short exact sequence of the faces is the cochain map induced by
the face map. -/
lemma homOfDegreewiseSplit_cubeComplexShortComplex :
    homOfDegreewiseSplit _ F.cubeComplexShortComplexSplitting =
      NatTrans.cubeComplexMap F.cubeFaceMap ≫
        (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).inv.app _ := by
  ext p : 1
  rw [homOfDegreewiseSplit_f]
  dsimp only [cocycleOfDegreewiseSplit]
  simp only [cubeComplexShortComplexSplitting_s, cubeComplexShortComplexSplitting_r,
    HomComplex.Cocycle.mk_coe, HomComplex.Cochain.mk_v, shiftFunctorCompIsoId, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, comp_f, shiftFunctor_obj_X', shiftFunctorZero_inv_app_f,
    shiftFunctorAdd'_hom_app_f', XIsoOfEq_hom_comp_XIsoOfEq_hom]
  exact F.cubeComplexZeroFaceι_d_cubeComplexOneFaceπ rfl _

/-! ### The mapping cone of the face map -/

section MappingCone

variable [HasBinaryBiproducts C]

/-- The identification of the term of degree `p` of the mapping cone of the face map with the term
of degree `p + 1` of the cube complex; it carries the sign `-1` on the `1`-face. -/
def cubeComplexMappingConeXIso (p : ℤ) :
    (mappingCone (NatTrans.cubeComplexMap F.cubeFaceMap)).X p ≅ F.cubeComplex.X (p + 1) where
  hom := (mappingCone.fst (NatTrans.cubeComplexMap F.cubeFaceMap)).1.v p (p + 1) rfl ≫
      F.cubeComplexZeroFaceι (p + 1) -
    (mappingCone.snd (NatTrans.cubeComplexMap F.cubeFaceMap)).v p p (add_zero p) ≫
      F.cubeComplexOneFaceι rfl
  inv := F.cubeComplexZeroFaceπ (p + 1) ≫
      (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) -
    F.cubeComplexOneFaceπ rfl ≫ (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p
  hom_inv_id := by
    simp [mappingCone.ext_from_iff _ (p + 1) p rfl]
  inv_hom_id := by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_fst_v_assoc,
      mappingCone.inr_f_snd_v_assoc, zero_comp, comp_zero, sub_zero, zero_sub, sub_neg_eq_add]
    exact (add_comm _ _).trans (F.cubeComplexOneFaceπ_ι_add_cubeComplexZeroFaceπ_ι rfl)

/-- The identification `Functor.cubeComplexMappingConeXIso` on the first summand of the cone. -/
@[reassoc (attr := simp)]
lemma inl_v_cubeComplexMappingConeXIso_hom (p : ℤ) :
    (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) ≫
      (F.cubeComplexMappingConeXIso p).hom = F.cubeComplexZeroFaceι (p + 1) := by
  simp [cubeComplexMappingConeXIso]

/-- The identification `Functor.cubeComplexMappingConeXIso` on the second summand of the cone. -/
@[reassoc (attr := simp)]
lemma inr_f_cubeComplexMappingConeXIso_hom (p : ℤ) :
    (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p ≫
      (F.cubeComplexMappingConeXIso p).hom = -F.cubeComplexOneFaceι (j := p) (r := p + 1) rfl := by
  simp [cubeComplexMappingConeXIso]

/-- The mapping cone of the cochain map induced by the face map is the cube complex, shifted by
`1`. It is the inclusion of the `0`-face on the first summand of the cone
(`Functor.inl_v_cubeComplexMappingConeIso_hom_f`) and the inclusion of the `1`-face with the sign
`-1` on the second (`Functor.inr_f_cubeComplexMappingConeIso_hom_f`). -/
def cubeComplexMappingConeIso :
    mappingCone (NatTrans.cubeComplexMap F.cubeFaceMap) ≅ F.cubeComplex⟦(1 : ℤ)⟧ :=
  Hom.isoOfComponents F.cubeComplexMappingConeXIso (by
    rintro p _ rfl
    rw [mappingCone.ext_from_iff _ (p + 1) p rfl, shiftFunctor_obj_d']
    constructor
    · rw [inl_v_cubeComplexMappingConeXIso_hom_assoc,
        mappingCone.inl_v_d_assoc _ (p + 1) p (p + 1 + 1) (by omega) (by omega)]
      simp only [cubeComplexZeroFaceι_d _ (rfl : p + 1 + 1 = p + 1 + 1), Int.negOnePow_one,
        Units.neg_smul, one_smul, Preadditive.comp_neg, Preadditive.sub_comp, Category.assoc,
        inr_f_cubeComplexMappingConeXIso_hom, inl_v_cubeComplexMappingConeXIso_hom,
        Preadditive.comp_neg]
      abel
    · rw [inr_f_cubeComplexMappingConeXIso_hom_assoc, mappingCone.inr_f_d_assoc,
        inr_f_cubeComplexMappingConeXIso_hom]
      simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg,
        Preadditive.neg_comp, neg_inj]
      rw [F.cubeComplexOneFaceι_d (j := p) (j' := p + 1) rfl rfl, neg_neg])

/-- On the summands of the `0`-face, the identification of the mapping cone of the face map with
the shifted cube complex is the inclusion of the `0`-face. -/
@[reassoc (attr := simp)]
lemma inl_v_cubeComplexMappingConeIso_hom_f (p : ℤ) :
    (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) ≫
      F.cubeComplexMappingConeIso.hom.f p = F.cubeComplexZeroFaceι (p + 1) := by
  simp [cubeComplexMappingConeIso, cubeComplexMappingConeXIso]

/-- On the summands of the `1`-face, the identification of the mapping cone of the face map with
the shifted cube complex is the inclusion of the `1`-face with the sign `-1`. -/
@[reassoc (attr := simp)]
lemma inr_f_cubeComplexMappingConeIso_hom_f (p : ℤ) :
    (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p ≫
      F.cubeComplexMappingConeIso.hom.f p = -F.cubeComplexOneFaceι (j := p) (r := p + 1) rfl := by
  simp [cubeComplexMappingConeIso, cubeComplexMappingConeXIso]

end MappingCone

end Functor

section Abelian

variable [Abelian C] [HasFiniteBiproducts C] {n : ℕ} (F : Finset (Fin (n + 1)) ⥤ C)

/-- The sequence `0 ⟶ (cubeComplex F₁)⟦-1⟧ ⟶ cubeComplex F ⟶ cubeComplex F₀ ⟶ 0` of the faces of a
cube at its first index is short exact. -/
lemma Functor.cubeComplexShortComplex_shortExact : F.cubeComplexShortComplex.ShortExact :=
  shortExact_of_degreewise_shortExact _ fun r ↦ (F.cubeComplexShortComplexSplitting r).shortExact

end Abelian

end CategoryTheory
