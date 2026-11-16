/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Iterated fibre products and their simplicial Čech nerve

For a map `π : Y → M` and a natural number `k`, `TauCeti.IteratedFiberProduct π k` is the subtype
of `k`-tuples in `Fin k → Y` whose entries all lie in the same fibre of `π`. Precomposition by any
index map `α : Fin m → Fin k` yields the contravariant reindexing map
`TauCeti.IteratedFiberProduct.reindex α : Y^[k] → Y^[m]`, which specializes to the Čech-nerve face
maps `face i` (deleting coordinate `i`) and diagonal degeneracies `degeneracy i` (duplicating
coordinate `i`). Together these satisfy all simplicial identities.

Topologically, `IteratedFiberProduct π k` carries the subspace topology from `Fin k → Y`. All
projections, diagonals, reindexing, face, and degeneracy maps are continuous, and the canonical
recursive splitting `Y^[k + 2] ≃ₜ Y^[k + 1] ×_M Y` is a homeomorphism
(`iteratedFiberProductSuccHomeomorph`). When `M` is Hausdorff and `π` is continuous, `Y^[k]` is
closed in `Fin k → Y`.

## Main definitions and results

* `TauCeti.IteratedFiberProduct`: the equal-projection subtype
  `{y : Fin k → Y // ∀ i j, π (y i) = π (y j)}`.
* `TauCeti.IteratedFiberProduct.coord`, `baseProj`, `diag`, `reindex`, `face`, `degeneracy`:
  projections, small diagonal, general index reindexing, and Čech-nerve face and degeneracy maps.
* `TauCeti.IteratedFiberProduct.face_comp_face`, `face_comp_degeneracy_of_le`,
  `face_castSucc_degeneracy`, `face_succ_degeneracy`, `face_comp_degeneracy_of_gt`,
  `degeneracy_comp_degeneracy`: the simplicial identities of the Čech nerve.
* `TauCeti.isClosed_iteratedFiberProduct_set`, `TauCeti.isClosedEmbedding_coe_iteratedFiberProduct`:
  closedness in `Fin k → Y` when `M` is Hausdorff and `π` is continuous.
* `TauCeti.iteratedFiberProductSuccHomeomorph`: the canonical homeomorphism
  `Y^[k + 2] ≃ₜ Y^[k + 1] ×_M Y` separating the last coordinate.

## References

* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416.
-/

public section

open Function Set Topology

namespace TauCeti

variable {Y M : Type*} {π : Y → M}

/-- The `k`-fold iterated fibre product of `π : Y → M`, consisting of `k`-tuples in `Y` whose
entries all lie in the same fibre of `π`. -/
abbrev IteratedFiberProduct (π : Y → M) (k : ℕ) : Type _ :=
  {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}

namespace IteratedFiberProduct

/-- The `i`-th coordinate projection from the `k`-fold iterated fibre product to `Y`. -/
def coord {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) : Y :=
  y.1 i

/-- Evaluating the `i`-th coordinate projection returns the `i`-th entry of the tuple. -/
@[simp]
theorem coord_apply {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) :
    y.coord i = y.1 i :=
  (rfl)

/-- The common projection of a nonempty-index iterated fibre product to the base `M`. -/
def baseProj {k : ℕ} (y : IteratedFiberProduct π (k + 1)) : M :=
  π (y.1 0)

/-- The base projection is defined by applying `π` to the `0`-th coordinate. -/
theorem baseProj_def {k : ℕ} (y : IteratedFiberProduct π (k + 1)) :
    y.baseProj = π (y.1 0) :=
  (rfl)

/-- Every coordinate of a tuple in the iterated fibre product projects to `baseProj`. -/
theorem map_coord_eq_baseProj {k : ℕ} (y : IteratedFiberProduct π (k + 1)) (i : Fin (k + 1)) :
    π (y.1 i) = y.baseProj :=
  y.2 i 0

/-- The small diagonal `Y → Y^[k]`, sending `y` to the constant `k`-tuple. -/
def diag (k : ℕ) (y : Y) : IteratedFiberProduct π k :=
  ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩

/-- The underlying tuple of the diagonal image of `y` is constantly `y`. -/
@[simp]
theorem coe_diag (k : ℕ) (y : Y) :
    (diag (π := π) k y).1 = fun _ ↦ y :=
  (rfl)

/-- The base projection of a diagonal tuple is `π y`. -/
@[simp]
theorem baseProj_diag (k : ℕ) (y : Y) :
    (diag (π := π) (k + 1) y).baseProj = π y :=
  (rfl)

/-- Every coordinate projection from `Y^[k]` to `Y` is surjective, with section `diag k`. -/
theorem surjective_coord {k : ℕ} (i : Fin k) :
    Surjective (coord (π := π) i) :=
  fun y ↦ ⟨diag k y, rfl⟩

/-- The small diagonal into a nonempty-index iterated fibre product is injective. -/
theorem injective_diag (k : ℕ) :
    Injective (diag (π := π) (k + 1)) :=
  fun _ _ h ↦ congrFun (congrArg Subtype.val h) 0

/-- The base projection `Y^[k + 1] → M` is surjective whenever `π : Y → M` is surjective. -/
theorem surjective_baseProj {k : ℕ} (hπ : Surjective π) :
    Surjective (baseProj (π := π) (k := k)) := by
  intro m
  obtain ⟨y, rfl⟩ := hπ m
  exact ⟨diag (k + 1) y, rfl⟩

/-- Contravariant reindexing of tuples in the iterated fibre product along an index map
`α : Fin m → Fin k`. -/
def reindex {m k : ℕ} (α : Fin m → Fin k) (y : IteratedFiberProduct π k) :
    IteratedFiberProduct π m :=
  ⟨y.1 ∘ α, fun i j ↦ y.2 (α i) (α j)⟩

/-- Reindexing acts on underlying tuples by precomposition. -/
@[simp]
theorem coe_reindex {m k : ℕ} (α : Fin m → Fin k) (y : IteratedFiberProduct π k) :
    (y.reindex α).1 = y.1 ∘ α :=
  (rfl)

/-- Reindexing along the identity map is the identity. -/
@[simp]
theorem reindex_id {k : ℕ} (y : IteratedFiberProduct π k) :
    y.reindex id = y :=
  (rfl)

/-- Reindexing is contravariantly functorial under composition of index maps. -/
@[simp]
theorem reindex_comp {l m k : ℕ} (α : Fin m → Fin k) (β : Fin l → Fin m)
    (y : IteratedFiberProduct π k) :
    (y.reindex α).reindex β = y.reindex (α ∘ β) :=
  (rfl)

/-- Reindexing preserves the common base projection. -/
@[simp]
theorem baseProj_reindex {m k : ℕ} (α : Fin (m + 1) → Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    (y.reindex α).baseProj = y.baseProj :=
  y.2 (α 0) 0

/-- Reindexing a constant diagonal tuple yields the constant diagonal tuple of the target length. -/
@[simp]
theorem reindex_diag {m k : ℕ} (α : Fin m → Fin k) (y : Y) :
    (diag (π := π) k y).reindex α = diag m y :=
  (rfl)

/-- Reindexing along an injective index map `Fin (m + 1) → Fin k` is surjective, since any left
inverse of the index map induces a right inverse on iterated fibre products. -/
theorem surjective_reindex {m k : ℕ} {α : Fin (m + 1) → Fin k} (hα : Injective α) :
    Surjective (reindex (π := π) α) := by
  classical
  let β : Fin k → Fin (m + 1) := invFun α
  intro z
  refine ⟨z.reindex β, Subtype.ext (funext fun i ↦ ?_)⟩
  exact congrArg z.1 (leftInverse_invFun hα i)

/-- Reindexing along a surjective index map `Fin m → Fin k` is injective. -/
theorem injective_reindex {m k : ℕ} {α : Fin m → Fin k} (hα : Surjective α) :
    Injective (reindex (π := π) α) := by
  intro y₁ y₂ h
  apply Subtype.ext
  funext i
  obtain ⟨j, rfl⟩ := hα i
  exact congrFun (congrArg Subtype.val h) j

/-- The `i`-th face map `Y^[k + 2] → Y^[k + 1]` of the Čech nerve, omitting the `i`-th
coordinate. -/
def face {k : ℕ} (i : Fin (k + 2)) (y : IteratedFiberProduct π (k + 2)) :
    IteratedFiberProduct π (k + 1) :=
  y.reindex i.succAbove

/-- The `i`-th face map is reindexing along `Fin.succAbove i`. -/
theorem face_eq_reindex {k : ℕ} (i : Fin (k + 2)) :
    face (π := π) i = reindex i.succAbove :=
  (rfl)

/-- The `i`-th face map acts on underlying tuples by precomposition with `Fin.succAbove i`. -/
@[simp]
theorem coe_face {k : ℕ} (i : Fin (k + 2)) (y : IteratedFiberProduct π (k + 2)) :
    (y.face i).1 = y.1 ∘ i.succAbove :=
  (rfl)

/-- Face maps commute with the base projection. -/
@[simp]
theorem baseProj_face {k : ℕ} (i : Fin (k + 2)) (y : IteratedFiberProduct π (k + 2)) :
    (y.face i).baseProj = y.baseProj :=
  baseProj_reindex i.succAbove y

/-- Every face map is surjective. -/
theorem surjective_face {k : ℕ} (i : Fin (k + 2)) :
    Surjective (face (π := π) i) :=
  surjective_reindex Fin.succAbove_right_injective

/-- The `i`-th diagonal degeneracy `Y^[k + 1] → Y^[k + 2]` of the Čech nerve, duplicating the
`i`-th coordinate. -/
def degeneracy {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    IteratedFiberProduct π (k + 2) :=
  y.reindex i.predAbove

/-- The `i`-th degeneracy map is reindexing along `Fin.predAbove i`. -/
theorem degeneracy_eq_reindex {k : ℕ} (i : Fin (k + 1)) :
    degeneracy (π := π) i = reindex i.predAbove :=
  (rfl)

/-- The `i`-th degeneracy acts on underlying tuples by precomposition with `Fin.predAbove i`. -/
@[simp]
theorem coe_degeneracy {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    (y.degeneracy i).1 = y.1 ∘ i.predAbove :=
  (rfl)

/-- Degeneracies commute with the base projection. -/
@[simp]
theorem baseProj_degeneracy {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    (y.degeneracy i).baseProj = y.baseProj :=
  baseProj_reindex i.predAbove y

/-- Every degeneracy map is injective. -/
theorem injective_degeneracy {k : ℕ} (i : Fin (k + 1)) :
    Injective (degeneracy (π := π) i) :=
  injective_reindex i.predAbove_surjective

/-! ### Simplicial identities -/

/-- First simplicial identity: for `i ≤ j`, deleting `j + 1` then `i` agrees with deleting `i`
then `j`. -/
theorem face_comp_face {k : ℕ} {i j : Fin (k + 2)} (hij : i ≤ j) :
    face (π := π) i ∘ face j.succ = face j ∘ face i.castSucc := by
  funext y
  apply Subtype.ext
  funext a
  exact congrArg y.1 (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_δ hij) a)

/-- Pointwise form of the first simplicial identity. -/
theorem face_face {k : ℕ} {i j : Fin (k + 2)} (hij : i ≤ j)
    (y : IteratedFiberProduct π (k + 3)) :
    (y.face j.succ).face i = (y.face i.castSucc).face j :=
  congrFun (face_comp_face hij) y

/-- Second simplicial identity: for `i ≤ j.castSucc`, duplicating `j + 1` then deleting `i`
agrees with deleting `i` then duplicating `j`. -/
theorem face_comp_degeneracy_of_le {k : ℕ} {i : Fin (k + 2)} {j : Fin (k + 1)}
    (hij : i ≤ j.castSucc) :
    face (π := π) i.castSucc ∘ degeneracy j.succ = degeneracy j ∘ face i := by
  funext y
  apply Subtype.ext
  funext a
  exact congrArg y.1
    (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_le hij) a)

/-- First part of the third simplicial identity: deleting the first copy after duplicating `i`
recovers the original tuple. -/
@[simp]
theorem face_castSucc_degeneracy {k : ℕ} (i : Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    (y.degeneracy i).face i.castSucc = y := by
  apply Subtype.ext
  funext a
  exact congrArg y.1
    (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_self (i := i)) a)

/-- Function-composition form of `face_castSucc_degeneracy`. -/
theorem face_castSucc_comp_degeneracy {k : ℕ} (i : Fin (k + 1)) :
    face (π := π) i.castSucc ∘ degeneracy i = id :=
  funext (face_castSucc_degeneracy i)

/-- Second part of the third simplicial identity: deleting the second copy after duplicating `i`
recovers the original tuple. -/
@[simp]
theorem face_succ_degeneracy {k : ℕ} (i : Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    (y.degeneracy i).face i.succ = y := by
  apply Subtype.ext
  funext a
  exact congrArg y.1
    (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_succ (i := i)) a)

/-- Function-composition form of `face_succ_degeneracy`. -/
theorem face_succ_comp_degeneracy {k : ℕ} (i : Fin (k + 1)) :
    face (π := π) i.succ ∘ degeneracy i = id :=
  funext (face_succ_degeneracy i)

/-- Fourth simplicial identity: for `j.castSucc < i`, duplicating `j` then deleting `i + 1`
agrees with deleting `i` then duplicating `j`. -/
theorem face_comp_degeneracy_of_gt {k : ℕ} {i : Fin (k + 2)} {j : Fin (k + 1)}
    (hij : j.castSucc < i) :
    face (π := π) i.succ ∘ degeneracy j.castSucc = degeneracy j ∘ face i := by
  funext y
  apply Subtype.ext
  funext a
  exact congrArg y.1
    (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_gt hij) a)

/-- Fifth simplicial identity: for `i ≤ j`, duplicating `j` then `i` agrees with duplicating
`i` then `j + 1`. -/
theorem degeneracy_comp_degeneracy {k : ℕ} {i j : Fin (k + 1)} (hij : i ≤ j) :
    degeneracy (π := π) i.castSucc ∘ degeneracy j = degeneracy j.succ ∘ degeneracy i := by
  funext y
  apply Subtype.ext
  funext a
  exact congrArg y.1 (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.σ_comp_σ hij) a)

/-! ### Topological properties -/

section Topology

variable [TopologicalSpace Y]

/-- Coordinate projections on the iterated fibre product are continuous. -/
theorem continuous_coord {k : ℕ} (i : Fin k) :
    Continuous (coord (π := π) i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- The base projection is continuous whenever `π` is continuous. -/
theorem continuous_baseProj [TopologicalSpace M] {k : ℕ} (hπ : Continuous π) :
    Continuous (baseProj (π := π) (k := k)) :=
  hπ.comp (continuous_coord 0)

/-- The small diagonal `Y → Y^[k]` is continuous. -/
theorem continuous_diag (k : ℕ) :
    Continuous (diag (π := π) k) :=
  (continuous_pi fun _ ↦ continuous_id).subtype_mk _

/-- Reindexing along any index map is continuous. -/
theorem continuous_reindex {m k : ℕ} (α : Fin m → Fin k) :
    Continuous (reindex (π := π) α) :=
  (continuous_pi fun i ↦ continuous_coord (α i)).subtype_mk _

/-- Every face map is continuous. -/
theorem continuous_face {k : ℕ} (i : Fin (k + 2)) :
    Continuous (face (π := π) i) :=
  continuous_reindex i.succAbove

/-- Every degeneracy map is continuous. -/
theorem continuous_degeneracy {k : ℕ} (i : Fin (k + 1)) :
    Continuous (degeneracy (π := π) i) :=
  continuous_reindex i.predAbove

end Topology

end IteratedFiberProduct

/-- When the base `M` is Hausdorff and `π : Y → M` is continuous, the iterated fibre product
is a closed subset of `Fin k → Y`. -/
theorem isClosed_iteratedFiberProduct_set [TopologicalSpace Y] [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} := by
  have heq : {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} =
      ⋂ i : Fin k, ⋂ j : Fin k, {y : Fin k → Y | π (y i) = π (y j)} := by
    ext y
    simp
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (hπ.comp (continuous_apply i)) (hπ.comp (continuous_apply j))

/-- When the base `M` is Hausdorff and `π : Y → M` is continuous, the inclusion of `Y^[k]` into
`Fin k → Y` is a closed topological embedding. -/
theorem isClosedEmbedding_coe_iteratedFiberProduct [TopologicalSpace Y] [TopologicalSpace M]
    [T2Space M] (hπ : Continuous π) (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → Fin k → Y) :=
  (isClosed_iteratedFiberProduct_set hπ k).isClosedEmbedding_subtypeVal

/-- The canonical homeomorphism splitting off the last coordinate of `Y^[k + 2]`, identifying
`Y^[k + 2]` with `Y^[k + 1] ×_M Y`. -/
def iteratedFiberProductSuccHomeomorph [TopologicalSpace Y] (k : ℕ) :
    IteratedFiberProduct π (k + 2) ≃ₜ
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} where
  toFun y := ⟨(y.reindex Fin.castSucc, y.1 (Fin.last (k + 1))),
    y.2 (Fin.castSucc 0) (Fin.last (k + 1))⟩
  invFun q := ⟨Fin.snoc q.1.1.1 q.1.2, by
    intro i j
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j
    · rfl
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact q.2.symm.trans (q.1.1.2 0 j')
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact (q.1.1.2 i' 0).trans q.2
    · simp only [Fin.snoc_castSucc]
      exact q.1.1.2 i' j'⟩
  left_inv y := Subtype.ext (funext fun i ↦
    Fin.lastCases (by simp) (fun i' ↦ by simp) i)
  right_inv q := Subtype.ext (Prod.ext
    (Subtype.ext (funext fun i ↦ by simp [IteratedFiberProduct.reindex])) (by simp))
  continuous_toFun :=
    ((IteratedFiberProduct.continuous_reindex Fin.castSucc).prodMk
      (IteratedFiberProduct.continuous_coord (Fin.last (k + 1)))).subtype_mk _
  continuous_invFun := by
    refine (continuous_pi fun i ↦ ?_).subtype_mk _
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · exact (continuous_snd.comp continuous_subtype_val).congr fun q ↦ by simp
    · exact ((IteratedFiberProduct.continuous_coord i').comp
        (continuous_fst.comp continuous_subtype_val)).congr fun q ↦ by simp

/-- The recursive splitting homeomorphism separates the initial `k + 1` coordinates from the last
coordinate. -/
@[simp]
theorem iteratedFiberProductSuccHomeomorph_apply [TopologicalSpace Y] (k : ℕ)
    (y : IteratedFiberProduct π (k + 2)) :
    (iteratedFiberProductSuccHomeomorph k y).1 =
      (y.reindex Fin.castSucc, y.1 (Fin.last (k + 1))) :=
  (rfl)

/-- The inverse of the recursive splitting homeomorphism appends the extra coordinate via
`Fin.snoc`. -/
@[simp]
theorem iteratedFiberProductSuccHomeomorph_symm_apply [TopologicalSpace Y] (k : ℕ)
    (q : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}) :
    ((iteratedFiberProductSuccHomeomorph k).symm q).1 = Fin.snoc q.1.1.1 q.1.2 :=
  (rfl)

end TauCeti
