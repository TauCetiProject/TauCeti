/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Iterated fibre products: simplicial and topological structure

Given a map `π : Y → M`, its `k`-fold fibre product `TauCeti.IteratedFiberProduct π k` is the
subtype `{y : Fin k → Y // ∀ i j : Fin k, π (y i) = π (y j)}` of `k`-tuples in `Y` lying in a
common fibre of `π`, endowed with the subspace topology inherited from `Fin k → Y`.

Every map `f : Fin l → Fin k` induces a contravariant reindexing map
`IteratedFiberProduct.reindex π f : IteratedFiberProduct π k → IteratedFiberProduct π l`.
In particular, the order-preserving coface and codegeneracy maps of `Fin` induce the face maps
`IteratedFiberProduct.face π i` (omitting coordinate `i`) and the diagonal degeneracy maps
`IteratedFiberProduct.degen π i` (duplicating coordinate `i`), which satisfy all five simplicial
identities. Injective index maps between nonempty finite types induce surjective reindexing maps
without any surjectivity assumption on `π`, while surjective index maps induce topological
embeddings (which are closed embeddings when `Y` is Hausdorff). When `M` is Hausdorff and `π` is
continuous, `IteratedFiberProduct π k` is closed in `Fin k → Y`.

## Main definitions

* `TauCeti.IteratedFiberProduct π k`: the subtype of `k`-tuples in `Y` lying in a common fibre
  of `π`.
* `TauCeti.IteratedFiberProduct.proj`: the `i`-th coordinate projection `Y^[k] → Y`.
* `TauCeti.IteratedFiberProduct.baseProj`: the common base projection `Y^[k+1] → M`.
* `TauCeti.IteratedFiberProduct.diag`: the diagonal map `Y → Y^[k]`.
* `TauCeti.IteratedFiberProduct.reindex`: contravariant reindexing along `f : Fin l → Fin k`.
* `TauCeti.IteratedFiberProduct.face`: the `i`-th simplicial face map `Y^[k+2] → Y^[k+1]`.
* `TauCeti.IteratedFiberProduct.degen`: the `i`-th simplicial degeneracy map `Y^[k+1] → Y^[k+2]`.

## Main results

* `TauCeti.IteratedFiberProduct.face_face`, `face_degen_of_le`, `face_castSucc_degen`,
  `face_succ_degen`, `face_degen_of_gt`, `degen_degen`: the five simplicial identities.
* `TauCeti.IteratedFiberProduct.surjective_reindex`, `surjective_proj`, `surjective_face`,
  `surjective_baseProj`: surjectivity of structure maps.
* `TauCeti.IteratedFiberProduct.isEmbedding_reindex`, `isEmbedding_degen`, `isEmbedding_diag`,
  `isClosedEmbedding_coe`, `isClosedEmbedding_reindex`, `isClosedEmbedding_degen`,
  `isClosedEmbedding_diag`: topological and closed embedding results.

## References

* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416, §3
  (iterated fibre products and their simplicial face maps).
-/

public section

open Function Set Topology

namespace TauCeti

/-- The `k`-fold fibre product `Y^[k]` of a map `π : Y → M`: the subtype of `k`-tuples in `Y`
whose coordinates all have the same image under `π`, equipped with the subspace topology of
`Fin k → Y`. -/
abbrev IteratedFiberProduct {Y M : Type*} (π : Y → M) (k : ℕ) : Type _ :=
  {y : Fin k → Y // ∀ i j : Fin k, π (y i) = π (y j)}

namespace IteratedFiberProduct

section Pure

variable {Y M : Type*} (π : Y → M)

/-- Two elements of an iterated fibre product are equal when all their coordinates agree. -/
theorem ext {k : ℕ} {y z : IteratedFiberProduct π k} (h : ∀ i, y.1 i = z.1 i) : y = z :=
  Subtype.ext (funext h)

/-- The `i`-th factor projection `Y^[k] → Y`. -/
@[expose] def proj {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) : Y :=
  y.1 i

/-- Evaluating the `i`-th projection returns the `i`-th coordinate. -/
@[simp]
theorem proj_apply {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) :
    proj π i y = y.1 i :=
  (rfl)

/-- The canonical projection `Y^[k+1] → M` sending a matching tuple to the common image of its
coordinates under `π`. -/
@[expose] def baseProj {k : ℕ} (y : IteratedFiberProduct π (k + 1)) : M :=
  π (y.1 0)

/-- The base projection agrees with `π` evaluated on any coordinate of the tuple. -/
theorem baseProj_eq {k : ℕ} (y : IteratedFiberProduct π (k + 1)) (i : Fin (k + 1)) :
    baseProj π y = π (y.1 i) :=
  y.2 0 i

/-- The base projection is `π` applied to the zeroth coordinate. -/
theorem baseProj_eq_zero {k : ℕ} (y : IteratedFiberProduct π (k + 1)) :
    baseProj π y = π (y.1 0) :=
  (rfl)

/-- The diagonal embedding `Y → Y^[k]` repeating a point `k` times. -/
@[expose] def diag (k : ℕ) (y : Y) : IteratedFiberProduct π k :=
  ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩

/-- The underlying tuple of the diagonal is constant. -/
@[simp]
theorem coe_diag (k : ℕ) (y : Y) : (diag π k y).1 = fun _ ↦ y :=
  (rfl)

/-- Every coordinate projection of the diagonal returns the original point. -/
theorem proj_diag {k : ℕ} (i : Fin k) (y : Y) : proj π i (diag π k y) = y :=
  (rfl)

/-- The base projection of the `(k + 1)`-fold diagonal is `π`. -/
@[simp]
theorem baseProj_diag (k : ℕ) (y : Y) : baseProj π (diag π (k + 1) y) = π y :=
  (rfl)

/-- Contravariant reindexing `Y^[k] → Y^[l]` induced by `f : Fin l → Fin k`. -/
@[expose] def reindex {k l : ℕ} (f : Fin l → Fin k) (y : IteratedFiberProduct π k) :
    IteratedFiberProduct π l :=
  ⟨y.1 ∘ f, fun i j ↦ y.2 (f i) (f j)⟩

/-- The underlying tuple of a reindexed element is precomposition with `f`. -/
@[simp]
theorem coe_reindex {k l : ℕ} (f : Fin l → Fin k) (y : IteratedFiberProduct π k) :
    (reindex π f y).1 = y.1 ∘ f :=
  (rfl)

/-- Coordinate projections of a reindexed element. -/
theorem proj_reindex {k l : ℕ} (f : Fin l → Fin k) (j : Fin l) (y : IteratedFiberProduct π k) :
    proj π j (reindex π f y) = y.1 (f j) :=
  (rfl)

/-- Reindexing along the identity map is the identity. -/
@[simp]
theorem reindex_id {k : ℕ} (y : IteratedFiberProduct π k) :
    reindex π id y = y :=
  Subtype.ext rfl

/-- Reindexing is contravariantly functorial in the index map. -/
theorem reindex_comp {k l m : ℕ} (f : Fin l → Fin k) (g : Fin m → Fin l)
    (y : IteratedFiberProduct π k) :
    reindex π (f ∘ g) y = reindex π g (reindex π f y) :=
  Subtype.ext rfl

/-- Reindexing commutes with the base projection to `M`. -/
@[simp]
theorem baseProj_reindex {k l : ℕ} (f : Fin (l + 1) → Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    baseProj π (reindex π f y) = baseProj π y :=
  y.2 (f 0) 0

/-- Reindexing sends the diagonal to the diagonal. -/
@[simp]
theorem reindex_diag {k l : ℕ} (f : Fin l → Fin k) (y : Y) :
    reindex π f (diag π k y) = diag π l y :=
  Subtype.ext rfl

/-- The `i`-th simplicial face map `Y^[k+2] → Y^[k+1]`, omitting the `i`-th coordinate. -/
@[expose] def face {k : ℕ} (i : Fin (k + 2)) :
    IteratedFiberProduct π (k + 2) → IteratedFiberProduct π (k + 1) :=
  reindex π i.succAbove

/-- The underlying tuple of `face π i y` precomposes `y.1` with `i.succAbove`. -/
@[simp]
theorem coe_face {k : ℕ} (i : Fin (k + 2)) (y : IteratedFiberProduct π (k + 2)) :
    (face π i y).1 = y.1 ∘ i.succAbove :=
  (rfl)

/-- Coordinate formula for the `i`-th face map. -/
theorem proj_face {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (y : IteratedFiberProduct π (k + 2)) :
    proj π j (face π i y) = y.1 (i.succAbove j) :=
  (rfl)

/-- Face maps preserve the base projection to `M`. -/
@[simp]
theorem baseProj_face {k : ℕ} (i : Fin (k + 2)) (y : IteratedFiberProduct π (k + 2)) :
    baseProj π (face π i y) = baseProj π y :=
  baseProj_reindex π i.succAbove y

/-- Face maps carry the diagonal to the diagonal. -/
@[simp]
theorem face_diag {k : ℕ} (i : Fin (k + 2)) (y : Y) :
    face π i (diag π (k + 2) y) = diag π (k + 1) y :=
  reindex_diag π i.succAbove y

/-- The `i`-th simplicial degeneracy map `Y^[k+1] → Y^[k+2]`, duplicating the `i`-th coordinate. -/
@[expose] def degen {k : ℕ} (i : Fin (k + 1)) :
    IteratedFiberProduct π (k + 1) → IteratedFiberProduct π (k + 2) :=
  reindex π i.predAbove

/-- The underlying tuple of `degen π i y` precomposes `y.1` with `i.predAbove`. -/
@[simp]
theorem coe_degen {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    (degen π i y).1 = y.1 ∘ i.predAbove :=
  (rfl)

/-- Coordinate formula for the `i`-th degeneracy map. -/
theorem proj_degen {k : ℕ} (i : Fin (k + 1)) (j : Fin (k + 2))
    (y : IteratedFiberProduct π (k + 1)) :
    proj π j (degen π i y) = y.1 (i.predAbove j) :=
  (rfl)

/-- Degeneracy maps preserve the base projection to `M`. -/
@[simp]
theorem baseProj_degen {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    baseProj π (degen π i y) = baseProj π y :=
  baseProj_reindex π i.predAbove y

/-- Degeneracy maps carry the diagonal to the diagonal. -/
@[simp]
theorem degen_diag {k : ℕ} (i : Fin (k + 1)) (y : Y) :
    degen π i (diag π (k + 1) y) = diag π (k + 2) y :=
  reindex_diag π i.predAbove y

/-! #### Simplicial identities -/

/-- **First simplicial identity**: `face i ∘ face j.succ = face j ∘ face i.castSucc` for
`i ≤ j`. -/
theorem face_face {k : ℕ} {i j : Fin (k + 2)} (h : i ≤ j)
    (y : IteratedFiberProduct π (k + 3)) :
    face π i (face π j.succ y) = face π j (face π i.castSucc y) := by
  apply ext
  intro m
  have hδ := congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk (k + 2) ↦ f.toOrderHom m)
    (SimplexCategory.δ_comp_δ h)
  exact congrArg y.1 hδ

/-- **Second simplicial identity**: `face i.castSucc ∘ degen j.succ = degen j ∘ face i` for
`i ≤ j.castSucc`. -/
theorem face_degen_of_le {k : ℕ} {i : Fin (k + 2)} {j : Fin (k + 1)} (h : i ≤ j.castSucc)
    (y : IteratedFiberProduct π (k + 2)) :
    face π i.castSucc (degen π j.succ y) = degen π j (face π i y) := by
  apply ext
  intro m
  have hδσ := congrArg (fun f : SimplexCategory.mk (k + 1) ⟶ SimplexCategory.mk (k + 1) ↦
    f.toOrderHom m) (SimplexCategory.δ_comp_σ_of_le h)
  exact congrArg y.1 hδσ

/-- **Third simplicial identity (left)**: `face i.castSucc ∘ degen i = id`. -/
@[simp]
theorem face_castSucc_degen {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    face π i.castSucc (degen π i y) = y := by
  apply ext
  intro m
  have hδσ := congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk k ↦ f.toOrderHom m)
    (SimplexCategory.δ_comp_σ_self (i := i))
  exact congrArg y.1 hδσ

/-- **Third simplicial identity (right)**: `face i.succ ∘ degen i = id`. -/
@[simp]
theorem face_succ_degen {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    face π i.succ (degen π i y) = y := by
  apply ext
  intro m
  have hδσ := congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk k ↦ f.toOrderHom m)
    (SimplexCategory.δ_comp_σ_succ (i := i))
  exact congrArg y.1 hδσ

/-- **Fourth simplicial identity**: `face i.succ ∘ degen j.castSucc = degen j ∘ face i` for
`j.castSucc < i`. -/
theorem face_degen_of_gt {k : ℕ} {i : Fin (k + 2)} {j : Fin (k + 1)} (h : j.castSucc < i)
    (y : IteratedFiberProduct π (k + 2)) :
    face π i.succ (degen π j.castSucc y) = degen π j (face π i y) := by
  apply ext
  intro m
  have hδσ := congrArg (fun f : SimplexCategory.mk (k + 1) ⟶ SimplexCategory.mk (k + 1) ↦
    f.toOrderHom m) (SimplexCategory.δ_comp_σ_of_gt h)
  exact congrArg y.1 hδσ

/-- **Fifth simplicial identity**: `degen i.castSucc ∘ degen j = degen j.succ ∘ degen i` for
`i ≤ j`. -/
theorem degen_degen {k : ℕ} {i j : Fin (k + 1)} (h : i ≤ j)
    (y : IteratedFiberProduct π (k + 1)) :
    degen π i.castSucc (degen π j y) = degen π j.succ (degen π i y) := by
  apply ext
  intro m
  have hσσ := congrArg (fun f : SimplexCategory.mk (k + 2) ⟶ SimplexCategory.mk k ↦
    f.toOrderHom m) (SimplexCategory.σ_comp_σ h)
  exact congrArg y.1 hσσ

/-! #### Surjectivity and injectivity -/

/-- Any injective index map `f : Fin (l + 1) → Fin (k + 1)` induces a surjective reindexing map
`Y^[k+1] → Y^[l+1]`: coordinates outside the range of `f` can be filled with a chosen entry.
No surjectivity hypothesis on `π` is needed. -/
theorem surjective_reindex {k l : ℕ} {f : Fin (l + 1) → Fin (k + 1)} (hf : Injective f) :
    Surjective (reindex π f) := by
  classical
  intro z
  let g : Fin (k + 1) → Fin (l + 1) := invFun f
  have hgf : ∀ j, g (f j) = j := leftInverse_invFun hf
  exact ⟨reindex π g z, by
    apply ext
    intro j
    simp [hgf]⟩

/-- Any surjective index map induces an injective reindexing map. -/
theorem injective_reindex {k l : ℕ} {f : Fin l → Fin k} (hf : Surjective f) :
    Injective (reindex π f) := by
  intro y z h
  apply ext
  intro i
  obtain ⟨j, rfl⟩ := hf i
  exact congrFun (congrArg Subtype.val h) j

/-- Every coordinate projection `Y^[k] → Y` is surjective, with section `diag π k`. -/
theorem surjective_proj {k : ℕ} (i : Fin k) : Surjective (proj π i) :=
  fun y ↦ ⟨diag π k y, rfl⟩

/-- Every face map `Y^[k+2] → Y^[k+1]` is surjective. -/
theorem surjective_face {k : ℕ} (i : Fin (k + 2)) : Surjective (face π i) :=
  surjective_reindex π Fin.succAbove_right_injective

/-- Every degeneracy map `Y^[k+1] → Y^[k+2]` is injective. -/
theorem injective_degen {k : ℕ} (i : Fin (k + 1)) : Injective (degen π i) :=
  Function.LeftInverse.injective (face_castSucc_degen π i)

/-- The diagonal `Y → Y^[k+1]` is injective. -/
theorem injective_diag (k : ℕ) : Injective (diag π (k + 1)) :=
  Function.LeftInverse.injective (proj_diag π (0 : Fin (k + 1)))

/-- The base projection `Y^[k+1] → M` is surjective whenever `π` is surjective. -/
theorem surjective_baseProj {π : Y → M} (hπ : Surjective π) (k : ℕ) :
    Surjective (baseProj π : IteratedFiberProduct π (k + 1) → M) := by
  intro x
  obtain ⟨y, rfl⟩ := hπ x
  exact ⟨diag π (k + 1) y, rfl⟩

end Pure

/-! ### Continuity and closed embeddedness -/

section Topology

variable {Y M : Type*} [TopologicalSpace Y] (π : Y → M)

/-- Each coordinate projection `Y^[k] → Y` is continuous. -/
theorem continuous_proj {k : ℕ} (i : Fin k) : Continuous (proj π i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- Every reindexing map `Y^[k] → Y^[l]` is continuous. -/
theorem continuous_reindex {k l : ℕ} (f : Fin l → Fin k) : Continuous (reindex π f) :=
  (continuous_pi fun j ↦ continuous_proj π (f j)).subtype_mk _

/-- Every face map `Y^[k+2] → Y^[k+1]` is continuous. -/
theorem continuous_face {k : ℕ} (i : Fin (k + 2)) : Continuous (face π i) :=
  continuous_reindex π i.succAbove

/-- Every degeneracy map `Y^[k+1] → Y^[k+2]` is continuous. -/
theorem continuous_degen {k : ℕ} (i : Fin (k + 1)) : Continuous (degen π i) :=
  continuous_reindex π i.predAbove

/-- The diagonal map `Y → Y^[k]` is continuous. -/
theorem continuous_diag (k : ℕ) : Continuous (diag π k) :=
  (continuous_pi fun _ ↦ continuous_id).subtype_mk _

/-- Any surjective index map induces a topological embedding on iterated fibre products, with
continuous left inverse given by reindexing along a right inverse of `f`. -/
theorem isEmbedding_reindex {k l : ℕ} {f : Fin l → Fin k} (hf : Surjective f) :
    IsEmbedding (reindex π f) := by
  let g : Fin k → Fin l := surjInv hf
  have hleft : LeftInverse (reindex π g) (reindex π f) := fun y ↦ by
    apply ext
    intro i
    exact congrArg y.1 (surjInv_eq hf i)
  exact hleft.isEmbedding (continuous_reindex π g) (continuous_reindex π f)

/-- Every degeneracy map is a topological embedding. -/
theorem isEmbedding_degen {k : ℕ} (i : Fin (k + 1)) : IsEmbedding (degen π i) :=
  isEmbedding_reindex π (Fin.predAbove_surjective i)

/-- The diagonal `Y → Y^[k+1]` is a topological embedding. -/
theorem isEmbedding_diag (k : ℕ) : IsEmbedding (diag π (k + 1)) :=
  Function.LeftInverse.isEmbedding (proj_diag π (0 : Fin (k + 1)))
    (continuous_proj π 0) (continuous_diag π (k + 1))

/-- When `Y` is Hausdorff, any surjective index map induces a closed topological embedding on
iterated fibre products, since its image is the fixed-point locus of a continuous retraction. -/
theorem isClosedEmbedding_reindex [T2Space Y] {k l : ℕ} {f : Fin l → Fin k} (hf : Surjective f) :
    IsClosedEmbedding (reindex π f) := by
  refine ⟨isEmbedding_reindex π hf, ?_⟩
  let g : Fin k → Fin l := surjInv hf
  have hleft : LeftInverse (reindex π g) (reindex π f) := fun y ↦ by
    apply ext
    intro i
    exact congrArg y.1 (surjInv_eq hf i)
  have hrange : range (reindex π f) = {z : IteratedFiberProduct π l |
      reindex π f (reindex π g z) = z} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      simp [hleft y]
    · intro hz
      exact ⟨reindex π g z, hz⟩
  rw [hrange]
  exact isClosed_eq ((continuous_reindex π f).comp (continuous_reindex π g)) continuous_id

/-- When `Y` is Hausdorff, every degeneracy map is a closed topological embedding. -/
theorem isClosedEmbedding_degen [T2Space Y] {k : ℕ} (i : Fin (k + 1)) :
    IsClosedEmbedding (degen π i) :=
  isClosedEmbedding_reindex π (Fin.predAbove_surjective i)

/-- When `Y` is Hausdorff, the diagonal `Y → Y^[k+1]` is a closed topological embedding. -/
theorem isClosedEmbedding_diag [T2Space Y] (k : ℕ) :
    IsClosedEmbedding (diag π (k + 1)) := by
  refine ⟨isEmbedding_diag π k, ?_⟩
  have hrange : range (diag π (k + 1)) = {z : IteratedFiberProduct π (k + 1) |
      diag π (k + 1) (proj π 0 z) = z} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hz
      exact ⟨proj π 0 z, hz⟩
  rw [hrange]
  exact isClosed_eq ((continuous_diag π (k + 1)).comp (continuous_proj π 0)) continuous_id

/-- The base projection `Y^[k+1] → M` is continuous when `π` is continuous. -/
theorem continuous_baseProj [TopologicalSpace M] {π : Y → M} (hπ : Continuous π) (k : ℕ) :
    Continuous (baseProj π : IteratedFiberProduct π (k + 1) → M) :=
  hπ.comp (continuous_proj π (0 : Fin (k + 1)))

/-- When `M` is Hausdorff and `π : Y → M` is continuous, the locus of matching `k`-tuples is
closed in `Fin k → Y`. -/
theorem isClosed_setOf_iteratedFiberProduct [TopologicalSpace M] [T2Space M] {π : Y → M}
    (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j : Fin k, π (y i) = π (y j)} := by
  have hset : {y : Fin k → Y | ∀ i j : Fin k, π (y i) = π (y j)} =
      ⋂ i : Fin k, ⋂ j : Fin k, {y : Fin k → Y | π (y i) = π (y j)} := by
    ext y
    simp
  rw [hset]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (hπ.comp (continuous_apply i)) (hπ.comp (continuous_apply j))

/-- When `M` is Hausdorff and `π : Y → M` is continuous, the inclusion of `Y^[k]` into
`Fin k → Y` is a closed topological embedding. -/
theorem isClosedEmbedding_coe [TopologicalSpace M] [T2Space M] {π : Y → M} (hπ : Continuous π)
    (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → Fin k → Y) :=
  (isClosed_setOf_iteratedFiberProduct hπ k).isClosedEmbedding_subtypeVal

end Topology

end IteratedFiberProduct

end TauCeti
