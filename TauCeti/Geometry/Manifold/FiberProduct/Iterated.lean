/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.Geometry.Manifold.FiberProduct.Identity
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Pi
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Iterated fibre products of submersions and their simplicial structure

For a map `π : Y → M` and `k : ℕ`, the `k`-fold iterated fibre product
`TauCeti.IteratedFiberProduct π k` is the subtype `{y : Fin k → Y // ∀ i j, π (y i) = π (y j)}`
with its inherited subspace topology. Any function `f : Fin m → Fin k` induces the contravariant
reindexing map `TauCeti.IteratedFiberProduct.reindex f`, specialising to the face maps
`TauCeti.IteratedFiberProduct.face` (omitting one coordinate) and the diagonal degeneracy maps
`TauCeti.IteratedFiberProduct.degen` (repeating one coordinate). These maps commute with the
base projection `TauCeti.IteratedFiberProduct.baseProj` (for `1 ≤ k`) and satisfy all five
simplicial identities. When `π` is continuous and `M` is Hausdorff, the carrier is closed in
`Fin k → Y`, so the inclusion is a closed topological embedding.

When `π : Y → M` is a `C^n` submersion (`1 ≤ n`) between finite-dimensional boundaryless real
manifolds, each `IteratedFiberProduct π k` (`k : ℕ`) carries a `C^n` manifold structure
(`TauCeti.IteratedFiberProduct.chartedSpace`) of model dimension
`k * dim Y - (k - 1) * dim M` (in particular, dimension `0` for the one-point space at `k = 0`),
constructed by iterating `TauCeti.transverseFiberProductChartedSpace` along
`Y^[k + 1] ≃ Y^[k] ×_M Y`. Its inclusion into `Fin k → Y` is a smooth embedding
(`TauCeti.IteratedFiberProduct.isSmoothEmbedding_val`), and its tangent vectors are exactly the
`k`-tuples of tangent vectors of `Y` with matching images under `dπ`
(`TauCeti.IteratedFiberProduct.mem_range_mfderiv_val_iff`). No Hausdorff, countability,
surjectivity, or nonemptiness assumptions are needed for the smooth structure or its local
properties.

Every reindexing map is `C^n`, every injective reindexing map (in particular every face map and
every coordinate projection) is a `C^n` submersion (and surjective when `1 ≤ m`), the base
projection is a `C^n` submersion (surjective when `π` is surjective), and every degeneracy map is
a `C^n` smooth embedding. The smooth structure is independent of the order of iteration: any smooth
manifold embedded onto the same subset of `Fin k → Y` is canonically diffeomorphic to
`IteratedFiberProduct π k` (`TauCeti.IteratedFiberProduct.diffeomorphOfRangeEq`), and canonical
diffeomorphisms identify permutations (`reindexDiffeomorph`), the unary case (`oneDiffeomorph`),
the binary transverse fibre product (`twoDiffeomorph`), arbitrary splittings
`Y^[p + q] ≃ Y^[p] ×_M Y^[q]` (`addDiffeomorph`), and the identity cover `M^[k] ≃ M`
(`idDiffeomorph`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 4.26 (submersion level sets) and Theorem 6.30 (transverse fibre products).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. 54 (1996), 403–416, §3
  (iterated fibre products of a surjective submersion).
-/

public section

open Function Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The `k`-fold iterated fibre product of `π : Y → M`, consisting of `k`-tuples in `Y` lying in
a common fibre of `π`, with the inherited subspace topology from `Fin k → Y`. -/
abbrev IteratedFiberProduct {Y M : Type*} (π : Y → M) (k : ℕ) :=
  {y : Fin k → Y // ∀ i j, π (y i) = π (y j)}

namespace IteratedFiberProduct

section SetLevel

variable {Y M : Type*} {π : Y → M} {k m l : ℕ}

/-- The canonical base projection `Y^[k] → M` for `1 ≤ k`, sending a matching `k`-tuple to the
common image of its coordinates under `π`. -/
def baseProj (hk : 1 ≤ k) (p : IteratedFiberProduct π k) : M :=
  π (p.1 ⟨0, hk⟩)

/-- The base projection evaluates `π` on the zeroth coordinate. -/
theorem baseProj_apply (hk : 1 ≤ k) (p : IteratedFiberProduct π k) :
    p.baseProj hk = π (p.1 ⟨0, hk⟩) :=
  (rfl)

/-- The base projection agrees with `π` evaluated on any coordinate of the tuple. -/
theorem baseProj_eq (p : IteratedFiberProduct π k) (i : Fin k) :
    p.baseProj i.pos = π (p.1 i) :=
  p.2 ⟨0, i.pos⟩ i

/-- Every coordinate projection `Y^[k] → Y` is surjective, witnessed by constant tuples. -/
theorem coord_surjective (i : Fin k) :
    Surjective (fun p : IteratedFiberProduct π k ↦ p.1 i) :=
  fun y ↦ ⟨⟨fun _ ↦ y, fun _ _ ↦ rfl⟩, rfl⟩

/-- When `π` is surjective, the base projection `Y^[k] → M` is surjective for `1 ≤ k`. -/
theorem baseProj_surjective (hk : 1 ≤ k) (hπ : Surjective π) :
    Surjective (baseProj (π := π) hk) := fun x ↦ by
  obtain ⟨y, rfl⟩ := hπ x
  exact ⟨⟨fun _ ↦ y, fun _ _ ↦ rfl⟩, rfl⟩

/-- Contravariant reindexing `Y^[k] → Y^[m]` induced by an index map `f : Fin m → Fin k`. -/
def reindex (f : Fin m → Fin k) (p : IteratedFiberProduct π k) : IteratedFiberProduct π m :=
  ⟨p.1 ∘ f, fun i j ↦ p.2 (f i) (f j)⟩

/-- Reindexing evaluates coordinates by precomposition with `f`. -/
@[simp]
theorem reindex_val_apply (f : Fin m → Fin k) (p : IteratedFiberProduct π k) (i : Fin m) :
    (p.reindex f).1 i = p.1 (f i) :=
  (rfl)

/-- Reindexing along the identity is the identity map. -/
@[simp]
theorem reindex_id : reindex (π := π) (id : Fin k → Fin k) = id :=
  funext fun _ ↦ Subtype.ext rfl

/-- Reindexing is contravariantly functorial in the index map. -/
theorem reindex_comp (f : Fin l → Fin m) (g : Fin m → Fin k) :
    reindex (π := π) f ∘ reindex g = reindex (g ∘ f) :=
  funext fun _ ↦ Subtype.ext rfl

/-- Pointwise functoriality of reindexing. -/
@[simp]
theorem reindex_reindex (f : Fin l → Fin m) (g : Fin m → Fin k) (p : IteratedFiberProduct π k) :
    (p.reindex g).reindex f = p.reindex (g ∘ f) :=
  (rfl)

/-- Reindexing commutes with the base projection to `M`. -/
@[simp]
theorem baseProj_reindex (hm : 1 ≤ m) (f : Fin m → Fin k) (p : IteratedFiberProduct π k) :
    (p.reindex f).baseProj hm = p.baseProj (f ⟨0, hm⟩).pos :=
  p.2 (f ⟨0, hm⟩) ⟨0, (f ⟨0, hm⟩).pos⟩

/-- Reindexing along an injective map `f : Fin m → Fin k` with `1 ≤ m` is surjective, without
assuming surjectivity of `π`: indices outside the range of `f` are filled with a fixed entry of
the given `m`-tuple. -/
theorem reindex_surjective_of_injective (hm : 1 ≤ m) {f : Fin m → Fin k} (hf : Injective f) :
    Surjective (reindex (π := π) f) := by
  classical
  intro q
  let i₀ : Fin m := ⟨0, hm⟩
  refine ⟨⟨fun j ↦ if h : ∃ i, f i = j then q.1 h.choose else q.1 i₀, fun j₁ j₂ ↦ ?_⟩, ?_⟩
  · dsimp only
    split_ifs <;> exact q.2 _ _
  · refine Subtype.ext (funext fun i ↦ ?_)
    simp only [reindex_val_apply]
    split_ifs with h
    · exact congrArg q.1 (hf h.choose_spec)
    · exact (h ⟨i, rfl⟩).elim

/-- The `i`-th face map `Y^[k + 1] → Y^[k]`, omitting coordinate `i`. -/
def face (i : Fin (k + 1)) : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k :=
  reindex i.succAbove

/-- The `i`-th face map acts on coordinates via `Fin.succAbove i`. -/
@[simp]
theorem face_val_apply (i : Fin (k + 1)) (p : IteratedFiberProduct π (k + 1)) (j : Fin k) :
    (p.face i).1 j = p.1 (i.succAbove j) :=
  (rfl)

/-- Every face map commutes with the base projection to `M`. -/
@[simp]
theorem baseProj_face (hk : 1 ≤ k) (i : Fin (k + 1)) (p : IteratedFiberProduct π (k + 1)) :
    (p.face i).baseProj hk = p.baseProj (Nat.le_succ_of_le hk) :=
  baseProj_reindex hk i.succAbove p

/-- For `1 ≤ k`, every face map `Y^[k + 1] → Y^[k]` is surjective. -/
theorem face_surjective (hk : 1 ≤ k) (i : Fin (k + 1)) :
    Surjective (face (π := π) i) :=
  reindex_surjective_of_injective hk (Fin.succAbove_right_injective (p := i))

/-- The `i`-th diagonal degeneracy map `Y^[k] → Y^[k + 1]`, repeating coordinate `i`. -/
def degen (i : Fin k) : IteratedFiberProduct π k → IteratedFiberProduct π (k + 1) :=
  reindex i.predAbove

/-- The `i`-th degeneracy map acts on coordinates via `Fin.predAbove i`. -/
@[simp]
theorem degen_val_apply (i : Fin k) (p : IteratedFiberProduct π k) (j : Fin (k + 1)) :
    (p.degen i).1 j = p.1 (i.predAbove j) :=
  (rfl)

/-- Every degeneracy map commutes with the base projection to `M`. -/
@[simp]
theorem baseProj_degen (i : Fin k) (p : IteratedFiberProduct π k) :
    (p.degen i).baseProj (Nat.le_succ_of_le i.pos) = p.baseProj i.pos :=
  baseProj_reindex (Nat.le_succ_of_le i.pos) i.predAbove p

/-- First simplicial identity: for `i ≤ j`, omitting `j + 1` then `i` agrees with omitting `i`
then `j`. -/
theorem face_comp_face {i j : Fin (k + 1)} (hij : i ≤ j) :
    face (π := π) i ∘ face j.succ = face j ∘ face i.castSucc := by
  cases k with
  | zero =>
    funext p
    exact Subtype.ext (funext fun x ↦ Fin.elim0 x)
  | succ m =>
    funext p
    have h := congrArg SimplexCategory.Hom.toOrderHom (SimplexCategory.δ_comp_δ (n := m) hij)
    exact Subtype.ext (funext fun x ↦ congrArg p.1 (congrFun (congrArg DFunLike.coe h) x))

/-- Fifth simplicial identity: for `i ≤ j`, repeating `j` then `i` agrees with repeating `i`
then `j + 1`. -/
theorem degen_comp_degen {i j : Fin k} (hij : i ≤ j) :
    degen (π := π) i.castSucc ∘ degen j = degen j.succ ∘ degen i := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ m =>
    funext p
    have h := congrArg SimplexCategory.Hom.toOrderHom (SimplexCategory.σ_comp_σ (n := m) hij)
    exact Subtype.ext (funext fun x ↦ congrArg p.1 (congrFun (congrArg DFunLike.coe h) x))

/-- Second simplicial identity: for `i ≤ j`, repeating `j + 1` then omitting `i` agrees with
omitting `i` then repeating `j`. -/
theorem face_comp_degen_of_le {i : Fin (k + 1)} {j : Fin k} (hij : i ≤ j.castSucc) :
    face (π := π) i.castSucc ∘ degen j.succ = degen j ∘ face i := by
  cases k with
  | zero => exact Fin.elim0 j
  | succ m =>
    funext p
    have h := congrArg SimplexCategory.Hom.toOrderHom
      (SimplexCategory.δ_comp_σ_of_le (n := m) hij)
    exact Subtype.ext (funext fun x ↦ congrArg p.1 (congrFun (congrArg DFunLike.coe h) x))

/-- First part of the third simplicial identity: omitting the first copy created by `degen i`
recovers the identity. -/
@[simp]
theorem face_comp_degen_self (i : Fin k) :
    face (π := π) i.castSucc ∘ degen i = id := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ m =>
    funext p
    have h := congrArg SimplexCategory.Hom.toOrderHom
      (SimplexCategory.δ_comp_σ_self (n := m) (i := i))
    exact Subtype.ext (funext fun x ↦ congrArg p.1 (congrFun (congrArg DFunLike.coe h) x))

/-- Pointwise form of `face_comp_degen_self`. -/
@[simp]
theorem face_degen_self (i : Fin k) (p : IteratedFiberProduct π k) :
    (p.degen i).face i.castSucc = p :=
  congrFun (face_comp_degen_self i) p

/-- Second part of the third simplicial identity: omitting the second copy created by `degen i`
recovers the identity. -/
@[simp]
theorem face_comp_degen_succ (i : Fin k) :
    face (π := π) i.succ ∘ degen i = id := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ m =>
    funext p
    have h := congrArg SimplexCategory.Hom.toOrderHom
      (SimplexCategory.δ_comp_σ_succ (n := m) (i := i))
    exact Subtype.ext (funext fun x ↦ congrArg p.1 (congrFun (congrArg DFunLike.coe h) x))

/-- Pointwise form of `face_comp_degen_succ`. -/
@[simp]
theorem face_degen_succ (i : Fin k) (p : IteratedFiberProduct π k) :
    (p.degen i).face i.succ = p :=
  congrFun (face_comp_degen_succ i) p

/-- Fourth simplicial identity: for `j < i`, repeating `j` then omitting `i + 1` agrees with
omitting `i` then repeating `j`. -/
theorem face_comp_degen_of_gt {i : Fin (k + 1)} {j : Fin k} (hji : j.castSucc < i) :
    face (π := π) i.succ ∘ degen j.castSucc = degen j ∘ face i := by
  cases k with
  | zero => exact Fin.elim0 j
  | succ m =>
    funext p
    have h := congrArg SimplexCategory.Hom.toOrderHom
      (SimplexCategory.δ_comp_σ_of_gt (n := m) hji)
    exact Subtype.ext (funext fun x ↦ congrArg p.1 (congrFun (congrArg DFunLike.coe h) x))

end SetLevel

section Topology

variable {Y M : Type*} [TopologicalSpace Y] {π : Y → M}

/-- Homeomorphism identifying `Y^[1]` with the graph fibre product `{q : Y × M // π q.1 = q.2}`. -/
private def oneHomeomorph [TopologicalSpace M] (hπ : Continuous π) :
    IteratedFiberProduct π 1 ≃ₜ {q : Y × M // π q.1 = id q.2} where
  toFun p := ⟨(p.1 0, π (p.1 0)), rfl⟩
  invFun q := ⟨fun _ ↦ q.1.1, fun _ _ ↦ rfl⟩
  left_inv p := Subtype.ext (funext fun i ↦ congrArg p.1 (Fin.eq_zero i).symm)
  right_inv q := Subtype.ext (Prod.ext rfl q.2)
  continuous_toFun :=
    (((continuous_apply (0 : Fin 1)).comp continuous_subtype_val).prodMk
      (hπ.comp ((continuous_apply (0 : Fin 1)).comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun _ ↦ continuous_fst.comp continuous_subtype_val).subtype_mk _

/-- Homeomorphism identifying `Y^[k + 1]` with the binary fibre product `Y^[k] ×_M Y` along the
base projection `baseProj hk` and `π`. -/
private def snocHomeomorph {k : ℕ} (hk : 1 ≤ k) :
    IteratedFiberProduct π (k + 1) ≃ₜ
      {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2} where
  toFun p :=
    ⟨(⟨fun i : Fin k ↦ p.1 i.castSucc, fun i j ↦ p.2 _ _⟩, p.1 (Fin.last k)),
      p.2 (⟨0, hk⟩ : Fin k).castSucc (Fin.last k)⟩
  invFun q :=
    ⟨Fin.snoc q.1.1.1 q.1.2, fun i j ↦ by
      refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · rfl
      · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using
          (q.2.symm.trans (q.1.1.baseProj_eq j'))
      · simpa only [Fin.snoc_last, Fin.snoc_castSucc] using
          ((q.1.1.baseProj_eq i').symm.trans q.2)
      · simpa only [Fin.snoc_castSucc] using q.1.1.2 i' j'⟩
  left_inv p := Subtype.ext <| funext fun i ↦
    Fin.lastCases (by simp [Fin.snoc_last]) (fun j ↦ by simp [Fin.snoc_castSucc]) i
  right_inv q := Subtype.ext <| Prod.ext
    (Subtype.ext (funext fun j ↦ by simp [Fin.snoc_castSucc])) (by simp [Fin.snoc_last])
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact (continuous_pi fun i ↦
        (continuous_apply i.castSucc).comp continuous_subtype_val).subtype_mk _
    · exact (continuous_apply (Fin.last k)).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.snoc_last, Function.comp_def] using continuous_snd.comp continuous_subtype_val
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j).comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))

/-- When `π` is continuous and `M` is Hausdorff, the carrier of the `k`-fold iterated fibre
product is closed in `Fin k → Y`, as the intersection of preimages of the closed diagonal. -/
theorem isClosed_carrier [TopologicalSpace M] [T2Space M] (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} := by
  have heq : {y : Fin k → Y | ∀ i j, π (y i) = π (y j)} =
      ⋂ i : Fin k, ⋂ j : Fin k, {y : Fin k → Y | π (y i) = π (y j)} := by
    ext y
    simp
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (hπ.comp (continuous_apply i)) (hπ.comp (continuous_apply j))

/-- When `π` is continuous and `M` is Hausdorff, the inclusion of `IteratedFiberProduct π k`
into `Fin k → Y` is a closed topological embedding. -/
theorem isClosedEmbedding_val [TopologicalSpace M] [T2Space M] (hπ : Continuous π) (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) :=
  (isClosed_carrier hπ k).isClosedEmbedding_subtypeVal

end Topology

end IteratedFiberProduct

section Transversality

variable {𝕜 EX HX X EY HY Y EN HN N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IX : ModelWithCorners 𝕜 EX HX} {IY : ModelWithCorners 𝕜 EY HY}
  {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω}

/-- Every map into `N` is transverse to a `C^n` submersion (`n ≠ 0`) in the second factor. -/
theorem transverse_isSubmersion_right {f : X → N} {g : Y → N} (hn : n ≠ 0)
    (hg : Manifold.IsSubmersion IY IN n g) (p : X × Y) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  have hs : Surjective (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
      (mfderiv IY IN g p.2)) :=
    (tangentSpaceCast IN (g p.2) (f p.1)).surjective.comp (hg.surjective_mfderiv hn p.2)
  rw [LinearMap.range_eq_top.2 hs, sup_top_eq]

end Transversality

namespace IteratedFiberProduct

section ManifoldConstruction

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  {π : Y → M}

/-- Existence statement for an embedded `C^n` manifold structure of dimension `d` on
`IteratedFiberProduct π k`, factored out to transport across equal model dimensions. -/
private abbrev HasEmbeddedManifold (IY : ModelWithCorners ℝ EY HY) (IM : ModelWithCorners ℝ EM HM)
    (n : ℕ∞ω) (π : Y → M) (k d : ℕ) : Prop :=
  ∃ cs : ChartedSpace (Fin d → ℝ) (IteratedFiberProduct π k),
    letI := cs
    IsManifold 𝓘(ℝ, Fin d → ℝ) n (IteratedFiberProduct π k) ∧
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
      (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) ∧
    ∀ (p : IteratedFiberProduct π k)
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) p.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
        (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p).range ↔
      ∀ i j : Fin k,
        mfderiv IY IM π (p.1 i) (v i) =
          tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j))

private theorem iteratedDim_succ {k dY dM : ℕ} (hk : 1 ≤ k) (hle : dM ≤ dY) :
    (k * dY - (k - 1) * dM) + dY - dM = (k + 1) * dY - k * dM := by
  have h1 : (k - 1) * dM ≤ k * dY :=
    (Nat.mul_le_mul_left _ hle).trans (Nat.mul_le_mul_right _ (Nat.sub_le k 1))
  have h2 : k * dM ≤ (k + 1) * dY :=
    (Nat.mul_le_mul_left _ hle).trans (Nat.mul_le_mul_right _ (Nat.le_succ k))
  have h3 : (k - 1) * dM + dM = k * dM := by
    cases k with
    | zero => omega
    | succ m => simp [Nat.add_mul]
  have h4 : k * dY + dY = (k + 1) * dY := by simp [Nat.add_mul]
  omega

omit [TopologicalSpace M] [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless]
  [IM.Boundaryless] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] in
/-- For any charted structure on `Y^[k]` making `Subtype.val` differentiable at `p`, the
differential of the `i`-th coordinate projection is the `i`-th component of `d(Subtype.val)`. -/
private theorem mfderiv_coord_of_mdifferentiableAt_val {k d : ℕ}
    [ChartedSpace (Fin d → ℝ) (IteratedFiberProduct π k)] {p : IteratedFiberProduct π k}
    (hval : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
      (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p)
    (i : Fin k) (ξ : TangentSpace 𝓘(ℝ, Fin d → ℝ) p) :
    mfderiv 𝓘(ℝ, Fin d → ℝ) IY (fun q : IteratedFiberProduct π k ↦ q.1 i) p ξ =
      mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
        (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p ξ i := by
  have hcomp := mfderiv_comp p
    (hasMFDerivAt_apply (I := fun _ : Fin k ↦ IY) i p.1).mdifferentiableAt hval
  have happly := DFunLike.congr_fun hcomp ξ
  rw [ContinuousLinearMap.comp_apply, mfderiv_apply] at happly
  exact happly

omit [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] in
/-- Differential of `baseProj hk` in terms of `dπ` applied to the zeroth component of
`d(Subtype.val)`. -/
private theorem mfderiv_baseProj_of_mdifferentiableAt_val {k d : ℕ} (hk : 1 ≤ k)
    [ChartedSpace (Fin d → ℝ) (IteratedFiberProduct π k)] {q : IteratedFiberProduct π k}
    (hπd : MDifferentiableAt IY IM π (q.1 ⟨0, hk⟩))
    (hval : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
      (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) q)
    (u : TangentSpace 𝓘(ℝ, Fin d → ℝ) q) :
    mfderiv 𝓘(ℝ, Fin d → ℝ) IM (baseProj hk) q u =
      mfderiv IY IM π (q.1 ⟨0, hk⟩)
        (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
          (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) q u ⟨0, hk⟩) := by
  have hbase_eq : baseProj (π := π) hk = π ∘ fun r : IteratedFiberProduct π k ↦ r.1 ⟨0, hk⟩ :=
    funext fun _ ↦ baseProj_apply hk _
  have h0 : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) IY
      (fun r : IteratedFiberProduct π k ↦ r.1 ⟨0, hk⟩) q :=
    (hasMFDerivAt_apply (I := fun _ : Fin k ↦ IY) ⟨0, hk⟩ q.1).mdifferentiableAt.comp q hval
  have hcomp := mfderiv_comp q hπd h0
  rw [hbase_eq]
  have happly := DFunLike.congr_fun hcomp u
  rw [ContinuousLinearMap.comp_apply,
    mfderiv_coord_of_mdifferentiableAt_val hval ⟨0, hk⟩ u] at happly
  exact happly

omit [IsManifold IM n M] [IM.Boundaryless] [FiniteDimensional ℝ EM] in
private theorem hasEmbeddedManifold_zero (hn : 1 ≤ n) :
    HasEmbeddedManifold IY IM n π 0 (0 * finrank ℝ EY - (0 - 1) * finrank ℝ EM) := by
  have hdim : 0 = 0 * finrank ℝ EY - (0 - 1) * finrank ℝ EM := by simp
  rw [← hdim]
  let e₀ : IteratedFiberProduct π 0 ≃ₜ (Fin 0 → ℝ) :=
    { toFun := fun _ ↦ Fin.elim0
      invFun := fun _ ↦ ⟨Fin.elim0, fun i ↦ i.elim0⟩
      left_inv := fun p ↦ Subtype.ext (funext fun i ↦ i.elim0)
      right_inv := fun _ ↦ funext fun i ↦ i.elim0
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  let := e₀.pullbackChartedSpace (H := Fin 0 → ℝ)
  have : IsManifold 𝓘(ℝ, Fin 0 → ℝ) n (IteratedFiberProduct π 0) :=
    e₀.pullback_isManifold 𝓘(ℝ, Fin 0 → ℝ) n
  have hval : ContMDiff 𝓘(ℝ, Fin 0 → ℝ) (ModelWithCorners.pi fun _ : Fin 0 ↦ IY) n
      (Subtype.val : IteratedFiberProduct π 0 → (Fin 0 → Y)) :=
    contMDiff_pi_iff.2 fun i ↦ i.elim0
  have hImm : Manifold.IsImmersion 𝓘(ℝ, Fin 0 → ℝ) (ModelWithCorners.pi fun _ : Fin 0 ↦ IY) n
      (Subtype.val : IteratedFiberProduct π 0 → (Fin 0 → Y)) :=
    hval.isImmersion_of_injective_mfderiv hn fun _ _ _ _ ↦ funext fun i ↦ i.elim0
  exact ⟨inferInstance, inferInstance, ⟨hImm, IsEmbedding.subtypeVal⟩,
    fun _ _ ↦ ⟨fun _ i ↦ i.elim0, fun _ ↦ ⟨0, funext fun i ↦ i.elim0⟩⟩⟩

omit [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EM] in
private theorem hasEmbeddedManifold_of_isEmpty {k d : ℕ} (hEmpty : IsEmpty Y) (hk : 1 ≤ k) :
    HasEmbeddedManifold IY IM n π k d := by
  have : IsEmpty (IteratedFiberProduct π k) := ⟨fun p ↦ hEmpty.false (p.1 ⟨0, hk⟩)⟩
  let cs : ChartedSpace (Fin d → ℝ) (IteratedFiberProduct π k) :=
    { atlas := ∅
      chartAt := fun p ↦ IsEmpty.elim inferInstance p
      mem_chart_source := fun p ↦ IsEmpty.elim inferInstance p
      chart_mem_atlas := fun p ↦ IsEmpty.elim inferInstance p }
  let := cs
  have : HasGroupoid (IteratedFiberProduct π k) (contDiffGroupoid n 𝓘(ℝ, Fin d → ℝ)) :=
    ⟨fun h _ ↦ False.elim h⟩
  refine ⟨cs, { },
    ⟨isImmersion_iff_forall_isImmersionAt.2 (fun p ↦ IsEmpty.elim inferInstance p),
      IsEmbedding.subtypeVal⟩,
    fun p ↦ IsEmpty.elim inferInstance p⟩

omit [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EM] in
private theorem finrank_le_of_isSubmersion [Nonempty Y] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    finrank ℝ EM ≤ finrank ℝ EY := by
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  exact LinearMap.finrank_le_finrank_of_surjective (hπ.surjective_mfderiv hn0 y₀)

private theorem hasEmbeddedManifold_one (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π) :
    HasEmbeddedManifold IY IM n π 1 (1 * finrank ℝ EY - (1 - 1) * finrank ℝ EM) := by
  have hdim : finrank ℝ EY + finrank ℝ EM - finrank ℝ EM =
      1 * finrank ℝ EY - (1 - 1) * finrank ℝ EM := by simp
  rw [← hdim]
  let Q₁ := {q : Y × M // π q.1 = id q.2}
  let d₁ := finrank ℝ EY + finrank ℝ EM - finrank ℝ EM
  let := transverseFiberProductChartedSpace hn hπ.contMDiff (contMDiff_id (I := IM))
    (fun p _ ↦ transverse_id_right π p)
  have : IsManifold 𝓘(ℝ, Fin d₁ → ℝ) n Q₁ :=
    isManifold_transverseFiberProduct hn hπ.contMDiff (contMDiff_id (I := IM))
      (fun p _ ↦ transverse_id_right π p)
  let e₁ := oneHomeomorph hπ.contMDiff.continuous
  let := e₁.pullbackChartedSpace (H := Fin d₁ → ℝ)
  have : IsManifold 𝓘(ℝ, Fin d₁ → ℝ) n (IteratedFiberProduct π 1) :=
    e₁.pullback_isManifold 𝓘(ℝ, Fin d₁ → ℝ) n
  let Φ₁ := (e₁.pullbackDiffeomorph 𝓘(ℝ, Fin d₁ → ℝ) n).trans
    (transverseFiberProductIdRightDiffeomorph hn hπ.contMDiff)
  let Ψ₁ : Y ≃ₘ^n⟮IY, ModelWithCorners.pi fun _ : Fin 1 ↦ IY⟯ (Fin 1 → Y) :=
    { toFun := fun y _ ↦ y
      invFun := fun f ↦ f 0
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun i ↦ congrArg f (Fin.eq_zero i).symm
      contMDiff_toFun := contMDiff_pi_iff.2 fun _ ↦ contMDiff_id
      contMDiff_invFun := contMDiff_apply }
  let D := Φ₁.trans Ψ₁
  have hD : (D : IteratedFiberProduct π 1 → (Fin 1 → Y)) = Subtype.val := by
    funext p i
    have h2 : D p i = (transverseFiberProductIdRightDiffeomorph hn hπ.contMDiff)
        ((e₁.pullbackDiffeomorph 𝓘(ℝ, Fin d₁ → ℝ) n) p) := rfl
    rw [h2, e₁.coe_pullbackDiffeomorph, transverseFiberProductIdRightDiffeomorph_apply]
    exact congrArg p.1 (Fin.eq_zero i).symm
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hImm : Manifold.IsImmersion 𝓘(ℝ, Fin d₁ → ℝ) (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n
      (Subtype.val : IteratedFiberProduct π 1 → (Fin 1 → Y)) := by
    rw [← hD]
    exact D.contMDiff.isImmersion_of_injective_mfderiv hn fun p ↦ by
      rw [← D.mfderivToContinuousLinearEquiv_coe hn0]
      exact (D.mfderivToContinuousLinearEquiv hn0 p).injective
  refine ⟨inferInstance, inferInstance, ⟨hImm, IsEmbedding.subtypeVal⟩, fun p v ↦
    ⟨fun _ i j ↦ by rw [Subsingleton.elim i j]; rfl, fun _ ↦ ?_⟩⟩
  rw [← hD, ← D.mfderivToContinuousLinearEquiv_coe hn0]
  exact (D.mfderivToContinuousLinearEquiv hn0 p).surjective v

section SuccStep

variable {k d : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
  [ChartedSpace (Fin d → ℝ) (IteratedFiberProduct π k)]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) n (IteratedFiberProduct π k)]
  (hembk : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
    (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)))
  (hbase : ContMDiff 𝓘(ℝ, Fin d → ℝ) IM n (baseProj (π := π) hk))
  (htrans : ∀ q : IteratedFiberProduct π k × Y, q.1.baseProj hk = π q.2 →
    (mfderiv 𝓘(ℝ, Fin d → ℝ) IM (baseProj hk) q.1).range ⊔
      (((tangentSpaceCast IM (π q.2) (q.1.baseProj hk)).toContinuousLinearMap).comp
        (mfderiv IY IM π q.2)).range = ⊤)

include hembk

/-- Coordinate differentials of `Subtype.val : Y^[k + 1] → (Fin (k + 1) → Y)` under the pulled-back
chart structure from `Y^[k] ×_M Y`. -/
private theorem hasEmbeddedManifold_succ_coord :
    let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
    let Q := {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2}
    letI := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
    let e := snocHomeomorph (π := π) hk
    letI := e.pullbackChartedSpace (H := Fin d' → ℝ)
    ContMDiff 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) ∧
    ∀ (p : IteratedFiberProduct π (k + 1)) (ξ : TangentSpace 𝓘(ℝ, Fin d' → ℝ) p),
      let η := mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p ξ
      let u := mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d → ℝ) (fun q : Q ↦ q.1.1) (e p) η
      let w := mfderiv 𝓘(ℝ, Fin d' → ℝ) IY (fun q : Q ↦ q.1.2) (e p) η
      (∀ j : Fin k, mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) p ξ j.castSucc =
        mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
          (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) (e p).1.1 u j) ∧
      mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) p ξ (Fin.last k) =
        w := by
  let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
  let Q := {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2}
  let := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
  have hembQ := isSmoothEmbedding_coe_transverseFiberProduct hn hbase hπ.contMDiff htrans
  let e := snocHomeomorph (π := π) hk
  let := e.pullbackChartedSpace (H := Fin d' → ℝ)
  let Φ := e.pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
  have hΦe : ⇑Φ = ⇑e := e.coe_pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hval : ContMDiff 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) := by
    refine contMDiff_pi_iff.2 fun i ↦ Fin.lastCases ?_ (fun j ↦ ?_) i
    · have h := hembQ.contMDiff.snd.comp Φ.contMDiff
      rwa [hΦe] at h
    · have h := ((contMDiff_apply (i := j)).comp hembk.contMDiff).comp
        (hembQ.contMDiff.fst.comp Φ.contMDiff)
      rwa [hΦe] at h
  refine ⟨hval, fun p ξ ↦ ?_⟩
  have hΦd : MDifferentiableAt 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p :=
    hΦe ▸ Φ.mdifferentiable hn0 p
  have hfst : MDifferentiableAt 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d → ℝ) (fun q : Q ↦ q.1.1) (e p) :=
    (hembQ.contMDiff.fst (e p)).mdifferentiableAt hn0
  have hsnd : MDifferentiableAt 𝓘(ℝ, Fin d' → ℝ) IY (fun q : Q ↦ q.1.2) (e p) :=
    (hembQ.contMDiff.snd (e p)).mdifferentiableAt hn0
  have hvalk := (hembk.contMDiff (e p).1.1).mdifferentiableAt hn0
  have hvald := (hval p).mdifferentiableAt hn0
  constructor
  · intro j
    rw [← mfderiv_coord_of_mdifferentiableAt_val hvald j.castSucc ξ,
      ← mfderiv_coord_of_mdifferentiableAt_val hvalk j]
    have hgj : MDifferentiableAt 𝓘(ℝ, Fin d → ℝ) IY
        (fun q : IteratedFiberProduct π k ↦ q.1 j) (e p).1.1 :=
      (hasMFDerivAt_apply (I := fun _ : Fin k ↦ IY) j (e p).1.1.1).mdifferentiableAt.comp
        (e p).1.1 hvalk
    have h1 := DFunLike.congr_fun (mfderiv_comp p (hgj.comp (e p) hfst) hΦd) ξ
    have h2 := DFunLike.congr_fun (mfderiv_comp (e p) hgj hfst)
      (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p ξ)
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at h1 h2
    exact h1.trans h2
  · rw [← mfderiv_coord_of_mdifferentiableAt_val hvald (Fin.last k) ξ]
    have h1 := DFunLike.congr_fun (mfderiv_comp p hsnd hΦd) ξ
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at h1
    exact h1

/-- Forward direction of the tangent-image characterisation at `k + 1`. -/
private theorem hasEmbeddedManifold_succ_range_mp
    (hrangek : ∀ (p : IteratedFiberProduct π k)
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) p.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
        (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p).range ↔
      ∀ i j : Fin k, mfderiv IY IM π (p.1 i) (v i) =
        tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j))) :
    let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
    letI := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
    letI := (snocHomeomorph (π := π) hk).pullbackChartedSpace (H := Fin d' → ℝ)
    ∀ (p : IteratedFiberProduct π (k + 1)) (ξ : TangentSpace 𝓘(ℝ, Fin d' → ℝ) p)
      (i j : Fin (k + 1)),
      mfderiv IY IM π (p.1 i)
        (mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) p ξ i) =
      tangentSpaceCast IM (π (p.1 j)) (π (p.1 i))
        (mfderiv IY IM π (p.1 j)
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
            (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) p ξ j)) := by
  intro d' p ξ
  let Q := {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2}
  let := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
  let e := snocHomeomorph (π := π) hk
  let := e.pullbackChartedSpace (H := Fin d' → ℝ)
  have hembQ := isSmoothEmbedding_coe_transverseFiberProduct hn hbase hπ.contMDiff htrans
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  obtain ⟨_, hcoord⟩ := hasEmbeddedManifold_succ_coord hk hn hπ hembk hbase htrans
  obtain ⟨hc1, hc2⟩ := hcoord p ξ
  set η := mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p ξ
  set u := mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d → ℝ) (fun q : Q ↦ q.1.1) (e p) η
  set w := mfderiv 𝓘(ℝ, Fin d' → ℝ) IY (fun q : Q ↦ q.1.2) (e p) η
  have hQpair : mfderiv 𝓘(ℝ, Fin d → ℝ) IM (baseProj hk) (e p).1.1 u =
      tangentSpaceCast IM (π (e p).1.2) ((e p).1.1.baseProj hk) (mfderiv IY IM π (e p).1.2 w) := by
    have hvalQ := (hembQ.contMDiff (e p)).mdifferentiableAt hn0
    have hmem := (mem_range_mfderiv_coe_transverseFiberProduct_iff hn hbase hπ.contMDiff htrans
      (e p) (mfderiv 𝓘(ℝ, Fin d' → ℝ) (𝓘(ℝ, Fin d → ℝ).prod IY) Subtype.val (e p) η)).1 ⟨η, rfl⟩
    rw [← hvalQ.mfderiv_fst_apply η, ← hvalQ.mfderiv_snd_apply η] at hmem
    exact hmem
  have hmatch_k := (hrangek (e p).1.1 (mfderiv 𝓘(ℝ, Fin d → ℝ)
    (ModelWithCorners.pi fun _ : Fin k ↦ IY) Subtype.val (e p).1.1 u)).1 ⟨u, rfl⟩
  have hbd := mfderiv_baseProj_of_mdifferentiableAt_val hk
    ((hπ.contMDiff ((e p).1.1.1 ⟨0, hk⟩)).mdifferentiableAt hn0)
    ((hembk.contMDiff (e p).1.1).mdifferentiableAt hn0) u
  have hall : ∀ i : Fin (k + 1),
      mfderiv IY IM π (p.1 i)
        (mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
          Subtype.val p ξ i) =
      tangentSpaceCast IM (π (p.1 (⟨0, hk⟩ : Fin k).castSucc)) (π (p.1 i))
        (mfderiv IY IM π (p.1 (⟨0, hk⟩ : Fin k).castSucc)
          (mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
            Subtype.val p ξ (⟨0, hk⟩ : Fin k).castSucc)) := by
    intro i
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · rw [hc1 ⟨0, hk⟩, hc2]
      exact (hbd.symm.trans hQpair).symm
    · rw [hc1 i', hc1 ⟨0, hk⟩]
      exact hmatch_k i' ⟨0, hk⟩
  intro i j
  rw [hall i, hall j]
  rfl

/-- Converse direction of the tangent-image characterisation at `k + 1`. -/
private theorem hasEmbeddedManifold_succ_range_mpr
    (hrangek : ∀ (p : IteratedFiberProduct π k)
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) p.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin d → ℝ) (ModelWithCorners.pi fun _ : Fin k ↦ IY)
        (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p).range ↔
      ∀ i j : Fin k, mfderiv IY IM π (p.1 i) (v i) =
        tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j))) :
    let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
    letI := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
    letI := (snocHomeomorph (π := π) hk).pullbackChartedSpace (H := Fin d' → ℝ)
    ∀ (p : IteratedFiberProduct π (k + 1))
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) p.1),
      (∀ i j : Fin (k + 1), mfderiv IY IM π (p.1 i) (v i) =
        tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j))) →
      v ∈ (mfderiv 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY)
        (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) p).range := by
  intro d' p v hv
  let Q := {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2}
  let := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
  have : IsManifold 𝓘(ℝ, Fin d' → ℝ) n Q :=
    isManifold_transverseFiberProduct hn hbase hπ.contMDiff htrans
  let e := snocHomeomorph (π := π) hk
  let := e.pullbackChartedSpace (H := Fin d' → ℝ)
  have : IsManifold 𝓘(ℝ, Fin d' → ℝ) n (IteratedFiberProduct π (k + 1)) :=
    e.pullback_isManifold 𝓘(ℝ, Fin d' → ℝ) n
  let Φ := e.pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
  have hΦe : ⇑Φ = ⇑e := e.coe_pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  obtain ⟨_, hcoord⟩ := hasEmbeddedManifold_succ_coord hk hn hπ hembk hbase htrans
  obtain ⟨u, hu⟩ := (hrangek (e p).1.1 (fun j : Fin k ↦ v j.castSucc)).2
    fun i j ↦ hv i.castSucc j.castSucc
  simp only [ContinuousLinearMap.coe_coe] at hu
  have hbd := mfderiv_baseProj_of_mdifferentiableAt_val hk
    ((hπ.contMDiff ((e p).1.1.1 ⟨0, hk⟩)).mdifferentiableAt hn0)
    ((hembk.contMDiff (e p).1.1).mdifferentiableAt hn0) u
  have huw : mfderiv 𝓘(ℝ, Fin d → ℝ) IM (baseProj hk) (e p).1.1 u =
      tangentSpaceCast IM (π (e p).1.2) ((e p).1.1.baseProj hk)
        (mfderiv IY IM π (e p).1.2 (v (Fin.last k))) := by
    rw [hbd, hu]
    exact hv (⟨0, hk⟩ : Fin k).castSucc (Fin.last k)
  obtain ⟨η, hη1, hη2⟩ := exists_mfderiv_eq_of_transverseFiberProduct hn hbase hπ.contMDiff
    htrans (e p) u (v (Fin.last k)) huw
  let ξ := (Φ.mfderivToContinuousLinearEquiv hn0 p).symm η
  have hΦξ : mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p ξ = η := by
    rw [← hΦe, ← Φ.mfderivToContinuousLinearEquiv_coe hn0]
    exact (Φ.mfderivToContinuousLinearEquiv hn0 p).apply_symm_apply η
  refine ⟨ξ, ?_⟩
  simp only [ContinuousLinearMap.coe_coe]
  funext i
  obtain ⟨hc1, hc2⟩ := hcoord p ξ
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [hc2, hΦξ, hη2]
  · rw [hc1 j, hΦξ, hη1, hu]

/-- The inclusion `Subtype.val : Y^[k + 1] → (Fin (k + 1) → Y)` is a `C^n` immersion. -/
private theorem hasEmbeddedManifold_succ_isImmersion :
    let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
    letI := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
    letI := (snocHomeomorph (π := π) hk).pullbackChartedSpace (H := Fin d' → ℝ)
    Manifold.IsImmersion 𝓘(ℝ, Fin d' → ℝ) (ModelWithCorners.pi fun _ : Fin (k + 1) ↦ IY) n
      (Subtype.val : IteratedFiberProduct π (k + 1) → (Fin (k + 1) → Y)) := by
  let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
  let Q := {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2}
  let := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
  have : IsManifold 𝓘(ℝ, Fin d' → ℝ) n Q :=
    isManifold_transverseFiberProduct hn hbase hπ.contMDiff htrans
  let e := snocHomeomorph (π := π) hk
  let := e.pullbackChartedSpace (H := Fin d' → ℝ)
  have : IsManifold 𝓘(ℝ, Fin d' → ℝ) n (IteratedFiberProduct π (k + 1)) :=
    e.pullback_isManifold 𝓘(ℝ, Fin d' → ℝ) n
  let Φ := e.pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
  have hΦe : ⇑Φ = ⇑e := e.coe_pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  obtain ⟨hval, hcoord⟩ := hasEmbeddedManifold_succ_coord hk hn hπ hembk hbase htrans
  refine hval.isImmersion_of_injective_mfderiv hn fun p ↦ (injective_iff_map_eq_zero _).2
    fun ξ hξ ↦ ?_
  obtain ⟨hc1, hc2⟩ := hcoord p ξ
  have hu : mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d → ℝ) (fun q : Q ↦ q.1.1) (e p)
      (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p ξ) = 0 :=
    (injective_iff_map_eq_zero _).1
      ((hembk.isImmersion.isImmersionAt (e p).1.1).mfderiv_injective hn0) _
      (funext fun j ↦ by rw [← hc1 j, hξ]; rfl)
  have hw : mfderiv 𝓘(ℝ, Fin d' → ℝ) IY (fun q : Q ↦ q.1.2) (e p)
      (mfderiv 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) e p ξ) = 0 := by
    rw [← hc2, hξ]; rfl
  have hη := eq_zero_of_mfderiv_transverseFiberProduct hn hbase hπ.contMDiff htrans (e p) _ hu hw
  rw [← hΦe, ← Φ.mfderivToContinuousLinearEquiv_coe hn0] at hη
  exact (injective_iff_map_eq_zero _).1 (Φ.mfderivToContinuousLinearEquiv hn0 p).injective ξ hη

end SuccStep

private theorem hasEmbeddedManifold_succ {k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (hle : finrank ℝ EM ≤ finrank ℝ EY)
    (ih : HasEmbeddedManifold IY IM n π k (k * finrank ℝ EY - (k - 1) * finrank ℝ EM)) :
    HasEmbeddedManifold IY IM n π (k + 1)
      ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) := by
  let d := k * finrank ℝ EY - (k - 1) * finrank ℝ EM
  let d' := finrank ℝ (Fin d → ℝ) + finrank ℝ EY - finrank ℝ EM
  have hdim : d' = (k + 1) * finrank ℝ EY - k * finrank ℝ EM := by
    dsimp [d', d]
    rw [Module.finrank_fin_fun]
    exact iteratedDim_succ hk hle
  rw [← hdim]
  obtain ⟨csk, hMk, hembk, hrangek⟩ := ih
  let := csk
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hbase : ContMDiff 𝓘(ℝ, Fin d → ℝ) IM n (baseProj (π := π) hk) :=
    hπ.contMDiff.comp ((contMDiff_apply (i := (⟨0, hk⟩ : Fin k))).comp hembk.contMDiff)
  have htrans : ∀ q : IteratedFiberProduct π k × Y, q.1.baseProj hk = π q.2 →
      (mfderiv 𝓘(ℝ, Fin d → ℝ) IM (baseProj hk) q.1).range ⊔
        (((tangentSpaceCast IM (π q.2) (q.1.baseProj hk)).toContinuousLinearMap).comp
          (mfderiv IY IM π q.2)).range = ⊤ :=
    fun q _ ↦ transverse_isSubmersion_right hn0 hπ q
  let := transverseFiberProductChartedSpace hn hbase hπ.contMDiff htrans
  have : IsManifold 𝓘(ℝ, Fin d' → ℝ) n
      {q : IteratedFiberProduct π k × Y // q.1.baseProj hk = π q.2} :=
    isManifold_transverseFiberProduct hn hbase hπ.contMDiff htrans
  let e := snocHomeomorph (π := π) hk
  let := e.pullbackChartedSpace (H := Fin d' → ℝ)
  have : IsManifold 𝓘(ℝ, Fin d' → ℝ) n (IteratedFiberProduct π (k + 1)) :=
    e.pullback_isManifold 𝓘(ℝ, Fin d' → ℝ) n
  refine ⟨inferInstance, inferInstance,
    ⟨hasEmbeddedManifold_succ_isImmersion hk hn hπ hembk hbase htrans, IsEmbedding.subtypeVal⟩,
    fun p v ↦ ⟨?_, hasEmbeddedManifold_succ_range_mpr hk hn hπ hembk hbase htrans hrangek p v⟩⟩
  rintro ⟨ξ, hξ⟩
  simp only [ContinuousLinearMap.coe_coe] at hξ
  subst hξ
  exact hasEmbeddedManifold_succ_range_mp hk hn hπ hembk hbase htrans hrangek p ξ

/-- **Iterated submersion fibre-product theorem.** For a `C^n` submersion `π : Y → M` (`1 ≤ n`)
between finite-dimensional boundaryless real manifolds and any `k : ℕ`, the `k`-fold iterated fibre
product `IteratedFiberProduct π k` admits a `C^n` manifold structure of dimension
`k * dim Y - (k - 1) * dim M` with its subspace topology, smoothly embedded in `Fin k → Y`,
whose tangent space consists of `k`-tuples with matching images under `dπ`. -/
theorem exists_isManifold_isSmoothEmbedding (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (k : ℕ) :
    ∃ cs : ChartedSpace (Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π k),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) n
        (IteratedFiberProduct π k) ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
        (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) ∧
      ∀ (p : IteratedFiberProduct π k)
        (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) p.1),
        v ∈ (mfderiv 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin k ↦ IY)
          (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p).range ↔
        ∀ i j : Fin k,
          mfderiv IY IM π (p.1 i) (v i) =
            tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j)) := by
  cases k with
  | zero => exact hasEmbeddedManifold_zero hn
  | succ m =>
    by_cases hY : Nonempty Y
    · have hle := finrank_le_of_isSubmersion hn hπ
      induction m with
      | zero => exact hasEmbeddedManifold_one hn hπ
      | succ l ih => exact hasEmbeddedManifold_succ (Nat.succ_pos l) hn hπ hle ih
    · exact hasEmbeddedManifold_of_isEmpty (not_nonempty_iff.mp hY) (Nat.succ_pos m)

variable (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- A fixed atlas on the `k`-fold iterated fibre product of a `C^n` submersion (`1 ≤ n`),
chosen from the iterative transverse fibre-product construction. It uses the subspace topology
and is not a global instance. -/
@[instance_reducible]
noncomputable def chartedSpace (k : ℕ) :
    ChartedSpace (Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π k) :=
  (exists_isManifold_isSmoothEmbedding hn hπ k).choose

/-- The `k`-fold iterated fibre product with its chosen atlas is a `C^n` manifold. -/
theorem isManifold (k : ℕ) :
    letI := chartedSpace hn hπ k
    IsManifold 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct π k) :=
  (exists_isManifold_isSmoothEmbedding hn hπ k).choose_spec.1

/-- The inclusion of the `k`-fold iterated fibre product into `Fin k → Y` is a `C^n` smooth
embedding. -/
theorem isSmoothEmbedding_val (k : ℕ) :
    letI := chartedSpace hn hπ k
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
      (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
      (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) :=
  (exists_isManifold_isSmoothEmbedding hn hπ k).choose_spec.2.1

/-- A tangent vector of `Fin k → Y` lies in the tangent image of `IteratedFiberProduct π k`
exactly when all of its components have equal images under `dπ`. -/
theorem mem_range_mfderiv_val_iff (k : ℕ) :
    letI := chartedSpace hn hπ k
    ∀ (p : IteratedFiberProduct π k)
      (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) p.1),
      v ∈ (mfderiv 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
        (ModelWithCorners.pi fun _ : Fin k ↦ IY)
        (Subtype.val : IteratedFiberProduct π k → (Fin k → Y)) p).range ↔
      ∀ i j : Fin k,
        mfderiv IY IM π (p.1 i) (v i) =
          tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j)) :=
  (exists_isManifold_isSmoothEmbedding hn hπ k).choose_spec.2.2

/-- Every `k`-tuple of tangent vectors with equal images under `dπ` is the tuple of derivatives
of the coordinate projections at some tangent vector of `IteratedFiberProduct π k`. -/
theorem exists_mfderiv_eq (k : ℕ) :
    letI := chartedSpace hn hπ k
    ∀ (p : IteratedFiberProduct π k) (v : ∀ i : Fin k, TangentSpace IY (p.1 i)),
      (∀ i j : Fin k, mfderiv IY IM π (p.1 i) (v i) =
        tangentSpaceCast IM (π (p.1 j)) (π (p.1 i)) (mfderiv IY IM π (p.1 j) (v j))) →
      ∃ ξ, ∀ i : Fin k,
        mfderiv 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IY
          (fun q : IteratedFiberProduct π k ↦ q.1 i) p ξ = v i := by
  let := chartedSpace hn hπ k
  intro p v hv
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hval := ((isSmoothEmbedding_val hn hπ k).contMDiff p).mdifferentiableAt hn0
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_val_iff hn hπ k p v).2 hv
  simp only [ContinuousLinearMap.coe_coe] at hξ
  refine ⟨ξ, fun i ↦ ?_⟩
  rw [mfderiv_coord_of_mdifferentiableAt_val hval i ξ, hξ]

/-- A tangent vector of `IteratedFiberProduct π k` is zero when the differentials of all
coordinate projections vanish on it. -/
theorem eq_zero_of_mfderiv (k : ℕ) :
    letI := chartedSpace hn hπ k
    ∀ (p : IteratedFiberProduct π k)
      (ξ : TangentSpace 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) p),
      (∀ i : Fin k,
        mfderiv 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IY
          (fun q : IteratedFiberProduct π k ↦ q.1 i) p ξ = 0) →
      ξ = 0 := by
  let := chartedSpace hn hπ k
  intro p ξ hξ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hi := isSmoothEmbedding_val hn hπ k
  have hval := (hi.contMDiff p).mdifferentiableAt hn0
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt p).mfderiv_injective hn0)
    ξ (funext fun i ↦ ?_)
  rw [← mfderiv_coord_of_mdifferentiableAt_val hval i ξ]
  exact hξ i

/-- Every coordinate projection `Y^[k] → Y` is `C^n`. -/
theorem contMDiff_coord {k : ℕ} (i : Fin k) :
    letI := chartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IY n
      (fun p : IteratedFiberProduct π k ↦ p.1 i) := by
  let := chartedSpace hn hπ k
  exact (contMDiff_apply (i := i)).comp (isSmoothEmbedding_val hn hπ k).contMDiff

/-- The base projection `Y^[k] → M` (`1 ≤ k`) is `C^n`. -/
theorem contMDiff_baseProj {k : ℕ} (hk : 1 ≤ k) :
    letI := chartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IM n
      (baseProj (π := π) hk) := by
  let := chartedSpace hn hπ k
  exact hπ.contMDiff.comp (contMDiff_coord hn hπ (⟨0, hk⟩ : Fin k))

/-- Every reindexing map `Y^[k] → Y^[m]` is `C^n`. -/
theorem contMDiff_reindex {m k : ℕ} (f : Fin m → Fin k) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ m
    ContMDiff 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin (m * finrank ℝ EY - (m - 1) * finrank ℝ EM) → ℝ) n
      (reindex (π := π) f) := by
  let := chartedSpace hn hπ k
  let := chartedSpace hn hπ m
  exact (isSmoothEmbedding_val hn hπ m).contMDiff_iff_comp.2 <|
    contMDiff_pi_iff.2 fun i ↦ contMDiff_coord hn hπ (f i)

/-- Every face map `Y^[k + 1] → Y^[k]` is `C^n`. -/
theorem contMDiff_face {k : ℕ} (i : Fin (k + 1)) :
    letI := chartedSpace hn hπ (k + 1)
    letI := chartedSpace hn hπ k
    ContMDiff 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - (k + 1 - 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) n
      (face (π := π) i) :=
  contMDiff_reindex hn hπ i.succAbove

/-- Every degeneracy map `Y^[k] → Y^[k + 1]` is `C^n`. -/
theorem contMDiff_degen {k : ℕ} (i : Fin k) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ (k + 1)
    ContMDiff 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - (k + 1 - 1) * finrank ℝ EM) → ℝ) n
      (degen (π := π) i) :=
  contMDiff_reindex hn hπ i.predAbove

/-- Composing the differential of a coordinate projection with the differential of `reindex f`
gives the differential of the `(f i)`-th coordinate projection. -/
theorem mfderiv_coord_reindex {m k : ℕ} (f : Fin m → Fin k) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ m
    ∀ (p : IteratedFiberProduct π k)
      (ξ : TangentSpace 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) p) (i : Fin m),
      mfderiv 𝓘(ℝ, Fin (m * finrank ℝ EY - (m - 1) * finrank ℝ EM) → ℝ) IY
          (fun q : IteratedFiberProduct π m ↦ q.1 i) (p.reindex f)
          (mfderiv 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
            𝓘(ℝ, Fin (m * finrank ℝ EY - (m - 1) * finrank ℝ EM) → ℝ) (reindex (π := π) f) p ξ) =
        mfderiv 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IY
          (fun q : IteratedFiberProduct π k ↦ q.1 (f i)) p ξ := by
  let := chartedSpace hn hπ k
  let := chartedSpace hn hπ m
  intro p ξ i
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have h1 := ((contMDiff_coord hn hπ i) (p.reindex f)).mdifferentiableAt hn0
  have h2 := ((contMDiff_reindex hn hπ f) p).mdifferentiableAt hn0
  exact (DFunLike.congr_fun (mfderiv_comp p h1 h2) ξ).symm

include hn hπ in
omit [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] in
/-- Lift a matching `m`-tuple of tangent vectors along an injective index map `f : Fin m → Fin k`
(`1 ≤ m`) to a matching `k`-tuple of tangent vectors at `p`, using surjectivity of `dπ` on
coordinates outside `range f`. -/
private theorem exists_tangentLift_of_injective {m k : ℕ} (hm : 1 ≤ m) {f : Fin m → Fin k}
    (hf : Injective f) (p : IteratedFiberProduct π k) (w : ∀ i : Fin m, TangentSpace IY (p.1 (f i)))
    (hw : ∀ i₁ i₂ : Fin m,
      mfderiv IY IM π (p.1 (f i₁)) (w i₁) =
        tangentSpaceCast IM (π (p.1 (f i₂))) (π (p.1 (f i₁)))
          (mfderiv IY IM π (p.1 (f i₂)) (w i₂))) :
    ∃ v : ∀ j : Fin k, TangentSpace IY (p.1 j),
      (∀ i : Fin m, v (f i) = w i) ∧
      ∀ j₁ j₂ : Fin k,
        mfderiv IY IM π (p.1 j₁) (v j₁) =
          tangentSpaceCast IM (π (p.1 j₂)) (π (p.1 j₁)) (mfderiv IY IM π (p.1 j₂) (v j₂)) := by
  classical
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let i₀ : Fin m := ⟨0, hm⟩
  let c : TangentSpace IM (π (p.1 (f i₀))) := mfderiv IY IM π (p.1 (f i₀)) (w i₀)
  let v : ∀ j : Fin k, TangentSpace IY (p.1 j) := fun j ↦
    if h : ∃ i, f i = j then
      tangentSpaceCast IY (p.1 (f h.choose)) (p.1 j) (w h.choose)
    else
      (hπ.surjective_mfderiv hn0 (p.1 j)
        (tangentSpaceCast IM (π (p.1 (f i₀))) (π (p.1 j)) c)).choose
  have hv_base : ∀ j : Fin k,
      mfderiv IY IM π (p.1 j) (v j) = tangentSpaceCast IM (π (p.1 (f i₀))) (π (p.1 j)) c := by
    intro j
    dsimp [v]
    split_ifs with h
    · have hj : f h.choose = j := h.choose_spec
      generalize h.choose = i at hj ⊢
      subst hj
      exact hw i i₀
    · exact (hπ.surjective_mfderiv hn0 (p.1 j)
        (tangentSpaceCast IM (π (p.1 (f i₀))) (π (p.1 j)) c)).choose_spec
  refine ⟨v, fun i ↦ ?_, fun j₁ j₂ ↦ by rw [hv_base j₁, hv_base j₂]; rfl⟩
  dsimp [v]
  split_ifs with h
  · have hi : h.choose = i := hf h.choose_spec
    rw [hi]
    rfl
  · exact (h ⟨i, rfl⟩).elim

/-- Reindexing along any injective map `f : Fin m → Fin k` is a `C^n` submersion. -/
theorem isSubmersion_reindex_of_injective {m k : ℕ} {f : Fin m → Fin k} (hf : Injective f) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ m
    Manifold.IsSubmersion 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin (m * finrank ℝ EY - (m - 1) * finrank ℝ EM) → ℝ) n
      (reindex (π := π) f) := by
  let := chartedSpace hn hπ k
  let := chartedSpace hn hπ m
  have := isManifold hn hπ k
  have := isManifold hn hπ m
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_reindex hn hπ f).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun p η ↦ ?_).isSubmersion
  cases m with
  | zero => exact ⟨0, funext fun i ↦ Fin.elim0 (i.cast (by simp))⟩
  | succ m' =>
    let w : ∀ i : Fin (m' + 1), TangentSpace IY (p.1 (f i)) :=
      fun i ↦ mfderiv 𝓘(ℝ, Fin ((m' + 1) * finrank ℝ EY - (m' + 1 - 1) * finrank ℝ EM) → ℝ) IY
        (fun q : IteratedFiberProduct π (m' + 1) ↦ q.1 i) (p.reindex f) η
    have hw_match : ∀ i₁ i₂ : Fin (m' + 1),
        mfderiv IY IM π (p.1 (f i₁)) (w i₁) =
          tangentSpaceCast IM (π (p.1 (f i₂))) (π (p.1 (f i₁)))
            (mfderiv IY IM π (p.1 (f i₂)) (w i₂)) := by
      have hvalm :=
        ((isSmoothEmbedding_val hn hπ (m' + 1)).contMDiff (p.reindex f)).mdifferentiableAt hn0
      have hrange := (mem_range_mfderiv_val_iff hn hπ (m' + 1) (p.reindex f)
        (mfderiv 𝓘(ℝ, Fin ((m' + 1) * finrank ℝ EY - (m' + 1 - 1) * finrank ℝ EM) → ℝ)
          (ModelWithCorners.pi fun _ : Fin (m' + 1) ↦ IY) Subtype.val (p.reindex f) η)).1 ⟨η, rfl⟩
      intro i₁ i₂
      have heq : ∀ i : Fin (m' + 1),
          mfderiv 𝓘(ℝ, Fin ((m' + 1) * finrank ℝ EY - (m' + 1 - 1) * finrank ℝ EM) → ℝ)
            (ModelWithCorners.pi fun _ : Fin (m' + 1) ↦ IY) Subtype.val (p.reindex f) η i = w i :=
        fun i ↦ (mfderiv_coord_of_mdifferentiableAt_val hvalm i η).symm
      have h := hrange i₁ i₂
      rw [heq i₁, heq i₂] at h
      exact h
    obtain ⟨v, hvfi, hvmatch⟩ :=
      exists_tangentLift_of_injective hn hπ (Nat.succ_pos m') hf p w hw_match
    obtain ⟨ξ, hξ⟩ := exists_mfderiv_eq hn hπ k p v hvmatch
    refine ⟨ξ, sub_eq_zero.mp (eq_zero_of_mfderiv hn hπ (m' + 1) (p.reindex f) _ fun i ↦ ?_)⟩
    rw [map_sub, mfderiv_coord_reindex hn hπ f p ξ i, hξ (f i), hvfi i, sub_self]

/-- Every face map `Y^[k + 1] → Y^[k]` is a `C^n` submersion. -/
theorem isSubmersion_face {k : ℕ} (i : Fin (k + 1)) :
    letI := chartedSpace hn hπ (k + 1)
    letI := chartedSpace hn hπ k
    Manifold.IsSubmersion 𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - (k + 1 - 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) n
      (face (π := π) i) :=
  isSubmersion_reindex_of_injective hn hπ (Fin.succAbove_right_injective (p := i))

/-- Every coordinate projection `Y^[k] → Y` is a `C^n` submersion. -/
theorem isSubmersion_coord {k : ℕ} (i : Fin k) :
    letI := chartedSpace hn hπ k
    Manifold.IsSubmersion 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IY n
      (fun p : IteratedFiberProduct π k ↦ p.1 i) := by
  let := chartedSpace hn hπ k
  let := chartedSpace hn hπ 1
  have := isManifold hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let f : Fin 1 → Fin k := fun _ ↦ i
  have hf : Injective f := fun _ _ _ ↦ Subsingleton.elim _ _
  refine ((contMDiff_coord hn hπ i).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun p u ↦ ?_).isSubmersion
  obtain ⟨η, hη⟩ := exists_mfderiv_eq hn hπ 1 (p.reindex f) (fun _ ↦ u) fun a b ↦ by
    rw [Subsingleton.elim a b]
    rfl
  obtain ⟨ξ, hξ⟩ := (isSubmersion_reindex_of_injective hn hπ hf).surjective_mfderiv hn0 p η
  refine ⟨ξ, ?_⟩
  rw [← mfderiv_coord_reindex hn hπ f p ξ 0, hξ, hη 0]

/-- The base projection `Y^[k] → M` (`1 ≤ k`) is a `C^n` submersion. -/
theorem isSubmersion_baseProj {k : ℕ} (hk : 1 ≤ k) :
    letI := chartedSpace hn hπ k
    Manifold.IsSubmersion 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ) IM n
      (baseProj (π := π) hk) := by
  let := chartedSpace hn hπ k
  have := isManifold hn hπ k
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_baseProj hn hπ hk).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun p ↦ ?_).isSubmersion
  have hbase_eq : baseProj (π := π) hk = π ∘ fun q : IteratedFiberProduct π k ↦ q.1 ⟨0, hk⟩ :=
    funext fun _ ↦ baseProj_apply hk _
  have h1 := (hπ.contMDiff (p.1 ⟨0, hk⟩)).mdifferentiableAt hn0
  have h2 := ((contMDiff_coord hn hπ (⟨0, hk⟩ : Fin k)) p).mdifferentiableAt hn0
  rw [hbase_eq, mfderiv_comp p h1 h2, ContinuousLinearMap.coe_comp]
  exact (hπ.surjective_mfderiv hn0 (p.1 ⟨0, hk⟩)).comp
    ((isSubmersion_coord hn hπ (⟨0, hk⟩ : Fin k)).surjective_mfderiv hn0 p)

/-- Every diagonal degeneracy map `Y^[k] → Y^[k + 1]` is a `C^n` smooth embedding,
since it has the smooth left inverse `face i.castSucc`. -/
theorem isSmoothEmbedding_degen {k : ℕ} (i : Fin k) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ (k + 1)
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - (k + 1 - 1) * finrank ℝ EM) → ℝ) n
      (degen (π := π) i) := by
  let := chartedSpace hn hπ k
  let := chartedSpace hn hπ (k + 1)
  have := isManifold hn hπ k
  have := isManifold hn hπ (k + 1)
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hleft : LeftInverse (face (π := π) i.castSucc) (degen (π := π) i) :=
    face_degen_self i
  refine ⟨(contMDiff_degen hn hπ i).isImmersion_of_leftInverse hn
    (fun p ↦ ((contMDiff_face hn hπ i.castSucc) (p.degen i)).mdifferentiableAt hn0) hleft,
    hleft.isEmbedding (contMDiff_face hn hπ i.castSucc).continuous
      (contMDiff_degen hn hπ i).continuous⟩

section Uniqueness

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {k : ℕ} {ι : P → Fin k → Y}
  (hι : Manifold.IsSmoothEmbedding IP (ModelWithCorners.pi fun _ : Fin k ↦ IY) n ι)
  (hrange : range ι = {y : Fin k → Y | ∀ i j, π (y i) = π (y j)})

/-- **Uniqueness of the embedded submanifold structure.** Any manifold `P` admitting a `C^n`
smooth embedding `ι : P → (Fin k → Y)` onto the carrier of `IteratedFiberProduct π k` is
canonically `C^n`-diffeomorphic to `IteratedFiberProduct π k`, independently of how `P` was
constructed or parenthesised. -/
noncomputable def diffeomorphOfRangeEq :
    letI := chartedSpace hn hπ k
    P ≃ₘ^n⟮IP, 𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ)⟯
      IteratedFiberProduct π k := by
  letI := chartedSpace hn hπ k
  have hto : ∀ x : P, ∀ i j : Fin k, π (ι x i) = π (ι x j) :=
    fun x ↦ hrange.le (mem_range_self x)
  have hmem : ∀ p : IteratedFiberProduct π k, ∃ x : P, ι x = p.1 := fun p ↦ hrange.ge p.2
  have hcomp : ι ∘ (fun p : IteratedFiberProduct π k ↦ (hmem p).choose) = Subtype.val :=
    funext fun p ↦ (hmem p).choose_spec
  exact
    { toFun := fun x ↦ ⟨ι x, hto x⟩
      invFun := fun p ↦ (hmem p).choose
      left_inv := fun x ↦ hι.isEmbedding.injective (hmem ⟨ι x, hto x⟩).choose_spec
      right_inv := fun p ↦ Subtype.ext (hmem p).choose_spec
      contMDiff_toFun := (isSmoothEmbedding_val hn hπ k).contMDiff_iff_comp.2 hι.contMDiff
      contMDiff_invFun := hι.contMDiff_iff_comp.2
        (hcomp.symm ▸ (isSmoothEmbedding_val hn hπ k).contMDiff) }

/-- The comparison diffeomorphism sends `x : P` to `ι x` viewed in `IteratedFiberProduct π k`. -/
@[simp]
theorem diffeomorphOfRangeEq_val_apply (x : P) :
    (diffeomorphOfRangeEq hn hπ hι hrange x).1 = ι x :=
  (rfl)

/-- Applying `ι` to the inverse of `diffeomorphOfRangeEq` recovers the underlying `k`-tuple. -/
theorem apply_diffeomorphOfRangeEq_symm (p : IteratedFiberProduct π k) :
    letI := chartedSpace hn hπ k
    ι ((diffeomorphOfRangeEq hn hπ hι hrange).symm p) = p.1 := by
  let := chartedSpace hn hπ k
  exact (diffeomorphOfRangeEq_val_apply hn hπ hι hrange _).symm.trans
    (congrArg Subtype.val ((diffeomorphOfRangeEq hn hπ hι hrange).apply_symm_apply p))

end Uniqueness

/-- Every equivalence `e : Fin m ≃ Fin k` induces a `C^n` diffeomorphism `Y^[k] ≃ₘ^n Y^[m]`; in
particular permutations of the factors are `C^n` diffeomorphisms. -/
noncomputable def reindexDiffeomorph {m k : ℕ} (e : Fin m ≃ Fin k) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ m
    IteratedFiberProduct π k ≃ₘ^n⟮
      𝓘(ℝ, Fin (k * finrank ℝ EY - (k - 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (m * finrank ℝ EY - (m - 1) * finrank ℝ EM) → ℝ)⟯
      IteratedFiberProduct π m := by
  letI := chartedSpace hn hπ k
  letI := chartedSpace hn hπ m
  exact
    { toFun := reindex e
      invFun := reindex e.symm
      left_inv := fun p ↦ Subtype.ext <| funext fun i ↦ congrArg p.1 (e.apply_symm_apply i)
      right_inv := fun p ↦ Subtype.ext <| funext fun i ↦ congrArg p.1 (e.symm_apply_apply i)
      contMDiff_toFun := contMDiff_reindex hn hπ e
      contMDiff_invFun := contMDiff_reindex hn hπ e.symm }

/-- The reindexing diffeomorphism acts by `reindex e`. -/
@[simp]
theorem reindexDiffeomorph_apply {m k : ℕ} (e : Fin m ≃ Fin k)
    (p : IteratedFiberProduct π k) :
    reindexDiffeomorph hn hπ e p = p.reindex e :=
  (rfl)

/-- The inverse of the reindexing diffeomorphism acts by `reindex e.symm`. -/
@[simp]
theorem reindexDiffeomorph_symm_apply {m k : ℕ} (e : Fin m ≃ Fin k)
    (p : IteratedFiberProduct π m) :
    letI := chartedSpace hn hπ k
    letI := chartedSpace hn hπ m
    (reindexDiffeomorph hn hπ e).symm p = p.reindex e.symm :=
  (rfl)

/-- The `1`-fold iterated fibre product `Y^[1]` is canonically `C^n`-diffeomorphic to `Y`. -/
noncomputable def oneDiffeomorph :
    letI := chartedSpace hn hπ 1
    IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin (1 * finrank ℝ EY - (1 - 1) * finrank ℝ EM) → ℝ), IY⟯ Y := by
  letI := chartedSpace hn hπ 1
  exact
    { toFun := fun p ↦ p.1 0
      invFun := fun y ↦ ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩
      left_inv := fun p ↦ Subtype.ext (funext fun i ↦ congrArg p.1 (Fin.eq_zero i).symm)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := contMDiff_coord hn hπ (0 : Fin 1)
      contMDiff_invFun := (isSmoothEmbedding_val hn hπ 1).contMDiff_iff_comp.2
        (contMDiff_pi_iff.2 fun _ ↦ contMDiff_id) }

/-- The unary comparison sends a `1`-tuple to its single entry. -/
@[simp]
theorem oneDiffeomorph_apply (p : IteratedFiberProduct π 1) :
    oneDiffeomorph hn hπ p = p.1 0 :=
  (rfl)

/-- The inverse unary comparison forms the constant `1`-tuple. -/
@[simp]
theorem oneDiffeomorph_symm_apply (y : Y) :
    letI := chartedSpace hn hπ 1
    (oneDiffeomorph hn hπ).symm y = ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩ :=
  (rfl)

/-- The `2`-fold iterated fibre product `Y^[2]` is canonically `C^n`-diffeomorphic to the binary
transverse fibre product `{q : Y × Y // π q.1 = π q.2}` with its chosen transverse atlas. -/
noncomputable def twoDiffeomorph :
    letI := chartedSpace hn hπ 2
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun q _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne' hπ q)
    IteratedFiberProduct π 2 ≃ₘ^n⟮
      𝓘(ℝ, Fin (2 * finrank ℝ EY - (2 - 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {q : Y × Y // π q.1 = π q.2} := by
  letI := chartedSpace hn hπ 2
  letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
    (fun q _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne' hπ q)
  have hemb2 := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hπ.contMDiff
    (fun q _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne' hπ q)
  refine
    { toFun := fun p ↦ ⟨(p.1 0, p.1 1), p.2 0 1⟩
      invFun := fun q ↦ ⟨![q.1.1, q.1.2], fun i j ↦ by
        fin_cases i <;> fin_cases j
        · rfl
        · exact q.2
        · exact q.2.symm
        · rfl⟩
      left_inv := fun p ↦ Subtype.ext <| funext fun i ↦ by fin_cases i <;> rfl
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := hemb2.contMDiff_iff_comp.2
        ((contMDiff_coord hn hπ (0 : Fin 2)).prodMk (contMDiff_coord hn hπ (1 : Fin 2)))
      contMDiff_invFun := (isSmoothEmbedding_val hn hπ 2).contMDiff_iff_comp.2 <|
        contMDiff_pi_iff.2 fun i ↦ by
          fin_cases i
          · exact hemb2.contMDiff.fst
          · exact hemb2.contMDiff.snd }

/-- The binary comparison extracts the pair `(p 0, p 1)`. -/
@[simp]
theorem twoDiffeomorph_apply (p : IteratedFiberProduct π 2) :
    twoDiffeomorph hn hπ p = ⟨(p.1 0, p.1 1), p.2 0 1⟩ :=
  (rfl)

/-- The inverse binary comparison pairs the two components into a `2`-tuple. -/
@[simp]
theorem twoDiffeomorph_symm_val_zero (q : {q : Y × Y // π q.1 = π q.2}) :
    letI := chartedSpace hn hπ 2
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun q _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne' hπ q)
    ((twoDiffeomorph hn hπ).symm q).1 0 = q.1.1 :=
  (rfl)

/-- The inverse binary comparison places the second component at index `1`. -/
@[simp]
theorem twoDiffeomorph_symm_val_one (q : {q : Y × Y // π q.1 = π q.2}) :
    letI := chartedSpace hn hπ 2
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun q _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne' hπ q)
    ((twoDiffeomorph hn hπ).symm q).1 1 = q.1.2 :=
  (rfl)

omit [TopologicalSpace Y] [TopologicalSpace M] in
/-- Concatenation of matching `p`- and `q`-tuples into a `(p + q)`-tuple. -/
private def appendPair {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (r : {r : IteratedFiberProduct π p × IteratedFiberProduct π q //
      r.1.baseProj hp = r.2.baseProj hq}) : IteratedFiberProduct π (p + q) :=
  ⟨Fin.append r.1.1.1 r.1.2.1, fun i j ↦ by
    refine Fin.addCases (fun i₁ ↦ ?_) (fun i₂ ↦ ?_) i <;>
      refine Fin.addCases (fun j₁ ↦ ?_) (fun j₂ ↦ ?_) j
    · simpa only [Fin.append_left] using r.1.1.2 i₁ j₁
    · simpa only [Fin.append_left, Fin.append_right] using
        ((r.1.1.baseProj_eq i₁).symm.trans (r.2.trans (r.1.2.baseProj_eq j₂)))
    · simpa only [Fin.append_left, Fin.append_right] using
        ((r.1.2.baseProj_eq i₂).symm.trans (r.2.symm.trans (r.1.1.baseProj_eq j₁)))
    · simpa only [Fin.append_right] using r.1.2.2 i₂ j₂⟩

/-- **Independence of binary parenthesisation.** For `1 ≤ p` and `1 ≤ q`, the `(p + q)`-fold
iterated fibre product `Y^[p + q]` is canonically `C^n`-diffeomorphic to the transverse fibre
product `Y^[p] ×_M Y^[q]` along the two base projections. -/
noncomputable def addDiffeomorph {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    letI := chartedSpace hn hπ (p + q)
    letI := chartedSpace hn hπ p
    letI := chartedSpace hn hπ q
    haveI := isManifold hn hπ p
    haveI := isManifold hn hπ q
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ hp) (contMDiff_baseProj hn hπ hq)
      (fun r _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne'
        (isSubmersion_baseProj hn hπ hq) r)
    IteratedFiberProduct π (p + q) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((p + q) * finrank ℝ EY - (p + q - 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin (p * finrank ℝ EY - (p - 1) * finrank ℝ EM) → ℝ) +
        finrank ℝ (Fin (q * finrank ℝ EY - (q - 1) * finrank ℝ EM) → ℝ) -
        finrank ℝ EM) → ℝ)⟯
      {r : IteratedFiberProduct π p × IteratedFiberProduct π q //
        r.1.baseProj hp = r.2.baseProj hq} := by
  letI := chartedSpace hn hπ (p + q)
  letI := chartedSpace hn hπ p
  letI := chartedSpace hn hπ q
  haveI := isManifold hn hπ p
  haveI := isManifold hn hπ q
  letI := transverseFiberProductChartedSpace hn
    (contMDiff_baseProj hn hπ hp) (contMDiff_baseProj hn hπ hq)
    (fun r _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne'
      (isSubmersion_baseProj hn hπ hq) r)
  have hembPQ := isSmoothEmbedding_coe_transverseFiberProduct hn
    (contMDiff_baseProj hn hπ hp) (contMDiff_baseProj hn hπ hq)
    (fun r _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne'
      (isSubmersion_baseProj hn hπ hq) r)
  refine
    { toFun := fun y ↦
        ⟨(y.reindex (Fin.castAdd q), y.reindex (Fin.natAdd p)),
          (baseProj_reindex hp _ y).trans (baseProj_reindex hq _ y).symm⟩
      invFun := appendPair hp hq
      left_inv := fun y ↦ Subtype.ext <| funext fun i ↦
        Fin.addCases (fun i₁ ↦ by simp [appendPair, Fin.append_left])
          (fun i₂ ↦ by simp [appendPair, Fin.append_right]) i
      right_inv := fun r ↦ Subtype.ext <| Prod.ext
        (Subtype.ext (funext fun i ↦ Fin.append_left _ _ i))
        (Subtype.ext (funext fun j ↦ Fin.append_right _ _ j))
      contMDiff_toFun := hembPQ.contMDiff_iff_comp.2
        ((contMDiff_reindex hn hπ (Fin.castAdd q)).prodMk (contMDiff_reindex hn hπ (Fin.natAdd p)))
      contMDiff_invFun := (isSmoothEmbedding_val hn hπ (p + q)).contMDiff_iff_comp.2 <|
        contMDiff_pi_iff.2 fun i ↦ Fin.addCases
          (motive := fun i ↦ ContMDiff _ IY n (fun r : {r : IteratedFiberProduct π p ×
            IteratedFiberProduct π q // r.1.baseProj hp = r.2.baseProj hq} ↦
            Fin.append r.1.1.1 r.1.2.1 i))
          (fun i₁ ↦ by
            simpa only [Function.comp_def, Fin.append_left] using
              (contMDiff_coord hn hπ i₁).comp hembPQ.contMDiff.fst)
          (fun i₂ ↦ by
            simpa only [Function.comp_def, Fin.append_right] using
              (contMDiff_coord hn hπ i₂).comp hembPQ.contMDiff.snd) i }

/-- The splitting diffeomorphism restricts a `(p + q)`-tuple to its first `p` and last `q`
coordinates. -/
@[simp]
theorem addDiffeomorph_apply {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (y : IteratedFiberProduct π (p + q)) :
    addDiffeomorph hn hπ hp hq y =
      ⟨(y.reindex (Fin.castAdd q), y.reindex (Fin.natAdd p)),
        (baseProj_reindex hp _ y).trans (baseProj_reindex hq _ y).symm⟩ :=
  (rfl)

/-- The inverse splitting diffeomorphism concatenates a `p`-tuple and a `q`-tuple via
`Fin.append`. -/
@[simp]
theorem addDiffeomorph_symm_val {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (r : {r : IteratedFiberProduct π p × IteratedFiberProduct π q //
      r.1.baseProj hp = r.2.baseProj hq}) :
    letI := chartedSpace hn hπ (p + q)
    letI := chartedSpace hn hπ p
    letI := chartedSpace hn hπ q
    haveI := isManifold hn hπ p
    haveI := isManifold hn hπ q
    letI := transverseFiberProductChartedSpace hn
      (contMDiff_baseProj hn hπ hp) (contMDiff_baseProj hn hπ hq)
      (fun r _ ↦ transverse_isSubmersion_right (zero_lt_one.trans_le hn).ne'
        (isSubmersion_baseProj hn hπ hq) r)
    ((addDiffeomorph hn hπ hp hq).symm r).1 = Fin.append r.1.1.1 r.1.2.1 :=
  (rfl)

end ManifoldConstruction

section IdentityCover

variable {EM HM M : Type*}
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IM n M] [IM.Boundaryless] [FiniteDimensional ℝ EM]

/-- For the identity submersion `id : M → M`, the `k`-fold iterated fibre product `M^[k]`
(`1 ≤ k`) is canonically `C^n`-diffeomorphic to `M` (as the small diagonal). -/
noncomputable def idDiffeomorph (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    letI := chartedSpace hn (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) k
    IteratedFiberProduct (id : M → M) k ≃ₘ^n⟮
      𝓘(ℝ, Fin (k * finrank ℝ EM - (k - 1) * finrank ℝ EM) → ℝ), IM⟯ M := by
  letI := chartedSpace hn (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) k
  exact
    { toFun := fun p ↦ p.1 ⟨0, hk⟩
      invFun := fun x ↦ ⟨fun _ ↦ x, fun _ _ ↦ rfl⟩
      left_inv := fun p ↦ Subtype.ext (funext fun i ↦ (p.2 i ⟨0, hk⟩).symm)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun :=
        contMDiff_coord hn (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) (⟨0, hk⟩ : Fin k)
      contMDiff_invFun :=
        (isSmoothEmbedding_val hn (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M))
          k).contMDiff_iff_comp.2 (contMDiff_pi_iff.2 fun _ ↦ contMDiff_id) }

/-- The identity-cover comparison sends a constant `k`-tuple to its common entry. -/
@[simp]
theorem idDiffeomorph_apply (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (p : IteratedFiberProduct (id : M → M) k) :
    idDiffeomorph (IM := IM) hn hk p = p.1 ⟨0, hk⟩ :=
  (rfl)

/-- The inverse identity-cover comparison sends `x : M` to the constant `k`-tuple. -/
@[simp]
theorem idDiffeomorph_symm_apply (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (x : M) :
    letI := chartedSpace hn (Manifold.IsSubmersion.id (I := IM) (n := n) (M := M)) k
    (idDiffeomorph (IM := IM) hn hk).symm x = ⟨fun _ ↦ x, fun _ _ ↦ rfl⟩ :=
  (rfl)

end IdentityCover

end IteratedFiberProduct

end TauCeti
