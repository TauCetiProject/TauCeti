/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Simplicial
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Geometry.Manifold.Submersion.PartitionOfUnity
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic

/-!
# The alternating pullback complex of forms on the Čech nerve of a submersion

Let `π : Y → M` be a smooth submersion between finite-dimensional boundaryless real manifolds, with
Čech nerve `Y^[m + 1] = IteratedFiberProduct π (m + 1)`. Smooth `F`-valued `k`-forms on the
`Y^[m + 1]` form a cosimplicial real vector space `TauCeti.iteratedFiberProductForms` under pullback
along the reindexing maps. The differential of its alternating coface map complex
(`AlgebraicTopology.AlternatingCofaceMapComplex`) is the alternating pullback
`δ = ∑ᵢ (-1)ⁱ (face i)^*` (`TauCeti.iteratedFiberProductForms_objD_hom_apply`); on `Y^[1]` it is
`(face 0)^* - (face 1)^*`, the difference of the pullbacks along the two projections
`Y^[2] → Y^[1]`. Pullback along `baseProj : Y^[1] → M` augments it by the forms on `M`
(`TauCeti.iteratedFiberProductForms_objD_zero_mpullback_baseProj`).

When `π` is surjective and `M` is Hausdorff and `σ`-compact, the augmented complex
`0 → Ω^k(M) → Ω^k(Y^[1]) → Ω^k(Y^[2]) → ⋯` is exact:

* `TauCeti.iteratedFiberProductForms_existsUnique_mpullback_baseProj_eq_iff`: a form on `Y^[1]`
  descends to `M`, uniquely, exactly when its `δ` vanishes;
* `TauCeti.iteratedFiberProductForms_exists_objD_eq_iff` and
  `TauCeti.exactAt_alternatingCofaceMapComplex_iteratedFiberProductForms`: in every positive degree
  the `δ`-closed forms are the `δ`-exact ones.

This is the exactness of the fundamental complex of a surjective submersion, on which descent of
forms and connections for bundle gerbes rests. The proof constructs a contracting homotopy: local
smooth sections `s i` of `π` over the members `U i` of an open cover, glued by a subordinate smooth
partition of unity `ρ`, give `K φ = ∑ᵢ (ρ i ∘ baseProj) • (prepend (s i))^* φ`, where
`prepend (s i)` sends `y` to `(s i (baseProj y), y₀, …, y_m)` (`IteratedFiberProduct.cons`). It is
the argument for the generalized Mayer–Vietoris principle of Bott–Tu, with the Čech nerve of an
open cover replaced by that of a submersion.

## References

* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) **54** (1996), 403–416 (the fundamental
  complex of a surjective submersion).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982), §8
  (the generalized Mayer–Vietoris principle).
-/

public section

open Function Set Module Topology CategoryTheory
open scoped Manifold ContDiff Simplicial

namespace TauCeti

universe uY uF

section Manifold

variable {EY HY EM HM M : Type*} {Y : Type uY}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IY ∞ Y] [IsManifold IM ∞ M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  {π : Y → M} (hπ : Manifold.IsSubmersion IY IM ∞ π)
  (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)

/-- The cosimplicial real vector space of smooth `F`-valued `k`-forms on the Čech nerve of a smooth
submersion `π : Y → M`: in degree `m` it is the space of smooth `k`-forms on `Y^[m + 1]`, and a
monotone map `α : [m₁] → [m₂]` acts by pullback along `reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]`. -/
@[expose] noncomputable def iteratedFiberProductForms :
    CosimplicialObject (ModuleCat.{max uY uF} ℝ) where
  obj n :=
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n.len
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n.len
    ModuleCat.of ℝ (SmoothForm 𝓘(ℝ, Fin ((n.len + 1) * finrank ℝ EY - n.len * finrank ℝ EM) → ℝ)
      (IteratedFiberProduct π (n.len + 1)) F k)
  map {n₁ n₂} α :=
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n₁.len
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n₂.len
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n₁.len
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n₂.len
    ModuleCat.ofHom (SmoothForm.mpullback (IteratedFiberProduct.reindex α.toOrderHom)
      (contMDiff_reindex ENat.LEInfty.out hπ le_rfl α.toOrderHom))
  map_id n := by
    let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n.len
    have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n.len
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ Subtype.ext ?_)
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_apply,
      SmoothForm.coe_mpullback, SimplexCategory.id_toOrderHom, OrderHom.id_coe,
      IteratedFiberProduct.reindex_id, TauCeti.mpullback_id]
  map_comp {n₁ n₂ n₃} α β := by
    let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n₁.len
    let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n₂.len
    let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ n₃.len
    have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n₁.len
    have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n₂.len
    have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ n₃.len
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply,
      SmoothForm.mpullback_mpullback, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      ← IteratedFiberProduct.reindex_comp]

/-- A monotone map `α : [m₁] → [m₂]` acts on `iteratedFiberProductForms` by pullback along
`reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]`. -/
@[simp]
theorem iteratedFiberProductForms_map_hom_apply {m₁ m₂ : ℕ} (α : ⦋m₁⦌ ⟶ ⦋m₂⦌)
    (φ : (iteratedFiberProductForms hπ F k).obj ⦋m₁⦌) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m₁
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m₂
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m₁
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m₂
    ((iteratedFiberProductForms hπ F k).map α).hom φ =
      SmoothForm.mpullback (IteratedFiberProduct.reindex α.toOrderHom)
        (contMDiff_reindex ENat.LEInfty.out hπ le_rfl α.toOrderHom) φ :=
  (rfl)

/-- The coface map `δ i` of `iteratedFiberProductForms` is pullback along the face map
`face i : Y^[m + 2] → Y^[m + 1]`. -/
@[simp]
theorem iteratedFiberProductForms_δ_hom_apply {m : ℕ} (i : Fin (m + 2))
    (φ : (iteratedFiberProductForms hπ F k).obj ⦋m⦌) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
    ((iteratedFiberProductForms hπ F k).δ i).hom φ =
      SmoothForm.mpullback (IteratedFiberProduct.face i)
        (contMDiff_face ENat.LEInfty.out hπ le_rfl i) φ := by
  simp only [CosimplicialObject.δ, iteratedFiberProductForms, ModuleCat.hom_ofHom,
    IteratedFiberProduct.face_eq_reindex, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.coe_succAboveOrderEmb]
  -- The two sides differ only by `⦋m⦌.len = m` inside the chosen atlases, which `simp` cannot
  -- rewrite in instance arguments; this holds by definition.
  rfl

/-- The differential of the alternating coface map complex of `iteratedFiberProductForms` is the
alternating sum `∑ᵢ (-1)ⁱ (face i)^*` of pullbacks along the face maps. -/
theorem iteratedFiberProductForms_objD_hom_apply {m : ℕ}
    (φ : (iteratedFiberProductForms hπ F k).obj ⦋m⦌) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (iteratedFiberProductForms hπ F k) m).hom φ =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        SmoothForm.mpullback (IteratedFiberProduct.face i)
          (contMDiff_face ENat.LEInfty.out hπ le_rfl i) φ := by
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    ModuleCat.hom_smul, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    iteratedFiberProductForms_δ_hom_apply]
  -- The two sums have the same summands. Their addition and `ℤ`-action are those of the
  -- `ModuleCat` carrier over `⦋m + 1⦌.len` and of `SmoothForm` over `m + 1`, which agree by
  -- `SimplexCategory.len_mk`; that index sits in instance arguments, where it cannot be rewritten.
  rfl

section Homotopy

/-! ### The contracting homotopy

Fix a smooth partition of unity `ρ` on `M` subordinate to open sets `U i` carrying smooth sections
`s i` of `π`, extended to global set-theoretic sections. Prepending `s i (baseProj y)` to `y` gives
maps `Y^[m + 1] → Y^[m + 2]`, smooth over `U i`, and the operator
`K φ = ∑ᵢ (ρ i ∘ baseProj) • (prepend (s i))^* φ` lowers the degree of the Čech nerve by one. It
satisfies `K ∘ (face 0)^* = id` and `K ∘ (face (j + 1))^* = (face j)^* ∘ K`, the identities of an
extra codegeneracy, from which `δ K + K δ = id` follows. -/

variable {ι : Type*} {ρ : SmoothPartitionOfUnity ι IM M univ} {U : ι → Set M}
  (hρ : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i)) {s : ι → M → Y}
  (hs : ∀ i x, π (s i x) = x) (hsU : ∀ i, ContMDiffOn IM IY ∞ (s i) (U i))

include hU hsU in
/-- Prepending `s i (baseProj y)` is smooth at every point of `Y^[m + 1]` lying over `U i`. -/
private theorem contMDiffAt_cons_section_of_mem {m : ℕ} {i : ι}
    {y : IteratedFiberProduct π (m + 1)} (hy : IteratedFiberProduct.baseProj y ∈ U i) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    ContMDiffAt 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) ∞
      (fun y ↦ IteratedFiberProduct.cons (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) y :=
  contMDiffAt_cons_section ENat.LEInfty.out hπ le_rfl (hs i)
    ((hsU i).contMDiffAt ((hU i).mem_nhds hy))

/-- The contracting homotopy `Ω(Y^[m + 2]) → Ω(Y^[m + 1])`. -/
private noncomputable def homotopy (m : ℕ) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
    SmoothForm 𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 2)) F k →ₗ[ℝ]
      SmoothForm 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 1)) F k :=
  letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
  letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
  haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
  haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
  { toFun φ := ⟨fun y ↦ ∑ i ∈ ρ.finsupport (IteratedFiberProduct.baseProj y),
        ρ i (IteratedFiberProduct.baseProj y) •
          mpullback (F := F) _ _ (fun y ↦ IteratedFiberProduct.cons
            (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) φ.val y,
      (isSmoothForm_sum_finsupport_smul_mpullback hρ hU
        (contMDiff_baseProj ENat.LEInfty.out hπ le_rfl)
        (fun _ _ hy ↦ contMDiffAt_cons_section_of_mem hπ hU hs hsU hy) φ).mem_smoothBundleForms⟩
    map_add' φ ψ := by
      refine Subtype.ext (funext fun y ↦ ?_)
      simp only [Submodule.coe_add, mpullback_add, Pi.add_apply, smul_add,
        Finset.sum_add_distrib]
    map_smul' c φ := by
      refine Subtype.ext (funext fun y ↦ ?_)
      simp only [SetLike.val_smul, mpullback_smul, Pi.smul_apply, smul_comm c,
        Finset.smul_sum, RingHom.id_apply] }

/-- The underlying rough form of the contracting homotopy. -/
private theorem coe_homotopy (m : ℕ)
    (φ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
      SmoothForm 𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 2)) F k) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    (homotopy hπ F k hρ hU hs hsU m φ).val = fun y ↦
      ∑ i ∈ ρ.finsupport (IteratedFiberProduct.baseProj y),
        ρ i (IteratedFiberProduct.baseProj y) •
          mpullback (F := F) _ _ (fun y ↦ IteratedFiberProduct.cons
            (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) φ.val y :=
  (rfl)

/-- `K ∘ (face 0)^* = id`: omitting the prepended point undoes the prepending. -/
private theorem homotopy_mpullback_face_zero (m : ℕ)
    (φ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
      SmoothForm 𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 1)) F k) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
    homotopy hπ F k hρ hU hs hsU m (SmoothForm.mpullback (IteratedFiberProduct.face 0)
      (contMDiff_face ENat.LEInfty.out hπ le_rfl 0) φ) = φ := by
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
  refine Subtype.ext (funext fun y ↦ ?_)
  rw [coe_homotopy]
  refine ρ.sum_finsupport_smul_eq_of_forall_eq (mem_univ _) fun i hi ↦ ?_
  have hcomp : (IteratedFiberProduct.face (m := m) 0 ∘ fun y ↦ IteratedFiberProduct.cons
      (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) = id :=
    funext fun y ↦ IteratedFiberProduct.face_zero_cons _ _ _
  rw [SmoothForm.coe_mpullback, ← mpullback_comp_at
    ((contMDiffAt_cons_section_of_mem hπ hU hs hsU
      (hρ.mem_of_mem_finsupport hi)).mdifferentiableAt (by simp))
    ((contMDiff_face ENat.LEInfty.out hπ le_rfl 0 _).mdifferentiableAt (by simp)),
    hcomp, mpullback_id]

/-- `K ∘ (face (j + 1))^* = (face j)^* ∘ K`: prepending a point commutes with omitting a later
coordinate. -/
private theorem homotopy_mpullback_face_succ (m : ℕ) (j : Fin (m + 2))
    (φ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
      SmoothForm 𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 2)) F k) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 2)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 2)
    homotopy hπ F k hρ hU hs hsU (m + 1) (SmoothForm.mpullback (IteratedFiberProduct.face j.succ)
      (contMDiff_face ENat.LEInfty.out hπ le_rfl j.succ) φ) =
      SmoothForm.mpullback (IteratedFiberProduct.face j)
        (contMDiff_face ENat.LEInfty.out hπ le_rfl j) (homotopy hπ F k hρ hU hs hsU m φ) := by
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 2)
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 2)
  refine Subtype.ext (funext fun y ↦ ?_)
  -- Pulling back the pointwise sum defining `K φ` along `face j` pulls back each summand.
  rw [SmoothForm.coe_mpullback, coe_homotopy, coe_homotopy, mpullback_sum_smul]
  simp only [IteratedFiberProduct.baseProj_face]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hy : IteratedFiberProduct.baseProj y ∈ U i := hρ.mem_of_mem_finsupport hi
  have hy' : IteratedFiberProduct.baseProj (IteratedFiberProduct.face j y) ∈ U i := by
    rwa [IteratedFiberProduct.baseProj_face]
  have hcomp : (IteratedFiberProduct.face j.succ ∘ fun y ↦ IteratedFiberProduct.cons
      (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) =
      (fun y ↦ IteratedFiberProduct.cons (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) ∘
        IteratedFiberProduct.face j :=
    funext fun y ↦ by
      simp only [Function.comp_apply, IteratedFiberProduct.face_succ_cons,
        IteratedFiberProduct.baseProj_face]
  rw [SmoothForm.coe_mpullback, ← mpullback_comp_at
    ((contMDiffAt_cons_section_of_mem hπ hU hs hsU hy).mdifferentiableAt (by simp))
    ((contMDiff_face ENat.LEInfty.out hπ le_rfl j.succ _).mdifferentiableAt (by simp)),
    hcomp, mpullback_comp_at
    ((contMDiff_face ENat.LEInfty.out hπ le_rfl j _).mdifferentiableAt (by simp))
    ((contMDiffAt_cons_section_of_mem hπ hU hs hsU hy').mdifferentiableAt (by simp))]

/-- The homotopy identity `δ K + K δ = id` in positive degrees, with `δ = ∑ᵢ (-1)ⁱ (face i)^*`,
applied to a `δ`-closed form: `δ (K φ) = φ` whenever `δ φ = 0`. -/
private theorem sum_mpullback_face_homotopy_of_sum_mpullback_face_eq_zero (m : ℕ)
    (φ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
      SmoothForm 𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π (m + 2)) F k)
    (hφ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
      letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 2)
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 2)
      ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • SmoothForm.mpullback (IteratedFiberProduct.face i)
        (contMDiff_face ENat.LEInfty.out hπ le_rfl i) φ = 0) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ m
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ (m + 1)
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ m
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ (m + 1)
    ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • SmoothForm.mpullback (IteratedFiberProduct.face i)
        (contMDiff_face ENat.LEInfty.out hπ le_rfl i) (homotopy hπ F k hρ hU hs hsU m φ) = φ := by
  -- Apply `K` to `δ φ = 0` and expand `K δ φ` with the extra codegeneracy identities.
  have h := congrArg (homotopy hπ F k hρ hU hs hsU (m + 1)) hφ
  rw [map_zero, map_sum, Fin.sum_univ_succ (n := m + 2)] at h
  simp only [map_neg, map_zsmul, homotopy_mpullback_face_zero,
    homotopy_mpullback_face_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib] at h
  exact (add_neg_eq_zero.1 h).symm

include hρ hU hs hsU in
/-- **Descent in degree zero.** If `(face 0)^* φ = (face 1)^* φ` on `Y^[2]`, then `φ` is the
pullback along `baseProj : Y^[1] → M` of the form `∑ᵢ ρᵢ • (s i)^* φ` on `M`. -/
private theorem exists_mpullback_baseProj_eq_of_mpullback_face_eq
    (φ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
      SmoothForm 𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ)
        (IteratedFiberProduct π 1) F k)
    (hφ : letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
      letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 1
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
      haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 1
      SmoothForm.mpullback (IteratedFiberProduct.face 0)
        (contMDiff_face ENat.LEInfty.out hπ le_rfl 0) φ =
      SmoothForm.mpullback (IteratedFiberProduct.face 1)
        (contMDiff_face ENat.LEInfty.out hπ le_rfl 1) φ) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
    ∃ β : SmoothForm IM M F k, SmoothForm.mpullback IteratedFiberProduct.baseProj
      (contMDiff_baseProj ENat.LEInfty.out hπ le_rfl) β = φ := by
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 1
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 1
  have hσ : ∀ i x, x ∈ U i → ContMDiffAt IM
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ) ∞
      (fun x ↦ IteratedFiberProduct.const (π := π) 1 (s i x)) x := fun i x hx ↦
    (contMDiff_const ENat.LEInfty.out hπ le_rfl (s i x)).comp x
      ((hsU i).contMDiffAt ((hU i).mem_nhds hx))
  refine ⟨⟨fun x ↦ ∑ i ∈ ρ.finsupport x, ρ i x • mpullback (F := F) _ _
      (fun x ↦ IteratedFiberProduct.const (π := π) 1 (s i x)) φ.val x,
    (isSmoothForm_sum_finsupport_smul_mpullback hρ hU contMDiff_id hσ
      φ).mem_smoothBundleForms⟩, Subtype.ext (funext fun y ↦ ?_)⟩
  -- Pulling back the pointwise sum along `baseProj` pulls back each summand.
  rw [SmoothForm.coe_mpullback, mpullback_sum_smul]
  refine ρ.sum_finsupport_smul_eq_of_forall_eq (mem_univ _) fun i hi ↦ ?_
  have hy : IteratedFiberProduct.baseProj y ∈ U i := hρ.mem_of_mem_finsupport hi
  have hins := (contMDiffAt_cons_section_of_mem hπ hU hs hsU hy).mdifferentiableAt
    (n := ∞) (by simp)
  -- `x ↦ (s i x)` after `baseProj` is `face 1` after prepending `s i (baseProj y)`, and
  -- `face 0` after prepending is the identity.
  have h₁ : ((fun x ↦ IteratedFiberProduct.const (π := π) 1 (s i x)) ∘
      IteratedFiberProduct.baseProj) = IteratedFiberProduct.face 1 ∘ fun y ↦
        IteratedFiberProduct.cons (s i (IteratedFiberProduct.baseProj y)) y (hs i _) :=
    funext fun y ↦ (IteratedFiberProduct.face_one_cons _ _ _).symm
  have h₀ : (IteratedFiberProduct.face (m := 0) 0 ∘ fun y ↦ IteratedFiberProduct.cons
      (s i (IteratedFiberProduct.baseProj y)) y (hs i _)) = id :=
    funext fun y ↦ IteratedFiberProduct.face_zero_cons _ _ _
  rw [← mpullback_comp_at
    ((contMDiff_baseProj ENat.LEInfty.out hπ le_rfl y).mdifferentiableAt (by simp))
    ((hσ i _ hy).mdifferentiableAt (by simp)), h₁,
    mpullback_comp_at hins
      ((contMDiff_face ENat.LEInfty.out hπ le_rfl 1 _).mdifferentiableAt (by simp)),
    ← SmoothForm.coe_mpullback _ (contMDiff_face ENat.LEInfty.out hπ le_rfl 1), ← hφ,
    SmoothForm.coe_mpullback, ← mpullback_comp_at hins
      ((contMDiff_face ENat.LEInfty.out hπ le_rfl 0 _).mdifferentiableAt (by simp)),
    h₀, mpullback_id]

end Homotopy

/-- **Exactness of the alternating pullback complex in positive degrees.** For a surjective smooth
submersion `π : Y → M` over a Hausdorff `σ`-compact base, a smooth form `φ` on `Y^[m + 2]` is
`δ η` for a smooth form `η` on `Y^[m + 1]`, where `δ = ∑ᵢ (-1)ⁱ (face i)^*`, if and only if
`δ φ = 0`. -/
theorem iteratedFiberProductForms_exists_objD_eq_iff [T2Space M] [SigmaCompactSpace M]
    (hsurj : Surjective π) {m : ℕ} (φ : (iteratedFiberProductForms hπ F k).obj ⦋m + 1⦌) :
    (∃ η, (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (iteratedFiberProductForms hπ F k) m).hom η = φ) ↔
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (iteratedFiberProductForms hπ F k) (m + 1)).hom φ = 0 := by
  refine ⟨fun ⟨η, hη⟩ ↦ ?_, fun hφ ↦ ?_⟩
  · rw [← hη, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      AlgebraicTopology.AlternatingCofaceMapComplex.d_squared, ModuleCat.hom_zero,
      LinearMap.zero_apply]
  · obtain ⟨ρ, U, s, hρ, hU, hs, hsU⟩ :=
      hπ.exists_smoothPartitionOfUnity_sections_of_surjective hsurj
    refine ⟨homotopy hπ F k hρ hU hs hsU m φ, ?_⟩
    rw [iteratedFiberProductForms_objD_hom_apply] at hφ
    rw [iteratedFiberProductForms_objD_hom_apply hπ F k (homotopy hπ F k hρ hU hs hsU m φ)]
    exact sum_mpullback_face_homotopy_of_sum_mpullback_face_eq_zero hπ F k hρ hU hs hsU m φ hφ

/-- **Exactness of the alternating pullback complex.** For a surjective smooth submersion
`π : Y → M` over a Hausdorff `σ`-compact base, the alternating coface map complex of
`iteratedFiberProductForms` is exact in every positive degree. -/
theorem exactAt_alternatingCofaceMapComplex_iteratedFiberProductForms [T2Space M]
    [SigmaCompactSpace M] (hsurj : Surjective π) (m : ℕ) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
      (iteratedFiberProductForms hπ F k)).ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro φ hφ
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor'_obj_f, HomologicalComplex.shortComplexFunctor'_obj_g,
    CochainComplex.of_d] at hφ ⊢
  exact (iteratedFiberProductForms_exists_objD_eq_iff hπ F k hsurj φ).2 hφ

/-- The augmentation `baseProj^* : Ω(M) → Ω(Y^[1])` composed with the first differential vanishes:
`(face 0)^*` and `(face 1)^*` agree on forms pulled back from `M`. -/
theorem iteratedFiberProductForms_objD_zero_mpullback_baseProj (β : SmoothForm IM M F k) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (iteratedFiberProductForms hπ F k) 0).hom
      (SmoothForm.mpullback IteratedFiberProduct.baseProj
        (contMDiff_baseProj ENat.LEInfty.out hπ le_rfl) β) = 0 := by
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 1
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 1
  have hface : ∀ i : Fin 2,
      (IteratedFiberProduct.baseProj ∘ IteratedFiberProduct.face (π := π) (m := 0) i) =
        IteratedFiberProduct.baseProj :=
    fun i ↦ funext (IteratedFiberProduct.baseProj_face i)
  rw [iteratedFiberProductForms_objD_hom_apply hπ F k (SmoothForm.mpullback
    IteratedFiberProduct.baseProj (contMDiff_baseProj ENat.LEInfty.out hπ le_rfl) β)]
  simp only [Nat.reduceAdd, Int.reduceNeg, SmoothForm.mpullback_mpullback, hface,
    Fin.sum_univ_two, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ, pow_one, neg_smul,
    add_neg_cancel]
  -- The two sides are the zeros of `SmoothForm` over `0 + 1` and of the `ModuleCat` carrier over
  -- `⦋0⦌.len + 1`, which agree by `SimplexCategory.len_mk`; that index sits in instance arguments,
  -- where it cannot be rewritten.
  rfl

/-- **Exactness of the augmented alternating pullback complex in degree zero.** For a surjective
smooth submersion `π : Y → M` over a Hausdorff `σ`-compact base, a smooth form `φ` on `Y^[1]` is the
pullback along `baseProj : Y^[1] → M` of a unique smooth form on `M` if and only if
`δ φ = (face 0)^* φ - (face 1)^* φ` vanishes on `Y^[2]`. -/
theorem iteratedFiberProductForms_existsUnique_mpullback_baseProj_eq_iff [T2Space M]
    [SigmaCompactSpace M] (hsurj : Surjective π) (φ : (iteratedFiberProductForms hπ F k).obj ⦋0⦌) :
    letI := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
    haveI := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
    (∃! β : SmoothForm IM M F k, SmoothForm.mpullback IteratedFiberProduct.baseProj
        (contMDiff_baseProj ENat.LEInfty.out hπ le_rfl) β = φ) ↔
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (iteratedFiberProductForms hπ F k) 0).hom φ = 0 := by
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 0
  let := iteratedFiberProductChartedSpace ENat.LEInfty.out hπ 1
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 0
  have := isManifold_iteratedFiberProduct ENat.LEInfty.out hπ 1
  refine ⟨fun ⟨β, hβ, _⟩ ↦ hβ ▸ iteratedFiberProductForms_objD_zero_mpullback_baseProj hπ F k β,
    fun hφ ↦ ?_⟩
  obtain ⟨ρ, U, s, hρ, hU, hs, hsU⟩ := hπ.exists_smoothPartitionOfUnity_sections_of_surjective hsurj
  rw [iteratedFiberProductForms_objD_hom_apply, Fin.sum_univ_two] at hφ
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    ← sub_eq_add_neg] at hφ
  obtain ⟨β, hβ⟩ :=
    exists_mpullback_baseProj_eq_of_mpullback_face_eq hπ F k hρ hU hs hsU φ (sub_eq_zero.1 hφ)
  refine ⟨β, hβ, fun β' hβ' ↦ SmoothForm.mpullback_injective_of_surjective
    (contMDiff_baseProj ENat.LEInfty.out hπ le_rfl)
    (IteratedFiberProduct.surjective_baseProj_iff.2 hsurj)
    (fun y ↦ (isSubmersion_baseProj ENat.LEInfty.out hπ 0).surjective_mfderiv (by simp) y)
    (hβ'.trans hβ.symm)⟩

end Manifold

end TauCeti
