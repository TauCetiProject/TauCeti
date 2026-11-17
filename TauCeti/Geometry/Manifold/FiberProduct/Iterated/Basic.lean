/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Identity
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.MFDeriv.Pi
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.Submersion.Composition
import TauCeti.Geometry.Manifold.Diffeomorph.Pi
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Iterated submersion fibre products

Given `π : Y → M` and `k : ℕ`, `TauCeti.IteratedFiberProduct π k` (`Y ×_M ⋯ ×_M Y`) is the subtype
of `k`-tuples `y : Fin k → Y` whose images under `π` all agree. When `Y` and `M` are boundaryless
finite-dimensional real `C^n` manifolds (`1 ≤ n`) and `π` is a `C^n` submersion, this file equips
`IteratedFiberProduct π k` (`k ≥ 1`) with its canonical embedded `C^n` manifold structure of
dimension `k * dim Y - (k - 1) * dim M` (requiring neither `T2Space` nor
`SecondCountableTopology`), establishing Hausdorff closedness (`isClosedEmbedding_val`), smooth
universal properties (`contMDiff_iteratedFiberProduct_iff`, `contMDiffOn_iteratedFiberProduct_iff`),
tangent space (`mem_range_mfderiv_coe_iteratedFiberProduct_iff`), and local product normal form
(`exists_localNormalForm_iteratedFiberProduct`).

## References
* J.-L. Brylinski, *Loop Spaces, Characteristic Classes and Geometric Quantization*,
  Progress in Mathematics 107, Birkhäuser (1993), Chapter V.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Thms. 4.12, 6.30.
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416, §2.
* K. Waldorf, *String Connections and Chern–Simons 2-Gerbes*, arXiv:0906.0117, §2.
-/

public section

noncomputable section

open Function Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The `k`-fold iterated fibre product `Y ×_M ⋯ ×_M Y` of a map `π : Y → M`, realized as the
subtype of `k`-tuples in `Fin k → Y` whose images under `π` all agree. -/
abbrev IteratedFiberProduct {Y M : Type*} (π : Y → M) (k : ℕ) : Type _ :=
  {y : Fin k → Y // ∀ i j : Fin k, π (y i) = π (y j)}

namespace IteratedFiberProduct

variable {Y M : Type*} {π : Y → M} {k l m : ℕ}

@[ext] theorem ext {y z : IteratedFiberProduct π k} (h : ∀ i : Fin k, y.1 i = z.1 i) : y = z :=
  Subtype.ext (funext h)

/-- The `i`-th factor projection `IteratedFiberProduct π k → Y`. -/
def proj (i : Fin k) (y : IteratedFiberProduct π k) : Y := y.1 i
@[simp] theorem proj_mk (y : Fin k → Y) (hy : ∀ i j, π (y i) = π (y j)) (i : Fin k) :
    proj i (⟨y, hy⟩ : IteratedFiberProduct π k) = y i := (rfl)
@[simp] theorem val_apply (y : IteratedFiberProduct π k) (i : Fin k) : y.1 i = proj i y := (rfl)
theorem apply_proj_eq (y : IteratedFiberProduct π k) (i j : Fin k) :
    π (proj i y) = π (proj j y) := y.2 i j

/-- For `k ≥ 1`, the common base projection `IteratedFiberProduct π k → M`. -/
def baseProj [NeZero k] (y : IteratedFiberProduct π k) : M := π (proj 0 y)
@[simp] theorem baseProj_mk [NeZero k] (y : Fin k → Y) (hy : ∀ i j, π (y i) = π (y j)) :
    baseProj (⟨y, hy⟩ : IteratedFiberProduct π k) = π (y 0) := (rfl)
theorem proj_comp_eq_baseProj [NeZero k] (y : IteratedFiberProduct π k) (i : Fin k) :
    π (proj i y) = baseProj y := y.2 i 0
theorem comp_proj [NeZero k] (i : Fin k) :
    π ∘ (proj i : IteratedFiberProduct π k → Y) = baseProj :=
  funext fun y ↦ proj_comp_eq_baseProj y i

/-- Contravariant reindexing of `IteratedFiberProduct` along any map `α : Fin k → Fin l`. -/
def precomp (α : Fin k → Fin l) (y : IteratedFiberProduct π l) : IteratedFiberProduct π k :=
  ⟨y.1 ∘ α, fun i j ↦ y.2 (α i) (α j)⟩
@[simp] theorem proj_precomp (α : Fin k → Fin l) (y : IteratedFiberProduct π l) (i : Fin k) :
    proj i (precomp α y) = proj (α i) y := (rfl)
@[simp] theorem baseProj_precomp [NeZero k] [NeZero l] (α : Fin k → Fin l)
    (y : IteratedFiberProduct π l) : baseProj (precomp α y) = baseProj y := y.2 (α 0) 0
@[simp] theorem precomp_id (y : IteratedFiberProduct π k) : precomp id y = y := (rfl)
theorem precomp_comp (α : Fin k → Fin l) (β : Fin l → Fin m) (y : IteratedFiberProduct π m) :
    precomp (β ∘ α) y = precomp α (precomp β y) := (rfl)

/-- The constant-tuple map `Y → IteratedFiberProduct π k` repeating `y` in all `k` factors
(a smooth embedding for `k ≥ 1`; see `isSmoothEmbedding_constDiagonal`). -/
def constDiagonal (y : Y) (k : ℕ) : IteratedFiberProduct π k := ⟨fun _ ↦ y, fun _ _ ↦ rfl⟩
@[simp] theorem proj_constDiagonal (y : Y) (k : ℕ) (i : Fin k) :
    proj i (constDiagonal (π := π) y k) = y := (rfl)
@[simp] theorem baseProj_constDiagonal [NeZero k] (y : Y) :
    baseProj (constDiagonal (π := π) y k) = π y := (rfl)
theorem surjective_proj (i : Fin k) : Surjective (proj i : IteratedFiberProduct π k → Y) :=
  fun y ↦ ⟨constDiagonal y k, rfl⟩
theorem surjective_baseProj [NeZero k] (hπ : Surjective π) :
    Surjective (baseProj : IteratedFiberProduct π k → M) := fun x ↦ by
  obtain ⟨y, rfl⟩ := hπ x; exact ⟨constDiagonal y k, rfl⟩

/-- The multidiagonal `{m : Fin k → M | ∀ i j, m i = m j}` of `M^k`. -/
def multidiagonal (M : Type*) (k : ℕ) : Set (Fin k → M) := {x | ∀ i j : Fin k, x i = x j}
@[simp] theorem mem_multidiagonal {x : Fin k → M} :
    x ∈ multidiagonal M k ↔ ∀ i j : Fin k, x i = x j := Iff.rfl
theorem range_val_eq_preimage_multidiagonal :
    range (Subtype.val : IteratedFiberProduct π k → Fin k → Y) =
      (Pi.map fun _ : Fin k ↦ π) ⁻¹' multidiagonal M k := by ext y; simp

theorem isClosed_multidiagonal [TopologicalSpace M] [T2Space M] (k : ℕ) :
    IsClosed (multidiagonal M k) :=
  (by ext x; simp : multidiagonal M k = ⋂ (i : Fin k) (j : Fin k), {x | x i = x j}) ▸
    isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq (continuous_apply i) (continuous_apply j)

theorem isClosed_setOf_apply_eq [TopologicalSpace Y] [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosed {y : Fin k → Y | ∀ i j : Fin k, π (y i) = π (y j)} :=
  (isClosed_multidiagonal (M := M) k).preimage (continuous_pi fun i ↦ hπ.comp (continuous_apply i))

/-- When `M` is Hausdorff and `π : Y → M` is continuous, `Subtype.val` is a closed embedding. -/
theorem isClosedEmbedding_val [TopologicalSpace Y] [TopologicalSpace M] [T2Space M]
    (hπ : Continuous π) (k : ℕ) :
    IsClosedEmbedding (Subtype.val : IteratedFiberProduct π k → Fin k → Y) :=
  (isClosed_setOf_apply_eq hπ k).isClosedEmbedding_subtypeVal

theorem continuous_proj [TopologicalSpace Y] (i : Fin k) :
    Continuous (proj i : IteratedFiberProduct π k → Y) :=
  (continuous_apply i).comp continuous_subtype_val
theorem continuous_baseProj [TopologicalSpace Y] [TopologicalSpace M] [NeZero k]
    (hπ : Continuous π) : Continuous (baseProj : IteratedFiberProduct π k → M) :=
  hπ.comp (continuous_proj 0)

/-- For a continuous map `π : Y → M`, the 1-fold iterated fibre product is homeomorphic to the
graph fibre product `{p : Y × M // π p.1 = id p.2}`. -/
def oneHomeomorph [TopologicalSpace Y] [TopologicalSpace M] (hπ : Continuous π) :
    IteratedFiberProduct π 1 ≃ₜ {p : Y × M // π p.1 = id p.2} where
  toFun y := ⟨(y.1 0, π (y.1 0)), rfl⟩
  invFun p := ⟨fun _ ↦ p.1.1, fun _ _ ↦ rfl⟩
  left_inv y := Subtype.ext (funext fun i ↦ congrArg y.1 (Subsingleton.elim 0 i))
  right_inv p := Subtype.ext (Prod.ext rfl p.2)
  continuous_toFun := ((continuous_proj 0).prodMk (hπ.comp (continuous_proj 0))).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun _ ↦ continuous_fst.comp continuous_subtype_val).subtype_mk _

@[simp] theorem oneHomeomorph_apply [TopologicalSpace Y] [TopologicalSpace M]
    (hπ : Continuous π) (y : IteratedFiberProduct π 1) :
    oneHomeomorph hπ y = ⟨(y.1 0, π (y.1 0)), rfl⟩ := (rfl)
@[simp] theorem oneHomeomorph_symm_apply [TopologicalSpace Y] [TopologicalSpace M]
    (hπ : Continuous π) (p : {p : Y × M // π p.1 = id p.2}) :
    (oneHomeomorph hπ).symm p = ⟨fun _ ↦ p.1.1, fun _ _ ↦ rfl⟩ := (rfl)

/-- For `k ≥ 1`, splitting off the last coordinate identifies `IteratedFiberProduct π (k + 1)`
homeomorphically with `{p : IteratedFiberProduct π k × Y // baseProj p.1 = π p.2}`. -/
def snocHomeomorph [TopologicalSpace Y] (k : ℕ) [NeZero k] :
    IteratedFiberProduct π (k + 1) ≃ₜ
      {p : IteratedFiberProduct π k × Y // baseProj p.1 = π p.2} where
  toFun y := ⟨(y.precomp Fin.castSucc, proj (Fin.last k) y),
    (y.baseProj_precomp Fin.castSucc).trans (y.proj_comp_eq_baseProj (Fin.last k)).symm⟩
  invFun p := ⟨Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2, fun i j ↦
    have hall : ∀ l, π (Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 l) = baseProj p.1.1 :=
      Fin.lastCases (by rw [Fin.snoc_last (α := fun _ ↦ Y)]; exact p.2.symm)
        fun l ↦ by rw [Fin.snoc_castSucc (α := fun _ ↦ Y)]; exact p.1.1.proj_comp_eq_baseProj l
    (hall i).trans (hall j).symm⟩
  left_inv y := Subtype.ext (Fin.snoc_init_self y.1)
  right_inv p := Subtype.ext <| Prod.ext
    (Subtype.ext (Fin.init_snoc (α := fun _ ↦ Y) p.1.2 p.1.1.1))
    (Fin.snoc_last (α := fun _ ↦ Y) p.1.2 p.1.1.1)
  continuous_toFun := (((continuous_pi fun j : Fin k ↦ continuous_proj j.castSucc).subtype_mk _)
    |>.prodMk (continuous_proj (Fin.last k))).subtype_mk _
  continuous_invFun := (continuous_pi <| Fin.lastCases
    ((continuous_snd.comp continuous_subtype_val).congr fun p ↦
      (Fin.snoc_last (α := fun _ ↦ Y) p.1.2 p.1.1.1).symm)
    fun j ↦ ((continuous_proj j).comp (continuous_fst.comp continuous_subtype_val)).congr fun p ↦
      (Fin.snoc_castSucc (α := fun _ ↦ Y) p.1.2 p.1.1.1 j).symm).subtype_mk _

@[simp] theorem snocHomeomorph_apply [TopologicalSpace Y] (k : ℕ) [NeZero k]
    (y : IteratedFiberProduct π (k + 1)) : snocHomeomorph (π := π) k y =
      ⟨(y.precomp Fin.castSucc, proj (Fin.last k) y),
        (y.baseProj_precomp Fin.castSucc).trans (y.proj_comp_eq_baseProj (Fin.last k)).symm⟩ :=
  (rfl)
@[simp] theorem snocHomeomorph_symm_apply [TopologicalSpace Y] (k : ℕ) [NeZero k]
    (p : {p : IteratedFiberProduct π k × Y // baseProj p.1 = π p.2}) (i : Fin (k + 1)) :
    proj i ((snocHomeomorph (π := π) k).symm p) = Fin.snoc (α := fun _ ↦ Y) p.1.1.1 p.1.2 i :=
  proj_mk _ _ i

end IteratedFiberProduct

section Dimension

/-- Expected dimension `k * dim Y - (k - 1) * dim M` of the `k`-fold iterated fibre product of a
submersion `Y → M`. -/
def iteratedFiberProductDim (EY EM : Type*) [AddCommGroup EY] [Module ℝ EY]
    [AddCommGroup EM] [Module ℝ EM] (k : ℕ) : ℕ :=
  k * finrank ℝ EY - (k - 1) * finrank ℝ EM

section

variable (EY EM : Type*) [AddCommGroup EY] [Module ℝ EY] [AddCommGroup EM] [Module ℝ EM]

/-- Characteristic formula for `iteratedFiberProductDim`. -/
theorem iteratedFiberProductDim_def (k : ℕ) :
    iteratedFiberProductDim EY EM k = k * finrank ℝ EY - (k - 1) * finrank ℝ EM := (rfl)

@[simp] theorem iteratedFiberProductDim_one :
    iteratedFiberProductDim EY EM 1 = finrank ℝ EY := by simp [iteratedFiberProductDim_def]
@[simp] theorem iteratedFiberProductDim_two :
    iteratedFiberProductDim EY EM 2 = finrank ℝ EY + finrank ℝ EY - finrank ℝ EM := by
  simp [iteratedFiberProductDim_def, two_mul]

theorem iteratedFiberProductDim_succ {k : ℕ} [NeZero k] :
    iteratedFiberProductDim EY EM (k + 1) =
      iteratedFiberProductDim EY EM k + finrank ℝ EY - finrank ℝ EM := by
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  simp only [iteratedFiberProductDim_def, Nat.add_sub_cancel, Nat.succ_mul]
  by_cases h : m * finrank ℝ EM ≤ m * finrank ℝ EY + finrank ℝ EY
  · omega
  · have : finrank ℝ EY < finrank ℝ EM := by
      by_contra hba; have := Nat.mul_le_mul_left m (not_lt.mp hba); omega
    omega

theorem finrank_le_iteratedFiberProductDim {EY EM : Type*} [AddCommGroup EY] [Module ℝ EY]
    [AddCommGroup EM] [Module ℝ EM] (hle : finrank ℝ EM ≤ finrank ℝ EY) (k : ℕ) [NeZero k] :
    finrank ℝ EM ≤ iteratedFiberProductDim EY EM k := by
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  induction m with
  | zero => simpa using hle
  | succ m ih => rw [iteratedFiberProductDim_succ EY EM (k := m + 1)]; omega

theorem iteratedFiberProductDim_add {a b : ℕ} [NeZero a] [NeZero b]
    (hle : finrank ℝ EM ≤ finrank ℝ EY) :
    iteratedFiberProductDim EY EM (a + b) =
      iteratedFiberProductDim EY EM a + iteratedFiberProductDim EY EM b - finrank ℝ EM := by
  have hda := finrank_le_iteratedFiberProductDim hle a
  rcases b with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  induction m with
  | zero => rw [iteratedFiberProductDim_succ, iteratedFiberProductDim_one]
  | succ m ih =>
    have hdm := finrank_le_iteratedFiberProductDim hle (m + 1)
    rw [← add_assoc, iteratedFiberProductDim_succ EY EM (k := a + (m + 1)), ih,
      iteratedFiberProductDim_succ EY EM (k := m + 1)]; omega

@[simp] theorem iteratedFiberProductDim_self (k : ℕ) [NeZero k] :
    iteratedFiberProductDim EM EM k = finrank ℝ EM := by
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  simp [iteratedFiberProductDim_def, Nat.succ_mul]

end

end Dimension

section Manifold

open IteratedFiberProduct (proj baseProj val_apply proj_mk continuous_proj continuous_baseProj
  oneHomeomorph snocHomeomorph oneHomeomorph_apply snocHomeomorph_apply)

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}

/-- **Existence of the embedded manifold structure on iterated submersion fibre products.** -/
theorem exists_isManifold_iteratedFiberProduct [IsManifold IY n Y] [IsManifold IM n M]
    [IY.Boundaryless] [IM.Boundaryless] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
    {π : Y → M} (k : ℕ) [hk : NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    ∃ cs : ChartedSpace (Fin (iteratedFiberProductDim EY EM k) → ℝ) (IteratedFiberProduct π k),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (IteratedFiberProduct π k) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
        (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
        (Subtype.val : IteratedFiberProduct π k → Fin k → Y) ∧
      Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM n
        (baseProj : IteratedFiberProduct π k → M) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  revert hk; induction m with
  | zero =>
    -- Base case `k = 1`: pull back `{p : Y × M // π p.1 = id p.2}` along `oneHomeomorph`.
    intro
    have hd₁ : iteratedFiberProductDim EY EM 1 = finrank ℝ EY + finrank ℝ EM - finrank ℝ EM := by
      simp [iteratedFiberProductDim_def]
    rw [hd₁]; let d₁ := finrank ℝ EY + finrank ℝ EM - finrank ℝ EM
    let := transverseFiberProductChartedSpace hn hπ.contMDiff (contMDiff_id (I := IM))
      (fun p _ ↦ transverse_id_right π p)
    have := isManifold_transverseFiberProduct hn hπ.contMDiff (contMDiff_id (I := IM))
      (fun p _ ↦ transverse_id_right π p)
    let e₁ := oneHomeomorph hπ.contMDiff.continuous
    let cs₁ := e₁.pullbackChartedSpace (H := Fin d₁ → ℝ); let := cs₁
    have hman₁ := e₁.pullback_isManifold 𝓘(ℝ, Fin d₁ → ℝ) n
    let ΦY := (e₁.pullbackDiffeomorph 𝓘(ℝ, Fin d₁ → ℝ) n).trans
      (transverseFiberProductIdRightDiffeomorph hn hπ.contMDiff)
    let ΦPi := ΦY.trans (Diffeomorph.funUnique (Fin 1) IY Y n).symm
    have hΦY (y : IteratedFiberProduct π 1) : ΦY y = y.1 0 := by
      simp only [ΦY, Diffeomorph.coe_trans, Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph,
        e₁, oneHomeomorph_apply]
      exact transverseFiberProductIdRightDiffeomorph_apply hn hπ.contMDiff _
    have hval_eq : (Subtype.val : IteratedFiberProduct π 1 → Fin 1 → Y) = ⇑ΦPi := by
      ext y i; simp only [ΦPi, Diffeomorph.coe_trans, Function.comp_apply,
        Diffeomorph.funUnique_symm_apply, hΦY y]
      exact congrArg y.1 (Subsingleton.elim i 0)
    have hemb₁ : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d₁ → ℝ)
        (ModelWithCorners.pi fun _ : Fin 1 ↦ IY) n ⇑ΦPi := by
      simpa [Function.comp_id] using ΦPi.isSmoothEmbedding_comp hn Manifold.IsSmoothEmbedding.id
    have hbase_eq : (baseProj : IteratedFiberProduct π 1 → M) = π ∘ ⇑ΦY :=
      funext fun y ↦ congrArg π (hΦY y).symm
    exact ⟨cs₁, hman₁, hval_eq.symm ▸ hemb₁, hbase_eq ▸ hπ.comp (ΦY.isSubmersion hn0)⟩
  | succ m ih =>
    -- Inductive step `k = m + 2`: pull back the transverse fibre product along `snocHomeomorph`,
    -- then compose smooth embeddings through `Diffeomorph.piSnoc`.
    intro; obtain ⟨csk, hmank, hembk, hsubk⟩ := ih (hk := inferInstance); let := csk
    have hd : iteratedFiberProductDim EY EM (m + 2) =
        finrank ℝ (Fin (iteratedFiberProductDim EY EM (m + 1)) → ℝ) +
          finrank ℝ EY - finrank ℝ EM := by
      simpa [Module.finrank_fin_fun] using iteratedFiberProductDim_succ EY EM (k := m + 1)
    rw [hd]; let d' := finrank ℝ (Fin (iteratedFiberProductDim EY EM (m + 1)) → ℝ) +
      finrank ℝ EY - finrank ℝ EM
    let htr := fun (p : IteratedFiberProduct π (m + 1) × Y) (_ : baseProj p.1 = π p.2) ↦
      hsubk.transverse_left (IY := IY) hn0 π p
    let B := {p : IteratedFiberProduct π (m + 1) × Y // baseProj p.1 = π p.2}
    let := transverseFiberProductChartedSpace hn hsubk.contMDiff hπ.contMDiff htr
    have := isManifold_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htr
    have hembB := isSmoothEmbedding_coe_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htr
    have hsubB := isSubmersion_fst_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htr hπ
    let e := snocHomeomorph (π := π) (m + 1)
    let cs' := e.pullbackChartedSpace (H := Fin d' → ℝ); let := cs'
    have hman' := e.pullback_isManifold 𝓘(ℝ, Fin d' → ℝ) n
    let ΦB := e.pullbackDiffeomorph 𝓘(ℝ, Fin d' → ℝ) n
    have hembΦB : Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin d' → ℝ) 𝓘(ℝ, Fin d' → ℝ) n ⇑ΦB := by
      simpa [Function.comp_id] using ΦB.isSmoothEmbedding_comp hn Manifold.IsSmoothEmbedding.id
    let ΦSnoc := Diffeomorph.piSnoc (fun _ : Fin (m + 2) ↦ IY) (fun _ ↦ Y) n
    have hembChain := ΦSnoc.isSmoothEmbedding_comp hn <|
      (hembk.prodMap (Manifold.IsSmoothEmbedding.id (I := IY) (M := Y))).comp
        (hembB.comp hembΦB hn) hn
    have hval_eq : (Subtype.val : IteratedFiberProduct π (m + 2) → Fin (m + 2) → Y) =
        ⇑ΦSnoc ∘ Prod.map (Subtype.val : IteratedFiberProduct π (m + 1) → Fin (m + 1) → Y)
          (@id Y) ∘ (Subtype.val : B → IteratedFiberProduct π (m + 1) × Y) ∘ ⇑ΦB := by
      ext y i; simp only [ΦSnoc, ΦB, e, Function.comp_apply, Homeomorph.coe_pullbackDiffeomorph,
        snocHomeomorph_apply, Prod.map_apply, id_eq, Diffeomorph.piSnoc_apply]
      exact (congrFun (Fin.snoc_init_self y.1) i).symm
    have hbase_eq : (baseProj : IteratedFiberProduct π (m + 2) → M) =
        (baseProj : IteratedFiberProduct π (m + 1) → M) ∘ (fun p : B ↦ p.1.1) ∘ ⇑ΦB :=
      funext fun y ↦ by simp [ΦB, e, snocHomeomorph_apply]
    exact ⟨cs', hman', hval_eq.symm ▸ hembChain,
      hbase_eq ▸ hsubk.comp (hsubB.comp (ΦB.isSubmersion hn0))⟩

variable [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] {π : Y → M}

/-- Chosen `C^n` atlas on `IteratedFiberProduct π k` (`k ≥ 1`) for a `C^n` submersion `π : Y → M`
(`1 ≤ n`), scoped via `letI` on the inherited subspace topology. -/
@[instance_reducible]
noncomputable def iteratedFiberProductChartedSpace (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    ChartedSpace (Fin (iteratedFiberProductDim EY EM k) → ℝ) (IteratedFiberProduct π k) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose

/-- Equipped with the chosen atlas `iteratedFiberProductChartedSpace k hn hπ`,
`IteratedFiberProduct π k` (`k ≥ 1`) is a `C^n` manifold modelled on
`Fin (iteratedFiberProductDim EY EM k) → ℝ`. -/
theorem isManifold_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    IsManifold 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (IteratedFiberProduct π k) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose_spec.1

/-- Under the chosen atlas `iteratedFiberProductChartedSpace k hn hπ`, the canonical inclusion
`Subtype.val : IteratedFiberProduct π k → Fin k → Y` (`k ≥ 1`) is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_coe_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      (ModelWithCorners.pi fun _ : Fin k ↦ IY) n
      (Subtype.val : IteratedFiberProduct π k → Fin k → Y) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose_spec.2.1

/-- Under the chosen atlas `iteratedFiberProductChartedSpace k hn hπ`, the common base projection
`IteratedFiberProduct.baseProj : IteratedFiberProduct π k → M` (`k ≥ 1`) is a `C^n` submersion. -/
theorem isSubmersion_baseProj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM n
      (baseProj : IteratedFiberProduct π k → M) :=
  (exists_isManifold_iteratedFiberProduct k hn hπ).choose_spec.2.2

/-- **Smooth universal property of `IteratedFiberProduct`.** -/
theorem contMDiff_iteratedFiberProduct_iff
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) {g : Z → IteratedFiberProduct π k} :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff IZ 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m g ↔
      ∀ i : Fin k, ContMDiff IZ IY m (fun z ↦ proj i (g z)) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  rw [((isSmoothEmbedding_coe_iteratedFiberProduct k hn hπ).of_le hmn).contMDiff_iff_comp,
    contMDiff_pi_iff]; rfl

/-- **Smooth universal property on subsets.** -/
theorem contMDiffOn_iteratedFiberProduct_iff
    {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) {g : Z → IteratedFiberProduct π k} {s : Set Z} :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiffOn IZ 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m g s ↔
      ∀ i : Fin k, ContMDiffOn IZ IY m (fun z ↦ proj i (g z)) s := by
  let := iteratedFiberProductChartedSpace k hn hπ
  rw [((isSmoothEmbedding_coe_iteratedFiberProduct k hn hπ).of_le hmn).contMDiffOn_iff_comp,
    contMDiffOn_pi_iff]; rfl

/-- Each factor projection `IteratedFiberProduct.proj i` (`k ≥ 1`) is `C^m` for `m ≤ n`. -/
theorem contMDiff_proj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) (i : Fin k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IY m
      (proj i : IteratedFiberProduct π k → Y) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact ((contMDiff_iteratedFiberProduct_iff hn hπ hmn (g := id)).1 contMDiff_id) i

/-- The base projection `IteratedFiberProduct.baseProj` (`k ≥ 1`) is `C^m` for `m ≤ n`. -/
theorem contMDiff_baseProj_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM m
      (baseProj : IteratedFiberProduct π k → M) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact (hπ.contMDiff.of_le hmn).comp (contMDiff_proj_iteratedFiberProduct k hn hπ hmn 0)

/-- Reindexing `IteratedFiberProduct.precomp α` (`k, l ≥ 1`) is `C^m` for `m ≤ n`. -/
theorem IteratedFiberProduct.contMDiff_precomp {k l : ℕ} [NeZero k] [NeZero l] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) (α : Fin k → Fin l) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace l hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM l) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m
      (IteratedFiberProduct.precomp (π := π) α) := by
  let := iteratedFiberProductChartedSpace k hn hπ; let := iteratedFiberProductChartedSpace l hn hπ
  exact (contMDiff_iteratedFiberProduct_iff hn hπ hmn).2 fun i ↦
    contMDiff_proj_iteratedFiberProduct l hn hπ hmn (α i)

omit [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless] in
/-- For `k = m + 1`, the pairwise `dπ`-agreement equations at `y` define a surjective linear map
whose kernel has dimension `iteratedFiberProductDim EY EM (m + 1)`. -/
private theorem exists_tangentConstraint_surjective_finrank_ker (m : ℕ) (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π (m + 1)) :
    ∃ T : TangentSpace (ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY) y.1 →ₗ[ℝ]
        (Fin m → TangentSpace IM (π (proj 0 y))),
      (∀ w j, T w j =
        tangentSpaceCast IM (π (proj j.succ y)) (π (proj 0 y))
          (mfderiv IY IM π (proj j.succ y) (w j.succ)) - mfderiv IY IM π (proj 0 y) (w 0)) ∧
      finrank ℝ (LinearMap.ker T) = iteratedFiberProductDim EY EM (m + 1) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let IPi := ModelWithCorners.pi fun _ : Fin (m + 1) ↦ IY
  let V := TangentSpace IPi y.1; let TM₀ := TangentSpace IM (π (proj 0 y))
  let eV : V ≃ₗ[ℝ] (Fin (m + 1) → EY) := (tangentSpaceCastModel IPi y.1).toLinearEquiv
  have : FiniteDimensional ℝ V := eV.symm.finiteDimensional
  have : FiniteDimensional ℝ TM₀ :=
    (tangentSpaceCastModel IM (π (proj 0 y))).symm.toLinearEquiv.finiteDimensional
  let cLin (j : Fin m) : TangentSpace IM (π (proj j.succ y)) →ₗ[ℝ] TM₀ :=
    (tangentSpaceCast IM (π (proj j.succ y)) (π (proj 0 y))).toLinearEquiv.toLinearMap
  let dLin (i : Fin (m + 1)) : EY →ₗ[ℝ] TangentSpace IM (π (proj i y)) :=
    (mfderiv IY IM π (proj i y)).toLinearMap.comp
      (tangentSpaceCastModel IY (proj i y)).symm.toLinearEquiv.toLinearMap
  let T : V →ₗ[ℝ] (Fin m → TM₀) := LinearMap.pi fun j ↦
    (cLin j).comp ((dLin j.succ).comp ((LinearMap.proj j.succ).comp eV.toLinearMap)) -
      (dLin 0).comp ((LinearMap.proj 0).comp eV.toLinearMap)
  have hT_surj : Surjective T := fun z ↦ by
    let u (j : Fin m) : EY := tangentSpaceCastModel IY (proj j.succ y) <|
      Classical.choose <| hπ.surjective_mfderiv hn0 (proj j.succ y)
        ((tangentSpaceCast IM (π (proj j.succ y)) (π (proj 0 y))).symm (z j))
    have hu (j : Fin m) : dLin j.succ (u j) =
        (tangentSpaceCast IM (π (proj j.succ y)) (π (proj 0 y))).symm (z j) := by
      simp only [dLin, u, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.symm_apply_apply]
      exact Classical.choose_spec <| hπ.surjective_mfderiv hn0 (proj j.succ y) _
    refine ⟨eV.symm (Fin.cons (α := fun _ ↦ EY) 0 u), funext fun j ↦ ?_⟩
    simp only [T, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, eV.apply_symm_apply, LinearMap.proj_apply,
      Fin.cons_succ (α := fun _ ↦ EY), Fin.cons_zero (α := fun _ ↦ EY), map_zero, sub_zero,
      hu j, cLin, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨T, fun _ _ ↦ rfl, ?_⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker T
  rw [LinearMap.range_eq_top.2 hT_surj, finrank_top, Module.finrank_pi_fintype, eV.finrank_eq,
    Module.finrank_pi_fintype] at hrk
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, TM₀,
    (tangentSpaceCastModel IM (π (proj 0 y))).toLinearEquiv.finrank_eq] at hrk
  simp only [iteratedFiberProductDim_def, Nat.add_sub_cancel]
  exact Nat.eq_sub_of_add_eq' hrk

/-- **Tangent space of `IteratedFiberProduct`.** -/
theorem mem_range_mfderiv_coe_iteratedFiberProduct_iff (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y : IteratedFiberProduct π k)
    (v : TangentSpace (ModelWithCorners.pi fun _ : Fin k ↦ IY) y.1) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    v ∈ (mfderiv 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      (ModelWithCorners.pi fun _ : Fin k ↦ IY)
      (Subtype.val : IteratedFiberProduct π k → Fin k → Y) y).range ↔
      ∀ i j : Fin k, mfderiv IY IM π (proj i y) (v i) =
        tangentSpaceCast IM (π (proj j y)) (π (proj i y)) (mfderiv IY IM π (proj j y) (v j)) := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hemb := isSmoothEmbedding_coe_iteratedFiberProduct k hn hπ
  let Ik (d : ℕ) := 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM d) → ℝ)
  let IPi (d : ℕ) := ModelWithCorners.pi fun _ : Fin d ↦ IY
  -- Forward direction: differentiate the defining identities `π ∘ proj i = π ∘ proj j`.
  have hproj_mfderiv (i : Fin k) (u) :
      mfderiv (Ik k) IY (proj i : IteratedFiberProduct π k → Y) y u =
        (mfderiv (Ik k) (IPi k) (Subtype.val : IteratedFiberProduct π k → Fin k → Y) y u) i := by
    have hc := mfderiv_comp (I' := IPi k) y (hasMFDerivAt_apply i y.1).mdifferentiableAt
      ((hemb.contMDiff y).mdifferentiableAt hn0)
    rw [mfderiv_apply] at hc; exact DFunLike.congr_fun hc u
  have hfwd : ∀ w ∈ (mfderiv (Ik k) (IPi k)
      (Subtype.val : IteratedFiberProduct π k → Fin k → Y) y).range,
      ∀ i j : Fin k, mfderiv IY IM π (proj i y) (w i) =
        tangentSpaceCast IM (π (proj j y)) (π (proj i y)) (mfderiv IY IM π (proj j y) (w j)) := by
    rintro _ ⟨u, rfl⟩ i j
    have heq : (π ∘ proj i : IteratedFiberProduct π k → M) =ᶠ[𝓝 y] π ∘ proj j :=
      Filter.Eventually.of_forall fun z ↦ z.apply_proj_eq i j
    have hm := DFunLike.congr_fun (heq.mfderiv_eq (I := Ik k) (I' := IM)) u
    rw [mfderiv_comp y ((hπ.contMDiff (proj i y)).mdifferentiableAt hn0)
        ((contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl i y).mdifferentiableAt hn0),
      mfderiv_comp y ((hπ.contMDiff (proj j y)).mdifferentiableAt hn0)
        ((contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl j y).mdifferentiableAt hn0)] at hm
    dsimp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at hm
    rwa [hproj_mfderiv i u, hproj_mfderiv j u] at hm
  refine ⟨hfwd v, fun hv ↦ ?_⟩
  -- Reverse direction: match the range against `ker T` by finite-dimensionality and rank-nullity.
  rcases k with _ | m; · exact False.elim (NeZero.ne 0 rfl)
  obtain ⟨T, hT_apply, hdim_ker⟩ := exists_tangentConstraint_surjective_finrank_ker m hn hπ y
  have : FiniteDimensional ℝ (TangentSpace (IPi (m + 1)) y.1) :=
    (tangentSpaceCastModel (IPi (m + 1)) y.1).symm.toLinearEquiv.finiteDimensional
  have hle_ker : (mfderiv (Ik (m + 1)) (IPi (m + 1))
      (Subtype.val : IteratedFiberProduct π (m + 1) → Fin (m + 1) → Y) y).range ≤
      LinearMap.ker T := fun w hw ↦ by
    rw [LinearMap.mem_ker]; ext j; rw [hT_apply]; exact sub_eq_zero.2 (hfwd w hw 0 j.succ).symm
  have hdim_rng : finrank ℝ (mfderiv (Ik (m + 1)) (IPi (m + 1))
      (Subtype.val : IteratedFiberProduct π (m + 1) → Fin (m + 1) → Y) y).range =
      iteratedFiberProductDim EY EM (m + 1) := by
    rw [LinearMap.finrank_range_of_inj ((hemb.isImmersion.isImmersionAt y).mfderiv_injective hn0),
      (tangentSpaceCastModel _ y).toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  rw [Submodule.eq_of_le_of_finrank_eq hle_ker (hdim_rng.trans hdim_ker.symm), LinearMap.mem_ker]
  ext j; rw [hT_apply]; exact sub_eq_zero.2 (hv 0 j.succ).symm

/-- Around any `y₀ : IteratedFiberProduct π k`, align submersion charts `φ i` over the base chart
`ψ := chartAt HM (baseProj y₀)` and shrink to an open product rectangle `U ×ˢ Set.pi univ V`
whose fibrewise preimages under `L i` land inside the extended chart targets `(φ i).extend IY`. -/
private theorem exists_aligned_submersion_product_rect {k : ℕ} [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y₀ : IteratedFiberProduct π k) :
    let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
    let ψ := chartAt HM (baseProj y₀)
    ∃ (φ : Fin k → OpenPartialHomeomorph Y HY) (L : Fin k → (EY ≃L[ℝ] EM × F))
      (U : Set EM) (V : Fin k → Set F),
      (∀ i, y₀.1 i ∈ (φ i).source) ∧ (∀ i, φ i ∈ IsManifold.maximalAtlas IY n Y) ∧
      (∀ i, ∀ w ∈ ((φ i).extend IY).target,
        π (((φ i).extend IY).symm w) = (ψ.extend IM).symm (L i w).1 ∧
        ψ.extend IM (π (((φ i).extend IY).symm w)) = (L i w).1) ∧
      IsOpen U ∧ (∀ i, IsOpen (V i)) ∧ U ⊆ (ψ.extend IM).target ∧
      ψ.extend IM (baseProj y₀) ∈ U ∧ (∀ i, (L i ((φ i).extend IY (y₀.1 i))).2 ∈ V i) ∧
      ∀ {p : EM × (Fin k → F)}, p ∈ U ×ˢ Set.pi univ V → ∀ i,
        (L i).symm (p.1, p.2 i) ∈ ((φ i).extend IY).target := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ
  let x₀ := baseProj y₀; let ψ := chartAt HM x₀
  have hπF := hπ.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv hn
    (hπ.surjective_mfderiv hn0)
  let L : Fin k → (EY ≃L[ℝ] EM × F) := fun i ↦ (hπF.isSubmersionAt (y₀.1 i)).equiv
  choose φ hy₀_src hφ_max _ hφ_main using fun i : Fin k ↦
    (hπF.isSubmersionAt (y₀.1 i)).exists_domChart_of_codChart
      (by rw [val_apply, y₀.proj_comp_eq_baseProj i]; exact mem_chart_source _ _)
      (IsManifold.chart_mem_maximalAtlas x₀)
  have hφ_tgt_open (i : Fin k) : IsOpen (((φ i).extend IY).target) := by
    rw [(φ i).extend_target, IY.range_eq_univ, inter_univ]
    exact (φ i).open_target.preimage IY.continuous_symm
  have hψ_tgt_open : IsOpen ((ψ.extend IM).target) := by
    rw [ψ.extend_target, IM.range_eq_univ, inter_univ]
    exact ψ.open_target.preimage IM.continuous_symm
  let u₀ : EM := ψ.extend IM x₀; let v₀ : Fin k → F := fun i ↦ (L i ((φ i).extend IY (y₀.1 i))).2
  have hmem_W (i : Fin k) : (L i).symm (u₀, v₀ i) ∈ ((φ i).extend IY).target := by
    have hw₀ := ((φ i).extend IY).map_source ((φ i).extend_source (I := IY) ▸ hy₀_src i)
    have hfst : (L i ((φ i).extend IY (y₀.1 i))).1 = u₀ := by
      rw [← (hφ_main i _ hw₀).2.2, ((φ i).extend IY).left_inv (by simpa using hy₀_src i)]
      exact congrArg (ψ.extend IM) (y₀.proj_comp_eq_baseProj i)
    have hp₀ : (u₀, v₀ i) = L i ((φ i).extend IY (y₀.1 i)) := Prod.ext hfst.symm rfl
    rw [hp₀, ContinuousLinearEquiv.symm_apply_apply]; exact hw₀
  choose Ui V hUi_open hV_open hu₀_Ui hv₀_V hUiV_sub using fun i : Fin k ↦
    isOpen_prod_iff.1 ((hφ_tgt_open i).preimage (L i).symm.continuous) u₀ (v₀ i) (hmem_W i)
  refine ⟨φ, L, (ψ.extend IM).target ∩ ⋂ i : Fin k, Ui i, V, hy₀_src, hφ_max,
    fun i w hw ↦ (hφ_main i w hw).2, hψ_tgt_open.inter (isOpen_iInter_of_finite hUi_open),
    hV_open, inter_subset_left,
    ⟨(ψ.extend IM).map_source (ψ.extend_source (I := IM) ▸ mem_chart_source HM x₀),
      mem_iInter.2 hu₀_Ui⟩,
    hv₀_V, fun hp i ↦ hUiV_sub i ⟨mem_iInter.1 hp.1.2 i, hp.2 i (mem_univ i)⟩⟩

/-- **Local product normal form of `IteratedFiberProduct`.** -/
theorem exists_localNormalForm_iteratedFiberProduct (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (y₀ : IteratedFiberProduct π k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ∃ (U : Set EM) (V : Fin k → Set (Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
      (Φ : PartialDiffeomorph
        𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
        𝓘(ℝ, EM × (Fin k → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ))
        (IteratedFiberProduct π k)
        (EM × (Fin k → Fin (finrank ℝ EY - finrank ℝ EM) → ℝ)) n),
      IsOpen U ∧ (∀ i, IsOpen (V i)) ∧ y₀ ∈ Φ.source ∧ Φ.target = U ×ˢ Set.pi univ V ∧
      (∀ y ∈ Φ.source,
        baseProj y ∈ (chartAt HM (baseProj y₀)).source ∧
        (Φ y).1 = extChartAt IM (baseProj y₀) (baseProj y)) ∧
      (∀ p ∈ Φ.target, baseProj (Φ.symm p) = (extChartAt IM (baseProj y₀)).symm p.1) := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  let F := Fin (finrank ℝ EY - finrank ℝ EM) → ℝ; let x₀ := baseProj y₀; let ψ := chartAt HM x₀
  have hψ_max : ψ ∈ IsManifold.maximalAtlas IM n M := IsManifold.chart_mem_maximalAtlas x₀
  -- Step 1: obtain aligned submersion charts `(φ, L)` over `ψ` and an open product target `T`.
  obtain ⟨φ, L, U, V, hy₀_src, hφ_max, hφ_eq, hU_open, hV_open, hU_sub, hu₀_U, hv₀_V,
    hp_mem_tgt⟩ := exists_aligned_submersion_product_rect hn hπ y₀
  let T : Set (EM × (Fin k → F)) := U ×ˢ Set.pi univ V
  have hT_open : IsOpen T := hU_open.prod (isOpen_set_pi finite_univ fun i _ ↦ hV_open i)
  -- Step 2: define the open chart domain `Ω`, forward coordinate map `toFun`, and inverse `invFun`.
  let Ω : Set (IteratedFiberProduct π k) :=
    {y | baseProj y ∈ ψ.source ∧ ψ.extend IM (baseProj y) ∈ U ∧
      ∀ i : Fin k, y.1 i ∈ (φ i).source ∧ (L i ((φ i).extend IY (y.1 i))).2 ∈ V i}
  have hΩ_open : IsOpen Ω := by
    have hS₀ := ((by simpa using ψ.continuousOn_extend (I := IM) :
      ContinuousOn (ψ.extend IM) ψ.source).isOpen_inter_preimage ψ.open_source hU_open).preimage
        (continuous_baseProj (k := k) hπ.contMDiff.continuous)
    have hS₁ (i : Fin k) : IsOpen {y : IteratedFiberProduct π k |
        y.1 i ∈ (φ i).source ∧ (L i ((φ i).extend IY (y.1 i))).2 ∈ V i} :=
      (((continuous_snd.comp (L i).continuous).comp_continuousOn
        (by simpa using (φ i).continuousOn_extend (I := IY))).isOpen_inter_preimage
          (φ i).open_source (hV_open i)).preimage (continuous_proj i)
    convert hS₀.inter (isOpen_iInter_of_finite hS₁) using 1
    ext y; simp [Ω, and_assoc]
  let toFun : IteratedFiberProduct π k → EM × (Fin k → F) := fun y ↦
    (ψ.extend IM (baseProj y), fun i ↦ (L i ((φ i).extend IY (y.1 i))).2)
  let raw : EM × (Fin k → F) → Fin k → Y := fun p i ↦
    ((φ i).extend IY).symm ((L i).symm (p.1, p.2 i))
  have hraw_mem {p} (hp : p ∈ T) (i j : Fin k) : π (raw p i) = π (raw p j) := by
    simp only [raw, (hφ_eq _ _ (hp_mem_tgt hp _)).1, ContinuousLinearEquiv.apply_symm_apply]
  classical
  let invFun : EM × (Fin k → F) → IteratedFiberProduct π k := fun p ↦
    if hp : p ∈ T then ⟨raw p, hraw_mem hp⟩ else y₀
  have hinv_proj {p} (hp : p ∈ T) (i : Fin k) : proj i (invFun p) = raw p i := by simp [invFun, hp]
  have hinv_base {p} (hp : p ∈ T) : baseProj (invFun p) = (ψ.extend IM).symm p.1 := by
    rw [← IteratedFiberProduct.proj_comp_eq_baseProj (invFun p) 0, hinv_proj hp 0]
    simpa [raw] using (hφ_eq 0 _ (hp_mem_tgt hp 0)).1
  -- Step 3: assemble the `PartialDiffeomorph` and verify `C^n` smoothness on `Ω` and `T`.
  let Φ : PartialDiffeomorph
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) 𝓘(ℝ, EM × (Fin k → F))
      (IteratedFiberProduct π k) (EM × (Fin k → F)) n :=
    { toFun := toFun, invFun := invFun, source := Ω, target := T
      map_source' := fun _ hy ↦ ⟨hy.2.1, fun i _ ↦ (hy.2.2 i).2⟩
      map_target' := fun p hp ↦
        ⟨by rw [hinv_base hp]; simpa using (ψ.extend IM).map_target (hU_sub hp.1),
        by rw [hinv_base hp, (ψ.extend IM).right_inv (hU_sub hp.1)]; exact hp.1,
        fun i ↦ ⟨by rw [val_apply, hinv_proj hp i]; simpa [raw] using
          ((φ i).extend IY).map_target (hp_mem_tgt hp i),
        by rw [val_apply, hinv_proj hp i]; simp only [raw, ((φ i).extend IY).right_inv
          (hp_mem_tgt hp i), ContinuousLinearEquiv.apply_symm_apply]; exact hp.2 i (mem_univ i)⟩⟩
      left_inv' := fun y hy ↦ IteratedFiberProduct.ext fun i ↦ by
        rw [val_apply, hinv_proj ⟨hy.2.1, fun j _ ↦ (hy.2.2 j).2⟩ i]
        have hw := ((φ i).extend IY).map_source ((φ i).extend_source (I := IY) ▸ (hy.2.2 i).1)
        have hfst : (L i ((φ i).extend IY (y.1 i))).1 = ψ.extend IM (baseProj y) := by
          rw [← (hφ_eq i _ hw).2, ((φ i).extend IY).left_inv (by simpa using (hy.2.2 i).1)]
          exact congrArg (ψ.extend IM) (y.proj_comp_eq_baseProj i)
        have hpair : (ψ.extend IM (baseProj y), (L i ((φ i).extend IY (y.1 i))).2) =
            L i ((φ i).extend IY (y.1 i)) := Prod.ext hfst.symm rfl
        dsimp only [raw, toFun]; rw [hpair, ContinuousLinearEquiv.symm_apply_apply]
        exact ((φ i).extend IY).left_inv (by simpa using (hy.2.2 i).1)
      right_inv' := fun p hp ↦ Prod.ext
        (by dsimp only [toFun]; rw [hinv_base hp]; exact (ψ.extend IM).right_inv (hU_sub hp.1))
        (funext fun i ↦ by dsimp only [toFun]; rw [val_apply, hinv_proj hp i]; simp only [raw,
          ((φ i).extend IY).right_inv (hp_mem_tgt hp i), ContinuousLinearEquiv.apply_symm_apply])
      open_source := hΩ_open, open_target := hT_open
      contMDiffOn_toFun :=
        ((ψ.contMDiffOn_extend hψ_max).comp
          (contMDiff_baseProj_iteratedFiberProduct k hn hπ le_rfl).contMDiffOn
          (s := Ω) fun _ hy ↦ hy.1)
          |>.prodMk_space <| contMDiffOn_pi_module_iff.2 fun i ↦
            (((ContinuousLinearMap.snd ℝ EM F).comp
              (L i).toContinuousLinearMap).contDiff.contMDiff).comp_contMDiffOn <|
              ((φ i).contMDiffOn_extend (hφ_max i)).comp
                (contMDiff_proj_iteratedFiberProduct k hn hπ le_rfl i).contMDiffOn
                (s := Ω) fun _ hy ↦ (hy.2.2 i).1
      contMDiffOn_invFun := (contMDiffOn_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ by
        let Q : (EM × (Fin k → F)) →L[ℝ] EY := (L i).symm.toContinuousLinearMap.comp <|
          (ContinuousLinearMap.fst ℝ EM (Fin k → F)).prod
            ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ EM (Fin k → F)))
        have htgt : ((φ i).extend IY).target = IY '' (φ i).target :=
          (φ i).extend_target.trans (IY.image_eq (φ i).target).symm
        exact ((htgt.symm ▸ contMDiffOn_extend_symm (hφ_max i)).comp
          Q.contDiff.contMDiff.contMDiffOn fun _ hp ↦ hp_mem_tgt hp i).congr
          fun _ hp ↦ hinv_proj hp i }
  exact ⟨U, V, Φ, hU_open, hV_open, ⟨mem_chart_source HM x₀, hu₀_U, fun i ↦ ⟨hy₀_src i, hv₀_V i⟩⟩,
    rfl, fun _ hy ↦ ⟨hy.1, rfl⟩, fun _ hp ↦ hinv_base hp⟩

end Manifold

end TauCeti
