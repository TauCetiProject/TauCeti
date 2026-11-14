/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.LieRinehartAlgebra.ChevalleyEilenberg
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

Let `A : LieAlgebroid I F V` be a Lie algebroid on a finite-rank smooth real vector bundle `V → M`
over a finite-dimensional Hausdorff smooth manifold `M`. A smooth degree-`k` cochain on `A` is a
smooth section of the bundle `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` of continuous alternating forms on the
fibres of `V`.

By tensoriality (`ContMDiffSection.evalAlternatingEquiv`), smooth degree-`k` bundle sections
identify `C^∞(M)`-linearly with `C^∞(M)`-multilinear alternating maps on `A.Sections`
(`TauCeti.LieAlgebroid.cochainEquiv`). Transporting the Lie–Rinehart operators of
`TauCeti.Algebra.LieRinehartAlgebra.ChevalleyEilenberg` across this equivalence equips the smooth
bundle sections with:

* the Lie derivative `TauCeti.LieAlgebroid.lieDeriv` along smooth sections of `V`;
* the algebroid exterior derivative `TauCeti.LieAlgebroid.extDeriv` of degree `+1`, satisfying the
  explicit Chevalley–Eilenberg formula (`TauCeti.LieAlgebroid.evalAlternating_extDeriv_succ`) and
  `d_A ∘ d_A = 0` (`TauCeti.LieAlgebroid.extDeriv_extDeriv`);
* the Chevalley–Eilenberg cochain complex `TauCeti.LieAlgebroid.cochainComplex` in `ModuleCat ℝ`
  (isomorphic to the Lie–Rinehart cochain complex via `TauCeti.LieAlgebroid.cochainComplexIso`) and
  its cohomology `TauCeti.LieAlgebroid.cohomology`;
* the Cartan calculus identities relating `ContMDiffSection.interiorProd`, `lieDeriv`, and
  `extDeriv`, together with the graded derivation laws of `lieDeriv` and `extDeriv` across the
  fibrewise wedge product `ContMDiffSection.wedge` (`TauCeti.LieAlgebroid.lieDeriv_wedge`,
  `TauCeti.LieAlgebroid.extDeriv_wedge`);
* the comparison theorem `TauCeti.LieAlgebroid.tangent_extDeriv_toContMDiffSection` showing that
  specialising `A` to `TauCeti.LieAlgebroid.tangent` recovers the manifold exterior derivative
  `TauCeti.mextDerivₗ` on `SmoothForm I M ℝ k`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3 and §7.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107.
-/

public section

noncomputable section

open Bundle Function Manifold VectorField
open scoped ContDiff

namespace TauCeti.LieAlgebroid

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (A : LieAlgebroid I F V)

omit [FiniteDimensional ℝ F] in
/-- Lift a fibre vector `u : V x` to a global smooth section of `V` taking value `u` at `x`. -/
private theorem exists_section_apply_eq (x : M) (u : V x) :
    ∃ a : Cₛ^∞⟮I; F, V⟯, a x = u := by
  obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ u
  exact ⟨⟨s, hs⟩, hsx⟩

/-! ### Identification of bundle cochains with Lie–Rinehart cochains -/

/-- Smooth sections of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` identify `C^∞(M)`-linearly with
`C^∞(M)`-multilinear alternating cochains on `A.Sections`. -/
def cochainEquiv (k : ℕ) :
    Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (ContMDiffSection.evalAlternatingEquiv I F V k).trans
    (AlternatingMap.domLCongr C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (Fin k) C^∞⟮I, M; ℝ⟯
      A.sectionsEquiv.symm)

@[simp]
theorem cochainEquiv_apply (k : ℕ)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (s : Fin k → A.Sections) :
    A.cochainEquiv k φ s = φ.evalAlternating (A.sectionsEquiv ∘ s) := by
  simp [cochainEquiv, Function.comp_def]

@[simp]
theorem evalAlternating_cochainEquiv_symm (k : ℕ)
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    ((A.cochainEquiv k).symm Φ).evalAlternating s = Φ (A.sectionsEquiv.symm ∘ s) := by
  simp [cochainEquiv, Function.comp_def]

/-- `cochainEquiv` intertwines `ContMDiffSection.interiorProd` with `AlternatingMap.curryLeft`. -/
@[simp]
theorem curryLeft_cochainEquiv {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (s : A.Sections) :
    (A.cochainEquiv (k + 1) φ).curryLeft s =
      A.cochainEquiv k (φ.interiorProd (A.sectionsEquiv s)) := by
  simp [cochainEquiv, AlternatingMap.curryLeft_compLinearMap]

/-- Contracting `A.cochainEquiv (k + 1) φ` with `A.sectionsEquiv.symm a` corresponds to
`ContMDiffSection.interiorProd`. -/
theorem curryLeft_cochainEquiv_symm {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^∞⟮I; F, V⟯) :
    (A.cochainEquiv (k + 1) φ).curryLeft (A.sectionsEquiv.symm a) =
      A.cochainEquiv k (φ.interiorProd a) := by
  rw [A.curryLeft_cochainEquiv, A.sectionsEquiv.apply_symm_apply]

@[simp]
theorem cochainEquiv_zero_constOfIsEmptyEquiv (f : C^∞⟮I, M; ℝ⟯) :
    A.cochainEquiv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f) =
      AlternatingMap.constOfIsEmpty C^∞⟮I, M; ℝ⟯ A.Sections (Fin 0) f := by
  ext s
  simp [cochainEquiv_apply]

/-! ### Lie derivative on bundle cochains -/

/-- The Lie derivative `L_a` on smooth degree-`k` cochains of a Lie algebroid `A` along a smooth
section `a`, transported from `TauCeti.LieRinehartAlgebra.lieDeriv` via `A.cochainEquiv`. -/
def lieDeriv (k : ℕ) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[ℝ]
        Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ :=
  let eC := (A.cochainEquiv k).restrictScalars ℝ
  ((eC.symm.arrowCongr eC.symm).toLinearMap.comp
    (LieRinehartAlgebra.lieDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections)).comp
      (A.sectionsEquiv.symm.restrictScalars ℝ).toLinearMap

@[simp]
theorem cochainEquiv_lieDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    A.cochainEquiv k (A.lieDeriv k a φ) =
      LieRinehartAlgebra.lieDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections
        (A.sectionsEquiv.symm a) (A.cochainEquiv k φ) := by
  simp [lieDeriv]

/-- Evaluating `A.lieDeriv k a φ` on smooth sections differentiates along the anchor and subtracts
the algebroid brackets in each slot. -/
theorem evalAlternating_lieDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    (A.lieDeriv k a φ).evalAlternating s =
      A.anchorDeriv a (φ.evalAlternating s) -
        ∑ i : Fin k, φ.evalAlternating (update s i (A.bracket a (s i))) := by
  let s' : Fin k → A.Sections := A.sectionsEquiv.symm ∘ s
  have hs' : A.sectionsEquiv ∘ s' = s :=
    funext fun i ↦ A.sectionsEquiv.apply_symm_apply (s i)
  have hupd (i : Fin k) :
      A.sectionsEquiv ∘ update s' i ⁅A.sectionsEquiv.symm a, s' i⁆ =
        update s i (A.bracket a (s i)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [s', sectionsEquiv_lie]
    · simp [s', hj]
  have h := congr($(A.cochainEquiv_lieDeriv k a φ) s')
  rw [cochainEquiv_apply, hs', LieRinehartAlgebra.lieDeriv_apply] at h
  simpa only [cochainEquiv_apply, hs', Sections.lie_def, A.sectionsEquiv.apply_symm_apply,
    hupd] using h

/-! ### The algebroid exterior derivative -/

/-- The Chevalley–Eilenberg exterior derivative `d_A` of a Lie algebroid `A` in degree `k`,
transported from `TauCeti.LieRinehartAlgebra.d` across `A.cochainEquiv`. -/
def extDeriv (k : ℕ) :
    Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯ :=
  ((A.cochainEquiv (k + 1)).symm.restrictScalars ℝ).toLinearMap ∘ₗ
    LieRinehartAlgebra.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k ∘ₗ
      ((A.cochainEquiv k).restrictScalars ℝ).toLinearMap

@[simp]
theorem cochainEquiv_extDeriv (k : ℕ)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    A.cochainEquiv (k + 1) (A.extDeriv k φ) =
      LieRinehartAlgebra.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k (A.cochainEquiv k φ) := by
  simp [extDeriv]

/-- In degree zero, `d_A φ` evaluated on a section `s 0` differentiates `φ` along the anchor of
`s 0`. -/
@[simp]
theorem evalAlternating_extDeriv_zero
    (φ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (s : Fin 1 → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 φ).evalAlternating s = A.anchorDeriv (s 0) (φ.evalAlternating ![]) := by
  let s' : Fin 1 → A.Sections := A.sectionsEquiv.symm ∘ s
  have hs' : A.sectionsEquiv ∘ s' = s :=
    funext fun i ↦ A.sectionsEquiv.apply_symm_apply (s i)
  have h0 : (A.sectionsEquiv ∘ (![] : Fin 0 → A.Sections)) = ![] := Subsingleton.elim _ _
  have h := congr($(A.cochainEquiv_extDeriv 0 φ) s')
  rw [cochainEquiv_apply, hs', LieRinehartAlgebra.d_zero_apply] at h
  simpa only [cochainEquiv_apply, Sections.lie_def, h0, s', Function.comp_apply,
    A.sectionsEquiv.apply_symm_apply] using h

/-- Evaluating `d_A` of the degree-zero section attached to `f` on `a` gives `A.anchorDeriv a f`. -/
theorem evalAlternating_extDeriv_zero_constOfIsEmptyEquiv
    (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f)).evalAlternating ![a] =
      A.anchorDeriv a f := by
  simp

/-- Pointwise formula for the degree-zero algebroid exterior derivative:
`(d_A φ)_x (v) = mvfderiv I (y ↦ φ_y(0)) x (ρ_x(v_0))`. -/
@[simp]
theorem extDeriv_zero_apply
    (φ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin 1 → V x) :
    A.extDeriv 0 φ x v = mvfderiv I (fun y ↦ φ y 0) x (A.anchor x (v 0)) := by
  -- Lift `v 0` to a global smooth section `a` taking the value `v 0` at `x`.
  obtain ⟨a, ha⟩ := exists_section_apply_eq (I := I) (F := F) (V := V) x (v 0)
  have hv : v = fun i ↦ (![a] : Fin 1 → Cₛ^∞⟮I; F, V⟯) i x := by
    funext i
    obtain rfl : i = 0 := Fin.eq_zero i
    exact ha.symm
  have hφ0 : ⇑(φ.evalAlternating ![]) = fun y ↦ φ y 0 := by
    ext y
    rw [ContMDiffSection.evalAlternating_apply]
    exact congrArg (φ y) (Subsingleton.elim _ _)
  conv_lhs => rw [hv]
  rw [← ContMDiffSection.evalAlternating_apply, A.evalAlternating_extDeriv_zero,
    anchorDeriv_apply, hφ0, Matrix.cons_val_zero, ha]

/-- The degree-`1` Chevalley–Eilenberg formula for a Lie algebroid:
`(d_A φ)(a, b) = ρ(a)(φ(b)) - ρ(b)(φ(a)) - φ([a, b])`. -/
theorem evalAlternating_extDeriv_one
    (φ : Cₛ^∞⟮I; F [⋀^Fin 1]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 1]→L[ℝ] ℝ⟯)
    (a b : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 1 φ).evalAlternating ![a, b] =
      A.anchorDeriv a (φ.evalAlternating ![b]) -
        A.anchorDeriv b (φ.evalAlternating ![a]) -
        φ.evalAlternating ![A.bracket a b] := by
  have hpair (u v : Cₛ^∞⟮I; F, V⟯) :
      A.sectionsEquiv ∘ ![A.sectionsEquiv.symm u, A.sectionsEquiv.symm v] = ![u, v] := by
    funext i
    fin_cases i <;> simp
  have hsingle (u : Cₛ^∞⟮I; F, V⟯) :
      A.sectionsEquiv ∘ ![A.sectionsEquiv.symm u] = ![u] := by
    funext i
    fin_cases i
    simp
  have hlie :
      A.sectionsEquiv ∘ ![⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆] =
        ![A.bracket a b] := by
    funext i
    fin_cases i
    simp [sectionsEquiv_lie]
  have h := congr($(A.cochainEquiv_extDeriv 1 φ) ![A.sectionsEquiv.symm a, A.sectionsEquiv.symm b])
  rw [cochainEquiv_apply, hpair, LieRinehartAlgebra.d_one_apply] at h
  simpa only [cochainEquiv_apply, Sections.lie_def, A.sectionsEquiv.apply_symm_apply, hsingle,
    hlie] using h

/-- **The Chevalley–Eilenberg formula** for a Lie algebroid in arbitrary positive degree:
`(d_A φ)(s₀, …, sₖ₊₁) = ∑ i, (-1)^i ρ(sᵢ)(φ(…, ŝᵢ, …))`
`  + ∑_{i ≤ j} (-1)^(i + j + 1) φ([s_{i.castSucc}, s_{j.succ}], …)`. -/
theorem evalAlternating_extDeriv_succ {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (s : Fin (k + 2) → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv (k + 1) φ).evalAlternating s =
      ∑ i : Fin (k + 2),
          (-1 : ℤ) ^ (i : ℕ) • A.anchorDeriv (s i) (φ.evalAlternating (i.removeNth s)) +
        ∑ i : Fin (k + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          φ.evalAlternating
            (Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ))
              (j.removeNth (i.castSucc.removeNth s))) := by
  let s' : Fin (k + 2) → A.Sections := A.sectionsEquiv.symm ∘ s
  have hs' : A.sectionsEquiv ∘ s' = s :=
    funext fun r ↦ A.sectionsEquiv.apply_symm_apply (s r)
  have hrem (i : Fin (k + 2)) : A.sectionsEquiv ∘ i.removeNth s' = i.removeNth s := by
    funext r
    simp [s', Fin.removeNth]
  have hcons (i j : Fin (k + 1)) :
      A.sectionsEquiv ∘
          Matrix.vecCons ⁅s' i.castSucc, s' j.succ⁆ (j.removeNth (i.castSucc.removeNth s')) =
        Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ))
          (j.removeNth (i.castSucc.removeNth s)) := by
    funext r
    refine Fin.cases ?_ (fun t ↦ ?_) r
    · simp [s', sectionsEquiv_lie]
    · simp [s', Fin.removeNth]
  have h := congr($(A.cochainEquiv_extDeriv (k + 1) φ) s')
  rw [cochainEquiv_apply, hs', LieRinehartAlgebra.d_succ_apply] at h
  simp only [cochainEquiv_apply, Sections.lie_def, hrem, hcons] at h
  simpa only [s', Function.comp_apply, A.sectionsEquiv.apply_symm_apply] using h

/-- The exterior derivative of a Lie algebroid squares to zero. -/
@[simp]
theorem extDeriv_extDeriv (k : ℕ)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    A.extDeriv (k + 1) (A.extDeriv k φ) = 0 :=
  (A.cochainEquiv (k + 2)).injective (by simp)

/-- The exterior derivative of a Lie algebroid squares to zero as a composite of `ℝ`-linear maps. -/
theorem extDeriv_comp_extDeriv (k : ℕ) :
    A.extDeriv (k + 1) ∘ₗ A.extDeriv k = 0 :=
  LinearMap.ext (A.extDeriv_extDeriv k)

/-! ### The Chevalley–Eilenberg cochain complex and cohomology -/

/-- The Chevalley–Eilenberg cochain complex `(Ω^•(A), d_A)` of a Lie algebroid `A` in
`ModuleCat ℝ`, with degree-`k` cochains the smooth sections of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`. -/
@[expose] def cochainComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of
    (fun k ↦ ModuleCat.of ℝ
      Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (fun k ↦ ModuleCat.ofHom (A.extDeriv k))
    fun k ↦ by rw [← ModuleCat.ofHom_comp, A.extDeriv_comp_extDeriv, ModuleCat.ofHom_zero]

@[simp]
theorem cochainComplex_X (k : ℕ) :
    A.cochainComplex.X k =
      ModuleCat.of ℝ Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ :=
  (rfl)

@[simp]
theorem cochainComplex_d_succ (k : ℕ) :
    A.cochainComplex.d k (k + 1) = ModuleCat.ofHom (A.extDeriv k) := by
  simp [cochainComplex]

/-- The degreewise tensoriality equivalence `A.cochainEquiv` induces an isomorphism in
`CochainComplex (ModuleCat ℝ) ℕ` between the intrinsic bundle cochain complex of `A` and the
Lie–Rinehart Chevalley–Eilenberg cochain complex of `(C^∞(M), A.Sections)`. -/
def cochainComplexIso :
    A.cochainComplex ≅
      LieRinehartAlgebra.cochainComplex ℝ C^∞⟮I, M; ℝ⟯ A.Sections :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ ((A.cochainEquiv k).restrictScalars ℝ).toModuleIso)
    (by
      rintro k _ rfl
      dsimp [cochainComplex, LieRinehartAlgebra.cochainComplex]
      rw [CochainComplex.of_d, CochainComplex.of_d, LinearEquiv.toModuleIso_hom,
        LinearEquiv.toModuleIso_hom, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      congr 1
      refine LinearMap.ext fun φ ↦ ?_
      simp)

@[simp]
theorem cochainComplexIso_hom_f (k : ℕ) :
    A.cochainComplexIso.hom.f k =
      ModuleCat.ofHom ((A.cochainEquiv k).restrictScalars ℝ).toLinearMap :=
  (rfl)

@[simp]
theorem cochainComplexIso_inv_f (k : ℕ) :
    A.cochainComplexIso.inv.f k =
      ModuleCat.ofHom ((A.cochainEquiv k).restrictScalars ℝ).symm.toLinearMap :=
  (rfl)

/-- The `k`-th Lie algebroid cohomology `H^k(A)` of `A`. -/
abbrev cohomology (k : ℕ) : ModuleCat ℝ :=
  A.cochainComplex.homology k

/-- The `k`-th cohomology of `A` is canonically isomorphic to the `k`-th Lie–Rinehart cohomology of
`(C^∞(M), A.Sections)`. -/
@[expose] def cohomologyIso (k : ℕ) :
    A.cohomology k ≅ LieRinehartAlgebra.cohomology ℝ C^∞⟮I, M; ℝ⟯ A.Sections k :=
  HomologicalComplex.homologyMapIso A.cochainComplexIso k

/-! ### Cartan calculus on bundle cochains -/

/-- Cartan's formula in degree zero: `ι_a (d_A φ) = L_a φ`. -/
@[simp]
theorem interiorProd_extDeriv_zero
    (φ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (a : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 φ).interiorProd a = A.lieDeriv 0 a φ :=
  (A.cochainEquiv 0).injective <| by
    rw [← A.curryLeft_cochainEquiv_symm, A.cochainEquiv_extDeriv,
      LieRinehartAlgebra.curryLeft_d_zero, A.cochainEquiv_lieDeriv]

/-- **Cartan's magic formula** `ι_a (d_A φ) = L_a φ - d_A (ι_a φ)` on Lie algebroid cochains. -/
@[simp]
theorem interiorProd_extDeriv_succ {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv (k + 1) φ).interiorProd a =
      A.lieDeriv (k + 1) a φ - A.extDeriv k (φ.interiorProd a) :=
  (A.cochainEquiv (k + 1)).injective <| by
    rw [← A.curryLeft_cochainEquiv_symm, A.cochainEquiv_extDeriv,
      LieRinehartAlgebra.curryLeft_d_succ, map_sub, A.cochainEquiv_lieDeriv,
      A.cochainEquiv_extDeriv, A.curryLeft_cochainEquiv_symm]

/-- Cartan's magic formula solved for the Lie derivative: `L_a φ = ι_a (d_A φ) + d_A (ι_a φ)`. -/
theorem lieDeriv_eq_interiorProd_extDeriv_add_extDeriv_interiorProd {k : ℕ}
    (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯) :
    A.lieDeriv (k + 1) a φ =
      (A.extDeriv (k + 1) φ).interiorProd a + A.extDeriv k (φ.interiorProd a) := by
  rw [A.interiorProd_extDeriv_succ, sub_add_cancel]

/-- Scaling the differentiating section by a smooth function `f` in degree `0` scales `L_a φ`. -/
@[simp]
theorem lieDeriv_smul_left_zero (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯) :
    A.lieDeriv 0 (f • a) φ = f • A.lieDeriv 0 a φ := by
  rw [← A.interiorProd_extDeriv_zero, ContMDiffSection.interiorProd_smul_right,
    A.interiorProd_extDeriv_zero]

/-- Scaling the differentiating section by a smooth function `f` in positive degree satisfies
`L_{f • a} φ = f • ι_a (d_A φ) + d_A (f • ι_a φ)`. -/
theorem lieDeriv_smul_left_succ {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯) :
    A.lieDeriv (k + 1) (f • a) φ =
      f • (A.extDeriv (k + 1) φ).interiorProd a + A.extDeriv k (f • φ.interiorProd a) := by
  rw [A.lieDeriv_eq_interiorProd_extDeriv_add_extDeriv_interiorProd,
    ContMDiffSection.interiorProd_smul_right, ContMDiffSection.interiorProd_smul_right]

/-- Commutation of the Lie derivative with interior product:
`ι_b (L_a φ) = L_a (ι_b φ) - ι_{[a, b]} φ`. -/
theorem interiorProd_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯) :
    (A.lieDeriv (k + 1) a φ).interiorProd b =
      A.lieDeriv k a (φ.interiorProd b) - φ.interiorProd (A.bracket a b) :=
  (A.cochainEquiv k).injective <| by
    have hbr : ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ =
        A.sectionsEquiv.symm (A.bracket a b) :=
      A.sectionsEquiv.injective (by simp [sectionsEquiv_lie])
    rw [← A.curryLeft_cochainEquiv_symm, A.cochainEquiv_lieDeriv,
      LieRinehartAlgebra.curryLeft_lieDeriv, map_sub, A.cochainEquiv_lieDeriv,
      A.curryLeft_cochainEquiv_symm, hbr, A.curryLeft_cochainEquiv_symm]

/-- The Lie derivative is a Lie algebra representation: `L_{[a, b]} = [L_a, L_b]`. -/
theorem lieDeriv_bracket (k : ℕ) (a b : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    A.lieDeriv k (A.bracket a b) φ =
      A.lieDeriv k a (A.lieDeriv k b φ) - A.lieDeriv k b (A.lieDeriv k a φ) :=
  (A.cochainEquiv k).injective <| by
    have hbr : A.sectionsEquiv.symm (A.bracket a b) =
        ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ :=
      A.sectionsEquiv.injective (by simp [sectionsEquiv_lie])
    rw [A.cochainEquiv_lieDeriv, hbr, LieRinehartAlgebra.lieDeriv_lie, map_sub,
      A.cochainEquiv_lieDeriv, A.cochainEquiv_lieDeriv, A.cochainEquiv_lieDeriv,
      A.cochainEquiv_lieDeriv]

/-- The Lie derivative commutes with the exterior derivative: `L_a (d_A φ) = d_A (L_a φ)`. -/
@[simp]
theorem lieDeriv_extDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    A.lieDeriv (k + 1) a (A.extDeriv k φ) = A.extDeriv k (A.lieDeriv k a φ) :=
  (A.cochainEquiv (k + 1)).injective <| by
    rw [A.cochainEquiv_lieDeriv, A.cochainEquiv_extDeriv, LieRinehartAlgebra.lieDeriv_d,
      A.cochainEquiv_extDeriv, A.cochainEquiv_lieDeriv]

/-! ### Graded derivations on the fibrewise wedge product -/

omit [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
/-- Reindexing the Lie-bracket slot sum along `σ : Equiv.Perm (Fin (k + l))` splits it into the
slots of `φ` and the slots of `ψ`. -/
private theorem sum_update_wedge_split {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (s : Fin (k + l) → Cₛ^∞⟮I; F, V⟯) (σ : Equiv.Perm (Fin (k + l))) :
    (∑ r : Fin (k + l),
        φ.evalAlternating (fun i ↦ update s r (A.bracket a (s r)) (σ (Fin.castAdd l i))) *
          ψ.evalAlternating (fun j ↦ update s r (A.bracket a (s r)) (σ (Fin.natAdd k j)))) =
      (∑ i : Fin k,
          φ.evalAlternating (update (fun i' ↦ s (σ (Fin.castAdd l i'))) i
            (A.bracket a (s (σ (Fin.castAdd l i))))) *
            ψ.evalAlternating (fun j ↦ s (σ (Fin.natAdd k j)))) +
        ∑ j : Fin l,
          φ.evalAlternating (fun i ↦ s (σ (Fin.castAdd l i))) *
            ψ.evalAlternating (update (fun j' ↦ s (σ (Fin.natAdd k j'))) j
              (A.bracket a (s (σ (Fin.natAdd k j))))) := by
  rw [← Equiv.sum_comp σ, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h₁ :
        (fun i' ↦ update s (σ (Fin.castAdd l i)) (A.bracket a (s (σ (Fin.castAdd l i))))
          (σ (Fin.castAdd l i'))) =
        update (fun i' ↦ s (σ (Fin.castAdd l i'))) i (A.bracket a (s (σ (Fin.castAdd l i)))) := by
      funext i'
      by_cases h : i' = i
      · subst h; simp
      · simp [h, σ.injective.ne ((Fin.castAdd_injective k l).ne h)]
    have h₂ :
        (fun j ↦ update s (σ (Fin.castAdd l i)) (A.bracket a (s (σ (Fin.castAdd l i))))
          (σ (Fin.natAdd k j))) =
        fun j ↦ s (σ (Fin.natAdd k j)) := by
      funext j
      have hne : σ (Fin.natAdd k j) ≠ σ (Fin.castAdd l i) :=
        σ.injective.ne (by intro heq; have := congrArg Fin.val heq; simp at this; omega)
      simp [hne]
    rw [h₁, h₂]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h₁ :
        (fun i ↦ update s (σ (Fin.natAdd k j)) (A.bracket a (s (σ (Fin.natAdd k j))))
          (σ (Fin.castAdd l i))) =
        fun i ↦ s (σ (Fin.castAdd l i)) := by
      funext i
      have hne : σ (Fin.castAdd l i) ≠ σ (Fin.natAdd k j) :=
        σ.injective.ne (by intro heq; have := congrArg Fin.val heq; simp at this; omega)
      simp [hne]
    have h₂ :
        (fun j' ↦ update s (σ (Fin.natAdd k j)) (A.bracket a (s (σ (Fin.natAdd k j))))
          (σ (Fin.natAdd k j'))) =
        update (fun j' ↦ s (σ (Fin.natAdd k j'))) j (A.bracket a (s (σ (Fin.natAdd k j)))) := by
      funext j'
      by_cases h : j' = j
      · subst h; simp
      · simp [h, σ.injective.ne ((Fin.natAdd_injective l k).ne h)]
    rw [h₁, h₂]

/-- The Lie derivative is an even derivation of the fibrewise wedge product:
`L_a (φ ∧ ψ) = L_a φ ∧ ψ + φ ∧ L_a ψ`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    A.lieDeriv (k + l) a (φ.wedge ψ) =
      (A.lieDeriv k a φ).wedge ψ + φ.wedge (A.lieDeriv l a ψ) := by
  refine ContMDiffSection.eq_of_evalAlternating_eq <| AlternatingMap.ext fun s ↦ ?_
  -- Expand both sides via `evalAlternating_wedge_apply` and reindex the slot sum along `σ`.
  let D : C^∞⟮I, M; ℝ⟯ →+ C^∞⟮I, M; ℝ⟯ :=
    AddMonoidHom.mk' (A.anchorDeriv a) (A.anchorDeriv_add_right a)
  have hD (f : C^∞⟮I, M; ℝ⟯) : A.anchorDeriv a f = D f := rfl
  rw [A.evalAlternating_lieDeriv, ContMDiffSection.evalAlternating_add, add_apply]
  simp only [ContMDiffSection.evalAlternating_wedge_apply]
  rw [A.anchorDeriv_const_smul_right, hD, map_sum, ← Finset.smul_sum, Finset.sum_comm]
  simp only [Units.smul_def, map_zsmul]
  simp only [← hD, ← Finset.smul_sum, A.sum_update_wedge_split a φ ψ s]
  rw [← smul_sub, ← smul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← zsmul_sub, ← zsmul_add]
  congr 1
  rw [A.evalAlternating_lieDeriv, A.evalAlternating_lieDeriv, A.anchorDeriv_mul_right,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
  ring

/-- Transporting a cochain across an equality of degrees commutes with `A.extDeriv`. -/
private theorem extDeriv_congr_deg {k₁ k₂ : ℕ} (h : k₁ = k₂)
    (φ₁ : Cₛ^∞⟮I; F [⋀^Fin k₁]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k₁]→L[ℝ] ℝ⟯)
    (φ₂ : Cₛ^∞⟮I; F [⋀^Fin k₂]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k₂]→L[ℝ] ℝ⟯)
    (hφ : ∀ y (u : Fin k₂ → V y), φ₁ y (u ∘ Fin.cast h) = φ₂ y u)
    (x : M) (w : Fin (k₂ + 1) → V x) :
    A.extDeriv k₁ φ₁ x (w ∘ Fin.cast (congrArg (· + 1) h)) = A.extDeriv k₂ φ₂ x w := by
  subst h
  obtain rfl : φ₁ = φ₂ := by ext y u; exact hφ y u
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
/-- Evaluating a section at `x` on `v : Fin (m + 1) → V x` equals contracting first with a global
section `a` satisfying `a x = v 0` and evaluating on `Fin.tail v`. -/
private theorem apply_eq_interiorProd_tail {m : ℕ}
    (θ : Cₛ^∞⟮I; F [⋀^Fin (m + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (m + 1)]→L[ℝ] ℝ⟯)
    {a : Cₛ^∞⟮I; F, V⟯} {x : M} {v : Fin (m + 1) → V x} (ha : a x = v 0) :
    θ x v = θ.interiorProd a x (Fin.tail v) := by
  rw [ContMDiffSection.interiorProd_apply]
  congr 1
  funext i
  refine Fin.cases ha.symm (fun _ ↦ rfl) i

private theorem extDeriv_wedge_zero_zero
    (φ ψ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin 1 → V x) :
    A.extDeriv 0 (φ.wedge ψ) x v =
      (A.extDeriv 0 φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add 0 0)) +
        (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv 0 ψ)) x v := by
  obtain ⟨a, ha⟩ := exists_section_apply_eq (I := I) (F := F) (V := V) x (v 0)
  have hv₀ : v ∘ Fin.cast (Nat.succ_add 0 0) = v := rfl
  rw [hv₀, pow_zero, one_smul, apply_eq_interiorProd_tail _ ha,
    apply_eq_interiorProd_tail _ ha, apply_eq_interiorProd_tail _ ha,
    A.interiorProd_extDeriv_zero, A.lieDeriv_wedge (k := 0) (l := 0),
    ContMDiffSection.interiorProd_wedge_zero_right,
    ContMDiffSection.interiorProd_wedge_zero_left, A.interiorProd_extDeriv_zero,
    A.interiorProd_extDeriv_zero, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply]

private theorem extDeriv_wedge_succ_zero {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + 1 + 1) → V x)
    (ih : ∀ (φ' : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
      (w : Fin (k + 1) → V x),
      A.extDeriv k (φ'.wedge ψ) x w =
        (A.extDeriv k φ').wedge ψ x (w ∘ Fin.cast (Nat.succ_add k 0)) +
          (-1 : ℝ) ^ k • (φ'.wedge (A.extDeriv 0 ψ)) x w) :
    A.extDeriv (k + 1) (φ.wedge ψ) x v =
      (A.extDeriv (k + 1) φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add (k + 1) 0)) +
        (-1 : ℝ) ^ (k + 1) • (φ.wedge (A.extDeriv 0 ψ)) x v := by
  obtain ⟨a, ha⟩ := exists_section_apply_eq (I := I) (F := F) (V := V) x (v 0)
  have hv₁ : v ∘ Fin.cast (Nat.succ_add (k + 1) 0) = v := rfl
  have hcast : Fin.tail v ∘ Fin.cast (show k + (0 + 1) = k + 1 + 0 from rfl) = Fin.tail v := rfl
  have hw0 : Fin.tail v ∘ Fin.cast (Nat.succ_add k 0) = Fin.tail v := rfl
  rw [hv₁, apply_eq_interiorProd_tail _ ha, apply_eq_interiorProd_tail _ ha,
    apply_eq_interiorProd_tail _ ha, A.interiorProd_extDeriv_succ,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    A.lieDeriv_wedge (k := k + 1) (l := 0), ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, ContMDiffSection.interiorProd_wedge_zero_right,
    ih (φ.interiorProd a) (Fin.tail v), hw0,
    ContMDiffSection.interiorProd_wedge_zero_right, A.interiorProd_extDeriv_succ,
    ContMDiffSection.wedge_sub_left, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, ContMDiffSection.interiorProd_wedge_succ, hcast,
    A.interiorProd_extDeriv_zero]
  simp only [smul_eq_mul]
  have h1 : (-1 : ℝ) * (-1) = 1 := by ring
  have hsign : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← mul_pow, h1, one_pow]
  have hpow : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ]; ring
  linear_combination
    φ.wedge (A.lieDeriv 0 a ψ) x (Fin.tail v) * hsign.symm +
      (φ.interiorProd a).wedge (A.extDeriv 0 ψ) x (Fin.tail v) * hpow.symm

private theorem extDeriv_wedge_zero_succ {l : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (0 + (l + 1) + 1) → V x)
    (ih : ∀ (ψ' : Cₛ^∞⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
      (w : Fin (0 + l + 1) → V x),
      A.extDeriv (0 + l) (φ.wedge ψ') x w =
        (A.extDeriv 0 φ).wedge ψ' x (w ∘ Fin.cast (Nat.succ_add 0 l)) +
          (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv l ψ')) x w) :
    A.extDeriv (0 + (l + 1)) (φ.wedge ψ) x v =
      (A.extDeriv 0 φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add 0 (l + 1))) +
        (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv (l + 1) ψ)) x v := by
  obtain ⟨a, ha⟩ := exists_section_apply_eq (I := I) (F := F) (V := V) x (v 0)
  let v₀ : Fin ((0 + 1) + (l + 1)) → V x := v ∘ Fin.cast (Nat.succ_add 0 (l + 1))
  have ha₀ : a x = v₀ 0 := ha
  have htail₁ :
      Fin.tail v₀ ∘ Fin.cast (show 0 + (l + 1) = 0 + 1 + l by omega) = Fin.tail v := by
    ext i; simp [v₀, Fin.tail]
  have htail₂ : Fin.tail v₀ = Fin.tail v ∘ Fin.cast (Nat.succ_add 0 l) := by
    ext i; simp [v₀, Fin.tail]
  have hlie : A.lieDeriv (0 + l + 1) a (φ.wedge ψ) =
      (A.lieDeriv 0 a φ).wedge ψ + φ.wedge (A.lieDeriv (l + 1) a ψ) :=
    A.lieDeriv_wedge a φ ψ
  change A.extDeriv ((0 + l) + 1) (φ.wedge ψ) x v =
    (A.extDeriv 0 φ).wedge ψ x v₀ + (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv (l + 1) ψ)) x v
  rw [apply_eq_interiorProd_tail _ ha, apply_eq_interiorProd_tail _ ha₀,
    apply_eq_interiorProd_tail _ ha, A.interiorProd_extDeriv_succ,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    hlie, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, ContMDiffSection.interiorProd_wedge_zero_left,
    ih (ψ.interiorProd a) (Fin.tail v), ContMDiffSection.interiorProd_wedge_succ,
    htail₁, htail₂, A.interiorProd_extDeriv_zero,
    ContMDiffSection.interiorProd_wedge_zero_left, A.interiorProd_extDeriv_succ,
    ContMDiffSection.wedge_sub_right, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply]
  simp only [pow_zero, smul_eq_mul]
  ring

private theorem wedge_succ_succ_ring (k : ℕ) (r₁ r₂ r₃ r₄ r₅ r₆ : ℝ) :
    r₁ + r₂ - ((r₃ + (-1 : ℝ) ^ k • r₄) + (-1 : ℝ) ^ (k + 1) • (r₅ + (-1 : ℝ) ^ (k + 1) • r₆)) =
      (r₁ - r₃ + (-1 : ℝ) ^ (k + 1 + 1) • r₅) +
        (-1 : ℝ) ^ (k + 1) • (r₄ + (-1 : ℝ) ^ (k + 1) • (r₂ - r₆)) := by
  simp only [smul_eq_mul]
  have h1 : (-1 : ℝ) * (-1) = 1 := by ring
  have hsign : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← mul_pow, h1, one_pow]
  have hp₁ : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ]; ring
  have hp₂ : (-1 : ℝ) ^ (k + 1 + 1) = -((-1 : ℝ) ^ (k + 1)) := by rw [pow_succ]; ring
  linear_combination r₂ * hsign.symm + r₄ * hp₁.symm - r₅ * hp₂

private theorem extDeriv_interiorProd_wedge_succ {k l : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^∞⟮I; F, V⟯) (x : M) (u : Fin (k + 1 + l + 1) → V x) :
    A.extDeriv (k + 1 + l) ((φ.wedge ψ).interiorProd a) x u =
      A.extDeriv (k + (l + 1)) ((φ.interiorProd a).wedge ψ) x
          (u ∘ Fin.cast (congrArg (· + 1) (Nat.add_right_comm k 1 l).symm)) +
        (-1 : ℝ) ^ (k + 1) • A.extDeriv (k + 1 + l) (φ.wedge (ψ.interiorProd a)) x u := by
  have hcast : k + (l + 1) = k + 1 + l := (Nat.add_right_comm k 1 l).symm
  let ξ := (φ.wedge ψ).interiorProd a - (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.interiorProd a)
  have hξ : (φ.wedge ψ).interiorProd a = ξ + (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.interiorProd a) :=
    (sub_add_cancel _ _).symm
  have hcongr : A.extDeriv (k + 1 + l) ξ x u =
      A.extDeriv (k + (l + 1)) ((φ.interiorProd a).wedge ψ) x
        (u ∘ Fin.cast (congrArg (· + 1) hcast)) :=
    (A.extDeriv_congr_deg hcast ((φ.interiorProd a).wedge ψ) ξ
      (fun y w ↦ eq_sub_of_add_eq (ContMDiffSection.interiorProd_wedge_succ φ ψ a y w).symm)
      x u).symm
  have hlin : A.extDeriv (k + 1 + l) ((φ.wedge ψ).interiorProd a) =
      A.extDeriv (k + 1 + l) ξ +
        (-1 : ℝ) ^ (k + 1) • A.extDeriv (k + 1 + l) (φ.wedge (ψ.interiorProd a)) := by
    rw [hξ, map_add, map_smul]
  have happ : A.extDeriv (k + 1 + l) ((φ.wedge ψ).interiorProd a) x u =
      A.extDeriv (k + 1 + l) ξ x u +
        (-1 : ℝ) ^ (k + 1) • A.extDeriv (k + 1 + l) (φ.wedge (ψ.interiorProd a)) x u :=
    congr($hlin x u)
  exact happ.trans (congrArg (· + _) hcongr)

private theorem extDeriv_succ_wedge_apply {k l : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    {a : Cₛ^∞⟮I; F, V⟯} {x : M} {v : Fin ((k + 1) + (l + 1) + 1) → V x} (ha : a x = v 0) :
    (A.extDeriv (k + 1) φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add (k + 1) (l + 1))) =
      ((A.lieDeriv (k + 1) a φ).wedge ψ x (Fin.tail v) -
          (A.extDeriv k (φ.interiorProd a)).wedge ψ x (Fin.tail v)) +
        (-1 : ℝ) ^ (k + 1 + 1) •
          (A.extDeriv (k + 1) φ).wedge (ψ.interiorProd a) x
            (Fin.tail v ∘ Fin.cast (Nat.succ_add (k + 1) l)) := by
  let v₀ : Fin ((k + 1 + 1) + (l + 1)) → V x := v ∘ Fin.cast (Nat.succ_add (k + 1) (l + 1))
  have ha₀ : a x = v₀ 0 := ha
  have ht₂ :
      Fin.tail v₀ ∘ Fin.cast (show (k + 1) + (l + 1) = k + 1 + 1 + l by omega) = Fin.tail v := by
    ext i; simp [v₀, Fin.tail]
  have ht₃ : Fin.tail v₀ = Fin.tail v ∘ Fin.cast (Nat.succ_add (k + 1) l) := by
    ext i; simp [v₀, Fin.tail]
  have h₁ :=
    apply_eq_interiorProd_tail (m := k + 1 + 1 + l) ((A.extDeriv (k + 1) φ).wedge ψ) ha₀
  have h₂ := ContMDiffSection.interiorProd_wedge_succ (A.extDeriv (k + 1) φ) ψ a x (Fin.tail v₀)
  have hsub : ((A.extDeriv (k + 1) φ).interiorProd a).wedge ψ =
      (A.lieDeriv (k + 1) a φ).wedge ψ - (A.extDeriv k (φ.interiorProd a)).wedge ψ := by
    rw [A.interiorProd_extDeriv_succ, ContMDiffSection.wedge_sub_left]
  have h₃ : ((A.extDeriv (k + 1) φ).interiorProd a).wedge ψ x (Fin.tail v) =
      (A.lieDeriv (k + 1) a φ).wedge ψ x (Fin.tail v) -
        (A.extDeriv k (φ.interiorProd a)).wedge ψ x (Fin.tail v) :=
    congr($hsub x (Fin.tail v))
  rw [ht₂, ht₃, h₃] at h₂
  exact h₁.trans h₂

private theorem wedge_extDeriv_succ_apply {k l : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    {a : Cₛ^∞⟮I; F, V⟯} {x : M} {v : Fin ((k + 1) + (l + 1) + 1) → V x} (ha : a x = v 0) :
    (φ.wedge (A.extDeriv (l + 1) ψ)) x v =
      (φ.interiorProd a).wedge (A.extDeriv (l + 1) ψ) x
          (Fin.tail v ∘ Fin.cast (congrArg (· + 1) (Nat.add_right_comm k 1 l).symm)) +
        (-1 : ℝ) ^ (k + 1) •
          (φ.wedge (A.lieDeriv (l + 1) a ψ) x (Fin.tail v) -
            φ.wedge (A.extDeriv l (ψ.interiorProd a)) x (Fin.tail v)) := by
  have h₁ :=
    apply_eq_interiorProd_tail (m := (k + 1) + (l + 1)) (φ.wedge (A.extDeriv (l + 1) ψ)) ha
  have h₂ := ContMDiffSection.interiorProd_wedge_succ φ (A.extDeriv (l + 1) ψ) a x (Fin.tail v)
  have hsub : φ.wedge ((A.extDeriv (l + 1) ψ).interiorProd a) =
      φ.wedge (A.lieDeriv (l + 1) a ψ) - φ.wedge (A.extDeriv l (ψ.interiorProd a)) := by
    rw [A.interiorProd_extDeriv_succ, ContMDiffSection.wedge_sub_right]
  have h₃ : φ.wedge ((A.extDeriv (l + 1) ψ).interiorProd a) x (Fin.tail v) =
      φ.wedge (A.lieDeriv (l + 1) a ψ) x (Fin.tail v) -
        φ.wedge (A.extDeriv l (ψ.interiorProd a)) x (Fin.tail v) :=
    congr($hsub x (Fin.tail v))
  rw [h₃] at h₂
  exact h₁.trans h₂

private theorem extDeriv_wedge_succ_succ {k l : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin ((k + 1) + (l + 1) + 1) → V x)
    (ih₁ : ∀ (φ' : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
      (w : Fin (k + (l + 1) + 1) → V x),
      A.extDeriv (k + (l + 1)) (φ'.wedge ψ) x w =
        (A.extDeriv k φ').wedge ψ x (w ∘ Fin.cast (Nat.succ_add k (l + 1))) +
          (-1 : ℝ) ^ k • (φ'.wedge (A.extDeriv (l + 1) ψ)) x w)
    (ih₂ : ∀ (ψ' : Cₛ^∞⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
      (w : Fin ((k + 1) + l + 1) → V x),
      A.extDeriv ((k + 1) + l) (φ.wedge ψ') x w =
        (A.extDeriv (k + 1) φ).wedge ψ' x (w ∘ Fin.cast (Nat.succ_add (k + 1) l)) +
          (-1 : ℝ) ^ (k + 1) • (φ.wedge (A.extDeriv l ψ')) x w) :
    A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ) x v =
      (A.extDeriv (k + 1) φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add (k + 1) (l + 1))) +
        (-1 : ℝ) ^ (k + 1) • (φ.wedge (A.extDeriv (l + 1) ψ)) x v := by
  obtain ⟨a, ha⟩ := exists_section_apply_eq (I := I) (F := F) (V := V) x (v 0)
  let w₂ : Fin (k + (l + 1) + 1) → V x :=
    Fin.tail v ∘ Fin.cast (congrArg (· + 1) (Nat.add_right_comm k 1 l).symm)
  have ht₁ : w₂ ∘ Fin.cast (Nat.succ_add k (l + 1)) = Fin.tail v := by
    ext i; simp [w₂, Fin.tail]
  have h₁ := apply_eq_interiorProd_tail (A.extDeriv (k + 1 + l + 1) (φ.wedge ψ)) ha
  have h₂ : (A.extDeriv (k + 1 + l + 1) (φ.wedge ψ)).interiorProd a =
      ((A.lieDeriv (k + 1) a φ).wedge ψ + φ.wedge (A.lieDeriv (l + 1) a ψ)) -
        A.extDeriv (k + 1 + l) ((φ.wedge ψ).interiorProd a) :=
    (A.interiorProd_extDeriv_succ (k := k + 1 + l) (φ.wedge ψ) a).trans
      (congrArg (· - _) (A.lieDeriv_wedge a φ ψ))
  have h₃ : (A.extDeriv (k + 1 + l + 1) (φ.wedge ψ)).interiorProd a x (Fin.tail v) =
      (A.lieDeriv (k + 1) a φ).wedge ψ x (Fin.tail v) +
        φ.wedge (A.lieDeriv (l + 1) a ψ) x (Fin.tail v) -
        A.extDeriv (k + 1 + l) ((φ.wedge ψ).interiorProd a) x (Fin.tail v) :=
    congr($h₂ x (Fin.tail v))
  have e₁ := ih₁ (φ.interiorProd a) w₂
  rw [ht₁] at e₁
  have e₂ := ih₂ (ψ.interiorProd a) (Fin.tail v)
  have h₄ := (A.extDeriv_interiorProd_wedge_succ φ ψ a x (Fin.tail v)).trans
    (congrArg₂ (· + ·) e₁ (congrArg ((-1 : ℝ) ^ (k + 1) • ·) e₂))
  let r₁ : ℝ := (A.lieDeriv (k + 1) a φ).wedge ψ x (Fin.tail v)
  let r₂ : ℝ := φ.wedge (A.lieDeriv (l + 1) a ψ) x (Fin.tail v)
  have hlhs := (h₁.trans h₃).trans (congrArg (r₁ + r₂ - ·) h₄)
  exact hlhs.trans ((wedge_succ_succ_ring k _ _ _ _ _ _).trans
    (congrArg₂ (· + ·) (A.extDeriv_succ_wedge_apply φ ψ ha).symm
      (congrArg ((-1 : ℝ) ^ (k + 1) • ·) (A.wedge_extDeriv_succ_apply φ ψ ha).symm)))

/-- **Graded derivation law** for the algebroid exterior derivative on the fibrewise wedge product:
`d_A (φ ∧ ψ) = d_A φ ∧ ψ + (-1)^k φ ∧ d_A ψ` up to `Fin.cast (Nat.succ_add k l)`. -/
theorem extDeriv_wedge {k l : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l + 1) → V x) :
    A.extDeriv (k + l) (φ.wedge ψ) x v =
      (A.extDeriv k φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add k l)) +
        (-1 : ℝ) ^ k • (φ.wedge (A.extDeriv l ψ)) x v := by
  -- Induct on `k + l`, reducing via Cartan's magic formula `ι_a d_A + d_A ι_a = L_a`.
  suffices ∀ n : ℕ, ∀ {k l : ℕ}, k + l = n →
      ∀ (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
        (ψ : Cₛ^∞⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
        (v : Fin (k + l + 1) → V x),
        A.extDeriv (k + l) (φ.wedge ψ) x v =
          (A.extDeriv k φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add k l)) +
            (-1 : ℝ) ^ k • (φ.wedge (A.extDeriv l ψ)) x v from
    this (k + l) rfl φ ψ v
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k l hkl φ ψ v
    subst hkl
    cases k with
    | zero =>
      cases l with
      | zero => exact A.extDeriv_wedge_zero_zero φ ψ x v
      | succ l =>
        exact A.extDeriv_wedge_zero_succ φ ψ x v fun ψ' w ↦
          ih (0 + l) (by omega) rfl φ ψ' w
    | succ k =>
      cases l with
      | zero =>
        exact A.extDeriv_wedge_succ_zero φ ψ x v fun φ' w ↦
          ih (k + 0) (by omega) rfl φ' ψ w
      | succ l =>
        exact A.extDeriv_wedge_succ_succ φ ψ x v
          (fun φ' w ↦ ih (k + (l + 1)) (by omega) rfl φ' ψ w)
          (fun ψ' w ↦ ih ((k + 1) + l) (by omega) rfl φ ψ' w)

/-- Leibniz rule for `A.extDeriv` under scalar multiplication by a smooth function `f`:
`d_A (f • φ) = f • d_A φ + d_A f ∧ φ` up to `Fin.cast (Nat.add_comm 1 k)`. -/
theorem extDeriv_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯)
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + 1) → V x) :
    A.extDeriv k (f • φ) x v =
      f x • A.extDeriv k φ x v +
        (A.extDeriv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f)).wedge φ x
          (v ∘ Fin.cast (Nat.add_comm 1 k)) := by
  let f₀ := ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f
  have hfφ : φ.wedge f₀ = f • φ := by
    simp [f₀, ContMDiffSection.wedge_apply_zero_right]
  have hdfφ : (A.extDeriv k φ).wedge f₀ = f • A.extDeriv k φ := by
    simp [f₀, ContMDiffSection.wedge_apply_zero_right]
  have h := A.extDeriv_wedge (k := k) (l := 0) φ f₀ x v
  dsimp only [Nat.add_zero] at h
  rw [hfφ, show v ∘ Fin.cast (Nat.succ_add k 0) = v from rfl, hdfφ,
    ContMDiffSection.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContMDiffSection.wedge_comm φ (A.extDeriv 0 f₀) x v, Nat.mul_one, smul_smul, ← mul_pow] at h
  have h1 : (-1 : ℝ) * (-1) = 1 := by ring
  rw [h1, one_pow, one_smul] at h
  exact h

end General

/-! ### Comparison with the de Rham exterior derivative on the tangent Lie algebroid -/

section Tangent

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- On the tangent Lie algebroid `TauCeti.LieAlgebroid.tangent I M`, the algebroid exterior
derivative `extDeriv` coincides with the manifold exterior derivative `TauCeti.mextDerivₗ` via
`SmoothForm.toContMDiffSection`. -/
theorem tangent_extDeriv_toContMDiffSection (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k (SmoothForm.toContMDiffSection φ) =
      SmoothForm.toContMDiffSection (mextDerivₗ I k φ) := by
  refine ContMDiffSection.eq_of_evalAlternating_eq <| AlternatingMap.ext fun s ↦ ?_
  ext x
  cases k with
  | zero =>
    -- In degree `0`, both sides evaluate `mvfderiv I (y ↦ φ.1 y 0) x (s 0 x)`.
    have hs : (fun i : Fin 1 ↦ s i x) = ![s 0 x] := by
      funext i; fin_cases i; rfl
    have hφ0 : ⇑((SmoothForm.toContMDiffSection φ).evalAlternating ![]) = fun y ↦ φ.1 y 0 := by
      ext y
      rw [ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply]
      exact congrArg (φ.1 y) (Subsingleton.elim _ _)
    rw [evalAlternating_extDeriv_zero, anchorDeriv_apply, tangent_anchor_apply, hφ0,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply, hs,
      mextDerivₗ_zero_apply]
  | succ n =>
    -- In degree `n + 1`, compare the Chevalley–Eilenberg sum with `mextDeriv_apply_vectorField`.
    have hV (i : Fin (n + 2)) :
        MDifferentiableAt I I.tangent (fun y ↦ (s i y : TangentBundle I M)) x :=
      (s i).contMDiff.mdifferentiableAt (by simp)
    have heval (i : Fin (n + 2)) :
        ⇑((SmoothForm.toContMDiffSection φ).evalAlternating (i.removeNth s)) =
          fun y ↦ φ.1 y (i.removeNth (fun r ↦ s r y)) := by
      ext y
      rw [ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply]
      congr 1
    have hcons (i j : Fin (n + 1)) :
        (fun r ↦
          Matrix.vecCons ((tangent I M).bracket (s i.castSucc) (s j.succ))
            (j.removeNth (i.castSucc.removeNth s)) r x) =
          Matrix.vecCons (mlieBracket I (s i.castSucc) (s j.succ) x)
            (j.removeNth (i.castSucc.removeNth (fun r ↦ s r x))) := by
      funext r
      refine Fin.cases ?_ (fun t ↦ ?_) r
      · simp
      · simp [Fin.removeNth]
    rw [← ContMDiffMap.evalAlgHom_apply ℝ x, evalAlternating_extDeriv_succ,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply,
      mextDerivₗ_apply, SmoothForm.mextDeriv_apply_vectorField hV]
    simp only [map_add, map_sum, map_zsmul, ContMDiffMap.evalAlgHom_apply]
    simp only [anchorDeriv_apply, tangent_anchor_apply, heval,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply, hcons,
      zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, pow_succ (-1 : ℝ), mul_neg_one,
      neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]

end Tangent

end TauCeti.LieAlgebroid
