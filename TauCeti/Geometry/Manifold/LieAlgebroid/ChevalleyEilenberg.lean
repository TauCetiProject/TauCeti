/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Lie.Cohomology.LieRinehart
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Wedge

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

For a Lie algebroid `A` on a smooth real vector bundle `V → M`, a `k`-cochain (`A.Cochain k`) is a
smooth section of the bundle `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` of fibrewise continuous alternating
forms on `V`, i.e., `Γ(⋀^k A*)`.

Over a finite-dimensional Hausdorff base `M` and a finite-rank smooth vector bundle `V`,
multilinear section tensoriality (`ContMDiffSection.alternatingEquiv`) identifies `A.Cochain k`
`C^∞(M)`-linearly with `A.Sections [⋀^Fin k]→ₗ[C^∞(M)] C^∞(M)`. Because `(C^∞(M), A.Sections)` is
a Lie–Rinehart algebra over `ℝ`, the Lie–Rinehart Lie derivative and Chevalley–Eilenberg
differential of `TauCeti.LieRinehartAlgebra` transport across this equivalence to smooth section
operators:
* `A.interior a : A.Cochain (k + 1) →ₗ[C^∞(M)] A.Cochain k`: fibrewise interior product `ι_a`.
* `A.lieDeriv a : A.Cochain k →ₗ[ℝ] A.Cochain k`: Lie derivative `L_a`.
* `A.extDeriv k : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1)`: the Chevalley–Eilenberg differential `d_A`.

On smooth sections `s₀, …, sₖ₊₁` of `V`, `d_A` satisfies the invariant Chevalley–Eilenberg formula
`(d_A φ)(s₀, …, sₖ₊₁) = ∑ i, (-1)^i ρ(sᵢ)(φ(…, ŝᵢ, …))`
`  + ∑_{i < j} (-1)^(i + j) φ([sᵢ, sⱼ], s₀, …, ŝᵢ, …, ŝⱼ, …, sₖ₊₁)`
(`extDeriv_zero_evalSections`, `extDeriv_succ_evalSections`), squares to zero (`extDeriv_extDeriv`),
satisfies the full Cartan calculus (`interior_extDeriv_succ`, `interior_lieDeriv`,
`lieDeriv_lieDeriv_sub`, `lieDeriv_extDeriv`), and acts as a graded derivation of
`ContMDiffSection.wedge` (`lieDeriv_wedge`, `extDeriv_wedge`).

For the tangent Lie algebroid `LieAlgebroid.tangent I M`, `(tangent I M).Cochain k` identifies
with `SmoothForm I M ℝ k` and `(tangent I M).extDeriv k` agrees with the de Rham exterior
derivative `mextDeriv` (`tangent_extDeriv_apply`, `tangentCochainEquivSmoothForm_extDeriv`).

## Main definitions

* `TauCeti.LieAlgebroid.Cochain`: smooth `k`-cochains `Γ(⋀^k A*)` of a Lie algebroid `A`.
* `TauCeti.LieAlgebroid.cochainZeroEquiv`: `A.Cochain 0 ≃ₗ[C^∞(M)] C^∞(M)`.
* `TauCeti.LieAlgebroid.interior`: the interior product `ι_a`.
* `TauCeti.LieAlgebroid.cochainSectionsEquiv`: `A.Cochain k ≃ₗ[C^∞(M)]` alternating maps on `Γ(A)`.
* `TauCeti.LieAlgebroid.lieDeriv`, `TauCeti.LieAlgebroid.extDeriv`: Lie derivative and
  Chevalley–Eilenberg differential on `A.Cochain`.
* `TauCeti.LieAlgebroid.cochainComplex`, `TauCeti.LieAlgebroid.cohomology`: the Chevalley–Eilenberg
  cochain complex in `ModuleCat ℝ` and its cohomology modules.
* `TauCeti.LieAlgebroid.tangentCochainEquivSmoothForm`: `(tangent I M).Cochain k ≃ₗ[ℝ]` smooth
  differential `k`-forms on `M`.

## Main results

* `TauCeti.LieAlgebroid.extDeriv_succ_evalSections`: the Chevalley–Eilenberg formula on sections.
* `TauCeti.LieAlgebroid.extDeriv_extDeriv`: `d_A ∘ d_A = 0`.
* `TauCeti.LieAlgebroid.interior_extDeriv_succ`: Cartan's homotopy formula
  `ι_a d_A = L_a - d_A ι_a`.
* `TauCeti.LieAlgebroid.lieDeriv_wedge`, `TauCeti.LieAlgebroid.extDeriv_wedge`: graded Leibniz rules
  for `ContMDiffSection.wedge`.
* `TauCeti.LieAlgebroid.tangent_extDeriv_apply`: `(tangent I M).extDeriv` agrees with `mextDeriv`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §7.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), §1.2.
* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222.
-/

public section

noncomputable section

open Bundle Fin Manifold VectorField
open scoped ContDiff

namespace TauCeti.LieAlgebroid

section Basic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- A smooth `k`-cochain of a Lie algebroid `A`: a smooth section of the bundle of fibrewise
continuous `k`-alternating linear forms on `V`. -/
abbrev Cochain (_A : LieAlgebroid I F V) (k : ℕ) : Type _ :=
  Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯

variable (A : LieAlgebroid I F V)

/-- Degree-zero cochains of `A` identify `C^∞(M)`-linearly with smooth functions on `M`. -/
def cochainZeroEquiv : A.Cochain 0 ≃ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ :=
  ContMDiffSection.alternatingIsEmptyEquiv I F ∞ V (Fin 0)

@[simp]
theorem cochainZeroEquiv_apply (φ : A.Cochain 0) (x : M) :
    A.cochainZeroEquiv φ x = φ x 0 :=
  ContMDiffSection.alternatingIsEmptyEquiv_apply φ x

@[simp]
theorem cochainZeroEquiv_symm_apply (f : C^∞⟮I, M; ℝ⟯) (x : M) (v : Fin 0 → V x) :
    A.cochainZeroEquiv.symm f x v = f x :=
  ContMDiffSection.alternatingIsEmptyEquiv_symm_apply f x v

/-- Evaluate a `k`-cochain `φ` of `A` on `k` smooth sections of `V`, producing a smooth function on
`M`. -/
def evalSections {k : ℕ} (φ : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) : C^∞⟮I, M; ℝ⟯ :=
  φ.evalSection s

@[simp]
theorem evalSections_apply {k : ℕ} (φ : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    A.evalSections φ s x = φ x (s · x) :=
  ContMDiffSection.evalSection_apply φ s x

@[simp]
theorem evalSections_zero_cochain {k : ℕ} (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (0 : A.Cochain k) s = 0 := by
  ext x
  simp

@[simp]
theorem evalSections_add {k : ℕ} (φ₁ φ₂ : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (φ₁ + φ₂) s = A.evalSections φ₁ s + A.evalSections φ₂ s := by
  ext x
  simp

@[simp]
theorem evalSections_sub {k : ℕ} (φ₁ φ₂ : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (φ₁ - φ₂) s = A.evalSections φ₁ s - A.evalSections φ₂ s := by
  ext x
  simp

@[simp]
theorem evalSections_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (φ : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (f • φ) s = f * A.evalSections φ s := by
  ext x
  simp

@[simp]
theorem evalSections_const_smul {k : ℕ} (c : ℝ) (φ : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (c • φ) s = c • A.evalSections φ s := by
  ext x
  simp

@[simp]
theorem evalSections_zero (φ : A.Cochain 0) (s : Fin 0 → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections φ s = A.cochainZeroEquiv φ := by
  ext x
  rw [evalSections_apply, cochainZeroEquiv_apply]
  exact congrArg (φ x) (Subsingleton.elim (s · x) 0)

/-- The interior product `ι_a : A.Cochain (k + 1) →ₗ[C^∞(M)] A.Cochain k` inserting a smooth
section `a` into the first slot. -/
def interior {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) : A.Cochain (k + 1) →ₗ[C^∞⟮I, M; ℝ⟯] A.Cochain k where
  toFun φ := φ.curryLeft a
  map_add' φ₁ φ₂ := ContMDiffSection.curryLeft_add_left φ₁ φ₂ a
  map_smul' f φ := ContMDiffSection.curryLeft_fun_smul_left f φ a

@[simp]
theorem interior_apply {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.interior a φ = φ.curryLeft a :=
  (rfl)

theorem interior_apply_apply {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1))
    (x : M) (v : Fin k → V x) :
    A.interior a φ x v = φ x (Matrix.vecCons (a x) v) :=
  ContMDiffSection.curryLeft_apply_apply φ a x v

theorem interior_zero_left {k : ℕ} (φ : A.Cochain (k + 1)) :
    A.interior 0 φ = 0 :=
  ContMDiffSection.curryLeft_zero_right φ

theorem interior_add_left {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.interior (a + b) φ = A.interior a φ + A.interior b φ :=
  ContMDiffSection.curryLeft_add_right φ a b

theorem interior_smul_left {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) :
    A.interior (f • a) φ = f • A.interior a φ :=
  ContMDiffSection.curryLeft_fun_smul_right f φ a

theorem interior_self {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 2)) :
    A.interior a (A.interior a φ) = 0 :=
  ContMDiffSection.curryLeft_same φ a

theorem interior_interior_eq_neg {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 2)) :
    A.interior b (A.interior a φ) = -A.interior a (A.interior b φ) :=
  ContMDiffSection.curryLeft_curryLeft_eq_neg φ a b

theorem evalSections_interior {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1))
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (A.interior a φ) s = A.evalSections φ (Matrix.vecCons a s) := by
  ext x
  simp only [evalSections_apply, interior_apply_apply]
  congr 1
  ext i
  cases i using Fin.cases <;> rfl

private theorem sectionsEquiv_symm_bracket (a b : Cₛ^∞⟮I; F, V⟯) :
    ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ =
      A.sectionsEquiv.symm (A.bracket a b) :=
  A.sectionsEquiv.injective (by simp)

private theorem cast_cochain_self {m : ℕ} (h : m = m) (φ : A.Cochain m) :
    LinearEquiv.cast (R := ℝ) (M := A.Cochain) h φ = φ := by
  simp

/-- Splitting the sum of Lie-bracket slot updates of a wedge term along `Fin (k + l)` into updates
of the first `k` slots and updates of the last `l` slots. -/
private theorem sum_update_evalSection_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain k) (ψ : A.Cochain l) (s : Fin (k + l) → Cₛ^∞⟮I; F, V⟯)
    (σ : Equiv.Perm (Fin (k + l))) :
    ∑ m : Fin (k + l),
        (φ.evalSection (fun i ↦ Function.update s m (A.bracket a (s m)) (σ (Fin.castAdd l i))) *
          ψ.evalSection (fun j ↦ Function.update s m (A.bracket a (s m)) (σ (Fin.natAdd k j)))) =
      (∑ i : Fin k,
          φ.evalSection (Function.update (fun i' ↦ s (σ (Fin.castAdd l i'))) i
            (A.bracket a (s (σ (Fin.castAdd l i))))) *
          ψ.evalSection (fun j ↦ s (σ (Fin.natAdd k j)))) +
        (∑ j : Fin l,
          φ.evalSection (fun i ↦ s (σ (Fin.castAdd l i))) *
          ψ.evalSection (Function.update (fun j' ↦ s (σ (Fin.natAdd k j'))) j
            (A.bracket a (s (σ (Fin.natAdd k j)))))) := by
  rw [← Equiv.sum_comp σ, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦
      congrArg₂ (· * ·) (congrArg φ.evalSection ?_) (congrArg ψ.evalSection ?_)
    · funext i'
      by_cases h : i' = i
      · subst h; simp
      · have hne : σ (Fin.castAdd l i') ≠ σ (Fin.castAdd l i) :=
          σ.injective.ne fun h' ↦ h (Fin.ext (by simpa using congrArg Fin.val h'))
        simp [h, hne]
    · funext j
      have hne : σ (Fin.natAdd k j) ≠ σ (Fin.castAdd l i) :=
        σ.injective.ne fun h ↦ by have := congrArg Fin.val h; simp at this; omega
      exact Function.update_of_ne hne _ s
  · refine Finset.sum_congr rfl fun j _ ↦
      congrArg₂ (· * ·) (congrArg φ.evalSection ?_) (congrArg ψ.evalSection ?_)
    · funext i
      have hne : σ (Fin.castAdd l i) ≠ σ (Fin.natAdd k j) :=
        σ.injective.ne fun h ↦ by have := congrArg Fin.val h; simp at this; omega
      exact Function.update_of_ne hne _ s
    · funext j'
      by_cases h : j' = j
      · subst h; simp
      · have hne : σ (Fin.natAdd k j') ≠ σ (Fin.natAdd k j) :=
          σ.injective.ne fun h' ↦ h (Fin.ext (by simpa using congrArg Fin.val h'))
        simp [h, hne]

end Basic

section Separation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

/-- Two cochains of positive degree are equal as soon as all their interior products agree. -/
theorem interior_injective (A : LieAlgebroid I F V) {k : ℕ} {φ₁ φ₂ : A.Cochain (k + 1)}
    (h : ∀ a : Cₛ^∞⟮I; F, V⟯, A.interior a φ₁ = A.interior a φ₂) :
    φ₁ = φ₂ :=
  ContMDiffSection.curryLeft_injective h

end Separation

section Complex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

section ArbitraryAlgebroid

variable (A : LieAlgebroid I F V)

/-- Transport alternating `C^∞(M)`-multilinear maps along `A.sectionsEquiv`. -/
private def sectionsAlternatingEquiv (k : ℕ) :
    (Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) where
  toFun Φ := Φ.compLinearMap A.sectionsEquiv.toLinearMap
  invFun Ψ := Ψ.compLinearMap A.sectionsEquiv.symm.toLinearMap
  left_inv Φ := by
    ext s
    simp [AlternatingMap.compLinearMap_apply]
  right_inv Ψ := by
    ext s
    simp [AlternatingMap.compLinearMap_apply]
  map_add' _ _ := by ext s; rfl
  map_smul' _ _ := by ext s; rfl

/-- Over a finite-dimensional Hausdorff manifold and a finite-rank Lie algebroid `A`, `k`-cochains
identify `C^∞(M)`-linearly with `C^∞(M)`-multilinear alternating maps on `A.Sections`. -/
def cochainSectionsEquiv (k : ℕ) :
    A.Cochain k ≃ₗ[C^∞⟮I, M; ℝ⟯] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (ContMDiffSection.alternatingEquiv I F V (Fin k)).trans (A.sectionsAlternatingEquiv k)

@[simp]
theorem cochainSectionsEquiv_apply {k : ℕ} (φ : A.Cochain k) (s : Fin k → A.Sections) :
    A.cochainSectionsEquiv k φ s = A.evalSections φ (A.sectionsEquiv ∘ s) := by
  ext x
  simp [cochainSectionsEquiv, sectionsAlternatingEquiv, AlternatingMap.compLinearMap_apply]

private theorem evalSections_eq_cochainSectionsEquiv {k : ℕ} (φ : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections φ s = A.cochainSectionsEquiv k φ (A.sectionsEquiv.symm ∘ s) := by
  rw [cochainSectionsEquiv_apply]
  congr 1
  funext i
  simp

private theorem cochain_ext_evalSections {k : ℕ} {φ₁ φ₂ : A.Cochain k}
    (h : ∀ s : Fin k → Cₛ^∞⟮I; F, V⟯, A.evalSections φ₁ s = A.evalSections φ₂ s) :
    φ₁ = φ₂ :=
  (A.cochainSectionsEquiv k).injective <| AlternatingMap.ext fun s ↦ by
    simp only [cochainSectionsEquiv_apply]
    exact h (A.sectionsEquiv ∘ s)

@[simp]
theorem cochainSectionsEquiv_curryLeft {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.cochainSectionsEquiv k (φ.curryLeft a) =
      (A.cochainSectionsEquiv (k + 1) φ).curryLeft (A.sectionsEquiv.symm a) := by
  ext s x
  simp only [cochainSectionsEquiv_apply, evalSections_apply,
    ContMDiffSection.curryLeft_apply_apply, AlternatingMap.curryLeft_apply_apply]
  congr 1
  ext i
  cases i using Fin.cases <;> simp

theorem cochainSectionsEquiv_interior {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.cochainSectionsEquiv k (A.interior a φ) =
      (A.cochainSectionsEquiv (k + 1) φ).curryLeft (A.sectionsEquiv.symm a) :=
  A.cochainSectionsEquiv_curryLeft a φ

private theorem cochainSectionsEquiv_const_smul {k : ℕ} (c : ℝ) (φ : A.Cochain k) :
    A.cochainSectionsEquiv k (c • φ) = c • A.cochainSectionsEquiv k φ := by
  ext s x
  simp

private theorem cochainSectionsEquiv_symm_const_smul {k : ℕ} (c : ℝ)
    (Ψ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    (A.cochainSectionsEquiv k).symm (c • Ψ) = c • (A.cochainSectionsEquiv k).symm Ψ :=
  (A.cochainSectionsEquiv k).injective (by simp [cochainSectionsEquiv_const_smul])

/-! ### Lie derivative and Chevalley–Eilenberg differential -/

/-- The Lie derivative `L_a : A.Cochain k →ₗ[ℝ] A.Cochain k` along a smooth section `a`,
transported from `TauCeti.LieRinehartAlgebra.lieDeriv` across `cochainSectionsEquiv`. -/
def lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) : A.Cochain k →ₗ[ℝ] A.Cochain k where
  toFun φ :=
    (A.cochainSectionsEquiv k).symm
      (LieRinehartAlgebra.lieDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections
        (A.sectionsEquiv.symm a) (A.cochainSectionsEquiv k φ))
  map_add' φ₁ φ₂ := by simp
  map_smul' c φ := by
    simp only [RingHom.id_apply, cochainSectionsEquiv_const_smul, LinearMap.map_smul,
      cochainSectionsEquiv_symm_const_smul]

@[simp]
theorem cochainSectionsEquiv_lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.cochainSectionsEquiv k (A.lieDeriv a φ) =
      LieRinehartAlgebra.lieDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections
        (A.sectionsEquiv.symm a) (A.cochainSectionsEquiv k φ) :=
  (A.cochainSectionsEquiv k).apply_symm_apply _

/-- The Chevalley–Eilenberg differential `d_A : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1)` of a Lie
algebroid `A`, transported from `TauCeti.LieRinehartAlgebra.extDeriv` across
`cochainSectionsEquiv`. -/
def extDeriv (k : ℕ) : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1) where
  toFun φ :=
    (A.cochainSectionsEquiv (k + 1)).symm
      (LieRinehartAlgebra.extDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections k (A.cochainSectionsEquiv k φ))
  map_add' φ₁ φ₂ := by simp
  map_smul' c φ := by
    simp only [RingHom.id_apply, cochainSectionsEquiv_const_smul, LinearMap.map_smul,
      cochainSectionsEquiv_symm_const_smul]

@[simp]
theorem cochainSectionsEquiv_extDeriv (k : ℕ) (φ : A.Cochain k) :
    A.cochainSectionsEquiv (k + 1) (A.extDeriv k φ) =
      LieRinehartAlgebra.extDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections k (A.cochainSectionsEquiv k φ) :=
  (A.cochainSectionsEquiv (k + 1)).apply_symm_apply _

/-! ### Explicit evaluation formulas on smooth sections -/

/-- Explicit formula for the Lie derivative on smooth sections:
`(L_a φ)(s₀, …, sₖ₋₁) = ρ(a)(φ(s₀, …, sₖ₋₁)) - ∑ i, φ(s₀, …, [a, sᵢ], …, sₖ₋₁)`. -/
theorem lieDeriv_evalSections {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (A.lieDeriv a φ) s =
      A.anchorDeriv a (A.evalSections φ s) -
        ∑ i : Fin k, A.evalSections φ (Function.update s i (A.bracket a (s i))) := by
  rw [evalSections_eq_cochainSectionsEquiv, cochainSectionsEquiv_lieDeriv,
    LieRinehartAlgebra.lieDeriv_apply, Sections.lie_def, LinearEquiv.apply_symm_apply,
    ← evalSections_eq_cochainSectionsEquiv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [evalSections_eq_cochainSectionsEquiv]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj
    simp [sectionsEquiv_symm_bracket]
  · simp [hj]

/-- In degree zero, `(d_A φ)(s₀) = ρ(s₀)(φ)`. -/
@[simp]
theorem extDeriv_zero_evalSections (φ : A.Cochain 0) (s : Fin 1 → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (A.extDeriv 0 φ) s = A.anchorDeriv (s 0) (A.cochainZeroEquiv φ) := by
  rw [evalSections_eq_cochainSectionsEquiv, cochainSectionsEquiv_extDeriv,
    LieRinehartAlgebra.extDeriv_zero_apply, Function.comp_apply, Sections.lie_def,
    LinearEquiv.apply_symm_apply, cochainSectionsEquiv_apply, evalSections_zero]

/-- **The Chevalley–Eilenberg formula** for a Lie algebroid cochain of positive degree evaluated on
smooth sections:
`(d_A φ)(s₀, …, sₖ₊₁) = ∑ i, (-1)^i ρ(sᵢ)(φ(…, ŝᵢ, …))`
`  + ∑_{i < j} (-1)^(i + j) φ([sᵢ, sⱼ], s₀, …, ŝᵢ, …, ŝⱼ, …, sₖ₊₁)`,
with pairs `i < j` parametrized as `(i.castSucc, j.succ)` for `i ≤ j`. -/
theorem extDeriv_succ_evalSections {k : ℕ} (φ : A.Cochain (k + 1))
    (s : Fin (k + 2) → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (A.extDeriv (k + 1) φ) s =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          A.anchorDeriv (s i) (A.evalSections φ (i.removeNth s)) +
        ∑ i : Fin (k + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          A.evalSections φ
            (Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ))
              (j.removeNth (i.castSucc.removeNth s))) := by
  rw [evalSections_eq_cochainSectionsEquiv, cochainSectionsEquiv_extDeriv,
    LieRinehartAlgebra.extDeriv_succ_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
    rw [Function.comp_apply, Sections.lie_def, LinearEquiv.apply_symm_apply,
      evalSections_eq_cochainSectionsEquiv]
    rfl
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      congrArg ((-1 : ℤ) ^ (i + j + 1 : ℕ) • ·) ?_
    rw [evalSections_eq_cochainSectionsEquiv]
    congr 1
    ext m
    cases m using Fin.cases with
    | zero => simp [sectionsEquiv_symm_bracket]
    | succ r => rfl

/-- On a `1`-cochain and two smooth sections `a`, `b`,
`(d_A φ)(a, b) = ρ(a)(φ(b)) - ρ(b)(φ(a)) - φ([a, b])`. -/
theorem extDeriv_one_evalSections (φ : A.Cochain 1) (a b : Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (A.extDeriv 1 φ) ![a, b] =
      A.anchorDeriv a (A.evalSections φ ![b]) -
        A.anchorDeriv b (A.evalSections φ ![a]) -
        A.evalSections φ ![A.bracket a b] := by
  rw [A.extDeriv_succ_evalSections (k := 0) φ ![a, b], Fin.sum_univ_two, Fin.sum_univ_one]
  have hIci : Finset.Ici (0 : Fin 1) = {0} := by ext j; fin_cases j; simp
  have h₀ : removeNth (0 : Fin 2) ![a, b] = ![b] := by funext i; fin_cases i; rfl
  have h₁ : removeNth (1 : Fin 2) ![a, b] = ![a] := by funext i; fin_cases i; rfl
  rw [hIci, Finset.sum_singleton]
  simp only [val_zero, val_one, castSucc_zero, succ_zero_eq_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, h₀, h₁]
  abel

/-- Scalar Leibniz rule for `d_A` evaluated on smooth sections. -/
theorem extDeriv_smul_evalSections {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (φ : A.Cochain k)
    (s : Fin (k + 1) → Cₛ^∞⟮I; F, V⟯) :
    A.evalSections (A.extDeriv k (f • φ)) s =
      f * A.evalSections (A.extDeriv k φ) s +
        ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) •
          (A.anchorDeriv (s i) f * A.evalSections φ (i.removeNth s)) := by
  rw [evalSections_eq_cochainSectionsEquiv, cochainSectionsEquiv_extDeriv,
    (A.cochainSectionsEquiv k).map_smul, LieRinehartAlgebra.extDeriv_smul_apply,
    ← cochainSectionsEquiv_extDeriv, ← evalSections_eq_cochainSectionsEquiv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
  rw [Function.comp_apply, Sections.lie_def, LinearEquiv.apply_symm_apply,
    evalSections_eq_cochainSectionsEquiv]
  rfl

/-! ### Cochain complex, cohomology, and Cartan calculus -/

/-- The Chevalley–Eilenberg differential of a Lie algebroid squares to zero. -/
@[simp]
theorem extDeriv_extDeriv (k : ℕ) (φ : A.Cochain k) :
    A.extDeriv (k + 1) (A.extDeriv k φ) = 0 :=
  (A.cochainSectionsEquiv (k + 2)).injective (by simp)

theorem extDeriv_comp_extDeriv (k : ℕ) :
    A.extDeriv (k + 1) ∘ₗ A.extDeriv k = 0 :=
  LinearMap.ext (A.extDeriv_extDeriv k)

/-- The Chevalley–Eilenberg cochain complex of `A` in `ModuleCat ℝ`, whose degree-`k` term is
`A.Cochain k` and whose differential is `A.extDeriv k`. -/
@[expose] def cochainComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (A.Cochain k))
    (fun k ↦ ModuleCat.ofHom (A.extDeriv k)) fun k ↦ by
      rw [← ModuleCat.ofHom_comp, A.extDeriv_comp_extDeriv, ModuleCat.ofHom_zero]

@[simp]
theorem cochainComplex_X (k : ℕ) :
    A.cochainComplex.X k = ModuleCat.of ℝ (A.Cochain k) :=
  (rfl)

@[simp]
theorem cochainComplex_d_succ (k : ℕ) :
    A.cochainComplex.d k (k + 1) = ModuleCat.ofHom (A.extDeriv k) := by
  simp [cochainComplex]

/-- The `k`-th Lie algebroid cohomology `H^k(A)` of `A` with trivial coefficients, the homology of
`A.cochainComplex` in degree `k`. -/
abbrev cohomology (k : ℕ) : ModuleCat ℝ :=
  A.cochainComplex.homology k

@[simp]
theorem lieDeriv_zero_left {k : ℕ} (φ : A.Cochain k) :
    A.lieDeriv 0 φ = 0 :=
  (A.cochainSectionsEquiv k).injective (by simp)

@[simp]
theorem lieDeriv_add_left {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv (a + b) φ = A.lieDeriv a φ + A.lieDeriv b φ :=
  (A.cochainSectionsEquiv k).injective (by simp)

@[simp]
theorem lieDeriv_const_smul_left {k : ℕ} (c : ℝ) (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv (c • a) φ = c • A.lieDeriv a φ :=
  (A.cochainSectionsEquiv k).injective <| by
    rw [cochainSectionsEquiv_lieDeriv,
      LinearMapClass.map_smul_of_tower A.sectionsEquiv.symm c,
      LieRinehartAlgebra.lieDeriv_smul_const_left,
      cochainSectionsEquiv_const_smul, cochainSectionsEquiv_lieDeriv]

/-- Scalar Leibniz rule for the Lie derivative: `L_a (f • φ) = f • L_a φ + (ρ(a) f) • φ`. -/
theorem lieDeriv_smul_right {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯)
    (φ : A.Cochain k) :
    A.lieDeriv a (f • φ) = f • A.lieDeriv a φ + A.anchorDeriv a f • φ :=
  (A.cochainSectionsEquiv k).injective <| by
    rw [cochainSectionsEquiv_lieDeriv, map_smul, LieRinehartAlgebra.lieDeriv_smul_right,
      Sections.lie_def, LinearEquiv.apply_symm_apply, map_add, map_smul, map_smul,
      cochainSectionsEquiv_lieDeriv]

@[simp]
theorem curryLeft_extDeriv_zero (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain 0) :
    (A.extDeriv 0 φ).curryLeft a = A.lieDeriv a φ :=
  (A.cochainSectionsEquiv 0).injective (by simp)

/-- Cartan's homotopy formula in degree zero: `ι_a (d_A φ) = L_a φ`. -/
theorem interior_extDeriv_zero (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain 0) :
    A.interior a (A.extDeriv 0 φ) = A.lieDeriv a φ :=
  A.curryLeft_extDeriv_zero a φ

/-- **Cartan's homotopy formula** in positive degree: `ι_a (d_A φ) = L_a φ - d_A (ι_a φ)`. -/
theorem interior_extDeriv_succ {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.interior a (A.extDeriv (k + 1) φ) = A.lieDeriv a φ - A.extDeriv k (A.interior a φ) :=
  (A.cochainSectionsEquiv (k + 1)).injective (by simp)

/-- **Cartan's magic formula** `L_a φ = ι_a (d_A φ) + d_A (ι_a φ)` in positive degree. -/
theorem lieDeriv_succ_eq_interior_extDeriv_add {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) :
    A.lieDeriv a φ = A.interior a (A.extDeriv (k + 1) φ) + A.extDeriv k (A.interior a φ) := by
  rw [A.interior_extDeriv_succ]
  abel

/-- Cartan's commutator identity `ι_b (L_a φ) = L_a (ι_b φ) - ι_{[a, b]} φ`. -/
theorem interior_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.interior b (A.lieDeriv a φ) =
      A.lieDeriv a (A.interior b φ) - A.interior (A.bracket a b) φ :=
  (A.cochainSectionsEquiv k).injective <| by
    simp [LieRinehartAlgebra.curryLeft_lieDeriv, sectionsEquiv_symm_bracket]

/-- Cartan's commutator identity `[L_a, ι_b] = ι_{[a, b]}`. -/
theorem lieDeriv_interior_sub {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.lieDeriv a (A.interior b φ) - A.interior b (A.lieDeriv a φ) =
      A.interior (A.bracket a b) φ := by
  rw [A.interior_lieDeriv]
  abel

/-- The Lie derivative is a representation of smooth sections: `[L_a, L_b] = L_{[a, b]}`. -/
theorem lieDeriv_lieDeriv_sub {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv a (A.lieDeriv b φ) - A.lieDeriv b (A.lieDeriv a φ) =
      A.lieDeriv (A.bracket a b) φ :=
  (A.cochainSectionsEquiv k).injective <| by
    rw [map_sub, cochainSectionsEquiv_lieDeriv, cochainSectionsEquiv_lieDeriv,
      cochainSectionsEquiv_lieDeriv, cochainSectionsEquiv_lieDeriv,
      LieRinehartAlgebra.lieDeriv_lieDeriv_sub, sectionsEquiv_symm_bracket,
      cochainSectionsEquiv_lieDeriv]

/-- Naturality of the Chevalley–Eilenberg differential: `L_a (d_A φ) = d_A (L_a φ)`. -/
@[simp]
theorem lieDeriv_extDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv a (A.extDeriv k φ) = A.extDeriv k (A.lieDeriv a φ) :=
  (A.cochainSectionsEquiv (k + 1)).injective (by simp)

/-! ### Graded derivation laws for the wedge product -/

private def anchorDerivLM (a : Cₛ^∞⟮I; F, V⟯) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun := A.anchorDeriv a
  map_add' := A.anchorDeriv_add_right a
  map_smul' := A.anchorDeriv_const_smul_right a

/-- The Lie derivative is an even derivation of `ContMDiffSection.wedge`:
`L_a (φ ∧ ψ) = L_a φ ∧ ψ + φ ∧ L_a ψ`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.lieDeriv a (φ.wedge ψ) = (A.lieDeriv a φ).wedge ψ + φ.wedge (A.lieDeriv a ψ) := by
  refine A.cochain_ext_evalSections fun s ↦ ?_
  rw [A.lieDeriv_evalSections, A.evalSections_add]
  simp only [evalSections, ContMDiffSection.evalSection_wedge]
  change A.anchorDerivLM a _ - _ = _
  rw [map_smul, map_sum, ← Finset.smul_sum, Finset.sum_comm]
  simp_rw [Units.smul_def, map_zsmul, ← Finset.smul_sum, A.sum_update_evalSection_wedge]
  rw [← smul_sub, ← smul_add]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← zsmul_sub, ← zsmul_add]
  congr 1
  change A.anchorDeriv a _ - _ =
    A.evalSections (A.lieDeriv a φ) _ * _ + _ * A.evalSections (A.lieDeriv a ψ) _
  rw [A.anchorDeriv_mul_right, A.lieDeriv_evalSections, A.lieDeriv_evalSections]
  simp only [evalSections, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
  ring

/-- Base case `l = 0` of `extDeriv_wedge`: no degree cast is needed since `k + 0 = k` is
definitional. -/
private theorem extDeriv_wedge_zero_right {k : ℕ} (φ : A.Cochain k) (ψ : A.Cochain 0) :
    A.extDeriv k (φ.wedge ψ) =
      (A.extDeriv k φ).wedge ψ + (-1 : ℝ) ^ k • φ.wedge (A.extDeriv 0 ψ) := by
  induction k with
  | zero =>
    refine A.interior_injective fun a ↦ ?_
    rw [pow_zero, one_smul, map_add, interior_apply, curryLeft_extDeriv_zero,
      A.lieDeriv_wedge a φ ψ, interior_apply, interior_apply,
      ContMDiffSection.curryLeft_wedge_zero_right (A.extDeriv 0 φ) ψ a,
      ContMDiffSection.curryLeft_wedge_zero_left φ (A.extDeriv 0 ψ) a,
      curryLeft_extDeriv_zero, curryLeft_extDeriv_zero]
  | succ k ih =>
    refine A.interior_injective fun a ↦ ?_
    ext x w
    have hpow : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    have hL : A.interior a (A.extDeriv (k + 1) (φ.wedge ψ)) =
        (A.lieDeriv a φ).wedge ψ + φ.wedge (A.lieDeriv a ψ) -
          ((A.extDeriv k (φ.curryLeft a)).wedge ψ +
            (-1 : ℝ) ^ k • (φ.curryLeft a).wedge (A.extDeriv 0 ψ)) := by
      rw [A.interior_extDeriv_succ (k := k) a (φ.wedge ψ), A.lieDeriv_wedge a φ ψ, interior_apply,
        ContMDiffSection.curryLeft_wedge_zero_right φ ψ a, ih]
    rw [hL, interior_apply, ContMDiffSection.curryLeft_add_left,
      ContMDiffSection.curryLeft_smul_left]
    simp only [ContMDiffSection.curryLeft_wedge_zero_right,
      ← A.interior_apply a (A.extDeriv (k + 1) φ), A.interior_extDeriv_succ, interior_apply,
      ContMDiffSection.wedge_sub_left, ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
      ContMDiffSection.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.smul_apply,
      ContMDiffSection.curryLeft_wedge_apply φ (A.extDeriv 0 ψ) a x w,
      curryLeft_extDeriv_zero, smul_eq_mul]
    have hw : w ∘ Fin.cast (by omega : k + (0 + 1) = k + 1 + 0) = w := rfl
    rw [hw]
    simp only [mul_add, ← mul_assoc, hpow, one_mul]
    rw [pow_succ]
    ring

/-- Base case `k = 0` of `extDeriv_wedge`. -/
private theorem extDeriv_wedge_zero_left {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l) :
    A.extDeriv (0 + l) (φ.wedge ψ) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain)
        (show 0 + 1 + l = 0 + l + 1 by omega) ((A.extDeriv 0 φ).wedge ψ) +
      φ.wedge (A.extDeriv l ψ) := by
  induction l with
  | zero =>
    rw [A.cast_cochain_self]
    simpa using A.extDeriv_wedge_zero_right φ ψ
  | succ l ih =>
    refine A.interior_injective fun a ↦ ?_
    ext x w
    have hL : A.interior a (A.extDeriv (0 + (l + 1)) (φ.wedge ψ)) =
        (A.lieDeriv a φ).wedge ψ + φ.wedge (A.lieDeriv a ψ) -
          (LinearEquiv.cast (R := ℝ) (M := A.Cochain) (show 0 + 1 + l = 0 + (l + 1) by omega)
            ((A.extDeriv 0 φ).wedge (ψ.curryLeft a)) +
            φ.wedge (A.extDeriv l (ψ.curryLeft a))) := by
      have h1 : A.interior a (A.extDeriv (0 + (l + 1)) (φ.wedge ψ)) =
          A.lieDeriv (k := 0 + (l + 1)) a (φ.wedge ψ) -
            A.extDeriv (0 + l) (A.interior (k := 0 + l) a (φ.wedge ψ)) :=
        A.interior_extDeriv_succ (k := 0 + l) a (φ.wedge ψ)
      have h2 : A.interior (k := 0 + l) a (φ.wedge ψ) = φ.wedge (ψ.curryLeft a) :=
        ContMDiffSection.curryLeft_wedge_zero_left φ ψ a
      rw [h1, A.lieDeriv_wedge a φ ψ, h2, ih]
    rw [hL, interior_apply, ContMDiffSection.curryLeft_add_left]
    simp only [ContMDiffSection.curryLeft_cast_alternating,
      ContMDiffSection.curryLeft_wedge_zero_left, ← A.interior_apply a (A.extDeriv (l + 1) ψ),
      A.interior_extDeriv_succ, interior_apply, ContMDiffSection.wedge_sub_right,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
      ContMDiffSection.cast_alternating_apply,
      ContMDiffSection.curryLeft_wedge_apply (A.extDeriv 0 φ) ψ a,
      curryLeft_extDeriv_zero, smul_eq_mul]
    simp only [Function.comp_def, Fin.cast_cast, Fin.cast_eq_self]
    suffices ∀ a₁ b₁ c₁ d₁ : ℝ,
        a₁ + b₁ - (c₁ + d₁) = (a₁ + (-1 : ℝ) ^ (0 + 1) * c₁) + (b₁ - d₁) from
      this _ _ _ _
    intro a₁ b₁ c₁ d₁
    ring

private theorem extDeriv_cast_cochain {m m' : ℕ} (h : m = m') (η : A.Cochain m) :
    A.extDeriv m' (LinearEquiv.cast (R := ℝ) (M := A.Cochain) h η) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain) (congrArg (· + 1) h) (A.extDeriv m η) := by
  subst h
  rfl

private theorem curryLeft_wedge_extDeriv_succ_apply {k l : ℕ} (φ : A.Cochain (k + 1))
    (ψ : A.Cochain (l + 1)) (a : Cₛ^∞⟮I; F, V⟯) (x : M)
    (w : Fin ((k + 1) + (l + 1)) → V x) :
    ContMDiffSection.curryLeft (k := (k + 1) + (l + 1))
        (φ.wedge (A.extDeriv (l + 1) ψ)) a x w =
      (φ.curryLeft a).wedge (A.extDeriv (l + 1) ψ) x
        (fun i ↦ w (Fin.cast (by omega : k + (l + 1) + 1 = (k + 1) + (l + 1)) i)) +
      (-1 : ℝ) ^ (k + 1) * (φ.wedge (A.lieDeriv a ψ) x w -
        φ.wedge (A.extDeriv l (ψ.curryLeft a)) x w) := by
  have hc : ContMDiffSection.curryLeft (k := (k + 1) + (l + 1))
        (φ.wedge (A.extDeriv (l + 1) ψ)) a x w =
      (φ.curryLeft a).wedge (A.extDeriv (l + 1) ψ) x
        (w ∘ Fin.cast (show k + ((l + 1) + 1) = (k + 1) + (l + 1) by omega)) +
      (-1 : ℝ) ^ (k + 1) • φ.wedge ((A.extDeriv (l + 1) ψ).curryLeft a) x w :=
    ContMDiffSection.curryLeft_wedge_apply φ (A.extDeriv (l + 1) ψ) a x w
  have hd : (A.extDeriv (l + 1) ψ).curryLeft a =
      A.lieDeriv a ψ - A.extDeriv l (ψ.curryLeft a) :=
    A.interior_extDeriv_succ a ψ
  rw [hc, hd, ContMDiffSection.wedge_sub_right]
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    smul_eq_mul]
  rfl

/-- Inductive step `(k + 1, l + 1)` of `extDeriv_wedge`. -/
private theorem extDeriv_wedge_succ {k l : ℕ} (φ : A.Cochain (k + 1)) (ψ : A.Cochain (l + 1))
    (ih₁ : ∀ φ' : A.Cochain k,
      A.extDeriv (k + (l + 1)) (φ'.wedge ψ) =
        LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (show k + 1 + (l + 1) = k + (l + 1) + 1 by omega) ((A.extDeriv k φ').wedge ψ) +
        (-1 : ℝ) ^ k • φ'.wedge (A.extDeriv (l + 1) ψ))
    (ih₂ : ∀ ψ' : A.Cochain l,
      A.extDeriv (k + 1 + l) (φ.wedge ψ') =
        LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (show (k + 1) + 1 + l = (k + 1) + l + 1 by omega)
          ((A.extDeriv (k + 1) φ).wedge ψ') +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (A.extDeriv l ψ')) :
    A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain)
        (show (k + 1) + 1 + (l + 1) = (k + 1) + (l + 1) + 1 by omega)
        ((A.extDeriv (k + 1) φ).wedge ψ) +
      (-1 : ℝ) ^ (k + 1) • φ.wedge (A.extDeriv (l + 1) ψ) := by
  refine A.interior_injective fun a ↦ ?_
  ext x w
  have hpow : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hL : A.interior a (A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ)) =
      (A.lieDeriv a φ).wedge ψ + φ.wedge (A.lieDeriv a ψ) -
        (LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (show k + (l + 1) + 1 = (k + 1) + (l + 1) by omega)
          (A.extDeriv (k + (l + 1)) ((φ.curryLeft a).wedge ψ)) +
          (-1 : ℝ) ^ (k + 1) • A.extDeriv (k + 1 + l) (φ.wedge (ψ.curryLeft a))) := by
    have h1 : A.interior a (A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ)) =
        A.lieDeriv (k := (k + 1) + (l + 1)) a (φ.wedge ψ) -
          A.extDeriv (k + 1 + l) (A.interior (k := k + 1 + l) a (φ.wedge ψ)) :=
      A.interior_extDeriv_succ (k := k + 1 + l) a (φ.wedge ψ)
    have h2 : A.interior (k := k + 1 + l) a (φ.wedge ψ) =
        LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (show k + (l + 1) = k + 1 + l by omega) ((φ.curryLeft a).wedge ψ) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.curryLeft a) :=
      ContMDiffSection.curryLeft_wedge φ ψ a
    rw [h1, A.lieDeriv_wedge a φ ψ, h2, map_add, LinearMap.map_smul, A.extDeriv_cast_cochain]
  rw [hL, ih₁ (φ.curryLeft a), ih₂ (ψ.curryLeft a), interior_apply,
    ContMDiffSection.curryLeft_add_left, ContMDiffSection.curryLeft_smul_left]
  simp only [map_add, ContMDiffSection.curryLeft_cast_alternating,
    ContMDiffSection.curryLeft_wedge_apply, ← A.interior_apply a (A.extDeriv (k + 1) φ),
    A.interior_extDeriv_succ, interior_apply, ContMDiffSection.wedge_sub_left,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub, ContMDiffSection.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContMDiffSection.cast_alternating_apply, smul_eq_mul]
  simp only [Function.comp_def, Fin.cast_cast, Fin.cast_eq_self,
    A.curryLeft_wedge_extDeriv_succ_apply]
  suffices ∀ a₁ b₁ g₁ f₁ d₁ e₁ : ℝ,
      a₁ + b₁ - ((g₁ + (-1 : ℝ) ^ k * d₁) +
          (-1 : ℝ) ^ (k + 1) * (e₁ + (-1 : ℝ) ^ (k + 1) * f₁)) =
        ((a₁ - g₁) + (-1 : ℝ) ^ (k + 1 + 1) * e₁) +
          (-1 : ℝ) ^ (k + 1) * (d₁ + (-1 : ℝ) ^ (k + 1) * (b₁ - f₁)) from
    this _ _ _ _ _ _
  intro a₁ b₁ g₁ f₁ d₁ e₁
  simp only [mul_add, mul_sub, ← mul_assoc, hpow, one_mul]
  simp only [pow_succ]
  ring

/-- **Graded Leibniz rule** for the Chevalley–Eilenberg differential and `ContMDiffSection.wedge`:
`d_A (φ ∧ ψ) = d_A φ ∧ ψ + (-1)^k • φ ∧ d_A ψ`, with `d_A φ ∧ ψ` transported across
`k + 1 + l = k + l + 1`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.extDeriv (k + l) (φ.wedge ψ) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain)
        (show k + 1 + l = k + l + 1 by omega) ((A.extDeriv k φ).wedge ψ) +
      (-1 : ℝ) ^ k • φ.wedge (A.extDeriv l ψ) := by
  -- Induct on total degree `n = k + l`, using Cartan's formula and injectivity of `interior`.
  suffices ∀ (n k l : ℕ), k + l = n → ∀ (φ : A.Cochain k) (ψ : A.Cochain l),
      A.extDeriv (k + l) (φ.wedge ψ) =
        LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (show k + 1 + l = k + l + 1 by omega) ((A.extDeriv k φ).wedge ψ) +
        (-1 : ℝ) ^ k • φ.wedge (A.extDeriv l ψ) from this (k + l) k l rfl φ ψ
  intro n
  refine n.strong_induction_on fun n ih k l hkl φ ψ ↦ ?_
  cases k with
  | zero => simpa using A.extDeriv_wedge_zero_left φ ψ
  | succ k =>
    cases l with
    | zero =>
      rw [A.cast_cochain_self]
      simpa using A.extDeriv_wedge_zero_right φ ψ
    | succ l =>
      exact A.extDeriv_wedge_succ φ ψ
        (fun φ' ↦ ih (k + (l + 1)) (by omega) k (l + 1) rfl φ' ψ)
        (fun ψ' ↦ ih (k + 1 + l) (by omega) (k + 1) l rfl φ ψ')

/-- Pointwise evaluation form of the graded Leibniz rule `extDeriv_wedge`. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l)
    (x : M) (v : Fin (k + l + 1) → V x) :
    A.extDeriv (k + l) (φ.wedge ψ) x v =
      (A.extDeriv k φ).wedge ψ x (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • φ.wedge (A.extDeriv l ψ) x v := by
  have h := DFunLike.congr_fun (congrArg (· x) (A.extDeriv_wedge φ ψ)) v
  simpa only [ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContMDiffSection.cast_alternating_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply] using h

end ArbitraryAlgebroid

end Complex

/-! ### Comparison with the de Rham complex on the tangent Lie algebroid -/

section Tangent

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- Smooth `k`-cochains of `LieAlgebroid.tangent I M` identify `ℝ`-linearly with smooth real-valued
differential `k`-forms `SmoothForm I M ℝ k`. -/
def tangentCochainEquivSmoothForm (k : ℕ) :
    (tangent I M).Cochain k ≃ₗ[ℝ] SmoothForm I M ℝ k where
  toFun := SmoothForm.ofContMDiffSection
  invFun := SmoothForm.toContMDiffSection
  left_inv := SmoothForm.toContMDiffSection_ofContMDiffSection
  right_inv := SmoothForm.ofContMDiffSection_toContMDiffSection
  map_add' _ _ := SmoothForm.toContMDiffSection_injective (by simp)
  map_smul' _ _ := SmoothForm.toContMDiffSection_injective (by simp)

@[simp]
theorem tangentCochainEquivSmoothForm_apply {k : ℕ} (φ : (tangent I M).Cochain k) (x : M) :
    (tangentCochainEquivSmoothForm I M k φ).1 x = φ x := by
  rw [← SmoothForm.toContMDiffSection_apply]
  exact congrArg (· x) (SmoothForm.toContMDiffSection_ofContMDiffSection φ)

@[simp]
theorem tangentCochainEquivSmoothForm_symm_apply {k : ℕ} (ψ : SmoothForm I M ℝ k) (x : M) :
    (tangentCochainEquivSmoothForm I M k).symm ψ x = ψ.1 x :=
  SmoothForm.toContMDiffSection_apply ψ x

section T2

variable [T2Space M]

private theorem tangent_extDeriv_succ_evalSections_apply (m : ℕ)
    (φ : (tangent I M).Cochain (m + 1)) (s : Fin (m + 2) → Cₛ^∞⟮I; E, TangentSpace I⟯) (x : M) :
    (tangent I M).evalSections ((tangent I M).extDeriv (m + 1) φ) s x =
      (∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val •
          mvfderiv I (fun y ↦ φ y (i.removeNth (s · y))) x (s i x)) -
        ∑ i : Fin (m + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j : ℕ) •
          φ x (Matrix.vecCons (mlieBracket I (s i.castSucc) (s j.succ) x)
            (j.removeNth (i.castSucc.removeNth (s · x)))) := by
  rw [(tangent I M).extDeriv_succ_evalSections, ContMDiffMap.coe_add, Pi.add_apply, sub_eq_add_neg]
  congr 1
  · rw [← ContMDiffMap.coeFnLinearMap_apply (𝕜 := ℝ), map_sum]
    simp_rw [map_zsmul]
    simp only [Finset.sum_apply, Pi.smul_apply, ContMDiffMap.coeFnLinearMap_apply,
      anchorDeriv_apply, tangent_anchor_apply]
    refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ i.val • ·) ?_
    have hf : ⇑((tangent I M).evalSections φ (i.removeNth s)) =
        fun y ↦ φ y (i.removeNth (s · y)) := by
      ext y
      rw [evalSections_apply]
      congr 1
    rw [hf]
  · rw [← ContMDiffMap.coeFnLinearMap_apply (𝕜 := ℝ), map_sum, ← Finset.sum_neg_distrib]
    simp_rw [map_sum, map_zsmul, ← Finset.sum_neg_distrib]
    simp only [Finset.sum_apply, Pi.smul_apply, ContMDiffMap.coeFnLinearMap_apply,
      evalSections_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_succ, mul_neg, mul_one, neg_zsmul]
    refine congrArg (- ·) (congrArg (_ • ·) (congrArg (φ x) ?_))
    ext r
    cases r using Fin.cases <;> simp [Fin.removeNth]

/-- On the tangent Lie algebroid `LieAlgebroid.tangent I M`, the Chevalley–Eilenberg differential
agrees pointwise with the manifold exterior derivative `mextDeriv`. -/
theorem tangent_extDeriv_apply (k : ℕ) (φ : (tangent I M).Cochain k) (x : M) :
    (tangent I M).extDeriv k φ x = mextDeriv (fun y ↦ φ y) x := by
  ext w
  choose s hs using fun i ↦
    ContMDiffSection.evalLinearMap_surjective (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) ∞ x (w i)
  have hw : (s · x) = w := funext fun i ↦ by
    simpa only [ContMDiffSection.evalLinearMap_apply] using hs i
  have hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (φ y)) x :=
    (φ.contMDiff x).mdifferentiableAt (by simp)
  have hs_diff : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (s i y : TangentBundle I M)) x :=
    fun i ↦ ((s i).contMDiff x).mdifferentiableAt (by simp)
  rw [← hw, ← evalSections_apply (tangent I M)]
  cases k with
  | zero =>
    rw [(tangent I M).extDeriv_zero_evalSections, anchorDeriv_apply, tangent_anchor_apply,
      mextDeriv_apply_vectorField_of_mlieBracket_eq_zero hφ hs_diff]
    · rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, val_zero, pow_zero, one_smul]
      have hf : ⇑((tangent I M).cochainZeroEquiv φ) = fun y ↦ φ y (removeNth 0 (s · y)) := by
        ext y
        rw [cochainZeroEquiv_apply]
        exact congrArg (φ y) (Subsingleton.elim (0 : Fin 0 → TangentSpace I y) _)
      rw [hf]
    · intro i j
      obtain rfl : i = j := by omega
      simp
  | succ m =>
    rw [tangent_extDeriv_succ_evalSections_apply, mextDeriv_apply_vectorField hφ hs_diff]

/-- `tangentCochainEquivSmoothForm` intertwines the Chevalley–Eilenberg differential of
`LieAlgebroid.tangent I M` with the bundled de Rham exterior derivative `mextDerivₗ`. -/
@[simp]
theorem tangentCochainEquivSmoothForm_extDeriv (k : ℕ) (φ : (tangent I M).Cochain k) :
    tangentCochainEquivSmoothForm I M (k + 1) ((tangent I M).extDeriv k φ) =
      mextDerivₗ I k (tangentCochainEquivSmoothForm I M k φ) := by
  refine SmoothForm.toContMDiffSection_injective ?_
  ext x w
  have hη : (tangentCochainEquivSmoothForm I M k φ).1 = fun y ↦ φ y :=
    funext (tangentCochainEquivSmoothForm_apply φ)
  simp only [SmoothForm.toContMDiffSection_apply, tangentCochainEquivSmoothForm_apply,
    mextDerivₗ_apply, hη]
  exact DFunLike.congr_fun (tangent_extDeriv_apply k φ x) w

end T2

end Tangent

end TauCeti.LieAlgebroid
