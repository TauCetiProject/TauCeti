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
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Wedge
import TauCeti.Algebra.Ring.Parity
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

For a Lie algebroid `A` on a smooth real vector bundle `V → M`, a `k`-cochain (`A.Cochain k`) is a
smooth section of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`, i.e., `Γ(⋀^k A*)`.

Over a finite-dimensional Hausdorff base `M` and finite-rank smooth vector bundle `V`,
`ContMDiffSection.alternatingEquiv` identifies `A.Cochain k` `C^∞(M)`-linearly with
`A.Sections [⋀^Fin k]→ₗ[C^∞(M)] C^∞(M)`. Transporting `TauCeti.LieRinehartAlgebra` across this
equivalence yields the Lie derivative `A.lieDeriv` and Chevalley–Eilenberg differential
`A.extDeriv`, satisfying the invariant Chevalley–Eilenberg formula, `d_A ∘ d_A = 0`, Cartan
calculus with `ContMDiffSection.curryLeft`, and graded Leibniz rules for `ContMDiffSection.wedge`.
For `LieAlgebroid.tangent I M`, `A.extDeriv` agrees with the de Rham exterior derivative
`mextDeriv`, and `ContMDiffSection.wedge` agrees with `SmoothForm.wedge`.

## Main definitions

* `TauCeti.LieAlgebroid.Cochain`, `cochainZeroEquiv`, `cochainSectionsEquiv`: smooth `k`-cochains
  `Γ(⋀^k A*)`, degree-zero identification, and multilinear section equivalence.
* `TauCeti.LieAlgebroid.lieDeriv`, `extDeriv`, `cochainComplex`, `cochainComplexXIso`,
  `cohomology`: Lie derivative, Chevalley–Eilenberg differential, cochain complex in `ModuleCat ℝ`,
  canonical degreewise carrier isomorphism, and cohomology `H^k(A)`.
* `TauCeti.LieAlgebroid.tangentCochainEquivSmoothForm`: `(tangent I M).Cochain k ≃ₗ[ℝ]` smooth
  differential `k`-forms on `M`.

## Main results

* `TauCeti.LieAlgebroid.evalSection_extDeriv_succ`, `extDeriv_extDeriv`: Chevalley–Eilenberg
  formula on sections and `d_A ∘ d_A = 0`.
* `TauCeti.LieAlgebroid.curryLeft_extDeriv_succ`, `lieDeriv_wedge`, `extDeriv_wedge`: Cartan's
  homotopy formula and graded Leibniz rules for `ContMDiffSection.wedge`.
* `TauCeti.LieAlgebroid.tangent_extDeriv_apply`, `tangentCochainEquivSmoothForm_extDeriv`,
  `tangentCochainEquivSmoothForm_wedge`: comparison of `(tangent I M).extDeriv` and
  `ContMDiffSection.wedge` with `mextDeriv` and `SmoothForm.wedge`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, LMS Lecture Note Ser.
  213, Cambridge Univ. Press (2005), §7.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), §1.2.
* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222.
-/

public section

noncomputable section

open Bundle CategoryTheory Fin Manifold VectorField
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

@[simp] theorem cochainZeroEquiv_apply (φ : A.Cochain 0) (x : M) :
    A.cochainZeroEquiv φ x = φ x 0 :=
  ContMDiffSection.alternatingIsEmptyEquiv_apply φ x

@[simp] theorem cochainZeroEquiv_symm_apply (f : C^∞⟮I, M; ℝ⟯) (x : M) (v : Fin 0 → V x) :
    A.cochainZeroEquiv.symm f x v = f x :=
  ContMDiffSection.alternatingIsEmptyEquiv_symm_apply f x v

/-- Evaluating a degree-`0` cochain on an empty tuple of sections yields its corresponding smooth
function under `cochainZeroEquiv`. -/
theorem evalSection_eq_cochainZeroEquiv (φ : A.Cochain 0) (s : Fin 0 → Cₛ^∞⟮I; F, V⟯) :
    φ.evalSection s = A.cochainZeroEquiv φ := by
  ext x
  rw [ContMDiffSection.evalSection_apply, cochainZeroEquiv_apply]
  exact congrArg (φ x) (Subsingleton.elim (s · x) 0)

private theorem cast_cochain_self {m : ℕ} (h : m = m) (φ : A.Cochain m) :
    LinearEquiv.cast (R := ℝ) (M := A.Cochain) h φ = φ := by simp

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
  have hdisj (i : Fin k) (j : Fin l) : Fin.castAdd l i ≠ Fin.natAdd k j :=
    Fin.ext_iff.ne.2 <| Nat.ne_of_lt <| by
      rw [Fin.val_castAdd, Fin.val_natAdd]; exact lt_of_lt_of_le i.isLt (Nat.le_add_right k j)
  rw [← Equiv.sum_comp σ, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg₂ (· * ·) ?_ ?_
    · exact congrArg φ.evalSection <|
        Function.update_comp_eq_of_injective s (σ.injective.comp (Fin.castAdd_injective _ l)) i _
    · exact congrArg ψ.evalSection <|
        Function.update_comp_eq_of_forall_ne s _ fun j ↦ σ.injective.ne (hdisj i j).symm
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· * ·) ?_ ?_
    · exact congrArg φ.evalSection <|
        Function.update_comp_eq_of_forall_ne s _ fun i ↦ σ.injective.ne (hdisj i j)
    · exact congrArg ψ.evalSection <|
        Function.update_comp_eq_of_injective s (σ.injective.comp (Fin.natAdd_injective _ k)) j _

section Complex

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

/-- Over a finite-dimensional Hausdorff manifold and a finite-rank Lie algebroid `A`, `k`-cochains
identify `C^∞(M)`-linearly with `C^∞(M)`-multilinear alternating maps on `A.Sections`. -/
def cochainSectionsEquiv (k : ℕ) :
    A.Cochain k ≃ₗ[C^∞⟮I, M; ℝ⟯] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (ContMDiffSection.alternatingEquiv I F V (Fin k)).trans
    (AlternatingMap.domLCongr C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (Fin k) C^∞⟮I, M; ℝ⟯ A.sectionsEquiv.symm)

@[simp] theorem cochainSectionsEquiv_apply {k : ℕ} (φ : A.Cochain k) (s : Fin k → A.Sections) :
    A.cochainSectionsEquiv k φ s = φ.evalSection (A.sectionsEquiv ∘ s) := by
  ext x
  simp [cochainSectionsEquiv, AlternatingMap.compLinearMap_apply]

@[simp] theorem cochainSectionsEquiv_symm_apply_apply {k : ℕ}
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.cochainSectionsEquiv k).symm Φ x (s · x) = Φ (A.sectionsEquiv.symm ∘ s) x := by
  simp [cochainSectionsEquiv, AlternatingMap.compLinearMap_apply, Function.comp_def]

private theorem evalSection_eq_cochainSectionsEquiv {k : ℕ} (φ : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    φ.evalSection s = A.cochainSectionsEquiv k φ (A.sectionsEquiv.symm ∘ s) := by
  rw [cochainSectionsEquiv_apply]
  exact congrArg φ.evalSection (funext fun i ↦ by simp)

private theorem cochainSectionsEquiv_removeNth {k : ℕ} (φ : A.Cochain k)
    (s : Fin (k + 1) → Cₛ^∞⟮I; F, V⟯) (i : Fin (k + 1)) :
    A.cochainSectionsEquiv k φ (i.removeNth (A.sectionsEquiv.symm ∘ s)) =
      φ.evalSection (i.removeNth s) := by
  rw [A.evalSection_eq_cochainSectionsEquiv]
  exact congrArg _ (Fin.removeNth_comp A.sectionsEquiv.symm i s)

@[simp] theorem cochainSectionsEquiv_curryLeft {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) :
    A.cochainSectionsEquiv k (φ.curryLeft a) =
      (A.cochainSectionsEquiv (k + 1) φ).curryLeft (A.sectionsEquiv.symm a) := by
  simp [cochainSectionsEquiv, AlternatingMap.domLCongr_apply,
    AlternatingMap.curryLeft_compLinearMap]

/-! ### Lie derivative and Chevalley–Eilenberg differential -/

/-- The Lie derivative `L_a : A.Cochain k →ₗ[ℝ] A.Cochain k` along a smooth section `a`,
transported from `TauCeti.LieRinehartAlgebra.lieDeriv` across `cochainSectionsEquiv`. -/
def lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) : A.Cochain k →ₗ[ℝ] A.Cochain k :=
  (((A.cochainSectionsEquiv k).restrictScalars ℝ).arrowCongr
      ((A.cochainSectionsEquiv k).restrictScalars ℝ)).symm
    (LieRinehartAlgebra.lieDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections (A.sectionsEquiv.symm a))

@[simp] theorem cochainSectionsEquiv_lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.cochainSectionsEquiv k (A.lieDeriv a φ) = LieRinehartAlgebra.lieDeriv ℝ C^∞⟮I, M; ℝ⟯
      A.Sections (A.sectionsEquiv.symm a) (A.cochainSectionsEquiv k φ) := by
  simp only [lieDeriv, LinearEquiv.arrowCongr_symm_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.apply_symm_apply]

/-- The Chevalley–Eilenberg differential `d_A : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1)` of a Lie
algebroid `A`, transported from `TauCeti.LieRinehartAlgebra.extDeriv` across
`cochainSectionsEquiv`. -/
def extDeriv (k : ℕ) : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1) :=
  (((A.cochainSectionsEquiv k).restrictScalars ℝ).arrowCongr
      ((A.cochainSectionsEquiv (k + 1)).restrictScalars ℝ)).symm
    (LieRinehartAlgebra.extDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections k)

@[simp] theorem cochainSectionsEquiv_extDeriv (k : ℕ) (φ : A.Cochain k) :
    A.cochainSectionsEquiv (k + 1) (A.extDeriv k φ) =
      LieRinehartAlgebra.extDeriv ℝ C^∞⟮I, M; ℝ⟯ A.Sections k (A.cochainSectionsEquiv k φ) := by
  simp only [extDeriv, LinearEquiv.arrowCongr_symm_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.apply_symm_apply]

/-! ### Explicit evaluation formulas on smooth sections -/

/-- Explicit formula for the Lie derivative on smooth sections:
`(L_a φ)(s₀, …, sₖ₋₁) = ρ(a)(φ(s₀, …, sₖ₋₁)) - ∑ i, φ(s₀, …, [a, sᵢ], …, sₖ₋₁)`. -/
theorem evalSection_lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    (A.lieDeriv a φ).evalSection s = A.anchorDeriv a (φ.evalSection s) -
      ∑ i : Fin k, φ.evalSection (Function.update s i (A.bracket a (s i))) := by
  rw [A.evalSection_eq_cochainSectionsEquiv, cochainSectionsEquiv_lieDeriv,
    LieRinehartAlgebra.lieDeriv_apply, lie_sectionsEquiv_symm,
    ← A.evalSection_eq_cochainSectionsEquiv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [A.evalSection_eq_cochainSectionsEquiv, Function.comp_update, Function.comp_apply,
    sectionsEquiv_symm_bracket]

/-- In degree zero, `(d_A φ)(s₀) = ρ(s₀)(φ)`. -/
@[simp] theorem evalSection_extDeriv_zero (φ : A.Cochain 0) (s : Fin 1 → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 φ).evalSection s = A.anchorDeriv (s 0) (A.cochainZeroEquiv φ) := by
  rw [A.evalSection_eq_cochainSectionsEquiv, cochainSectionsEquiv_extDeriv,
    LieRinehartAlgebra.extDeriv_zero_apply, Function.comp_apply, lie_sectionsEquiv_symm,
    cochainSectionsEquiv_apply, A.evalSection_eq_cochainZeroEquiv]

/-- **The Chevalley–Eilenberg formula** for a Lie algebroid cochain of positive degree evaluated on
smooth sections:
`(d_A φ)(s₀, …, sₖ₊₁) = ∑ i, (-1)^i ρ(sᵢ)(φ(…, ŝᵢ, …))`
`  + ∑_{i < j} (-1)^(i + j) φ([sᵢ, sⱼ], s₀, …, ŝᵢ, …, ŝⱼ, …, sₖ₊₁)`,
with pairs `i < j` parametrized as `(i.castSucc, j.succ)` for `i ≤ j`. -/
theorem evalSection_extDeriv_succ {k : ℕ} (φ : A.Cochain (k + 1))
    (s : Fin (k + 2) → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv (k + 1) φ).evalSection s =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          A.anchorDeriv (s i) (φ.evalSection (i.removeNth s)) +
        ∑ i : Fin (k + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          φ.evalSection (Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ))
            (j.removeNth (i.castSucc.removeNth s))) := by
  rw [A.evalSection_eq_cochainSectionsEquiv, cochainSectionsEquiv_extDeriv,
    LieRinehartAlgebra.extDeriv_succ_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
    rw [Function.comp_apply, lie_sectionsEquiv_symm, cochainSectionsEquiv_removeNth]
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      congrArg ((-1 : ℤ) ^ (i + j + 1 : ℕ) • ·) ?_
    rw [A.evalSection_eq_cochainSectionsEquiv]
    congr 1
    simp only [Matrix.vecCons, Fin.comp_cons, Function.comp_apply, sectionsEquiv_symm_bracket]
    rw [Function.comp_def, Fin.removeNth_comp, Fin.removeNth_comp]
    rfl

/-- On a `1`-cochain and two smooth sections `a`, `b`,
`(d_A φ)(a, b) = ρ(a)(φ(b)) - ρ(b)(φ(a)) - φ([a, b])`. -/
theorem evalSection_extDeriv_one (φ : A.Cochain 1) (a b : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 1 φ).evalSection ![a, b] =
      A.anchorDeriv a (φ.evalSection ![b]) - A.anchorDeriv b (φ.evalSection ![a]) -
        φ.evalSection ![A.bracket a b] := by
  rw [A.evalSection_extDeriv_succ (k := 0) φ ![a, b], Fin.sum_univ_two, Fin.sum_univ_one]
  have hIci : Finset.Ici (0 : Fin 1) = {0} := by ext j; fin_cases j; simp
  have h₀ : removeNth (0 : Fin 2) ![a, b] = ![b] := by funext i; fin_cases i; rfl
  have h₁ : removeNth (1 : Fin 2) ![a, b] = ![a] := by funext i; fin_cases i; rfl
  rw [hIci, Finset.sum_singleton]
  simp only [val_zero, val_one, castSucc_zero, succ_zero_eq_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, h₀, h₁]
  abel

/-- Scalar Leibniz rule for `d_A` evaluated on smooth sections. -/
theorem evalSection_extDeriv_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (φ : A.Cochain k)
    (s : Fin (k + 1) → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv k (f • φ)).evalSection s = f * (A.extDeriv k φ).evalSection s +
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) •
        (A.anchorDeriv (s i) f * φ.evalSection (i.removeNth s)) := by
  rw [A.evalSection_eq_cochainSectionsEquiv, cochainSectionsEquiv_extDeriv,
    (A.cochainSectionsEquiv k).map_smul, LieRinehartAlgebra.extDeriv_smul_apply,
    ← cochainSectionsEquiv_extDeriv, ← A.evalSection_eq_cochainSectionsEquiv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
  rw [Function.comp_apply, lie_sectionsEquiv_symm, cochainSectionsEquiv_removeNth]

/-! ### Cochain complex, cohomology, and Cartan calculus -/

/-- The Chevalley–Eilenberg differential of a Lie algebroid squares to zero. -/
@[simp] theorem extDeriv_extDeriv (k : ℕ) (φ : A.Cochain k) :
    A.extDeriv (k + 1) (A.extDeriv k φ) = 0 :=
  (A.cochainSectionsEquiv (k + 2)).injective (by simp)

theorem extDeriv_comp_extDeriv (k : ℕ) : A.extDeriv (k + 1) ∘ₗ A.extDeriv k = 0 :=
  LinearMap.ext (A.extDeriv_extDeriv k)

private theorem cochainComplex_sq (k : ℕ) :
    ModuleCat.ofHom (A.extDeriv k) ≫ ModuleCat.ofHom (A.extDeriv (k + 1)) = 0 := by
  rw [← ModuleCat.ofHom_comp, A.extDeriv_comp_extDeriv, ModuleCat.ofHom_zero]

/-- The Chevalley–Eilenberg cochain complex of `A` in `ModuleCat ℝ`, whose degree-`k` term is
`A.Cochain k` and whose differential is `A.extDeriv k`. -/
def cochainComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (A.Cochain k))
    (fun k ↦ ModuleCat.ofHom (A.extDeriv k)) A.cochainComplex_sq

/-- The canonical identification of the degree-`k` object of `A.cochainComplex` with
`A.Cochain k`. This isomorphism makes the cochain carrier available without unfolding
`cochainComplex`. -/
def cochainComplexXIso (k : ℕ) :
    A.cochainComplex.X k ≅ ModuleCat.of ℝ (A.Cochain k) :=
  eqToIso (congrFun (CochainComplex.of_X (fun k ↦ ModuleCat.of ℝ (A.Cochain k))
    (fun k ↦ ModuleCat.ofHom (A.extDeriv k)) A.cochainComplex_sq) k)

/-- Under the canonical identifications of the objects, the differential of `A.cochainComplex` is
`A.extDeriv`. -/
@[reassoc]
theorem cochainComplex_d (k : ℕ) :
    A.cochainComplex.d k (k + 1) ≫ (A.cochainComplexXIso (k + 1)).hom =
      (A.cochainComplexXIso k).hom ≫ ModuleCat.ofHom (A.extDeriv k) := by
  simp [cochainComplex, cochainComplexXIso, CochainComplex.of_d]

/-- The `k`-th Lie algebroid cohomology `H^k(A)` of `A` with trivial coefficients, the homology of
`A.cochainComplex` in degree `k`. -/
abbrev cohomology (k : ℕ) : ModuleCat ℝ := A.cochainComplex.homology k

@[simp] theorem lieDeriv_zero_left {k : ℕ} (φ : A.Cochain k) : A.lieDeriv 0 φ = 0 :=
  (A.cochainSectionsEquiv k).injective (by simp)

@[simp] theorem lieDeriv_add_left {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv (a + b) φ = A.lieDeriv a φ + A.lieDeriv b φ :=
  (A.cochainSectionsEquiv k).injective (by simp)

@[simp] theorem lieDeriv_const_smul_left {k : ℕ} (c : ℝ) (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv (c • a) φ = c • A.lieDeriv a φ :=
  (A.cochainSectionsEquiv k).injective <| by
    rw [cochainSectionsEquiv_lieDeriv, LinearMapClass.map_smul_of_tower A.sectionsEquiv.symm c,
      LieRinehartAlgebra.lieDeriv_const_smul_left,
      LinearMapClass.map_smul_of_tower (A.cochainSectionsEquiv k) c, cochainSectionsEquiv_lieDeriv]

/-- Scalar Leibniz rule for the Lie derivative: `L_a (f • φ) = f • L_a φ + (ρ(a) f) • φ`. -/
theorem lieDeriv_smul_right {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (φ : A.Cochain k) :
    A.lieDeriv a (f • φ) = f • A.lieDeriv a φ + A.anchorDeriv a f • φ :=
  (A.cochainSectionsEquiv k).injective <| by
    simp [LieRinehartAlgebra.lieDeriv_smul_right]

/-- Cartan's homotopy formula in degree zero: `ι_a (d_A φ) = L_a φ`. -/
@[simp] theorem curryLeft_extDeriv_zero (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain 0) :
    (A.extDeriv 0 φ).curryLeft a = A.lieDeriv a φ :=
  (A.cochainSectionsEquiv 0).injective (by simp)

/-- **Cartan's homotopy formula** in positive degree: `ι_a (d_A φ) = L_a φ - d_A (ι_a φ)`. -/
@[simp] theorem curryLeft_extDeriv_succ {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    (A.extDeriv (k + 1) φ).curryLeft a = A.lieDeriv a φ - A.extDeriv k (φ.curryLeft a) :=
  (A.cochainSectionsEquiv (k + 1)).injective (by simp)

/-- **Cartan's magic formula** `L_a φ = ι_a (d_A φ) + d_A (ι_a φ)` in positive degree. -/
theorem lieDeriv_succ_eq_curryLeft_extDeriv_add {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) :
    A.lieDeriv a φ = (A.extDeriv (k + 1) φ).curryLeft a + A.extDeriv k (φ.curryLeft a) := by
  rw [A.curryLeft_extDeriv_succ]; abel

/-- Cartan's commutator identity `ι_b (L_a φ) = L_a (ι_b φ) - ι_{[a, b]} φ`. -/
theorem curryLeft_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    (A.lieDeriv a φ).curryLeft b =
      A.lieDeriv a (φ.curryLeft b) - φ.curryLeft (A.bracket a b) :=
  (A.cochainSectionsEquiv k).injective <| by
    simp [LieRinehartAlgebra.curryLeft_lieDeriv]

/-- Cartan's commutator identity `[L_a, ι_b] = ι_{[a, b]}`. -/
theorem lieDeriv_curryLeft_sub {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain (k + 1)) :
    A.lieDeriv a (φ.curryLeft b) - (A.lieDeriv a φ).curryLeft b =
      φ.curryLeft (A.bracket a b) := by rw [A.curryLeft_lieDeriv]; abel

/-- The Lie derivative is a representation of smooth sections: `[L_a, L_b] = L_{[a, b]}`. -/
theorem lieDeriv_lieDeriv_sub {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv a (A.lieDeriv b φ) - A.lieDeriv b (A.lieDeriv a φ) =
      A.lieDeriv (A.bracket a b) φ :=
  (A.cochainSectionsEquiv k).injective <| by
    simp [LieRinehartAlgebra.lieDeriv_lieDeriv_sub]

/-- Naturality of the Chevalley–Eilenberg differential: `L_a (d_A φ) = d_A (L_a φ)`. -/
@[simp] theorem lieDeriv_extDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) :
    A.lieDeriv a (A.extDeriv k φ) = A.extDeriv k (A.lieDeriv a φ) :=
  (A.cochainSectionsEquiv (k + 1)).injective (by simp)

/-! ### Graded derivation laws for the wedge product -/

/-- The Lie derivative is an even derivation of `ContMDiffSection.wedge`:
`L_a (φ ∧ ψ) = L_a φ ∧ ψ + φ ∧ L_a ψ`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.lieDeriv a (φ.wedge ψ) = (A.lieDeriv a φ).wedge ψ + φ.wedge (A.lieDeriv a ψ) := by
  refine ContMDiffSection.ext_evalSection fun s ↦ ?_
  simp only [A.evalSection_lieDeriv, ContMDiffSection.evalSection_add,
    ContMDiffSection.evalSection_wedge, A.anchorDeriv_const_smul_right]
  conv_lhs =>
    rw [← A.lie_sectionsEquiv_symm a]
    simp only [lie_sum, Units.smul_def, lie_zsmul, LieRinehartRing.leibniz_mul_right]
  simp only [A.lie_sectionsEquiv_symm, smul_eq_mul, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, A.sum_update_evalSection_wedge]
  simp only [← smul_sub, ← smul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ ↦ congrArg _ ?_)
  simp only [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
  ring

private theorem extDeriv_cast_cochain {m m' : ℕ} (h : m = m') (η : A.Cochain m) :
    A.extDeriv m' (LinearEquiv.cast (R := ℝ) (M := A.Cochain) h η) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain) (congrArg (· + 1) h) (A.extDeriv m η) := by
  subst h; rfl

/-- Base case `l = 0` of `extDeriv_wedge`: no degree cast is needed since `k + 0 = k` is
definitional. -/
private theorem extDeriv_wedge_zero_right {k : ℕ} (φ : A.Cochain k) (ψ : A.Cochain 0) :
    A.extDeriv k (φ.wedge ψ) =
      (A.extDeriv k φ).wedge ψ + (-1 : ℝ) ^ k • φ.wedge (A.extDeriv 0 ψ) := by
  induction k with
  | zero => refine ContMDiffSection.ext_curryLeft fun a ↦ ?_; simp [A.lieDeriv_wedge a φ ψ]
  | succ k ih =>
    refine ContMDiffSection.ext_curryLeft fun a ↦ ?_
    rw [A.curryLeft_extDeriv_succ (k := k) a (φ.wedge ψ), A.lieDeriv_wedge a φ ψ,
      ContMDiffSection.curryLeft_wedge_zero_right φ ψ a, ih,
      ContMDiffSection.curryLeft_add_left, ContMDiffSection.curryLeft_smul_left]
    ext x w
    simp only [ContMDiffSection.curryLeft_wedge_zero_right, A.curryLeft_extDeriv_succ,
      ContMDiffSection.wedge_sub_left, ContMDiffSection.alternating_add_apply,
      ContMDiffSection.alternating_sub_apply, ContMDiffSection.alternating_smul_apply,
      ContMDiffSection.curryLeft_wedge_apply φ (A.extDeriv 0 ψ) a x w,
      curryLeft_extDeriv_zero, smul_eq_mul, Function.comp_def, Fin.cast_eq_self,
      mul_add, neg_one_pow_mul_neg_one_pow_mul]
    rw [pow_succ]
    ring

/-- Base case `k = 0` of `extDeriv_wedge`, deduced from `extDeriv_wedge_zero_right` and graded
commutativity of `ContMDiffSection.wedge`. -/
private theorem extDeriv_wedge_zero_left {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l) :
    A.extDeriv (0 + l) (φ.wedge ψ) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain)
        (Nat.succ_add 0 l) ((A.extDeriv 0 φ).wedge ψ) +
      φ.wedge (A.extDeriv l ψ) := by
  have hcomm : φ.wedge ψ =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain) (Nat.zero_add l).symm (ψ.wedge φ) := by
    simpa using ContMDiffSection.wedge_comm φ ψ
  rw [hcomm, A.extDeriv_cast_cochain, A.extDeriv_wedge_zero_right]
  ext x v
  simp only [ContMDiffSection.cast_alternating_apply, ContMDiffSection.alternating_add_apply,
    ContMDiffSection.alternating_smul_apply]
  rw [ContMDiffSection.wedge_comm_apply (A.extDeriv l ψ) φ,
    ContMDiffSection.wedge_comm_apply ψ (A.extDeriv 0 φ)]
  simp only [zero_add, mul_zero, mul_one, pow_zero, one_smul, Function.comp_def, Fin.cast_cast,
    Fin.cast_eq_self, smul_smul, ← mul_pow, neg_mul_neg, one_pow]
  rw [add_comm]

private theorem curryLeft_wedge_extDeriv_succ_apply {k l : ℕ} (φ : A.Cochain (k + 1))
    (ψ : A.Cochain (l + 1)) (a : Cₛ^∞⟮I; F, V⟯) (x : M) (w : Fin ((k + 1) + (l + 1)) → V x) :
    ContMDiffSection.curryLeft (k := (k + 1) + (l + 1)) (φ.wedge (A.extDeriv (l + 1) ψ)) a x w =
      (φ.curryLeft a).wedge (A.extDeriv (l + 1) ψ) x
        (w ∘ Fin.cast (Nat.succ_add k (l + 1)).symm) +
      (-1 : ℝ) ^ (k + 1) * (φ.wedge (A.lieDeriv a ψ) x w -
        φ.wedge (A.extDeriv l (ψ.curryLeft a)) x w) := by
  rw [ContMDiffSection.curryLeft_wedge_apply φ (A.extDeriv (l + 1) ψ) a x w,
    A.curryLeft_extDeriv_succ a ψ, ContMDiffSection.wedge_sub_right,
    ContMDiffSection.alternating_sub_apply, smul_eq_mul]

/-- Sign cancellation identity used in the `succ`/`succ` inductive step of `extDeriv_wedge`. -/
private theorem extDeriv_wedge_sign_cancel (k : ℕ) (a₁ b₁ g₁ f₁ d₁ e₁ : ℝ) :
    a₁ + b₁ - ((g₁ + (-1 : ℝ) ^ k * d₁) +
        (-1 : ℝ) ^ (k + 1) * (e₁ + (-1 : ℝ) ^ (k + 1) * f₁)) =
      ((a₁ - g₁) + (-1 : ℝ) ^ (k + 1 + 1) * e₁) +
        (-1 : ℝ) ^ (k + 1) * (d₁ + (-1 : ℝ) ^ (k + 1) * (b₁ - f₁)) := by
  simp only [mul_add, mul_sub, neg_one_pow_mul_neg_one_pow_mul]
  simp only [pow_succ]
  ring

/-- Inductive step of `extDeriv_wedge` when both cochains have positive degree. -/
private theorem extDeriv_wedge_succ_succ {k l : ℕ} (φ : A.Cochain (k + 1)) (ψ : A.Cochain (l + 1))
    (ih₁ : ∀ a : Cₛ^∞⟮I; F, V⟯,
      A.extDeriv (k + l).succ ((φ.curryLeft a).wedge ψ) =
        LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (Nat.succ_add k (l + 1))
          ((A.extDeriv k (φ.curryLeft a)).wedge ψ) +
        (-1 : ℝ) ^ k • (φ.curryLeft a).wedge (A.extDeriv (l + 1) ψ))
    (ih₂ : ∀ a : Cₛ^∞⟮I; F, V⟯,
      A.extDeriv (k + 1 + l) (φ.wedge (ψ.curryLeft a)) =
        LinearEquiv.cast (R := ℝ) (M := A.Cochain)
          (Nat.succ_add (k + 1) l)
          ((A.extDeriv (k + 1) φ).wedge (ψ.curryLeft a)) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (A.extDeriv l (ψ.curryLeft a))) :
    A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain)
        (Nat.succ_add (k + 1) (l + 1))
        ((A.extDeriv (k + 1) φ).wedge ψ) +
      (-1 : ℝ) ^ (k + 1) • φ.wedge (A.extDeriv (l + 1) ψ) := by
  -- Separate both sides by interior products `curryLeft a` (`ext_curryLeft`), expand `ι_a d_A` via
  -- Cartan's formula (`curryLeft_extDeriv_succ`), and apply `ih₁` and `ih₂` to the lower-degree
  -- wedges produced by `curryLeft_wedge`.
  refine ContMDiffSection.ext_curryLeft fun a ↦ ?_
  have hL : (A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ)).curryLeft a =
      A.lieDeriv a (φ.wedge ψ) - A.extDeriv (k + 1 + l) ((φ.wedge ψ).curryLeft a) :=
    A.curryLeft_extDeriv_succ (k := k + 1 + l) a (φ.wedge ψ)
  rw [hL, A.lieDeriv_wedge a φ ψ, ContMDiffSection.curryLeft_wedge φ ψ a, map_add,
    LinearMap.map_smul, A.extDeriv_cast_cochain, ih₁ a, ih₂ a,
    ContMDiffSection.curryLeft_add_left, ContMDiffSection.curryLeft_smul_left]
  -- Evaluate pointwise and match the six wedge terms via `extDeriv_wedge_sign_cancel`.
  ext x w
  simp only [map_add, ContMDiffSection.curryLeft_cast_alternating,
    ContMDiffSection.curryLeft_wedge_apply, A.curryLeft_extDeriv_succ,
    ContMDiffSection.wedge_sub_left, ContMDiffSection.alternating_add_apply,
    ContMDiffSection.alternating_sub_apply, ContMDiffSection.alternating_smul_apply,
    ContMDiffSection.cast_alternating_apply, smul_eq_mul, Function.comp_def, Fin.cast_cast,
    Fin.cast_eq_self, A.curryLeft_wedge_extDeriv_succ_apply]
  exact extDeriv_wedge_sign_cancel k _ _ _ _ _ _

/-- **Graded Leibniz rule** for the Chevalley–Eilenberg differential and `ContMDiffSection.wedge`:
`d_A (φ ∧ ψ) = d_A φ ∧ ψ + (-1)^k • φ ∧ d_A ψ`, with `d_A φ ∧ ψ` transported across
`k + 1 + l = k + l + 1`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.extDeriv (k + l) (φ.wedge ψ) =
      LinearEquiv.cast (R := ℝ) (M := A.Cochain)
        (Nat.succ_add k l) ((A.extDeriv k φ).wedge ψ) +
      (-1 : ℝ) ^ k • φ.wedge (A.extDeriv l ψ) := by
  -- Strong induction on the total degree `k + l`, using the `k = 0` and `l = 0` base cases and
  -- separating the `succ`/`succ` case by interior products in `extDeriv_wedge_succ_succ`.
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | _ n ih =>
    cases k with
    | zero => simpa using A.extDeriv_wedge_zero_left φ ψ
    | succ k =>
      cases l with
      | zero => rw [A.cast_cochain_self]; exact A.extDeriv_wedge_zero_right φ ψ
      | succ l =>
        exact A.extDeriv_wedge_succ_succ φ ψ
          (fun a ↦ ih (k + (l + 1)) (by omega) (φ.curryLeft a) ψ rfl)
          (fun a ↦ ih (k + 1 + l) (by omega) φ (ψ.curryLeft a) rfl)

/-- Pointwise evaluation form of the graded Leibniz rule `extDeriv_wedge`. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l)
    (x : M) (v : Fin (k + l + 1) → V x) :
    A.extDeriv (k + l) (φ.wedge ψ) x v =
      (A.extDeriv k φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add k l)) +
        (-1 : ℝ) ^ k • φ.wedge (A.extDeriv l ψ) x v := by
  simpa only [ContMDiffSection.alternating_add_apply, ContMDiffSection.cast_alternating_apply,
    ContMDiffSection.alternating_smul_apply] using
    DFunLike.congr_fun (congrArg (· x) (A.extDeriv_wedge φ ψ)) v

end Complex

end Basic

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

@[simp] theorem tangentCochainEquivSmoothForm_apply {k : ℕ}
    (φ : (tangent I M).Cochain k) (x : M) :
    (tangentCochainEquivSmoothForm I M k φ).val x = φ x := by
  rw [← SmoothForm.toContMDiffSection_apply]
  exact congrArg (· x) (SmoothForm.toContMDiffSection_ofContMDiffSection φ)

@[simp] theorem tangentCochainEquivSmoothForm_symm_apply {k : ℕ}
    (ψ : SmoothForm I M ℝ k) (x : M) : (tangentCochainEquivSmoothForm I M k).symm ψ x = ψ.val x :=
  SmoothForm.toContMDiffSection_apply ψ x

/-- `tangentCochainEquivSmoothForm` intertwines `ContMDiffSection.wedge` with `SmoothForm.wedge`. -/
@[simp] theorem tangentCochainEquivSmoothForm_wedge {k l : ℕ}
    (φ : (tangent I M).Cochain k) (ψ : (tangent I M).Cochain l) :
    tangentCochainEquivSmoothForm I M (k + l) (φ.wedge ψ) =
      SmoothForm.wedge (tangentCochainEquivSmoothForm I M k φ)
        (tangentCochainEquivSmoothForm I M l ψ) := by
  refine SmoothForm.toContMDiffSection_injective ?_
  ext x v
  simp only [SmoothForm.toContMDiffSection_apply, tangentCochainEquivSmoothForm_apply,
    ContMDiffSection.wedge_apply, SmoothForm.coe_wedge, RoughForm.wedge_def,
    RoughForm.wedgeWith_apply']

private theorem evalSection_removeNth_coeFn {m : ℕ} (φ : (tangent I M).Cochain (m + 1))
    (s : Fin (m + 2) → Cₛ^∞⟮I; E, TangentSpace I⟯) (i : Fin (m + 2)) :
    ⇑(φ.evalSection (i.removeNth s)) = fun y ↦ φ y (i.removeNth (s · y)) :=
  funext fun y ↦ by
    rw [ContMDiffSection.evalSection_apply]
    exact congrArg (φ y)
      (Fin.removeNth_comp (fun z : Cₛ^∞⟮I; E, TangentSpace I⟯ ↦ z y) i s).symm

private theorem cochainZeroEquiv_coeFn (φ : (tangent I M).Cochain 0)
    (v : ∀ y : M, Fin 0 → TangentSpace I y) :
    ⇑((tangent I M).cochainZeroEquiv φ) = fun y ↦ φ y (v y) :=
  funext fun y ↦ by
    rw [cochainZeroEquiv_apply]
    exact congrArg (φ y) (Subsingleton.elim _ _)

section T2

variable [T2Space M]

private theorem tangent_extDeriv_succ_evalSection_apply (m : ℕ)
    (φ : (tangent I M).Cochain (m + 1)) (s : Fin (m + 2) → Cₛ^∞⟮I; E, TangentSpace I⟯) (x : M) :
    ((tangent I M).extDeriv (m + 1) φ).evalSection s x =
      (∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val •
          mvfderiv I (fun y ↦ φ y (i.removeNth (s · y))) x (s i x)) -
        ∑ i : Fin (m + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j : ℕ) •
          φ x (Matrix.vecCons (mlieBracket I (s i.castSucc) (s j.succ) x)
            (j.removeNth (i.castSucc.removeNth (s · x)))) := by
  rw [(tangent I M).evalSection_extDeriv_succ, ← ContMDiffMap.evalAlgHom_apply ℝ x,
    map_add, sub_eq_add_neg]
  congr 1
  · rw [map_sum]
    simp_rw [map_zsmul, ContMDiffMap.evalAlgHom_apply]
    refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ i.val • ·) ?_
    rw [anchorDeriv_apply, tangent_anchor_apply, evalSection_removeNth_coeFn]
  · rw [map_sum, ← Finset.sum_neg_distrib]
    simp_rw [map_sum, map_zsmul, ← Finset.sum_neg_distrib, ContMDiffMap.evalAlgHom_apply,
      ContMDiffSection.evalSection_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_succ, mul_neg, mul_one, neg_zsmul]
    refine congrArg (- ·) (congrArg (_ • ·) (congrArg (φ x) ?_))
    dsimp only [Matrix.vecCons]
    rw [← Function.comp_def (fun z : Cₛ^∞⟮I; E, TangentSpace I⟯ ↦ z x), Fin.comp_cons,
      tangent_bracket_apply, Function.comp_def,
      ← Fin.removeNth_comp (fun z : Cₛ^∞⟮I; E, TangentSpace I⟯ ↦ z x) j,
      ← Fin.removeNth_comp (fun z : Cₛ^∞⟮I; E, TangentSpace I⟯ ↦ z x) i.castSucc s]

/-- On the tangent Lie algebroid `LieAlgebroid.tangent I M`, the Chevalley–Eilenberg differential
agrees pointwise with the manifold exterior derivative `mextDeriv`. -/
theorem tangent_extDeriv_apply (k : ℕ) (φ : (tangent I M).Cochain k) (x : M) :
    (tangent I M).extDeriv k φ x = mextDeriv (fun y ↦ φ y) x := by
  ext w
  obtain ⟨s, hw⟩ := ContMDiffSection.exists_fun_apply_eq (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) ∞ x w
  have hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (φ y)) x :=
    (φ.contMDiff x).mdifferentiableAt (by simp)
  have hs_diff : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (s i y : TangentBundle I M)) x :=
    fun i ↦ ((s i).contMDiff x).mdifferentiableAt (by simp)
  rw [← hw, ← ContMDiffSection.evalSection_apply]
  cases k with
  | zero =>
    rw [(tangent I M).evalSection_extDeriv_zero, anchorDeriv_apply, tangent_anchor_apply,
      mextDeriv_apply_vectorField_of_mlieBracket_eq_zero hφ hs_diff]
    · rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, val_zero, pow_zero, one_smul,
        cochainZeroEquiv_coeFn φ (fun y ↦ removeNth 0 (s · y))]
    · intro i j; obtain rfl : i = j := (by omega); simp
  | succ m =>
    rw [tangent_extDeriv_succ_evalSection_apply, mextDeriv_apply_vectorField hφ hs_diff]

/-- `tangentCochainEquivSmoothForm` intertwines the Chevalley–Eilenberg differential of
`LieAlgebroid.tangent I M` with the bundled de Rham exterior derivative `mextDerivₗ`. -/
@[simp] theorem tangentCochainEquivSmoothForm_extDeriv (k : ℕ) (φ : (tangent I M).Cochain k) :
    tangentCochainEquivSmoothForm I M (k + 1) ((tangent I M).extDeriv k φ) =
      mextDerivₗ I k (tangentCochainEquivSmoothForm I M k φ) := by
  refine SmoothForm.toContMDiffSection_injective ?_
  ext x w
  have hη : (tangentCochainEquivSmoothForm I M k φ).val = fun y ↦ φ y :=
    funext (tangentCochainEquivSmoothForm_apply φ)
  simp only [SmoothForm.toContMDiffSection_apply, tangentCochainEquivSmoothForm_apply,
    mextDerivₗ_apply, hη]
  exact DFunLike.congr_fun (tangent_extDeriv_apply k φ x) w

end T2

end Tangent

end TauCeti.LieAlgebroid
