/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.LieRinehartAlgebra.Cohomology
public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Tensoriality
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

For a finite-rank smooth Lie algebroid `A` over a finite-dimensional Hausdorff real manifold `M`,
degree-`k` cochains `A.Cochain k` are smooth sections of `x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`. Via
`A.cochainAlternatingEquiv`, `A.Cochain k` identifies with `C^∞(M, ℝ)`-multilinear alternating forms
on the Lie–Rinehart algebra `(ℝ, C^∞⟮I, M; ℝ⟯, A.Sections)`. Transporting `lieDeriv` and `d` yields
`A.lieDeriv`, `A.extDeriv`, the Chevalley–Eilenberg formula, `d_A ∘ d_A = 0`, `A.cochainComplex`,
`A.cohomology`, and Cartan's calculus.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, LMS Lecture Note Series
  213, Cambridge University Press (2005), §7.1.
* M. Crainic, R. L. Fernandes, and I. Marcut, *Lectures on Poisson Geometry*, AMS Graduate Studies
  in Mathematics 217 (2021).
-/

public section
noncomputable section

open Bundle CategoryTheory Manifold VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.LieAlgebroid
section Cochain
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- Degree-`k` Chevalley–Eilenberg cochains of a Lie algebroid `A`. -/
abbrev Cochain (_A : LieAlgebroid I F V) (k : ℕ) : Type _ :=
  Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯

/-- Degree-zero cochains of `A` are `C^∞(M, ℝ)`-linearly equivalent to `C^∞⟮I, M; ℝ⟯`. -/
def cochainZeroEquiv (A : LieAlgebroid I F V) : A.Cochain 0 ≃ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ :=
  ContMDiffSection.alternatingIsEmptyEquiv.trans ContMDiffSection.trivialEquiv

@[simp] theorem cochainZeroEquiv_apply (A : LieAlgebroid I F V) (η : A.Cochain 0) (x : M) :
    A.cochainZeroEquiv η x = η x 0 := by simp [cochainZeroEquiv]
@[simp] theorem cochainZeroEquiv_symm_apply (A : LieAlgebroid I F V) (f : C^∞⟮I, M; ℝ⟯) (x : M)
    (v : Fin 0 → V x) : A.cochainZeroEquiv.symm f x v = f x := by simp [cochainZeroEquiv]
end Cochain

section Complex
open TauCeti.LieRinehartAlgebra
open ContMDiffSection (interior scalarAlternatingEquiv)
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] (A : LieAlgebroid I F V)

/-- Smooth degree-`k` cochains of `A` are `C^∞(M, ℝ)`-linearly equivalent to alternating
`C^∞(M, ℝ)`-multilinear maps `A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯`. -/
def cochainAlternatingEquiv (k : ℕ) :
    A.Cochain k ≃ₗ[C^∞⟮I, M; ℝ⟯] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  scalarAlternatingEquiv.trans
    (AlternatingMap.domLCongr C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (Fin k) C^∞⟮I, M; ℝ⟯ A.sectionsEquiv.symm)

@[simp] theorem cochainAlternatingEquiv_apply {k : ℕ} (η : A.Cochain k) (s : Fin k → A.Sections)
    (x : M) : A.cochainAlternatingEquiv k η s x = η x (fun i ↦ A.sectionsEquiv (s i) x) := by
  simp [cochainAlternatingEquiv, AlternatingMap.domLCongr]
@[simp] theorem cochainAlternatingEquiv_symm_apply_sections {k : ℕ}
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.cochainAlternatingEquiv k).symm Φ x (fun i ↦ s i x) =
      Φ (fun i ↦ A.sectionsEquiv.symm (s i)) x := by simp [cochainAlternatingEquiv]

/-- Evaluate a cochain on smooth sections via `cochainAlternatingEquiv`. -/
theorem cochain_apply_sections {k : ℕ} (η : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    η x (fun i ↦ s i x) = A.cochainAlternatingEquiv k η (fun i ↦ A.sectionsEquiv.symm (s i)) x := by
  simp

@[simp] theorem cochainAlternatingEquiv_zero_apply (η : A.Cochain 0) (s : Fin 0 → A.Sections) :
    A.cochainAlternatingEquiv 0 η s = A.cochainZeroEquiv η := by
  ext x; simpa using congr_arg (η x) (Subsingleton.elim _ 0)

@[simp] theorem cochainAlternatingEquiv_interior {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (η : A.Cochain (k + 1)) : A.cochainAlternatingEquiv k (interior a η) =
      (A.cochainAlternatingEquiv (k + 1) η).curryLeft (A.sectionsEquiv.symm a) := by
  ext s x; simp only [cochainAlternatingEquiv_apply, ContMDiffSection.interior_apply,
    AlternatingMap.curryLeft_apply_apply]
  congr 1; funext i; refine Fin.cases ?_ (fun _ ↦ rfl) i; simp

/-- The Lie derivative of algebroid cochains along a smooth section of `A`. -/
def lieDeriv {k : ℕ} : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] A.Cochain k →ₗ[ℝ] A.Cochain k where
  toFun a := ((A.cochainAlternatingEquiv k).restrictScalars ℝ).symm.toLinearMap ∘ₗ
    Cohomology.lieDeriv ℝ (A.sectionsEquiv.symm a) ∘ₗ
    ((A.cochainAlternatingEquiv k).restrictScalars ℝ).toLinearMap
  map_add' _ _ := LinearMap.ext fun _ ↦ (A.cochainAlternatingEquiv k).injective <| by simp
  map_smul' c a := LinearMap.ext fun _ ↦ (A.cochainAlternatingEquiv k).injective <| by
    rw [RingHom.id_apply, LinearMapClass.map_smul_of_tower A.sectionsEquiv.symm c a]; simp

@[simp] theorem cochainAlternatingEquiv_lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.cochainAlternatingEquiv k (A.lieDeriv a η) =
      Cohomology.lieDeriv ℝ (A.sectionsEquiv.symm a) (A.cochainAlternatingEquiv k η) :=
  (A.cochainAlternatingEquiv k).apply_symm_apply _

/-- The Lie derivative commutes with degree casts on cochains. -/
theorem lieDeriv_cast {m n : ℕ} (h : m = n) (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain m) :
    A.lieDeriv a (LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) h η) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) h (A.lieDeriv a η) := by cases h; rfl

/-- Evaluation of the Lie derivative of a `k`-cochain on global smooth sections. -/
theorem lieDeriv_apply_sections {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.lieDeriv a η) x (fun i ↦ s i x) = A.anchorDeriv a (scalarAlternatingEquiv η s) x -
        ∑ i : Fin k, η x (fun j ↦ Function.update s i (A.bracket a (s i)) j x) := by
  rw [A.cochain_apply_sections, A.cochainAlternatingEquiv_lieDeriv, Cohomology.lieDeriv_apply,
    ContMDiffMap.coe_sub, ContMDiffMap.coe_sum, Pi.sub_apply, Finset.sum_apply, Sections.lie_def,
    LinearEquiv.apply_symm_apply]
  refine congr_arg₂ (· - ·) (by congr 2; ext y; simp) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [cochainAlternatingEquiv_apply]; congr 1; funext j; by_cases hij : j = i <;> simp [hij]

@[simp] theorem cochainZeroEquiv_lieDeriv (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain 0) :
    A.cochainZeroEquiv (A.lieDeriv a η) = A.anchorDeriv a (A.cochainZeroEquiv η) := by
  rw [← A.cochainAlternatingEquiv_zero_apply (A.lieDeriv a η) ![],
    A.cochainAlternatingEquiv_lieDeriv, Cohomology.lieDeriv_apply]; simp [Sections.lie_def]

/-- Product rule for the Lie derivative on a scalar multiple `f • η`. -/
@[simp] theorem lieDeriv_smul {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) :
    A.lieDeriv a (f • η) = f • A.lieDeriv a η + A.anchorDeriv a f • η :=
  (A.cochainAlternatingEquiv k).injective <| by simp [map_add, map_smul, Sections.lie_def]

/-- The Chevalley–Eilenberg differential `d_A : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1)` of `A`. -/
def extDeriv (k : ℕ) : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1) :=
  ((A.cochainAlternatingEquiv (k + 1)).restrictScalars ℝ).symm.toLinearMap ∘ₗ
    Cohomology.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k ∘ₗ
    ((A.cochainAlternatingEquiv k).restrictScalars ℝ).toLinearMap

@[simp] theorem cochainAlternatingEquiv_extDeriv (k : ℕ) (η : A.Cochain k) :
    A.cochainAlternatingEquiv (k + 1) (A.extDeriv k η) =
      Cohomology.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k (A.cochainAlternatingEquiv k η) :=
  (A.cochainAlternatingEquiv (k + 1)).apply_symm_apply _

/-- The Chevalley–Eilenberg differential commutes with degree casts on cochains. -/
theorem extDeriv_cast {m n : ℕ} (h : m = n) (η : A.Cochain m) :
    A.extDeriv n (LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) h η) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) (congrArg (· + 1) h)
        (A.extDeriv m η) := by cases h; rfl

@[simp] theorem extDeriv_zero_apply_section (η : A.Cochain 0) (a : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv 0 η) x ![a x] = A.anchorDeriv a (A.cochainZeroEquiv η) x := by
  have htup : (![a x] : Fin 1 → V x) = fun i ↦ (![a] i) x := funext fun i ↦ by fin_cases i; rfl
  rw [htup, A.cochain_apply_sections, A.cochainAlternatingEquiv_extDeriv,
    Cohomology.d_zero_apply, Matrix.cons_val_zero, A.cochainAlternatingEquiv_zero_apply,
    Sections.lie_def, LinearEquiv.apply_symm_apply]

/-- Pointwise degree-zero formula `d_A f = ρ*(df)`. -/
theorem extDeriv_zero_apply (η : A.Cochain 0) (x : M) (v : V x) :
    (A.extDeriv 0 η) x ![v] = mvfderiv I (A.cochainZeroEquiv η) x (A.anchor x v) := by
  obtain ⟨a, hax⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (V := V) x v
  rw [ContMDiffSection.evalLinearMap_apply] at hax
  rw [← hax, A.extDeriv_zero_apply_section, anchorDeriv_apply]

/-- **The Chevalley–Eilenberg formula** for `A.extDeriv` in positive degree on smooth sections. -/
theorem extDeriv_succ_apply_sections {k : ℕ} (η : A.Cochain (k + 1))
    (s : Fin (k + 2) → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv (k + 1) η) x (fun i ↦ s i x) = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        A.anchorDeriv (s i) (scalarAlternatingEquiv η (i.removeNth s)) x +
      ∑ i : Fin (k + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) • η x (Matrix.vecCons
        (A.bracket (s i.castSucc) (s j.succ) x)
        (j.removeNth (i.castSucc.removeNth (fun r ↦ s r x)))) := by
  rw [A.cochain_apply_sections, A.cochainAlternatingEquiv_extDeriv, Cohomology.d_succ_apply,
    ContMDiffMap.coe_add, ContMDiffMap.coe_sum, ContMDiffMap.coe_sum, Pi.add_apply,
    Finset.sum_apply, Finset.sum_apply]
  have hz (c : ℤ) (g : C^∞⟮I, M; ℝ⟯) : (c • g) x = c • g x :=
    map_zsmul (ContMDiffMap.evalRingHom x) c g
  refine congr_arg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun i _ ↦ ?_)
  · have hrem : A.cochainAlternatingEquiv (k + 1) η
        (i.removeNth fun r ↦ A.sectionsEquiv.symm (s r)) =
        scalarAlternatingEquiv η (i.removeNth s) := by ext y; simp [Fin.removeNth]
    rw [hz, Sections.lie_def, LinearEquiv.apply_symm_apply, hrem]
  · rw [ContMDiffMap.coe_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hz, cochainAlternatingEquiv_apply]; congr 2; funext r
    refine Fin.cases (by simp) (fun _ ↦ by simp [Fin.removeNth]) r

/-- The algebroid Chevalley–Eilenberg differential squares to zero in every degree. -/
@[simp] theorem extDeriv_extDeriv (k : ℕ) (η : A.Cochain k) :
    A.extDeriv (k + 1) (A.extDeriv k η) = 0 :=
  (A.cochainAlternatingEquiv (k + 2)).injective (by simp)

/-- The algebroid differential squares to zero as a composite of linear maps. -/
theorem extDeriv_comp_extDeriv (k : ℕ) : A.extDeriv (k + 1) ∘ₗ A.extDeriv k = 0 :=
  LinearMap.ext (A.extDeriv_extDeriv k)

/-- The Chevalley–Eilenberg cochain complex of a Lie algebroid `A` in `ModuleCat ℝ`. -/
def cochainComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (A.Cochain k)) (fun k ↦ ModuleCat.ofHom (A.extDeriv k))
    fun k ↦ by rw [← ModuleCat.ofHom_comp, A.extDeriv_comp_extDeriv, ModuleCat.ofHom_zero]

/-- The degree-`k` term of `A.cochainComplex` is the `ℝ`-module `A.Cochain k`. -/
def cochainComplexXIso (k : ℕ) : A.cochainComplex.X k ≅ ModuleCat.of ℝ (A.Cochain k) := Iso.refl _

/-- Under the canonical identifications of terms, the differential of `A.cochainComplex` is
`A.extDeriv`. -/
@[reassoc] theorem cochainComplex_d (k : ℕ) :
    A.cochainComplex.d k (k + 1) ≫ (A.cochainComplexXIso (k + 1)).hom =
      (A.cochainComplexXIso k).hom ≫ ModuleCat.ofHom (A.extDeriv k) := by
  simp [cochainComplex, cochainComplexXIso, CochainComplex.of_d]

/-- The differential of `A.cochainComplex`, evaluated on an element. -/
theorem cochainComplex_d_apply (k : ℕ) (η : A.cochainComplex.X k) :
    A.cochainComplex.d k (k + 1) η =
      (A.cochainComplexXIso (k + 1)).inv (A.extDeriv k ((A.cochainComplexXIso k).hom η)) := by
  rw [(Iso.eq_comp_inv _).mpr (A.cochainComplex_d k)]; rfl

/-- The degree-`k` Lie algebroid cohomology `H^k(A)` as an `ℝ`-module. -/
abbrev cohomology (k : ℕ) : ModuleCat ℝ := A.cochainComplex.homology k

@[simp] theorem interior_extDeriv_zero (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain 0) :
    interior a (A.extDeriv 0 η) = A.lieDeriv a η :=
  (A.cochainAlternatingEquiv 0).injective (by simp)

/-- **Cartan's magic formula** for Lie algebroid cochains: `ι_a (d_A η) = L_a η - d_A (ι_a η)`. -/
theorem interior_extDeriv_succ {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    interior a (A.extDeriv (k + 1) η) = A.lieDeriv a η - A.extDeriv k (interior a η) :=
  (A.cochainAlternatingEquiv (k + 1)).injective (by simp [map_sub])

/-- Explicit Chevalley–Eilenberg formula for a `1`-cochain. -/
theorem extDeriv_one_apply_sections (α : A.Cochain 1) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv 1 α) x ![a x, b x] = A.anchorDeriv a (scalarAlternatingEquiv α ![b]) x -
      A.anchorDeriv b (scalarAlternatingEquiv α ![a]) x - α x ![A.bracket a b x] := by
  have hb : (![b x] : Fin 1 → V x) = fun i ↦ (![b] i) x := funext fun i ↦ by fin_cases i; rfl
  have hco : A.cochainZeroEquiv (interior a α) = scalarAlternatingEquiv α ![a] := by
    ext y; simpa using congr_arg (α y) (funext fun i ↦ by fin_cases i; rfl)
  change (A.extDeriv 1 α) x (Matrix.vecCons (a x) ![b x]) = _
  rw [← ContMDiffSection.interior_apply a, A.interior_extDeriv_succ, ContMDiffSection.coe_sub,
    Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hb, A.lieDeriv_apply_sections a α ![b] x,
    ← hb, A.extDeriv_zero_apply_section, Fin.sum_univ_one, hco]
  rw [show (fun j : Fin 1 ↦ Function.update ![b] 0 (A.bracket a (![b] 0)) j x) =
    ![A.bracket a b x] from funext fun i ↦ by fin_cases i; rfl]; ring

/-- Cartan's magic formula written for `L_a η = ι_a (d_A η) + d_A (ι_a η)`. -/
theorem lieDeriv_eq_interior_extDeriv_add {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    A.lieDeriv a η = interior a (A.extDeriv (k + 1) η) + A.extDeriv k (interior a η) := by
  rw [A.interior_extDeriv_succ, sub_add_cancel]

/-- Commutator of Lie derivative and interior product: `ι_b (L_a η) = L_a (ι_b η) - ι_{[a,b]} η`. -/
theorem interior_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    interior b (A.lieDeriv a η) = A.lieDeriv a (interior b η) - interior (A.bracket a b) η :=
  (A.cochainAlternatingEquiv k).injective <| by simp [map_sub, Cohomology.curryLeft_lieDeriv]

/-- The Lie derivative is a Lie algebra representation: `L_{[a, b]} = L_a ∘ L_b - L_b ∘ L_a`. -/
theorem lieDeriv_bracket {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.lieDeriv (A.bracket a b) η = A.lieDeriv a (A.lieDeriv b η) - A.lieDeriv b (A.lieDeriv a η) :=
  (A.cochainAlternatingEquiv k).injective <| by simp [map_sub, Cohomology.lieDeriv_lie]

/-- The Lie derivative commutes with the Chevalley–Eilenberg differential:
`L_a (d_A η) = d_A (L_a η)`. -/
@[simp] theorem lieDeriv_extDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.lieDeriv a (A.extDeriv k η) = A.extDeriv k (A.lieDeriv a η) :=
  (A.cochainAlternatingEquiv (k + 1)).injective (by simp)
end Complex
end TauCeti.LieAlgebroid
