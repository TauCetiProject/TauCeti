/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.LieRinehartAlgebra.Cohomology
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

For a finite-rank smooth Lie algebroid `A` over a finite-dimensional Hausdorff real manifold `M`,
degree-`k` cochains `A.Cochain k` are smooth sections of `x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`. Via
`A.cochainAlternatingEquiv`, `A.Cochain k` identifies with `C^∞(M, ℝ)`-multilinear alternating forms
on the Lie–Rinehart algebra `(ℝ, C^∞⟮I, M; ℝ⟯, A.Sections)`. Transporting `lieDeriv` and `d` yields
`A.lieDeriv`, `A.extDeriv`, the Chevalley–Eilenberg formula, `d_A ∘ d_A = 0`, `A.cochainComplex`,
`A.cohomology`, Cartan's calculus, the graded Leibniz rule on `ContMDiffSection.wedge`, and
comparison with the de Rham differential on `LieAlgebroid.tangent I M`.

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
@[simp] theorem cochainZeroEquiv_symm_apply (A : LieAlgebroid I F V) (f : C^∞⟮I, M; ℝ⟯)
    (x : M) (v : Fin 0 → V x) : A.cochainZeroEquiv.symm f x v = f x := by simp [cochainZeroEquiv]

private lemma cochainZeroEquiv_eq (A : LieAlgebroid I F V) (ξ : A.Cochain 0) :
    ContMDiffSection.trivialEquiv (ContMDiffSection.alternatingIsEmptyEquiv ξ) =
      A.cochainZeroEquiv ξ := by rw [cochainZeroEquiv, LinearEquiv.trans_apply]
end Cochain

section Complex
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] (A : LieAlgebroid I F V)

/-- Smooth degree-`k` cochains of `A` are `C^∞(M, ℝ)`-linearly equivalent to alternating
`C^∞(M, ℝ)`-multilinear maps `A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯`. -/
def cochainAlternatingEquiv (k : ℕ) :
    A.Cochain k ≃ₗ[C^∞⟮I, M; ℝ⟯] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  ContMDiffSection.scalarAlternatingEquiv.trans
    (AlternatingMap.domLCongr C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (Fin k) C^∞⟮I, M; ℝ⟯ A.sectionsEquiv.symm)

@[simp] theorem cochainAlternatingEquiv_apply {k : ℕ} (η : A.Cochain k) (s : Fin k → A.Sections)
    (x : M) : A.cochainAlternatingEquiv k η s x = η x (fun i ↦ A.sectionsEquiv (s i) x) := by
  simp [cochainAlternatingEquiv, AlternatingMap.domLCongr]
@[simp] theorem cochainAlternatingEquiv_symm_apply_sections {k : ℕ}
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.cochainAlternatingEquiv k).symm Φ x (fun i ↦ s i x) =
      Φ (fun i ↦ A.sectionsEquiv.symm (s i)) x := by
  simp [cochainAlternatingEquiv, AlternatingMap.domLCongr]

/-- Evaluate a cochain on smooth sections via `cochainAlternatingEquiv`. -/
theorem cochain_apply_sections {k : ℕ} (η : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    η x (fun i ↦ s i x) =
      A.cochainAlternatingEquiv k η (fun i ↦ A.sectionsEquiv.symm (s i)) x := by simp

@[simp] theorem cochainAlternatingEquiv_zero_apply (η : A.Cochain 0) (s : Fin 0 → A.Sections) :
    A.cochainAlternatingEquiv 0 η s = A.cochainZeroEquiv η := by
  ext x; simpa using congr_arg (η x) (Subsingleton.elim _ 0)

@[simp] theorem cochainAlternatingEquiv_interior {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (η : A.Cochain (k + 1)) :
    A.cochainAlternatingEquiv k (ContMDiffSection.interior a η) =
      (A.cochainAlternatingEquiv (k + 1) η).curryLeft (A.sectionsEquiv.symm a) := by
  ext s x; simp only [cochainAlternatingEquiv_apply, ContMDiffSection.interior_apply,
    AlternatingMap.curryLeft_apply_apply]
  congr 1; funext i; refine Fin.cases ?_ (fun _ ↦ rfl) i; simp

/-- The Lie derivative of algebroid cochains along a smooth section of `A`. -/
def lieDeriv {k : ℕ} : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] A.Cochain k →ₗ[ℝ] A.Cochain k where
  toFun a := ((A.cochainAlternatingEquiv k).restrictScalars ℝ).symm.toLinearMap ∘ₗ
    TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv ℝ (A.sectionsEquiv.symm a) ∘ₗ
    ((A.cochainAlternatingEquiv k).restrictScalars ℝ).toLinearMap
  map_add' _ _ := LinearMap.ext fun _ ↦ (A.cochainAlternatingEquiv k).injective <| by simp
  map_smul' c a := LinearMap.ext fun _ ↦ (A.cochainAlternatingEquiv k).injective <| by
    rw [RingHom.id_apply, LinearMapClass.map_smul_of_tower A.sectionsEquiv.symm c a]; simp

@[simp] theorem cochainAlternatingEquiv_lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.cochainAlternatingEquiv k (A.lieDeriv a η) =
      TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv ℝ (A.sectionsEquiv.symm a)
        (A.cochainAlternatingEquiv k η) := by
  rw [lieDeriv]; exact (A.cochainAlternatingEquiv k).apply_symm_apply _

/-- The Lie derivative commutes with degree casts on cochains. -/
theorem lieDeriv_cast {m n : ℕ} (h : m = n) (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain m) :
    A.lieDeriv a (LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) h η) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) h (A.lieDeriv a η) := by cases h; rfl

/-- Evaluation of the Lie derivative of a `k`-cochain on global smooth sections. -/
theorem lieDeriv_apply_sections {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.lieDeriv a η) x (fun i ↦ s i x) =
      A.anchorDeriv a (ContMDiffSection.scalarAlternatingEquiv η s) x -
        ∑ i : Fin k, η x (fun j ↦ Function.update s i (A.bracket a (s i)) j x) := by
  rw [A.cochain_apply_sections, A.cochainAlternatingEquiv_lieDeriv,
    TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv_apply, ContMDiffMap.coe_sub,
    ContMDiffMap.coe_sum, Pi.sub_apply, Finset.sum_apply, Sections.lie_def,
    LinearEquiv.apply_symm_apply]
  congr 1
  · congr 2; ext y; simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cochainAlternatingEquiv_apply]; congr 1; funext j; by_cases hij : j = i <;> simp [hij]

@[simp] theorem cochainZeroEquiv_lieDeriv (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain 0) :
    A.cochainZeroEquiv (A.lieDeriv a η) = A.anchorDeriv a (A.cochainZeroEquiv η) := by
  rw [← A.cochainAlternatingEquiv_zero_apply (A.lieDeriv a η) ![],
    A.cochainAlternatingEquiv_lieDeriv, TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv_apply,
    Finset.univ_eq_empty, Finset.sum_empty, sub_zero, A.cochainAlternatingEquiv_zero_apply,
    Sections.lie_def, LinearEquiv.apply_symm_apply]

/-- Product rule for the Lie derivative on a scalar multiple `f • η`. -/
@[simp] theorem lieDeriv_smul {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) :
    A.lieDeriv a (f • η) = f • A.lieDeriv a η + A.anchorDeriv a f • η := by
  refine (A.cochainAlternatingEquiv k).injective ?_; simp [map_add, map_smul, Sections.lie_def]

/-- The Chevalley–Eilenberg differential `d_A : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1)` of `A`. -/
def extDeriv (k : ℕ) : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1) :=
  ((A.cochainAlternatingEquiv (k + 1)).restrictScalars ℝ).symm.toLinearMap ∘ₗ
    TauCeti.LieRinehartAlgebra.Cohomology.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k ∘ₗ
    ((A.cochainAlternatingEquiv k).restrictScalars ℝ).toLinearMap

@[simp] theorem cochainAlternatingEquiv_extDeriv (k : ℕ) (η : A.Cochain k) :
    A.cochainAlternatingEquiv (k + 1) (A.extDeriv k η) =
      TauCeti.LieRinehartAlgebra.Cohomology.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k
        (A.cochainAlternatingEquiv k η) := by
  rw [extDeriv]; exact (A.cochainAlternatingEquiv (k + 1)).apply_symm_apply _

/-- The Chevalley–Eilenberg differential commutes with degree casts on cochains. -/
theorem extDeriv_cast {m n : ℕ} (h : m = n) (η : A.Cochain m) :
    A.extDeriv n (LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) h η) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) (congrArg (· + 1) h)
        (A.extDeriv m η) := by cases h; rfl

@[simp] theorem extDeriv_zero_apply_section (η : A.Cochain 0) (a : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv 0 η) x ![a x] = A.anchorDeriv a (A.cochainZeroEquiv η) x := by
  have htup : (![a x] : Fin 1 → V x) = fun i ↦ (![a] i) x := funext fun i ↦ by fin_cases i; rfl
  rw [htup, A.cochain_apply_sections, A.cochainAlternatingEquiv_extDeriv,
    TauCeti.LieRinehartAlgebra.Cohomology.d_zero_apply, Matrix.cons_val_zero,
    A.cochainAlternatingEquiv_zero_apply, Sections.lie_def, LinearEquiv.apply_symm_apply]

/-- Pointwise degree-zero formula `d_A f = ρ*(df)`. -/
theorem extDeriv_zero_apply (η : A.Cochain 0) (x : M) (v : V x) :
    (A.extDeriv 0 η) x ![v] = mvfderiv I (A.cochainZeroEquiv η) x (A.anchor x v) := by
  obtain ⟨a, hax⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (V := V) x v
  rw [ContMDiffSection.evalLinearMap_apply] at hax
  rw [← hax, A.extDeriv_zero_apply_section, anchorDeriv_apply]

/-- **The Chevalley–Eilenberg formula** for `A.extDeriv` in positive degree on smooth sections. -/
theorem extDeriv_succ_apply_sections {k : ℕ} (η : A.Cochain (k + 1))
    (s : Fin (k + 2) → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv (k + 1) η) x (fun i ↦ s i x) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          A.anchorDeriv (s i) (ContMDiffSection.scalarAlternatingEquiv η (i.removeNth s)) x +
        ∑ i : Fin (k + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          η x (Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ) x)
            (j.removeNth (i.castSucc.removeNth (fun r ↦ s r x)))) := by
  rw [A.cochain_apply_sections, A.cochainAlternatingEquiv_extDeriv,
    TauCeti.LieRinehartAlgebra.Cohomology.d_succ_apply, ContMDiffMap.coe_add, ContMDiffMap.coe_sum,
    ContMDiffMap.coe_sum, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  have hz (c : ℤ) (g : C^∞⟮I, M; ℝ⟯) : (c • g) x = c • g x :=
    map_zsmul (ContMDiffMap.evalRingHom x) c g
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hrem : A.cochainAlternatingEquiv (k + 1) η
          (i.removeNth fun r ↦ A.sectionsEquiv.symm (s r)) =
        ContMDiffSection.scalarAlternatingEquiv η (i.removeNth s) := by ext y; simp [Fin.removeNth]
    rw [hz, Sections.lie_def, LinearEquiv.apply_symm_apply, hrem]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContMDiffMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hz, cochainAlternatingEquiv_apply]
    congr 2; funext r; refine Fin.cases (by simp) (fun _ ↦ by simp [Fin.removeNth]) r

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
    ContMDiffSection.interior a (A.extDeriv 0 η) = A.lieDeriv a η :=
  (A.cochainAlternatingEquiv 0).injective (by simp)

/-- **Cartan's magic formula** for Lie algebroid cochains: `ι_a (d_A η) = L_a η - d_A (ι_a η)`. -/
theorem interior_extDeriv_succ {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    ContMDiffSection.interior a (A.extDeriv (k + 1) η) =
      A.lieDeriv a η - A.extDeriv k (ContMDiffSection.interior a η) :=
  (A.cochainAlternatingEquiv (k + 1)).injective (by simp [map_sub])

/-- Explicit Chevalley–Eilenberg formula for a `1`-cochain. -/
theorem extDeriv_one_apply_sections (α : A.Cochain 1) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv 1 α) x ![a x, b x] =
      A.anchorDeriv a (ContMDiffSection.scalarAlternatingEquiv α ![b]) x -
        A.anchorDeriv b (ContMDiffSection.scalarAlternatingEquiv α ![a]) x -
        α x ![A.bracket a b x] := by
  have hb : (![b x] : Fin 1 → V x) = fun i ↦ (![b] i) x := funext fun i ↦ by fin_cases i; rfl
  have hco : A.cochainZeroEquiv (ContMDiffSection.interior a α) =
      ContMDiffSection.scalarAlternatingEquiv α ![a] := by
    ext y; simpa [ContMDiffSection.interior_apply] using
      congr_arg (α y) (funext fun i ↦ by fin_cases i; rfl)
  change (A.extDeriv 1 α) x (Matrix.vecCons (a x) ![b x]) = _
  rw [← ContMDiffSection.interior_apply a, A.interior_extDeriv_succ, ContMDiffSection.coe_sub,
    Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hb, A.lieDeriv_apply_sections a α ![b] x,
    ← hb, A.extDeriv_zero_apply_section, Fin.sum_univ_one, hco]
  have hupd : (fun j : Fin 1 ↦ Function.update ![b] 0 (A.bracket a (![b] 0)) j x) =
      ![A.bracket a b x] := funext fun i ↦ by fin_cases i; rfl
  rw [hupd]; ring

/-- Cartan's magic formula written for `L_a η = ι_a (d_A η) + d_A (ι_a η)`. -/
theorem lieDeriv_eq_interior_extDeriv_add {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    A.lieDeriv a η =
      ContMDiffSection.interior a (A.extDeriv (k + 1) η) +
        A.extDeriv k (ContMDiffSection.interior a η) := by
  rw [A.interior_extDeriv_succ, sub_add_cancel]

omit [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
private lemma sectionsEquiv_symm_bracket (a b : Cₛ^∞⟮I; F, V⟯) :
    A.sectionsEquiv.symm (A.bracket a b) = ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ :=
  A.sectionsEquiv.injective (by simp)

/-- Commutator of Lie derivative and interior product: `ι_b (L_a η) = L_a (ι_b η) - ι_{[a,b]} η`. -/
theorem interior_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    ContMDiffSection.interior b (A.lieDeriv a η) =
      A.lieDeriv a (ContMDiffSection.interior b η) -
        ContMDiffSection.interior (A.bracket a b) η :=
  (A.cochainAlternatingEquiv k).injective <| by
    simp [map_sub, A.sectionsEquiv_symm_bracket,
      TauCeti.LieRinehartAlgebra.Cohomology.curryLeft_lieDeriv]

/-- The Lie derivative is a Lie algebra representation: `L_{[a, b]} = L_a ∘ L_b - L_b ∘ L_a`. -/
theorem lieDeriv_bracket {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.lieDeriv (A.bracket a b) η =
      A.lieDeriv a (A.lieDeriv b η) - A.lieDeriv b (A.lieDeriv a η) :=
  (A.cochainAlternatingEquiv k).injective <| by
    simp [map_sub, A.sectionsEquiv_symm_bracket, TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv_lie]

/-- The Lie derivative commutes with the Chevalley–Eilenberg differential:
`L_a (d_A η) = d_A (L_a η)`. -/
@[simp] theorem lieDeriv_extDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.lieDeriv a (A.extDeriv k η) = A.extDeriv k (A.lieDeriv a η) :=
  (A.cochainAlternatingEquiv (k + 1)).injective (by simp)

/-- The Lie derivative is an ungraded derivation of `ContMDiffSection.wedge`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.lieDeriv a (ContMDiffSection.wedge φ ψ) =
      ContMDiffSection.wedge (A.lieDeriv a φ) ψ +
        ContMDiffSection.wedge φ (A.lieDeriv a ψ) := by
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | ind n ih =>
    rcases k with _ | k
    · simp only [ContMDiffSection.wedge_zero_left, A.cochainZeroEquiv_eq, A.lieDeriv_cast,
        A.lieDeriv_smul, map_add, A.cochainZeroEquiv_lieDeriv]; exact add_comm _ _
    rcases l with _ | l
    · simp only [ContMDiffSection.wedge_zero_right, A.cochainZeroEquiv_eq, A.lieDeriv_cast,
        A.lieDeriv_smul, map_add, A.cochainZeroEquiv_lieDeriv]
    refine ContMDiffSection.ext_of_interior (k := k + 1 + l) fun b ↦ ?_
    have ih₁ := ih (k + (l + 1)) (by omega) (ContMDiffSection.interior b φ) ψ rfl
    have ih₂ := ih ((k + 1) + l) (by omega) φ (ContMDiffSection.interior b ψ) rfl
    simp only [A.interior_lieDeriv, ContMDiffSection.interior_wedge, map_add, map_sub, map_smul,
      LinearMap.sub_apply, A.lieDeriv_cast, ih₁, ih₂]; module

/-- Scalar derivation rule for `A.extDeriv` in terms of `ContMDiffSection.wedge`. -/
theorem extDeriv_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) :
    A.extDeriv k (f • η) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain) (Nat.add_comm 1 k)
        (ContMDiffSection.wedge (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η) +
        f • A.extDeriv k η := by
  induction k with
  | zero =>
    ext x v
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    have hcast : ((![v 0] : Fin 1 → V x) ∘ Fin.cast (Nat.add_comm 1 0)) ∘
        Fin.cast (Nat.add_zero 1).symm = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hv, ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      ContMDiffSection.alternating_cast_apply, ContMDiffSection.smul_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, A.extDeriv_zero_apply,
      A.extDeriv_zero_apply, map_smul, smul_eq_mul, ContMDiffMap.coe_mul,
      ContMDiffSection.wedge_apply_zero_right, ← A.cochainZeroEquiv_apply η x, hcast,
      A.extDeriv_zero_apply, LinearEquiv.apply_symm_apply,
      mvfderiv_mul (f.contMDiff.mdifferentiableAt (by simp))
        ((A.cochainZeroEquiv η).contMDiff.mdifferentiableAt (by simp))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]; ring
  | succ k ih =>
    refine ContMDiffSection.ext_of_interior fun a ↦ ?_
    simp only [A.interior_extDeriv_succ, A.lieDeriv_smul, map_add, ContMDiffSection.interior_cast,
      ContMDiffSection.interior_wedge (k := 0) a (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η,
      A.interior_extDeriv_zero, ContMDiffSection.wedge_zero_left, A.cochainZeroEquiv_eq,
      A.cochainZeroEquiv_lieDeriv, LinearEquiv.apply_symm_apply,
      LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯), ih (ContMDiffSection.interior a η),
      smul_sub]
    simp only [LinearEquiv.cast_apply, cast_cast, cast_eq]; module

/-- Pointwise scalar derivation rule for `A.extDeriv` in terms of `ContMDiffSection.wedge`. -/
theorem extDeriv_smul_apply {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) (x : M)
    (v : Fin (k + 1) → V x) :
    (A.extDeriv k (f • η)) x v =
      ContMDiffSection.wedge (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η x
          (v ∘ Fin.cast (Nat.add_comm 1 k)) + f x * (A.extDeriv k η) x v := by
  rw [A.extDeriv_smul, ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContMDiffSection.alternating_cast_apply, ContMDiffSection.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]

private lemma extDeriv_wedge_zero_left {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l) :
    A.extDeriv (0 + l) (ContMDiffSection.wedge φ ψ) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show 0 + 1 + l = 0 + l + 1 by omega)
        (ContMDiffSection.wedge (A.extDeriv 0 φ) ψ) +
        (-1 : ℝ) ^ 0 • LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (show 0 + (l + 1) = 0 + l + 1 by omega)
          (ContMDiffSection.wedge φ (A.extDeriv l ψ)) := by
  simp only [ContMDiffSection.wedge_zero_left, A.cochainZeroEquiv_eq, A.extDeriv_cast,
    A.extDeriv_smul, LinearEquiv.symm_apply_apply, map_add, pow_zero, one_smul]
  simp only [LinearEquiv.cast_apply, cast_cast]

private lemma extDeriv_wedge_zero_right {k : ℕ} (φ : A.Cochain (k + 1)) (ψ : A.Cochain 0) :
    A.extDeriv (k + 1 + 0) (ContMDiffSection.wedge φ ψ) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show k + 1 + 1 + 0 = k + 1 + 0 + 1 by omega)
        (ContMDiffSection.wedge (A.extDeriv (k + 1) φ) ψ) +
        (-1 : ℝ) ^ (k + 1) • LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (show k + 1 + (0 + 1) = k + 1 + 0 + 1 by omega)
          (ContMDiffSection.wedge φ (A.extDeriv 0 ψ)) := by
  have hsmul_sq (ξ : A.Cochain (k + 1 + 0 + 1)) :
      (-1 : ℝ) ^ (k + 1) • (-1 : ℝ) ^ ((k + 1) * (0 + 1)) • ξ = ξ := by
    rw [smul_smul, zero_add, mul_one, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_smul]
  simp only [ContMDiffSection.wedge_zero_right, A.cochainZeroEquiv_eq, A.extDeriv_cast,
    A.extDeriv_smul, LinearEquiv.symm_apply_apply, ContMDiffSection.wedge_comm φ (A.extDeriv 0 ψ),
    LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯)]
  simp only [LinearEquiv.cast_apply, cast_cast, hsmul_sq]; exact add_comm _ _

/-- **Graded Leibniz rule** for `A.extDeriv` with respect to `ContMDiffSection.wedge`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.extDeriv (k + l) (ContMDiffSection.wedge φ ψ) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
        (show k + 1 + l = k + l + 1 by omega)
        (ContMDiffSection.wedge (A.extDeriv k φ) ψ) +
        (-1 : ℝ) ^ k • LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := A.Cochain)
          (show k + (l + 1) = k + l + 1 by omega)
          (ContMDiffSection.wedge φ (A.extDeriv l ψ)) := by
  obtain ⟨n, hn⟩ : ∃ n, k + l = n := ⟨k + l, rfl⟩
  induction n using Nat.strong_induction_on generalizing k l with
  | ind n ih =>
    rcases k with _ | k
    · exact A.extDeriv_wedge_zero_left φ ψ
    rcases l with _ | l
    · exact A.extDeriv_wedge_zero_right φ ψ
    refine ContMDiffSection.ext_of_interior (k := k + 1 + l + 1) fun a ↦ ?_
    have ih₁ := ih (k + (l + 1)) (by omega) (ContMDiffSection.interior a φ) ψ rfl
    have ih₂ := ih ((k + 1) + l) (by omega) φ (ContMDiffSection.interior a ψ) rfl
    have hsmul_add (c : ℝ) (x y : A.Cochain (k + 1 + l + 1)) := smul_add c x y
    have hsmul_sub (c : ℝ) (x y : A.Cochain (k + 1 + l + 1)) := smul_sub c x y
    have hsmul_sq (ξ : A.Cochain (k + 1 + l + 1)) :
        (-1 : ℝ) ^ (k + 1) • (-1 : ℝ) ^ (k + 1) • ξ = ξ := by
      rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_smul]
    have hpow₁ : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ, mul_neg, mul_one]
    have hpow₂ : (-1 : ℝ) ^ (k + 1 + 1) = (-1 : ℝ) ^ k := by rw [pow_succ, pow_succ]; ring
    refine (A.interior_extDeriv_succ (k := k + 1 + l) a (ContMDiffSection.wedge φ ψ)).trans ?_
    simp only [A.lieDeriv_wedge a φ ψ, ContMDiffSection.interior_wedge a φ ψ,
      ContMDiffSection.interior_cast, ContMDiffSection.interior_wedge a (A.extDeriv (k + 1) φ) ψ,
      ContMDiffSection.interior_wedge a φ (A.extDeriv (l + 1) ψ), A.interior_extDeriv_succ,
      A.extDeriv_cast, map_add, map_sub, map_smul, LinearMap.sub_apply,
      LinearMapClass.map_smul_of_tower (S := C^∞⟮I, M; ℝ⟯), ih₁, ih₂]
    simp only [LinearEquiv.cast_apply, cast_cast, cast_eq, hsmul_add, hsmul_sub, hsmul_sq]
    simp only [hpow₁, hpow₂]; module

/-- Pointwise **graded Leibniz rule** for `A.extDeriv` with respect to `ContMDiffSection.wedge`. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l)
    (x : M) (v : Fin (k + l + 1) → V x) :
    (A.extDeriv (k + l) (ContMDiffSection.wedge φ ψ)) x v =
      ContMDiffSection.wedge (A.extDeriv k φ) ψ x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • ContMDiffSection.wedge φ (A.extDeriv l ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  rw [A.extDeriv_wedge, ContMDiffSection.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContMDiffSection.alternating_cast_apply, ContMDiffSection.alternating_cast_apply]
end Complex

section TangentComparison
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

omit [T2Space M] in
/-- Smooth differential `k`-forms identify `ℝ`-linearly with degree-`k` cochains of
`LieAlgebroid.tangent I M`. -/
def tangentCochainEquiv (k : ℕ) : SmoothForm I M ℝ k ≃ₗ[ℝ] (tangent I M).Cochain k where
  toFun := SmoothForm.toContMDiffSection
  invFun := SmoothForm.ofContMDiffSection
  left_inv := SmoothForm.ofContMDiffSection_toContMDiffSection
  right_inv := SmoothForm.toContMDiffSection_ofContMDiffSection
  map_add' := SmoothForm.add_toContMDiffSection
  map_smul' _ _ := by simp

omit [T2Space M] in
@[simp] theorem tangentCochainEquiv_apply {k : ℕ} (φ : SmoothForm I M ℝ k) :
    tangentCochainEquiv k φ = φ.toContMDiffSection := (rfl)
omit [T2Space M] in
@[simp] theorem tangentCochainEquiv_symm_apply {k : ℕ} (η : (tangent I M).Cochain k) :
    (tangentCochainEquiv k).symm η = SmoothForm.ofContMDiffSection η := (rfl)

/-- On `LieAlgebroid.tangent I M`, `extDeriv` agrees with the de Rham exterior derivative
`TauCeti.mextDerivₗ`. -/
theorem tangent_extDeriv_toContMDiffSection {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k φ.toContMDiffSection = (mextDerivₗ I k φ).toContMDiffSection := by
  ext x v
  choose V hV using fun i ↦ ContMDiffSection.evalLinearMap_surjective (I := I) (F := E) ∞
    (V := (TangentSpace I : M → Type _)) x (v i)
  have hv : (fun i ↦ V i x) = v := funext fun i ↦ by
    simpa only [ContMDiffSection.evalLinearMap_apply] using hV i
  rw [← hv]; cases k with
  | zero =>
    have htup : (fun i : Fin 1 ↦ V i x) = ![V 0 x] := funext fun i ↦ by fin_cases i; rfl
    rw [htup, (tangent I M).extDeriv_zero_apply_section, anchorDeriv_apply, tangent_anchor_apply,
      SmoothForm.toContMDiffSection_apply, mextDerivₗ_zero_apply]
    congr 2; ext y; simp
  | succ k =>
    rw [(tangent I M).extDeriv_succ_apply_sections,
      (mextDerivₗ I (k + 1) φ).toContMDiffSection_apply x, mextDerivₗ_apply,
      TauCeti.mextDeriv_apply_vectorField (φ.mdifferentiableAt x)
        (fun i ↦ (V i).contMDiff.mdifferentiableAt (by simp)),
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [anchorDeriv_apply, tangent_anchor_apply]; congr 3; ext y
      simp only [ContMDiffSection.scalarAlternatingEquiv_apply, SmoothForm.toContMDiffSection_apply]
      congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [φ.toContMDiffSection_apply x, tangent_bracket_apply, pow_succ, mul_neg, mul_one, neg_smul]

/-- `tangentCochainEquiv` intertwines the de Rham exterior derivative `TauCeti.mextDerivₗ` with
`extDeriv` on `LieAlgebroid.tangent I M`. -/
theorem extDeriv_tangentCochainEquiv {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k (tangentCochainEquiv k φ) =
      tangentCochainEquiv (k + 1) (mextDerivₗ I k φ) :=
  tangent_extDeriv_toContMDiffSection φ
end TangentComparison

end TauCeti.LieAlgebroid
