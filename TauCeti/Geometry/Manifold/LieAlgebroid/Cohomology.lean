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
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.Derivation

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

For a finite-rank smooth Lie algebroid `A` over a finite-dimensional Hausdorff real manifold `M`,
degree-`k` cochains `A.Cochain k` are smooth sections of the alternating bundle
`x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`. By local-frame tensoriality (`ContMDiffSection.scalarAlternatingEquiv`),
`A.Cochain k` is `C^∞(M, ℝ)`-linearly equivalent (`A.cochainAlternatingEquiv k`) to the module of
alternating `C^∞(M, ℝ)`-multilinear forms `A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯` on
the Lie–Rinehart algebra `(ℝ, C^∞⟮I, M; ℝ⟯, A.Sections)`.

Transporting `TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv` and
`TauCeti.LieRinehartAlgebra.Cohomology.d` across `A.cochainAlternatingEquiv` yields the algebroid
Lie derivative `A.lieDeriv` and the Chevalley–Eilenberg differential `A.extDeriv` on smooth bundle
cochains, together with:

* the explicit Chevalley–Eilenberg formula (`A.extDeriv_zero_apply`,
  `A.extDeriv_one_apply_sections`, `A.extDeriv_succ_apply_sections`);
* `d_A ∘ d_A = 0` in every degree (`A.extDeriv_extDeriv`, `A.extDeriv_comp_extDeriv`), the cochain
  complex `A.cochainComplex` in `ModuleCat ℝ`, and the algebroid cohomology `A.cohomology`;
* the Cartan calculus (`A.interior_extDeriv_zero`, `A.interior_extDeriv_succ`,
  `A.interior_lieDeriv`, `A.lieDeriv_bracket`, `A.lieDeriv_extDeriv`);
* the derivation and graded Leibniz rules with respect to `A.wedge`
  (`A.lieDeriv_wedge`, `A.extDeriv_wedge_apply`, `A.extDeriv_wedge`);
* comparison with the de Rham exterior derivative on `LieAlgebroid.tangent I M`
  (`TauCeti.LieAlgebroid.tangent_extDeriv_toContMDiffSection`);
* the rescaled tangent algebroid `scaledTangentReal` on `ℝ` with anchor `ρ(∂_x) = x ∂_x`, whose
  differential `(d_A f)(∂_x) = x f'` vanishes on the coordinate function at the origin while its
  degree-zero cocycles are still the constant functions
  (`scaledTangentReal_extDeriv_zero_id`, `scaledTangentReal_extDeriv_zero_eq_zero_iff`).

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Mathematical
  Society Lecture Note Series 213, Cambridge University Press (2005), §7.1.
* R. Loja Fernandes and I. Marcut, *Lectures on Poisson Geometry*, AMS Graduate Studies in
  Mathematics (2025), Chapter 8.
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.LieAlgebroid

section Cochain

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- Degree-`k` Chevalley–Eilenberg cochains of a Lie algebroid `A`: smooth sections of the
scalar-valued alternating bundle `x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`. -/
abbrev Cochain (_A : LieAlgebroid I F V) (k : ℕ) : Type _ :=
  Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯

/-- Transport cochains of `A` along a degree equality `m = n`. -/
def cochainCast (A : LieAlgebroid I F V) {m n : ℕ} (h : m = n) :
    A.Cochain m ≃ₗ[C^∞⟮I, M; ℝ⟯] A.Cochain n := by
  cases h
  exact LinearEquiv.refl _ _

@[simp]
theorem cochainCast_apply (A : LieAlgebroid I F V) {m n : ℕ} (h : m = n) (η : A.Cochain m)
    (x : M) (v : Fin n → V x) :
    A.cochainCast h η x v = η x (v ∘ Fin.cast h) := by
  cases h
  rfl

@[simp]
theorem cochainCast_rfl (A : LieAlgebroid I F V) {m : ℕ} (η : A.Cochain m) :
    A.cochainCast rfl η = η := (rfl)

@[simp]
theorem cochainCast_trans (A : LieAlgebroid I F V) {m n p : ℕ} (h₁ : m = n) (h₂ : n = p)
    (η : A.Cochain m) :
    A.cochainCast h₂ (A.cochainCast h₁ η) = A.cochainCast (h₁.trans h₂) η := by
  cases h₁
  cases h₂
  rfl

/-- Interior product inserting a smooth section of `A` into the first slot of a `(k + 1)`-cochain,
specializing `ContMDiffSection.interior` to `A.Cochain`. -/
def interior (A : LieAlgebroid I F V) (k : ℕ) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] A.Cochain (k + 1) →ₗ[C^∞⟮I, M; ℝ⟯] A.Cochain k :=
  ContMDiffSection.interior (I := I) (FW := F) (FV := ℝ) (W := V) (V := Bundle.Trivial M ℝ)
    (n := ∞) (k := k)

/-- `LieAlgebroid.interior` agrees definitionally with `ContMDiffSection.interior`. -/
theorem interior_eq_contMDiffSection (A : LieAlgebroid I F V) {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (η : A.Cochain (k + 1)) :
    A.interior k a η = ContMDiffSection.interior a η := (rfl)

@[simp]
theorem interior_apply (A : LieAlgebroid I F V) {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (η : A.Cochain (k + 1)) (x : M) (v : Fin k → V x) :
    A.interior k a η x v = η x (Matrix.vecCons (a x) v) :=
  ContMDiffSection.interior_apply a η x v

/-- Exterior (wedge) product of a `k`-cochain and an `l`-cochain of `A`, specializing
`ContMDiffSection.wedge` to `A.Cochain`. -/
def wedge (A : LieAlgebroid I F V) (k l : ℕ) :
    A.Cochain k →ₗ[C^∞⟮I, M; ℝ⟯] A.Cochain l →ₗ[C^∞⟮I, M; ℝ⟯] A.Cochain (k + l) :=
  ContMDiffSection.wedge (I := I) (FW := F) (W := V) (n := ∞) (k := k) (l := l)

/-- `LieAlgebroid.wedge` agrees definitionally with `ContMDiffSection.wedge`. -/
theorem wedge_eq_contMDiffSection (A : LieAlgebroid I F V) {k l : ℕ} (φ : A.Cochain k)
    (ψ : A.Cochain l) :
    A.wedge k l φ ψ = ContMDiffSection.wedge φ ψ := (rfl)

@[simp]
theorem wedge_apply_zero_left (A : LieAlgebroid I F V) {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l)
    (x : M) (v : Fin (0 + l) → V x) :
    A.wedge 0 l φ ψ x v = φ x 0 * ψ x (v ∘ Fin.cast (Nat.zero_add l).symm) :=
  ContMDiffSection.wedge_apply_zero_left φ ψ x v

@[simp]
theorem wedge_apply_zero_right (A : LieAlgebroid I F V) {k : ℕ} (φ : A.Cochain k) (ψ : A.Cochain 0)
    (x : M) (v : Fin (k + 0) → V x) :
    A.wedge k 0 φ ψ x v = φ x (v ∘ Fin.cast (Nat.add_zero k).symm) * ψ x 0 :=
  ContMDiffSection.wedge_apply_zero_right φ ψ x v

/-- Graded commutativity of the wedge product of algebroid cochains upon evaluation. -/
theorem wedge_comm_apply (A : LieAlgebroid I F V) {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l)
    (x : M) (v : Fin (k + l) → V x) :
    A.wedge k l φ ψ x v =
      (-1 : ℝ) ^ (k * l) • A.wedge l k ψ φ x (v ∘ Fin.cast (Nat.add_comm l k)) :=
  ContMDiffSection.wedge_comm_apply φ ψ x v

/-- Graded Leibniz rule for `LieAlgebroid.interior` across `LieAlgebroid.wedge` upon evaluation. -/
theorem interior_wedge_apply (A : LieAlgebroid I F V) {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) (ψ : A.Cochain (l + 1)) (x : M) (v : Fin (k + 1 + l) → V x) :
    A.interior (k + 1 + l) a (A.wedge (k + 1) (l + 1) φ ψ) x v =
      A.wedge k (l + 1) (A.interior k a φ) ψ x
          (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.interior l a ψ) x v :=
  ContMDiffSection.interior_wedge_apply a φ ψ x v

/-- Degree-zero cochains of `A` are `C^∞(M, ℝ)`-linearly equivalent to smooth scalar functions
`C^∞⟮I, M; ℝ⟯`. -/
def cochainZeroEquiv (A : LieAlgebroid I F V) : A.Cochain 0 ≃ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ where
  toFun η := ContMDiffSection.trivialEquiv
    ⟨fun x ↦ η x 0, η.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ Fin.elim0 i⟩
  invFun f :=
    ⟨fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ (V x) (Fin 0) (f x), fun x₀ ↦ by
      rw [contMDiffAt_continuousAlternatingMap_bundle]
      refine ⟨contMDiffAt_id, ?_⟩
      have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates F (E₁ := V) ℝ
          (E₂ := Bundle.Trivial M ℝ) x₀ y x₀ y
          (ContinuousAlternatingMap.constOfIsEmpty ℝ (V y) (Fin 0) (f y))) =
          fun y ↦ (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ F ℝ (Fin 0)).toContinuousLinearMap
            (f y) := by
        funext y
        ext v
        simp [ContinuousAlternatingMap.inCoordinates]
      rw [heq]
      exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ F ℝ (Fin 0))
        |>.toContinuousLinearMap.contDiff.comp_contMDiffAt (f.contMDiff x₀)⟩
  left_inv η := by
    ext x v
    simpa using congr_arg (η x) (Subsingleton.elim 0 v)
  right_inv f := by
    ext x
    rw [ContMDiffSection.trivialEquiv_apply]
    rfl
  map_add' _ _ := by
    ext x
    simp
  map_smul' f η := by
    ext x
    simp [ContMDiffSection.smul_apply]

@[simp]
theorem cochainZeroEquiv_apply (A : LieAlgebroid I F V) (η : A.Cochain 0) (x : M) :
    A.cochainZeroEquiv η x = η x 0 :=
  ContMDiffSection.trivialEquiv_apply _ x

@[simp]
theorem cochainZeroEquiv_symm_apply (A : LieAlgebroid I F V) (f : C^∞⟮I, M; ℝ⟯)
    (x : M) (v : Fin 0 → V x) :
    A.cochainZeroEquiv.symm f x v = f x := (rfl)

/-- Left wedge product with a `0`-cochain is scalar multiplication by `cochainZeroEquiv φ`. -/
theorem wedge_zero_left (A : LieAlgebroid I F V) {l : ℕ} (φ : A.Cochain 0) (ψ : A.Cochain l) :
    A.wedge 0 l φ ψ = A.cochainCast (Nat.zero_add l).symm (A.cochainZeroEquiv φ • ψ) := by
  ext x v
  simp [ContMDiffSection.smul_apply]

/-- Right wedge product with a `0`-cochain is scalar multiplication by `cochainZeroEquiv ψ`. -/
theorem wedge_zero_right (A : LieAlgebroid I F V) {k : ℕ} (φ : A.Cochain k) (ψ : A.Cochain 0) :
    A.wedge k 0 φ ψ = A.cochainCast (Nat.add_zero k).symm (A.cochainZeroEquiv ψ • φ) := by
  ext x v
  simp only [A.wedge_apply_zero_right, map_smul, ContMDiffSection.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, A.cochainZeroEquiv_apply, A.cochainCast_apply]
  exact mul_comm _ _

/-- Graded Leibniz rule for `LieAlgebroid.interior` across `LieAlgebroid.wedge` at cochain level. -/
theorem interior_wedge (A : LieAlgebroid I F V) {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) (ψ : A.Cochain (l + 1)) :
    A.interior (k + 1 + l) a (A.wedge (k + 1) (l + 1) φ ψ) =
      A.cochainCast (show k + (l + 1) = k + 1 + l by omega)
          (A.wedge k (l + 1) (A.interior k a φ) ψ) +
        (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.interior l a ψ) := by
  ext x v
  simpa using A.interior_wedge_apply a φ ψ x v

end Cochain

section Complex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  (A : LieAlgebroid I F V)

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private lemma contMDiffMap_zsmul_apply (z : ℤ) (g : C^∞⟮I, M; ℝ⟯) (x : M) :
    (z • g) x = z • g x := by
  rw [← Int.cast_smul_eq_zsmul ℝ z g, ← Int.cast_smul_eq_zsmul ℝ z (g x), ContMDiffMap.coe_smul,
    Pi.smul_apply]

/-- Smooth degree-`k` cochains of `A` are `C^∞(M, ℝ)`-linearly equivalent to alternating
`C^∞(M, ℝ)`-multilinear maps `A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯`. -/
def cochainAlternatingEquiv (k : ℕ) :
    A.Cochain k ≃ₗ[C^∞⟮I, M; ℝ⟯] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  ContMDiffSection.scalarAlternatingEquiv.trans
    { toFun Φ := Φ.compLinearMap A.sectionsEquiv.toLinearMap
      invFun Ψ := Ψ.compLinearMap A.sectionsEquiv.symm.toLinearMap
      left_inv Φ := by ext s x; simp
      right_inv Ψ := by ext s x; simp
      map_add' _ _ := by ext s x; simp
      map_smul' _ _ := by ext s x; simp }

/-- `A.cochainAlternatingEquiv` viewed as an `ℝ`-linear equivalence. -/
def cochainAlternatingEquivReal (k : ℕ) :
    A.Cochain k ≃ₗ[ℝ] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  { A.cochainAlternatingEquiv k with
    map_smul' c η := by
      change A.cochainAlternatingEquiv k (c • η) = c • A.cochainAlternatingEquiv k η
      rw [← algebraMap_smul C^∞⟮I, M; ℝ⟯ c η, (A.cochainAlternatingEquiv k).map_smul]
      ext s x
      rfl }

@[simp]
theorem cochainAlternatingEquivReal_apply {k : ℕ} (η : A.Cochain k) :
    A.cochainAlternatingEquivReal k η = A.cochainAlternatingEquiv k η := (rfl)

@[simp]
theorem cochainAlternatingEquivReal_symm_apply {k : ℕ}
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    (A.cochainAlternatingEquivReal k).symm Φ = (A.cochainAlternatingEquiv k).symm Φ := (rfl)

@[simp]
theorem cochainAlternatingEquiv_apply {k : ℕ} (η : A.Cochain k) (s : Fin k → A.Sections)
    (x : M) :
    A.cochainAlternatingEquiv k η s x = η x (fun i ↦ A.sectionsEquiv (s i) x) := by
  rw [cochainAlternatingEquiv]
  simp

@[simp]
theorem cochainAlternatingEquiv_symm_apply_sections {k : ℕ}
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.cochainAlternatingEquiv k).symm Φ x (fun i ↦ s i x) =
      Φ (fun i ↦ A.sectionsEquiv.symm (s i)) x := by
  rw [cochainAlternatingEquiv]
  simp

/-- Pointwise evaluation of a `k`-cochain on global smooth sections via
`cochainAlternatingEquiv`. -/
theorem cochain_apply_sections {k : ℕ} (η : A.Cochain k) (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    η x (fun i ↦ s i x) =
      A.cochainAlternatingEquiv k η (fun i ↦ A.sectionsEquiv.symm (s i)) x := by
  simp

@[simp]
theorem cochainAlternatingEquiv_zero_apply (η : A.Cochain 0) (s : Fin 0 → A.Sections) :
    A.cochainAlternatingEquiv 0 η s = A.cochainZeroEquiv η := by
  ext x
  simpa using congr_arg (η x) (Subsingleton.elim _ 0)

@[simp]
theorem cochainAlternatingEquiv_interior {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    A.cochainAlternatingEquiv k (A.interior k a η) =
      (A.cochainAlternatingEquiv (k + 1) η).curryLeft (A.sectionsEquiv.symm a) := by
  ext s x
  simp only [cochainAlternatingEquiv_apply, A.interior_apply, AlternatingMap.curryLeft_apply_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun _ ↦ rfl) i
  simp

omit [FiniteDimensional ℝ F] in
/-- Two positive-degree cochains are equal when all their interior products with global smooth
sections agree. -/
theorem cochain_ext_of_interior {k : ℕ} {φ ψ : A.Cochain (k + 1)}
    (h : ∀ a : Cₛ^∞⟮I; F, V⟯, A.interior k a φ = A.interior k a ψ) :
    φ = ψ :=
  ContMDiffSection.ext_of_interior h

/-- The Lie derivative of algebroid cochains along a smooth section of `A`, transported from the
Lie–Rinehart Lie derivative on `A.Sections`. -/
def lieDeriv {k : ℕ} : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] A.Cochain k →ₗ[ℝ] A.Cochain k where
  toFun a :=
    (A.cochainAlternatingEquivReal k).symm.toLinearMap ∘ₗ
      TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv ℝ (A.sectionsEquiv.symm a) ∘ₗ
      (A.cochainAlternatingEquivReal k).toLinearMap
  map_add' a b := by
    refine LinearMap.ext fun η ↦ (A.cochainAlternatingEquiv k).injective ?_
    simp [map_add]
  map_smul' c a := by
    refine LinearMap.ext fun η ↦ (A.cochainAlternatingEquivReal k).injective ?_
    rw [RingHom.id_apply, LinearMapClass.map_smul_of_tower A.sectionsEquiv.symm c a]
    simp

@[simp]
theorem cochainAlternatingEquiv_lieDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.cochainAlternatingEquiv k (A.lieDeriv a η) =
      TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv ℝ (A.sectionsEquiv.symm a)
        (A.cochainAlternatingEquiv k η) := by
  rw [lieDeriv]
  exact (A.cochainAlternatingEquiv k).apply_symm_apply _

/-- `LieAlgebroid.lieDeriv` commutes with degree casts `cochainCast`. -/
theorem lieDeriv_cochainCast {m n : ℕ} (h : m = n) (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain m) :
    A.lieDeriv a (A.cochainCast h η) = A.cochainCast h (A.lieDeriv a η) := by
  cases h
  rfl

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
  · congr 2
    ext y
    simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cochainAlternatingEquiv_apply]
    congr 1
    funext j
    by_cases hij : j = i <;> simp [hij]

@[simp]
theorem cochainZeroEquiv_lieDeriv (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain 0) :
    A.cochainZeroEquiv (A.lieDeriv a η) = A.anchorDeriv a (A.cochainZeroEquiv η) := by
  rw [← A.cochainAlternatingEquiv_zero_apply (A.lieDeriv a η) ![],
    A.cochainAlternatingEquiv_lieDeriv, TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv_apply,
    Finset.univ_eq_empty, Finset.sum_empty, sub_zero, A.cochainAlternatingEquiv_zero_apply,
    Sections.lie_def, LinearEquiv.apply_symm_apply]

/-- Leibniz rule for the Lie derivative with respect to multiplication by a smooth function. -/
@[simp]
theorem lieDeriv_smul {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) :
    A.lieDeriv a (f • η) = f • A.lieDeriv a η + A.anchorDeriv a f • η := by
  refine (A.cochainAlternatingEquiv k).injective ?_
  simp [map_add, map_smul, Sections.lie_def]

/-- The Chevalley–Eilenberg differential `d_A : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1)` of a Lie
algebroid `A`. -/
def extDeriv (k : ℕ) : A.Cochain k →ₗ[ℝ] A.Cochain (k + 1) :=
  (A.cochainAlternatingEquivReal (k + 1)).symm.toLinearMap ∘ₗ
    TauCeti.LieRinehartAlgebra.Cohomology.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k ∘ₗ
    (A.cochainAlternatingEquivReal k).toLinearMap

@[simp]
theorem cochainAlternatingEquiv_extDeriv (k : ℕ) (η : A.Cochain k) :
    A.cochainAlternatingEquiv (k + 1) (A.extDeriv k η) =
      TauCeti.LieRinehartAlgebra.Cohomology.d ℝ C^∞⟮I, M; ℝ⟯ A.Sections k
        (A.cochainAlternatingEquiv k η) := by
  rw [extDeriv]
  exact (A.cochainAlternatingEquiv (k + 1)).apply_symm_apply _

/-- `LieAlgebroid.extDeriv` commutes with degree casts `cochainCast`. -/
theorem extDeriv_cochainCast {m n : ℕ} (h : m = n) (η : A.Cochain m) :
    A.extDeriv n (A.cochainCast h η) =
      A.cochainCast (congrArg (· + 1) h) (A.extDeriv m η) := by
  cases h
  rfl

/-- In degree zero, `(d_A η)(a) = ρ(a) (cochainZeroEquiv η)`. -/
@[simp]
theorem extDeriv_zero_apply_section (η : A.Cochain 0) (a : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv 0 η) x ![a x] = A.anchorDeriv a (A.cochainZeroEquiv η) x := by
  have htup : (![a x] : Fin 1 → V x) = fun i ↦ (![a] i) x := funext fun i ↦ by fin_cases i; rfl
  rw [htup, A.cochain_apply_sections, A.cochainAlternatingEquiv_extDeriv,
    TauCeti.LieRinehartAlgebra.Cohomology.d_zero_apply, Matrix.cons_val_zero,
    A.cochainAlternatingEquiv_zero_apply, Sections.lie_def, LinearEquiv.apply_symm_apply]

/-- Pointwise degree-zero formula `d_A f = ρ*(df)`: evaluating `d_A η` on any fibre vector `v : V x`
differentiates `cochainZeroEquiv η` along `ρ(v)`. -/
theorem extDeriv_zero_apply (η : A.Cochain 0) (x : M) (v : V x) :
    (A.extDeriv 0 η) x ![v] = mvfderiv I (A.cochainZeroEquiv η) x (A.anchor x v) := by
  obtain ⟨a, hax⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (V := V) x v
  rw [ContMDiffSection.evalLinearMap_apply] at hax
  rw [← hax, A.extDeriv_zero_apply_section, anchorDeriv_apply]

/-- **The Chevalley–Eilenberg formula** for `A.extDeriv` in positive degree, evaluated on smooth
sections of `A`. -/
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
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hrem : A.cochainAlternatingEquiv (k + 1) η
          (i.removeNth fun r ↦ A.sectionsEquiv.symm (s r)) =
        ContMDiffSection.scalarAlternatingEquiv η (i.removeNth s) := by
      ext y
      simp [Fin.removeNth]
    rw [contMDiffMap_zsmul_apply, Sections.lie_def, LinearEquiv.apply_symm_apply, hrem]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContMDiffMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [contMDiffMap_zsmul_apply, cochainAlternatingEquiv_apply]
    congr 2
    funext r
    refine Fin.cases ?_ (fun q ↦ ?_) r
    · simp
    · simp [Fin.removeNth]

/-! ### Nilpotency, cochain complex, and cohomology -/

/-- The algebroid Chevalley–Eilenberg differential squares to zero in every degree. -/
@[simp]
theorem extDeriv_extDeriv (k : ℕ) (η : A.Cochain k) :
    A.extDeriv (k + 1) (A.extDeriv k η) = 0 := by
  refine (A.cochainAlternatingEquiv (k + 2)).injective ?_
  simp

/-- Composite form of `d_A ∘ d_A = 0`. -/
theorem extDeriv_comp_extDeriv (k : ℕ) : A.extDeriv (k + 1) ∘ₗ A.extDeriv k = 0 :=
  LinearMap.ext (A.extDeriv_extDeriv k)

/-- The Chevalley–Eilenberg cochain complex of a Lie algebroid `A` in `ModuleCat ℝ`. -/
@[expose] def cochainComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (A.Cochain k))
    (fun k ↦ ModuleCat.ofHom (A.extDeriv k)) fun k ↦ by
      rw [← ModuleCat.ofHom_comp, A.extDeriv_comp_extDeriv, ModuleCat.ofHom_zero]

@[simp]
theorem cochainComplex_X (k : ℕ) :
    A.cochainComplex.X k = ModuleCat.of ℝ (A.Cochain k) := (rfl)

@[simp]
theorem cochainComplex_d_succ (k : ℕ) :
    A.cochainComplex.d k (k + 1) = ModuleCat.ofHom (A.extDeriv k) := by
  simp [cochainComplex]

/-- The degree-`k` Lie algebroid cohomology `H^k(A)` as an `ℝ`-module. -/
abbrev cohomology (k : ℕ) : ModuleCat ℝ :=
  A.cochainComplex.homology k

/-! ### Cartan calculus -/

/-- Cartan's formula in degree zero: `ι_a (d_A η) = L_a η`. -/
@[simp]
theorem interior_extDeriv_zero (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain 0) :
    A.interior 0 a (A.extDeriv 0 η) = A.lieDeriv a η := by
  refine (A.cochainAlternatingEquiv 0).injective ?_
  simp

/-- **Cartan's magic formula** for Lie algebroid cochains:
`ι_a (d_A η) = L_a η - d_A (ι_a η)`. -/
theorem interior_extDeriv_succ {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    A.interior (k + 1) a (A.extDeriv (k + 1) η) =
      A.lieDeriv a η - A.extDeriv k (A.interior k a η) := by
  refine (A.cochainAlternatingEquiv (k + 1)).injective ?_
  simp [map_sub]

/-- Explicit Chevalley–Eilenberg formula for a `1`-cochain:
`(d_A α)(a, b) = ρ(a)(α(b)) - ρ(b)(α(a)) - α([a, b])`. -/
theorem extDeriv_one_apply_sections (α : A.Cochain 1) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (A.extDeriv 1 α) x ![a x, b x] =
      A.anchorDeriv a (ContMDiffSection.scalarAlternatingEquiv α ![b]) x -
        A.anchorDeriv b (ContMDiffSection.scalarAlternatingEquiv α ![a]) x -
        α x ![A.bracket a b x] := by
  have hcons : (![a x, b x] : Fin 2 → V x) = Matrix.vecCons (a x) ![b x] := rfl
  rw [hcons, ← A.interior_apply a, A.interior_extDeriv_succ, ContMDiffSection.coe_sub,
    Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
  have hb : (![b x] : Fin 1 → V x) = fun i ↦ (![b] i) x := funext fun i ↦ by fin_cases i; rfl
  rw [hb, A.lieDeriv_apply_sections a α ![b] x, ← hb, A.extDeriv_zero_apply_section]
  simp only [Fin.sum_univ_one]
  have hupd : (fun j : Fin 1 ↦ Function.update ![b] 0 (A.bracket a (![b] 0)) j x) =
      ![A.bracket a b x] :=
    funext fun i ↦ by fin_cases i; rfl
  have hco : A.cochainZeroEquiv (A.interior 0 a α) =
      ContMDiffSection.scalarAlternatingEquiv α ![a] := by
    ext y
    simpa [A.interior_apply] using congr_arg (α y) (funext fun i ↦ by fin_cases i; rfl)
  rw [hupd, hco]
  ring

/-- Rearranged Cartan magic formula: `L_a η = ι_a (d_A η) + d_A (ι_a η)`. -/
theorem lieDeriv_eq_interior_extDeriv_add {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    A.lieDeriv a η =
      A.interior (k + 1) a (A.extDeriv (k + 1) η) + A.extDeriv k (A.interior k a η) := by
  rw [A.interior_extDeriv_succ, sub_add_cancel]

/-- Commutator of Lie derivative and interior product:
`ι_b (L_a η) = L_a (ι_b η) - ι_{[a, b]} η`. -/
theorem interior_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain (k + 1)) :
    A.interior k b (A.lieDeriv a η) =
      A.lieDeriv a (A.interior k b η) - A.interior k (A.bracket a b) η := by
  refine (A.cochainAlternatingEquiv k).injective ?_
  have hbr : A.sectionsEquiv.symm (A.bracket a b) =
      ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ := by
    apply A.sectionsEquiv.injective
    simp
  simp [map_sub, hbr, TauCeti.LieRinehartAlgebra.Cohomology.curryLeft_lieDeriv]

/-- The Lie derivative is a Lie algebra representation: `L_{[a, b]} = L_a ∘ L_b - L_b ∘ L_a`. -/
theorem lieDeriv_bracket {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.lieDeriv (A.bracket a b) η =
      A.lieDeriv a (A.lieDeriv b η) - A.lieDeriv b (A.lieDeriv a η) := by
  refine (A.cochainAlternatingEquiv k).injective ?_
  have hbr : A.sectionsEquiv.symm (A.bracket a b) =
      ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ := by
    apply A.sectionsEquiv.injective
    simp
  simp [map_sub, hbr, TauCeti.LieRinehartAlgebra.Cohomology.lieDeriv_lie]

/-- The Lie derivative commutes with the Chevalley–Eilenberg differential:
`L_a (d_A η) = d_A (L_a η)`. -/
@[simp]
theorem lieDeriv_extDeriv {k : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (η : A.Cochain k) :
    A.lieDeriv a (A.extDeriv k η) = A.extDeriv k (A.lieDeriv a η) := by
  refine (A.cochainAlternatingEquiv (k + 1)).injective ?_
  simp

/-! ### Wedge derivation and graded Leibniz rules -/

private lemma comp_finCast {α : Type*} {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (f : Fin c → α) :
    (f ∘ Fin.cast h₂) ∘ Fin.cast h₁ = f ∘ Fin.cast (h₁.trans h₂) := by
  funext i
  rfl

private lemma comp_finCast_self {α : Type*} {a : ℕ} (h : a = a) (f : Fin a → α) :
    f ∘ Fin.cast h = f := by
  funext i
  rfl

private theorem lieDeriv_wedge_abel {G : Type*} [AddCommGroup G] (x₁ x₂ x₃ x₄ y₁ y₂ : G) :
    (x₁ + x₂ + (x₃ + x₄)) - (y₁ + y₂) = (x₁ - y₁ + x₃) + (x₂ + (x₄ - y₂)) := by
  abel

private theorem lieDeriv_wedge_succ {k l : ℕ} (a b : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) (ψ : A.Cochain (l + 1))
    (ih₁ : A.lieDeriv a (A.wedge k (l + 1) (A.interior k b φ) ψ) =
      A.wedge k (l + 1) (A.lieDeriv a (A.interior k b φ)) ψ +
        A.wedge k (l + 1) (A.interior k b φ) (A.lieDeriv a ψ))
    (ih₂ : A.lieDeriv a (A.wedge (k + 1) l φ (A.interior l b ψ)) =
      A.wedge (k + 1) l (A.lieDeriv a φ) (A.interior l b ψ) +
        A.wedge (k + 1) l φ (A.lieDeriv a (A.interior l b ψ))) :
    A.interior (k + 1 + l) b (A.lieDeriv a (A.wedge (k + 1) (l + 1) φ ψ)) =
      A.interior (k + 1 + l) b
        (A.wedge (k + 1) (l + 1) (A.lieDeriv a φ) ψ +
          A.wedge (k + 1) (l + 1) φ (A.lieDeriv a ψ)) := by
  have hc : k + (l + 1) = k + 1 + l := by omega
  have hl₁ : A.lieDeriv a (A.cochainCast hc (A.wedge k (l + 1) (A.interior k b φ) ψ)) =
      A.cochainCast hc (A.wedge k (l + 1) (A.lieDeriv a (A.interior k b φ)) ψ) +
        A.cochainCast hc (A.wedge k (l + 1) (A.interior k b φ) (A.lieDeriv a ψ)) :=
    (A.lieDeriv_cochainCast hc a _).trans
      ((congr_arg (A.cochainCast hc) ih₁).trans ((A.cochainCast hc).map_add _ _))
  have hl₂ : A.lieDeriv a ((-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.interior l b ψ)) =
      (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l (A.lieDeriv a φ) (A.interior l b ψ) +
        (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.lieDeriv a (A.interior l b ψ)) := by
    rw [(A.lieDeriv a).map_smul, ih₂, smul_add]
  have hlhs := (A.interior_lieDeriv a b (A.wedge (k + 1) (l + 1) φ ψ)).trans (congr_arg₂ (· - ·)
    ((congr_arg (A.lieDeriv a) (A.interior_wedge b φ ψ)).trans
      (((A.lieDeriv a).map_add _ _).trans (congr_arg₂ (· + ·) hl₁ hl₂)))
    (A.interior_wedge (A.bracket a b) φ ψ))
  have hr₁ := (A.interior_wedge b (A.lieDeriv a φ) ψ).trans (congr_arg₂ (· + ·)
    ((congr_arg (fun η ↦ A.cochainCast hc (A.wedge k (l + 1) η ψ))
      (A.interior_lieDeriv a b φ)).trans
      ((congr_arg (A.cochainCast hc) (LinearMap.map_sub₂ _ _ _ _)).trans
        ((A.cochainCast hc).map_sub _ _))) rfl)
  have hr₂sub : (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.interior l b (A.lieDeriv a ψ)) =
      (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.lieDeriv a (A.interior l b ψ)) -
        (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) l φ (A.interior l (A.bracket a b) ψ) := by
    rw [A.interior_lieDeriv a b ψ, LinearMap.map_sub]
    ext x v
    simp [mul_sub]
  have hr₂ := (A.interior_wedge b φ (A.lieDeriv a ψ)).trans (congr_arg₂ (· + ·) rfl hr₂sub)
  exact hlhs.trans ((lieDeriv_wedge_abel _ _ _ _ _ _).trans
    (((A.interior (k + 1 + l) b).map_add _ _).trans (congr_arg₂ (· + ·) hr₁ hr₂)).symm)

/-- The Lie derivative is an ungraded derivation of `A.wedge`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.lieDeriv a (A.wedge k l φ ψ) =
      A.wedge k l (A.lieDeriv a φ) ψ + A.wedge k l φ (A.lieDeriv a ψ) := by
  suffices ∀ n, ∀ {k l : ℕ}, k + l = n → ∀ (φ : A.Cochain k) (ψ : A.Cochain l),
      A.lieDeriv a (A.wedge k l φ ψ) =
        A.wedge k l (A.lieDeriv a φ) ψ + A.wedge k l φ (A.lieDeriv a ψ) from
    this (k + l) rfl φ ψ
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro k l _ φ ψ
    rcases k with _ | k
    · rw [A.wedge_zero_left φ ψ, A.lieDeriv_cochainCast, A.lieDeriv_smul, map_add,
        A.wedge_zero_left (A.lieDeriv a φ) ψ, A.wedge_zero_left φ (A.lieDeriv a ψ),
        A.cochainZeroEquiv_lieDeriv]
      exact add_comm _ _
    rcases l with _ | l
    · rw [A.wedge_zero_right φ ψ, A.lieDeriv_cochainCast, A.lieDeriv_smul, map_add,
        A.wedge_zero_right (A.lieDeriv a φ) ψ, A.wedge_zero_right φ (A.lieDeriv a ψ),
        A.cochainZeroEquiv_lieDeriv]
    refine A.cochain_ext_of_interior fun b ↦ A.lieDeriv_wedge_succ a b φ ψ
      (ih (k + (l + 1)) (by omega) rfl (A.interior k b φ) ψ)
      (ih ((k + 1) + l) (by omega) rfl φ (A.interior l b ψ))

/-- Scalar derivation rule for `A.extDeriv` in terms of `A.wedge`. -/
theorem extDeriv_smul_apply {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (η : A.Cochain k) (x : M)
    (v : Fin (k + 1) → V x) :
    (A.extDeriv k (f • η)) x v =
      A.wedge 1 k (A.extDeriv 0 (A.cochainZeroEquiv.symm f)) η x
          (v ∘ Fin.cast (Nat.add_comm 1 k)) +
        f x * (A.extDeriv k η) x v := by
  revert η v
  induction k with
  | zero =>
    intro η v
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hv, A.extDeriv_zero_apply, A.extDeriv_zero_apply, map_smul, smul_eq_mul,
      ContMDiffMap.coe_mul, A.wedge_apply_zero_right, ← A.cochainZeroEquiv_apply η x, comp_finCast]
    have hcast : (![v 0] : Fin 1 → V x) ∘
        Fin.cast ((Nat.add_zero 1).symm.trans (Nat.add_comm 1 0)) = ![v 0] :=
      funext fun i ↦ by fin_cases i; rfl
    rw [hcast, A.extDeriv_zero_apply, LinearEquiv.apply_symm_apply,
      mvfderiv_mul (f.contMDiff.mdifferentiableAt (by simp))
        ((A.cochainZeroEquiv η).contMDiff.mdifferentiableAt (by simp))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  | succ k ih =>
    intro η v
    obtain ⟨a, hax⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (V := V) x
      (v 0)
    rw [ContMDiffSection.evalLinearMap_apply] at hax
    let w : Fin (k + 1) → V x := Fin.tail v
    have hv : v = Matrix.vecCons (a x) w := by rw [hax]; exact (Matrix.cons_head_tail v).symm
    have hcons : Matrix.vecCons (a x) w ∘ Fin.cast (Nat.add_comm 1 (k + 1)) =
        Matrix.vecCons (a x) (w ∘ Fin.cast (Nat.add_comm 1 k)) :=
      funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
    rw [hv, ← A.interior_apply, ← A.interior_apply,
      A.interior_extDeriv_succ, A.interior_extDeriv_succ, A.lieDeriv_smul a f η,
      (A.interior k a).map_smul f η, hcons,
      ← A.interior_apply (k := 0 + 1 + k), A.interior_wedge_apply,
      A.interior_extDeriv_zero, A.wedge_apply_zero_left, ← A.cochainZeroEquiv_apply
        (A.lieDeriv a _), A.cochainZeroEquiv_lieDeriv, LinearEquiv.apply_symm_apply]
    simp only [ContMDiffSection.coe_sub, ContMDiffSection.coe_add, ContMDiffSection.smul_apply,
      Pi.sub_apply, Pi.add_apply, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ih (A.interior k a η) w]
    rw [comp_finCast, comp_finCast, comp_finCast_self]
    ring

private theorem extDeriv_wedge_succ_rhs {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯)
    (φ : A.Cochain (k + 1)) (ψ : A.Cochain (l + 1)) (x : M) (w : Fin (k + 1 + (l + 1)) → V x) :
    A.wedge (k + 1 + 1) (l + 1) (A.extDeriv (k + 1) φ) ψ x
        (Matrix.vecCons (a x) w ∘
          Fin.cast (show k + 1 + 1 + (l + 1) = k + 1 + (l + 1) + 1 by omega)) +
      (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) (l + 1 + 1) φ (A.extDeriv (l + 1) ψ) x
        (Matrix.vecCons (a x) w ∘
          Fin.cast (show k + 1 + (l + 1 + 1) = k + 1 + (l + 1) + 1 by omega)) =
      ((A.wedge (k + 1) (l + 1) (A.lieDeriv a φ) ψ x w -
          A.wedge (k + 1) (l + 1) (A.extDeriv k (A.interior k a φ)) ψ x w) +
        (-1 : ℝ) ^ (k + 1 + 1) *
          A.wedge (k + 1 + 1) l (A.extDeriv (k + 1) φ) (A.interior l a ψ) x
            (w ∘ Fin.cast (show k + 1 + 1 + l = k + 1 + (l + 1) by omega))) +
      (-1 : ℝ) ^ (k + 1) *
        (A.wedge k (l + 1 + 1) (A.interior k a φ) (A.extDeriv (l + 1) ψ) x
            (w ∘ Fin.cast (show k + (l + 1 + 1) = k + 1 + (l + 1) by omega)) +
          (-1 : ℝ) ^ (k + 1) *
            (A.wedge (k + 1) (l + 1) φ (A.lieDeriv a ψ) x w -
              A.wedge (k + 1) (l + 1) φ (A.extDeriv l (A.interior l a ψ)) x w)) := by
  refine congr_arg₂ (· + ·) ?_ ((smul_eq_mul _ _).trans (congr_arg (_ * ·) ?_))
  · have hcons₁ : Matrix.vecCons (a x) w ∘
          Fin.cast (show k + 1 + 1 + (l + 1) = k + 1 + (l + 1) + 1 by omega) =
        Matrix.vecCons (a x) (w ∘ Fin.cast (show k + 1 + 1 + l = k + 1 + (l + 1) by omega)) :=
      funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
    have hw₁ : A.wedge (k + 1) (l + 1) (A.interior (k + 1) a (A.extDeriv (k + 1) φ)) ψ =
        A.wedge (k + 1) (l + 1) (A.lieDeriv a φ) ψ -
          A.wedge (k + 1) (l + 1) (A.extDeriv k (A.interior k a φ)) ψ :=
      (congr_arg (fun η ↦ A.wedge (k + 1) (l + 1) η ψ) (A.interior_extDeriv_succ a φ)).trans
        (LinearMap.map_sub₂ _ _ _ _)
    rw [hcons₁, ← A.interior_apply (k := k + 1 + 1 + l), A.interior_wedge_apply,
      comp_finCast, comp_finCast_self, smul_eq_mul]
    exact congr_arg₂ (· + ·) (by rw [hw₁]; simp) rfl
  · have hcons₂ : Matrix.vecCons (a x) w ∘
        Fin.cast (show k + 1 + (l + 1 + 1) = k + 1 + (l + 1) + 1 by omega) =
        Matrix.vecCons (a x) w :=
      funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
    have hw₂ : A.wedge (k + 1) (l + 1) φ (A.interior (l + 1) a (A.extDeriv (l + 1) ψ)) =
        A.wedge (k + 1) (l + 1) φ (A.lieDeriv a ψ) -
          A.wedge (k + 1) (l + 1) φ (A.extDeriv l (A.interior l a ψ)) :=
      (congr_arg (A.wedge (k + 1) (l + 1) φ) (A.interior_extDeriv_succ a ψ)).trans
        (LinearMap.map_sub _ _ _)
    rw [hcons₂, ← A.interior_apply (k := k + 1 + (l + 1)), A.interior_wedge_apply, smul_eq_mul]
    exact congr_arg₂ (· + ·) rfl (congr_arg (_ * ·) (by rw [hw₂]; simp))

private theorem extDeriv_wedge_succ_apply {k l : ℕ} (φ : A.Cochain (k + 1))
    (ψ : A.Cochain (l + 1)) (x : M) (v : Fin (k + 1 + (l + 1) + 1) → V x)
    (ih₁ : ∀ (a : Cₛ^∞⟮I; F, V⟯) (u : Fin (k + (l + 1) + 1) → V x),
      (A.extDeriv (k + (l + 1)) (A.wedge k (l + 1) (A.interior k a φ) ψ)) x u =
        A.wedge (k + 1) (l + 1) (A.extDeriv k (A.interior k a φ)) ψ x
            (u ∘ Fin.cast (show k + 1 + (l + 1) = k + (l + 1) + 1 by omega)) +
          (-1 : ℝ) ^ k • A.wedge k (l + 1 + 1) (A.interior k a φ) (A.extDeriv (l + 1) ψ) x
            (u ∘ Fin.cast (show k + (l + 1 + 1) = k + (l + 1) + 1 by omega)))
    (ih₂ : ∀ (a : Cₛ^∞⟮I; F, V⟯) (u : Fin (k + 1 + l + 1) → V x),
      (A.extDeriv (k + 1 + l) (A.wedge (k + 1) l φ (A.interior l a ψ))) x u =
        A.wedge (k + 1 + 1) l (A.extDeriv (k + 1) φ) (A.interior l a ψ) x
            (u ∘ Fin.cast (show k + 1 + 1 + l = k + 1 + l + 1 by omega)) +
          (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) (l + 1) φ (A.extDeriv l (A.interior l a ψ)) x
            (u ∘ Fin.cast (show k + 1 + (l + 1) = k + 1 + l + 1 by omega))) :
    (A.extDeriv (k + 1 + (l + 1)) (A.wedge (k + 1) (l + 1) φ ψ)) x v =
      A.wedge (k + 1 + 1) (l + 1) (A.extDeriv (k + 1) φ) ψ x
          (v ∘ Fin.cast (show k + 1 + 1 + (l + 1) = k + 1 + (l + 1) + 1 by omega)) +
        (-1 : ℝ) ^ (k + 1) • A.wedge (k + 1) (l + 1 + 1) φ (A.extDeriv (l + 1) ψ) x
          (v ∘ Fin.cast (show k + 1 + (l + 1 + 1) = k + 1 + (l + 1) + 1 by omega)) := by
  obtain ⟨a, hax⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (V := V) x (v 0)
  rw [ContMDiffSection.evalLinearMap_apply] at hax
  let w : Fin (k + 1 + (l + 1)) → V x := Fin.tail v
  have hv : v = Matrix.vecCons (a x) w := by rw [hax]; exact (Matrix.cons_head_tail v).symm
  have hmain : A.interior (k + 1 + (l + 1)) a
        (A.extDeriv (k + 1 + (l + 1)) (A.wedge (k + 1) (l + 1) φ ψ)) =
      A.lieDeriv a (A.wedge (k + 1) (l + 1) φ ψ) -
        A.extDeriv (k + 1 + l) (A.interior (k + 1 + l) a (A.wedge (k + 1) (l + 1) φ ψ)) :=
    A.interior_extDeriv_succ a _
  have h₂ := by
    simpa only [comp_finCast, comp_finCast_self] using
      ih₂ a (w ∘ Fin.cast (show k + 1 + l + 1 = k + 1 + (l + 1) by omega))
  have hsq : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩]
  rw [hv, A.extDeriv_wedge_succ_rhs a φ ψ x w, ← A.interior_apply, hmain]
  simp only [A.lieDeriv_wedge, A.interior_wedge, (A.extDeriv (k + 1 + l)).map_add,
    (A.extDeriv (k + 1 + l)).map_smul, A.extDeriv_cochainCast,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_add, ContMDiffSection.coe_smul,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    A.cochainCast_apply, ih₁ a _, h₂, smul_eq_mul, mul_add, mul_sub, ← mul_assoc, hsq, one_mul]
  simp only [pow_succ]
  repeat rw [comp_finCast]
  repeat rw [comp_finCast_self]
  ring

/-- **Graded Leibniz rule** for `A.extDeriv` with respect to `A.wedge`, evaluated on fibre
vectors. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l)
    (x : M) (v : Fin (k + l + 1) → V x) :
    (A.extDeriv (k + l) (A.wedge k l φ ψ)) x v =
      A.wedge (k + 1) l (A.extDeriv k φ) ψ x
          (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
        (-1 : ℝ) ^ k • A.wedge k (l + 1) φ (A.extDeriv l ψ) x
          (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) := by
  suffices ∀ n, ∀ {k l : ℕ}, k + l = n → ∀ (φ : A.Cochain k) (ψ : A.Cochain l)
      (v : Fin (k + l + 1) → V x),
      (A.extDeriv (k + l) (A.wedge k l φ ψ)) x v =
        A.wedge (k + 1) l (A.extDeriv k φ) ψ x
            (v ∘ Fin.cast (show k + 1 + l = k + l + 1 by omega)) +
          (-1 : ℝ) ^ k • A.wedge k (l + 1) φ (A.extDeriv l ψ) x
            (v ∘ Fin.cast (show k + (l + 1) = k + l + 1 by omega)) from
    this (k + l) rfl φ ψ v
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro k l _ φ ψ v
    rcases k with _ | k
    · rw [A.wedge_zero_left φ ψ, A.extDeriv_cochainCast, A.cochainCast_apply,
        A.extDeriv_smul_apply, A.wedge_apply_zero_left φ (A.extDeriv l ψ),
        LinearEquiv.symm_apply_apply, pow_zero, one_smul, A.cochainZeroEquiv_apply,
        comp_finCast, comp_finCast]
    rcases l with _ | l
    · have hexp : (-1 : ℝ) ^ ((0 + 1) * (k + 1)) = (-1 : ℝ) ^ (k + 1) := by rw [zero_add, one_mul]
      rw [A.wedge_zero_right φ ψ, A.extDeriv_cochainCast, A.cochainCast_apply,
        A.extDeriv_smul_apply, A.wedge_comm_apply (A.extDeriv 0 _) φ,
        A.wedge_apply_zero_right (A.extDeriv (k + 1) φ) ψ,
        LinearEquiv.symm_apply_apply, A.cochainZeroEquiv_apply, hexp,
        smul_eq_mul, smul_eq_mul, comp_finCast, comp_finCast]
      ring
    exact A.extDeriv_wedge_succ_apply φ ψ x v
      (fun a u ↦ ih (k + (l + 1)) (by omega) rfl (A.interior k a φ) ψ u)
      (fun a u ↦ ih ((k + 1) + l) (by omega) rfl φ (A.interior l a ψ) u)

/-- Bundled form of the graded Leibniz rule for `A.extDeriv` on `A.wedge`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : A.Cochain k) (ψ : A.Cochain l) :
    A.extDeriv (k + l) (A.wedge k l φ ψ) =
      A.cochainCast (show k + 1 + l = k + l + 1 by omega)
          (A.wedge (k + 1) l (A.extDeriv k φ) ψ) +
        (-1 : ℝ) ^ k • A.cochainCast (show k + (l + 1) = k + l + 1 by omega)
          (A.wedge k (l + 1) φ (A.extDeriv l ψ)) := by
  ext x v
  simpa using A.extDeriv_wedge_apply φ ψ x v

end Complex

/-! ### Comparison with the de Rham complex on `LieAlgebroid.tangent` -/

section TangentComparison

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

omit [T2Space M] in
/-- Smooth differential `k`-forms identify `ℝ`-linearly with degree-`k` cochains of the tangent
Lie algebroid `LieAlgebroid.tangent I M`. -/
def tangentCochainEquiv (k : ℕ) : SmoothForm I M ℝ k ≃ₗ[ℝ] (tangent I M).Cochain k where
  toFun := SmoothForm.toContMDiffSection
  invFun := SmoothForm.ofContMDiffSection
  left_inv := SmoothForm.ofContMDiffSection_toContMDiffSection
  right_inv := SmoothForm.toContMDiffSection_ofContMDiffSection
  map_add' := SmoothForm.add_toContMDiffSection
  map_smul' _ _ := by simp

/-- On the tangent Lie algebroid `LieAlgebroid.tangent I M`, the Chevalley–Eilenberg differential
agrees with the de Rham exterior derivative `TauCeti.mextDerivₗ`. -/
theorem tangent_extDeriv_toContMDiffSection {k : ℕ} (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k φ.toContMDiffSection = (mextDerivₗ I k φ).toContMDiffSection := by
  ext x v
  choose V hV using fun i ↦ ContMDiffSection.evalLinearMap_surjective (I := I) (F := E) ∞
    (V := (TangentSpace I : M → Type _)) x (v i)
  have hv : (fun i ↦ V i x) = v := funext fun i ↦ by
    simpa only [ContMDiffSection.evalLinearMap_apply] using hV i
  rw [← hv]
  cases k with
  | zero =>
    have htup : (fun i : Fin 1 ↦ V i x) = ![V 0 x] := funext fun i ↦ by fin_cases i; rfl
    rw [htup, (tangent I M).extDeriv_zero_apply_section, anchorDeriv_apply, tangent_anchor_apply,
      SmoothForm.toContMDiffSection_apply, mextDerivₗ_zero_apply]
    congr 2
    ext y
    simp
  | succ k =>
    rw [(tangent I M).extDeriv_succ_apply_sections,
      (mextDerivₗ I (k + 1) φ).toContMDiffSection_apply x, mextDerivₗ_apply,
      TauCeti.mextDeriv_apply_vectorField (φ.mdifferentiableAt x)
        (fun i ↦ (V i).contMDiff.mdifferentiableAt (by simp)),
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [anchorDeriv_apply, tangent_anchor_apply]
      congr 3
      ext y
      simp only [ContMDiffSection.scalarAlternatingEquiv_apply, SmoothForm.toContMDiffSection_apply]
      congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [φ.toContMDiffSection_apply x, tangent_bracket_apply, pow_succ, mul_neg, mul_one, neg_smul]

end TangentComparison

/-! ### Rescaled tangent Lie algebroid on `ℝ` -/

section ScaledTangentReal

/-- The global unit vector field `∂_x` on `ℝ`. -/
def realUnitVectorField : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯ :=
  ⟨fun _ ↦ (1 : ℝ), contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const⟩

/-- Evaluating `realUnitVectorField` at any point of `ℝ` gives `1`. -/
theorem realUnitVectorField_apply (x : ℝ) : (show ℝ from realUnitVectorField x) = 1 := (rfl)

private def realFieldCoord
    (u : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯ :=
  ⟨fun x ↦ (u x : ℝ), (contMDiff_vectorSpace_iff_contDiff.mp u.contMDiff).contMDiff⟩

@[simp]
private theorem realFieldCoord_apply
    (u : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) (x : ℝ) :
    realFieldCoord u x = (u x : ℝ) := (rfl)

private theorem eq_realFieldCoord_smul
    (u : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) :
    u = realFieldCoord u • realUnitVectorField := by
  ext x
  rw [ContMDiffSection.smul_apply]
  change (show ℝ from u x) = (show ℝ from u x) * 1
  exact (mul_one _).symm

private theorem tangent_anchorDeriv_realUnitVectorField (g : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) :
    (tangent 𝓘(ℝ, ℝ) ℝ).anchorDeriv realUnitVectorField g = lineDerivation ℝ 1 g := by
  ext x
  rw [anchorDeriv_apply, tangent_anchor_apply, mvfderiv_eq_fderiv_apply,
    lineDerivation_apply_apply]
  rfl

private theorem tangent_real_bracket_eq
    (u v : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) :
    (tangent 𝓘(ℝ, ℝ) ℝ).bracket u v =
      (realFieldCoord u * lineDerivation ℝ 1 (realFieldCoord v) -
        realFieldCoord v * lineDerivation ℝ 1 (realFieldCoord u)) • realUnitVectorField := by
  let T := tangent 𝓘(ℝ, ℝ) ℝ
  have hskew (a b : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) :
      T.bracket a b = -T.bracket b a := by
    have h := T.bracket_self (a + b)
    simp only [map_add, LinearMap.add_apply, T.bracket_self, zero_add, add_zero,
      add_eq_zero_iff_eq_neg] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  conv_lhs => rw [eq_realFieldCoord_smul u, eq_realFieldCoord_smul v]
  rw [T.bracket_smul_right, hskew (realFieldCoord u • realUnitVectorField) realUnitVectorField,
    T.bracket_smul_right, T.bracket_self, smul_zero, zero_add, smul_neg, ← mul_smul, ← neg_smul,
    T.anchorDeriv_smul_left, tangent_anchorDeriv_realUnitVectorField,
    tangent_anchorDeriv_realUnitVectorField, add_comm, ← add_smul, ← sub_eq_add_neg]

/-- The Lie algebroid on `Tℝ` with rescaled anchor `ρ(∂_x) = x ∂_x` and bracket
`[f ∂_x, g ∂_x] = x (f g' - g f') ∂_x`. -/
def scaledTangentReal : LieAlgebroid 𝓘(ℝ, ℝ) ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) where
  anchor := (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) • (tangent 𝓘(ℝ, ℝ) ℝ).anchor
  bracket := LinearMap.mk₂ ℝ
    (fun u v ↦ (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) • (tangent 𝓘(ℝ, ℝ) ℝ).bracket u v)
    (fun u₁ u₂ v ↦ by simp [map_add, smul_add])
    (fun c u v ↦ by simp [smul_comm c (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯)])
    (fun u v₁ v₂ ↦ by simp [map_add, smul_add])
    (fun c u v ↦ by simp [smul_comm c (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯)])
  bracket_self u := by simp [(tangent 𝓘(ℝ, ℝ) ℝ).bracket_self]
  bracket_bracket u v w := by
    have hmul (f : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) :
        realFieldCoord (f • realUnitVectorField) = f := by
      ext y
      rw [realFieldCoord_apply, ContMDiffSection.smul_apply]
      change f y * 1 = f y
      exact mul_one (f y)
    simp only [LinearMap.mk₂_apply, tangent_real_bracket_eq, ← mul_smul, hmul, ← add_smul,
      Derivation.leibniz, map_sub, smul_eq_mul]
    congr 1
    ring
  bracket_smul_apply u v f x := by
    have hid : (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) x = x := rfl
    simp only [LinearMap.mk₂_apply, ContMDiffSection.smul_apply,
      (tangent 𝓘(ℝ, ℝ) ℝ).bracket_smul_apply, hid, tangent_anchor_apply,
      FunLike.coe_smul, Pi.smul_apply, map_smul]
    module

@[simp]
theorem scaledTangentReal_anchor_apply (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    scaledTangentReal.anchor x v = x • v := by
  have hid : (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) x = x := rfl
  simp [scaledTangentReal, ContMDiffSection.smul_apply, hid]

/-- On `scaledTangentReal`, `(d_A f)(∂_x) = x f'(x)`. -/
theorem scaledTangentReal_extDeriv_zero_apply (f : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) (x : ℝ) :
    (scaledTangentReal.extDeriv 0 (scaledTangentReal.cochainZeroEquiv.symm f)) x
        ![realUnitVectorField x] =
      x * fderiv ℝ f x 1 := by
  rw [scaledTangentReal.extDeriv_zero_apply, LinearEquiv.apply_symm_apply,
    scaledTangentReal_anchor_apply, map_smul, smul_eq_mul, mvfderiv_eq_fderiv_apply]
  rfl

/-- Unlike the de Rham differential `dx`, `d_A x` on `scaledTangentReal` evaluates on `∂_x` to `x`
and therefore vanishes at `0`. -/
theorem scaledTangentReal_extDeriv_zero_id (x : ℝ) :
    (scaledTangentReal.extDeriv 0 (scaledTangentReal.cochainZeroEquiv.symm ContMDiffMap.id)) x
        ![realUnitVectorField x] = x := by
  rw [scaledTangentReal_extDeriv_zero_apply]
  change x * fderiv ℝ (_root_.id : ℝ → ℝ) x 1 = x
  simp

/-- Despite the anchor vanishing at `0`, the degree-zero Chevalley–Eilenberg cocycles of
`scaledTangentReal` on `ℝ` are still precisely the constant functions. -/
theorem scaledTangentReal_extDeriv_zero_eq_zero_iff (η : scaledTangentReal.Cochain 0) :
    scaledTangentReal.extDeriv 0 η = 0 ↔
      ∃ c : ℝ, η = scaledTangentReal.cochainZeroEquiv.symm (ContMDiffMap.const c) := by
  constructor
  · intro hη
    let f : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯ := scaledTangentReal.cochainZeroEquiv η
    have hηf : η = scaledTangentReal.cochainZeroEquiv.symm f :=
      (scaledTangentReal.cochainZeroEquiv.symm_apply_apply η).symm
    have hmul (x : ℝ) : x * lineDerivation ℝ (1 : ℝ) f x = 0 := by
      have hx := congr($hη x ![realUnitVectorField x])
      rw [hηf, scaledTangentReal_extDeriv_zero_apply] at hx
      simpa [lineDerivation_apply_apply] using hx
    have hcompl : ∀ x ∈ ({0}ᶜ : Set ℝ), lineDerivation ℝ (1 : ℝ) f x = 0 := fun x hx ↦
      (mul_eq_zero.mp (hmul x)).resolve_left hx
    have hderiv0 : ∀ x : ℝ, lineDerivation ℝ (1 : ℝ) f x = 0 := fun x ↦
      congr_fun ((lineDerivation ℝ (1 : ℝ) f).contMDiff.continuous.ext_on
        (dense_compl_singleton (0 : ℝ)) continuous_const hcompl) x
    have hfderiv (x : ℝ) : fderiv ℝ f x = 0 := by
      ext
      rw [← lineDerivation_apply_apply, hderiv0 x, _root_.zero_apply]
    refine ⟨f 0, ?_⟩
    rw [hηf]
    congr 1
    ext x
    exact is_const_of_fderiv_eq_zero (f.contMDiff.contDiff.differentiable (by simp)) hfderiv x 0
  · rintro ⟨c, rfl⟩
    refine ContMDiffSection.ext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    change ((scaledTangentReal.extDeriv 0
      (scaledTangentReal.cochainZeroEquiv.symm (ContMDiffMap.const c))) x) v = 0
    rw [hv, scaledTangentReal.extDeriv_zero_apply, LinearEquiv.apply_symm_apply]
    change mvfderiv 𝓘(ℝ, ℝ) (fun _ : ℝ ↦ c) x _ = 0
    simp

end ScaledTangentReal

end TauCeti.LieAlgebroid
