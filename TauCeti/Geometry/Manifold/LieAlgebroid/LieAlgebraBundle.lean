/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Zero-anchor Lie algebroids from bundles of Lie algebras

A smooth real vector bundle `V → M` equipped with a smooth section `B` of `V →L[ℝ] V →L[ℝ] V` that
is fibrewise alternating and satisfies the fibrewise Jacobi identity is a Lie algebroid with zero
anchor (`TauCeti.LieAlgebroid.ofFiberwiseBracket`) and `C^∞⟮I, M; ℝ⟯`-bilinear section bracket.
Specializing to `Bundle.Trivial M 𝔤` for a finite-dimensional real Hausdorff topological Lie algebra
`𝔤` gives `TauCeti.LieAlgebroid.trivialLieAlgebra`, together with `trivialLieAlgebraEval`,
`trivialLieAlgebraConst`, and `trivialLieAlgebraPullback`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff

namespace TauCeti

namespace LieAlgebroid

section ZeroAnchor

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- When the anchor of a Lie algebroid vanishes, its bracket is `C^∞⟮I, M; ℝ⟯`-linear on the
right. -/
theorem bracket_smul_right_of_anchor_eq_zero {A : LieAlgebroid I F V} (hA : A.anchor = 0)
    (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.bracket a (f • b) = f • A.bracket a b := by ext x; simp [hA]

/-- All Lie algebroid brackets are skew-symmetric: `bracket a b = -bracket b a`. -/
theorem bracket_swap (A : LieAlgebroid I F V) (a b : Cₛ^∞⟮I; F, V⟯) :
    A.bracket a b = -A.bracket b a := by
  have h := A.bracket_self (a + b)
  simp only [map_add, LinearMap.add_apply, A.bracket_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The Leibniz rule in the first argument: `[f • a, b] = f • [a, b] - (ρ(b) f) • a`. -/
theorem bracket_smul_left (A : LieAlgebroid I F V) (f : C^∞⟮I, M; ℝ⟯) (a b : Cₛ^∞⟮I; F, V⟯) :
    A.bracket (f • a) b = f • A.bracket a b - A.anchorDeriv b f • a := by
  rw [A.bracket_swap (f • a) b, A.bracket_smul_right, neg_add, ← smul_neg, ← A.bracket_swap,
    sub_eq_add_neg]

/-- When the anchor of a Lie algebroid vanishes, its bracket is `C^∞⟮I, M; ℝ⟯`-linear on the
left. -/
theorem bracket_smul_left_of_anchor_eq_zero {A : LieAlgebroid I F V} (hA : A.anchor = 0)
    (f : C^∞⟮I, M; ℝ⟯) (a b : Cₛ^∞⟮I; F, V⟯) :
    A.bracket (f • a) b = f • A.bracket a b := by ext x; simp [A.bracket_smul_left, hA]

section FiberwiseBracket

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- A smooth bundle of Lie algebras — a smooth section `B` of `V →L[ℝ] V →L[ℝ] V` that is fibrewise
alternating and satisfies the fibrewise Jacobi identity — forms a Lie algebroid with zero anchor and
pointwise bracket `(bracket a b) x = B x (a x) (b x)`. -/
def ofFiberwiseBracket (B : Cₛ^∞⟮I; F →L[ℝ] F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x →L[ℝ] V x⟯)
    (hself : ∀ (x : M) (v : V x), B x v v = 0)
    (hjacobi : ∀ (x : M) (u v w : V x), B x u (B x v w) = B x (B x u v) w + B x v (B x u w)) :
    LieAlgebroid I F V where
  anchor := 0
  bracket := LinearMap.mk₂ ℝ
    (fun a b ↦ ⟨fun x ↦ B x (a x) (b x),
      (B.contMDiff.clm_bundle_apply a.contMDiff).clm_bundle_apply b.contMDiff⟩)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by simp)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by simp)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by simp)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by simp)
  bracket_self a := ContMDiffSection.ext fun x ↦ hself x (a x)
  bracket_bracket a b c := ContMDiffSection.ext fun x ↦ hjacobi x (a x) (b x) (c x)
  bracket_smul_apply _ _ _ _ := by simp

section Simp

variable (B : Cₛ^∞⟮I; F →L[ℝ] F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x →L[ℝ] V x⟯)
  (hself : ∀ (x : M) (v : V x), B x v v = 0)
  (hjacobi : ∀ (x : M) (u v w : V x), B x u (B x v w) = B x (B x u v) w + B x v (B x u w))

@[simp] theorem ofFiberwiseBracket_anchor : (ofFiberwiseBracket B hself hjacobi).anchor = 0 := (rfl)

@[simp] theorem ofFiberwiseBracket_anchorField :
    (ofFiberwiseBracket B hself hjacobi).anchorField = 0 := by ext a x; simp

@[simp] theorem ofFiberwiseBracket_anchorDeriv (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (ofFiberwiseBracket B hself hjacobi).anchorDeriv a f = 0 := by ext x; simp

@[simp] theorem ofFiberwiseBracket_bracket_apply (a b : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (ofFiberwiseBracket B hself hjacobi).bracket a b x = B x (a x) (b x) := (rfl)

@[simp] theorem ofFiberwiseBracket_bracket_smul_left (f : C^∞⟮I, M; ℝ⟯) (a b : Cₛ^∞⟮I; F, V⟯) :
    (ofFiberwiseBracket B hself hjacobi).bracket (f • a) b =
      f • (ofFiberwiseBracket B hself hjacobi).bracket a b :=
  bracket_smul_left_of_anchor_eq_zero rfl f a b

end Simp

/-- Over a finite-dimensional Hausdorff base, the smooth fibrewise bracket `B` is uniquely
determined by the Lie algebroid `ofFiberwiseBracket B`. -/
theorem ofFiberwiseBracket_inj [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]
    {B₁ B₂ : Cₛ^∞⟮I; F →L[ℝ] F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x →L[ℝ] V x⟯}
    {hself₁ hjacobi₁ hself₂ hjacobi₂}
    (h : ofFiberwiseBracket B₁ hself₁ hjacobi₁ = ofFiberwiseBracket B₂ hself₂ hjacobi₂) :
    B₁ = B₂ := by
  ext x u v
  obtain ⟨a, ha, hax⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ u
  obtain ⟨b, hb, hbx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
  simpa [hax, hbx] using congr($(congrArg LieAlgebroid.bracket h) ⟨a, ha⟩ ⟨b, hb⟩ x)

end FiberwiseBracket

end ZeroAnchor

section TrivialLieAlgebra

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

omit [IsManifold I ∞ M] in
private theorem contMDiff_const_lieBracket :
    ContMDiff I
      (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤 →L[ℝ] Bundle.TrivialModel ℝ 𝔤 →L[ℝ]
        Bundle.TrivialModel ℝ 𝔤)) ∞
      (fun y ↦ TotalSpace.mk'
        (Bundle.TrivialModel ℝ 𝔤 →L[ℝ] Bundle.TrivialModel ℝ 𝔤 →L[ℝ] Bundle.TrivialModel ℝ 𝔤)
        (E := fun z ↦ Bundle.Trivial M 𝔤 z →L[ℝ] Bundle.Trivial M 𝔤 z →L[ℝ] Bundle.Trivial M 𝔤 z)
        y (LieAlgebra.ad ℝ 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).toContinuousBilinearMap) := fun x ↦ by
  rw [contMDiffAt_hom_bundle]
  let F := Bundle.TrivialModel ℝ 𝔤
  let μ := (LieAlgebra.ad ℝ 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).toContinuousBilinearMap
  refine ⟨contMDiffAt_id, (contMDiffAt_const (c := ContinuousLinearMap.inCoordinates F
    (Bundle.Trivial M 𝔤) (F →L[ℝ] F) (fun z ↦ Bundle.Trivial M 𝔤 z →L[ℝ] Bundle.Trivial M 𝔤 z)
    x x x x μ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ ?_)⟩
  ext v w; dsimp only [F, μ]
  rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp),
    inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
  simp

variable (I M 𝔤) in
/-- The trivial Lie algebra bundle algebroid `M × 𝔤 → M` of a finite-dimensional real Hausdorff
topological Lie algebra `𝔤`: zero anchor and pointwise Lie bracket `(bracket a b) x = ⁅a x, b x⁆`.
-/
def trivialLieAlgebra : LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
  ofFiberwiseBracket
    ⟨fun _ ↦ (LieAlgebra.ad ℝ 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).toContinuousBilinearMap,
      contMDiff_const_lieBracket⟩
    (fun _ ↦ lie_self) (fun _ ↦ leibniz_lie)

@[simp] theorem trivialLieAlgebra_anchor : (trivialLieAlgebra I M 𝔤).anchor = 0 := (rfl)

@[simp] theorem trivialLieAlgebra_anchorField : (trivialLieAlgebra I M 𝔤).anchorField = 0 :=
  ofFiberwiseBracket_anchorField _ _ _

@[simp] theorem trivialLieAlgebra_anchorDeriv
    (a : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (trivialLieAlgebra I M 𝔤).anchorDeriv a f = 0 :=
  ofFiberwiseBracket_anchorDeriv _ _ _ a f

@[simp] theorem trivialLieAlgebra_bracket_apply
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    (trivialLieAlgebra I M 𝔤).bracket a b x = ⁅a x, b x⁆ := (rfl)

@[simp] theorem trivialLieAlgebra_bracket_modelConst (ξ η : 𝔤) :
    (trivialLieAlgebra I M 𝔤).bracket (ContMDiffSection.modelConst I M ∞ ξ)
        (ContMDiffSection.modelConst I M ∞ η) = ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ := by
  ext x; simp

variable (I M 𝔤) in
/-- Evaluation at `x : M` as a Lie algebra homomorphism from sections of `M × 𝔤` to `𝔤`. -/
def trivialLieAlgebraEval (x : M) : (trivialLieAlgebra I M 𝔤).Sections →ₗ⁅ℝ⁆ 𝔤 where
  toFun s := (trivialLieAlgebra I M 𝔤).sectionsEquiv s x
  map_add' _ _ := by simp
  map_smul' _ _ := by rw [LinearMapClass.map_smul_of_tower]; rfl
  map_lie' := by intros; simp

@[simp] theorem trivialLieAlgebraEval_apply (x : M) (s : (trivialLieAlgebra I M 𝔤).Sections) :
    trivialLieAlgebraEval I M 𝔤 x s = (trivialLieAlgebra I M 𝔤).sectionsEquiv s x := (rfl)

variable (I M 𝔤) in
/-- Constant sections of `M × 𝔤` as a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ Γ(M × 𝔤)`. -/
def trivialLieAlgebraConst : 𝔤 →ₗ⁅ℝ⁆ (trivialLieAlgebra I M 𝔤).Sections where
  toFun ξ := (trivialLieAlgebra I M 𝔤).sectionsEquiv.symm (ContMDiffSection.modelConst I M ∞ ξ)
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by rw [map_smul, LinearMapClass.map_smul_of_tower]; rfl
  map_lie' := by intro _ _; exact (trivialLieAlgebra I M 𝔤).sectionsEquiv.injective (by simp)

@[simp] theorem sectionsEquiv_trivialLieAlgebraConst (ξ : 𝔤) :
    (trivialLieAlgebra I M 𝔤).sectionsEquiv (trivialLieAlgebraConst I M 𝔤 ξ) =
      ContMDiffSection.modelConst I M ∞ ξ :=
  (trivialLieAlgebra I M 𝔤).sectionsEquiv.apply_symm_apply _

theorem trivialLieAlgebraEval_trivialLieAlgebraConst (x : M) (ξ : 𝔤) :
    trivialLieAlgebraEval I M 𝔤 x (trivialLieAlgebraConst I M 𝔤 ξ) = ξ := by simp

theorem trivialLieAlgebraEval_surjective (x : M) :
    Function.Surjective (trivialLieAlgebraEval I M 𝔤 x) :=
  fun ξ ↦ ⟨trivialLieAlgebraConst I M 𝔤 ξ, trivialLieAlgebraEval_trivialLieAlgebraConst x ξ⟩

theorem trivialLieAlgebraConst_injective [Nonempty M] :
    Function.Injective (trivialLieAlgebraConst I M 𝔤) := by
  obtain ⟨x⟩ := ‹Nonempty M›
  exact Function.RightInverse.injective (trivialLieAlgebraEval_trivialLieAlgebraConst x)

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Pullback of sections of `trivialLieAlgebra` along a smooth map `φ : N → M`, as a Lie algebra
homomorphism. -/
def trivialLieAlgebraPullback (φ : C^∞⟮J, N; I, M⟯) :
    (trivialLieAlgebra I M 𝔤).Sections →ₗ⁅ℝ⁆ (trivialLieAlgebra J N 𝔤).Sections where
  toFun s := (trivialLieAlgebra J N 𝔤).sectionsEquiv.symm <|
    ContMDiffSection.modelPullback φ ((trivialLieAlgebra I M 𝔤).sectionsEquiv s)
  map_add' _ _ := (trivialLieAlgebra J N 𝔤).sectionsEquiv.injective <| by ext y; simp
  map_smul' _ _ := (trivialLieAlgebra J N 𝔤).sectionsEquiv.injective <| by
    rw [LinearMapClass.map_smul_of_tower, LinearEquiv.apply_symm_apply,
      LinearMapClass.map_smul_of_tower]; ext y; simp
  map_lie' := by
    intro _ _; exact (trivialLieAlgebra J N 𝔤).sectionsEquiv.injective (by ext y; simp)

@[simp] theorem sectionsEquiv_trivialLieAlgebraPullback_apply (φ : C^∞⟮J, N; I, M⟯)
    (s : (trivialLieAlgebra I M 𝔤).Sections) (y : N) :
    (trivialLieAlgebra J N 𝔤).sectionsEquiv (trivialLieAlgebraPullback φ s) y =
      (trivialLieAlgebra I M 𝔤).sectionsEquiv s (φ y) := by
  simp [trivialLieAlgebraPullback]

end Pullback

end TrivialLieAlgebra

end LieAlgebroid

end TauCeti
