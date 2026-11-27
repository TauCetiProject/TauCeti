/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Zero-anchor Lie algebroids from bundles of Lie algebras

A Lie algebroid with zero anchor is totally intransitive: its Leibniz rule reduces to
`C^∞(M)`-bilinearity of the bracket (`TauCeti.LieAlgebroid.bracket_smul_right_of_anchor_eq_zero`,
`TauCeti.LieAlgebroid.bracket_smul_left_of_anchor_eq_zero`), so the bracket is purely fibrewise.
Concretely, a smooth real vector bundle `V → M` equipped with a smooth fibrewise alternating Jacobi
section `B` of `V →L[ℝ] V →L[ℝ] V` is a zero-anchor Lie algebroid
(`TauCeti.LieAlgebroid.ofFiberwiseBracket`). Specializing to `Bundle.Trivial M 𝔤` gives the
trivial Lie algebra bundle algebroid (`trivialLieAlgebra`, the zero-action base case of
transformation Lie algebroids), together with evaluation (`trivialLieAlgebraEval`), constant
sections (`trivialLieAlgebraConst`), and pullback (`trivialLieAlgebraPullback`) (Mackenzie 2005,
§3.3).

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
-/

public section
noncomputable section

open Bundle Manifold
open scoped ContDiff

namespace TauCeti.LieAlgebroid
section FiberwiseBracket
variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- A smooth bundle of Lie algebras — a smooth fibrewise alternating Jacobi section `B` of
`V →L[ℝ] V →L[ℝ] V` — forms a zero-anchor Lie algebroid with `(bracket a b) x = B x (a x) (b x)`. -/
def ofFiberwiseBracket (B : Cₛ^∞⟮I; F →L[ℝ] F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x →L[ℝ] V x⟯)
    (hself : ∀ (x : M) (v : V x), B x v v = 0)
    (hjacobi : ∀ (x : M) (u v w : V x), B x u (B x v w) = B x (B x u v) w + B x v (B x u w)) :
    LieAlgebroid I F V :=
  ⟨0, LinearMap.mk₂ ℝ (fun a b ↦ ⟨fun x ↦ B x (a x) (b x),
      (B.contMDiff.clm_bundle_apply a.contMDiff).clm_bundle_apply b.contMDiff⟩)
    (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp),
    fun a ↦ ContMDiffSection.ext fun x ↦ hself x (a x),
    fun a b c ↦ ContMDiffSection.ext fun x ↦ hjacobi x (a x) (b x) (c x),
    fun _ _ _ _ ↦ by simp⟩

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

theorem ofFiberwiseBracket_bracket_smul_left (f : C^∞⟮I, M; ℝ⟯) (a b : Cₛ^∞⟮I; F, V⟯) :
    (ofFiberwiseBracket B hself hjacobi).bracket (f • a) b =
      f • (ofFiberwiseBracket B hself hjacobi).bracket a b :=
  bracket_smul_left_of_anchor_eq_zero rfl f a b

end Simp

/-- Over a finite-dimensional Hausdorff base, two smooth fibrewise brackets define the same Lie
algebroid if and only if they are equal. -/
theorem ofFiberwiseBracket_inj [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]
    {B₁ B₂ : Cₛ^∞⟮I; F →L[ℝ] F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x →L[ℝ] V x⟯}
    {hself₁ hjacobi₁ hself₂ hjacobi₂} :
    ofFiberwiseBracket B₁ hself₁ hjacobi₁ = ofFiberwiseBracket B₂ hself₂ hjacobi₂ ↔ B₁ = B₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩; ext x u v
  obtain ⟨a, ha, hax⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ u
  obtain ⟨b, hb, hbx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
  simpa [hax, hbx] using congr($(congrArg LieAlgebroid.bracket h) ⟨a, ha⟩ ⟨b, hb⟩ x)

end FiberwiseBracket

section TrivialLieAlgebra
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

variable (I M 𝔤) in
/-- The trivial Lie algebra bundle algebroid `M × 𝔤 → M` of a finite-dimensional real Hausdorff
topological Lie algebra `𝔤`, with zero anchor and `(bracket a b) x = ⁅a x, b x⁆`. -/
def trivialLieAlgebra : LieAlgebroid I (TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
  ofFiberwiseBracket
    ⟨fun _ ↦ (LieAlgebra.ad ℝ 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).toContinuousBilinearMap,
      contMDiff_hom_bundle_of_inCoordinates_eq_const
        (c := fun a ↦ ContinuousLinearMap.inCoordinates (TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤)
          (TrivialModel ℝ 𝔤 →L[ℝ] TrivialModel ℝ 𝔤)
          (fun z ↦ Bundle.Trivial M 𝔤 z →L[ℝ] Bundle.Trivial M 𝔤 z) a a a a
          (LieAlgebra.ad ℝ 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).toContinuousBilinearMap)
        fun _ _ _ _ ↦ by
          ext v w; rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp),
            inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]; simp [Bundle.Trivial]⟩
    (fun _ ↦ lie_self) (fun _ ↦ leibniz_lie)

@[simp] theorem trivialLieAlgebra_anchor : (trivialLieAlgebra I M 𝔤).anchor = 0 := (rfl)

@[simp] theorem trivialLieAlgebra_anchorField : (trivialLieAlgebra I M 𝔤).anchorField = 0 :=
  ofFiberwiseBracket_anchorField _ _ _

@[simp] theorem trivialLieAlgebra_anchorDeriv
    (a : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (trivialLieAlgebra I M 𝔤).anchorDeriv a f = 0 := ofFiberwiseBracket_anchorDeriv _ _ _ a f

@[simp] theorem trivialLieAlgebra_bracket_apply
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    (trivialLieAlgebra I M 𝔤).bracket a b x = ⁅a x, b x⁆ := (rfl)

@[simp] theorem trivialLieAlgebra_bracket_modelConst (ξ η : 𝔤) :
    (trivialLieAlgebra I M 𝔤).bracket (ContMDiffSection.modelConst I M ∞ ξ)
        (ContMDiffSection.modelConst I M ∞ η) = ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ :=
  ContMDiffSection.ext fun _ ↦ by simp

variable (I M 𝔤) in
/-- Evaluation at `x : M` as a Lie algebra homomorphism from sections of `M × 𝔤` to `𝔤`. -/
def trivialLieAlgebraEval (x : M) : (trivialLieAlgebra I M 𝔤).Sections →ₗ⁅ℝ⁆ 𝔤 :=
  { ((ContMDiffSection.evalLinearMap I (TrivialModel ℝ 𝔤) ∞ (Bundle.Trivial M 𝔤) x).restrictScalars
      ℝ).comp ((trivialLieAlgebra I M 𝔤).sectionsEquiv.restrictScalars ℝ).toLinearMap with
    map_lie' {_ _} := by simp }

@[simp] theorem trivialLieAlgebraEval_apply (x : M) (s : (trivialLieAlgebra I M 𝔤).Sections) :
    trivialLieAlgebraEval I M 𝔤 x s = (trivialLieAlgebra I M 𝔤).sectionsEquiv s x := by
  rw [← LieHom.coe_toLinearMap]; simp [trivialLieAlgebraEval]

variable (I M 𝔤) in
/-- Constant sections of `M × 𝔤` as a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ Γ(M × 𝔤)`. -/
def trivialLieAlgebraConst : 𝔤 →ₗ⁅ℝ⁆ (trivialLieAlgebra I M 𝔤).Sections :=
  { ((trivialLieAlgebra I M 𝔤).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp
      (ContMDiffSection.modelConst I M ∞) with
    map_lie' {_ _} := (trivialLieAlgebra I M 𝔤).sectionsEquiv.injective (by simp) }

@[simp] theorem sectionsEquiv_trivialLieAlgebraConst (ξ : 𝔤) :
    (trivialLieAlgebra I M 𝔤).sectionsEquiv (trivialLieAlgebraConst I M 𝔤 ξ) =
      ContMDiffSection.modelConst I M ∞ ξ := by
  rw [← LieHom.coe_toLinearMap]; simp [trivialLieAlgebraConst]

theorem trivialLieAlgebraEval_trivialLieAlgebraConst (x : M) (ξ : 𝔤) :
    trivialLieAlgebraEval I M 𝔤 x (trivialLieAlgebraConst I M 𝔤 ξ) = ξ := by simp

theorem trivialLieAlgebraEval_surjective (x : M) :
    Function.Surjective (trivialLieAlgebraEval I M 𝔤 x) :=
  fun ξ ↦ ⟨trivialLieAlgebraConst I M 𝔤 ξ, trivialLieAlgebraEval_trivialLieAlgebraConst x ξ⟩

theorem trivialLieAlgebraConst_injective [Nonempty M] :
    Function.Injective (trivialLieAlgebraConst I M 𝔤) :=
  let ⟨x⟩ := ‹Nonempty M›
  Function.RightInverse.injective (trivialLieAlgebraEval_trivialLieAlgebraConst x)

variable {E' H' N E'' H'' P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

/-- Pullback of sections of `trivialLieAlgebra` along a smooth map `φ : N → M`. -/
def trivialLieAlgebraPullback (φ : C^∞⟮J, N; I, M⟯) :
    (trivialLieAlgebra I M 𝔤).Sections →ₗ⁅ℝ⁆ (trivialLieAlgebra J N 𝔤).Sections :=
  { (((trivialLieAlgebra J N 𝔤).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp <|
      (ContMDiffSection.modelPullback φ).comp
        ((trivialLieAlgebra I M 𝔤).sectionsEquiv.restrictScalars ℝ).toLinearMap) with
    map_lie' {_ _} := (trivialLieAlgebra J N 𝔤).sectionsEquiv.injective (by ext y; simp) }

@[simp] theorem sectionsEquiv_trivialLieAlgebraPullback_apply (φ : C^∞⟮J, N; I, M⟯)
    (s : (trivialLieAlgebra I M 𝔤).Sections) (y : N) :
    (trivialLieAlgebra J N 𝔤).sectionsEquiv (trivialLieAlgebraPullback φ s) y =
      (trivialLieAlgebra I M 𝔤).sectionsEquiv s (φ y) := by
  rw [← LieHom.coe_toLinearMap]; simp [trivialLieAlgebraPullback]

@[simp] theorem trivialLieAlgebraPullback_smul (φ : C^∞⟮J, N; I, M⟯) (f : C^∞⟮I, M; ℝ⟯)
    (s : (trivialLieAlgebra I M 𝔤).Sections) :
    trivialLieAlgebraPullback (𝔤 := 𝔤) φ (f • s) = f.comp φ • trivialLieAlgebraPullback φ s :=
  (trivialLieAlgebra J N 𝔤).sectionsEquiv.injective <| by ext y; simp

@[simp] theorem trivialLieAlgebraPullback_trivialLieAlgebraConst (φ : C^∞⟮J, N; I, M⟯) (ξ : 𝔤) :
    trivialLieAlgebraPullback φ (trivialLieAlgebraConst I M 𝔤 ξ) =
      trivialLieAlgebraConst J N 𝔤 ξ :=
  (trivialLieAlgebra J N 𝔤).sectionsEquiv.injective <| by ext y; simp

@[simp] theorem trivialLieAlgebraPullback_id :
    trivialLieAlgebraPullback (𝔤 := 𝔤) (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) = LieHom.id := by
  ext s; exact (trivialLieAlgebra I M 𝔤).sectionsEquiv.injective (by ext x; simp; rfl)

theorem trivialLieAlgebraPullback_comp (φ : C^∞⟮J, N; I, M⟯) (ψ : C^∞⟮K, P; J, N⟯) :
    trivialLieAlgebraPullback (𝔤 := 𝔤) (φ.comp ψ) =
      (trivialLieAlgebraPullback ψ).comp (trivialLieAlgebraPullback φ) := by
  ext s; exact (trivialLieAlgebra K P 𝔤).sectionsEquiv.injective (by ext z; simp)

end TrivialLieAlgebra
end TauCeti.LieAlgebroid
