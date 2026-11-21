/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AffineLine
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.LieAlgebroid.LieAlgebraBundle
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Action (transformation) Lie algebroids

Given a finite-dimensional real Hausdorff topological Lie algebra `𝔤` and a Lie algebra
homomorphism `α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections`, `Bundle.Trivial M 𝔤` carries the
**transformation Lie algebroid** `TauCeti.LieAlgebroid.transformation α` (Mackenzie 2005, §3.3;
Crainic–Fernandes 2011, Ex. 1.6). Over a Hausdorff base, `transformationBracket_jacobi_iff` shows
that the Jacobi identity holds if and only if the underlying linear map intertwines brackets.

Because a `TauCeti.InfinitesimalAction` is a Lie algebra antihomomorphism (`act ⁅ξ, η⁆ = -[act ξ,
act η]`), negating it (`InfinitesimalAction.negLieHom`) yields a Lie algebra homomorphism into
`(tangent I M).Sections` and hence the transformation Lie algebroids
`InfinitesimalAction.lieAlgebroid` and `ofMulAction`, whereas omitting the minus sign violates the
Jacobi identity (`not_transformationBracket_jacobi_toSectionLinearMap_affineLine`). When an abelian
Lie algebra `𝔤` acts on a finite-dimensional real normed space `V` by translations along a linear
equivalence `τ : 𝔤 ≃ₗ[ℝ] V`, the anchor identifies the section Lie algebra with
`(tangent 𝓘(ℝ, V) V).Sections` (`translationSectionsLieEquiv`).

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107, Example 1.6.
-/
public section
noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff

namespace TauCeti
namespace LieAlgebroid
section LinearPreAlgebroid
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
  (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

/-- Smooth anchor bundle morphism `(x, ξ) ↦ α₀ ξ x` on `Bundle.Trivial M 𝔤`. -/
def transformationAnchor :
    Cₛ^∞⟮I; TrivialModel ℝ 𝔤 →L[ℝ] E, fun x ↦ Bundle.Trivial M 𝔤 x →L[ℝ] TangentSpace I x⟯ :=
  let anchorLin (x : M) : Bundle.Trivial M 𝔤 x →ₗ[ℝ] TangentSpace I x :=
    ⟨⟨fun ξ ↦ α₀ ξ x, fun _ _ ↦ by simp⟩, fun _ _ ↦ by simp⟩
  ⟨fun x ↦ LinearMap.toContinuousLinearMap (anchorLin x), by
    have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
    rw [contMDiff_hom_bundle_iff]; let B := Module.finBasis ℝ 𝔤; let e := TrivialModel.equiv ℝ 𝔤
    let hproj := contMDiff_proj (IB := I) (n := ∞) (F := TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤)
    let hsnd := (TrivialModel.contMDiff_mk_iff.1 (contMDiff_id (I := I.prod 𝓘(ℝ, TrivialModel ℝ 𝔤))
      (M := TotalSpace (TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤)) (n := ∞))).2
    refine (ContMDiff.sum_sectionAlong (V := TangentSpace I) (b := TotalSpace.proj) Finset.univ
      (fun i p ↦ B.coord i p.snd • α₀ (B i) p.proj) hproj fun i _ ↦
        (((LinearMap.toContinuousLinearMap ((B.coord i).comp e.symm.toLinearMap)).contMDiff.comp
          hsnd).congr fun _ ↦ by simp [e]).smul_totalSpace ((α₀ (B i)).contMDiff.comp hproj)).congr
      fun p ↦ congrArg (TotalSpace.mk' E p.proj) ?_
    simp only [LinearMap.coe_toContinuousLinearMap']; conv_lhs => rw [← B.sum_repr p.snd]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ by simp [anchorLin]⟩

@[simp] theorem transformationAnchor_apply (x : M) (ξ : 𝔤) :
    transformationAnchor α₀ x ξ = α₀ ξ x := (rfl)

/-- Smooth tangent vector field `x ↦ α₀ (a x) x` induced by a smooth section `a` of
`Bundle.Trivial M 𝔤`, linear over `C^∞⟮I, M; ℝ⟯`. -/
def transformationAnchorField : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  have h := (contMDiff_hom_bundle_iff _).1 (transformationAnchor α₀).contMDiff
  ⟨(ContMDiffSection.mapLinearMap (fun x ↦ (transformationAnchor α₀ x).toLinearMap) h).toAddHom,
    ContMDiffSection.mapLinearMap_smul_function _ h⟩

@[simp] theorem transformationAnchorField_apply
    (a : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    transformationAnchorField α₀ a x = α₀ (a x) x := by simp [transformationAnchorField]

@[simp] theorem transformationAnchorField_modelConst (ξ : 𝔤) :
    transformationAnchorField α₀ (ContMDiffSection.modelConst I M ∞ ξ) = α₀ ξ := by ext x; simp

private theorem infty_add_one_le : (∞ : ℕ∞ω) + 1 ≤ ∞ := by simp

/-- The transformation section bracket on `Bundle.Trivial M 𝔤` attached to `α₀`:
`[a, b](x) = ⁅a x, b x⁆ + b.modelDeriv x (α₀ (a x) x) - a.modelDeriv x (α₀ (b x) x)`. -/
def transformationBracket : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[ℝ]
    Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[ℝ]
    Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ :=
  LinearMap.mk₂ ℝ
    (fun a b ↦ (trivialLieAlgebra I M 𝔤).bracket a b +
      ContMDiffSection.modelLieDeriv (transformationAnchorField α₀ a) b infty_add_one_le -
      ContMDiffSection.modelLieDeriv (transformationAnchorField α₀ b) a infty_add_one_le)
    (fun _ _ _ ↦ by ext; simp; abel) (fun _ _ _ ↦ by ext; simp [smul_add, smul_sub])
    (fun _ _ _ ↦ by ext; simp; abel) (fun _ _ _ ↦ by ext; simp [smul_add, smul_sub])

@[simp] theorem transformationBracket_apply
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    transformationBracket α₀ a b x =
      ⁅a x, b x⁆ + b.modelDeriv x (α₀ (a x) x) - a.modelDeriv x (α₀ (b x) x) := by
  simp [transformationBracket]

@[simp] theorem transformationBracket_self (a : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a a = 0 := by ext x; simp

theorem transformationBracket_swap (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a b = -transformationBracket α₀ b a := by
  ext x; simp only [transformationBracket_apply, ContMDiffSection.coe_neg, Pi.neg_apply,
    ← lie_skew (a x) (b x)]; abel

theorem transformationBracket_smul_apply
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    transformationBracket α₀ a (f • b) x = f x • transformationBracket α₀ a b x +
      mvfderiv I f x (transformationAnchor α₀ x (a x)) • b x := by
  simp [smul_add, smul_sub]; abel

@[simp] theorem transformationBracket_modelConst (ξ η : 𝔤) :
    transformationBracket α₀ (ContMDiffSection.modelConst I M ∞ ξ)
      (ContMDiffSection.modelConst I M ∞ η) = ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ := by
  ext x; simp

end LinearPreAlgebroid

section Homomorphism
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

section GeneralLieAlgebra
variable (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections)

private def toTangentLinearMap : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ((tangent I M).sectionsEquiv.restrictScalars ℝ).toLinearMap.comp α.toLinearMap

private theorem toTangentLinearMap_lie (ξ η : 𝔤) : toTangentLinearMap α ⁅ξ, η⁆ =
    (tangent I M).bracket (toTangentLinearMap α ξ) (toTangentLinearMap α η) := by
  simp [toTangentLinearMap]

/-- The **isotropy Lie subalgebra** `{ξ ∈ 𝔤 | α ξ x = 0} ≤ 𝔤` at `x : M`. -/
def transformationIsotropy (x : M) : LieSubalgebra ℝ 𝔤 :=
  { LinearMap.ker
      ((ContMDiffSection.evalLinearMap I E ∞ (TangentSpace I) x).comp (toTangentLinearMap α)) with
    lie_mem' hξ hη := by
      simpa [toTangentLinearMap] using mlieBracket_eq_zero_of_eq_zero
        (by simpa [toTangentLinearMap] using hξ) (by simpa [toTangentLinearMap] using hη) }

@[simp] theorem mem_transformationIsotropy_iff (x : M) {ξ : 𝔤} :
    ξ ∈ transformationIsotropy α x ↔ (tangent I M).sectionsEquiv (α ξ) x = 0 := by
  simp [transformationIsotropy, toTangentLinearMap]

@[simp] theorem transformationIsotropy_comp {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤) (x : M) :
    transformationIsotropy (α.comp ψ) x = (transformationIsotropy α x).comap ψ :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

end GeneralLieAlgebra

variable [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤]
  [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

@[simp] theorem transformationBracket_smul_right
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (f : C^∞⟮I, M; ℝ⟯) :
    transformationBracket α₀ a (f • b) = f • transformationBracket α₀ a b +
      (tangent I M).anchorDeriv (transformationAnchorField α₀ a) f • b := by
  ext x; simp [smul_add, smul_sub]; abel

/-- Whenever `α₀` intertwines Lie brackets (without requiring `T2Space M`),
`transformationAnchorField α₀` intertwines `transformationBracket α₀` with the tangent Lie
bracket. -/
theorem transformationAnchorField_transformationBracket
    {α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hα : ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η))
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationAnchorField α₀ (transformationBracket α₀ a b) =
      (tangent I M).bracket (transformationAnchorField α₀ a) (transformationAnchorField α₀ b) := by
  let P u v := transformationAnchorField α₀ (transformationBracket α₀ u v) =
    (tangent I M).bracket (transformationAnchorField α₀ u) (transformationAnchorField α₀ v)
  have hr {u v} (h : P u v) (g : C^∞⟮I, M; ℝ⟯) : P u (g • v) := by
    dsimp only [P] at h ⊢; rw [transformationBracket_smul_right, map_add, map_smul, map_smul,
      map_smul, (tangent I M).bracket_smul_right, h]
  have hswap {u v} (h : P u v) : P v u := by
    dsimp only [P] at h ⊢; rw [transformationBracket_swap α₀ v u, map_neg, h,
      (tangent I M).bracket_swap, neg_neg]
  let B := Module.finBasis ℝ 𝔤
  rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B a,
    ContMDiffSection.eq_sum_modelCoord_smul_modelConst B b]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    hswap (hr (hswap (hr (by dsimp only [P]; simp [hα]) _)) _)

/-- Whenever `α₀` intertwines Lie brackets (without requiring `T2Space M`),
`transformationBracket α₀` satisfies the Jacobi identity. -/
theorem transformationBracket_jacobi {α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hα : ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η))
    (a b c : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a (transformationBracket α₀ b c) =
      transformationBracket α₀ (transformationBracket α₀ a b) c +
        transformationBracket α₀ b (transformationBracket α₀ a c) := by
  let br := transformationBracket α₀
  let J (u v w : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :=
    br u (br v w) - br (br u v) w - br v (br u w)
  have hJ_smul₃ (u v w) (f : C^∞⟮I, M; ℝ⟯) : J u v (f • w) = f • J u v w := by
    simp only [J, br, transformationBracket_smul_right, map_add,
      transformationAnchorField_transformationBracket hα u v, tangent_anchorDeriv_bracket]; module
  have hJ_swap₁₂ (u v w) : J v u w = -J u v w := by
    simp only [J, br]; rw [transformationBracket_swap α₀ v u, map_neg, LinearMap.neg_apply]; abel
  have hJ_swap₂₃ (u v w) : J u w v = -J u v w := by
    simp only [J, br]; rw [transformationBracket_swap α₀ w v, map_neg,
      transformationBracket_swap α₀ (transformationBracket α₀ u w) v,
      transformationBracket_swap α₀ w (transformationBracket α₀ u v)]; abel
  have hJ_smul₂ (u v w) (f : C^∞⟮I, M; ℝ⟯) : J u (f • v) w = f • J u v w := by
    rw [hJ_swap₂₃ u w (f • v), hJ_smul₃ u w v f, hJ_swap₂₃ u v w]; ext x; simp
  have hJ_smul₁ (u v w) (f : C^∞⟮I, M; ℝ⟯) : J (f • u) v w = f • J u v w := by
    rw [hJ_swap₁₂ v (f • u) w, hJ_smul₂ v u w f, hJ_swap₁₂ u v w]; ext x; simp
  let B := Module.finBasis ℝ 𝔤; let S := Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯
  have vanish {P : S → S} (ha : ∀ x y, P (x + y) = P x + P y)
      (hs : ∀ (f : C^∞⟮I, M; ℝ⟯) x, P (f • x) = f • P x)
      (hB : ∀ i, P (ContMDiffSection.modelConst I M ∞ (B i)) = 0) (s) : P s = 0 := by
    let P' : S →ₗ[C^∞⟮I, M; ℝ⟯] S := ⟨⟨P, ha⟩, hs⟩
    suffices P' s = 0 by simpa only [P', LinearMap.coe_mk, AddHom.coe_mk] using this
    rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B s, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by
      simp only [map_smul, P', LinearMap.coe_mk, AddHom.coe_mk, hB i]; ext x; simp [S]
  have hJ₁ (ξ η : 𝔤) (w) :
      J (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η) w = 0 :=
    vanish (fun _ _ ↦ by simp only [J, map_add]; abel) (fun f x ↦ hJ_smul₃ _ _ x f)
      (fun _ ↦ by ext x; simp [J, br]) w
  have hJ₂ (ξ : 𝔤) (v w) : J (ContMDiffSection.modelConst I M ∞ ξ) v w = 0 :=
    vanish (P := fun v ↦ J (ContMDiffSection.modelConst I M ∞ ξ) v w)
      (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel)
      (fun f x ↦ hJ_smul₂ _ x w f) (fun j ↦ hJ₁ ξ (B j) w) v
  have hJ_zero : J a b c = 0 := vanish (P := fun u ↦ J u b c)
    (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel)
    (fun f x ↦ hJ_smul₁ x b c f) (fun i ↦ hJ₂ (B i) b c) a
  dsimp only [J, br] at hJ_zero; rwa [sub_eq_zero, sub_eq_iff_eq_add, add_comm] at hJ_zero

/-- Over a Hausdorff base, `transformationBracket α₀` satisfies the Jacobi identity if and only if
`α₀` intertwines Lie brackets. -/
theorem transformationBracket_jacobi_iff [T2Space M]
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (∀ a b c, transformationBracket α₀ a (transformationBracket α₀ b c) =
        transformationBracket α₀ (transformationBracket α₀ a b) c +
          transformationBracket α₀ b (transformationBracket α₀ a c)) ↔
      ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η) := by
  refine ⟨fun hjac ξ η ↦ ?_, transformationBracket_jacobi⟩
  let A : LieAlgebroid I (TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
    ⟨transformationAnchor α₀, transformationBracket α₀, transformationBracket_self α₀, hjac,
      transformationBracket_smul_apply α₀⟩
  ext x; have hc (ζ) : ⇑(A.anchorField (ContMDiffSection.modelConst I M ∞ ζ)) = ⇑(α₀ ζ) :=
    funext fun _ ↦ by simp [A]
  simpa [A, hc] using A.anchor_bracket (ContMDiffSection.modelConst I M ∞ ξ)
    (ContMDiffSection.modelConst I M ∞ η) x

section LieHom
variable (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections)

/-- The **transformation** (or **action**) **Lie algebroid** `M ⋉ 𝔤` on `Bundle.Trivial M 𝔤`
associated with a Lie algebra homomorphism `α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections`. -/
def transformation : LieAlgebroid I (TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
  ⟨transformationAnchor (toTangentLinearMap α), transformationBracket (toTangentLinearMap α),
    transformationBracket_self (toTangentLinearMap α),
    transformationBracket_jacobi (toTangentLinearMap_lie α),
    transformationBracket_smul_apply (toTangentLinearMap α)⟩

@[simp] theorem transformation_anchor_apply (x : M) (ξ : 𝔤) :
    (transformation α).anchor x ξ = (tangent I M).sectionsEquiv (α ξ) x := by
  simp [transformation, toTangentLinearMap]

@[simp] theorem transformation_anchorField_modelConst (ξ : 𝔤) :
    (transformation α).anchorField (ContMDiffSection.modelConst I M ∞ ξ) =
      (tangent I M).sectionsEquiv (α ξ) := by ext x; simp

@[simp] theorem transformation_bracket_apply
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    (transformation α).bracket a b x =
      ⁅a x, b x⁆ + b.modelDeriv x ((tangent I M).sectionsEquiv (α (a x)) x) -
        a.modelDeriv x ((tangent I M).sectionsEquiv (α (b x)) x) := by
  simp [transformation, toTangentLinearMap]

@[simp] theorem transformation_bracket_modelConst (ξ η : 𝔤) :
    (transformation α).bracket (ContMDiffSection.modelConst I M ∞ ξ)
      (ContMDiffSection.modelConst I M ∞ η) = ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ :=
  transformationBracket_modelConst (toTangentLinearMap α) ξ η

@[simp] theorem transformation_zero :
    transformation (0 : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) = trivialLieAlgebra I M 𝔤 :=
  LieAlgebroid.ext (by ext; simp) (by ext; simp)

/-- Constant sections define a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections`. -/
def transformationConst : 𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections :=
  { ((transformation α).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp
      (ContMDiffSection.modelConst I M ∞) with
    map_lie' {_ _} := (transformation α).sectionsEquiv.injective (by simp) }

@[simp] theorem sectionsEquiv_transformationConst (ξ : 𝔤) :
    (transformation α).sectionsEquiv (transformationConst α ξ) =
      ContMDiffSection.modelConst I M ∞ ξ := by
  rw [← LieHom.coe_toLinearMap]; simp [transformationConst]

theorem transformationConst_injective [Nonempty M] :
    Function.Injective (transformationConst α) := fun _ _ h ↦
  ContMDiffSection.modelConst_injective (by simpa using congrArg (transformation α).sectionsEquiv h)

/-- The anchor of `transformation α` on sections as a Lie algebra homomorphism into
`(tangent I M).Sections` (without requiring `M` to be Hausdorff). -/
def transformationAnchorHom : (transformation α).Sections →ₗ⁅ℝ⁆ (tangent I M).Sections :=
  (transformation α).anchorLieHomOfBracket fun a b ↦ by
    have hField (u) : (transformation α).anchorField u =
        transformationAnchorField (toTangentLinearMap α) u := by ext x; simp [toTangentLinearMap]
    rw [hField, hField, hField]
    exact transformationAnchorField_transformationBracket (toTangentLinearMap_lie α) a b

@[simp] theorem sectionsEquiv_transformationAnchorHom (s : (transformation α).Sections) :
    (tangent I M).sectionsEquiv (transformationAnchorHom α s) =
      (transformation α).anchorField ((transformation α).sectionsEquiv s) :=
  (transformation α).sectionsEquiv_anchorLieHomOfBracket _ s

@[simp] theorem transformationAnchorHom_smul (f : C^∞⟮I, M; ℝ⟯) (s : (transformation α).Sections) :
    transformationAnchorHom α (f • s) = f • transformationAnchorHom α s :=
  (transformation α).anchorLieHomOfBracket_smul _ f s

@[simp] theorem transformationAnchorHom_lie [T2Space M]
    (s : (transformation α).Sections) (f : C^∞⟮I, M; ℝ⟯) :
    ⁅transformationAnchorHom α s, f⁆ = ⁅s, f⁆ :=
  (transformation α).anchorLieHomOfBracket_lie _ s f

@[simp] theorem transformationAnchorHom_comp_transformationConst :
    (transformationAnchorHom α).comp (transformationConst α) = α := by
  ext ξ; exact (tangent I M).sectionsEquiv.injective (by simp)

theorem transformationIsotropy_toSubmodule (x : M) :
    (transformationIsotropy α x).toSubmodule =
      LinearMap.ker ((transformation α).anchor x).toLinearMap := Submodule.ext fun _ ↦ by simp

variable {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] [TopologicalSpace 𝔥]
  [IsTopologicalAddGroup 𝔥] [ContinuousSMul ℝ 𝔥] [T2Space 𝔥] [FiniteDimensional ℝ 𝔥]
  (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤)

/-- Pushforward of sections along a Lie algebra homomorphism `ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤`. -/
def transformationMapLieHom :
    (transformation (α.comp ψ)).Sections →ₗ⁅ℝ⁆ (transformation α).Sections :=
  { (((transformation α).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp <|
      ((ContMDiffSection.modelMap ψ.toLinearMap).restrictScalars ℝ).comp
        ((transformation (α.comp ψ)).sectionsEquiv.restrictScalars ℝ).toLinearMap) with
    map_lie' {_ _} := (transformation α).sectionsEquiv.injective (by ext x; simp) }

@[simp] theorem sectionsEquiv_transformationMapLieHom_apply
    (s : (transformation (α.comp ψ)).Sections) (x : M) :
    (transformation α).sectionsEquiv (transformationMapLieHom α ψ s) x =
      ψ ((transformation (α.comp ψ)).sectionsEquiv s x) := by
  rw [← LieHom.coe_toLinearMap]; simp [transformationMapLieHom]

@[simp] theorem transformationMapLieHom_smul (f : C^∞⟮I, M; ℝ⟯)
    (s : (transformation (α.comp ψ)).Sections) :
    transformationMapLieHom α ψ (f • s) = f • transformationMapLieHom α ψ s :=
  (transformation α).sectionsEquiv.injective (by ext x; simp)

@[simp] theorem transformationMapLieHom_transformationConst (ξ : 𝔥) :
    transformationMapLieHom α ψ (transformationConst (α.comp ψ) ξ) =
      transformationConst α (ψ ξ) :=
  (transformation α).sectionsEquiv.injective (by ext x; simp)

@[simp] theorem transformationMapLieHom_id :
    transformationMapLieHom α (LieHom.id : 𝔤 →ₗ⁅ℝ⁆ 𝔤) = LieHom.id :=
  LieHom.ext fun s ↦ (transformation α).sectionsEquiv.injective <| ContMDiffSection.ext fun x ↦
    (sectionsEquiv_transformationMapLieHom_apply α LieHom.id s x).trans <| (LieHom.id_apply _).trans
      (congrArg (fun t ↦ (transformation α).sectionsEquiv t x) (LieHom.id_apply s).symm)

theorem transformationMapLieHom_comp {𝔨 : Type*} [LieRing 𝔨] [LieAlgebra ℝ 𝔨]
    [TopologicalSpace 𝔨] [IsTopologicalAddGroup 𝔨] [ContinuousSMul ℝ 𝔨] [T2Space 𝔨]
    [FiniteDimensional ℝ 𝔨] (χ : 𝔨 →ₗ⁅ℝ⁆ 𝔥) :
    transformationMapLieHom α (ψ.comp χ) =
      (transformationMapLieHom α ψ).comp (transformationMapLieHom (α.comp ψ) χ) :=
  LieHom.ext fun s ↦ (transformation α).sectionsEquiv.injective <| ContMDiffSection.ext fun x ↦
    (sectionsEquiv_transformationMapLieHom_apply α (ψ.comp χ) s x).trans <|
      ((sectionsEquiv_transformationMapLieHom_apply α ψ _ x).trans
        (congrArg ψ (sectionsEquiv_transformationMapLieHom_apply (α.comp ψ) χ s x))).symm

@[simp] theorem transformationAnchorHom_comp_transformationMapLieHom :
    (transformationAnchorHom α).comp (transformationMapLieHom α ψ) =
      transformationAnchorHom (α.comp ψ) := by
  ext s; exact (tangent I M).sectionsEquiv.injective (by ext x; simp)

end LieHom

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {α_M : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections} {α_N : 𝔤 →ₗ⁅ℝ⁆ (tangent J N).Sections}

section Pullback
variable (φ : C^∞⟮J, N; I, M⟯)
  (hφ : ∀ (ξ : 𝔤) (y : N), mfderiv J I φ y ((tangent J N).sectionsEquiv (α_N ξ) y) =
    (tangent I M).sectionsEquiv (α_M ξ) (φ y))

/-- Pullback of sections along a smooth map `φ : N → M` intertwining `α_N` and `α_M`. -/
def transformationPullback : (transformation α_M).Sections →ₗ⁅ℝ⁆ (transformation α_N).Sections :=
  { (((transformation α_N).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp <|
      (ContMDiffSection.modelPullback φ).comp
        ((transformation α_M).sectionsEquiv.restrictScalars ℝ).toLinearMap) with
    map_lie' {_ _} := (transformation α_N).sectionsEquiv.injective (by ext y; simp [hφ]) }

@[simp] theorem sectionsEquiv_transformationPullback_apply (s : (transformation α_M).Sections)
    (y : N) : (transformation α_N).sectionsEquiv (transformationPullback φ hφ s) y =
      (transformation α_M).sectionsEquiv s (φ y) := by
  rw [← LieHom.coe_toLinearMap]; simp [transformationPullback]

@[simp] theorem transformationPullback_smul (f : C^∞⟮I, M; ℝ⟯)
    (s : (transformation α_M).Sections) :
    transformationPullback (α_M := α_M) (α_N := α_N) φ hφ (f • s) =
      f.comp φ • transformationPullback φ hφ s :=
  (transformation α_N).sectionsEquiv.injective (by ext y; simp)

@[simp] theorem transformationPullback_transformationConst (ξ : 𝔤) :
    transformationPullback (α_M := α_M) (α_N := α_N) φ hφ (transformationConst α_M ξ) =
      transformationConst α_N ξ := (transformation α_N).sectionsEquiv.injective (by ext y; simp)

end Pullback

@[simp] theorem transformationPullback_id
    (hφ : ∀ (ξ : 𝔤) (x : M), mfderiv I I (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) x
      ((tangent I M).sectionsEquiv (α_M ξ) x) =
      (tangent I M).sectionsEquiv (α_M ξ) ((ContMDiffMap.id : C^∞⟮I, M; I, M⟯) x)) :
    transformationPullback (α_M := α_M) (α_N := α_M) ContMDiffMap.id hφ = LieHom.id := by
  ext s; exact (transformation α_M).sectionsEquiv.injective (by ext x; simp; rfl)

theorem transformationPullback_comp {E'' H'' P : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [FiniteDimensional ℝ E''] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
    {α_P : 𝔤 →ₗ⁅ℝ⁆ (tangent K P).Sections} (φ : C^∞⟮J, N; I, M⟯) (hφ) (ψ : C^∞⟮K, P; J, N⟯) (hψ)
    (hφψ : ∀ (ξ : 𝔤) (z : P), mfderiv K I (φ.comp ψ) z ((tangent K P).sectionsEquiv (α_P ξ) z) =
      (tangent I M).sectionsEquiv (α_M ξ) ((φ.comp ψ) z)) :
    transformationPullback (α_M := α_M) (α_N := α_P) (φ.comp ψ) hφψ =
      (transformationPullback (α_M := α_N) (α_N := α_P) ψ hψ).comp
        (transformationPullback (α_M := α_M) (α_N := α_N) φ hφ) := by
  ext s; exact (transformation α_P).sectionsEquiv.injective (by ext z; simp)

end Homomorphism
end LieAlgebroid

namespace InfinitesimalAction
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (act : InfinitesimalAction 𝔤 I M)

/-- Negating an infinitesimal action turns its antihomomorphism law `act ⁅ξ, η⁆ = -[act ξ, act η]`
into a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections`. -/
def negLieHom : 𝔤 →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections :=
  { (((LieAlgebroid.tangent I M).sectionsEquiv.symm.restrictScalars ℝ).toLinearMap.comp
      (-act.toSectionLinearMap)) with
    map_lie' {_ _} := (LieAlgebroid.tangent I M).sectionsEquiv.injective <| by
      have hcoe (ζ : 𝔤) : ⇑(act.toSectionLinearMap ζ) = act ζ :=
        funext (act.toSectionLinearMap_apply ζ)
      ext x; simp [hcoe, act.map_lie] }

@[simp] theorem sectionsEquiv_negLieHom_apply (ξ : 𝔤) (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv (act.negLieHom ξ) x = -act ξ x := by
  rw [← LieHom.coe_toLinearMap]; simp [negLieHom]

@[simp] theorem comp_negLieHom {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤) :
    (act.comp ψ).negLieHom = act.negLieHom.comp ψ := by
  ext ξ; exact (LieAlgebroid.tangent I M).sectionsEquiv.injective (by ext x; simp)

@[simp] theorem transformationIsotropy_negLieHom (x : M) :
    LieAlgebroid.transformationIsotropy act.negLieHom x = act.isotropy x :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

variable [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤]
  [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

/-- The transformation Lie algebroid `M ⋉ 𝔤` of an infinitesimal action `act`, with anchor
`(x, ξ) ↦ -act ξ x`. -/
def lieAlgebroid : LieAlgebroid I (TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
  LieAlgebroid.transformation act.negLieHom

theorem lieAlgebroid_eq : act.lieAlgebroid = LieAlgebroid.transformation act.negLieHom := (rfl)

@[simp] theorem lieAlgebroid_anchor_apply (x : M) (ξ : 𝔤) :
    act.lieAlgebroid.anchor x ξ = -act ξ x := by simp [lieAlgebroid]

@[simp] theorem lieAlgebroid_bracket_apply
    (a b : Cₛ^∞⟮I; TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    act.lieAlgebroid.bracket a b x =
      ⁅a x, b x⁆ - b.modelDeriv x (act (a x) x) + a.modelDeriv x (act (b x) x) := by
  simp only [lieAlgebroid, LieAlgebroid.transformation_bracket_apply,
    sectionsEquiv_negLieHom_apply, map_neg]; abel

end InfinitesimalAction

namespace LieAlgebroid
section MulAction
variable {EG HG E H : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {J : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup J (minSmoothness ℝ 3) G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MulAction G M]
  [ContMDiffSMul J I ∞ G M]

variable (J G I M) in
/-- The transformation Lie algebroid `M ⋉ Lie(G)` of a smooth left action of a finite-dimensional
real Lie group `G` on `M`, with anchor `(x, ξ) ↦ -fundamentalVectorField I ξ x`. -/
def ofMulAction : LieAlgebroid I (TrivialModel ℝ (GroupLieAlgebra J G))
    (Bundle.Trivial M (GroupLieAlgebra J G)) :=
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  (InfinitesimalAction.fundamental J G I M).lieAlgebroid

theorem ofMulAction_eq : ofMulAction J G I M =
    (haveI : IsManifold I 1 M := .of_le (n := ∞) (by simp)
    (InfinitesimalAction.fundamental J G I M).lieAlgebroid) := (rfl)

@[simp] theorem ofMulAction_anchor_apply (x : M) (ξ : GroupLieAlgebra J G) :
    (ofMulAction J G I M).anchor x ξ = -fundamentalVectorField I ξ x := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp); simp [ofMulAction]

@[simp] theorem ofMulAction_bracket_apply
    (a b : Cₛ^∞⟮I; TrivialModel ℝ (GroupLieAlgebra J G), Bundle.Trivial M (GroupLieAlgebra J G)⟯)
    (x : M) : (ofMulAction J G I M).bracket a b x =
      ⁅a x, b x⁆ - b.modelDeriv x (fundamentalVectorField I (a x) x) +
        a.modelDeriv x (fundamentalVectorField I (b x) x) := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp); simp [ofMulAction]

variable (J G I M) in
/-- Constant sections as a Lie algebra homomorphism into `(ofMulAction J G I M).Sections`. -/
def ofMulActionConst : GroupLieAlgebra J G →ₗ⁅ℝ⁆ (ofMulAction J G I M).Sections :=
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  transformationConst (InfinitesimalAction.fundamental J G I M).negLieHom

@[simp] theorem sectionsEquiv_ofMulActionConst (ξ : GroupLieAlgebra J G) :
    (ofMulAction J G I M).sectionsEquiv (ofMulActionConst J G I M ξ) =
      ContMDiffSection.modelConst I M ∞ ξ := by
  unfold ofMulActionConst ofMulAction InfinitesimalAction.lieAlgebroid
  exact sectionsEquiv_transformationConst _ ξ

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] [MulAction G N] [ContMDiffSMul J I' ∞ G N]

section EquivariantPullback
variable (φ : C^∞⟮I', N; I, M⟯) (hφ : ∀ (g : G) (y : N), φ (g • y) = g • φ y)

/-- Smooth `G`-equivariant pullback of sections of `ofMulAction`. -/
def ofMulActionPullback : (ofMulAction J G I M).Sections →ₗ⁅ℝ⁆ (ofMulAction J G I' N).Sections :=
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : ContMDiffSMul J I' 1 G N := .of_le (M := N) ENat.LEInfty.out
  transformationPullback φ fun ξ y ↦ by
    simp only [InfinitesimalAction.sectionsEquiv_negLieHom_apply,
      InfinitesimalAction.fundamental_apply, map_neg, neg_inj]
    exact mfderiv_fundamentalVectorField_of_map_smul (φ.contMDiff.mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := J) (I' := I') (n := 1) y).mdifferentiableAt
        one_ne_zero) (fun g ↦ hφ g y) ξ

@[simp] theorem sectionsEquiv_ofMulActionPullback_apply (s : (ofMulAction J G I M).Sections)
    (y : N) : (ofMulAction J G I' N).sectionsEquiv (ofMulActionPullback φ hφ s) y =
      (ofMulAction J G I M).sectionsEquiv s (φ y) := by
  unfold ofMulActionPullback ofMulAction InfinitesimalAction.lieAlgebroid
  exact sectionsEquiv_transformationPullback_apply φ _ s y

theorem sectionsEquiv_ofMulActionPullback (s : (ofMulAction J G I M).Sections) :
    (ofMulAction J G I' N).sectionsEquiv (ofMulActionPullback φ hφ s) =
      ContMDiffSection.modelPullback φ ((ofMulAction J G I M).sectionsEquiv s) := by ext y; simp

@[simp] theorem ofMulActionPullback_smul (f : C^∞⟮I, M; ℝ⟯) (s : (ofMulAction J G I M).Sections) :
    ofMulActionPullback (J := J) φ hφ (f • s) = f.comp φ • ofMulActionPullback φ hφ s :=
  (ofMulAction J G I' N).sectionsEquiv.injective (by ext y; simp)

@[simp] theorem ofMulActionPullback_ofMulActionConst (ξ : GroupLieAlgebra J G) :
    ofMulActionPullback (J := J) φ hφ (ofMulActionConst J G I M ξ) =
      ofMulActionConst J G I' N ξ := (ofMulAction J G I' N).sectionsEquiv.injective (by ext y; simp)

end EquivariantPullback

@[simp] theorem ofMulActionPullback_id
    (hφ : ∀ (g : G) (x : M), (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) (g • x) =
      g • (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) x) :
    ofMulActionPullback (J := J) (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) hφ = LieHom.id := by
  ext s; exact (ofMulAction J G I M).sectionsEquiv.injective (by ext x; simp; rfl)

theorem ofMulActionPullback_comp {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P] [MulAction G P]
    [ContMDiffSMul J I'' ∞ G P] (φ : C^∞⟮I', N; I, M⟯) (hφ) (ψ : C^∞⟮I'', P; I', N⟯) (hψ)
    (hφψ : ∀ (g : G) (z : P), (φ.comp ψ) (g • z) = g • (φ.comp ψ) z) :
    ofMulActionPullback (J := J) (φ.comp ψ) hφψ =
      (ofMulActionPullback (J := J) ψ hψ).comp (ofMulActionPullback (J := J) φ hφ) := by
  ext s; exact (ofMulAction J G I'' P).sectionsEquiv.injective (by ext z; simp)

end MulAction

section TranslationAction
variable {V 𝔤 : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [IsLieAbelian 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
  (τ : 𝔤 ≃ₗ[ℝ] V)

private theorem fromTangentSpace_translation_anchor (f : 𝔤 →ₗ[ℝ] V) (x : V) (ξ : 𝔤) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) x
      ((InfinitesimalAction.translation f).lieAlgebroid.anchor x ξ) = -f ξ := by
  rw [InfinitesimalAction.lieAlgebroid_anchor_apply, map_neg,
    NormedSpace.fromTangentSpace_apply, InfinitesimalAction.translation_apply]

omit [IsLieAbelian 𝔤] in
private def translationInvSection (X : Cₛ^∞⟮𝓘(ℝ, V); V, (TangentSpace 𝓘(ℝ, V) : V → Type _)⟯) :
    Cₛ^∞⟮𝓘(ℝ, V); TrivialModel ℝ 𝔤, Bundle.Trivial V 𝔤⟯ :=
  let L : V →L[ℝ] TrivialModel ℝ 𝔤 := LinearMap.toContinuousLinearMap
    (-(TrivialModel.equiv ℝ 𝔤).toLinearMap.comp τ.symm.toLinearMap)
  have hX : ContDiff ℝ ∞ (fun x ↦ NormedSpace.fromTangentSpace (𝕜 := ℝ) x (X x)) :=
    contMDiff_vectorSpace_iff_contDiff.1 X.contMDiff
  ⟨fun x ↦ -τ.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) x (X x)), TrivialModel.contMDiff_mk_iff.2
    ⟨contMDiff_id, (L.contMDiff.comp hX.contMDiff).congr fun _ ↦ by simp [L]⟩⟩

/-- When an abelian Lie algebra `𝔤` acts on `V` by translations along `τ : 𝔤 ≃ₗ[ℝ] V`, the anchor
`s ↦ (x ↦ -τ (s x))` is a `C^∞⟮𝓘(ℝ, V), V; ℝ⟯`-linear equivalence onto
`(tangent 𝓘(ℝ, V) V).Sections`. -/
def translationSectionsLinearEquiv :
    (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections ≃ₗ[C^∞⟮𝓘(ℝ, V), V; ℝ⟯]
      (tangent 𝓘(ℝ, V) V).Sections :=
  let A := (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid
  { ((tangent 𝓘(ℝ, V) V).sectionsEquiv.symm.toLinearMap.comp
      (A.anchorField.comp A.sectionsEquiv.toLinearMap)) with
    invFun t := A.sectionsEquiv.symm (translationInvSection τ ((tangent 𝓘(ℝ, V) V).sectionsEquiv t))
    left_inv _ := A.sectionsEquiv.injective <| by
      ext; simp only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply, translationInvSection, ContMDiffSection.coeFn_mk,
        anchorField_apply, A, fromTangentSpace_translation_anchor, map_neg, neg_neg,
        τ.symm_apply_apply]
    right_inv _ := (tangent 𝓘(ℝ, V) V).sectionsEquiv.injective <| by
      ext x; apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).injective
      simp only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply, anchorField_apply, translationInvSection,
        ContMDiffSection.coeFn_mk, A, fromTangentSpace_translation_anchor, map_neg, neg_neg,
        τ.apply_symm_apply] }

@[simp] theorem sectionsEquiv_translationSectionsLinearEquiv
    (s : (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLinearEquiv τ s) =
      (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.anchorField
        ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.sectionsEquiv s) := by
  simp [translationSectionsLinearEquiv]

@[simp] theorem sectionsEquiv_translationSectionsLinearEquiv_symm_apply
    (t : (tangent 𝓘(ℝ, V) V).Sections) (x : V) :
    (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.sectionsEquiv
      ((translationSectionsLinearEquiv τ).symm t) x =
        -τ.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) x ((tangent 𝓘(ℝ, V) V).sectionsEquiv t x)) :=
  by simp [translationSectionsLinearEquiv, translationInvSection]

theorem translationSectionsLinearEquiv_apply
    (s : (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections) :
    translationSectionsLinearEquiv τ s =
      (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.anchorLieHom s :=
  (tangent 𝓘(ℝ, V) V).sectionsEquiv.injective (by simp)

/-- For the translation action of `𝔤 ≃ₗ[ℝ] V` on `V`, the anchor identifies sections of the
transformation Lie algebroid with `(tangent 𝓘(ℝ, V) V).Sections` as Lie algebras over `ℝ`. -/
def translationSectionsLieEquiv :
    (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections ≃ₗ⁅ℝ⁆
      (tangent 𝓘(ℝ, V) V).Sections :=
  { (translationSectionsLinearEquiv τ).restrictScalars ℝ with
    map_lie' {_ _} := by simp [translationSectionsLinearEquiv_apply] }

theorem coe_translationSectionsLieEquiv :
    ⇑(translationSectionsLieEquiv τ) = translationSectionsLinearEquiv τ := (rfl)

theorem coe_translationSectionsLieEquiv_symm :
    ⇑(translationSectionsLieEquiv τ).symm = (translationSectionsLinearEquiv τ).symm := by
  ext t; rw [LieEquiv.symm_apply_eq, coe_translationSectionsLieEquiv, LinearEquiv.apply_symm_apply]

@[simp] theorem sectionsEquiv_translationSectionsLieEquiv
    (s : (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLieEquiv τ s) =
      (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.anchorField
        ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.sectionsEquiv s) := by
  rw [coe_translationSectionsLieEquiv, sectionsEquiv_translationSectionsLinearEquiv]

@[simp] theorem sectionsEquiv_translationSectionsLieEquiv_symm_apply
    (t : (tangent 𝓘(ℝ, V) V).Sections) (x : V) :
    (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.sectionsEquiv
      ((translationSectionsLieEquiv τ).symm t) x =
        -τ.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) x ((tangent 𝓘(ℝ, V) V).sectionsEquiv t x)) :=
  by rw [coe_translationSectionsLieEquiv_symm,
    sectionsEquiv_translationSectionsLinearEquiv_symm_apply]

theorem sectionsEquiv_translationSectionsLieEquiv_apply
    (s : (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections) (x : V) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLieEquiv τ s) x =
      -τ ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.sectionsEquiv s x) :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).injective <| by
    rw [sectionsEquiv_translationSectionsLieEquiv, anchorField_apply,
      fromTangentSpace_translation_anchor, LinearEquiv.coe_toLinearMap]
    exact (NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) x _).symm

@[simp] theorem translationSectionsLieEquiv_lie
    (s : (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid.Sections)
    (f : C^∞⟮𝓘(ℝ, V), V; ℝ⟯) : ⁅translationSectionsLieEquiv τ s, f⁆ = ⁅s, f⁆ := by
  rw [coe_translationSectionsLieEquiv, translationSectionsLinearEquiv_apply, anchorLieHom_lie]

end TranslationAction

/-- Omitting the minus sign on the infinitesimal generators `x ∂_x` and `∂_x` of
`LieAlgebra.AffineLine ℝ` violates the Jacobi identity for `transformationBracket`. -/
theorem not_transformationBracket_jacobi_toSectionLinearMap_affineLine :
    ¬∀ a b c : Cₛ^∞⟮𝓘(ℝ, ℝ); TrivialModel ℝ (LieAlgebra.AffineLine ℝ),
        Bundle.Trivial ℝ (LieAlgebra.AffineLine ℝ)⟯,
      transformationBracket InfinitesimalAction.affineLine.toSectionLinearMap a
          (transformationBracket InfinitesimalAction.affineLine.toSectionLinearMap b c) =
        transformationBracket InfinitesimalAction.affineLine.toSectionLinearMap
            (transformationBracket InfinitesimalAction.affineLine.toSectionLinearMap a b) c +
          transformationBracket InfinitesimalAction.affineLine.toSectionLinearMap b
            (transformationBracket InfinitesimalAction.affineLine.toSectionLinearMap a c) :=
  fun hjac ↦ by
    let act := InfinitesimalAction.affineLine
    have hcoe (u) : ⇑(act.toSectionLinearMap u) = act u := funext (act.toSectionLinearMap_apply u)
    have h0 := congrArg (fun s ↦ NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ) (s 0)) <|
      (transformationBracket_jacobi_iff act.toSectionLinearMap).1 hjac
        (LieAlgebra.AffineLine.dilation ℝ) (LieAlgebra.AffineLine.translation ℝ)
    have hmlie : mlieBracket 𝓘(ℝ, ℝ) (act (LieAlgebra.AffineLine.dilation ℝ))
        (act (LieAlgebra.AffineLine.translation ℝ)) =
          -act ⁅LieAlgebra.AffineLine.dilation ℝ, LieAlgebra.AffineLine.translation ℝ⁆ := by
      rw [act.map_lie, neg_neg]
    simp only [InfinitesimalAction.toSectionLinearMap_apply, tangent_bracket_apply, hcoe, hmlie,
      LieAlgebra.AffineLine.lie_dilation_translation, Pi.neg_apply, map_neg] at h0
    have h1 : NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)
        (act (LieAlgebra.AffineLine.translation ℝ) 0) = 1 :=
      (NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (0 : ℝ) _).trans <|
        (InfinitesimalAction.affineLine_apply _ _).trans (by simp; rfl)
    rw [h1] at h0; norm_num at h0

end LieAlgebroid
end TauCeti
