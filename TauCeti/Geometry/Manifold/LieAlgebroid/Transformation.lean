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
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Action (transformation) Lie algebroids

Given a finite-dimensional real Hausdorff topological Lie algebra `𝔤` and a Lie algebra homomorphism
`α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections` into smooth vector fields on a smooth finite-dimensional real
manifold `M`, the trivial vector bundle `Bundle.Trivial M 𝔤` carries the **transformation** (or
**action**) **Lie algebroid** structure `TauCeti.LieAlgebroid.transformation α`:

* its anchor `TauCeti.LieAlgebroid.transformationAnchor` evaluates at `(x, ξ)` to `α ξ x`;
* its section bracket `TauCeti.LieAlgebroid.transformationBracket` is the sum of the pointwise Lie
  bracket in `𝔤` and the directional derivatives along the anchor vector fields,
  `[a, b](x) = ⁅a(x), b(x)⁆ + (L_{α(a(x))} b)(x) - (L_{α(b(x))} a)(x)`.

To analyze the exact role of the Lie algebra homomorphism condition, `transformationAnchor` and
`transformationBracket` are first constructed for an arbitrary `ℝ`-linear map
`α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, TangentSpace I⟯`. Alternatingness, the Leibniz rule, and closure on
constant sections hold unconditionally for any linear `α₀`. Over a Hausdorff base,
`transformationBracket α₀` satisfies the Jacobi identity if and only if `α₀` intertwines the Lie
bracket of `𝔤` with the manifold Lie bracket of vector fields
(`TauCeti.LieAlgebroid.transformationBracket_jacobi_iff`).

Because an infinitesimal action `act : InfinitesimalAction 𝔤 I M` (such as the fundamental vector
fields of a smooth left Lie group action) is an *antihomomorphism* `act ⁅ξ, η⁆ = -[act ξ, act η]`,
passing to `act.negLieHom : ξ ↦ -act ξ` produces a Lie algebra homomorphism and hence the
transformation Lie algebroid `act.lieAlgebroid` (and `TauCeti.LieAlgebroid.ofMulAction` for a smooth
Lie group action). For the standard affine action of the two-dimensional nonabelian Lie algebra
`TauCeti.LieAlgebra.AffineLine ℝ` on `ℝ` (`dilation ↦ x ∂_x`, `translation ↦ ∂_x`), omitting this
minus sign genuinely violates the Jacobi identity
(`TauCeti.LieAlgebroid.not_transformationBracket_jacobi_affineLine_pos`).

## Main definitions

* `TauCeti.LieAlgebroid.transformationAnchor`, `TauCeti.LieAlgebroid.transformationBracket`: the
  anchor and section bracket on `Bundle.Trivial M 𝔤` attached to any linear map
  `α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, TangentSpace I⟯`.
* `TauCeti.LieAlgebroid.transformation`: the transformation Lie algebroid `M ⋉ 𝔤` of a Lie algebra
  homomorphism `α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections`.
* `TauCeti.LieAlgebroid.transformationConst`: constant sections as a Lie algebra homomorphism
  `𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections`.
* `TauCeti.LieAlgebroid.transformationAnchorHom`: the anchor on sections as a Lie algebra
  homomorphism `(transformation α).Sections →ₗ⁅ℝ⁆ (tangent I M).Sections`.
* `TauCeti.LieAlgebroid.transformationIsotropy`: the isotropy Lie subalgebra `ker (anchor x) ≤ 𝔤` at
  `x : M`.
* `TauCeti.LieAlgebroid.transformationMapLieHom`, `TauCeti.LieAlgebroid.transformationPullback`:
  functoriality of transformation Lie algebroid sections along Lie algebra homomorphisms `𝔥 →ₗ⁅ℝ⁆ 𝔤`
  and smooth maps `N → M` intertwining the actions.
* `TauCeti.InfinitesimalAction.negLieHom`, `TauCeti.InfinitesimalAction.lieAlgebroid`: the
  transformation Lie algebroid of an infinitesimal action.
* `TauCeti.LieAlgebroid.ofMulAction`, `TauCeti.LieAlgebroid.ofMulActionPullback`: the transformation
  Lie algebroid `M ⋉ Lie(G)` of a smooth left Lie group action and pullback along equivariant maps.
* `TauCeti.InfinitesimalAction.affineLine`: the standard infinitesimal action of
  `LieAlgebra.AffineLine ℝ` on `ℝ`.
* `TauCeti.LieAlgebroid.translationSectionsLieEquiv`: for an abelian Lie algebra isomorphic to a
  finite-dimensional real normed space `V` acting by translations, the Lie algebra isomorphism
  identifying sections of the transformation Lie algebroid with `(tangent 𝓘(ℝ, V) V).Sections`.

## Main results

* `TauCeti.LieAlgebroid.transformationBracket_jacobi_iff`: over a Hausdorff base,
  `transformationBracket α₀` satisfies the Jacobi identity if and only if `α₀` is a Lie algebra
  homomorphism into `(tangent I M).Sections`.
* `TauCeti.LieAlgebroid.transformation_zero`: the transformation Lie algebroid of the zero action is
  `trivialLieAlgebra I M 𝔤`.
* `TauCeti.LieAlgebroid.not_transformationBracket_jacobi_affineLine_pos`: the un-negated affine-line
  generators `x ∂_x` and `∂_x` on `ℝ` violate the Jacobi identity for `transformationBracket`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), Example 1.6.
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
  [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

/-- The smooth anchor bundle morphism `(x, ξ) ↦ α₀ ξ x` on `Bundle.Trivial M 𝔤` attached to an
`ℝ`-linear map `α₀` from `𝔤` into smooth tangent vector fields on `M`. -/
def transformationAnchor (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤 →L[ℝ] E,
      fun x ↦ Bundle.Trivial M 𝔤 x →L[ℝ] TangentSpace I x⟯ :=
  let anchorLin (x : M) : Bundle.Trivial M 𝔤 x →ₗ[ℝ] TangentSpace I x :=
    { toFun ξ := α₀ ξ x
      map_add' ξ η := by simp
      map_smul' c ξ := by simp }
  { toFun x := LinearMap.toContinuousLinearMap (anchorLin x)
    contMDiff_toFun := by
      have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
      rw [contMDiff_hom_bundle_iff]
      let B := Module.finBasis ℝ 𝔤
      let e := Bundle.TrivialModel.equiv ℝ 𝔤
      have hproj : ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤)) I ∞
          (TotalSpace.proj (F := Bundle.TrivialModel ℝ 𝔤) (E := Bundle.Trivial M 𝔤)) :=
        contMDiff_proj (Bundle.Trivial M 𝔤)
      have hsnd : ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤))
          𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤) ∞
          (fun p : TotalSpace (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) ↦ e p.2) :=
        (Bundle.TrivialModel.contMDiff_mk_iff.1 contMDiff_id).2
      have hcoord (i : Fin (Module.finrank ℝ 𝔤)) :
          ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤)) 𝓘(ℝ, ℝ) ∞
            (fun p : TotalSpace (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) ↦
              B.coord i p.2) := by
        let L : Bundle.TrivialModel ℝ 𝔤 →L[ℝ] ℝ :=
          LinearMap.toContinuousLinearMap ((B.coord i).comp e.symm.toLinearMap)
        exact (L.contMDiff.comp hsnd).congr fun p ↦ by simp [L]
      have hsum := ContMDiff.sum_sectionAlong (V := TangentSpace I) (b := TotalSpace.proj)
        Finset.univ
        (fun i (p : TotalSpace (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤)) ↦
          B.coord i p.2 • α₀ (B i) p.proj)
        hproj fun i _ ↦ (hcoord i).smul_totalSpace ((α₀ (B i)).contMDiff.comp hproj)
      refine hsum.congr fun p ↦ congrArg (TotalSpace.mk' E p.proj) ?_
      simp only [LinearMap.coe_toContinuousLinearMap']
      conv_lhs => rw [← B.sum_repr p.2]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [anchorLin] }

@[simp]
theorem transformationAnchor_apply (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (ξ : 𝔤) :
    transformationAnchor α₀ x ξ = α₀ ξ x :=
  (rfl)

/-- The smooth tangent vector field `x ↦ α₀ (a x) x` induced by a smooth section `a` of
`Bundle.Trivial M 𝔤`, linear over `C^∞⟮I, M; ℝ⟯`. -/
def transformationAnchorField (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun a :=
    { toFun x := transformationAnchor α₀ x (a x)
      contMDiff_toFun := (transformationAnchor α₀).contMDiff.clm_bundle_apply a.contMDiff }
  map_add' a b := by ext x; simp
  map_smul' f a := by ext x; simp

@[simp]
theorem transformationAnchorField_apply
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    transformationAnchorField α₀ a x = α₀ (a x) x :=
  (rfl)

@[simp]
theorem transformationAnchorField_modelConst
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (ξ : 𝔤) :
    transformationAnchorField α₀ (ContMDiffSection.modelConst I M ∞ ξ) = α₀ ξ := by
  ext x
  simp

/-- The transformation section bracket on `Bundle.Trivial M 𝔤` attached to an `ℝ`-linear map
`α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, TangentSpace I⟯`:
`[a, b](x) = ⁅a x, b x⁆ + b.modelDeriv x (α₀ (a x) x) - a.modelDeriv x (α₀ (b x) x)`. -/
def transformationBracket (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ :=
  LinearMap.mk₂ ℝ
    (fun a b ↦
      (trivialLieAlgebra I M 𝔤).bracket a b +
        ContMDiffSection.modelLieDeriv (transformationAnchorField α₀ a) b -
        ContMDiffSection.modelLieDeriv (transformationAnchorField α₀ b) a)
    (fun a a' b ↦ ContMDiffSection.ext fun x ↦ by
      simp [ContMDiffSection.modelDeriv_add]
      abel)
    (fun c a b ↦ ContMDiffSection.ext fun x ↦ by
      simp [ContMDiffSection.modelDeriv_const_smul, smul_add, smul_sub])
    (fun a b b' ↦ ContMDiffSection.ext fun x ↦ by
      simp [ContMDiffSection.modelDeriv_add]
      abel)
    (fun c a b ↦ ContMDiffSection.ext fun x ↦ by
      simp [ContMDiffSection.modelDeriv_const_smul, smul_add, smul_sub])

@[simp]
theorem transformationBracket_apply
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    transformationBracket α₀ a b x =
      ⁅a x, b x⁆ + b.modelDeriv x (α₀ (a x) x) - a.modelDeriv x (α₀ (b x) x) := by
  simp [transformationBracket]

@[simp]
theorem transformationBracket_self
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a a = 0 := by
  ext x
  simp

theorem transformationBracket_swap
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a b = -transformationBracket α₀ b a := by
  ext x
  simp only [transformationBracket_apply, ContMDiffSection.coe_neg, Pi.neg_apply,
    ← lie_skew (a x) (b x)]
  abel

theorem transformationBracket_smul_apply
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯)
    (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    transformationBracket α₀ a (f • b) x =
      f x • transformationBracket α₀ a b x +
        mvfderiv I f x (transformationAnchor α₀ x (a x)) • b x := by
  simp only [transformationBracket_apply, ContMDiffSection.smul_apply, lie_smul,
    ContMDiffSection.modelDeriv_smul, map_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    transformationAnchor_apply, smul_add, smul_sub]
  abel

@[simp]
theorem transformationBracket_modelConst
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (ξ η : 𝔤) :
    transformationBracket α₀
        (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η) =
      ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ := by
  ext x
  simp

end LinearPreAlgebroid

section Homomorphism

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

/-- Section-level Leibniz rule for `transformationBracket` along `transformationAnchorField`. -/
theorem transformationBracket_smul_right
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (f : C^∞⟮I, M; ℝ⟯) :
    transformationBracket α₀ a (f • b) =
      f • transformationBracket α₀ a b +
        (tangent I M).anchorDeriv (transformationAnchorField α₀ a) f • b := by
  ext x
  rw [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.smul_apply,
    ContMDiffSection.smul_apply, transformationBracket_smul_apply]
  simp

/-- Directional differentiation along smooth tangent vector fields intertwines the manifold Lie
bracket with the commutator of derivations, without any Hausdorff assumption on the base. -/
private theorem tangent_anchorDeriv_bracket
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (tangent I M).anchorDeriv ((tangent I M).bracket X Y) f =
      (tangent I M).anchorDeriv X ((tangent I M).anchorDeriv Y f) -
        (tangent I M).anchorDeriv Y ((tangent I M).anchorDeriv X f) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hYf : ⇑((tangent I M).anchorDeriv Y f) = fun y ↦ mvfderiv I f y (Y y) :=
    funext fun y ↦ by rw [anchorDeriv_apply, tangent_anchor_apply]
  have hXf : ⇑((tangent I M).anchorDeriv X f) = fun y ↦ mvfderiv I f y (X y) :=
    funext fun y ↦ by rw [anchorDeriv_apply, tangent_anchor_apply]
  ext x
  simp only [anchorDeriv_apply, tangent_anchor_apply, tangent_bracket_apply,
    ContMDiffMap.coe_sub, Pi.sub_apply, hYf, hXf]
  exact _root_.mvfderiv_mlieBracket f.contMDiff.contMDiffAt (by simp)
    (X.contMDiff.mdifferentiableAt (by simp)) (Y.contMDiff.mdifferentiableAt (by simp))

/-- Whenever `α₀` intertwines the Lie bracket of `𝔤` with the manifold Lie bracket of vector
fields, `transformationAnchorField α₀` intertwines `transformationBracket α₀` with the tangent
bracket on all smooth sections (without requiring `M` to be Hausdorff). -/
theorem transformationAnchorField_transformationBracket
    {α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hα : ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η))
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationAnchorField α₀ (transformationBracket α₀ a b) =
      (tangent I M).bracket (transformationAnchorField α₀ a) (transformationAnchorField α₀ b) := by
  -- Both sides satisfy the same Leibniz rules in both slots, so expanding `a` and `b` in a finite
  -- basis of `𝔤` reduces the identity to constant sections, which is `hα`.
  have hsmul_right {u v : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯}
      (huv : transformationAnchorField α₀ (transformationBracket α₀ u v) =
        (tangent I M).bracket (transformationAnchorField α₀ u) (transformationAnchorField α₀ v))
      (g : C^∞⟮I, M; ℝ⟯) :
      transformationAnchorField α₀ (transformationBracket α₀ u (g • v)) =
        (tangent I M).bracket (transformationAnchorField α₀ u)
          (transformationAnchorField α₀ (g • v)) := by
    rw [transformationBracket_smul_right, map_add, map_smul, map_smul, map_smul,
      (tangent I M).bracket_smul_right, huv]
  have hsmul_left {u v : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯}
      (huv : transformationAnchorField α₀ (transformationBracket α₀ u v) =
        (tangent I M).bracket (transformationAnchorField α₀ u) (transformationAnchorField α₀ v))
      (f : C^∞⟮I, M; ℝ⟯) :
      transformationAnchorField α₀ (transformationBracket α₀ (f • u) v) =
        (tangent I M).bracket (transformationAnchorField α₀ (f • u))
          (transformationAnchorField α₀ v) := by
    have hvu : transformationAnchorField α₀ (transformationBracket α₀ v u) =
        (tangent I M).bracket (transformationAnchorField α₀ v)
          (transformationAnchorField α₀ u) := by
      rw [transformationBracket_swap, map_neg, huv, (tangent I M).bracket_swap, neg_neg]
    rw [transformationBracket_swap, map_neg, hsmul_right hvu f,
      (tangent I M).bracket_swap, neg_neg]
  let B := Module.finBasis ℝ 𝔤
  rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B a,
    ContMDiffSection.eq_sum_modelCoord_smul_modelConst B b]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  refine hsmul_left (hsmul_right ?_ _) _
  simp [hα]

/-- Whenever `α₀` intertwines the Lie bracket of `𝔤` with the manifold Lie bracket of vector
fields, `transformationBracket α₀` satisfies the Jacobi identity (without requiring `M` to be
Hausdorff). -/
theorem transformationBracket_jacobi
    {α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hα : ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η))
    (a b c : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a (transformationBracket α₀ b c) =
      transformationBracket α₀ (transformationBracket α₀ a b) c +
        transformationBracket α₀ b (transformationBracket α₀ a c) := by
  -- The Jacobiator `J a b c` is `C^∞(M, ℝ)`-linear in its third slot because the anchor intertwines
  -- brackets, hence `C^∞(M, ℝ)`-trilinear by skew-symmetry; basis expansion reduces to `𝔤`.
  let br := transformationBracket α₀
  let J (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
      Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ :=
    br u (br v w) - br (br u v) w - br v (br u w)
  have hJ_smul₃ (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯)
      (f : C^∞⟮I, M; ℝ⟯) : J u v (f • w) = f • J u v w := by
    simp only [J, br, transformationBracket_smul_right, map_add,
      transformationAnchorField_transformationBracket hα u v, tangent_anchorDeriv_bracket]
    module
  have hJ_swap₁₂ (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
      J v u w = -J u v w := by
    simp only [J, br]
    rw [transformationBracket_swap α₀ v u, map_neg, LinearMap.neg_apply]
    abel
  have hJ_swap₂₃ (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
      J u w v = -J u v w := by
    simp only [J, br]
    rw [transformationBracket_swap α₀ w v, map_neg,
      transformationBracket_swap α₀ (transformationBracket α₀ u w) v,
      transformationBracket_swap α₀ w (transformationBracket α₀ u v)]
    abel
  have hJ_smul₂ (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯)
      (f : C^∞⟮I, M; ℝ⟯) : J u (f • v) w = f • J u v w := by
    rw [hJ_swap₂₃ u w (f • v), hJ_smul₃ u w v f, hJ_swap₂₃ u v w]
    ext x
    simp
  have hJ_smul₁ (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯)
      (f : C^∞⟮I, M; ℝ⟯) : J (f • u) v w = f • J u v w := by
    rw [hJ_swap₁₂ v (f • u) w, hJ_smul₂ v u w f, hJ_swap₁₂ u v w]
    ext x
    simp
  have hJ_add₁ (u₁ u₂ v w) : J (u₁ + u₂) v w = J u₁ v w + J u₂ v w := by
    simp only [J, map_add, LinearMap.add_apply]; abel
  have hJ_add₂ (u v₁ v₂ w) : J u (v₁ + v₂) w = J u v₁ w + J u v₂ w := by
    simp only [J, map_add, LinearMap.add_apply]; abel
  have hJ_add₃ (u v w₁ w₂) : J u v (w₁ + w₂) = J u v w₁ + J u v w₂ := by
    simp only [J, map_add]; abel
  let B := Module.finBasis ℝ 𝔤
  have hJ_const (ξ η ζ : 𝔤) :
      J (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η)
        (ContMDiffSection.modelConst I M ∞ ζ) = 0 := by
    ext x
    simp [J, br]
  have hJ_zero : J a b c = 0 := by
    rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B a]
    have hsum₁ : ∀ s : Finset (Fin (Module.finrank ℝ 𝔤)),
        J (∑ i ∈ s, a.modelCoord B i • ContMDiffSection.modelConst I M ∞ (B i)) b c = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [J]
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, hJ_add₁, ih, add_zero, hJ_smul₁]
        rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B b]
        have hsum₂ : ∀ t : Finset (Fin (Module.finrank ℝ 𝔤)),
            J (ContMDiffSection.modelConst I M ∞ (B i))
              (∑ j ∈ t, b.modelCoord B j • ContMDiffSection.modelConst I M ∞ (B j)) c = 0 := by
          intro t
          induction t using Finset.induction_on with
          | empty => simp [J]
          | insert j t hj iht =>
            rw [Finset.sum_insert hj, hJ_add₂, iht, add_zero, hJ_smul₂]
            rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B c]
            have hsum₃ : ∀ r : Finset (Fin (Module.finrank ℝ 𝔤)),
                J (ContMDiffSection.modelConst I M ∞ (B i))
                  (ContMDiffSection.modelConst I M ∞ (B j))
                  (∑ l ∈ r, c.modelCoord B l • ContMDiffSection.modelConst I M ∞ (B l)) = 0 := by
              intro r
              induction r using Finset.induction_on with
              | empty => simp [J]
              | insert l r hl ihr =>
                rw [Finset.sum_insert hl, hJ_add₃, ihr, add_zero, hJ_smul₃, hJ_const]
                ext x
                simp
            rw [hsum₃ Finset.univ]
            ext x
            simp
        rw [hsum₂ Finset.univ]
        ext x
        simp
    exact hsum₁ Finset.univ
  dsimp only [J, br] at hJ_zero
  rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm] at hJ_zero
  exact hJ_zero

/-- Over a Hausdorff base, `transformationBracket α₀` satisfies the Jacobi identity if and only if
`α₀` intertwines the Lie bracket of `𝔤` with the Lie bracket of smooth tangent vector fields. -/
theorem transformationBracket_jacobi_iff [T2Space M]
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (∀ a b c,
      transformationBracket α₀ a (transformationBracket α₀ b c) =
        transformationBracket α₀ (transformationBracket α₀ a b) c +
          transformationBracket α₀ b (transformationBracket α₀ a c)) ↔
      ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η) := by
  refine ⟨fun hjac ξ η ↦ ?_, transformationBracket_jacobi⟩
  let A : LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
    { anchor := transformationAnchor α₀
      bracket := transformationBracket α₀
      bracket_self := transformationBracket_self α₀
      bracket_bracket := hjac
      bracket_smul_apply := transformationBracket_smul_apply α₀ }
  ext x
  have h := A.anchor_bracket (ContMDiffSection.modelConst I M ∞ ξ)
    (ContMDiffSection.modelConst I M ∞ η) x
  have hξ : ⇑(A.anchorField (ContMDiffSection.modelConst I M ∞ ξ)) = ⇑(α₀ ξ) :=
    funext fun y ↦ by simp [A]
  have hη : ⇑(A.anchorField (ContMDiffSection.modelConst I M ∞ η)) = ⇑(α₀ η) :=
    funext fun y ↦ by simp [A]
  simpa [A, hξ, hη] using h

/-! ### The transformation Lie algebroid of a Lie algebra homomorphism -/

/-- Underlying linear map `𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, TangentSpace I⟯` of `α : 𝔤 →ₗ⁅ℝ⁆ Γ(TM)`. -/
private def toTangentLinearMap (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) :
    𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ((tangent I M).sectionsEquiv.restrictScalars ℝ).toLinearMap.comp α.toLinearMap

omit [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤]
  [FiniteDimensional ℝ 𝔤] in
private theorem toTangentLinearMap_lie (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ξ η : 𝔤) :
    toTangentLinearMap α ⁅ξ, η⁆ =
      (tangent I M).bracket (toTangentLinearMap α ξ) (toTangentLinearMap α η) := by
  simp [toTangentLinearMap]

/-- The **transformation** (or **action**) **Lie algebroid** `M ⋉ 𝔤` on `Bundle.Trivial M 𝔤`
associated with a Lie algebra homomorphism `α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections`. -/
def transformation (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) :
    LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) where
  anchor := transformationAnchor (toTangentLinearMap α)
  bracket := transformationBracket (toTangentLinearMap α)
  bracket_self := transformationBracket_self (toTangentLinearMap α)
  bracket_bracket := transformationBracket_jacobi (toTangentLinearMap_lie α)
  bracket_smul_apply := transformationBracket_smul_apply (toTangentLinearMap α)

@[simp]
theorem transformation_anchor_apply (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (x : M) (ξ : 𝔤) :
    (transformation α).anchor x ξ = (tangent I M).sectionsEquiv (α ξ) x := by
  simp [transformation, toTangentLinearMap]

@[simp]
theorem transformation_anchorField_modelConst (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ξ : 𝔤) :
    (transformation α).anchorField (ContMDiffSection.modelConst I M ∞ ξ) =
      (tangent I M).sectionsEquiv (α ξ) := by
  ext x
  simp

@[simp]
theorem transformation_bracket_apply (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections)
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    (transformation α).bracket a b x =
      ⁅a x, b x⁆ + b.modelDeriv x ((tangent I M).sectionsEquiv (α (a x)) x) -
        a.modelDeriv x ((tangent I M).sectionsEquiv (α (b x)) x) := by
  simp [transformation, toTangentLinearMap]

@[simp]
theorem transformation_bracket_modelConst (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ξ η : 𝔤) :
    (transformation α).bracket
        (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η) =
      ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ :=
  transformationBracket_modelConst (toTangentLinearMap α) ξ η

/-- The transformation Lie algebroid of the zero Lie algebra homomorphism is the trivial Lie
algebra bundle algebroid `trivialLieAlgebra I M 𝔤`. -/
@[simp]
theorem transformation_zero :
    transformation (0 : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) = trivialLieAlgebra I M 𝔤 := by
  refine LieAlgebroid.ext (ContMDiffSection.ext fun x ↦ ContinuousLinearMap.ext fun ξ ↦ ?_)
    (LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ContMDiffSection.ext fun x ↦ ?_)
  · simp
  · simp

/-- Constant sections define a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections`. -/
def transformationConst (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) :
    𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections where
  toFun ξ := (transformation α).sectionsEquiv.symm (ContMDiffSection.modelConst I M ∞ ξ)
  map_add' ξ η := by simp only [map_add]
  map_smul' c ξ := by
    rw [map_smul, LinearMapClass.map_smul_of_tower]
    rfl
  map_lie' := by
    intro ξ η
    exact (transformation α).sectionsEquiv.injective <| by simp

@[simp]
theorem sectionsEquiv_transformationConst (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ξ : 𝔤) :
    (transformation α).sectionsEquiv (transformationConst α ξ) =
      ContMDiffSection.modelConst I M ∞ ξ :=
  (transformation α).sectionsEquiv.apply_symm_apply _

theorem transformationConst_injective (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) [Nonempty M] :
    Function.Injective (transformationConst α) := by
  intro ξ η h
  exact ContMDiffSection.modelConst_injective <| by
    simpa using congrArg (transformation α).sectionsEquiv h

/-- The anchor of `transformation α` on sections as a Lie algebra homomorphism into
`(tangent I M).Sections` (without requiring `M` to be Hausdorff). -/
def transformationAnchorHom (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) :
    (transformation α).Sections →ₗ⁅ℝ⁆ (tangent I M).Sections where
  toFun s := (tangent I M).sectionsEquiv.symm
    ((transformation α).anchorField ((transformation α).sectionsEquiv s))
  map_add' s t := by simp only [map_add]
  map_smul' c s := by
    rw [LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower,
      LinearMapClass.map_smul_of_tower]
    rfl
  map_lie' := by
    intro s t
    apply (tangent I M).sectionsEquiv.injective
    have hField (u : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
        (transformation α).anchorField u = transformationAnchorField (toTangentLinearMap α) u := by
      ext x
      simp [toTangentLinearMap]
    simp only [LinearEquiv.apply_symm_apply, sectionsEquiv_lie, hField]
    exact transformationAnchorField_transformationBracket (toTangentLinearMap_lie α)
      ((transformation α).sectionsEquiv s) ((transformation α).sectionsEquiv t)

@[simp]
theorem sectionsEquiv_transformationAnchorHom (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections)
    (s : (transformation α).Sections) :
    (tangent I M).sectionsEquiv (transformationAnchorHom α s) =
      (transformation α).anchorField ((transformation α).sectionsEquiv s) :=
  (tangent I M).sectionsEquiv.apply_symm_apply _

@[simp]
theorem transformationAnchorHom_comp_transformationConst (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) :
    (transformationAnchorHom α).comp (transformationConst α) = α := by
  ext ξ
  apply (tangent I M).sectionsEquiv.injective
  simp

/-- The **isotropy Lie subalgebra** `ker ((transformation α).anchor x) ≤ 𝔤` of `transformation α`
at `x : M`. -/
def transformationIsotropy (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (x : M) : LieSubalgebra ℝ 𝔤 where
  toSubmodule := LinearMap.ker ((transformation α).anchor x).toLinearMap
  lie_mem' {ξ η} hξ hη := by
    rw [Submodule.mem_carrier, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, transformation_anchor_apply] at hξ hη ⊢
    rw [α.map_lie, sectionsEquiv_lie, tangent_bracket_apply]
    exact mlieBracket_eq_zero_of_eq_zero hξ hη

@[simp]
theorem mem_transformationIsotropy_iff (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (x : M) {ξ : 𝔤} :
    ξ ∈ transformationIsotropy α x ↔ (transformation α).anchor x ξ = 0 :=
  LinearMap.mem_ker

theorem transformationIsotropy_toSubmodule (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (x : M) :
    (transformationIsotropy α x).toSubmodule =
      LinearMap.ker ((transformation α).anchor x).toLinearMap :=
  (rfl)

/-! ### Functoriality in the Lie algebra and in the base manifold -/

section Functoriality

variable {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] [TopologicalSpace 𝔥]
  [IsTopologicalAddGroup 𝔥] [ContinuousSMul ℝ 𝔥] [T2Space 𝔥] [FiniteDimensional ℝ 𝔥]

/-- Pushforward of sections along a Lie algebra homomorphism `ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤` gives a Lie algebra
homomorphism `(transformation (α.comp ψ)).Sections →ₗ⁅ℝ⁆ (transformation α).Sections`. -/
def transformationMapLieHom (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤) :
    (transformation (α.comp ψ)).Sections →ₗ⁅ℝ⁆ (transformation α).Sections where
  toFun s := (transformation α).sectionsEquiv.symm
    (ContMDiffSection.modelMap ψ.toLinearMap ((transformation (α.comp ψ)).sectionsEquiv s))
  map_add' s t := by simp only [map_add]
  map_smul' c s := (transformation α).sectionsEquiv.injective <| by
    rw [LinearEquiv.apply_symm_apply, LinearMapClass.map_smul_of_tower,
      LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower,
      LinearEquiv.apply_symm_apply]
    rfl
  map_lie' := by
    intro s t
    apply (transformation α).sectionsEquiv.injective
    ext x
    simp [ContMDiffSection.modelDeriv_modelMap]

@[simp]
theorem transformationMapLieHom_smul (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤)
    (f : C^∞⟮I, M; ℝ⟯) (s : (transformation (α.comp ψ)).Sections) :
    transformationMapLieHom α ψ (f • s) = f • transformationMapLieHom α ψ s := by
  apply (transformation α).sectionsEquiv.injective
  simp [transformationMapLieHom]

@[simp]
theorem sectionsEquiv_transformationMapLieHom_apply
    (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤)
    (s : (transformation (α.comp ψ)).Sections) (x : M) :
    (transformation α).sectionsEquiv (transformationMapLieHom α ψ s) x =
      ψ ((transformation (α.comp ψ)).sectionsEquiv s x) := by
  simp [transformationMapLieHom]

@[simp]
theorem transformationAnchorHom_comp_transformationMapLieHom
    (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤) :
    (transformationAnchorHom α).comp (transformationMapLieHom α ψ) =
      transformationAnchorHom (α.comp ψ) := by
  ext s
  apply (tangent I M).sectionsEquiv.injective
  ext x
  simp

@[simp]
theorem transformationIsotropy_comp (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤)
    (x : M) :
    transformationIsotropy (α.comp ψ) x = (transformationIsotropy α x).comap ψ :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

end Functoriality

/-- Pullback of sections along a smooth map `φ : N → M` intertwining `α_N` and `α_M` is a Lie
algebra homomorphism `(transformation α_M).Sections →ₗ⁅ℝ⁆ (transformation α_N).Sections`. -/
def transformationPullback {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {α_M : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections} {α_N : 𝔤 →ₗ⁅ℝ⁆ (tangent J N).Sections}
    (φ : C^∞⟮J, N; I, M⟯)
    (hφ : ∀ (ξ : 𝔤) (y : N),
      mfderiv J I φ y ((tangent J N).sectionsEquiv (α_N ξ) y) =
        (tangent I M).sectionsEquiv (α_M ξ) (φ y)) :
    (transformation α_M).Sections →ₗ⁅ℝ⁆ (transformation α_N).Sections where
  toFun s := (transformation α_N).sectionsEquiv.symm <|
    ContMDiffSection.modelPullback φ ((transformation α_M).sectionsEquiv s)
  map_add' s t := (transformation α_N).sectionsEquiv.injective <| by ext y; simp
  map_smul' c s := (transformation α_N).sectionsEquiv.injective <| by
    rw [LinearMapClass.map_smul_of_tower, LinearEquiv.apply_symm_apply,
      LinearMapClass.map_smul_of_tower]
    ext y
    simp
  map_lie' := by
    intro s t
    apply (transformation α_N).sectionsEquiv.injective
    ext y
    simp [ContMDiffSection.modelDeriv_modelPullback, hφ]

@[simp]
theorem sectionsEquiv_transformationPullback_apply {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {α_M : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections} {α_N : 𝔤 →ₗ⁅ℝ⁆ (tangent J N).Sections}
    (φ : C^∞⟮J, N; I, M⟯) (hφ) (s : (transformation α_M).Sections) (y : N) :
    (transformation α_N).sectionsEquiv (transformationPullback φ hφ s) y =
      (transformation α_M).sectionsEquiv s (φ y) := by
  simp [transformationPullback]

end Homomorphism

end LieAlgebroid

/-! ### Infinitesimal actions and smooth Lie group actions -/

namespace InfinitesimalAction

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- Negating the vector fields of an infinitesimal action `act : InfinitesimalAction 𝔤 I M` turns
its antihomomorphism law `act ⁅ξ, η⁆ = -[act ξ, act η]` into a Lie algebra homomorphism
`𝔤 →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections`. -/
def negLieHom (act : InfinitesimalAction 𝔤 I M) :
    𝔤 →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections where
  toFun ξ := (LieAlgebroid.tangent I M).sectionsEquiv.symm
    { toFun := act (-ξ)
      contMDiff_toFun := act.contMDiff (-ξ) }
  map_add' ξ η := (LieAlgebroid.tangent I M).sectionsEquiv.injective <| by
    ext x
    simp [ContMDiffSection.coeFn_mk]
    abel
  map_smul' c ξ := (LieAlgebroid.tangent I M).sectionsEquiv.injective <| by
    rw [LinearEquiv.apply_symm_apply, LinearMapClass.map_smul_of_tower]
    ext x
    simp [ContMDiffSection.coeFn_mk]
  map_lie' := by
    intro ξ η
    apply (LieAlgebroid.tangent I M).sectionsEquiv.injective
    ext x
    simp only [LinearEquiv.apply_symm_apply, LieAlgebroid.sectionsEquiv_lie,
      LieAlgebroid.tangent_bracket_apply, ContMDiffSection.coeFn_mk]
    have hneg (ζ : 𝔤) : act (-ζ) = -act ζ := map_neg act ζ
    rw [hneg, hneg, hneg, act.map_lie, neg_neg, mlieBracket_neg_left, mlieBracket_neg_right,
      neg_neg]

@[simp]
theorem sectionsEquiv_negLieHom_apply (act : InfinitesimalAction 𝔤 I M)
    (ξ : 𝔤) (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv (act.negLieHom ξ) x = -act ξ x := by
  simp [negLieHom, ContMDiffSection.coeFn_mk]

section TopologicalLieAlgebra

variable [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤]
  [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

/-- The transformation Lie algebroid `M ⋉ 𝔤` of an infinitesimal action `act`, with anchor
`(x, ξ) ↦ -act ξ x`. -/
def lieAlgebroid (act : InfinitesimalAction 𝔤 I M) :
    LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
  LieAlgebroid.transformation act.negLieHom

@[simp]
theorem lieAlgebroid_anchor_apply (act : InfinitesimalAction 𝔤 I M)
    (x : M) (ξ : 𝔤) :
    act.lieAlgebroid.anchor x ξ = -act ξ x := by
  simp [lieAlgebroid]

@[simp]
theorem lieAlgebroid_isotropy (act : InfinitesimalAction 𝔤 I M) (x : M) :
    LieAlgebroid.transformationIsotropy act.negLieHom x = act.isotropy x :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

end TopologicalLieAlgebra

end InfinitesimalAction

namespace LieAlgebroid

section MulAction

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {J : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [LieGroup J (minSmoothness ℝ 3) G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul J I ∞ G M]

variable (J G I M) in
/-- The transformation Lie algebroid `M ⋉ Lie(G)` of a smooth left action of a finite-dimensional
real Lie group `G` on `M`, with anchor `(x, ξ) ↦ -fundamentalVectorField I ξ x`. -/
def ofMulAction :
    LieAlgebroid I (Bundle.TrivialModel ℝ (GroupLieAlgebra J G))
      (Bundle.Trivial M (GroupLieAlgebra J G)) :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  (InfinitesimalAction.fundamental J G I M).lieAlgebroid

@[simp]
theorem ofMulAction_anchor_apply (x : M) (ξ : GroupLieAlgebra J G) :
    (ofMulAction J G I M).anchor x ξ = -fundamentalVectorField I ξ x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  simp [ofMulAction]

/-- A smooth `G`-equivariant map `φ : N → M` pulls back sections of `ofMulAction J G I M` to
sections of `ofMulAction J G I' N` as a Lie algebra homomorphism. -/
def ofMulActionPullback {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    [MulAction G N] [ContMDiffSMul J I' ∞ G N]
    (φ : C^∞⟮I', N; I, M⟯) (hφ : ∀ (g : G) (y : N), φ (g • y) = g • φ y) :
    (ofMulAction J G I M).Sections →ₗ⁅ℝ⁆ (ofMulAction J G I' N).Sections :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (by simp)
  have : ContMDiffSMul J I' 1 G N := ContMDiffSMul.of_le (M := N) ENat.LEInfty.out
  transformationPullback φ fun ξ y ↦ by
    simp only [InfinitesimalAction.sectionsEquiv_negLieHom_apply,
      InfinitesimalAction.fundamental_apply, map_neg, neg_inj]
    exact mfderiv_fundamentalVectorField_of_map_smul
      (φ.contMDiff.mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := J) (I' := I') (n := 1) y).mdifferentiableAt
        one_ne_zero)
      (fun g ↦ hφ g y) ξ

end MulAction

/-! ### Standard examples and sign check -/

section TranslationAction

private def ofTangentV {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V)
    (w : TangentSpace 𝓘(ℝ, V) x) : V :=
  w

private def translationInvMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] [TopologicalSpace 𝔤]
    [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
    (τ : 𝔤 ≃ₗ[ℝ] V)
    (X : Cₛ^∞⟮𝓘(ℝ, V); V, (TangentSpace 𝓘(ℝ, V) : V → Type _)⟯) :
    C^∞⟮𝓘(ℝ, V), V; 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤), Bundle.TrivialModel ℝ 𝔤⟯ :=
  let negTauSymm : V →L[ℝ] Bundle.TrivialModel ℝ 𝔤 :=
    LinearMap.toContinuousLinearMap
      (-(Bundle.TrivialModel.equiv ℝ 𝔤).toLinearMap.comp τ.symm.toLinearMap)
  ⟨fun x ↦ negTauSymm (ofTangentV x (X x)),
    negTauSymm.contMDiff.comp
      (show ContDiff ℝ ∞ (fun x ↦ ofTangentV x (X x)) from
        contMDiff_vectorSpace_iff_contDiff.1 X.contMDiff).contMDiff⟩

private def translationInvSection {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] [TopologicalSpace 𝔤]
    [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
    (τ : 𝔤 ≃ₗ[ℝ] V)
    (X : Cₛ^∞⟮𝓘(ℝ, V); V, (TangentSpace 𝓘(ℝ, V) : V → Type _)⟯) :
    Cₛ^∞⟮𝓘(ℝ, V); Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial V 𝔤⟯ :=
  ContMDiffSection.modelEquiv.symm (translationInvMap τ X)

private theorem translationInvSection_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] [TopologicalSpace 𝔤]
    [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
    (τ : 𝔤 ≃ₗ[ℝ] V)
    (X : Cₛ^∞⟮𝓘(ℝ, V); V, (TangentSpace 𝓘(ℝ, V) : V → Type _)⟯) (x : V) :
    translationInvSection τ X x = -τ.symm (ofTangentV x (X x)) := by
  dsimp only [translationInvSection]
  rw [ContMDiffSection.modelEquiv_symm_apply]
  have hval : translationInvMap τ X x =
      (LinearMap.toContinuousLinearMap
        (-(Bundle.TrivialModel.equiv ℝ 𝔤).toLinearMap.comp τ.symm.toLinearMap))
        (ofTangentV x (X x)) := rfl
  rw [hval]
  simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [IsLieAbelian 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

/-- When an abelian Lie algebra `𝔤` acts on a finite-dimensional real normed space `V` by
translations along a linear equivalence `τ : 𝔤 ≃ₗ[ℝ] V`, the anchor `s ↦ (x ↦ -τ (s x))` is a
`C^∞⟮𝓘(ℝ, V), V; ℝ⟯`-linear equivalence from sections of the transformation Lie algebroid to
sections of the tangent Lie algebroid `tangent 𝓘(ℝ, V) V`. -/
def translationSectionsLinearEquiv (τ : 𝔤 ≃ₗ[ℝ] V) :
    ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections ≃ₗ[C^∞⟮𝓘(ℝ, V), V; ℝ⟯]
      (tangent 𝓘(ℝ, V) V).Sections :=
  let A := (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid
  { toFun s := (tangent 𝓘(ℝ, V) V).sectionsEquiv.symm (A.anchorField (A.sectionsEquiv s))
    invFun t := A.sectionsEquiv.symm
      (translationInvSection τ ((tangent 𝓘(ℝ, V) V).sectionsEquiv t))
    left_inv s := A.sectionsEquiv.injective <| by
      ext x
      simp only [LinearEquiv.apply_symm_apply]
      rw [translationInvSection_apply]
      have hA : ofTangentV x (A.anchorField (A.sectionsEquiv s) x) =
          -τ (A.sectionsEquiv s x) := by
        simp only [ofTangentV, anchorField_apply, A, InfinitesimalAction.lieAlgebroid_anchor_apply]
        exact (Pi.neg_apply _ _).trans
          (congrArg Neg.neg (InfinitesimalAction.translation_apply _ _ _))
      rw [hA]
      simp
    right_inv t := (tangent 𝓘(ℝ, V) V).sectionsEquiv.injective <| by
      ext x
      simp only [LinearEquiv.apply_symm_apply]
      rw [anchorField_apply, translationInvSection_apply]
      simp only [A, InfinitesimalAction.lieAlgebroid_anchor_apply]
      refine ((Pi.neg_apply _ _).trans
        (congrArg Neg.neg (InfinitesimalAction.translation_apply _ _ _))).trans ?_
      -- On the model manifold `V`, `TangentSpace 𝓘(ℝ, V) x` is `V`.
      change -τ (-τ.symm (ofTangentV x ((tangent 𝓘(ℝ, V) V).sectionsEquiv t x))) =
        ofTangentV x ((tangent 𝓘(ℝ, V) V).sectionsEquiv t x)
      simp
    map_add' s t := by simp only [map_add]
    map_smul' f s := by simp only [map_smul, RingHom.id_apply] }

/-- For the translation action of `𝔤 ≃ₗ[ℝ] V` on `V`, the anchor identifies sections of the
transformation Lie algebroid with `(tangent 𝓘(ℝ, V) V).Sections` as Lie algebras over `ℝ`. -/
def translationSectionsLieEquiv (τ : 𝔤 ≃ₗ[ℝ] V) :
    ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections ≃ₗ⁅ℝ⁆
      (tangent 𝓘(ℝ, V) V).Sections :=
  { (translationSectionsLinearEquiv τ).restrictScalars ℝ with
    map_lie' := by
      intro s t
      let A := (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid
      apply (tangent 𝓘(ℝ, V) V).sectionsEquiv.injective
      ext x
      have h := A.anchor_bracket (A.sectionsEquiv s) (A.sectionsEquiv t) x
      simpa [translationSectionsLinearEquiv, A] using h }

@[simp]
theorem sectionsEquiv_translationSectionsLieEquiv (τ : 𝔤 ≃ₗ[ℝ] V)
    (s : ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLieEquiv τ s) =
      ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).anchorField
        (((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).sectionsEquiv s) :=
  (tangent 𝓘(ℝ, V) V).sectionsEquiv.apply_symm_apply _

theorem sectionsEquiv_translationSectionsLieEquiv_apply (τ : 𝔤 ≃ₗ[ℝ] V)
    (s : ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections) (x : V) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLieEquiv τ s) x =
      -τ (((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).sectionsEquiv s x) := by
  have h1 := DFunLike.congr_fun (sectionsEquiv_translationSectionsLieEquiv τ s) x
  have h2 := anchorField_apply (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid
    (((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).sectionsEquiv s) x
  have h3 := InfinitesimalAction.lieAlgebroid_anchor_apply
    (InfinitesimalAction.translation τ.toLinearMap) x
    (((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).sectionsEquiv s x)
  exact ((h1.trans h2).trans h3).trans
    ((Pi.neg_apply _ _).trans (congrArg Neg.neg (InfinitesimalAction.translation_apply _ _ _)))

/-- The Lie algebra isomorphism `translationSectionsLieEquiv τ` intertwines the Lie–Rinehart anchor
actions on smooth scalar functions. -/
@[simp]
theorem lie_translationSectionsLieEquiv_apply (τ : 𝔤 ≃ₗ[ℝ] V)
    (s : ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections)
    (f : C^∞⟮𝓘(ℝ, V), V; ℝ⟯) :
    ⁅translationSectionsLieEquiv τ s, f⁆ = ⁅s, f⁆ := by
  rw [Sections.lie_def, Sections.lie_def, sectionsEquiv_translationSectionsLieEquiv]
  ext x
  simp

end TranslationAction

end LieAlgebroid

section AffineLine

/-- The standard infinitesimal action of the two-dimensional nonabelian Lie algebra
`LieAlgebra.AffineLine ℝ` on `ℝ`, sending the dilation `(1, 0)` to `x ↦ x` (`x ∂_x`) and the
translation `(0, 1)` to `x ↦ 1` (`∂_x`). -/
def InfinitesimalAction.affineLine :
    InfinitesimalAction (LieAlgebra.AffineLine ℝ) 𝓘(ℝ, ℝ) ℝ where
  toLinearMap :=
    { toFun u x := (u.1 * x + u.2 : ℝ)
      map_add' u v := funext fun x ↦ by
        -- On the model manifold `ℝ`, `TangentSpace 𝓘(ℝ, ℝ) x` is `ℝ`.
        change (u + v).1 * x + (u + v).2 = (u.1 * x + u.2) + (v.1 * x + v.2)
        simp [add_mul]
        ring
      map_smul' c u := funext fun x ↦ by
        -- On the model manifold `ℝ`, `TangentSpace 𝓘(ℝ, ℝ) x` is `ℝ`.
        change (c • u).1 * x + (c • u).2 = c * (u.1 * x + u.2)
        simp [mul_add, mul_assoc] }
  contMDiff_toLinearMap' u :=
    contMDiff_vectorSpace_iff_contDiff.2
      ((contDiff_const.mul contDiff_id).add contDiff_const)
  toLinearMap_lie' u v := by
    funext x
    let V (w : LieAlgebra.AffineLine ℝ) : ∀ y : ℝ, TangentSpace 𝓘(ℝ, ℝ) y :=
      fun y ↦ (w.1 * y + w.2 : ℝ)
    have hu (w : LieAlgebra.AffineLine ℝ) :
        HasFDerivAt (fun y : ℝ ↦ w.1 * y + w.2)
          (w.1 • ContinuousLinearMap.id ℝ ℝ) x := by
      simpa using ((hasFDerivAt_id x).const_mul w.1).add_const w.2
    -- Evaluate `toLinearMap` at `⁅u, v⁆` and expose the dependent section `V` for `mlieBracket`.
    change ((⁅u, v⁆ : LieAlgebra.AffineLine ℝ).1 * x +
        (⁅u, v⁆ : LieAlgebra.AffineLine ℝ).2 : ℝ) =
      -mlieBracket 𝓘(ℝ, ℝ) (V u) (V v) x
    rw [mlieBracket_eq_lieBracket]
    -- On the model manifold `ℝ`, `TangentSpace 𝓘(ℝ, ℝ) x` is `ℝ`.
    change ((⁅u, v⁆ : LieAlgebra.AffineLine ℝ).1 * x +
        (⁅u, v⁆ : LieAlgebra.AffineLine ℝ).2 : ℝ) =
      -lieBracket ℝ (fun y : ℝ ↦ u.1 * y + u.2) (fun y : ℝ ↦ v.1 * y + v.2) x
    rw [lieBracket_eq]
    dsimp only
    rw [(hu u).fderiv, (hu v).fderiv]
    simp only [LieAlgebra.AffineLine.fst_lie, LieAlgebra.AffineLine.snd_lie,
      _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring

@[simp]
theorem InfinitesimalAction.affineLine_apply (u : LieAlgebra.AffineLine ℝ) (x : ℝ) :
    InfinitesimalAction.affineLine u x = u.1 * x + u.2 :=
  (rfl)

namespace LieAlgebroid

/-- The un-negated linear map sending `u : LieAlgebra.AffineLine ℝ` to the affine vector field
`x ↦ u.1 * x + u.2` on `ℝ`. -/
def affineLinePosLinearMap :
    LieAlgebra.AffineLine ℝ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯ where
  toFun u :=
    { toFun := InfinitesimalAction.affineLine u
      contMDiff_toFun := InfinitesimalAction.affineLine.contMDiff u }
  map_add' u v := ContMDiffSection.ext fun x ↦ by simp
  map_smul' c u := ContMDiffSection.ext fun x ↦ by simp

/-- Omitting the minus sign on the infinitesimal generators `x ∂_x` and `∂_x` of
`LieAlgebra.AffineLine ℝ` violates the Jacobi identity for `transformationBracket`, because
`[x ∂_x, ∂_x] = -∂_x` whereas `⁅dilation ℝ, translation ℝ⁆ = +translation ℝ`. -/
theorem not_transformationBracket_jacobi_affineLine_pos :
    ¬∀ a b c : Cₛ^∞⟮𝓘(ℝ, ℝ); Bundle.TrivialModel ℝ (LieAlgebra.AffineLine ℝ),
        Bundle.Trivial ℝ (LieAlgebra.AffineLine ℝ)⟯,
      transformationBracket affineLinePosLinearMap a
          (transformationBracket affineLinePosLinearMap b c) =
        transformationBracket affineLinePosLinearMap
            (transformationBracket affineLinePosLinearMap a b) c +
          transformationBracket affineLinePosLinearMap b
            (transformationBracket affineLinePosLinearMap a c) := by
  intro hjac
  have hlie := (transformationBracket_jacobi_iff affineLinePosLinearMap).1 hjac
    (LieAlgebra.AffineLine.dilation ℝ) (LieAlgebra.AffineLine.translation ℝ)
  have h0 := congr($hlie 0)
  let Xd : ∀ x : ℝ, TangentSpace 𝓘(ℝ, ℝ) x := fun x ↦ (x : ℝ)
  have hd : ⇑(affineLinePosLinearMap (LieAlgebra.AffineLine.dilation ℝ)) = Xd :=
    funext fun x ↦ by
      rw [affineLinePosLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffSection.coeFn_mk,
        InfinitesimalAction.affineLine_apply, LieAlgebra.AffineLine.fst_dilation,
        LieAlgebra.AffineLine.snd_dilation, one_mul, add_zero]
  have ht : ⇑(affineLinePosLinearMap (LieAlgebra.AffineLine.translation ℝ)) =
      fun _ : ℝ ↦ (1 : ℝ) :=
    funext fun x ↦ by
      rw [affineLinePosLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffSection.coeFn_mk,
        InfinitesimalAction.affineLine_apply, LieAlgebra.AffineLine.fst_translation,
        LieAlgebra.AffineLine.snd_translation, zero_mul, zero_add]
  rw [LieAlgebra.AffineLine.lie_dilation_translation, tangent_bracket_apply, hd, ht,
    mlieBracket_const_right_model_space] at h0
  -- On `ℝ`, `TangentSpace 𝓘(ℝ, ℝ) 0` is `ℝ` and `Xd` is `fun x ↦ x`.
  change (1 : ℝ) = -fderiv ℝ (fun x : ℝ ↦ x) 0 1 at h0
  rw [fderiv_fun_id] at h0
  norm_num at h0

end LieAlgebroid

end AffineLine

end TauCeti
