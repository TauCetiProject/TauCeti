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
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Action (transformation) Lie algebroids

Given a finite-dimensional real Hausdorff topological Lie algebra `𝔤` and a Lie algebra homomorphism
`α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections`, the trivial bundle `Bundle.Trivial M 𝔤` carries the
**transformation** (or **action**) **Lie algebroid** `TauCeti.LieAlgebroid.transformation α` with
anchor `(x, ξ) ↦ α ξ x` and section bracket
`[a, b](x) = ⁅a(x), b(x)⁆ + b.modelDeriv x (α (a x) x) - a.modelDeriv x (α (b x) x)`.

`transformationAnchor` and `transformationBracket` are first defined for any `ℝ`-linear map
`α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, TangentSpace I⟯`: alternatingness and the Leibniz rule hold
unconditionally, while over a Hausdorff base `transformationBracket_jacobi_iff` shows Jacobi holds
if and only if `α₀` intertwines Lie brackets. Since an `InfinitesimalAction 𝔤 I M` satisfies the
antihomomorphism law `act ⁅ξ, η⁆ = -[act ξ, act η]`, negating it (`act.negLieHom`) yields
`act.lieAlgebroid` and `TauCeti.LieAlgebroid.ofMulAction`; omitting this minus sign on
`LieAlgebra.AffineLine ℝ` violates Jacobi (`not_transformationBracket_jacobi_affineLine_pos`), and
translation actions on vector spaces recover the tangent Lie algebroid
(`translationSectionsLieEquiv`).

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
  [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
  (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

/-- Smooth anchor bundle morphism `(x, ξ) ↦ α₀ ξ x` on `Bundle.Trivial M 𝔤` attached to an
`ℝ`-linear map `α₀` from `𝔤` into smooth tangent vector fields on `M`. -/
def transformationAnchor :
    Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤 →L[ℝ] E,
      fun x ↦ Bundle.Trivial M 𝔤 x →L[ℝ] TangentSpace I x⟯ :=
  let anchorLin (x : M) : Bundle.Trivial M 𝔤 x →ₗ[ℝ] TangentSpace I x :=
    ⟨⟨fun ξ ↦ α₀ ξ x, fun _ _ ↦ by simp⟩, fun _ _ ↦ by simp⟩
  { toFun x := LinearMap.toContinuousLinearMap (anchorLin x)
    contMDiff_toFun := by
      have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
      rw [contMDiff_hom_bundle_iff]
      let B := Module.finBasis ℝ 𝔤
      let e := Bundle.TrivialModel.equiv ℝ 𝔤
      have hproj : ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤)) I ∞
          (TotalSpace.proj (F := Bundle.TrivialModel ℝ 𝔤) (E := Bundle.Trivial M 𝔤)) :=
        contMDiff_proj (Bundle.Trivial M 𝔤)
      have hsnd : ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤)) 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤) ∞
          (fun p : TotalSpace (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) ↦ e p.2) :=
        (Bundle.TrivialModel.contMDiff_mk_iff.1 contMDiff_id).2
      have hcoord (i : Fin (Module.finrank ℝ 𝔤)) :
          ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤)) 𝓘(ℝ, ℝ) ∞
            (fun p : TotalSpace (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) ↦ B.coord i p.2) :=
        ((LinearMap.toContinuousLinearMap ((B.coord i).comp e.symm.toLinearMap)).contMDiff.comp
          hsnd).congr fun _ ↦ by simp [e]
      refine (ContMDiff.sum_sectionAlong (V := TangentSpace I) (b := TotalSpace.proj) Finset.univ
        (fun i p ↦ B.coord i p.2 • α₀ (B i) p.proj) hproj
        fun i _ ↦ (hcoord i).smul_totalSpace ((α₀ (B i)).contMDiff.comp hproj)).congr
        fun p ↦ congrArg (TotalSpace.mk' E p.proj) ?_
      simp only [LinearMap.coe_toContinuousLinearMap']
      conv_lhs => rw [← B.sum_repr p.2]
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ by simp [anchorLin] }

@[simp] theorem transformationAnchor_apply (x : M) (ξ : 𝔤) :
    transformationAnchor α₀ x ξ = α₀ ξ x := (rfl)

/-- Smooth tangent vector field `x ↦ α₀ (a x) x` induced by a smooth section `a` of
`Bundle.Trivial M 𝔤`, linear over `C^∞⟮I, M; ℝ⟯`. -/
def transformationAnchorField :
    Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  have h : ContMDiff (I.prod 𝓘(ℝ, Bundle.TrivialModel ℝ 𝔤)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) ↦
        (⟨p.proj, transformationAnchor α₀ p.proj p.2⟩ : TotalSpace E (TangentSpace I))) :=
    (contMDiff_hom_bundle_iff _).1 (transformationAnchor α₀).contMDiff
  { (ContMDiffSection.mapLinearMap (fun x ↦ (transformationAnchor α₀ x).toLinearMap) h).toAddHom
      with
    map_smul' := ContMDiffSection.mapLinearMap_smul_function
      (fun x ↦ (transformationAnchor α₀ x).toLinearMap) h }

@[simp] theorem transformationAnchorField_apply
    (a : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    transformationAnchorField α₀ a x = α₀ (a x) x := by simp [transformationAnchorField]

@[simp] theorem transformationAnchorField_modelConst (ξ : 𝔤) :
    transformationAnchorField α₀ (ContMDiffSection.modelConst I M ∞ ξ) = α₀ ξ := by ext x; simp

/-- The transformation section bracket on `Bundle.Trivial M 𝔤` attached to `α₀`:
`[a, b](x) = ⁅a x, b x⁆ + b.modelDeriv x (α₀ (a x) x) - a.modelDeriv x (α₀ (b x) x)`. -/
def transformationBracket :
    Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ :=
  LinearMap.mk₂ ℝ
    (fun a b ↦ (trivialLieAlgebra I M 𝔤).bracket a b +
      ContMDiffSection.modelLieDeriv (transformationAnchorField α₀ a) b -
      ContMDiffSection.modelLieDeriv (transformationAnchorField α₀ b) a)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by simp [ContMDiffSection.modelDeriv_add]; abel)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by
      simp [ContMDiffSection.modelDeriv_const_smul, smul_add, smul_sub])
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by simp [ContMDiffSection.modelDeriv_add]; abel)
    (fun _ _ _ ↦ ContMDiffSection.ext fun _ ↦ by
      simp [ContMDiffSection.modelDeriv_const_smul, smul_add, smul_sub])

@[simp] theorem transformationBracket_apply
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    transformationBracket α₀ a b x =
      ⁅a x, b x⁆ + b.modelDeriv x (α₀ (a x) x) - a.modelDeriv x (α₀ (b x) x) := by
  simp [transformationBracket]

@[simp] theorem transformationBracket_self
    (a : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a a = 0 := by ext x; simp

theorem transformationBracket_swap (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a b = -transformationBracket α₀ b a := by
  ext x; simp only [transformationBracket_apply, ContMDiffSection.coe_neg, Pi.neg_apply,
    ← lie_skew (a x) (b x)]; abel

theorem transformationBracket_smul_apply
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    transformationBracket α₀ a (f • b) x =
      f x • transformationBracket α₀ a b x +
        mvfderiv I f x (transformationAnchor α₀ x (a x)) • b x := by
  simp only [transformationBracket_apply, ContMDiffSection.smul_apply, lie_smul,
    ContMDiffSection.modelDeriv_smul, map_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    transformationAnchor_apply, smul_add, smul_sub]; abel

@[simp] theorem transformationBracket_modelConst (ξ η : 𝔤) :
    transformationBracket α₀
        (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η) =
      ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ := by ext x; simp

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
  ext x; rw [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.smul_apply,
    ContMDiffSection.smul_apply, transformationBracket_smul_apply]; simp

/-- Whenever `α₀` intertwines Lie brackets, `transformationAnchorField α₀` intertwines
`transformationBracket α₀` with the tangent bracket on all smooth sections. -/
theorem transformationAnchorField_transformationBracket
    {α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hα : ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η))
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationAnchorField α₀ (transformationBracket α₀ a b) =
      (tangent I M).bracket (transformationAnchorField α₀ a) (transformationAnchorField α₀ b) := by
  -- Both sides satisfy the same Leibniz rules, reducing via a finite basis of `𝔤` to `hα`.
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
        (tangent I M).bracket (transformationAnchorField α₀ v) (transformationAnchorField α₀ u) :=
      by rw [transformationBracket_swap, map_neg, huv, (tangent I M).bracket_swap, neg_neg]
    rw [transformationBracket_swap, map_neg, hsmul_right hvu f, (tangent I M).bracket_swap, neg_neg]
  let B := Module.finBasis ℝ 𝔤
  rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B a,
    ContMDiffSection.eq_sum_modelCoord_smul_modelConst B b]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    hsmul_left (hsmul_right (by simp [hα]) _) _

/-- Whenever `α₀` intertwines Lie brackets, `transformationBracket α₀` satisfies the Jacobi
identity. -/
theorem transformationBracket_jacobi
    {α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hα : ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η))
    (a b c : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :
    transformationBracket α₀ a (transformationBracket α₀ b c) =
      transformationBracket α₀ (transformationBracket α₀ a b) c +
        transformationBracket α₀ b (transformationBracket α₀ a c) := by
  -- The Jacobiator `J` is `C^∞(M, ℝ)`-trilinear by `hα` and skew-symmetry, reducing to `𝔤`.
  let br := transformationBracket α₀
  let J (u v w : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) :=
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
  let B := Module.finBasis ℝ 𝔤
  have vanish {P : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯ →
      Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯} (h0 : P 0 = 0)
      (hadd : ∀ x y, P (x + y) = P x + P y) (hsmul : ∀ (f : C^∞⟮I, M; ℝ⟯) x, P (f • x) = f • P x)
      (hB : ∀ i, P (ContMDiffSection.modelConst I M ∞ (B i)) = 0) (s) : P s = 0 := by
    rw [ContMDiffSection.eq_sum_modelCoord_smul_modelConst B s]
    suffices ∀ r, P (∑ i ∈ r, s.modelCoord B i • ContMDiffSection.modelConst I M ∞ (B i)) = 0 from
      this Finset.univ
    intro r; refine Finset.induction_on r (by simpa using h0) fun i r hi ih ↦ ?_
    rw [Finset.sum_insert hi, hadd, ih, add_zero, hsmul, hB i]; ext x; simp
  have hJ₁ (ξ η : 𝔤) (w) :
      J (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η) w = 0 :=
    vanish (by simp [J]) (fun _ _ ↦ by simp only [J, map_add]; abel) (fun f x ↦ hJ_smul₃ _ _ x f)
      (fun _ ↦ by ext x; simp [J, br]) w
  have hJ₂ (ξ : 𝔤) (v w) : J (ContMDiffSection.modelConst I M ∞ ξ) v w = 0 :=
    vanish (P := fun v ↦ J (ContMDiffSection.modelConst I M ∞ ξ) v w) (by simp [J])
      (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel)
      (fun f x ↦ hJ_smul₂ _ x w f) (fun j ↦ hJ₁ ξ (B j) w) v
  have hJ_zero : J a b c = 0 :=
    vanish (P := fun u ↦ J u b c) (by simp [J])
      (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel)
      (fun f x ↦ hJ_smul₁ x b c f) (fun i ↦ hJ₂ (B i) b c) a
  dsimp only [J, br] at hJ_zero; rwa [sub_eq_zero, sub_eq_iff_eq_add, add_comm] at hJ_zero

/-- Over a Hausdorff base, `transformationBracket α₀` satisfies the Jacobi identity if and only if
`α₀` intertwines the Lie bracket of `𝔤` with the Lie bracket of smooth tangent vector fields. -/
theorem transformationBracket_jacobi_iff [T2Space M]
    (α₀ : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (∀ a b c, transformationBracket α₀ a (transformationBracket α₀ b c) =
        transformationBracket α₀ (transformationBracket α₀ a b) c +
          transformationBracket α₀ b (transformationBracket α₀ a c)) ↔
      ∀ ξ η : 𝔤, α₀ ⁅ξ, η⁆ = (tangent I M).bracket (α₀ ξ) (α₀ η) := by
  refine ⟨fun hjac ξ η ↦ ?_, transformationBracket_jacobi⟩
  let A : LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
    ⟨transformationAnchor α₀, transformationBracket α₀, transformationBracket_self α₀,
      hjac, transformationBracket_smul_apply α₀⟩
  ext x; have h := A.anchor_bracket (ContMDiffSection.modelConst I M ∞ ξ)
    (ContMDiffSection.modelConst I M ∞ η) x
  have hc (ζ) : ⇑(A.anchorField (ContMDiffSection.modelConst I M ∞ ζ)) = ⇑(α₀ ζ) :=
    funext fun _ ↦ by simp [A]
  simpa [A, hc] using h

/-! ### The transformation Lie algebroid of a Lie algebra homomorphism -/

section LieHom

variable (α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections)

private def toTangentLinearMap : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ((tangent I M).sectionsEquiv.restrictScalars ℝ).toLinearMap.comp α.toLinearMap

omit [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤]
  [FiniteDimensional ℝ 𝔤] in
private theorem toTangentLinearMap_lie (ξ η : 𝔤) :
    toTangentLinearMap α ⁅ξ, η⁆ =
      (tangent I M).bracket (toTangentLinearMap α ξ) (toTangentLinearMap α η) := by
  simp [toTangentLinearMap]

/-- The **transformation** (or **action**) **Lie algebroid** `M ⋉ 𝔤` on `Bundle.Trivial M 𝔤`
associated with a Lie algebra homomorphism `α : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections`. -/
def transformation : LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) where
  anchor := transformationAnchor (toTangentLinearMap α)
  bracket := transformationBracket (toTangentLinearMap α)
  bracket_self := transformationBracket_self (toTangentLinearMap α)
  bracket_bracket := transformationBracket_jacobi (toTangentLinearMap_lie α)
  bracket_smul_apply := transformationBracket_smul_apply (toTangentLinearMap α)

@[simp] theorem transformation_anchor_apply (x : M) (ξ : 𝔤) :
    (transformation α).anchor x ξ = (tangent I M).sectionsEquiv (α ξ) x := by
  simp [transformation, toTangentLinearMap]

@[simp] theorem transformation_anchorField_modelConst (ξ : 𝔤) :
    (transformation α).anchorField (ContMDiffSection.modelConst I M ∞ ξ) =
      (tangent I M).sectionsEquiv (α ξ) := by ext x; simp

@[simp] theorem transformation_bracket_apply
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    (transformation α).bracket a b x =
      ⁅a x, b x⁆ + b.modelDeriv x ((tangent I M).sectionsEquiv (α (a x)) x) -
        a.modelDeriv x ((tangent I M).sectionsEquiv (α (b x)) x) := by
  simp [transformation, toTangentLinearMap]

@[simp] theorem transformation_bracket_modelConst (ξ η : 𝔤) :
    (transformation α).bracket
        (ContMDiffSection.modelConst I M ∞ ξ) (ContMDiffSection.modelConst I M ∞ η) =
      ContMDiffSection.modelConst I M ∞ ⁅ξ, η⁆ :=
  transformationBracket_modelConst (toTangentLinearMap α) ξ η

/-- The transformation Lie algebroid of the zero homomorphism is `trivialLieAlgebra I M 𝔤`. -/
@[simp] theorem transformation_zero :
    transformation (0 : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections) = trivialLieAlgebra I M 𝔤 := by
  refine LieAlgebroid.ext (ContMDiffSection.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp)
    (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ContMDiffSection.ext fun _ ↦ by simp)

/-- Constant sections define a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections`. -/
def transformationConst : 𝔤 →ₗ⁅ℝ⁆ (transformation α).Sections where
  toFun ξ := (transformation α).sectionsEquiv.symm (ContMDiffSection.modelConst I M ∞ ξ)
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by rw [map_smul, LinearMapClass.map_smul_of_tower]; rfl
  map_lie' := by intro _ _; exact (transformation α).sectionsEquiv.injective (by simp)

@[simp] theorem sectionsEquiv_transformationConst (ξ : 𝔤) :
    (transformation α).sectionsEquiv (transformationConst α ξ) =
      ContMDiffSection.modelConst I M ∞ ξ :=
  (transformation α).sectionsEquiv.apply_symm_apply _

theorem transformationConst_injective [Nonempty M] :
    Function.Injective (transformationConst α) := fun _ _ h ↦
  ContMDiffSection.modelConst_injective <|
    by simpa using congrArg (transformation α).sectionsEquiv h

/-- The anchor of `transformation α` on sections as a Lie algebra homomorphism into
`(tangent I M).Sections`. -/
def transformationAnchorHom : (transformation α).Sections →ₗ⁅ℝ⁆ (tangent I M).Sections where
  toFun s := (tangent I M).sectionsEquiv.symm
    ((transformation α).anchorField ((transformation α).sectionsEquiv s))
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by
    rw [LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower,
      LinearMapClass.map_smul_of_tower]; rfl
  map_lie' := by
    intro s t; apply (tangent I M).sectionsEquiv.injective
    have hField (u) :
        (transformation α).anchorField u = transformationAnchorField (toTangentLinearMap α) u := by
      ext x; simp [toTangentLinearMap]
    simp only [LinearEquiv.apply_symm_apply, sectionsEquiv_lie, hField]
    exact transformationAnchorField_transformationBracket (toTangentLinearMap_lie α)
      ((transformation α).sectionsEquiv s) ((transformation α).sectionsEquiv t)

@[simp] theorem sectionsEquiv_transformationAnchorHom (s : (transformation α).Sections) :
    (tangent I M).sectionsEquiv (transformationAnchorHom α s) =
      (transformation α).anchorField ((transformation α).sectionsEquiv s) :=
  (tangent I M).sectionsEquiv.apply_symm_apply _

@[simp] theorem transformationAnchorHom_comp_transformationConst :
    (transformationAnchorHom α).comp (transformationConst α) = α := by
  ext ξ; exact (tangent I M).sectionsEquiv.injective (by simp)

/-- The **isotropy Lie subalgebra** `ker ((transformation α).anchor x) ≤ 𝔤` at `x : M`. -/
def transformationIsotropy (x : M) : LieSubalgebra ℝ 𝔤 where
  toSubmodule := LinearMap.ker ((transformation α).anchor x).toLinearMap
  lie_mem' hξ hη := by
    rw [Submodule.mem_carrier, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, transformation_anchor_apply] at hξ hη ⊢
    rw [α.map_lie, sectionsEquiv_lie, tangent_bracket_apply]
    exact mlieBracket_eq_zero_of_eq_zero hξ hη

@[simp] theorem mem_transformationIsotropy_iff (x : M) {ξ : 𝔤} :
    ξ ∈ transformationIsotropy α x ↔ (transformation α).anchor x ξ = 0 := LinearMap.mem_ker

theorem transformationIsotropy_toSubmodule (x : M) :
    (transformationIsotropy α x).toSubmodule =
      LinearMap.ker ((transformation α).anchor x).toLinearMap := (rfl)

/-! ### Functoriality in the Lie algebra and in the base manifold -/

variable {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] [TopologicalSpace 𝔥]
  [IsTopologicalAddGroup 𝔥] [ContinuousSMul ℝ 𝔥] [T2Space 𝔥] [FiniteDimensional ℝ 𝔥]
  (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤)

/-- Pushforward of sections along a Lie algebra homomorphism `ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤` gives a Lie algebra
homomorphism `(transformation (α.comp ψ)).Sections →ₗ⁅ℝ⁆ (transformation α).Sections`. -/
def transformationMapLieHom :
    (transformation (α.comp ψ)).Sections →ₗ⁅ℝ⁆ (transformation α).Sections where
  toFun s := (transformation α).sectionsEquiv.symm
    (ContMDiffSection.modelMap ψ.toLinearMap ((transformation (α.comp ψ)).sectionsEquiv s))
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := (transformation α).sectionsEquiv.injective <| by
    rw [LinearEquiv.apply_symm_apply, LinearMapClass.map_smul_of_tower,
      LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower,
      LinearEquiv.apply_symm_apply]; rfl
  map_lie' := by
    intro _ _; apply (transformation α).sectionsEquiv.injective
    ext x; simp [ContMDiffSection.modelDeriv_modelMap]

@[simp] theorem transformationMapLieHom_smul (f : C^∞⟮I, M; ℝ⟯)
    (s : (transformation (α.comp ψ)).Sections) :
    transformationMapLieHom α ψ (f • s) = f • transformationMapLieHom α ψ s :=
  (transformation α).sectionsEquiv.injective <| by simp [transformationMapLieHom]

@[simp] theorem sectionsEquiv_transformationMapLieHom_apply
    (s : (transformation (α.comp ψ)).Sections) (x : M) :
    (transformation α).sectionsEquiv (transformationMapLieHom α ψ s) x =
      ψ ((transformation (α.comp ψ)).sectionsEquiv s x) := by simp [transformationMapLieHom]

@[simp] theorem transformationAnchorHom_comp_transformationMapLieHom :
    (transformationAnchorHom α).comp (transformationMapLieHom α ψ) =
      transformationAnchorHom (α.comp ψ) := by
  ext s; exact (tangent I M).sectionsEquiv.injective (by ext x; simp)

@[simp] theorem transformationIsotropy_comp (x : M) :
    transformationIsotropy (α.comp ψ) x = (transformationIsotropy α x).comap ψ :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

end LieHom

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {α_M : 𝔤 →ₗ⁅ℝ⁆ (tangent I M).Sections} {α_N : 𝔤 →ₗ⁅ℝ⁆ (tangent J N).Sections}

/-- Pullback of sections along a smooth map `φ : N → M` intertwining `α_N` and `α_M` is a Lie
algebra homomorphism `(transformation α_M).Sections →ₗ⁅ℝ⁆ (transformation α_N).Sections`. -/
def transformationPullback (φ : C^∞⟮J, N; I, M⟯)
    (hφ : ∀ (ξ : 𝔤) (y : N), mfderiv J I φ y ((tangent J N).sectionsEquiv (α_N ξ) y) =
      (tangent I M).sectionsEquiv (α_M ξ) (φ y)) :
    (transformation α_M).Sections →ₗ⁅ℝ⁆ (transformation α_N).Sections where
  toFun s := (transformation α_N).sectionsEquiv.symm <|
    ContMDiffSection.modelPullback φ ((transformation α_M).sectionsEquiv s)
  map_add' _ _ := (transformation α_N).sectionsEquiv.injective <| by ext y; simp
  map_smul' _ _ := (transformation α_N).sectionsEquiv.injective <| by
    rw [LinearMapClass.map_smul_of_tower, LinearEquiv.apply_symm_apply,
      LinearMapClass.map_smul_of_tower]; ext y; simp
  map_lie' := by
    intro _ _; apply (transformation α_N).sectionsEquiv.injective
    ext y; simp [ContMDiffSection.modelDeriv_modelPullback, hφ]

@[simp] theorem sectionsEquiv_transformationPullback_apply (φ : C^∞⟮J, N; I, M⟯) (hφ)
    (s : (transformation α_M).Sections) (y : N) :
    (transformation α_N).sectionsEquiv (transformationPullback φ hφ s) y =
      (transformation α_M).sectionsEquiv s (φ y) := by simp [transformationPullback]

end Homomorphism

end LieAlgebroid

/-! ### Infinitesimal actions and smooth Lie group actions -/

namespace InfinitesimalAction

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (act : InfinitesimalAction 𝔤 I M)

/-- Negating an infinitesimal action turns its antihomomorphism law `act ⁅ξ, η⁆ = -[act ξ, act η]`
into a Lie algebra homomorphism `𝔤 →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections`. -/
def negLieHom : 𝔤 →ₗ⁅ℝ⁆ (LieAlgebroid.tangent I M).Sections where
  toFun ξ := (LieAlgebroid.tangent I M).sectionsEquiv.symm ⟨act (-ξ), act.contMDiff (-ξ)⟩
  map_add' _ _ := (LieAlgebroid.tangent I M).sectionsEquiv.injective <| by
    ext x; simp [ContMDiffSection.coeFn_mk]; abel
  map_smul' _ _ := (LieAlgebroid.tangent I M).sectionsEquiv.injective <| by
    rw [LinearEquiv.apply_symm_apply, LinearMapClass.map_smul_of_tower]
    ext x; simp [ContMDiffSection.coeFn_mk]
  map_lie' := by
    intro _ _; apply (LieAlgebroid.tangent I M).sectionsEquiv.injective
    ext x
    simp only [LinearEquiv.apply_symm_apply, LieAlgebroid.sectionsEquiv_lie,
      LieAlgebroid.tangent_bracket_apply, ContMDiffSection.coeFn_mk]
    have hneg (ζ : 𝔤) : act (-ζ) = -act ζ := map_neg act ζ
    rw [hneg, hneg, hneg, act.map_lie, neg_neg, mlieBracket_neg_left, mlieBracket_neg_right,
      neg_neg]

@[simp] theorem sectionsEquiv_negLieHom_apply (ξ : 𝔤) (x : M) :
    (LieAlgebroid.tangent I M).sectionsEquiv (act.negLieHom ξ) x = -act ξ x := by
  simp [negLieHom, ContMDiffSection.coeFn_mk]

variable [TopologicalSpace 𝔤] [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤]
  [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]

/-- The transformation Lie algebroid `M ⋉ 𝔤` of an infinitesimal action `act`, with anchor
`(x, ξ) ↦ -act ξ x`. -/
def lieAlgebroid : LieAlgebroid I (Bundle.TrivialModel ℝ 𝔤) (Bundle.Trivial M 𝔤) :=
  LieAlgebroid.transformation act.negLieHom

theorem lieAlgebroid_eq : act.lieAlgebroid = LieAlgebroid.transformation act.negLieHom := (rfl)

@[simp] theorem lieAlgebroid_anchor_apply (x : M) (ξ : 𝔤) :
    act.lieAlgebroid.anchor x ξ = -act ξ x := by simp [lieAlgebroid]

@[simp] theorem lieAlgebroid_bracket_apply
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial M 𝔤⟯) (x : M) :
    act.lieAlgebroid.bracket a b x =
      ⁅a x, b x⁆ - b.modelDeriv x (act (a x) x) + a.modelDeriv x (act (b x) x) := by
  simp only [lieAlgebroid, LieAlgebroid.transformation_bracket_apply,
    sectionsEquiv_negLieHom_apply, map_neg]; abel

@[simp] theorem lieAlgebroid_isotropy (x : M) :
    LieAlgebroid.transformationIsotropy act.negLieHom x = act.isotropy x :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

end InfinitesimalAction

namespace LieAlgebroid

section MulAction

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {J : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup J (minSmoothness ℝ 3) G] {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MulAction G M] [ContMDiffSMul J I ∞ G M]

variable (J G I M) in
/-- The transformation Lie algebroid `M ⋉ Lie(G)` of a smooth left action of a finite-dimensional
real Lie group `G` on `M`, with anchor `(x, ξ) ↦ -fundamentalVectorField I ξ x`. -/
def ofMulAction :
    LieAlgebroid I (Bundle.TrivialModel ℝ (GroupLieAlgebra J G))
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
    (a b : Cₛ^∞⟮I; Bundle.TrivialModel ℝ (GroupLieAlgebra J G),
      Bundle.Trivial M (GroupLieAlgebra J G)⟯) (x : M) :
    (ofMulAction J G I M).bracket a b x =
      ⁅a x, b x⁆ - b.modelDeriv x (fundamentalVectorField I (a x) x) +
        a.modelDeriv x (fundamentalVectorField I (b x) x) := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp); simp [ofMulAction]

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] [MulAction G N] [ContMDiffSMul J I' ∞ G N]

/-- A smooth `G`-equivariant map `φ : N → M` pulls back sections of `ofMulAction J G I M` to
sections of `ofMulAction J G I' N` as a Lie algebra homomorphism. -/
def ofMulActionPullback (φ : C^∞⟮I', N; I, M⟯) (hφ : ∀ (g : G) (y : N), φ (g • y) = g • φ y) :
    (ofMulAction J G I M).Sections →ₗ⁅ℝ⁆ (ofMulAction J G I' N).Sections :=
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold I' 1 N := .of_le (n := ∞) (by simp)
  have : ContMDiffSMul J I' 1 G N := .of_le (M := N) ENat.LEInfty.out
  transformationPullback φ fun ξ y ↦ by
    simp only [InfinitesimalAction.sectionsEquiv_negLieHom_apply,
      InfinitesimalAction.fundamental_apply, map_neg, neg_inj]
    exact mfderiv_fundamentalVectorField_of_map_smul (φ.contMDiff.mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := J) (I' := I') (n := 1) y).mdifferentiableAt
        one_ne_zero) (fun g ↦ hφ g y) ξ

@[simp] theorem sectionsEquiv_ofMulActionPullback_apply
    (φ : C^∞⟮I', N; I, M⟯) (hφ : ∀ (g : G) (y : N), φ (g • y) = g • φ y)
    (s : (ofMulAction J G I M).Sections) (y : N) :
    (ofMulAction J G I' N).sectionsEquiv (ofMulActionPullback φ hφ s) y =
      (ofMulAction J G I M).sectionsEquiv s (φ y) := by
  have h : ofMulActionPullback φ hφ s = (ofMulAction J G I' N).sectionsEquiv.symm
      (ContMDiffSection.modelPullback φ ((ofMulAction J G I M).sectionsEquiv s)) := rfl
  rw [h, LinearEquiv.apply_symm_apply, ContMDiffSection.modelPullback_apply]

end MulAction

/-! ### Standard examples and sign check -/

section TranslationAction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [IsLieAbelian 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤]
  (τ : 𝔤 ≃ₗ[ℝ] V)

omit [FiniteDimensional ℝ V] [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [IsLieAbelian 𝔤] [TopologicalSpace 𝔤]
  [IsTopologicalAddGroup 𝔤] [ContinuousSMul ℝ 𝔤] [T2Space 𝔤] [FiniteDimensional ℝ 𝔤] in
private def ofTangentV (x : V) (w : TangentSpace 𝓘(ℝ, V) x) : V := w

omit [IsLieAbelian 𝔤] in
private def translationInvSection (X : Cₛ^∞⟮𝓘(ℝ, V); V, (TangentSpace 𝓘(ℝ, V) : V → Type _)⟯) :
    Cₛ^∞⟮𝓘(ℝ, V); Bundle.TrivialModel ℝ 𝔤, Bundle.Trivial V 𝔤⟯ :=
  let L : V →L[ℝ] Bundle.TrivialModel ℝ 𝔤 := LinearMap.toContinuousLinearMap
    (-(Bundle.TrivialModel.equiv ℝ 𝔤).toLinearMap.comp τ.symm.toLinearMap)
  -- On a normed vector space `V`, `contMDiff_vectorSpace_iff_contDiff` identifies smooth tangent
  -- vector fields with smooth maps `V → V`, which here is `fun x ↦ ofTangentV x (X x)`.
  have hX : ContDiff ℝ ∞ (fun x ↦ ofTangentV x (X x)) :=
    contMDiff_vectorSpace_iff_contDiff.1 X.contMDiff
  ⟨fun x ↦ -τ.symm (ofTangentV x (X x)), Bundle.TrivialModel.contMDiff_mk_iff.2
    ⟨contMDiff_id, (L.contMDiff.comp hX.contMDiff).congr fun _ ↦ by simp [L]⟩⟩

/-- When an abelian Lie algebra `𝔤` acts on `V` by translations along `τ : 𝔤 ≃ₗ[ℝ] V`, the anchor
`s ↦ (x ↦ -τ (s x))` is a `C^∞⟮𝓘(ℝ, V), V; ℝ⟯`-linear equivalence onto
`(tangent 𝓘(ℝ, V) V).Sections`. -/
def translationSectionsLinearEquiv :
    ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections ≃ₗ[C^∞⟮𝓘(ℝ, V), V; ℝ⟯]
      (tangent 𝓘(ℝ, V) V).Sections :=
  let A := (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid
  { toFun s := (tangent 𝓘(ℝ, V) V).sectionsEquiv.symm (A.anchorField (A.sectionsEquiv s))
    invFun t := A.sectionsEquiv.symm
      (translationInvSection τ ((tangent 𝓘(ℝ, V) V).sectionsEquiv t))
    left_inv s := A.sectionsEquiv.injective <| by
      ext x; simp only [LinearEquiv.apply_symm_apply, translationInvSection,
        ContMDiffSection.coeFn_mk]
      have hA : ofTangentV x (A.anchorField (A.sectionsEquiv s) x) = -τ (A.sectionsEquiv s x) := by
        simp only [ofTangentV, anchorField_apply, A, InfinitesimalAction.lieAlgebroid_anchor_apply]
        exact (Pi.neg_apply _ _).trans
          (congrArg Neg.neg (InfinitesimalAction.translation_apply _ _ _))
      rw [hA]; simp
    right_inv t := (tangent 𝓘(ℝ, V) V).sectionsEquiv.injective <| by
      ext x; simp only [LinearEquiv.apply_symm_apply, anchorField_apply, translationInvSection,
        ContMDiffSection.coeFn_mk, A, InfinitesimalAction.lieAlgebroid_anchor_apply]
      refine ((Pi.neg_apply _ _).trans
        (congrArg Neg.neg (InfinitesimalAction.translation_apply _ _ _))).trans ?_
      -- On the model manifold `V`, `TangentSpace 𝓘(ℝ, V) x` is `V`.
      change -τ (-τ.symm (ofTangentV x ((tangent 𝓘(ℝ, V) V).sectionsEquiv t x))) =
        ofTangentV x ((tangent 𝓘(ℝ, V) V).sectionsEquiv t x)
      simp
    map_add' _ _ := by simp only [map_add]
    map_smul' _ _ := by simp only [map_smul, RingHom.id_apply] }

/-- For the translation action of `𝔤 ≃ₗ[ℝ] V` on `V`, the anchor identifies sections of the
transformation Lie algebroid with `(tangent 𝓘(ℝ, V) V).Sections` as Lie algebras over `ℝ`. -/
def translationSectionsLieEquiv :
    ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections ≃ₗ⁅ℝ⁆
      (tangent 𝓘(ℝ, V) V).Sections :=
  { (translationSectionsLinearEquiv τ).restrictScalars ℝ with
    map_lie' := by
      intro s t; apply (tangent 𝓘(ℝ, V) V).sectionsEquiv.injective
      let A := (InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid
      ext x; simpa [translationSectionsLinearEquiv, A] using
        A.anchor_bracket (A.sectionsEquiv s) (A.sectionsEquiv t) x }

@[simp] theorem sectionsEquiv_translationSectionsLieEquiv
    (s : ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLieEquiv τ s) =
      ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).anchorField
        (((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).sectionsEquiv s) :=
  (tangent 𝓘(ℝ, V) V).sectionsEquiv.apply_symm_apply _

theorem sectionsEquiv_translationSectionsLieEquiv_apply
    (s : ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections) (x : V) :
    (tangent 𝓘(ℝ, V) V).sectionsEquiv (translationSectionsLieEquiv τ s) x =
      -τ (((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).sectionsEquiv s x) := by
  rw [sectionsEquiv_translationSectionsLieEquiv, anchorField_apply,
    InfinitesimalAction.lieAlgebroid_anchor_apply]
  exact (Pi.neg_apply _ _).trans (congrArg Neg.neg (InfinitesimalAction.translation_apply _ _ _))

/-- `translationSectionsLieEquiv τ` intertwines the Lie–Rinehart anchor actions on smooth scalar
functions. -/
@[simp] theorem lie_translationSectionsLieEquiv_apply
    (s : ((InfinitesimalAction.translation τ.toLinearMap).lieAlgebroid).Sections)
    (f : C^∞⟮𝓘(ℝ, V), V; ℝ⟯) :
    ⁅translationSectionsLieEquiv τ s, f⁆ = ⁅s, f⁆ := by
  rw [Sections.lie_def, Sections.lie_def, sectionsEquiv_translationSectionsLieEquiv]; ext x; simp

end TranslationAction

/-- The un-negated linear map sending `u : LieAlgebra.AffineLine ℝ` to `x ↦ u.1 * x + u.2`. -/
def affineLinePosLinearMap :
    LieAlgebra.AffineLine ℝ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯ where
  toFun u := ⟨InfinitesimalAction.affineLine u, InfinitesimalAction.affineLine.contMDiff u⟩
  map_add' _ _ := ContMDiffSection.ext fun _ ↦ by simp
  map_smul' _ _ := ContMDiffSection.ext fun _ ↦ by simp

@[simp] private theorem affineLinePosLinearMap_apply (u : LieAlgebra.AffineLine ℝ) (x : ℝ) :
    affineLinePosLinearMap u x = u.1 * x + u.2 := by simp [affineLinePosLinearMap]; rfl

/-- Omitting the minus sign on the infinitesimal generators `x ∂_x` and `∂_x` of
`LieAlgebra.AffineLine ℝ` violates the Jacobi identity for `transformationBracket`. -/
theorem not_transformationBracket_jacobi_affineLine_pos :
    ¬∀ a b c : Cₛ^∞⟮𝓘(ℝ, ℝ); Bundle.TrivialModel ℝ (LieAlgebra.AffineLine ℝ),
        Bundle.Trivial ℝ (LieAlgebra.AffineLine ℝ)⟯,
      transformationBracket affineLinePosLinearMap a
          (transformationBracket affineLinePosLinearMap b c) =
        transformationBracket affineLinePosLinearMap
            (transformationBracket affineLinePosLinearMap a b) c +
          transformationBracket affineLinePosLinearMap b
            (transformationBracket affineLinePosLinearMap a c) := fun hjac ↦ by
  have h0 := congr($((transformationBracket_jacobi_iff affineLinePosLinearMap).1 hjac
    (LieAlgebra.AffineLine.dilation ℝ) (LieAlgebra.AffineLine.translation ℝ)) 0)
  let Xd : ∀ x : ℝ, TangentSpace 𝓘(ℝ, ℝ) x := fun x ↦ (x : ℝ)
  have hd : ⇑(affineLinePosLinearMap (LieAlgebra.AffineLine.dilation ℝ)) = Xd :=
    funext fun _ ↦ by simp [Xd]; rfl
  have ht : ⇑(affineLinePosLinearMap (LieAlgebra.AffineLine.translation ℝ)) =
      fun _ : ℝ ↦ (1 : ℝ) := funext fun _ ↦ by simp; rfl
  rw [LieAlgebra.AffineLine.lie_dilation_translation, tangent_bracket_apply, hd, ht,
    mlieBracket_const_right_model_space] at h0
  -- On `ℝ`, `TangentSpace 𝓘(ℝ, ℝ) 0` is `ℝ` and `Xd` is `fun x ↦ x`.
  change (1 : ℝ) = -fderiv ℝ (fun x : ℝ ↦ x) 0 1 at h0
  rw [fderiv_fun_id] at h0; norm_num at h0

end LieAlgebroid

end TauCeti
