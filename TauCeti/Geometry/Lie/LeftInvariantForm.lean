/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.Algebra.Lie.Cohomology.FiniteDimensional
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Lie.Tangent.Differential
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Left-invariant differential forms on a Lie group

Let `G` be a Lie group with Lie algebra `𝔤 = T₁G` (`GroupLieAlgebra I G`). A continuous
alternating `k`-form `α` on `𝔤` with values in a normed space `F` extends to a differential
`k`-form `α^L` on `G` (`TauCeti.leftInvariantForm`): at `g`, translate the tangent vectors back to
the identity by the differential of `L_{g⁻¹} : x ↦ g⁻¹ * x` and evaluate `α` on them,

`α^L_g (v₁, …, vₖ) = α (dL_{g⁻¹} v₁, …, dL_{g⁻¹} vₖ)`.

On the left-invariant vector fields `X^L` (`mulInvariantVectorField X`) the form is constant,
`α^L (X₁^L, …, Xₖ^L) = α (X₁, …, Xₖ)`, so `α^L` vanishes at no point unless `α = 0`. Every left
translation preserves `α^L`, and conversely a form preserved by every left translation is the
extension of its value at the identity (`TauCeti.forall_mpullback_mul_left_eq_iff`). A smooth
homomorphism `φ : K → G` pulls `α^L` back to `(α ∘ dφ)^L`, where `dφ : 𝔨 → 𝔤` is its
differential at the identity
(`TauCeti.mpullback_leftInvariantForm_of_contMDiffMonoidMorphism`,
`ContMDiffMonoidMorphism.mpullback_leftInvariantSmoothForm`). The extension is smooth
(`TauCeti.isSmoothForm_leftInvariantForm`); on a smooth Lie group it is bundled as a smooth form,
`TauCeti.leftInvariantSmoothForm`.

The exterior derivative of a left-invariant form is left-invariant, and on `𝔤` it is the
Chevalley–Eilenberg differential `d` with trivial coefficients,
`TauCeti.LieModule.Cohomology.trivialD` (`TauCeti.mextDeriv_leftInvariantForm`):

`d (α^L) = (d α)^L`, where
`(d α)(X₀, …, Xₖ) = ∑_{i < j} (-1)^(i + j) α (⁅Xᵢ, Xⱼ⁆, X₀, …, X̂ᵢ, …, X̂ⱼ, …, Xₖ)`.

Indeed, evaluated on left-invariant vector fields the directional terms of the invariant formula
for `d` differentiate constant functions, and the bracket of two left-invariant fields is the
left-invariant field of the bracket in `𝔤`. So `α^L` is closed exactly when `α` is a
Chevalley–Eilenberg cocycle (`TauCeti.isClosed_leftInvariantSmoothForm_iff`). This turns cocycles
of the Lie algebra, such as the Cartan three-form `(X, Y, Z) ↦ B (X, ⁅Y, Z⁆)` of an invariant
bilinear form `B`, into closed differential forms on the group. In degree one, with real
coefficients, the left-invariant form of a covector is also constructed as a pullback of the
Liouville form, `Module.Dual.leftInvariantForm`, which agrees with this extension
(`Module.Dual.leftInvariantForm_eq_leftInvariantSmoothForm`).

The coefficient space `F` is a normed space. The definition of `trivialD` regards it as a
trivial module over `𝔤` through Mathlib's type synonym `TrivialLieModule ℝ 𝔤 F`, so no Lie module
structure on `F` itself is needed. The trivial action is what makes `d` the de Rham differential,
since the exterior derivative has no term in which `𝔤` acts on the values of the form.

## Main definitions

* `TauCeti.leftInvariantForm I G F k`: the left-invariant extension `α ↦ α^L`, a linear map from
  alternating `k`-forms on `𝔤` to differential `k`-forms on `G`.
* `TauCeti.leftInvariantSmoothForm I G F k`: the same, as smooth forms on a smooth Lie group.

## Main results

* `TauCeti.leftInvariantForm_apply_mulInvariantVectorField`: `α^L (X₁^L, …, Xₖ^L) = α (X₁, …, Xₖ)`.
* `TauCeti.leftInvariantForm_apply_eq_zero_iff`: `α^L` vanishes at a point exactly when `α = 0`.
* `TauCeti.mpullback_mul_left_leftInvariantForm`,
  `TauCeti.mpullback_mul_left_leftInvariantSmoothForm`: left translations preserve `α^L`.
* `TauCeti.forall_mpullback_mul_left_eq_iff`: the left-invariant forms are the forms `α^L`.
* `TauCeti.mpullback_leftInvariantForm_of_contMDiffMonoidMorphism`,
  `ContMDiffMonoidMorphism.mpullback_leftInvariantSmoothForm`: `φ^* α^L = (α ∘ dφ)^L` for a smooth
  homomorphism `φ`.
* `TauCeti.isSmoothForm_leftInvariantForm`: on a `C^n` Lie group, `α^L` is `C^m` for `m + 1 ≤ n`.
* `TauCeti.mextDeriv_leftInvariantForm`, `TauCeti.mextDerivₗ_leftInvariantSmoothForm`:
  `d (α^L) = (d α)^L`.
* `TauCeti.mextDeriv_leftInvariantForm_eq_zero_iff`,
  `TauCeti.isClosed_leftInvariantSmoothForm_iff`: `α^L` is closed exactly when `d α = 0`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 14
  (the invariant formula for the exterior derivative) and Chapter 20.
-/

public section

noncomputable section

open Bundle Manifold VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The left-invariant extension -/

variable (I G F k) in
/-- The left-invariant extension `α^L` of a continuous alternating `k`-form `α` on the Lie algebra
`T₁G`: at `g`, it evaluates `α` on the translates of the tangent vectors back to the identity by
the differential of `x ↦ g⁻¹ * x`. -/
def leftInvariantForm :
    (GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) →ₗ[ℝ] RoughForm I G F k where
  toFun α g := α.compContinuousLinearMap (mfderiv I I (g⁻¹ * ·) g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- At `g`, the left-invariant extension of `α` is `α` precomposed with the differential of
`x ↦ g⁻¹ * x` at `g`. -/
theorem leftInvariantForm_def (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (g : G) :
    leftInvariantForm I G F k α g = α.compContinuousLinearMap (mfderiv I I (g⁻¹ * ·) g) :=
  (rfl)

/-- The left-invariant extension of `α` evaluates `α` on the translates to the identity. -/
@[simp]
theorem leftInvariantForm_apply (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (g : G)
    (v : Fin k → TangentSpace I g) :
    leftInvariantForm I G F k α g v = α (fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i)) :=
  (rfl)

/-- At the identity, the left-invariant extension of `α` is `α`. -/
@[simp]
theorem leftInvariantForm_one (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantForm I G F k α 1 = α := by
  have h : (fun x : G ↦ (1 : G)⁻¹ * x) = id := by
    funext x
    simp
  ext v
  rw [leftInvariantForm_apply, h, mfderiv_id]
  -- The identity of `T₁G` now acts on `v`, with target `T_{1⁻¹ * 1}G`; both tangent spaces are
  -- the model space, so `ContinuousLinearMap.id_apply` does not apply syntactically.
  rfl

/-- A form on the Lie algebra is determined by its left-invariant extension. -/
theorem leftInvariantForm_injective : Function.Injective (leftInvariantForm I G F k) :=
  fun α β h ↦ by rw [← leftInvariantForm_one α, h, leftInvariantForm_one]

section Invariance

variable [ContMDiffMul I 1 G]

/-- On left-invariant vector fields, the left-invariant extension of `α` is constant:
`α^L (X₁^L, …, Xₖ^L) = α (X₁, …, Xₖ)`. Its priority is high so that it fires before the general
`leftInvariantForm_apply`, which would leave `mulInvariantVectorField (X i) (g⁻¹ * g)`. -/
@[simp high]
theorem leftInvariantForm_apply_mulInvariantVectorField
    (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (g : G) (X : Fin k → GroupLieAlgebra I G) :
    leftInvariantForm I G F k α g (fun i ↦ mulInvariantVectorField (X i) g) = α X := by
  simp only [leftInvariantForm_apply, mfderiv_inv_mul_mulInvariantVectorField]

/-- The left-invariant extension of `α` vanishes at a point exactly when `α` is zero: its value
at `g` on the left-invariant vector fields is `α` itself. -/
@[simp]
theorem leftInvariantForm_apply_eq_zero_iff {α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F} {g : G} :
    leftInvariantForm I G F k α g = 0 ↔ α = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext X
  rw [← leftInvariantForm_apply_mulInvariantVectorField α g X, h]
  simp

/-- Every left translation preserves the left-invariant extension of `α`. -/
@[simp]
theorem mpullback_mul_left_leftInvariantForm (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F)
    (g : G) :
    mpullback I I (g * ·) (leftInvariantForm I G F k α) = leftInvariantForm I G F k α := by
  funext x
  ext v
  -- Write the tangent vectors at `x` as values of left-invariant vector fields.
  obtain ⟨X, rfl⟩ : ∃ X : Fin k → GroupLieAlgebra I G,
      (fun i ↦ mulInvariantVectorField (X i) x) = v :=
    ⟨fun i ↦ mfderiv I I (x⁻¹ * ·) x (v i),
      funext fun i ↦ mulInvariantVectorField_mfderiv_inv_mul (v i)⟩
  simp only [mpullback_apply, mfderiv_mul_left_mulInvariantVectorField,
    leftInvariantForm_apply_mulInvariantVectorField]

/-- **The left-invariant forms are the left-invariant extensions.** A differential form is
preserved by every left translation exactly when it is the left-invariant extension of its value
at the identity. -/
theorem forall_mpullback_mul_left_eq_iff {φ : RoughForm I G F k} :
    (∀ g : G, mpullback I I (g * ·) φ = φ) ↔ φ = leftInvariantForm I G F k (φ 1) := by
  refine ⟨fun h ↦ ?_, fun h g ↦ by rw [h, mpullback_mul_left_leftInvariantForm]⟩
  -- The values of a form at two equal points agree, all tangent spaces being the model space.
  have hpt {p q : G} (hpq : p = q) (w : Fin k → E) : φ p w = φ q w := by
    subst hpq
    rfl
  funext x
  ext v
  conv_lhs => rw [← h x⁻¹]
  rw [mpullback_apply, leftInvariantForm_apply]
  exact hpt (inv_mul_cancel x) _

end Invariance

/-! ### Smoothness -/

/-- On a `C^n` Lie group, the left-invariant extension of a form on the Lie algebra is a `C^m`
differential form when `m + 1 ≤ n`. -/
theorem isSmoothForm_leftInvariantForm [IsManifold I 1 G] {m n : WithTop ℕ∞} [LieGroup I n G]
    (hmn : m + 1 ≤ n) (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    IsSmoothForm I m (leftInvariantForm I G F k α) := by
  rw [isSmoothForm_def]
  intro x₀
  -- The form is the constant form `α` over the constant base point `x⁻¹ * x = 1`, precomposed
  -- with the derivative of `y ↦ x⁻¹ * y` at `x`, which is `C^m` in tangent coordinates.
  have hd : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) m
      (inTangentCoordinates I I id (fun x : G ↦ x⁻¹ * x) (fun x ↦ mfderiv I I (x⁻¹ * ·) x) x₀)
      x₀ :=
    ContMDiffAt.mfderiv (fun x y : G ↦ x⁻¹ * y) id
      (((contMDiff_inv I n).comp contMDiff_fst).mul contMDiff_snd).contMDiffAt contMDiffAt_id
      hmn
  have hc : ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) m (fun y : G ↦
      ContinuousAlternatingMap.inCoordinates (E₁ := TangentSpace I) (E₂ := Trivial G F) E F
        (x₀⁻¹ * x₀) (y⁻¹ * y) x₀ y α) x₀ := by
    have h : (fun y : G ↦
        ContinuousAlternatingMap.inCoordinates (E₁ := TangentSpace I) (E₂ := Trivial G F) E F
          (x₀⁻¹ * x₀) (y⁻¹ * y) x₀ y α) = fun _ ↦
        ContinuousAlternatingMap.inCoordinates (E₁ := TangentSpace I) (E₂ := Trivial G F) E F
          (1 : G) (1 : G) x₀ x₀ α := by
      funext y
      rw [inv_mul_cancel, inv_mul_cancel]
      ext v
      simp [ContinuousAlternatingMap.inCoordinates,
        Bundle.Trivial.continuousLinearMapAt_trivialization]
    rw [h]
    exact contMDiffAt_const
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E) (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffAt hd).clm_apply hc
  apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨contMDiffAt_id, hp.congr_of_eventuallyEq ?_⟩
  filter_upwards with y
  have hy : y⁻¹ * y ∈ (trivializationAt E (TangentSpace I) (x₀⁻¹ * x₀)).baseSet := by
    rw [inv_mul_cancel, inv_mul_cancel]
    exact FiberBundle.mem_baseSet_trivializationAt' _
  rw [leftInvariantForm_def]
  exact ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap
    (𝕜 := ℝ) (ι := Fin k) (V₂ := TangentSpace I) (F₂ := E) (V₃ := Trivial G F) (F₃ := F)
    (y₀ := x₀⁻¹ * x₀) (y := y⁻¹ * y) (z₀ := x₀) (z := y) α _ hy

section Smooth

variable [IsManifold I 1 G] [LieGroup I ∞ G]

variable (I G F k) in
/-- The left-invariant extension of a form on the Lie algebra of a smooth Lie group, as a smooth
differential form. -/
def leftInvariantSmoothForm :
    (GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) →ₗ[ℝ] SmoothForm I G F k where
  toFun α := ⟨leftInvariantForm I G F k α,
    (isSmoothForm_leftInvariantForm (n := ∞) le_rfl α).mem_smoothBundleForms⟩
  map_add' α β := Subtype.ext (map_add _ α β)
  map_smul' c α := Subtype.ext (map_smul _ c α)

/-- The rough form underlying the smooth left-invariant extension is the left-invariant
extension. -/
@[simp]
theorem leftInvariantSmoothForm_val (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    (leftInvariantSmoothForm I G F k α).val = leftInvariantForm I G F k α :=
  (rfl)

/-- Every left translation preserves the smooth left-invariant extension of `α`. -/
@[simp]
theorem mpullback_mul_left_leftInvariantSmoothForm (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F)
    (g : G) :
    SmoothForm.mpullback (g * ·) contMDiff_mul_left (leftInvariantSmoothForm I G F k α) =
      leftInvariantSmoothForm I G F k α :=
  Subtype.ext <| by
    rw [SmoothForm.coe_mpullback, leftInvariantSmoothForm_val,
      mpullback_mul_left_leftInvariantForm]

end Smooth

/-! ### Pullback along homomorphisms -/

section Homomorphism

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

/-- **Left-invariant forms along a homomorphism.** A smooth homomorphism `φ : G' → G` pulls the
left-invariant extension of a form `α` on the Lie algebra of `G` back to the left-invariant
extension of `α ∘ dφ`, where `dφ` is the differential of `φ` at the identity. -/
@[simp]
theorem mpullback_leftInvariantForm_of_contMDiffMonoidMorphism
    (φ : ContMDiffMonoidMorphism I' I ∞ G' G) (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    mpullback I' I φ (leftInvariantForm I G F k α) =
      leftInvariantForm I' G' F k
        (α.compContinuousLinearMap (φ.toMonoidHom.groupLieAlgebraMap I' I)) := by
  funext g
  ext v
  -- Write the tangent vectors at `g` as values of left-invariant vector fields.
  obtain ⟨X, rfl⟩ : ∃ X : Fin k → GroupLieAlgebra I' G',
      (fun i ↦ mulInvariantVectorField (X i) g) = v :=
    ⟨fun i ↦ mfderiv I' I' (g⁻¹ * ·) g (v i),
      funext fun i ↦ mulInvariantVectorField_mfderiv_inv_mul (v i)⟩
  simp only [mpullback_apply, φ.mfderiv_mulInvariantVectorField,
    leftInvariantForm_apply_mulInvariantVectorField,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]

variable [IsManifold I 1 G] [IsManifold I' 1 G']

/-- A smooth homomorphism `φ : G' → G` pulls the smooth left-invariant extension of a form `α` on
the Lie algebra of `G` back to the smooth left-invariant extension of `α ∘ dφ`, where `dφ` is the
differential of `φ` at the identity. -/
@[simp]
theorem _root_.ContMDiffMonoidMorphism.mpullback_leftInvariantSmoothForm
    (φ : ContMDiffMonoidMorphism I' I ∞ G' G) (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    SmoothForm.mpullback φ φ.contMDiff_toFun (leftInvariantSmoothForm I G F k α) =
      leftInvariantSmoothForm I' G' F k
        (α.compContinuousLinearMap (φ.toMonoidHom.groupLieAlgebraMap I' I)) :=
  Subtype.ext <| by
    rw [SmoothForm.coe_mpullback, leftInvariantSmoothForm_val, leftInvariantSmoothForm_val,
      mpullback_leftInvariantForm_of_contMDiffMonoidMorphism]

end Homomorphism

/-! ### The exterior derivative -/

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E] [LieGroup I 3 G]

/-- **The exterior derivative of a left-invariant form** is the left-invariant extension of the
Chevalley–Eilenberg differential of its value at the identity, with `F` regarded as a trivial
module over the Lie algebra (`TrivialLieModule`): `d (α^L) = (d α)^L`. -/
@[simp]
theorem mextDeriv_leftInvariantForm (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    mextDeriv (leftInvariantForm I G F k α) =
      leftInvariantForm I G F (k + 1)
        (LieModule.Cohomology.trivialD ℝ (GroupLieAlgebra I G) F k α) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : ContMDiffMul I 1 G := ContMDiffMul.of_le (n := 3) (by norm_num)
  funext x
  ext w
  -- Evaluate both sides on left-invariant vector fields `X^L` through the tangent vectors.
  obtain ⟨X, rfl⟩ : ∃ X : Fin (k + 1) → GroupLieAlgebra I G,
      (fun i ↦ mulInvariantVectorField (X i) x) = w :=
    ⟨fun i ↦ mfderiv I I (x⁻¹ * ·) x (w i),
      funext fun i ↦ mulInvariantVectorField_mfderiv_inv_mul (w i)⟩
  have hφ := ((isSmoothForm_def _ _).1
    (isSmoothForm_leftInvariantForm (I := I) (G := G) (m := 1) (n := 3) (by norm_num) α)
    x).mdifferentiableAt one_ne_zero
  have hV (i : Fin (k + 1)) := mdifferentiableAt_mulInvariantVectorField (I := I) (X i) (g := x)
  -- The directional terms of the invariant formula differentiate constant functions.
  have hconst (i : Fin (k + 1)) : (fun y ↦ leftInvariantForm I G F k α y
      (i.removeNth fun j ↦ mulInvariantVectorField (X j) y)) = fun _ ↦ α (i.removeNth X) :=
    funext fun y ↦ leftInvariantForm_apply_mulInvariantVectorField α y (i.removeNth X)
  rw [leftInvariantForm_apply_mulInvariantVectorField]
  cases k with
  | zero =>
    rw [mextDeriv_apply_vectorField_of_mlieBracket_eq_zero hφ hV fun i j ↦ by
      rw [Subsingleton.elim (α := Fin 1) i j, mlieBracket_self, Pi.zero_apply],
      LieModule.Cohomology.trivialD_zero]
    simp only [hconst, mvfderiv_const, zero_apply, smul_zero, Finset.sum_const_zero,
      LinearMap.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  | succ n =>
    -- The bracket terms are values of `α` on brackets in the Lie algebra.
    have hvec (i j : Fin (n + 1)) :
        Matrix.vecCons (mlieBracket I (mulInvariantVectorField (X i.castSucc))
          (mulInvariantVectorField (X j.succ)) x)
          (j.removeNth (i.castSucc.removeNth fun k ↦ mulInvariantVectorField (X k) x)) =
        fun k ↦ mulInvariantVectorField
          (Matrix.vecCons ⁅X i.castSucc, X j.succ⁆ (j.removeNth (i.castSucc.removeNth X)) k) x := by
      rw [← mulInvariantVector_mlieBracket, ← GroupLieAlgebra.bracket_def]
      ext k
      exact Fin.cases rfl (fun k ↦ rfl) k
    rw [mextDeriv_apply_vectorField hφ hV, LieModule.Cohomology.trivialD_succ_apply]
    simp only [hconst, mvfderiv_const, zero_apply, smul_zero, Finset.sum_const_zero, zero_sub,
      hvec, leftInvariantForm_apply_mulInvariantVectorField]
    simp [pow_succ, ← Finset.sum_neg_distrib]

/-- **A left-invariant form is closed exactly when its value at the identity is a
Chevalley–Eilenberg cocycle**, with `F` regarded as a trivial module over the Lie algebra. -/
theorem mextDeriv_leftInvariantForm_eq_zero_iff (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    mextDeriv (leftInvariantForm I G F k α) = 0 ↔
      LieModule.Cohomology.trivialD ℝ (GroupLieAlgebra I G) F k α = 0 := by
  rw [mextDeriv_leftInvariantForm, ← map_zero (leftInvariantForm I G F (k + 1)),
    leftInvariantForm_injective.eq_iff]

/-- **The exterior derivative of a smooth left-invariant form** is the smooth left-invariant
extension of the Chevalley–Eilenberg differential of its value at the identity, with `F` regarded
as a trivial module over the Lie algebra. -/
@[simp]
theorem mextDerivₗ_leftInvariantSmoothForm [IsManifold I 1 G] [LieGroup I ∞ G]
    (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    mextDerivₗ I k (leftInvariantSmoothForm I G F k α) =
      leftInvariantSmoothForm I G F (k + 1)
        (LieModule.Cohomology.trivialD ℝ (GroupLieAlgebra I G) F k α) :=
  Subtype.ext <| by
    rw [mextDerivₗ_apply, leftInvariantSmoothForm_val, leftInvariantSmoothForm_val,
      mextDeriv_leftInvariantForm]

/-- **The smooth left-invariant extension of a form is closed exactly when the form is a
Chevalley–Eilenberg cocycle**, with `F` regarded as a trivial module over the Lie algebra. -/
theorem isClosed_leftInvariantSmoothForm_iff [IsManifold I 1 G] [LieGroup I ∞ G]
    (α : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    (leftInvariantSmoothForm I G F k α).IsClosed ↔
      LieModule.Cohomology.trivialD ℝ (GroupLieAlgebra I G) F k α = 0 := by
  rw [SmoothForm.isClosed_def, leftInvariantSmoothForm_val,
    mextDeriv_leftInvariantForm_eq_zero_iff]

end TauCeti
