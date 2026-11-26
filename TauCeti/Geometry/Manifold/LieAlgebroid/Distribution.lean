/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
import TauCeti.Geometry.Manifold.Distribution.Levi
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Lie algebroids of involutive distributions

An involutive smooth rank-`k` distribution `D ⊆ TM` carries a Lie algebroid structure
`TauCeti.LieAlgebroid.ofDistribution` with inclusion anchor
`TauCeti.IsContMDiffDistribution.inclusionHom` and injective section Lie algebra homomorphism
`ofDistributionSectionsInclusion`. Over a Hausdorff base, a Lie algebroid on `D` with inclusion
anchor is unique (`eq_of_anchor_eq_subtypeL`) and exists iff `D` is involutive
(`exists_lieAlgebroid_anchor_eq_subtypeL_iff`; Mackenzie 2005, §3.3), ruling out
`standardContactDistribution` (`not_exists_lieAlgebroid_standardContactDistribution`).

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
-/

public section
noncomputable section

open Bundle Filter Manifold Set VectorField
open scoped ContDiff Topology

namespace TauCeti.LieAlgebroid
section Distribution
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  (hD : IsContMDiffDistribution I ∞ k D)

section Involutive
variable (hinv : IsInvolutiveDistribution I D)

private def ofDistributionBracketAux : letI := hD.fiberBundle; letI := hD.vectorBundle
    Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ → Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ →
      Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ :=
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle
  fun a b ↦ hD.mkSection ((tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b))
    fun x ↦ by
      rw [tangent_bracket_apply]; exact hinv.mlieBracket_mem isOpen_univ
        ((hD.toTangentSection a).contMDiff.mdifferentiable (by simp)).mdifferentiableOn
        ((hD.toTangentSection b).contMDiff.mdifferentiable (by simp)).mdifferentiableOn
        (fun y _ ↦ by simp [(a y).property]) (fun y _ ↦ by simp [(b y).property]) (mem_univ x)

/-- A smooth involutive rank-`k` distribution `D ⊆ TM` is a Lie algebroid with subbundle inclusion
anchor `x ↦ (D x).subtypeL` and restriction of the Lie bracket of vector fields. -/
def ofDistribution : letI := hD.fiberBundle; letI := hD.vectorBundle
    LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x) :=
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle
  have h (a b) : hD.toTangentSection (ofDistributionBracketAux hD hinv a b) =
      (tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b) :=
    hD.toTangentSection_mkSection _ _
  ⟨hD.inclusionHom, LinearMap.mk₂ ℝ (ofDistributionBracketAux hD hinv)
      (fun _ _ _ ↦ hD.toTangentSection_injective <| by simp [h])
      (fun _ _ _ ↦ hD.toTangentSection_injective <| by
        simp [LinearMapClass.map_smul_of_tower hD.toTangentSection, h])
      (fun _ _ _ ↦ hD.toTangentSection_injective <| by simp [h])
      (fun _ _ _ ↦ hD.toTangentSection_injective <| by
        simp [LinearMapClass.map_smul_of_tower hD.toTangentSection, h]),
    fun _ ↦ hD.toTangentSection_injective <| by simp [h, LieAlgebroid.bracket_self],
    fun _ _ _ ↦ hD.toTangentSection_injective <| by
      simp only [LinearMap.mk₂_apply, map_add, h]; exact (tangent I M).bracket_bracket _ _ _,
    fun a b f x ↦ Subtype.ext <| by
      have hx := congr($(h a (f • b)) x)
      rw [hD.toTangentSection.map_smul, (tangent I M).bracket_smul_apply, ← h a b] at hx
      simpa using hx⟩

theorem ofDistribution_anchor :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; (ofDistribution hD hinv).anchor) =
      (letI := hD.fiberBundle; letI := hD.vectorBundle
      haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp); hD.inclusionHom) := (rfl)

@[simp] theorem ofDistribution_anchor_apply (x : M) (v : D x) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; (ofDistribution hD hinv).anchor x v) =
      (v : TangentSpace I x) := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; simp [ofDistribution]

@[simp] theorem ofDistribution_anchorField :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; (ofDistribution hD hinv).anchorField) =
      (letI := hD.fiberBundle; letI := hD.vectorBundle
      haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp); hD.toTangentSection) := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; ext a x; simp

@[simp] theorem toTangentSection_ofDistribution_bracket :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    ∀ a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯,
      hD.toTangentSection ((ofDistribution hD hinv).bracket a b) =
        (tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b) :=
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; fun _ _ ↦ hD.toTangentSection_mkSection _ _

@[simp] theorem coe_ofDistribution_bracket_apply : letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ (a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯) (x : M),
      (((ofDistribution hD hinv).bracket a b x : D x) : TangentSpace I x) =
        mlieBracket I (fun y ↦ (a y : TangentSpace I y)) (fun y ↦ (b y : TangentSpace I y)) x := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; intro a b x
  have h := congr($(toTangentSection_ofDistribution_bracket hD hinv a b) x)
  rwa [hD.toTangentSection_apply, tangent_bracket_apply, funext (hD.toTangentSection_apply a),
    funext (hD.toTangentSection_apply b)] at h

/-- Inclusion of sections of an involutive distribution Lie algebroid into `(tangent I M).Sections`
as a Lie algebra homomorphism. -/
def ofDistributionSectionsInclusion : letI := hD.fiberBundle; letI := hD.vectorBundle
    (ofDistribution hD hinv).Sections →ₗ⁅ℝ⁆ (tangent I M).Sections :=
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle
  (ofDistribution hD hinv).anchorLieHomOfBracket fun _ _ ↦ by simp

@[simp] theorem sectionsEquiv_ofDistributionSectionsInclusion :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    ∀ s : (ofDistribution hD hinv).Sections,
      (tangent I M).sectionsEquiv (ofDistributionSectionsInclusion hD hinv s) =
        hD.toTangentSection ((ofDistribution hD hinv).sectionsEquiv s) := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; intro s; simp [ofDistributionSectionsInclusion]

theorem ofDistributionSectionsInclusion_injective :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    Function.Injective (ofDistributionSectionsInclusion hD hinv) := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; intro _ _ hst
  exact (ofDistribution hD hinv).sectionsEquiv.injective <|
    hD.toTangentSection_injective (by simpa using congrArg (tangent I M).sectionsEquiv hst)

@[simp] theorem ofDistributionSectionsInclusion_smul :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ (f : C^∞⟮I, M; ℝ⟯) (s : (ofDistribution hD hinv).Sections),
      ofDistributionSectionsInclusion hD hinv (f • s) =
        f • ofDistributionSectionsInclusion hD hinv s :=
  let := hD.fiberBundle; let := hD.vectorBundle
  (ofDistribution hD hinv).anchorLieHomOfBracket_smul _

@[simp] theorem ofDistributionSectionsInclusion_lie [T2Space M] :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp); letI := hD.contMDiffVectorBundle
    ∀ (s : (ofDistribution hD hinv).Sections) (f : C^∞⟮I, M; ℝ⟯),
      ⁅ofDistributionSectionsInclusion hD hinv s, f⁆ = ⁅s, f⁆ :=
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; let := hD.contMDiffVectorBundle
  (ofDistribution hD hinv).anchorLieHomOfBracket_lie _

end Involutive

variable [T2Space M]

/-- Over a Hausdorff base, any Lie algebroid on `D` with inclusion anchor has bracket agreeing
with `mlieBracket` on the underlying tangent vector fields. -/
theorem coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ {A : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x)} (_hA : ∀ x, A.anchor x = (D x).subtypeL)
      (a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯) (x : M),
      ((A.bracket a b x : D x) : TangentSpace I x) =
        mlieBracket I (fun y ↦ (a y : TangentSpace I y)) (fun y ↦ (b y : TangentSpace I y)) x := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; let := hD.contMDiffVectorBundle; intro A hA a b x
  have hc (s : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯) :
      ⇑(A.anchorField s) = fun y ↦ (s y : TangentSpace I y) := funext fun y ↦ by simp [hA y]
  simpa [hA x, hc] using A.anchor_bracket a b x

/-- Over a Hausdorff base, at most one Lie algebroid structure on `D` has inclusion anchor. -/
theorem eq_of_anchor_eq_subtypeL : letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ {A₁ A₂ : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x)},
      (∀ x, A₁.anchor x = (D x).subtypeL) → (∀ x, A₂.anchor x = (D x).subtypeL) → A₁ = A₂ := by
  let := hD.fiberBundle; let := hD.vectorBundle; intro A₁ A₂ hA₁ hA₂
  refine LieAlgebroid.ext (ContMDiffSection.ext fun x ↦ (hA₁ x).trans (hA₂ x).symm)
    (LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ContMDiffSection.ext fun x ↦ Subtype.ext ?_)
  exact (coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL hD hA₁ a b x).trans
    (coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL hD hA₂ a b x).symm

/-- Over a Hausdorff base, the existence of a Lie algebroid structure on `D` with inclusion anchor
forces `D` to be involutive. -/
theorem isInvolutiveDistribution_of_anchor_eq_subtypeL :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    ∀ {A : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x)},
      (∀ x, A.anchor x = (D x).subtypeL) → IsInvolutiveDistribution I D := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.fiberBundle; let := hD.vectorBundle; let := hD.contMDiffVectorBundle; intro A hA
  refine (isInvolutiveDistribution_iff_distributionLeviForm_eq_zero hD (by simp)).2 fun x ↦ ?_
  ext u v
  have hex (w : D x) :=
    ContMDiffSection.evalLinearMap_surjective (I := I) (F := Fin k → ℝ) (V := fun y ↦ D y) ∞ x w
  obtain ⟨sa, hax⟩ := hex u; obtain ⟨sb, hbx⟩ := hex v
  have hmem (s : Cₛ^∞⟮I; Fin k → ℝ, fun y ↦ D y⟯) : ∀ᶠ y in 𝓝 x, hD.toTangentSection s y ∈ D y :=
    Eventually.of_forall fun y ↦ by rw [hD.toTangentSection_apply]; exact (s y).property
  have hsub (s : Cₛ^∞⟮I; Fin k → ℝ, fun y ↦ D y⟯) :
      (⟨hD.toTangentSection s x, (hmem s).self_of_nhds⟩ : D x) = s x :=
    Subtype.ext (hD.toTangentSection_apply s x)
  rw [← hax, ← hbx, ContMDiffSection.evalLinearMap_apply, ContMDiffSection.evalLinearMap_apply,
    ← hsub sa, ← hsub sb, LinearMap.zero_apply, LinearMap.zero_apply]
  refine (distributionLeviForm_apply_eq_zero_iff hD (by simp)
    ((hD.toTangentSection sa).contMDiff.mdifferentiableAt (by simp))
    ((hD.toTangentSection sb).contMDiff.mdifferentiableAt (by simp)) (hmem sa) (hmem sb)).2 ?_
  rw [funext (hD.toTangentSection_apply sa), funext (hD.toTangentSection_apply sb),
    ← coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL hD hA sa sb x]
  exact (A.bracket sa sb x).property

/-- Over a Hausdorff base, a smooth constant-rank distribution `D` carries a Lie algebroid
structure with inclusion anchor if and only if `D` is involutive. -/
theorem exists_lieAlgebroid_anchor_eq_subtypeL_iff :
    (letI := hD.fiberBundle; letI := hD.vectorBundle;
      ∃ A : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x), ∀ x, A.anchor x = (D x).subtypeL) ↔
      IsInvolutiveDistribution I D :=
  ⟨fun ⟨_, hA⟩ ↦ isInvolutiveDistribution_of_anchor_eq_subtypeL hD hA, fun hinv ↦
    ⟨ofDistribution hD hinv, fun x ↦ by
      have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
      let := hD.fiberBundle; let := hD.vectorBundle; simp [ofDistribution]⟩⟩

end Distribution

/-- The standard contact distribution on `ℝ³` admits no Lie algebroid with inclusion anchor. -/
theorem not_exists_lieAlgebroid_standardContactDistribution :
    let D₀ : Π p : ℝ × ℝ × ℝ, Submodule ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
      standardContactDistribution ℝ
    let hD := isContMDiffDistribution_standardContactDistribution (𝕜 := ℝ) ∞
    letI := hD.fiberBundle; letI := hD.vectorBundle
    ¬∃ A : LieAlgebroid 𝓘(ℝ, ℝ × ℝ × ℝ) (Fin 2 → ℝ) (fun p ↦ D₀ p),
      ∀ p, A.anchor p = (D₀ p).subtypeL :=
  fun h ↦ not_isInvolutiveDistribution_standardContactDistribution
    ((exists_lieAlgebroid_anchor_eq_subtypeL_iff
      (isContMDiffDistribution_standardContactDistribution (𝕜 := ℝ) ∞)).1 h)

end TauCeti.LieAlgebroid
