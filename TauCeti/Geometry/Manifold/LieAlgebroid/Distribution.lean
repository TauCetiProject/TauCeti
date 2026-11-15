/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Lie algebroids of involutive distributions

A smooth distribution `D` of rank `k` on a finite-dimensional real manifold `M` is a smooth
subbundle of the tangent bundle (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`), so its
fibrewise subspace inclusions `(D x).subtypeL : D x →L[ℝ] TangentSpace I x` assemble into a smooth
bundle morphism (`TauCeti.IsContMDiffDistribution.inclusionAnchor`).

When `D` is involutive (`TauCeti.IsInvolutiveDistribution I D`), the manifold Lie bracket of smooth
tangent vector fields restricts to smooth sections of `D` and equips `D` with a Lie algebroid
structure (`TauCeti.LieAlgebroid.ofDistribution`) whose anchor is the subbundle inclusion. Section
inclusion into `Γ(TM)` is then an injective Lie algebra homomorphism
(`TauCeti.LieAlgebroid.ofDistributionSectionsInclusion`).

Conversely, over a Hausdorff base, if `D` admits any Lie algebroid structure whose anchor is the
subbundle inclusion, then `D` is involutive
(`TauCeti.LieAlgebroid.isInvolutiveDistribution_of_anchor_eq_subtypeL`), and that Lie algebroid
structure is unique (`TauCeti.LieAlgebroid.eq_of_anchor_eq_subtypeL`). Thus a smooth constant-rank
distribution carries a Lie algebroid structure with inclusion anchor if and only if it is involutive
(`TauCeti.LieAlgebroid.exists_lieAlgebroid_anchor_eq_subtypeL_iff`). In particular, the standard
contact distribution on `ℝ³` admits no such Lie algebroid structure
(`TauCeti.LieAlgebroid.not_exists_lieAlgebroid_standardContactDistribution`).

## Main definitions

* `TauCeti.IsContMDiffDistribution.inclusionAnchor`: the smooth Hom-bundle section
  `x ↦ (D x).subtypeL` of a smooth constant-rank distribution `D`.
* `TauCeti.IsContMDiffDistribution.toTangentSection`: the `C^∞⟮I, M; ℝ⟯`-linear inclusion of smooth
  sections of `D` into smooth tangent vector fields.
* `TauCeti.IsContMDiffDistribution.mkSection`: packaging a smooth tangent vector field tangent to
  `D` everywhere as a smooth section of `D`.
* `TauCeti.LieAlgebroid.ofDistribution`: the Lie algebroid structure on a smooth involutive
  constant-rank distribution.
* `TauCeti.LieAlgebroid.ofDistributionSectionsInclusion`: the injective Lie algebra homomorphism
  `Γ(D) →ₗ⁅ℝ⁆ Γ(TM)`.

## Main results

* `TauCeti.LieAlgebroid.eq_of_anchor_eq_subtypeL`: the Lie algebroid structure on `D` with
  inclusion anchor is unique over a Hausdorff base.
* `TauCeti.LieAlgebroid.isInvolutiveDistribution_of_anchor_eq_subtypeL`: any Lie algebroid on `D`
  with inclusion anchor forces `D` to be involutive.
* `TauCeti.LieAlgebroid.exists_lieAlgebroid_anchor_eq_subtypeL_iff`: existence of a Lie algebroid
  structure on `D` with inclusion anchor is equivalent to involutivity of `D`.
* `TauCeti.LieAlgebroid.not_exists_lieAlgebroid_standardContactDistribution`: the standard contact
  distribution on `ℝ³` carries no Lie algebroid structure with inclusion anchor.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
-/

public section

noncomputable section

open Bundle Filter Manifold Set VectorField
open scoped ContDiff Topology

namespace TauCeti

namespace IsContMDiffDistribution

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- The fibrewise continuous linear inclusions `(D x).subtypeL : D x →L[ℝ] TangentSpace I x` of a
smooth rank-`k` distribution form a smooth section of the Hom bundle `D →L[ℝ] TM`. -/
def inclusionAnchor (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    Cₛ^∞⟮I; (Fin k → ℝ) →L[ℝ] E, fun x ↦ D x →L[ℝ] TangentSpace I x⟯ :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  { toFun x := (D x).subtypeL
    contMDiff_toFun :=
      (contMDiff_hom_bundle_iff _).2 hD.contMDiff_totalSpace_inclusion }

@[simp]
theorem inclusionAnchor_apply (hD : IsContMDiffDistribution I ∞ k D) (x : M) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; hD.inclusionAnchor x) = (D x).subtypeL :=
  (rfl)

/-- Inclusion of smooth sections of a smooth rank-`k` distribution `D` into smooth tangent vector
fields, linear over `C^∞⟮I, M; ℝ⟯`. -/
def toTangentSection (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  { toFun a :=
      { toFun x := (a x : TangentSpace I x)
        contMDiff_toFun := hD.inclusionAnchor.contMDiff.clm_bundle_apply a.contMDiff }
    map_add' _ _ := ContMDiffSection.ext fun _ ↦ rfl
    map_smul' _ _ := ContMDiffSection.ext fun _ ↦ by simp; rfl }

@[simp]
theorem toTangentSection_apply (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ (a : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯) (x : M),
      hD.toTangentSection a x = (a x : TangentSpace I x) :=
  fun _ _ ↦ rfl

theorem toTangentSection_injective (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    Function.Injective hD.toTangentSection := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro a b hab
  ext x
  simpa using congr($hab x)

/-- A smooth tangent vector field taking values in `D` at every point defines a smooth section of
`D`. -/
def mkSection (hD : IsContMDiffDistribution I ∞ k D)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (hX : ∀ x, X x ∈ D x) :
    letI := hD.fiberBundle
    Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  { toFun x := ⟨X x, hX x⟩
    contMDiff_toFun x := hD.contMDiffAt_totalSpace_mk X.contMDiff.contMDiffAt hX }

@[simp]
theorem coe_mkSection_apply (hD : IsContMDiffDistribution I ∞ k D)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (hX : ∀ x, X x ∈ D x) (x : M) :
    (letI := hD.fiberBundle; (hD.mkSection X hX x : TangentSpace I x)) = X x :=
  (rfl)

@[simp]
theorem toTangentSection_mkSection (hD : IsContMDiffDistribution I ∞ k D)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (hX : ∀ x, X x ∈ D x) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; hD.toTangentSection (hD.mkSection X hX)) =
      X := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  ext x
  simp

end IsContMDiffDistribution

namespace LieAlgebroid

section Distribution

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- Pointwise restriction of the tangent Lie bracket to smooth sections of a smooth involutive
rank-`k` distribution `D`. -/
private def ofDistributionBracketAux (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ →
      Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ →
      Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  fun a b ↦
    hD.mkSection ((tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b)) fun x ↦ by
      rw [tangent_bracket_apply]
      exact hinv.mlieBracket_mem isOpen_univ
        ((hD.toTangentSection a).contMDiff.mdifferentiable (by simp)).mdifferentiableOn
        ((hD.toTangentSection b).contMDiff.mdifferentiable (by simp)).mdifferentiableOn
        (fun y _ ↦ by simp [(a y).2]) (fun y _ ↦ by simp [(b y).2]) (mem_univ x)

private theorem toTangentSection_ofDistributionBracketAux (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯,
      hD.toTangentSection (ofDistributionBracketAux hD hinv a b) =
        (tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro a b
  exact hD.toTangentSection_mkSection _ _

/-- Bundled `ℝ`-bilinear section bracket on a smooth involutive rank-`k` distribution `D`. -/
private def ofDistributionBracket (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯ :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  LinearMap.mk₂ ℝ (ofDistributionBracketAux hD hinv)
    (fun a a' b ↦ hD.toTangentSection_injective <| by
      simp only [map_add, toTangentSection_ofDistributionBracketAux, LinearMap.add_apply])
    (fun c a b ↦ hD.toTangentSection_injective <| by
      simp only [LinearMapClass.map_smul_of_tower hD.toTangentSection,
        toTangentSection_ofDistributionBracketAux, map_smul, LinearMap.smul_apply])
    (fun a b b' ↦ hD.toTangentSection_injective <| by
      simp only [map_add, toTangentSection_ofDistributionBracketAux])
    (fun c a b ↦ hD.toTangentSection_injective <| by
      simp only [LinearMapClass.map_smul_of_tower hD.toTangentSection,
        toTangentSection_ofDistributionBracketAux, map_smul])

private theorem toTangentSection_ofDistributionBracket' (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯,
      hD.toTangentSection (ofDistributionBracket hD hinv a b) =
        (tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b) :=
  toTangentSection_ofDistributionBracketAux hD hinv

/-- A smooth involutive rank-`k` distribution `D ⊆ TM` is a Lie algebroid with the subbundle
inclusion anchor `x ↦ (D x).subtypeL` and the restriction of the Lie bracket of vector fields. -/
def ofDistribution (hD : IsContMDiffDistribution I ∞ k D) (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x) :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  { anchor := hD.inclusionAnchor
    bracket := ofDistributionBracket hD hinv
    bracket_self a := hD.toTangentSection_injective <| by
      rw [toTangentSection_ofDistributionBracket', (tangent I M).bracket_self, map_zero]
    bracket_bracket a b c := hD.toTangentSection_injective <| by
      rw [map_add, toTangentSection_ofDistributionBracket', toTangentSection_ofDistributionBracket',
        toTangentSection_ofDistributionBracket', toTangentSection_ofDistributionBracket',
        toTangentSection_ofDistributionBracket', toTangentSection_ofDistributionBracket',
        (tangent I M).bracket_bracket]
    bracket_smul_apply a b f x := Subtype.ext <| by
      have h := congr($(toTangentSection_ofDistributionBracket' hD hinv a (f • b)) x)
      rw [hD.toTangentSection.map_smul, (tangent I M).bracket_smul_apply,
        ← toTangentSection_ofDistributionBracket' hD hinv a b] at h
      simpa using h }

@[simp]
theorem ofDistribution_anchor (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; (ofDistribution hD hinv).anchor) =
      (letI := hD.fiberBundle; letI := hD.vectorBundle; hD.inclusionAnchor) :=
  (rfl)

theorem ofDistribution_anchor_apply (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) (x : M) (v : D x) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle;
      (ofDistribution hD hinv).anchor x v) = (v : TangentSpace I x) :=
  (rfl)

@[simp]
theorem ofDistribution_anchorField (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle; (ofDistribution hD hinv).anchorField) =
      (letI := hD.fiberBundle; letI := hD.vectorBundle; hD.toTangentSection) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  ext a x
  simp

@[simp]
theorem toTangentSection_ofDistribution_bracket (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯,
      hD.toTangentSection ((ofDistribution hD hinv).bracket a b) =
        (tangent I M).bracket (hD.toTangentSection a) (hD.toTangentSection b) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro a b
  exact hD.toTangentSection_mkSection _ _

theorem coe_ofDistribution_bracket_apply (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ (a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯) (x : M),
      (((ofDistribution hD hinv).bracket a b x : D x) : TangentSpace I x) =
        mlieBracket I (fun y ↦ (a y : TangentSpace I y)) (fun y ↦ (b y : TangentSpace I y)) x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro a b x
  have h := congr($(toTangentSection_ofDistribution_bracket hD hinv a b) x)
  have ha : ⇑(hD.toTangentSection a) = fun y ↦ (a y : TangentSpace I y) :=
    funext (hD.toTangentSection_apply a)
  have hb : ⇑(hD.toTangentSection b) = fun y ↦ (b y : TangentSpace I y) :=
    funext (hD.toTangentSection_apply b)
  rw [hD.toTangentSection_apply, tangent_bracket_apply, ha, hb] at h
  exact h

/-- Inclusion of sections of an involutive distribution Lie algebroid into sections of the tangent
Lie algebroid, as a Lie algebra homomorphism. -/
def ofDistributionSectionsInclusion (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    (ofDistribution hD hinv).Sections →ₗ⁅ℝ⁆ (tangent I M).Sections :=
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  { toFun s := (tangent I M).sectionsEquiv.symm
      (hD.toTangentSection ((ofDistribution hD hinv).sectionsEquiv s))
    map_add' s t := by simp only [map_add]
    map_smul' c s := by
      rw [LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower,
        LinearMapClass.map_smul_of_tower]
      rfl
    map_lie' := by
      intro s t
      exact (tangent I M).sectionsEquiv.injective <| by simp }

@[simp]
theorem sectionsEquiv_ofDistributionSectionsInclusion (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ s : (ofDistribution hD hinv).Sections,
      (tangent I M).sectionsEquiv (ofDistributionSectionsInclusion hD hinv s) =
        hD.toTangentSection ((ofDistribution hD hinv).sectionsEquiv s) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro s
  exact (tangent I M).sectionsEquiv.apply_symm_apply _

theorem ofDistributionSectionsInclusion_injective (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    Function.Injective (ofDistributionSectionsInclusion hD hinv) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro s t hst
  apply (ofDistribution hD hinv).sectionsEquiv.injective
  apply hD.toTangentSection_injective
  simpa using congrArg (tangent I M).sectionsEquiv hst

@[simp]
theorem ofDistributionSectionsInclusion_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hinv : IsInvolutiveDistribution I D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ (f : C^∞⟮I, M; ℝ⟯) (s : (ofDistribution hD hinv).Sections),
      ofDistributionSectionsInclusion hD hinv (f • s) =
        f • ofDistributionSectionsInclusion hD hinv s := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro f s
  apply (tangent I M).sectionsEquiv.injective
  simp

section Converse

variable [T2Space M]

/-- Over a Hausdorff base, any Lie algebroid on `D` whose anchor is the subbundle inclusion must
have section bracket equal to the restriction of the manifold Lie bracket of vector fields. -/
theorem coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL
    (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ {A : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x)}
      (_hA : ∀ x, A.anchor x = (D x).subtypeL)
      (a b : Cₛ^∞⟮I; Fin k → ℝ, fun x ↦ D x⟯) (x : M),
      ((A.bracket a b x : D x) : TangentSpace I x) =
        mlieBracket I (fun y ↦ (a y : TangentSpace I y)) (fun y ↦ (b y : TangentSpace I y)) x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  let := hD.contMDiffVectorBundle
  intro A hA a b x
  have hbr := A.anchor_bracket a b x
  have ha : ⇑(A.anchorField a) = fun y ↦ (a y : TangentSpace I y) := by
    funext y
    simp [hA y]
  have hb : ⇑(A.anchorField b) = fun y ↦ (b y : TangentSpace I y) := by
    funext y
    simp [hA y]
  simpa [hA x, ha, hb] using hbr

/-- Over a Hausdorff base, at most one Lie algebroid structure on a smooth constant-rank
distribution `D` has the subbundle inclusion as its anchor. -/
theorem eq_of_anchor_eq_subtypeL (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ {A₁ A₂ : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x)},
      (∀ x, A₁.anchor x = (D x).subtypeL) → (∀ x, A₂.anchor x = (D x).subtypeL) → A₁ = A₂ := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro A₁ A₂ hA₁ hA₂
  refine LieAlgebroid.ext (ContMDiffSection.ext fun x ↦ (hA₁ x).trans (hA₂ x).symm)
    (LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ContMDiffSection.ext fun x ↦ Subtype.ext ?_)
  exact (coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL hD hA₁ a b x).trans
    (coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL hD hA₂ a b x).symm

/-- Over a Hausdorff base, if a smooth constant-rank distribution `D` admits a Lie algebroid
structure whose anchor is the subbundle inclusion, then `D` is involutive. -/
theorem isInvolutiveDistribution_of_anchor_eq_subtypeL (hD : IsContMDiffDistribution I ∞ k D) :
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ∀ {A : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x)},
      (∀ x, A.anchor x = (D x).subtypeL) → IsInvolutiveDistribution I D := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let := hD.fiberBundle
  let := hD.vectorBundle
  intro A hA
  refine isInvolutiveDistribution_iff.mpr fun U₀ hU₀ V W hV hW hVD hWD x hx₀ ↦ ?_
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  obtain ⟨ρ, -, hρ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hU.mem_nhds hxU)
  -- Cut off each local frame field `X i` by `ρ` to obtain global smooth sections of `D` agreeing
  -- with `X i` near `x`; `A.anchor_bracket` then places `[X i, X j] x` in `D x`.
  have hρX_mem (i : Fin k) (y : M) : ((ρ : M → ℝ) • X i) y ∈ D y := by
    by_cases hy : y ∈ U
    · exact (D y).smul_mem (ρ y) (hX.isSubbundleFrameOn.apply_mem i hy)
    · simp [image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hρ h))]
  let sX (i : Fin k) : Cₛ^∞⟮I; Fin k → ℝ, fun y ↦ D y⟯ :=
    hD.mkSection
      ⟨(ρ : M → ℝ) • X i,
        (ρ.contMDiff.contMDiffOn (s := U)).smul_section_of_tsupport hU hρ (hX.contMDiffOn i)⟩
      (hρX_mem i)
  have hsX_eq (i : Fin k) : (fun y ↦ (sX i y : TangentSpace I y)) =ᶠ[𝓝 x] X i := by
    filter_upwards [ρ.eventuallyEq_one] with y hy
    simp only [sX, IsContMDiffDistribution.coe_mkSection_apply, ContMDiffSection.coeFn_mk]
    have hy1 : ρ y = 1 := hy
    -- Pointwise scalar multiplication of the dependent vector field `X i` by `ρ`.
    change ρ y • X i y = X i y
    rw [hy1, one_smul]
  have hXX (i : Fin k) (_ : i ∈ Finset.univ) (j : Fin k) (_ : j ∈ Finset.univ) :
      mlieBracket I (X i) (X j) x ∈ D x := by
    have heq := (hsX_eq i).symm.mlieBracket_vectorField_eq (hsX_eq j).symm
    rw [heq, ← coe_bracket_eq_mlieBracket_of_anchor_eq_subtypeL hD hA (sX i) (sX j) x]
    exact (A.bracket (sX i) (sX j) x).2
  -- Expand `V` and `W` near `x` in the local frame `X` with differentiable coefficients.
  have hVx : MDiffAt (T% V) x := (hV x hx₀).mdifferentiableAt (hU₀.mem_nhds hx₀)
  have hWx : MDiffAt (T% W) x := (hW x hx₀).mdifferentiableAt (hU₀.mem_nhds hx₀)
  obtain ⟨f, hf, hVf⟩ := hX.exists_mdifferentiableAt_coeff (by simp) (hU.mem_nhds hxU) hVx
    (eventually_of_mem (hU₀.mem_nhds hx₀) hVD)
  obtain ⟨g, hg, hWg⟩ := hX.exists_mdifferentiableAt_coeff (by simp) (hU.mem_nhds hxU) hWx
    (eventually_of_mem (hU₀.mem_nhds hx₀) hWD)
  have hVf' : V =ᶠ[𝓝 x] ∑ i ∈ Finset.univ, f i • X i := by
    filter_upwards [hVf] with y hy
    exact hy.trans
      (map_sum (Pi.evalAddMonoidHom (fun z ↦ TangentSpace I z) y) (fun i ↦ f i • X i)
        Finset.univ).symm
  have hWg' : W =ᶠ[𝓝 x] ∑ j ∈ Finset.univ, g j • X j := by
    filter_upwards [hWg] with y hy
    exact hy.trans
      (map_sum (Pi.evalAddMonoidHom (fun z ↦ TangentSpace I z) y) (fun j ↦ g j • X j)
        Finset.univ).symm
  rw [hVf'.mlieBracket_vectorField_eq hWg']
  exact mlieBracket_sum_smul_mem
    (fun i _ ↦ ((hX.contMDiffOn i).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp))
    (fun i _ ↦ hX.isSubbundleFrameOn.apply_mem i hxU) hXX
    (fun i _ ↦ hf i) (fun j _ ↦ hg j)

/-- Over a Hausdorff base, a smooth constant-rank distribution `D` carries a Lie algebroid
structure whose anchor is the subbundle inclusion if and only if `D` is involutive. -/
theorem exists_lieAlgebroid_anchor_eq_subtypeL_iff (hD : IsContMDiffDistribution I ∞ k D) :
    (letI := hD.fiberBundle; letI := hD.vectorBundle;
      ∃ A : LieAlgebroid I (Fin k → ℝ) (fun x ↦ D x), ∀ x, A.anchor x = (D x).subtypeL) ↔
      IsInvolutiveDistribution I D :=
  ⟨fun ⟨_, hA⟩ ↦ isInvolutiveDistribution_of_anchor_eq_subtypeL hD hA,
    fun hinv ↦ ⟨ofDistribution hD hinv, fun _ ↦ rfl⟩⟩

end Converse

end Distribution

/-- The standard contact distribution on `ℝ³` is a smooth rank-2 distribution that admits no Lie
algebroid structure whose anchor is the subbundle inclusion. -/
theorem not_exists_lieAlgebroid_standardContactDistribution :
    let D₀ : Π p : ℝ × ℝ × ℝ, Submodule ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
      standardContactDistribution ℝ
    let hD : IsContMDiffDistribution 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ 2 D₀ :=
      isContMDiffDistribution_standardContactDistribution (𝕜 := ℝ) ∞
    letI := hD.fiberBundle
    letI := hD.vectorBundle
    ¬∃ A : LieAlgebroid 𝓘(ℝ, ℝ × ℝ × ℝ) (Fin 2 → ℝ) (fun p ↦ D₀ p),
      ∀ p, A.anchor p = (D₀ p).subtypeL :=
  fun h ↦ not_isInvolutiveDistribution_standardContactDistribution
    ((exists_lieAlgebroid_anchor_eq_subtypeL_iff
      (isContMDiffDistribution_standardContactDistribution (𝕜 := ℝ) ∞)).1 h)

end LieAlgebroid

end TauCeti
