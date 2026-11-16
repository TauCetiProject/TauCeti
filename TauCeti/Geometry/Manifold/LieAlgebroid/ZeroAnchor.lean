/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.LocalFrame
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
import TauCeti.Geometry.Manifold.DerivationBundle
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal

/-!
# Anchor uniqueness, zero-anchor Lie algebroids, and 1D rescaled tangent algebroids

Over a finite-dimensional Hausdorff base `M`, `A.bracket` uniquely determines `A.anchor`
(`anchor_eq_of_bracket_eq`, `ext_bracket`, `not_exists_lieAlgebroid_tangent_two_smul_anchor`), and
`A.anchor = 0` iff `A.bracket` is `C^∞(M)`-bilinear (`anchor_eq_zero_iff_bracket_smul_right`), built
via `ofZeroAnchor` (`LieAlgebroid.zero` trivial) with finite-rank fibre Lie algebras
(`zeroAnchorFiberBracket`, `zeroAnchorFiberLieRing`, `zeroAnchorFiberLieAlgebra`; Mackenzie 2005,
§3.3). In 1D, rescaling `tangent I M` by `φ` gives `rescaledTangent1D φ` and `mulCoordTangent`.
-/

public noncomputable section

open Bundle Manifold Module TopologicalSpace VectorField
open scoped ContDiff Topology

namespace TauCeti.LieAlgebroid

section GeneralBundle
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (I F V) in
/-- The trivial Lie algebroid on `V`, with zero anchor and zero bracket. -/
def zero : LieAlgebroid I F V where
  anchor := 0; bracket := 0; bracket_self _ := rfl; bracket_bracket _ _ _ := (add_zero 0).symm
  bracket_smul_apply _ _ _ _ := by
    simp only [LinearMap.zero_apply, ContMDiffSection.coe_zero, Pi.zero_apply, _root_.zero_apply,
      map_zero, smul_zero, zero_smul, add_zero]

instance instInhabited : Inhabited (LieAlgebroid I F V) := ⟨zero I F V⟩
@[simp] theorem zero_anchor_apply (x : M) : (zero I F V).anchor x = 0 := by
  rw [zero, ContMDiffSection.coe_zero, Pi.zero_apply]
@[simp] theorem zero_bracket_apply (a b : Cₛ^∞⟮I; F, V⟯) : (zero I F V).bracket a b = 0 := by
  rw [zero, LinearMap.zero_apply, LinearMap.zero_apply]

theorem bracket_smul_right_of_anchor_eq_zero {A : LieAlgebroid I F V} (hA : A.anchor = 0)
    (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) : A.bracket a (f • b) = f • A.bracket a b := by
  ext x; rw [A.bracket_smul_apply, hA, ContMDiffSection.coe_zero, Pi.zero_apply,
    _root_.zero_apply, map_zero, zero_smul, add_zero, ContMDiffSection.smul_apply]

theorem bracket_smul_left_of_anchor_eq_zero {A : LieAlgebroid I F V} (hA : A.anchor = 0)
    (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) : A.bracket (f • a) b = f • A.bracket a b := by
  rw [A.bracket_swap, A.bracket_smul_right_of_anchor_eq_zero hA, ← smul_neg, ← A.bracket_swap]

section OfZeroAnchor
variable (bracket : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯)
  (bracket_self : ∀ a, bracket a a = 0)
  (bracket_bracket : ∀ a b c,
    bracket a (bracket b c) = bracket (bracket a b) c + bracket b (bracket a c))

/-- Construct a zero-anchor Lie algebroid from an alternating Jacobi `C^∞(M)`-bilinear bracket. -/
def ofZeroAnchor : LieAlgebroid I F V where
  anchor := 0
  bracket := LinearMap.mk₂ ℝ (fun a b ↦ bracket a b)
    (fun _ _ _ ↦ by rw [map_add, LinearMap.add_apply])
    (fun r a _ ↦ by rw [LinearMapClass.map_smul_of_tower bracket r a, LinearMap.smul_apply])
    (fun a ↦ map_add (bracket a)) (fun r a b ↦ LinearMapClass.map_smul_of_tower (bracket a) r b)
  bracket_self := bracket_self; bracket_bracket := bracket_bracket
  bracket_smul_apply _ _ _ _ := by
    simp only [LinearMap.mk₂_apply, map_smul, ContMDiffSection.coe_zero, Pi.zero_apply,
      _root_.zero_apply, map_zero, zero_smul, add_zero, ContMDiffSection.smul_apply]

@[simp] theorem ofZeroAnchor_anchor :
    (ofZeroAnchor bracket bracket_self bracket_bracket).anchor = 0 := by ext x v; rw [ofZeroAnchor]
@[simp] theorem ofZeroAnchor_bracket_apply (a b : Cₛ^∞⟮I; F, V⟯) :
    (ofZeroAnchor bracket bracket_self bracket_bracket).bracket a b = bracket a b := by
  ext x; rw [ofZeroAnchor, LinearMap.mk₂_apply]
end OfZeroAnchor

section FiniteDimBase
variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]

omit [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] in
private theorem eq_of_forall_mvfderiv_smul_eq {x : M} {v : V x} (hv : v ≠ 0)
    {w₁ w₂ : TangentSpace I x}
    (h : ∀ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x w₁ • v = mvfderiv I f x w₂ • v) : w₁ = w₂ := by
  apply tangentToPointDerivation_injective (I := I) x; ext f; let f' : C^∞⟮I, M; ℝ⟯ := f
  change mvfderiv I f' x w₁ = mvfderiv I f' x w₂; by_contra hne
  have hinv := congrArg ((mvfderiv I f' x w₁ - mvfderiv I f' x w₂)⁻¹ • ·)
    (by rw [sub_smul, h f', sub_self] : (mvfderiv I f' x w₁ - mvfderiv I f' x w₂) • v = 0)
  rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul, smul_zero] at hinv; exact hv hinv

private theorem anchor_eq_of_forall_smul_eq
    {ρ₁ ρ₂ : Cₛ^∞⟮I; F →L[ℝ] E, fun x : M ↦ V x →L[ℝ] TangentSpace I x⟯}
    (h : ∀ (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) x,
      mvfderiv I f x (ρ₁ x (a x)) • a x = mvfderiv I f x (ρ₂ x (a x)) • a x) : ρ₁ = ρ₂ := by
  refine ContMDiffSection.ext fun x ↦ ContinuousLinearMap.ext fun v ↦ ?_
  by_cases hv : v = 0
  · simp only [hv, map_zero]
  · obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
    exact eq_of_forall_mvfderiv_smul_eq hv fun f ↦ by simpa [hsx] using h ⟨s, hs⟩ f x

/-- **The Lie bracket determines the anchor.** -/
theorem anchor_eq_of_bracket_eq {A₁ A₂ : LieAlgebroid I F V} (h : A₁.bracket = A₂.bracket) :
    A₁.anchor = A₂.anchor :=
  anchor_eq_of_forall_smul_eq fun a f x ↦ by
    have hb : A₁.bracket a (f • a) x = A₂.bracket a (f • a) x := congr($h a (f • a) x)
    rwa [A₁.bracket_smul_apply, A₂.bracket_smul_apply, A₁.bracket_self, A₂.bracket_self,
      ContMDiffSection.coe_zero, Pi.zero_apply, smul_zero, zero_add, zero_add] at hb

theorem ext_bracket {A₁ A₂ : LieAlgebroid I F V} (h : A₁.bracket = A₂.bracket) : A₁ = A₂ :=
  LieAlgebroid.ext (anchor_eq_of_bracket_eq h) h

/-- Over a finite-dimensional Hausdorff base, `A.anchor = 0` iff `A.bracket` is right
`C^∞(M)`-linear. -/
theorem anchor_eq_zero_iff_bracket_smul_right (A : LieAlgebroid I F V) :
    A.anchor = 0 ↔ ∀ (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯),
      A.bracket a (f • b) = f • A.bracket a b :=
  ⟨A.bracket_smul_right_of_anchor_eq_zero, fun h ↦ anchor_eq_of_forall_smul_eq fun a f x ↦ by
    have hb := congr($(h a a f) x)
    rw [A.bracket_smul_apply, ContMDiffSection.smul_apply, A.bracket_self,
      ContMDiffSection.coe_zero, Pi.zero_apply, smul_zero, zero_add] at hb
    rw [ContMDiffSection.coe_zero, Pi.zero_apply, _root_.zero_apply, map_zero, zero_smul]; exact hb⟩

/-- Over a nonempty manifold of positive dimension, no Lie algebroid on `TM` has bracket
`mlieBracket` and anchor `2 • id`. -/
theorem not_exists_lieAlgebroid_tangent_two_smul_anchor [Nontrivial E] [Nonempty M] :
    ¬ ∃ A : LieAlgebroid I E (TangentSpace I : M → Type _),
      (∀ (x : M) (v : TangentSpace I x), A.anchor x v = (2 : ℝ) • v) ∧
        A.bracket = (tangent I M).bracket := by
  rintro ⟨A, hρ, hbr⟩; obtain ⟨x⟩ := ‹Nonempty M›; obtain ⟨vE, hvE⟩ := exists_ne (0 : E)
  let e := trivializationAt E (TangentSpace I) x
  let v : TangentSpace I x := e.symmL ℝ x vE
  have hv : v ≠ 0 := fun h0 ↦ hvE <| by simpa [v, h0] using
    (e.continuousLinearMapAt_symmL (R := ℝ) (mem_baseSet_trivializationAt E _ x) vE).symm
  have hv' := hρ x v
  rw [ext_bracket hbr, tangent_anchor_apply, two_smul, left_eq_add] at hv'; exact hv hv'

section FiberLieAlgebra
variable [FiniteDimensional ℝ F] (A : LieAlgebroid I F V)

theorem bracket_apply_eq_zero_left_of_anchor_eq_zero (hA : A.anchor = 0) {x : M}
    {a : Cₛ^∞⟮I; F, V⟯} (ha : a x = 0) (b : Cₛ^∞⟮I; F, V⟯) : A.bracket a b x = 0 :=
  Submodule.smul_induction_on (p := fun u ↦ A.bracket u b x = 0)
    (mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero ha)
    (fun f hf u _ ↦ by rw [A.bracket_smul_left_of_anchor_eq_zero hA, ContMDiffSection.smul_apply,
      mem_smoothVanishingIdeal_iff.mp hf, zero_smul])
    (fun _ _ h₁ h₂ ↦ by
      rw [map_add, LinearMap.add_apply, ContMDiffSection.coe_add, Pi.add_apply, h₁, h₂, add_zero])

theorem bracket_apply_eq_zero_right_of_anchor_eq_zero (hA : A.anchor = 0) {x : M}
    (a : Cₛ^∞⟮I; F, V⟯) {b : Cₛ^∞⟮I; F, V⟯} (hb : b x = 0) : A.bracket a b x = 0 := by
  rw [A.bracket_swap, ContMDiffSection.coe_neg, Pi.neg_apply,
    A.bracket_apply_eq_zero_left_of_anchor_eq_zero hA hb, neg_zero]

theorem bracket_apply_congr_of_anchor_eq_zero (hA : A.anchor = 0) {x : M}
    {a₁ a₂ b₁ b₂ : Cₛ^∞⟮I; F, V⟯} (ha : a₁ x = a₂ x) (hb : b₁ x = b₂ x) :
    A.bracket a₁ b₁ x = A.bracket a₂ b₂ x := by
  have h₁ := A.bracket_apply_eq_zero_left_of_anchor_eq_zero hA (a := a₁ - a₂)
    (by rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact ha) b₁
  have h₂ := A.bracket_apply_eq_zero_right_of_anchor_eq_zero hA a₂ (b := b₁ - b₂)
    (by rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact hb)
  rw [map_sub, LinearMap.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₁
  rw [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₂; exact h₁.trans h₂

omit [FiniteDimensional ℝ F] in
private def chooseSectionAt (x : M) (v : V x) : Cₛ^∞⟮I; F, V⟯ :=
  (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v).choose
omit [FiniteDimensional ℝ F] in
private theorem chooseSectionAt_apply (x : M) (v : V x) :
    chooseSectionAt (I := I) (F := F) (V := V) x v x = v := by
  simpa [chooseSectionAt] using
    (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v).choose_spec

/-- The fibrewise `ℝ`-bilinear bracket on `V x` induced by a zero-anchor Lie algebroid `A`. -/
def zeroAnchorFiberBracket (hA : A.anchor = 0) (x : M) : V x →ₗ[ℝ] V x →ₗ[ℝ] V x :=
  let ch := chooseSectionAt (I := I) (F := F) (V := V) x
  have hc := chooseSectionAt_apply (I := I) (F := F) (V := V) x
  have hadd (w₁ w₂ : V x) : ch (w₁ + w₂) x = (ch w₁ + ch w₂) x := by
    rw [hc, ContMDiffSection.coe_add, Pi.add_apply, hc, hc]
  have hsmul (r : ℝ) (w : V x) : ch (r • w) x = (r • ch w) x := by
    rw [hc, ContMDiffSection.coe_smul, Pi.smul_apply, hc]
  LinearMap.mk₂ ℝ (fun u v ↦ A.bracket (ch u) (ch v) x)
    (fun u₁ u₂ v ↦ by rw [A.bracket_apply_congr_of_anchor_eq_zero hA (hadd u₁ u₂) rfl,
      map_add, LinearMap.add_apply, ContMDiffSection.coe_add, Pi.add_apply])
    (fun r u v ↦ by rw [A.bracket_apply_congr_of_anchor_eq_zero hA (hsmul r u) rfl,
      map_smul, LinearMap.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply])
    (fun u v₁ v₂ ↦ by rw [A.bracket_apply_congr_of_anchor_eq_zero hA rfl (hadd v₁ v₂),
      map_add, ContMDiffSection.coe_add, Pi.add_apply])
    (fun r u v ↦ by rw [A.bracket_apply_congr_of_anchor_eq_zero hA rfl (hsmul r v),
      map_smul, ContMDiffSection.coe_smul, Pi.smul_apply])

@[simp] theorem zeroAnchorFiberBracket_apply_section (hA : A.anchor = 0) (x : M)
    (a b : Cₛ^∞⟮I; F, V⟯) : A.zeroAnchorFiberBracket hA x (a x) (b x) = A.bracket a b x := by
  rw [zeroAnchorFiberBracket, LinearMap.mk₂_apply]; exact A.bracket_apply_congr_of_anchor_eq_zero
    hA (chooseSectionAt_apply x (a x)) (chooseSectionAt_apply x (b x))

/-- The induced fibrewise `LieRing` structure on `V x` for a zero-anchor Lie algebroid `A`. -/
@[instance_reducible] def zeroAnchorFiberLieRing (hA : A.anchor = 0) (x : M) : LieRing (V x) :=
  have hsurj := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x
  { bracket := fun u v ↦ A.zeroAnchorFiberBracket hA x u v
    add_lie := fun _ _ _ ↦ by rw [map_add, LinearMap.add_apply]
    lie_add := fun u ↦ map_add (A.zeroAnchorFiberBracket hA x u)
    lie_self := fun u ↦ by
      obtain ⟨a, rfl⟩ := hsurj u
      rw [ContMDiffSection.evalLinearMap_apply, A.zeroAnchorFiberBracket_apply_section hA x a a,
        A.bracket_self, ContMDiffSection.coe_zero, Pi.zero_apply]
    leibniz_lie := fun u v w ↦ by
      obtain ⟨a, rfl⟩ := hsurj u; obtain ⟨b, rfl⟩ := hsurj v; obtain ⟨c, rfl⟩ := hsurj w
      simp only [ContMDiffSection.evalLinearMap_apply, A.zeroAnchorFiberBracket_apply_section]
      rw [A.bracket_bracket a b c, ContMDiffSection.coe_add, Pi.add_apply] }

/-- The induced fibrewise `ℝ`-`LieAlgebra` structure on `V x` for a zero-anchor Lie algebroid. -/
@[instance_reducible] def zeroAnchorFiberLieAlgebra (hA : A.anchor = 0) (x : M) :
    letI : LieRing (V x) := A.zeroAnchorFiberLieRing hA x; LieAlgebra ℝ (V x) :=
  letI : LieRing (V x) := A.zeroAnchorFiberLieRing hA x
  { lie_smul := fun r u v ↦ map_smul (A.zeroAnchorFiberBracket hA x u) r v }
end FiberLieAlgebra
end FiniteDimBase
end GeneralBundle

section RescaledTangent1D
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ ℝ H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem rescaledTangent1D_cyclic_deriv_eq_zero (φ : C^∞⟮I, M; ℝ⟯)
    (X Y Z : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    (tangent I M).anchorDeriv X φ x₀ • (tangent I M).bracket Y Z x₀ =
      (tangent I M).anchorDeriv Y φ x₀ • (tangent I M).bracket X Z x₀ -
        (tangent I M).anchorDeriv Z φ x₀ • (tangent I M).bracket X Y x₀ := by
  let T := tangent I M; let e := trivializationAt ℝ (TangentSpace I) x₀
  let U : Opens M := ⟨e.baseSet, e.open_baseSet⟩; have hU : (U : Set M) ⊆ e.baseSet := subset_rfl
  let z₀ : U := ⟨x₀, mem_baseSet_trivializationAt ℝ (TangentSpace I) x₀⟩
  let b := Basis.singleton Unit ℝ; let TU := T.restrict U
  let e₀ := e.openLocalFrameSection I ∞ b hU (); let co := e.openLocalFrameCoeff I ∞ b hU ()
  let w₀ : TangentSpace I x₀ := e₀ z₀
  let jU : C^∞⟮I, U; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  have hexp (W : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) :
      W.restrict U = co (W.restrict U) • e₀ := by
    have h := e.eq_sum_openLocalFrameCoeff_smul b hU (W.restrict U)
    rwa [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h
  have hbr (V₁ V₂ : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) : T.bracket V₁ V₂ x₀ =
      (co (V₁.restrict U) z₀ * TU.anchorDeriv e₀ (co (V₂.restrict U)) z₀ -
        co (V₂.restrict U) z₀ * TU.anchorDeriv e₀ (co (V₁.restrict U)) z₀) • w₀ := by
    have h₁ : T.bracket V₁ V₂ x₀ = TU.bracket (V₁.restrict U) (V₂.restrict U) z₀ :=
      ((T.bracket V₁ V₂).restrict_apply U z₀).symm.trans
        (congr($(T.restrict_bracket_restrict U V₁ V₂) z₀)).symm
    conv_lhs => rw [h₁, hexp V₁, hexp V₂, TU.bracket_smul_smul, TU.bracket_self, smul_zero,
      zero_add]
    simp only [ContMDiffSection.coe_sub, ContMDiffSection.smul_apply, ContMDiffMap.coe_mul,
      Pi.sub_apply, Pi.mul_apply]; exact (sub_smul _ _ w₀).symm
  have hd (V₁ : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) :
      T.anchorDeriv V₁ φ x₀ = co (V₁.restrict U) z₀ * TU.anchorDeriv e₀ (φ.comp jU) z₀ := by
    have h₁ : T.anchorDeriv V₁ φ x₀ = TU.anchorDeriv (V₁.restrict U) (φ.comp jU) z₀ :=
      (congr($(T.restrict_anchorDeriv_comp U V₁ φ) z₀)).symm
    conv_lhs => rw [h₁, hexp V₁, TU.anchorDeriv_smul_left]
    rfl
  rw [hbr Y Z, hbr X Z, hbr X Y, hd X, hd Y, hd Z, smul_smul, smul_smul, smul_smul, ← sub_smul]
  exact congrArg (· • w₀) (by ring)

/-- On a 1D Hausdorff smooth manifold `M`, rescaling the anchor and bracket of `TM` by a smooth
function `φ : C^∞⟮I, M; ℝ⟯` yields a Lie algebroid. -/
def rescaledTangent1D (φ : C^∞⟮I, M; ℝ⟯) : LieAlgebroid I ℝ (TangentSpace I : M → Type _) where
  anchor := φ • (tangent I M).anchor
  bracket := LinearMap.mk₂ ℝ (fun X Y ↦ φ • (tangent I M).bracket X Y)
    (fun _ _ _ ↦ by rw [map_add, LinearMap.add_apply, smul_add])
    (fun _ _ _ ↦ by rw [map_smul, LinearMap.smul_apply, smul_comm])
    (fun _ _ _ ↦ by rw [map_add, smul_add]) (fun _ _ _ ↦ by rw [map_smul, smul_comm])
  bracket_self _ := by simp only [LinearMap.mk₂_apply, (tangent I M).bracket_self, smul_zero]
  bracket_bracket X Y Z := by
    ext x₀
    simp only [LinearMap.mk₂_apply, (tangent I M).bracket_smul_right,
      (tangent I M).bracket_smul_left, smul_add, smul_sub, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, ContMDiffSection.smul_apply, Pi.add_apply, Pi.sub_apply]
    rw [(tangent I M).bracket_bracket X Y Z, ContMDiffSection.coe_add, Pi.add_apply, smul_add,
      smul_add, rescaledTangent1D_cyclic_deriv_eq_zero φ X Y Z x₀, smul_sub]
    abel_nf
  bracket_smul_apply X Y f x := by
    simp only [LinearMap.mk₂_apply, ContMDiffSection.smul_apply, (tangent I M).bracket_smul_apply,
      _root_.smul_apply, tangent_anchor_apply, map_smul, smul_add, smul_smul, smul_eq_mul,
      mul_comm (φ x) (f x)]

@[simp] theorem rescaledTangent1D_anchor_apply (φ : C^∞⟮I, M; ℝ⟯) (x : M) (v : TangentSpace I x) :
    (rescaledTangent1D φ).anchor x v = φ x • v := by
  rw [rescaledTangent1D, ContMDiffSection.smul_apply, _root_.smul_apply, tangent_anchor_apply]

@[simp] theorem rescaledTangent1D_bracket_apply (φ : C^∞⟮I, M; ℝ⟯)
    (X Y : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) (x : M) :
    (rescaledTangent1D φ).bracket X Y x = φ x • mlieBracket I X Y x := by
  rw [rescaledTangent1D, LinearMap.mk₂_apply, ContMDiffSection.smul_apply, tangent_bracket_apply]

/-- The Lie algebroid on `Tℝ` with anchor `ρ(x)(v) = x • v` and bracket `[X, Y]_x = x • [X, Y]`. -/
def mulCoordTangent : LieAlgebroid 𝓘(ℝ, ℝ) ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) :=
  rescaledTangent1D (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯)

@[simp] theorem mulCoordTangent_anchor_apply (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    mulCoordTangent.anchor x v = x • v := by
  exact rescaledTangent1D_anchor_apply ContMDiffMap.id x v

@[simp] theorem mulCoordTangent_bracket_apply
    (X Y : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) (x : ℝ) :
    mulCoordTangent.bracket X Y x = x • mlieBracket 𝓘(ℝ, ℝ) X Y x := by
  exact rescaledTangent1D_bracket_apply ContMDiffMap.id X Y x

/-- Expanding `mulCoordTangent.bracket (f • X) (g • X)` gives `(x * (f X(g) - g X(f))) • X`. -/
theorem mulCoordTangent_bracket_smul_smul
    (X : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯)
    (f g : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯) (x : ℝ) :
    mulCoordTangent.bracket (f • X) (g • X) x =
      (x * (f x * mvfderiv 𝓘(ℝ, ℝ) g x (X x) - g x * mvfderiv 𝓘(ℝ, ℝ) f x (X x))) • X x := by
  rw [mulCoordTangent.bracket_smul_smul, mulCoordTangent.bracket_self, smul_zero, zero_add,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.smul_apply,
    ContMDiffSection.smul_apply, ContMDiffMap.coe_mul, ContMDiffMap.coe_mul, Pi.mul_apply,
    Pi.mul_apply, anchorDeriv_apply, anchorDeriv_apply, mulCoordTangent_anchor_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul, ← sub_smul]
  exact congrArg (· • X x) (by ring)

end RescaledTangent1D

end TauCeti.LieAlgebroid
