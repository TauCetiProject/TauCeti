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
# Anchor uniqueness, zero-anchor Lie algebroids, and one-dimensional rescaled tangent algebroids

Over a finite-dimensional Hausdorff base manifold `M`, the anchor of a Lie algebroid `A` on a
smooth real vector bundle `V → M` is uniquely determined by its Lie bracket (`ext_bracket`):
comparing `[a, f • a]` on a section `a` with `a x = v ≠ 0` determines `mvfderiv I f x (ρ x v)` for
all smooth functions `f`, and point derivations separate tangent vectors. Consequently, changing
the anchor of the tangent Lie algebroid `TM` from `id` to `2 • id` while retaining the Lie bracket
of vector fields cannot satisfy the Leibniz rule over any nontrivial base
(`not_exists_lieAlgebroid_tangent_two_smul_anchor`).

A Lie algebroid has zero anchor if and only if its section bracket is `C^∞(M)`-bilinear
(`anchor_eq_zero_iff_bracket_smul_right`); conversely, any alternating `C^∞(M)`-bilinear section
bracket satisfying the Jacobi identity defines a zero-anchor Lie algebroid (`ofZeroAnchor`), with
the zero bracket giving the trivial Lie algebroid `LieAlgebroid.zero`. When `V` has finite rank, a
zero-anchor Lie algebroid induces a `LieRing` and `ℝ`-`LieAlgebra` structure on each fibre `V x`
(`zeroAnchorFiberBracket`, `zeroAnchorFiberLieRing`, `zeroAnchorFiberLieAlgebra`).

Finally, on any one-dimensional Hausdorff smooth manifold `M`, rescaling both the identity anchor
and the vector-field Lie bracket of `TM` by an arbitrary smooth function `φ : C^∞⟮I, M; ℝ⟯` yields
a Lie algebroid `rescaledTangent1D φ` (with `mulCoordTangent` on `ℝ` corresponding to `φ(x) = x`).

## Main definitions

* `TauCeti.LieAlgebroid.zero`: the trivial Lie algebroid with zero anchor and zero bracket.
* `TauCeti.LieAlgebroid.ofZeroAnchor`: zero-anchor Lie algebroid from an alternating Jacobi
  `C^∞(M)`-bilinear bracket on smooth sections.
* `TauCeti.LieAlgebroid.zeroAnchorFiberBracket`, `TauCeti.LieAlgebroid.zeroAnchorFiberLieRing`,
  `TauCeti.LieAlgebroid.zeroAnchorFiberLieAlgebra`: the induced fibrewise Lie algebra of a
  zero-anchor Lie algebroid on a finite-rank bundle.
* `TauCeti.LieAlgebroid.rescaledTangent1D` and `TauCeti.LieAlgebroid.mulCoordTangent`: rescaled
  tangent Lie algebroids in dimension one, including the `x ∂_x`-anchored Lie algebroid on `Tℝ`.

## Main results

* `TauCeti.LieAlgebroid.anchor_eq_of_bracket_eq` and `TauCeti.LieAlgebroid.ext_bracket`: the Lie
  bracket uniquely determines the anchor.
* `TauCeti.LieAlgebroid.anchor_eq_zero_iff_bracket_smul_right`: `A.anchor = 0` iff `A.bracket` is
  right `C^∞(M)`-linear.
* `TauCeti.LieAlgebroid.not_exists_lieAlgebroid_tangent_two_smul_anchor`: no Lie algebroid on `TM`
  over a nonempty manifold of positive dimension has bracket `mlieBracket` and anchor `2 • id`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), §1.1.
-/

public section

noncomputable section

open Bundle Manifold Module TopologicalSpace VectorField
open scoped ContDiff Topology

namespace TauCeti

namespace LieAlgebroid

section ZeroAndBilinear

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (I F V) in
/-- The trivial Lie algebroid on `V`, with zero anchor and zero bracket. -/
def zero : LieAlgebroid I F V where
  anchor := 0
  bracket := 0
  bracket_self _ := rfl
  bracket_bracket _ _ _ := (add_zero 0).symm
  bracket_smul_apply _ _ _ _ := by
    simp only [LinearMap.zero_apply, ContMDiffSection.coe_zero, Pi.zero_apply, _root_.zero_apply,
      map_zero, smul_zero, zero_smul, add_zero]

instance instInhabited : Inhabited (LieAlgebroid I F V) :=
  ⟨zero I F V⟩

@[simp]
theorem zero_anchor_apply (x : M) : (zero I F V).anchor x = 0 := by
  rw [zero, ContMDiffSection.coe_zero, Pi.zero_apply]

@[simp]
theorem zero_bracket_apply (a b : Cₛ^∞⟮I; F, V⟯) : (zero I F V).bracket a b = 0 := by
  rw [zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-- When `A.anchor = 0`, the bracket is right `C^∞(M)`-linear. -/
theorem bracket_smul_right_of_anchor_eq_zero {A : LieAlgebroid I F V} (hA : A.anchor = 0)
    (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.bracket a (f • b) = f • A.bracket a b := by
  ext x
  rw [A.bracket_smul_apply, hA, ContMDiffSection.coe_zero, Pi.zero_apply,
    _root_.zero_apply, map_zero, zero_smul, add_zero, ContMDiffSection.smul_apply]

/-- When `A.anchor = 0`, the bracket is left `C^∞(M)`-linear. -/
theorem bracket_smul_left_of_anchor_eq_zero {A : LieAlgebroid I F V} (hA : A.anchor = 0)
    (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.bracket (f • a) b = f • A.bracket a b := by
  rw [A.bracket_swap, A.bracket_smul_right_of_anchor_eq_zero hA, ← smul_neg, ← A.bracket_swap]

/-- Construct a zero-anchor Lie algebroid from an alternating `C^∞(M)`-bilinear bracket on smooth
sections satisfying the Jacobi identity. -/
def ofZeroAnchor
    (bracket : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯)
    (bracket_self : ∀ a, bracket a a = 0)
    (bracket_bracket : ∀ a b c,
      bracket a (bracket b c) = bracket (bracket a b) c + bracket b (bracket a c)) :
    LieAlgebroid I F V where
  anchor := 0
  bracket := LinearMap.mk₂ ℝ (fun a b ↦ bracket a b)
    (fun a₁ a₂ b ↦ by rw [map_add, LinearMap.add_apply])
    (fun r a b ↦ by rw [LinearMapClass.map_smul_of_tower, LinearMap.smul_apply])
    (fun a b₁ b₂ ↦ map_add (bracket a) b₁ b₂)
    (fun r a b ↦ LinearMapClass.map_smul_of_tower (bracket a) r b)
  bracket_self := bracket_self
  bracket_bracket := bracket_bracket
  bracket_smul_apply a b f x := by
    simp only [LinearMap.mk₂_apply, map_smul, ContMDiffSection.coe_zero, Pi.zero_apply,
      _root_.zero_apply, map_zero, zero_smul, add_zero, ContMDiffSection.smul_apply]

@[simp]
theorem ofZeroAnchor_anchor
    (bracket : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯)
    (bracket_self : ∀ a, bracket a a = 0)
    (bracket_bracket : ∀ a b c,
      bracket a (bracket b c) = bracket (bracket a b) c + bracket b (bracket a c)) :
    (ofZeroAnchor bracket bracket_self bracket_bracket).anchor = 0 := by
  ext x v
  rw [ofZeroAnchor]

@[simp]
theorem ofZeroAnchor_bracket_apply
    (bracket : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯)
    (bracket_self : ∀ a, bracket a a = 0)
    (bracket_bracket : ∀ a b c,
      bracket a (bracket b c) = bracket (bracket a b) c + bracket b (bracket a c))
    (a b : Cₛ^∞⟮I; F, V⟯) :
    (ofZeroAnchor bracket bracket_self bracket_bracket).bracket a b = bracket a b := by
  ext x
  rw [ofZeroAnchor, LinearMap.mk₂_apply]

end ZeroAndBilinear

section AnchorUniqueness

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

omit [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] in
private theorem eq_of_forall_mvfderiv_smul_eq {x : M} {v : V x} (hv : v ≠ 0)
    {w₁ w₂ : TangentSpace I x}
    (h : ∀ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x w₁ • v = mvfderiv I f x w₂ • v) :
    w₁ = w₂ := by
  apply tangentToPointDerivation_injective (I := I) x
  ext f
  let f' : C^∞⟮I, M; ℝ⟯ := f
  have h₁ : tangentToPointDerivation x w₁ f = mvfderiv I f' x w₁ := rfl
  have h₂ : tangentToPointDerivation x w₂ f = mvfderiv I f' x w₂ := rfl
  rw [h₁, h₂]
  by_contra hne
  have hsub : (mvfderiv I f' x w₁ - mvfderiv I f' x w₂) • v = 0 := by
    rw [sub_smul, h f', sub_self]
  have hinv := congrArg ((mvfderiv I f' x w₁ - mvfderiv I f' x w₂)⁻¹ • ·) hsub
  rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul, smul_zero] at hinv
  exact hv hinv

/-- **The Lie bracket determines the anchor.** Over a finite-dimensional Hausdorff base, two Lie
algebroids on the same smooth vector bundle with the same section bracket have the same anchor. -/
theorem anchor_eq_of_bracket_eq {A₁ A₂ : LieAlgebroid I F V} (h : A₁.bracket = A₂.bracket) :
    A₁.anchor = A₂.anchor := by
  apply ContMDiffSection.ext
  intro x
  ext v
  by_cases hv : v = 0
  · simp only [hv, map_zero]
  · obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
    let a : Cₛ^∞⟮I; F, V⟯ := ⟨s, hs⟩
    have hax : a x = v := hsx
    refine eq_of_forall_mvfderiv_smul_eq hv fun f ↦ ?_
    have hb : A₁.bracket a (f • a) x = A₂.bracket a (f • a) x := congr($h a (f • a) x)
    rw [A₁.bracket_smul_apply, A₂.bracket_smul_apply, A₁.bracket_self, A₂.bracket_self,
      ContMDiffSection.coe_zero, Pi.zero_apply, smul_zero, zero_add, zero_add, hax] at hb
    exact hb

/-- Two Lie algebroids over a finite-dimensional Hausdorff base are equal as soon as their section
brackets coincide. -/
theorem ext_bracket {A₁ A₂ : LieAlgebroid I F V} (h : A₁.bracket = A₂.bracket) : A₁ = A₂ :=
  LieAlgebroid.ext (anchor_eq_of_bracket_eq h) h

/-- Over a finite-dimensional Hausdorff base, a Lie algebroid has zero anchor if and only if its
section bracket is right `C^∞(M)`-linear. -/
theorem anchor_eq_zero_iff_bracket_smul_right (A : LieAlgebroid I F V) :
    A.anchor = 0 ↔ ∀ (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯),
      A.bracket a (f • b) = f • A.bracket a b := by
  refine ⟨A.bracket_smul_right_of_anchor_eq_zero, fun h ↦ ?_⟩
  apply ContMDiffSection.ext
  intro x
  ext v
  rw [ContMDiffSection.coe_zero, Pi.zero_apply, _root_.zero_apply]
  by_cases hv : v = 0
  · simp only [hv, map_zero]
  · obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
    let a : Cₛ^∞⟮I; F, V⟯ := ⟨s, hs⟩
    have hax : a x = v := hsx
    refine eq_of_forall_mvfderiv_smul_eq hv fun f ↦ ?_
    have hb := congr($(h a a f) x)
    rw [A.bracket_smul_apply, ContMDiffSection.smul_apply, A.bracket_self,
      ContMDiffSection.coe_zero, Pi.zero_apply, smul_zero, zero_add, hax] at hb
    rw [map_zero, zero_smul]
    exact hb

/-- Over a nonempty manifold of positive dimension, there is no Lie algebroid on `TM` whose bracket
is the Lie bracket of vector fields and whose anchor is `2 • id`. -/
theorem not_exists_lieAlgebroid_tangent_two_smul_anchor [Nontrivial E] [Nonempty M] :
    ¬ ∃ A : LieAlgebroid I E (TangentSpace I : M → Type _),
      (∀ (x : M) (v : TangentSpace I x), A.anchor x v = (2 : ℝ) • v) ∧
        A.bracket = (tangent I M).bracket := by
  rintro ⟨A, hρ, hbr⟩
  have hA : A = tangent I M := ext_bracket hbr
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨vE, hvE⟩ := exists_ne (0 : E)
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let v : TangentSpace I x := e.symmL ℝ x vE
  have hv : v ≠ 0 := fun h0 ↦ hvE <| by
    have h1 := e.continuousLinearMapAt_symmL (R := ℝ) hx vE
    rw [show e.symmL ℝ x vE = v from rfl, h0, map_zero] at h1
    exact h1.symm
  have hv' := hρ x v
  rw [hA, tangent_anchor_apply, two_smul, left_eq_add] at hv'
  exact hv hv'

end AnchorUniqueness

section FiberLieAlgebra

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  (A : LieAlgebroid I F V)

/-- In a zero-anchor Lie algebroid on a finite-rank bundle, `[a, b] x = 0` whenever `a x = 0`. -/
theorem bracket_apply_eq_zero_left_of_anchor_eq_zero (hA : A.anchor = 0) {x : M}
    {a : Cₛ^∞⟮I; F, V⟯} (ha : a x = 0) (b : Cₛ^∞⟮I; F, V⟯) :
    A.bracket a b x = 0 := by
  have hmem := mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero ha
  refine Submodule.smul_induction_on (p := fun u ↦ A.bracket u b x = 0) hmem ?_ ?_
  · intro f hf u _
    rw [A.bracket_smul_left_of_anchor_eq_zero hA, ContMDiffSection.smul_apply,
      mem_smoothVanishingIdeal_iff.mp hf, zero_smul]
  · intro u₁ u₂ h₁ h₂
    rw [map_add, LinearMap.add_apply, ContMDiffSection.coe_add, Pi.add_apply, h₁, h₂, add_zero]

/-- In a zero-anchor Lie algebroid on a finite-rank bundle, `[a, b] x = 0` whenever `b x = 0`. -/
theorem bracket_apply_eq_zero_right_of_anchor_eq_zero (hA : A.anchor = 0) {x : M}
    (a : Cₛ^∞⟮I; F, V⟯) {b : Cₛ^∞⟮I; F, V⟯} (hb : b x = 0) :
    A.bracket a b x = 0 := by
  rw [A.bracket_swap, ContMDiffSection.coe_neg, Pi.neg_apply,
    A.bracket_apply_eq_zero_left_of_anchor_eq_zero hA hb, neg_zero]

/-- In a zero-anchor Lie algebroid on a finite-rank bundle, `[a, b] x` depends only on `a x` and
`b x`. -/
theorem bracket_apply_congr_of_anchor_eq_zero (hA : A.anchor = 0) {x : M}
    {a₁ a₂ b₁ b₂ : Cₛ^∞⟮I; F, V⟯} (ha : a₁ x = a₂ x) (hb : b₁ x = b₂ x) :
    A.bracket a₁ b₁ x = A.bracket a₂ b₂ x := by
  have ha0 : (a₁ - a₂) x = 0 := by
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact ha
  have hb0 : (b₁ - b₂) x = 0 := by
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact hb
  have h₁ := A.bracket_apply_eq_zero_left_of_anchor_eq_zero hA ha0 b₁
  have h₂ := A.bracket_apply_eq_zero_right_of_anchor_eq_zero hA a₂ hb0
  rw [map_sub, LinearMap.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₁
  rw [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₂
  exact h₁.trans h₂

omit [FiniteDimensional ℝ F] in
private def chooseSectionAt (x : M) (v : V x) : Cₛ^∞⟮I; F, V⟯ :=
  (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v).choose

omit [FiniteDimensional ℝ F] in
private theorem chooseSectionAt_apply (x : M) (v : V x) :
    chooseSectionAt (I := I) (F := F) (V := V) x v x = v := by
  simpa [chooseSectionAt] using
    (ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v).choose_spec

/-- The fibrewise `ℝ`-bilinear bracket on `V x` induced by a zero-anchor Lie algebroid `A` on a
finite-rank smooth vector bundle. -/
def zeroAnchorFiberBracket (hA : A.anchor = 0) (x : M) : V x →ₗ[ℝ] V x →ₗ[ℝ] V x :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ A.bracket (chooseSectionAt x u) (chooseSectionAt x v) x)
    (fun u₁ u₂ v ↦ by
      have h : chooseSectionAt (I := I) (F := F) (V := V) x (u₁ + u₂) x =
          (chooseSectionAt (I := I) (F := F) (V := V) x u₁ +
            chooseSectionAt (I := I) (F := F) (V := V) x u₂) x := by
        rw [chooseSectionAt_apply, ContMDiffSection.coe_add, Pi.add_apply,
          chooseSectionAt_apply, chooseSectionAt_apply]
      rw [A.bracket_apply_congr_of_anchor_eq_zero hA h rfl, map_add, LinearMap.add_apply,
        ContMDiffSection.coe_add, Pi.add_apply])
    (fun r u v ↦ by
      have h : chooseSectionAt (I := I) (F := F) (V := V) x (r • u) x =
          (r • chooseSectionAt (I := I) (F := F) (V := V) x u) x := by
        rw [chooseSectionAt_apply, ContMDiffSection.coe_smul, Pi.smul_apply, chooseSectionAt_apply]
      rw [A.bracket_apply_congr_of_anchor_eq_zero hA h rfl, map_smul, LinearMap.smul_apply,
        ContMDiffSection.coe_smul, Pi.smul_apply])
    (fun u v₁ v₂ ↦ by
      have h : chooseSectionAt (I := I) (F := F) (V := V) x (v₁ + v₂) x =
          (chooseSectionAt (I := I) (F := F) (V := V) x v₁ +
            chooseSectionAt (I := I) (F := F) (V := V) x v₂) x := by
        rw [chooseSectionAt_apply, ContMDiffSection.coe_add, Pi.add_apply,
          chooseSectionAt_apply, chooseSectionAt_apply]
      rw [A.bracket_apply_congr_of_anchor_eq_zero hA rfl h, map_add,
        ContMDiffSection.coe_add, Pi.add_apply])
    (fun r u v ↦ by
      have h : chooseSectionAt (I := I) (F := F) (V := V) x (r • v) x =
          (r • chooseSectionAt (I := I) (F := F) (V := V) x v) x := by
        rw [chooseSectionAt_apply, ContMDiffSection.coe_smul, Pi.smul_apply, chooseSectionAt_apply]
      rw [A.bracket_apply_congr_of_anchor_eq_zero hA rfl h, map_smul,
        ContMDiffSection.coe_smul, Pi.smul_apply])

@[simp]
theorem zeroAnchorFiberBracket_apply_section (hA : A.anchor = 0) (x : M)
    (a b : Cₛ^∞⟮I; F, V⟯) :
    A.zeroAnchorFiberBracket hA x (a x) (b x) = A.bracket a b x := by
  rw [zeroAnchorFiberBracket, LinearMap.mk₂_apply]
  exact A.bracket_apply_congr_of_anchor_eq_zero hA
    (chooseSectionAt_apply x (a x)) (chooseSectionAt_apply x (b x))

/-- The induced fibrewise `LieRing` structure on `V x` for a zero-anchor Lie algebroid `A`. -/
@[instance_reducible]
def zeroAnchorFiberLieRing (hA : A.anchor = 0) (x : M) : LieRing (V x) where
  bracket u v := A.zeroAnchorFiberBracket hA x u v
  add_lie u₁ u₂ v := by rw [map_add, LinearMap.add_apply]
  lie_add u v₁ v₂ := map_add (A.zeroAnchorFiberBracket hA x u) v₁ v₂
  lie_self u := by
    obtain ⟨a, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x u
    rw [ContMDiffSection.evalLinearMap_apply, A.zeroAnchorFiberBracket_apply_section hA x a a,
      A.bracket_self, ContMDiffSection.coe_zero, Pi.zero_apply]
  leibniz_lie u v w := by
    obtain ⟨a, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x u
    obtain ⟨b, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v
    obtain ⟨c, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x w
    simp only [ContMDiffSection.evalLinearMap_apply, A.zeroAnchorFiberBracket_apply_section]
    rw [A.bracket_bracket a b c, ContMDiffSection.coe_add, Pi.add_apply]

/-- The induced fibrewise `ℝ`-`LieAlgebra` structure on `V x` for a zero-anchor Lie algebroid `A`.
-/
@[instance_reducible]
def zeroAnchorFiberLieAlgebra (hA : A.anchor = 0) (x : M) :
    letI : LieRing (V x) := A.zeroAnchorFiberLieRing hA x
    LieAlgebra ℝ (V x) :=
  letI : LieRing (V x) := A.zeroAnchorFiberLieRing hA x
  { lie_smul := fun r u v ↦ map_smul (A.zeroAnchorFiberBracket hA x u) r v }

end FiberLieAlgebra

section RescaledTangent1D

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ ℝ H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem rescaledTangent1D_cyclic_deriv_eq_zero (φ : C^∞⟮I, M; ℝ⟯)
    (X Y Z : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    (tangent I M).anchorDeriv X φ x₀ • (tangent I M).bracket Y Z x₀ =
      (tangent I M).anchorDeriv Y φ x₀ • (tangent I M).bracket X Z x₀ -
        (tangent I M).anchorDeriv Z φ x₀ • (tangent I M).bracket X Y x₀ := by
  let T := tangent I M
  let e := trivializationAt ℝ (TangentSpace I) x₀
  let U : Opens M := ⟨e.baseSet, e.open_baseSet⟩
  have hU : (U : Set M) ⊆ e.baseSet := subset_rfl
  let z₀ : U := ⟨x₀, mem_baseSet_trivializationAt ℝ (TangentSpace I) x₀⟩
  let b := Basis.singleton Unit ℝ
  let e₀ := e.openLocalFrameSection I ∞ b hU ()
  let w₀ : TangentSpace I x₀ := e₀ z₀
  let co := e.openLocalFrameCoeff I ∞ b hU ()
  let TU := T.restrict U
  let jU : C^∞⟮I, U; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  have hexp (W : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) :
      W.restrict U = co (W.restrict U) • e₀ := by
    have h := e.eq_sum_openLocalFrameCoeff_smul b hU (W.restrict U)
    rwa [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at h
  have hbr (V₁ V₂ : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) :
      T.bracket V₁ V₂ x₀ =
        (co (V₁.restrict U) z₀ * TU.anchorDeriv e₀ (co (V₂.restrict U)) z₀ -
          co (V₂.restrict U) z₀ * TU.anchorDeriv e₀ (co (V₁.restrict U)) z₀) • w₀ := by
    have h₁ : T.bracket V₁ V₂ x₀ = TU.bracket (V₁.restrict U) (V₂.restrict U) z₀ :=
      ((T.bracket V₁ V₂).restrict_apply U z₀).symm.trans
        (congr($(T.restrict_bracket_restrict U V₁ V₂) z₀)).symm
    conv_lhs => rw [h₁, hexp V₁, hexp V₂, TU.bracket_smul_smul, TU.bracket_self, smul_zero,
      zero_add]
    simp only [ContMDiffSection.coe_sub, ContMDiffSection.smul_apply, ContMDiffMap.coe_mul,
      Pi.sub_apply, Pi.mul_apply]
    exact (sub_smul _ _ w₀).symm
  have hd (V₁ : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) :
      T.anchorDeriv V₁ φ x₀ = co (V₁.restrict U) z₀ * TU.anchorDeriv e₀ (φ.comp jU) z₀ := by
    have h₁ : T.anchorDeriv V₁ φ x₀ = TU.anchorDeriv (V₁.restrict U) (φ.comp jU) z₀ :=
      (congr($(T.restrict_anchorDeriv_comp U V₁ φ) z₀)).symm
    conv_lhs => rw [h₁, hexp V₁, TU.anchorDeriv_smul_left]
    rfl
  rw [hbr Y Z, hbr X Z, hbr X Y, hd X, hd Y, hd Z, smul_smul, smul_smul, smul_smul, ← sub_smul]
  exact congrArg (· • w₀) (by ring)

/-- On any one-dimensional Hausdorff smooth manifold `M`, rescaling both the identity anchor and the
vector-field Lie bracket of `TM` by a smooth function `φ : C^∞⟮I, M; ℝ⟯` yields a Lie algebroid. -/
def rescaledTangent1D (φ : C^∞⟮I, M; ℝ⟯) : LieAlgebroid I ℝ (TangentSpace I : M → Type _) where
  anchor := φ • (tangent I M).anchor
  bracket := LinearMap.mk₂ ℝ (fun X Y ↦ φ • (tangent I M).bracket X Y)
    (fun X₁ X₂ Y ↦ by rw [map_add, LinearMap.add_apply, smul_add])
    (fun r X Y ↦ by rw [map_smul, LinearMap.smul_apply, smul_comm])
    (fun X Y₁ Y₂ ↦ by rw [map_add, smul_add])
    (fun r X Y ↦ by rw [map_smul, smul_comm])
  bracket_self X := by simp only [LinearMap.mk₂_apply, (tangent I M).bracket_self, smul_zero]
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
      _root_.smul_apply, tangent_anchor_apply, map_smul, smul_add, smul_smul,
      smul_eq_mul, mul_comm (φ x) (f x)]

@[simp]
theorem rescaledTangent1D_anchor_apply (φ : C^∞⟮I, M; ℝ⟯) (x : M) (v : TangentSpace I x) :
    (rescaledTangent1D φ).anchor x v = φ x • v := by
  rw [rescaledTangent1D, ContMDiffSection.smul_apply, _root_.smul_apply,
    tangent_anchor_apply]

@[simp]
theorem rescaledTangent1D_bracket_apply (φ : C^∞⟮I, M; ℝ⟯)
    (X Y : Cₛ^∞⟮I; ℝ, (TangentSpace I : M → Type _)⟯) (x : M) :
    (rescaledTangent1D φ).bracket X Y x = φ x • mlieBracket I X Y x := by
  rw [rescaledTangent1D, LinearMap.mk₂_apply, ContMDiffSection.smul_apply, tangent_bracket_apply]

/-- The Lie algebroid on `Tℝ` with anchor `ρ(x)(v) = x • v` and bracket `[X, Y]_x = x • [X, Y]`,
forcing `[f X, g X]_x = x (f X(g) - g X(f)) X` by the Leibniz rule. -/
def mulCoordTangent : LieAlgebroid 𝓘(ℝ, ℝ) ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) :=
  rescaledTangent1D (ContMDiffMap.id : C^∞⟮𝓘(ℝ, ℝ), ℝ; ℝ⟯)

@[simp]
theorem mulCoordTangent_anchor_apply (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    mulCoordTangent.anchor x v = x • v :=
  rescaledTangent1D_anchor_apply ContMDiffMap.id x v

@[simp]
theorem mulCoordTangent_bracket_apply
    (X Y : Cₛ^∞⟮𝓘(ℝ, ℝ); ℝ, (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)⟯) (x : ℝ) :
    mulCoordTangent.bracket X Y x = x • mlieBracket 𝓘(ℝ, ℝ) X Y x :=
  rescaledTangent1D_bracket_apply ContMDiffMap.id X Y x

/-- On any vector field `X` of `ℝ`, expanding `mulCoordTangent.bracket (f • X) (g • X)` produces
`(x * (f X(g) - g X(f))) • X`. -/
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

end LieAlgebroid

end TauCeti
