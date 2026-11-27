/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Group
import TauCeti.Algebra.Lie.InvariantForm.RankOne
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Geometry.Lie.Subgroup.Weyl.Faithful
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Rank-one representatives of root reflections

Let `G` be a finite-dimensional real Lie group with Lie algebra `𝔤` of left-invariant derivations,
let `t ⊆ 𝔤` be a subspace and `α ∈ t*`. A **root pair** of `t` is a pair `x, y ∈ 𝔤` that every
`H ∈ t` rotates by the angle `α(H)`,

`⁅H, x⁆ = α(H) y`,  `⁅H, y⁆ = -α(H) x`;

it is **normalized** when its bracket `Z = ⁅x, y⁆` lies in `t` with `α(Z) = 1`. For a positive
definite invariant form, `x, y, Z` then span a copy of `so(3) ≅ 𝔰𝔲(2)`
(`LinearMap.BilinForm.exists_injective_lieHom_soThree_of_lie_eq_smul`). The results below use only
the first equation and the normalization. They give `⁅x, H⁆ = -α(H) y` for `H ∈ t` and
`⁅x, Z⁆ = -y`, so `ad x` kills the hyperplane `ker α` of `t` and rotates the plane spanned by `Z`
and `y`. By the adjoint-exponential formula `Ad (exp X) = exp (ad X)`, the one-parameter subgroup
of `x` acts on `t` by

`Ad (exp (θ x)) H = H - α(H) ((1 - cos θ) Z + sin θ y)`

(`TauCeti.Lie.Ad_lieExp_smul_apply_of_lie_eq_smul`). At `θ = π` this is the **root reflection**

`Ad (exp (π x)) H = H - α(H) α^∨`,  `α^∨ = 2 Z`,

which fixes `ker α` and sends the coroot `α^∨` (with `α(α^∨) = 2`) to its negative
(`TauCeti.Lie.Ad_lieExp_pi_smul_apply_of_lie_eq_smul`). So `n_α = exp (π x)` is a group element
realizing the reflection of the root `α`:

* when `t` is the Lie algebra of a closed connected subgroup `T`, such as a torus, `n_α`
  normalizes `T` (`TauCeti.Lie.lieExp_pi_smul_mem_normalizer_of_lie_eq_smul`), since an element
  normalizes such a subgroup once its adjoint action maps the Lie algebra into itself;
* for every `X ∈ t` with `α(X) = 0`, `ad x` kills `X`, so the whole one-parameter subgroup of `x`,
  and with it `n_α`, lies in the identity component `Z_G(X)⁰` of the adjoint stabilizer of `X`
  (`TauCeti.Lie.lieExp_smul_mem_connectedComponentIn_stabilizer_continuousAdjointRepresentation`).

For a maximal torus `T` of a compact Lie group and a symmetric positive definite invariant form `B`
on `𝔤`, every nonzero real root plane of `T` (`TauCeti.IsRootPlane`) with nonzero root `α` contains
a normalized root pair, a rescaling of `v, J v` for any `v ≠ 0` in the plane
(`TauCeti.IsRootPlane.exists_injective_lieHom_soThree`). Hence every real root `α` of `T` has a
representative `n_α` in the normalizer `N(T)` whose class in the Weyl group `N(T) / T` acts on `𝔱`
as the `B`-orthogonal reflection in `ker α`, that is, as `Module.reflection` along the coroot
`α^∨ ∈ 𝔱`, the element with `α(α^∨) = 2` that is `B`-orthogonal to `ker α`; and `n_α` lies in
`Z_G(X)⁰` whenever `α(X) = 0`
(`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_reflection`). When `G` is also
connected, the Weyl group acts faithfully on `𝔱`, so the reflection is a single element of the
Weyl group (`TauCeti.Lie.IsMaximalTorus.existsUnique_weylAdjointRepresentation_eq_reflection`).
No integration of `𝔰𝔲(2)` to a homomorphism `SU(2) → G` is needed for this: `n_α` is an
exponential.

## Main results

* `TauCeti.Lie.Ad_lieExp_smul_apply_of_lie_eq_smul`: the one-parameter subgroup of a normalized
  root pair acts on `t` by a rotation in the plane of `Z` and `y`.
* `TauCeti.Lie.Ad_lieExp_pi_smul_apply_of_lie_eq_smul`: `exp (π x)` acts on `t` by the root
  reflection `H ↦ H - α(H) (2 Z)`.
* `TauCeti.Lie.lieExp_pi_smul_mem_normalizer_of_lie_eq_smul`: `exp (π x)` normalizes a closed
  connected subgroup with Lie algebra `t`.
* `TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_reflection`: every real root
  of a maximal torus of a compact Lie group has a representative in the normalizer acting on `𝔱`
  by the orthogonal reflection in the root, lying in `Z_G(X)⁰` whenever `α(X) = 0`.
* `TauCeti.Lie.IsMaximalTorus.existsUnique_weylAdjointRepresentation_eq_reflection`: for a
  compact connected Lie group, exactly one element of the Weyl group acts by this reflection.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 2 and Chapter V, § 2 (the subgroups of rank one
  and the reflections of the Weyl group).
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, Proposition 12.5 (the Weyl group
  contains the root reflections).
-/

public section

noncomputable section

open Module (Dual)
open Real
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### The one-parameter subgroup of a normalized root pair -/

section RootPair

variable {t : Submodule ℝ (LeftInvariantDerivation I G)} {α : Dual ℝ t}
  {x y : LeftInvariantDerivation I G}

/-- **The one-parameter subgroup of a normalized root pair rotates `t`.** Let `⁅X, x⁆ = α(X) y`
for every `X ∈ t`, and let `Z = ⁅x, y⁆` lie in `t` with `α(Z) = 1`. Then `exp (θ x)` fixes `ker α`
and acts on `t` by `Ad (exp (θ x)) X = X - α(X) ((1 - cos θ) Z + sin θ y)`. -/
theorem Ad_lieExp_smul_apply_of_lie_eq_smul
    (hx : ∀ X : t, ⁅(X : LeftInvariantDerivation I G), x⁆ = α X • y)
    (hxy : ⁅x, y⁆ ∈ t)
    (hα : α ⟨⁅x, y⁆, hxy⟩ = 1) (θ : ℝ) (X : t) :
    Ad (I := I) (lieExp (I := I) (θ • x)) X =
      (X : LeftInvariantDerivation I G) - α X • ((1 - cos θ) • ⁅x, y⁆ + sin θ • y) := by
  have : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  have := FiniteDimensional.completeSpace ℝ (LeftInvariantDerivation I G)
  -- `ad x` sends `Z = ⁅x, y⁆` to `-y` and `-y` to `-Z`, so `exp (θ x)` rotates `Z` towards `-y`.
  have hxZ : ⁅x, ⁅x, y⁆⁆ = -y := by
    rw [← lie_skew, hx ⟨_, hxy⟩, hα, one_smul]
  have hZ : Ad (I := I) (lieExp (I := I) (θ • x)) ⁅x, y⁆ = cos θ • ⁅x, y⁆ + sin θ • -y := by
    have hAd := LeftInvariantDerivation.Ad_lieExp_apply (I := I) (θ • x) ⁅x, y⁆
    dsimp only at hAd
    rw [hAd]
    refine ContinuousLinearMap.exp_apply_eq_cos_smul_add_sin_smul _ ?_ ?_
    · simp [hxZ]
    · simp only [LinearMap.coe_toContinuousLinearMap', LieAlgebra.ad_apply, lie_neg, smul_lie]
  -- `ad x` kills the component `X - α(X) Z` of `X` in `ker α`.
  have hX₀ : Ad (I := I) (lieExp (I := I) (θ • x)) ((X : LeftInvariantDerivation I G) -
      α X • ⁅x, y⁆) = (X : LeftInvariantDerivation I G) - α X • ⁅x, y⁆ := by
    refine Ad_lieExp_apply_eq_self_of_lie_eq_zero ?_
    have h₀ := hx (X - α X • ⟨_, hxy⟩)
    simp only [map_sub, map_smul, hα, smul_eq_mul, mul_one, sub_self, zero_smul,
      Submodule.coe_sub, Submodule.coe_smul] at h₀
    rw [smul_lie, ← lie_skew, h₀, neg_zero, smul_zero]
  have hdecomp : (X : LeftInvariantDerivation I G) =
      ((X : LeftInvariantDerivation I G) - α X • ⁅x, y⁆) + α X • ⁅x, y⁆ := by abel
  rw [hdecomp, map_add, map_smul, hX₀, hZ]
  module

/-- **`exp (π x)` acts on `t` by the root reflection.** Let `⁅X, x⁆ = α(X) y` for every `X ∈ t`,
and let `⁅x, y⁆` lie in `t` with `α(⁅x, y⁆) = 1`. Then `exp (π x)` acts on `t` by
`X ↦ X - α(X) α^∨`, the reflection fixing `ker α` along the coroot `α^∨ = 2 ⁅x, y⁆`, for which
`α(α^∨) = 2`. -/
theorem Ad_lieExp_pi_smul_apply_of_lie_eq_smul
    (hx : ∀ X : t, ⁅(X : LeftInvariantDerivation I G), x⁆ = α X • y)
    (hxy : ⁅x, y⁆ ∈ t)
    (hα : α ⟨⁅x, y⁆, hxy⟩ = 1) (X : t) :
    Ad (I := I) (lieExp (I := I) (π • x)) X =
      (X : LeftInvariantDerivation I G) - α X • (2 : ℝ) • ⁅x, y⁆ := by
  rw [Ad_lieExp_smul_apply_of_lie_eq_smul hx hxy hα, cos_pi, sin_pi]
  module

/-- **`exp (π x)` normalizes `T`.** Let `T` be a closed preconnected subgroup, such as a torus,
with Lie algebra `𝔱`. If `⁅X, x⁆ = α(X) y` for every `X ∈ 𝔱`, and `⁅x, y⁆` lies in `𝔱`
with `α(⁅x, y⁆) = 1`, then `exp (π x)` lies in the normalizer of `T`. -/
theorem lieExp_pi_smul_mem_normalizer_of_lie_eq_smul {T : Subgroup G}
    (hT : IsClosed (T : Set G)) (hconn : IsPreconnected (T : Set G))
    {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    (hx : ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      ⁅(X : LeftInvariantDerivation I G), x⁆ = α X • y)
    (hxy : ⁅x, y⁆ ∈ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (hα : α ⟨⁅x, y⁆, hxy⟩ = 1) :
    lieExp (I := I) (π • x) ∈ Subgroup.normalizer (T : Set G) := by
  refine (mem_normalizer_iff_forall_Ad_mem (I := I) hT hconn).mpr fun X hX ↦ ?_
  have h := Ad_lieExp_pi_smul_apply_of_lie_eq_smul hx hxy hα ⟨X, hX⟩
  dsimp only at h
  rw [h]
  exact sub_mem hX (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hxy))

end RootPair

/-! ### Root reflections of a maximal torus -/

section MaximalTorus

variable [CompactSpace G]

/-- A nonzero root plane of a maximal torus with nonzero root contains a normalized root pair: the
images `x, y` of `ê₀, ê₁` under its rank-one homomorphism `so(3) → 𝔤`. -/
private theorem IsMaximalTorus.exists_lie_eq_smul_of_isRootPlane {T : Subgroup G}
    (hT : IsMaximalTorus T) {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}
    (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J) (hα : α ≠ 0)
    (hV : V ≠ ⊥) :
    ∃ x y : LeftInvariantDerivation I G,
      (∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        ⁅(X : LeftInvariantDerivation I G), x⁆ = α X • y) ∧
      ∃ hxy : ⁅x, y⁆ ∈ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule, α ⟨_, hxy⟩ = 1 := by
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  -- `⁅w, J w⁆` commutes with `𝔱`, so it lies in `𝔱` by maximality.
  have hwt : ⁅(w : LeftInvariantDerivation I G), (J w : LeftInvariantDerivation I G)⁆ ∈
      (lieSubalgebraOfSubgroup (I := I) T).toSubmodule :=
    lie_mem_of_lie_eq_smul (fun z hz ↦ hT.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero
        fun Y hY ↦ by rw [← lie_skew, hz ⟨Y, hY⟩, neg_zero])
      (h.lie_apply · w) fun X ↦ by rw [h.lie_apply, h.apply_apply, Submodule.coe_neg, smul_neg]
  obtain ⟨f, -, ⟨c, -, hf₀, hf₁⟩, hf₂, hα₁⟩ :=
    h.exists_injective_lieHom_soThree hBs hBp hB hα hw hwt
  have hxy : ⁅f (soThreeEquiv ℝ (Pi.single 0 1)), f (soThreeEquiv ℝ (Pi.single 1 1))⁆ =
      f (soThreeEquiv ℝ (Pi.single 2 1)) := by
    rw [← LieHom.map_lie, lie_soThreeEquiv_single_zero_one]
  refine ⟨_, _, fun X ↦ ?_, hxy ▸ hf₂, (congrArg α (Subtype.ext hxy)).trans hα₁⟩
  rw [hf₀, hf₁, lie_smul, h.lie_apply, smul_comm]

/-- **Every real root of a maximal torus has a rank-one representative of its reflection.** Let
`T` be a maximal torus of a compact Lie group with Lie algebra `𝔱`, let `B` be a symmetric
positive definite invariant form on `𝔤`, and let `V` be a nonzero real root plane of `𝔱` with
nonzero root `α`. Then there are a coroot `α^∨ ∈ 𝔱`, the unique element with `α(α^∨) = 2` that is
`B`-orthogonal to `ker α`, and an element `n` of the normalizer of `T` whose class in the Weyl
group `N(T) / T` acts on `𝔱` by the reflection `X ↦ X - α(X) α^∨`; moreover `n` lies in the
identity component of the adjoint stabilizer `Z_G(X)` of every `X ∈ 𝔱` with `α(X) = 0`. -/
theorem IsMaximalTorus.exists_weylAdjointRepresentation_eq_reflection {T : Subgroup G}
    [IsMulCommutative T] (hT : IsMaximalTorus T)
    {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}
    (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J) (hα : α ≠ 0)
    (hV : V ≠ ⊥) :
    ∃ (c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (hc : α c = 2),
      (∀ X, α X = 0 → B (X : LeftInvariantDerivation I G) c = 0) ∧
      (∀ c', α c' = 2 → (∀ X, α X = 0 → B (X : LeftInvariantDerivation I G) c' = 0) → c' = c) ∧
      ∃ n : Subgroup.normalizer (T : Set G),
        T.weylAdjointRepresentation (I := I) n = (Module.reflection hc).toLinearMap ∧
        ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule, α X = 0 →
          (n : G) ∈ connectedComponentIn
            ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
              (X : LeftInvariantDerivation I G) : Set G) 1 := by
  obtain ⟨x, y, hx, hxy, hα₁⟩ := hT.exists_lie_eq_smul_of_isRootPlane hBs hBp hB h hα hV
  -- The coroot `c = 2 ⁅x, y⁆` and the representative `exp (π x)`.
  obtain ⟨c, hcdef⟩ : ∃ c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      c = (2 : ℝ) • ⟨⁅x, y⁆, hxy⟩ := ⟨_, rfl⟩
  have hc : α c = 2 := by rw [hcdef, map_smul, hα₁, smul_eq_mul, mul_one]
  -- `B(X, ⁅x, y⁆) = α(X) B(y, y)` vanishes on `ker α`.
  have hcB (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (hX : α X = 0) :
      B (X : LeftInvariantDerivation I G) c = 0 := by
    rw [hcdef, Submodule.coe_smul, map_smul, Submodule.coe_mk,
      hB.apply_lie_eq_mul_of_lie_eq_smul hx X, hX, zero_mul, smul_zero]
  have hn := lieExp_pi_smul_mem_normalizer_of_lie_eq_smul hT.isTorus.isClosed
    hT.isTorus.isConnected.isPreconnected hx hxy hα₁
  refine ⟨c, hc, hcB, fun c' hc' hc'B ↦ ?_, ⟨_, hn⟩, ?_, fun X hX ↦ ?_⟩
  · exact LinearMap.BilinForm.eq_of_apply_eq_of_forall_ker_orthogonal hBp.anisotropic
      (hc'.trans hc.symm) hc'B hcB
  · refine LinearMap.ext fun X ↦ Subtype.ext ?_
    rw [LinearEquiv.coe_coe, Module.reflection_apply,
      Subgroup.coe_weylAdjointRepresentation_mk_apply,
      Ad_lieExp_pi_smul_apply_of_lie_eq_smul hx hxy hα₁, hcdef]
    simp
  · -- `ad x` kills `X ∈ ker α`, so the one-parameter subgroup of `x` fixes `X`.
    exact lieExp_smul_mem_connectedComponentIn_stabilizer_continuousAdjointRepresentation (I := I)
      (by rw [← lie_skew, hx X, hX, zero_smul, neg_zero]) π

/-- **The reflection of a real root is a well-defined element of the Weyl group.** Let `T` be a
maximal torus of a compact connected Lie group, `B` a symmetric positive definite invariant form
on `𝔤`, and `V` a nonzero real root plane of `𝔱` with nonzero root `α`. Then exactly one element
of the Weyl group `N(T) / T` acts on `𝔱` by the reflection `X ↦ X - α(X) α^∨` along the coroot
`α^∨`, the element of `𝔱` with `α(α^∨) = 2` that is `B`-orthogonal to `ker α`. -/
theorem IsMaximalTorus.existsUnique_weylAdjointRepresentation_eq_reflection [ConnectedSpace G]
    {T : Subgroup G} [IsMulCommutative T] (hT : IsMaximalTorus T)
    {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}
    (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J) (hα : α ≠ 0)
    (hV : V ≠ ⊥) :
    ∃ (c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (hc : α c = 2),
      (∀ X, α X = 0 → B (X : LeftInvariantDerivation I G) c = 0) ∧
      ∃! w : T.normalizerQuotient,
        T.weylAdjointRepresentation (I := I) w = (Module.reflection hc).toLinearMap := by
  obtain ⟨c, hc, hcB, -, n, hn, -⟩ :=
    hT.exists_weylAdjointRepresentation_eq_reflection hBs hBp hB h hα hV
  -- The Weyl group of a maximal torus of a compact connected Lie group acts faithfully on `𝔱`.
  exact ⟨c, hc, hcB, n, hn, fun w hw ↦ hT.weylAdjointRepresentation_injective I (hw.trans hn.symm)⟩

end MaximalTorus

end TauCeti.Lie
