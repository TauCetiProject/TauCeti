/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus.OrbitType
public import TauCeti.Geometry.Lie.Subgroup.Torus.Root.Reflection
public import TauCeti.Geometry.Lie.Subgroup.Weyl.OrbitSpace
import TauCeti.Geometry.Lie.Subgroup.Weyl.Finite
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# Closed Weyl chambers parametrize the adjoint and coadjoint orbits

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱 ⊆ 𝔤`, Weyl group
`W = N(T) / T` acting on `𝔱` (`Subgroup.weylAdjointRepresentation`), and let `B` be an invariant
inner product on `𝔤`. Decompose `𝔤 = 𝔱 ⊕ E₁ ⊕ ⋯ ⊕ E_r` into nonzero real root planes with nonzero
roots `α₁, …, α_r ∈ 𝔱*` (`TauCeti.IsRootPlaneDecomposition`). The **closed Weyl chamber** of an
element `X₀ ∈ 𝔱` (`TauCeti.sameSideChamber`) is

`C = {X ∈ 𝔱 | 0 ≤ α_i(X₀) α_i(X) for every i}`,

the elements lying, for every root, on the same closed side of its kernel as `X₀`. When `X₀` is
regular, no root vanishing at it, `C` is the closure of the open Weyl chamber containing `X₀`.
This file proves that for a compact connected group and a regular `X₀`, every Weyl orbit in `𝔱`,
hence every adjoint orbit in `𝔤` and every coadjoint orbit in `𝔤*`, meets `C` in exactly one
point, and that `C` is homeomorphic to the adjoint and coadjoint orbit spaces. Existence holds for
every `X₀`; uniqueness fails without regularity, since `X₀ = 0` gives `C = 𝔱`.

* **Existence**
  (`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_mem_sameSideChamber`).
  Among the finitely many points `w X`, `w ∈ W`, take one maximizing `B(w X, X₀)`. Each root
  reflection `s_α`, which lies in `W`
  (`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_reflection`),
  changes this pairing by `-α(w X) α(X₀) B(α^∨, α^∨) / 2`, so at the maximum no root separates
  `w X` from `X₀`. This needs neither connectedness nor regularity of `X₀`.
* **The open chambers.** For a compact connected group the stabilizer of a regular element is `T`
  (`TauCeti.IsRootPlaneDecomposition.stabilizer_continuousAdjointRepresentation_eq_iff`), so `W`
  preserves the regular elements
  (`TauCeti.Lie.IsMaximalTorus.apply_weylAdjointRepresentation_ne_zero`). An element of `W`
  carrying one point of the open chamber of a regular `X₀` into it therefore carries the whole
  convex open chamber into itself, and so fixes the barycentre of an orbit of the cyclic group it
  generates. That barycentre is regular, and `W` acts freely on regular elements
  (`TauCeti.Lie.IsMaximalTorus.eq_one_of_weylAdjointRepresentation_apply_eq_self`), so the element
  is the identity
  (`TauCeti.Lie.IsMaximalTorus.eq_one_of_forall_pos_mul_apply_weylAdjointRepresentation`).
* **Uniqueness on the closed chamber**
  (`TauCeti.Lie.IsMaximalTorus.eq_of_weylAdjointRepresentation_apply_eq`). Let `G` be compact
  connected and `X₀` regular. If `w X = Y` with `X, Y ∈ C`, choose `v ∈ W` fixing `Y` and
  maximizing `B(v w X₀, X₀)`. The reflections in the roots vanishing at `Y` fix `Y`, so at the
  maximum these roots are positive at `v w X₀`. Then for small `s > 0` the element `v w` carries
  `X + s X₀` to `Y + s v w X₀`, both in the open chamber, so `v w = 1` and `X = v w X = v Y = Y`.
  This is a direct argument for the closed chamber, with walls, not only for the open one.

The chamber is cut out by the roots, not by the reflecting hyperplanes of the finite group `W`
acting on `𝔱` as in `Representation.chamber`, and not through a root pairing as in
`TauCeti.weylChamber`: identifying either of those with the root data of `T` requires knowing that
every reflection in `W` is a root reflection, which the argument here does not use. Only the root
reflections, the finiteness of `W` and the stabilizers of regular elements enter.

Connectedness is needed for uniqueness: for `G = O(2)` and `T = SO(2)` there are no roots, so
`C = 𝔱`, while `W` has order two and acts on `𝔱 ≅ ℝ` by `-1`.

For a compact connected group and a regular `X₀`, restricting the proper map `𝔱 → 𝔤 / Ad G`
(`TauCeti.Lie.IsMaximalTorus.isProperMap_orbitRel_mk_coe`) to the closed set `C` gives a continuous
proper bijection, so a homeomorphism `C ≃ₜ 𝔤 / Ad G`
(`TauCeti.Lie.IsMaximalTorus.sameSideChamberOrbitHomeomorph`). Through the homeomorphisms of
`TauCeti.Geometry.Lie.Subgroup.Weyl.OrbitSpace`, `C` is also homeomorphic to the coadjoint orbit
space `𝔤* / Ad* G`, placing `X ∈ C` at the coadjoint orbit of its covector for an invariant form
(`TauCeti.Lie.IsMaximalTorus.sameSideChamberCoadjointOrbitHomeomorph`).

## Main definitions

* `TauCeti.sameSideChamber α X₀`: the closed chamber of a family of linear forms containing `X₀`.
* `TauCeti.Lie.IsMaximalTorus.sameSideChamberOrbitHomeomorph`: `C ≃ₜ 𝔤 / Ad G`.
* `TauCeti.Lie.IsMaximalTorus.sameSideChamberCoadjointOrbitHomeomorph`: `C ≃ₜ 𝔤* / Ad* G`.

## Main results

* `TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_mem_sameSideChamber`: every Weyl
  orbit meets the closed chamber.
* `TauCeti.Lie.IsMaximalTorus.apply_weylAdjointRepresentation_ne_zero`: for a compact connected
  group, the Weyl group preserves the regular elements.
* `TauCeti.Lie.IsMaximalTorus.eq_one_of_weylAdjointRepresentation_apply_eq_self`: for a compact
  connected group, the Weyl group acts freely on the regular elements.
* `TauCeti.Lie.IsMaximalTorus.eq_one_of_forall_pos_mul_apply_weylAdjointRepresentation`: the Weyl
  group acts freely on the open chambers.
* `TauCeti.Lie.IsMaximalTorus.eq_of_weylAdjointRepresentation_apply_eq`: for a compact connected
  group and a regular `X₀`, two Weyl-related points of the closed chamber are equal.
* `TauCeti.Lie.IsMaximalTorus.existsUnique_mem_sameSideChamber_Ad`: for a compact connected group
  and a regular `X₀`, every adjoint orbit meets the closed chamber in exactly one point.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 2 (Weyl chambers and the Weyl group).
* M. M. Alexandrino and R. G. Bettiol, *Lie Groups and Geometric Aspects of Isometric Actions*,
  Springer, 2015, Theorem 4.31.
-/

public section

noncomputable section

open Module (Dual)
open Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Closed Weyl chambers -/

section Chamber

variable {ι M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The **same-side chamber** of a family `α` of linear forms containing `X₀`: the vectors `X`
lying, for every `i`, on the same closed side of `ker (α i)` as `X₀`, that is,
`0 ≤ α i X₀ * α i X`. For the roots of a compact Lie group and a regular `X₀`, this is the closed
Weyl chamber containing `X₀`, the closure of the open Weyl chamber containing `X₀`. -/
def sameSideChamber (α : ι → Dual ℝ M) (X₀ : M) : Set M :=
  {X | ∀ i, 0 ≤ α i X₀ * α i X}

@[simp]
theorem mem_sameSideChamber {α : ι → Dual ℝ M} {X₀ X : M} :
    X ∈ sameSideChamber α X₀ ↔ ∀ i, 0 ≤ α i X₀ * α i X :=
  Iff.rfl

theorem self_mem_sameSideChamber (α : ι → Dual ℝ M) (X₀ : M) :
    X₀ ∈ sameSideChamber α X₀ :=
  fun _ ↦ mul_self_nonneg _

/-- A same-side chamber is convex, as an intersection of closed half-spaces. -/
theorem convex_sameSideChamber (α : ι → Dual ℝ M) (X₀ : M) :
    Convex ℝ (sameSideChamber α X₀) := by
  simp only [sameSideChamber, Set.ofPred_forall]
  exact convex_iInter fun i ↦ convex_halfSpace_ge (α i X₀ • α i).isLinear 0

/-- A same-side chamber of a finite-dimensional space is closed. -/
theorem isClosed_sameSideChamber [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul ℝ M] [T2Space M] [FiniteDimensional ℝ M] (α : ι → Dual ℝ M) (X₀ : M) :
    IsClosed (sameSideChamber α X₀) := by
  simp only [sameSideChamber, Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const
    (continuous_const.mul (LinearMap.continuous_of_finiteDimensional (α i)))

end Chamber

namespace Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [CompactSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {T : Subgroup G} [IsMulCommutative T]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} {ι : Type*}
  {α : ι → Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
  {V : ι → Submodule ℝ (LeftInvariantDerivation I G)} {J : (i : ι) → Module.End ℝ (V i)}

/-! ### Root reflections and the pairing with a fixed element -/

/-- **A root reflection moves the pairing with `X₀` by the product of the root values.** For a
nonzero root plane with nonzero root `a` of a maximal torus, some element `r` of the Weyl group
fixes the kernel of `a`, and changes `B(Z, X₀)` to `B(r Z, X₀) = B(Z, X₀) - k a(Z) a(X₀)` for a
constant `k > 0`: it is the reflection along the coroot `a^∨`, and `k = B(a^∨, a^∨) / 2`. -/
private theorem IsMaximalTorus.exists_weylAdjointRepresentation_apply_sub (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    {a : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    {V' : Submodule ℝ (LeftInvariantDerivation I G)} {J' : Module.End ℝ V'}
    (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule a V' J') (ha : a ≠ 0)
    (hV : V' ≠ ⊥) :
    ∃ (k : ℝ) (r : T.normalizerQuotient), 0 < k ∧
      (∀ Z, a Z = 0 → T.weylAdjointRepresentation (I := I) r Z = Z) ∧
      ∀ Z X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        B (T.weylAdjointRepresentation (I := I) r Z : LeftInvariantDerivation I G) X₀ =
          B (Z : LeftInvariantDerivation I G) X₀ - k * (a Z * a X₀) := by
  obtain ⟨c, hc, hcB, -, n, hn, -⟩ :=
    hT.exists_weylAdjointRepresentation_eq_reflection hBs hBp hB h ha hV
  have hrefl (Z : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
      T.weylAdjointRepresentation (I := I) n Z = Z - a Z • c := by
    rw [hn, LinearEquiv.coe_coe, Module.reflection_apply]
  -- `c ≠ 0` since `a c = 2`, so `B(c, c) > 0`.
  have hc0 : (c : LeftInvariantDerivation I G) ≠ 0 := fun h0 ↦ by
    have : c = 0 := Subtype.ext h0
    rw [this, map_zero] at hc
    norm_num at hc
  have hcc : 0 < B (c : LeftInvariantDerivation I G) c := by
    simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hBp _ hc0
  -- `B(c, X₀) = a(X₀) B(c, c) / 2`, since `X₀ - (a(X₀) / 2) c` lies in the kernel of `a`.
  have hcX (X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
      B (c : LeftInvariantDerivation I G) X₀ =
        a X₀ * B (c : LeftInvariantDerivation I G) c / 2 := by
    have h0 := hcB (X₀ - (a X₀ / 2) • c) (by rw [map_sub, map_smul, hc, smul_eq_mul]; ring)
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, map_sub, map_smul,
      LinearMap.sub_apply, hBs.eq, LinearMap.smul_apply, smul_eq_mul] at h0
    linear_combination h0
  refine ⟨B (c : LeftInvariantDerivation I G) c / 2, n, by positivity,
    fun Z hZ ↦ by rw [hrefl, hZ, zero_smul, sub_zero], fun Z X₀ ↦ ?_⟩
  rw [hrefl]
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, hcX X₀, smul_eq_mul, sub_right_inj]
  ring

/-! ### Existence of a representative in the closed chamber -/

/-- **Every Weyl orbit meets the closed Weyl chamber.** Let `T` be a maximal torus of a compact
Lie group, `B` a symmetric positive definite invariant form on `𝔤`, and `α_i` the roots of nonzero
root planes of `𝔱`. Then for every `X₀, X ∈ 𝔱` some element `w` of the Weyl group carries `X` into
the closed chamber of `X₀`: no root separates `w X` from `X₀`. -/
theorem IsMaximalTorus.exists_weylAdjointRepresentation_mem_sameSideChamber
    (hT : IsMaximalTorus T) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (h : ∀ i, IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule (α i) (V i) (J i))
    (hV : ∀ i, V i ≠ ⊥) (X₀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    ∃ w : T.normalizerQuotient,
      T.weylAdjointRepresentation (I := I) w X ∈ sameSideChamber α X₀ := by
  have := hT.finite_normalizerQuotient I
  -- Maximize the pairing `B(w X, X₀)` over the finite Weyl group.
  obtain ⟨w, hw⟩ := Finite.exists_max fun w : T.normalizerQuotient ↦
    B (T.weylAdjointRepresentation (I := I) w X : LeftInvariantDerivation I G) X₀
  refine ⟨w, fun i ↦ not_lt.1 fun hneg ↦ ?_⟩
  -- A root separating `w X` from `X₀` is nonzero, and its reflection increases the pairing.
  have hα : α i ≠ 0 := fun h0 ↦ by simp [h0] at hneg
  obtain ⟨k, r, hk, -, hr⟩ :=
    hT.exists_weylAdjointRepresentation_apply_sub hBs hBp hB (h i) hα (hV i)
  have := hw (r * w)
  rw [map_mul, mul_apply_eq_comp, hr] at this
  nlinarith [mul_pos hk (neg_pos.2 hneg)]

/-! ### The open chambers of a compact connected group -/

section Connected

variable [ConnectedSpace G] [Finite ι]

/-- **The Weyl group preserves regular elements.** For a compact connected group, an element of
`𝔱` at which no root vanishes is carried by the Weyl group to another such element. -/
theorem IsMaximalTorus.apply_weylAdjointRepresentation_ne_zero (hT : IsMaximalTorus T)
    (hB : B.lieInvariant (LeftInvariantDerivation I G)) (hsep : B.SeparatingLeft)
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hV : ∀ i, V i ≠ ⊥) (w : T.normalizerQuotient)
    {X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hX : ∀ i, α i X ≠ 0) (i : ι) :
    α i (T.weylAdjointRepresentation (I := I) w X) ≠ 0 := by
  have hα : ∀ i, α i ≠ 0 := fun i h0 ↦ hX i (by simp [h0])
  revert i
  rw [← hD.stabilizer_continuousAdjointRepresentation_eq_iff hT.isTorus rfl hB hsep hα hV] at hX ⊢
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  -- The stabilizer of `Ad_n X` is the conjugate by `n` of the stabilizer `T` of `X`.
  have := Representation.stabilizer_conj
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation n X
  simp only [ContRepresentation.toRepresentation_apply, continuousAdjointRepresentation_apply,
    hX] at this
  rw [Subgroup.coe_weylAdjointRepresentation_mk_apply, this]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.1 n.property

/-- **The Weyl group acts freely on the regular elements.** For a compact connected group, an
element of the Weyl group fixing an element of `𝔱` at which no root vanishes is the identity: a
representative fixes that element, so lies in its stabilizer `T`. -/
theorem IsMaximalTorus.eq_one_of_weylAdjointRepresentation_apply_eq_self (hT : IsMaximalTorus T)
    (hB : B.lieInvariant (LeftInvariantDerivation I G)) (hsep : B.SeparatingLeft)
    (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hV : ∀ i, V i ≠ ⊥) {w : T.normalizerQuotient}
    {X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hX : ∀ i, α i X ≠ 0)
    (hw : T.weylAdjointRepresentation (I := I) w X = X) : w = 1 := by
  have hα : ∀ i, α i ≠ 0 := fun i h0 ↦ hX i (by simp [h0])
  rw [← hD.stabilizer_continuousAdjointRepresentation_eq_iff hT.isTorus rfl hB hsep hα hV] at hX
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hn : (n : G) ∈
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (X : LeftInvariantDerivation I G) := by
    rw [mem_stabilizer_continuousAdjointRepresentation_iff,
      ← Subgroup.coe_weylAdjointRepresentation_mk_apply]
    exact congrArg Subtype.val hw
  rw [hX] at hn
  exact (QuotientGroup.eq_one_iff n).2 (Subgroup.mem_subgroupOf.2 hn)

variable (hT : IsMaximalTorus T) (hB : B.lieInvariant (LeftInvariantDerivation I G))
  (hsep : B.SeparatingLeft)
  (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
  (hV : ∀ i, V i ≠ ⊥)
  {X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}

include hT hB hsep hD hV

/-- **An element of the Weyl group meeting the open chamber preserves it.** If `w X₁` lies in the
open chamber `{X | 0 < α_i(X₀) α_i(X) for all i}` together with `X₁`, so does `w Y` for every `Y`
in it. Otherwise some root takes values of opposite signs at `w X₁` and `w Y`, hence vanishes at the
image of a positive combination of `X₁` and `Y`, which is regular. -/
private theorem forall_pos_mul_apply_weylAdjointRepresentation (w : T.normalizerQuotient)
    {X₁ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hX₁ : ∀ i, 0 < α i X₀ * α i X₁)
    (hw : ∀ i, 0 < α i X₀ * α i (T.weylAdjointRepresentation (I := I) w X₁))
    {Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hY : ∀ i, 0 < α i X₀ * α i Y) (i : ι) :
    0 < α i X₀ * α i (T.weylAdjointRepresentation (I := I) w Y) := by
  by_contra! hle
  set ρ := T.weylAdjointRepresentation (I := I)
  set a := α i X₀ * α i (ρ w X₁)
  set b := α i X₀ * α i (ρ w Y)
  -- The positive combination `P = (-b) X₁ + a Y` lies in the open chamber.
  have hP (j : ι) : 0 < α j X₀ * α j ((-b) • X₁ + a • Y) := by
    have := mul_nonneg (neg_nonneg.2 hle) (hX₁ j).le
    have := mul_pos (hw i) (hY j)
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    linarith
  have hreg := hT.apply_weylAdjointRepresentation_ne_zero hB hsep hD hV w
    (X := (-b) • X₁ + a • Y) (fun j h0 ↦ (hP j).ne' (by rw [h0, mul_zero])) i
  -- But `α_i(X₀) α_i(w P) = -b a + a b = 0`.
  have h0 : α i X₀ * α i (ρ w ((-b) • X₁ + a • Y)) = 0 := by
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  exact hreg ((mul_eq_zero.1 h0).resolve_left fun h ↦ by simpa [h] using hX₁ i)

/-- **The Weyl group acts freely on the open chambers.** For a compact connected group and a
regular `X₀`, an element of the Weyl group carrying some point of the open chamber of `X₀` into
that chamber is the identity. -/
theorem IsMaximalTorus.eq_one_of_forall_pos_mul_apply_weylAdjointRepresentation
    (w : T.normalizerQuotient) {X₁ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    (hX₁ : ∀ i, 0 < α i X₀ * α i X₁)
    (hw : ∀ i, 0 < α i X₀ * α i (T.weylAdjointRepresentation (I := I) w X₁)) : w = 1 := by
  have := hT.finite_normalizerQuotient I
  set ρ := T.weylAdjointRepresentation (I := I)
  -- Every power of `w` preserves the open chamber.
  have hpow (k : ℕ) {Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
      (hY : ∀ i, 0 < α i X₀ * α i Y) : ∀ i, 0 < α i X₀ * α i (ρ (w ^ k) Y) := by
    induction k generalizing Y with
    | zero => simpa using hY
    | succ k ih =>
      intro i
      rw [pow_succ', map_mul, mul_apply_eq_comp]
      exact forall_pos_mul_apply_weylAdjointRepresentation hT hB hsep hD hV w hX₁ hw (ih hY) i
  -- The barycentre `Z = ∑_{k < m} w^k X₁`, `m` the order of `w`, lies in the chamber and is fixed
  -- by `w`.
  set m := orderOf w
  have hm : 0 < m := orderOf_pos w
  set Z := ∑ k ∈ Finset.range m, ρ (w ^ k) X₁
  have hZ (i : ι) : 0 < α i X₀ * α i Z := by
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_pos (fun k _ ↦ hpow k hX₁ i) (Finset.nonempty_range_iff.2 hm.ne')
  have hwZ : ρ w Z = Z := by
    have hs := (Finset.sum_range_succ' (fun k ↦ ρ (w ^ k) X₁) m).symm.trans
      (Finset.sum_range_succ (fun k ↦ ρ (w ^ k) X₁) m)
    rw [pow_orderOf_eq_one, pow_zero, add_left_inj] at hs
    rw [map_sum]
    exact (Finset.sum_congr rfl fun k _ ↦ by rw [pow_succ', map_mul, mul_apply_eq_comp]).trans hs
  -- `w` fixes the regular element `Z`.
  exact hT.eq_one_of_weylAdjointRepresentation_apply_eq_self hB hsep hD hV
    (fun i h0 ↦ by simpa [h0] using hZ i) hwZ

end Connected

/-! ### Uniqueness of the chamber representative of an orbit -/

section Orbit

variable [ConnectedSpace G] [Finite ι]
  (hT : IsMaximalTorus T) (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
  (hB : B.lieInvariant (LeftInvariantDerivation I G))
  (hD : IsRootPlaneDecomposition B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
  (hV : ∀ i, V i ≠ ⊥)
  {X₀ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hX₀ : ∀ i, α i X₀ ≠ 0)

include hT hBs hBp hB hD hV hX₀

/-- **Two Weyl-related points of a closed Weyl chamber are equal.** Let `T` be a maximal torus of a
compact connected Lie group, `B` a symmetric positive definite invariant form on `𝔤`, and
`𝔤 = 𝔱 ⊕ E₁ ⊕ ⋯ ⊕ E_r` a decomposition into nonzero root planes with roots `α_i`. For a
regular `X₀ ∈ 𝔱`, if an element of the Weyl group carries a point `X` of the closed chamber of `X₀`
to a point `Y` of that chamber, then `X = Y`. -/
theorem IsMaximalTorus.eq_of_weylAdjointRepresentation_apply_eq
    {X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hX : X ∈ sameSideChamber α X₀)
    (hY : Y ∈ sameSideChamber α X₀) {w : T.normalizerQuotient}
    (hw : T.weylAdjointRepresentation (I := I) w X = Y) : X = Y := by
  have hsep : B.SeparatingLeft := LinearMap.BilinForm.separatingLeft_of_anisotropic hBp.anisotropic
  have hα : ∀ i, α i ≠ 0 := fun i h0 ↦ hX₀ i (by simp [h0])
  have := hT.finite_normalizerQuotient I
  set ρ := T.weylAdjointRepresentation (I := I)
  have : Nonempty {v : T.normalizerQuotient // ρ v Y = Y} := ⟨⟨1, by simp⟩⟩
  -- Among the Weyl elements fixing `Y`, take `v` maximizing `B(v w X₀, X₀)`, and put `U = v w X₀`.
  obtain ⟨⟨v, hvY⟩, hv⟩ := Finite.exists_max fun v : {v : T.normalizerQuotient // ρ v Y = Y} ↦
    B (ρ v (ρ w X₀) : LeftInvariantDerivation I G) X₀
  set U := ρ v (ρ w X₀)
  have hU (i : ι) : α i U ≠ 0 :=
    hT.apply_weylAdjointRepresentation_ne_zero hB hsep hD hV v
      (hT.apply_weylAdjointRepresentation_ne_zero hB hsep hD hV w hX₀) i
  -- The roots vanishing at `Y` are positive at `U`: their reflections fix `Y`, and would otherwise
  -- increase the pairing.
  have hUpos (i : ι) (hi : α i Y = 0) : 0 < α i X₀ * α i U := by
    refine lt_of_le_of_ne (not_lt.1 fun hneg ↦ ?_) (mul_ne_zero (hX₀ i) (hU i)).symm
    obtain ⟨k, r, hk, hrfix, hr⟩ :=
      hT.exists_weylAdjointRepresentation_apply_sub hBs hBp hB (hD.isRootPlane i) (hα i) (hV i)
    have := hv ⟨r * v, by rw [map_mul, mul_apply_eq_comp, hvY, hrfix Y hi]⟩
    simp only [map_mul, mul_apply_eq_comp] at this
    rw [hr] at this
    nlinarith [mul_pos hk (neg_pos.2 hneg)]
  -- For small `s > 0`, `Y + s U` lies in the open chamber.
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, 0 < α i X₀ * α i (Y + s • U) := by
    refine eventually_all.2 fun i ↦ ?_
    simp only [map_add, map_smul, smul_eq_mul, mul_add]
    rcases eq_or_ne (α i Y) 0 with hi | hi
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hi, mul_zero, zero_add, mul_left_comm]
      exact mul_pos hs (hUpos i hi)
    · have hpos : 0 < α i X₀ * α i Y := lt_of_le_of_ne (hY i) (mul_ne_zero (hX₀ i) hi).symm
      have ht : Tendsto (fun s : ℝ ↦ α i X₀ * α i Y + α i X₀ * (s * α i U)) (𝓝 0)
          (𝓝 (α i X₀ * α i Y)) := by
        have hc : Continuous fun s : ℝ ↦ α i X₀ * α i Y + α i X₀ * (s * α i U) := by fun_prop
        simpa using hc.tendsto 0
      exact (ht.eventually (lt_mem_nhds hpos)).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hsY, hs⟩ := (hev.and self_mem_nhdsWithin).exists
  -- `X + s X₀` lies in the open chamber and `v w` carries it to `Y + s U`, so `v w = 1`.
  have hXs (i : ι) : 0 < α i X₀ * α i (X + s • X₀) := by
    rw [map_add, map_smul, smul_eq_mul, mul_add, mul_left_comm]
    exact add_pos_of_nonneg_of_pos (hX i) (mul_pos hs (mul_self_pos.2 (hX₀ i)))
  have himg : ρ (v * w) (X + s • X₀) = Y + s • U := by
    rw [map_mul, mul_apply_eq_comp, map_add, map_smul, hw, map_add, map_smul, hvY]
  have h1 := hT.eq_one_of_forall_pos_mul_apply_weylAdjointRepresentation hB hsep hD hV (v * w)
    hXs (himg ▸ hsY)
  calc X = ρ (v * w) X := by rw [h1, map_one, one_apply_eq_self]
    _ = Y := by rw [map_mul, mul_apply_eq_comp, hw, hvY]

/-- **Every Weyl orbit meets a closed Weyl chamber in exactly one point.** For a maximal torus of a
compact connected Lie group, a root-plane decomposition with nonzero planes for a
symmetric positive definite invariant form, and a regular `X₀`, each `X ∈ 𝔱` is Weyl-related to
exactly one point of the closed chamber of `X₀`. -/
theorem IsMaximalTorus.existsUnique_mem_sameSideChamber_orbitRel
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    ∃! Y, Y ∈ sameSideChamber α X₀ ∧ (T.weylAdjointRepresentation (I := I)).orbitRel Y X := by
  obtain ⟨w, hw⟩ :=
    hT.exists_weylAdjointRepresentation_mem_sameSideChamber hBs hBp hB hD.isRootPlane hV X₀ X
  refine ⟨_, ⟨hw, (Representation.orbitRel_apply _).2 ⟨w, rfl⟩⟩, fun Y ⟨hY, hYX⟩ ↦ ?_⟩
  obtain ⟨u, hu⟩ := (Representation.orbitRel_apply _).1 hYX
  refine (hT.eq_of_weylAdjointRepresentation_apply_eq hBs hBp hB hD hV hX₀ hw hY
    (w := u * w⁻¹) ?_).symm
  simp [← hu, ← mul_apply_eq_comp, ← map_mul]

/-- **Every adjoint orbit meets a closed Weyl chamber in exactly one point.** For a maximal torus
`T` of a compact connected Lie group, a root-plane decomposition of `𝔤` over `𝔱` with nonzero
planes for a symmetric positive definite invariant form, and a regular `X₀ ∈ 𝔱`, each `Z ∈ 𝔤`
is carried by the adjoint action to exactly one point of the closed chamber of `X₀`. -/
theorem IsMaximalTorus.existsUnique_mem_sameSideChamber_Ad (Z : LeftInvariantDerivation I G) :
    ∃! Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      Y ∈ sameSideChamber α X₀ ∧ ∃ g : G, Ad (I := I) g Z = Y := by
  obtain ⟨g, hg⟩ := hT.exists_Ad_mem_lieSubalgebraOfSubgroup Z
  obtain ⟨Y, ⟨hY, hYX⟩, huniq⟩ :=
    hT.existsUnique_mem_sameSideChamber_orbitRel hBs hBp hB hD hV hX₀ ⟨_, hg⟩
  -- Points of `𝔱` are adjoint-related exactly when they are Weyl-related.
  have hrel (Y' : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
      (∃ g' : G, Ad (I := I) g' Z = Y') ↔
        (T.weylAdjointRepresentation (I := I)).orbitRel Y' ⟨_, hg⟩ := by
    have hZ :
        Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
          (Ad (I := I) g Z) = Quotient.mk _ Z :=
      (Representation.orbitRel_mk_eq_mk_iff _).2 ⟨g, by simp⟩
    rw [hT.orbitRel_weylAdjointRepresentation_iff, ← Quotient.eq]
    simp [hZ, Representation.orbitRel_mk_eq_mk_iff]
  exact ⟨Y, ⟨hY, (hrel Y).2 hYX⟩, fun Y' ⟨hY', hY'Z⟩ ↦ huniq Y' ⟨hY', (hrel Y').1 hY'Z⟩⟩

/-! ### The chamber as the orbit space -/

/-- The map from the closed Weyl chamber to the adjoint orbit space is bijective. -/
private theorem bijective_sameSideChamber_orbitRel_mk :
    Function.Bijective fun X : sameSideChamber α X₀ ↦
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        ((X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) : LeftInvariantDerivation I G) := by
  have huniq := hT.existsUnique_mem_sameSideChamber_Ad hBs hBp hB hD hV hX₀
  refine ⟨fun X Y hXY ↦ Subtype.ext ?_, fun q ↦ ?_⟩
  · obtain ⟨g, hg⟩ := (Representation.orbitRel_mk_eq_mk_iff _).1 hXY
    simp only [ContRepresentation.toRepresentation_apply, continuousAdjointRepresentation_apply]
      at hg
    exact (huniq (X : LeftInvariantDerivation I G)).unique ⟨X.property, 1, by simp⟩
      ⟨Y.property, g⁻¹, by rw [← hg, Ad_inv, LieEquiv.symm_apply_apply]⟩
  · induction q using Quotient.inductionOn' with | h Z => ?_
    obtain ⟨Y, ⟨hY, g, hg⟩, -⟩ := huniq Z
    refine ⟨⟨Y, hY⟩, (Representation.orbitRel_mk_eq_mk_iff _).2 ⟨g, ?_⟩⟩
    simp only [ContRepresentation.toRepresentation_apply, continuousAdjointRepresentation_apply, hg]

/-- **A closed Weyl chamber is the adjoint orbit space.** For a maximal torus `T` of a compact
connected Lie group, a root-plane decomposition of `𝔤` over `𝔱` with nonzero planes for
a symmetric positive definite invariant form, and a regular `X₀ ∈ 𝔱`, sending a point of the closed
chamber of `X₀` to its adjoint orbit is a homeomorphism onto `𝔤 / Ad G`. -/
def IsMaximalTorus.sameSideChamberOrbitHomeomorph :
    sameSideChamber α X₀ ≃ₜ
      Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel :=
  have hp : IsProperMap fun X : sameSideChamber α X₀ ↦
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        ((X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) : LeftInvariantDerivation I G) :=
    hT.isProperMap_orbitRel_mk_coe.comp
      (isClosed_sameSideChamber α X₀).isClosedEmbedding_subtypeVal.isProperMap
  (Equiv.ofBijective _ (bijective_sameSideChamber_orbitRel_mk hT hBs hBp hB hD hV hX₀))
    |>.toHomeomorphOfContinuousClosed hp.continuous hp.isClosedMap

/-- The homeomorphism `IsMaximalTorus.sameSideChamberOrbitHomeomorph` sends a point of the
chamber to its adjoint orbit. -/
@[simp]
theorem IsMaximalTorus.sameSideChamberOrbitHomeomorph_apply (X : sameSideChamber α X₀) :
    hT.sameSideChamberOrbitHomeomorph hBs hBp hB hD hV hX₀ X =
      Quotient.mk (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel
        ((X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) : LeftInvariantDerivation I G) :=
  (rfl)

/-- Evaluation at the identity, the Lie algebra isomorphism from left-invariant derivations to the
tangent Lie algebra `𝔤` on which the coadjoint representation is defined. -/
local notation "evalOne" => leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
  (BoundarylessManifold.isInteriorPoint (x := (1 : G)))

variable {B' : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  (hB' : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B')
  (hB's : LinearMap.SeparatingLeft B')
  [TopologicalSpace (Module.Dual ℝ (GroupLieAlgebra I G))]
  [IsModuleTopology ℝ (Module.Dual ℝ (GroupLieAlgebra I G))]

/-- **A closed Weyl chamber is the coadjoint orbit space.** For a maximal torus `T` of a compact
connected Lie group, a root-plane decomposition of `𝔤` over `𝔱` with nonzero planes for
a symmetric positive definite invariant form, a regular `X₀ ∈ 𝔱`, and an invariant form `B'` with
trivial left radical on the tangent Lie algebra, sending a point `X` of the closed chamber of `X₀`
to the coadjoint orbit of its covector `B' (X, ·)` is a homeomorphism onto `𝔤* / Ad* G`, for the
module topology on `𝔤*`. -/
def IsMaximalTorus.sameSideChamberCoadjointOrbitHomeomorph :
    sameSideChamber α X₀ ≃ₜ Quotient (coadjointRepresentation ℝ I G).orbitRel :=
  ((hT.sameSideChamberOrbitHomeomorph hBs hBp hB hD hV hX₀).trans
    hT.weylOrbitHomeomorph.symm).trans (hT.weylCoadjointOrbitHomeomorph hB' hB's)

/-- The homeomorphism `IsMaximalTorus.sameSideChamberCoadjointOrbitHomeomorph` sends a point `X`
of the chamber to the coadjoint orbit of `B' (X, ·)`. -/
@[simp]
theorem IsMaximalTorus.sameSideChamberCoadjointOrbitHomeomorph_apply
    (X : sameSideChamber α X₀) :
    hT.sameSideChamberCoadjointOrbitHomeomorph hBs hBp hB hD hV hX₀ hB' hB's X =
      Quotient.mk (coadjointRepresentation ℝ I G).orbitRel
        (B' (evalOne ((X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
          LeftInvariantDerivation I G))) := by
  have : hT.weylOrbitHomeomorph.symm
      (hT.sameSideChamberOrbitHomeomorph hBs hBp hB hD hV hX₀ X) = Quotient.mk _ X.val := by
    rw [Homeomorph.symm_apply_eq, weylOrbitHomeomorph_mk, sameSideChamberOrbitHomeomorph_apply]
  rw [sameSideChamberCoadjointOrbitHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    this, weylCoadjointOrbitHomeomorph_mk]

end Orbit

end Lie

end TauCeti
