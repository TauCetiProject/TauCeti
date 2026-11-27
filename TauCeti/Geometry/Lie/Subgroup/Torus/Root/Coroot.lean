/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character
import TauCeti.Geometry.Lie.RankOne
import TauCeti.Geometry.Lie.Subgroup.Torus.Root.Plane
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Integrality of coroots and the Cartan integers of torus characters

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱 ⊆ 𝔤`, and let `B` be a
symmetric positive definite invariant form on `𝔤`. For a nonzero real root plane of `𝔱` with
nonzero root `α`, the **coroot** `α^∨ ∈ 𝔱` is the element with `α(α^∨) = 2` that is `B`-orthogonal
to `ker α`, so `α^∨ = 2 a / B(a, a)` for the `B`-dual `a ∈ 𝔱` of `α`. This file proves the
integral normalization of these data, with the circle period `2π` of `Circle.exp t = e^{it}`. Call
`ℓ ∈ 𝔱*` *integral* when `ℓ(X) ∈ 2πℤ` whenever `exp X = 1`, and call `X ∈ 𝔱` an *integral
cocharacter* when `exp(2π X) = 1`, that is, when `X` lies in the period lattice
`Λ_ℤ = (2π)⁻¹ ker(exp)`.

* **The coroot is an integral cocharacter**: `exp_G(2π α^∨) = 1`
  (`TauCeti.Lie.IsMaximalTorus.lieExp_two_pi_smul_eq_one_of_isRootPlane`). The rank-one
  homomorphism `φ_α : SU(2) → G` of the root has differential sending `diag(i, -i)` to `α^∨`
  (`TauCeti.IsRootPlane.exists_contMDiffMonoidMorphism`), so it sends `diag(e^{is}, e^{-is})` to
  `exp_G(s α^∨)` (`ContMDiffMonoidMorphism.map_torusExp`), and `diag(e^{2πi}, e^{-2πi}) = 1`
  (`ContMDiffMonoidMorphism.lieExp_two_pi_smul_lieMap_torusGenerator`).
* **The differential of a character is integral.** If `χ : T → S¹` satisfies
  `χ (exp X) = e^{i ℓ(X)}` for `X ∈ 𝔱`, that is `dχ = i ℓ`, then `ℓ` is integral
  (`TauCeti.Lie.exists_apply_eq_intCast_mul_of_apply_lieExp_eq_circleExp`). The roots are
  integral in this sense (`TauCeti.IsRootPlane.exists_apply_eq_intCast_mul_of_lieExp_eq_one`).
* **Integral functionals pair integrally with integral cocharacters**
  (`TauCeti.Lie.exists_apply_eq_intCast_of_lieExp_two_pi_smul_eq_one`). So the pairing `ℓ(α^∨)`
  of the real differential of every character of `T` with every coroot is an integer. In terms of
  `B` this is the integrality of the Cartan integer `2 B(a, l) / B(a, a)`, where `l` is the
  `B`-dual of `ℓ` (`TauCeti.Lie.IsMaximalTorus.exists_int_two_mul_apply_eq_mul_of_isRootPlane`).
  For the root `β` of another root plane, `β(α^∨)` is the usual Cartan integer.
* **The root reflection preserves both lattices.** The reflection `s_α X = X - α(X) α^∨` of `𝔱`,
  by which the Weyl group element of the root acts
  (`TauCeti.Lie.IsMaximalTorus.exists_weylAdjointRepresentation_eq_reflection`), maps the period
  lattice to itself (`TauCeti.Lie.lieExp_two_pi_smul_reflection_eq_one`), and its transpose
  `ℓ ↦ ℓ ∘ s_α = ℓ - ℓ(α^∨) α` maps integral functionals to integral functionals
  (`TauCeti.Lie.exists_apply_reflection_eq_intCast_mul_of_lieExp_eq_one`). Both statements are
  proved for any integral `α` and integral cocharacter `c` with `α(c) = 2`, which the root and its
  coroot are.

## Main results

* `TauCeti.Lie.IsMaximalTorus.lieExp_two_pi_smul_eq_one_of_isRootPlane`: `exp_G(2π α^∨) = 1`.
* `TauCeti.Lie.exists_apply_eq_intCast_mul_of_apply_lieExp_eq_circleExp`: the differential of a
  character is integral.
* `TauCeti.Lie.exists_apply_eq_intCast_of_lieExp_two_pi_smul_eq_one`: an integral functional
  takes integer values on integral cocharacters.
* `TauCeti.Lie.IsMaximalTorus.exists_int_two_mul_apply_eq_mul_of_isRootPlane`: the Cartan integer
  `2 B(a, l) / B(a, a)` of an integral functional is an integer.
* `TauCeti.Lie.lieExp_two_pi_smul_reflection_eq_one`,
  `TauCeti.Lie.exists_apply_reflection_eq_intCast_mul_of_lieExp_eq_one`: the reflection along an
  integral cocharacter preserves the period lattice and the integral functionals.

## References

* B. Conrad and C. Landesman, *Compact Lie Groups*, Appendix R, Proposition R.2.1 and its proof
  (integrality of coroots and of the pairing of characters with coroots).
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 2 (the subgroups `SU(2)` attached to the roots).
-/

public section

noncomputable section

open Module (Dual)
open Real
open scoped ContDiff Manifold

namespace TauCeti.Lie

/-! ### Integral functionals and integral cocharacters -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {t : Submodule ℝ (LeftInvariantDerivation I G)} {α ℓ : Dual ℝ t} {c : t}

/-- **A reflection along an integral cocharacter preserves the integral functionals.** Let
`α, ℓ ∈ t*` take values in `2πℤ` on the kernel of the exponential, and let `c ∈ t` satisfy
`α(c) = 2` and `exp(2π c) = 1`. Then `ℓ ∘ s = ℓ - ℓ(c) α`, the transform of `ℓ` under the
reflection `s X = X - α(X) c`, also takes values in `2πℤ` on the kernel of the exponential. For a
root `α` of a maximal torus and its coroot `c = α^∨`
(`IsMaximalTorus.lieExp_two_pi_smul_eq_one_of_isRootPlane`), `s` is the root reflection. -/
theorem exists_apply_reflection_eq_intCast_mul_of_lieExp_eq_one
    (hα : ∀ X : t, lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 →
      ∃ n : ℤ, α X = n * (2 * π))
    (hℓ : ∀ X : t, lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 →
      ∃ n : ℤ, ℓ X = n * (2 * π))
    (hc : α c = 2) (hc₁ : lieExp (I := I) ((2 * π) • (c : LeftInvariantDerivation I G)) = 1)
    {X : t} (hX : lieExp (I := I) (X : LeftInvariantDerivation I G) = 1) :
    ∃ n : ℤ, ℓ (Module.reflection hc X) = n * (2 * π) := by
  obtain ⟨m, hm⟩ := exists_apply_eq_intCast_of_lieExp_two_pi_smul_eq_one hℓ hc₁
  obtain ⟨k, hk⟩ := hℓ X hX
  obtain ⟨j, hj⟩ := hα X hX
  refine ⟨k - j * m, ?_⟩
  rw [Module.reflection_apply, map_sub, map_smul, smul_eq_mul, hk, hj, hm]
  push_cast
  ring

/-- **A reflection along an integral cocharacter preserves the period lattice.** Let `T` be a
commutative subgroup with Lie algebra `𝔱`, let `α ∈ 𝔱*` take values in `2πℤ` on the kernel of the
exponential, and let `c ∈ 𝔱` satisfy `α(c) = 2` and `exp(2π c) = 1`. If `X ∈ 𝔱` satisfies
`exp(2π X) = 1`, then so does its reflection `s X = X - α(X) c`. For a root `α` of a maximal torus
and its coroot `c = α^∨` (`IsMaximalTorus.lieExp_two_pi_smul_eq_one_of_isRootPlane`), `s` is the
root reflection. -/
theorem lieExp_two_pi_smul_reflection_eq_one {T : Subgroup G} [IsMulCommutative T]
    {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    {c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    (hα : ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 → ∃ n : ℤ, α X = n * (2 * π))
    (hc : α c = 2) (hc₁ : lieExp (I := I) ((2 * π) • (c : LeftInvariantDerivation I G)) = 1)
    {X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    (hX : lieExp (I := I) ((2 * π) • (X : LeftInvariantDerivation I G)) = 1) :
    lieExp (I := I) ((2 * π) • (Module.reflection hc X : LeftInvariantDerivation I G)) = 1 := by
  -- `α(X)` is an integer `n`, since `α` is integral and `2π X` lies in the kernel of `exp`.
  obtain ⟨n, hαX⟩ := exists_apply_eq_intCast_of_lieExp_two_pi_smul_eq_one hα hX
  -- So `2π s X = 2π X - n (2π c)` is a difference of commuting elements of the kernel.
  have hcomm : ⁅(2 * π) • (X : LeftInvariantDerivation I G),
      -((n : ℝ) • (2 * π) • (c : LeftInvariantDerivation I G))⁆ = 0 :=
    lie_eq_zero_of_mem_lieSubalgebraOfSubgroup (K := T)
      (Submodule.smul_mem _ _ X.property)
      (Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ c.property)))
  have hpow : lieExp (I := I) ((n : ℝ) • (2 * π) • (c : LeftInvariantDerivation I G)) = 1 := by
    rw [Int.cast_smul_eq_zsmul, lieExp_zsmul, hc₁, one_zpow]
  rw [Module.reflection_apply, Submodule.coe_sub, Submodule.coe_smul, hαX, smul_sub,
    smul_comm (2 * π), sub_eq_add_neg, lieExp_add_of_lie_eq_zero hcomm, lieExp_neg, hX, hpow,
    inv_one, one_mul]

end Integral

/-! ### Coroots of a maximal torus -/

section Coroot

-- The rank-one homomorphisms `SU(2) → G` are constructed for models in `Type`.
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [CompactSpace G]
  {T : Subgroup G} {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
  {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
  {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The coroot is an integral cocharacter.** Let `T` be a maximal torus of a compact Lie group
with Lie algebra `𝔱`, let `B` be a symmetric positive definite invariant form on `𝔤`, and let `V` be
a nonzero real root plane of `𝔱` with nonzero root `α`. The coroot `α^∨ ∈ 𝔱`, the element with
`α(α^∨) = 2` that is `B`-orthogonal to `ker α`, satisfies `exp_G(2π α^∨) = 1`. -/
theorem IsMaximalTorus.lieExp_two_pi_smul_eq_one_of_isRootPlane (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J) (hα : α ≠ 0)
    (hV : V ≠ ⊥) {c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule} (hc : α c = 2)
    (hcB : ∀ X, α X = 0 → B (X : LeftInvariantDerivation I G) c = 0) :
    lieExp (I := I) ((2 * π) • (c : LeftInvariantDerivation I G)) = 1 := by
  have := I.secondCountableTopology
  have : SecondCountableTopology G := ChartedSpace.secondCountable_of_sigmaCompact H G
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- The differential of the rank-one homomorphism `φ_α` sends `diag(i, -i)` to the coroot.
  obtain ⟨φ, -, ⟨hφt, hφα, hφB⟩, -⟩ :=
    h.exists_contMDiffMonoidMorphism hBs hBp hB hα hv (hT.lie_mem_of_isRootPlane h v)
  obtain rfl : (⟨_, hφt⟩ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) = c :=
    LinearMap.BilinForm.eq_of_apply_eq_of_forall_ker_orthogonal hBp.anisotropic
      (hφα.trans hc.symm) hφB hcB
  exact φ.lieExp_two_pi_smul_lieMap_torusGenerator

/-- **The Cartan integer of an integral functional.** In the setting of
`IsMaximalTorus.lieExp_two_pi_smul_eq_one_of_isRootPlane`, let `a, l ∈ 𝔱` be the `B`-duals of the
root `α` and of a functional `ℓ ∈ 𝔱*` taking values in `2πℤ` on the kernel of the exponential, for
instance the real differential of a character of `T`. Then `2 B(a, l) / B(a, a)`, the pairing
`ℓ(α^∨)`, is an integer. -/
theorem IsMaximalTorus.exists_int_two_mul_apply_eq_mul_of_isRootPlane (hT : IsMaximalTorus T)
    (hBs : B.IsSymm) (hBp : B.toQuadraticMap.PosDef)
    (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J) (hα : α ≠ 0)
    (hV : V ≠ ⊥) {ℓ : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    (hℓ : ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 → ∃ n : ℤ, ℓ X = n * (2 * π))
    {a l : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
    (ha : ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      B (a : LeftInvariantDerivation I G) X = α X)
    (hl : ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      B (l : LeftInvariantDerivation I G) X = ℓ X) :
    ∃ n : ℤ, 2 * B (a : LeftInvariantDerivation I G) l = n * B a a := by
  have haa : B (a : LeftInvariantDerivation I G) a ≠ 0 := by
    refine fun h0 ↦ hα (LinearMap.ext fun X ↦ ?_)
    rw [← ha, Submodule.coe_eq_zero.mp (hBp.anisotropic _ h0), Submodule.coe_zero,
      LinearMap.map_zero₂, LinearMap.zero_apply]
  have hBsymm (X Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
      B (X : LeftInvariantDerivation I G) Y = B (Y : LeftInvariantDerivation I G) X :=
    hBs.eq _ _
  -- The coroot is `α^∨ = (2 / B(a, a)) a`, an integral cocharacter.
  have hc : α ((2 / B (a : LeftInvariantDerivation I G) a) • a) = 2 := by
    rw [map_smul, ← ha, smul_eq_mul, div_mul_cancel₀ _ haa]
  obtain ⟨n, hn⟩ := exists_apply_eq_intCast_of_lieExp_two_pi_smul_eq_one hℓ
    (hT.lieExp_two_pi_smul_eq_one_of_isRootPlane hBs hBp hB h hα hV hc
      fun X hX ↦ by rw [Submodule.coe_smul, map_smul, hBsymm X a, ha X, hX, smul_zero])
  refine ⟨n, ?_⟩
  rw [map_smul, ← hl, smul_eq_mul, hBsymm l a] at hn
  field_simp at hn
  linear_combination hn

end Coroot

end TauCeti.Lie
