/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.RankOne
public import TauCeti.Geometry.Lie.Subgroup.Torus.Root.Character
import TauCeti.Geometry.Lie.Adjoint.LieMap

/-!
# Root data under conjugation of a torus

Let `T` be a subgroup of a Lie group `G`, for instance a maximal torus, with Lie algebra
`𝔱 ⊆ 𝔤`, and let `g ∈ G`. The Lie algebra of the conjugate `T' = g T g⁻¹` is `Ad g 𝔱`
(`TauCeti.Lie.lieSubalgebraOfSubgroup_map_conj`), through the linear isomorphism
`e = Ad g : 𝔱 ≃ 𝔱'` (`TauCeti.Lie.lieSubalgebraOfSubgroupMapConjEquiv`). This file shows that
conjugation by `g` carries all the root data of `T` attached to an `Ad g`-invariant form `B` on `𝔤`
to the corresponding data of `T'`:

* **root planes**: a root plane `V` of `𝔱` with root `α` and rotation `J` gives the root plane
  `Ad g V` of `𝔱'` with root `α ∘ e⁻¹` and rotation `Ad g ∘ J ∘ Ad g⁻¹`
  (`TauCeti.IsRootPlane.map_conj`);
* **root characters**: the root character of the conjugate plane is the root character of `V`
  composed with the inverse conjugation, `χ'(g x g⁻¹) = χ(x)`
  (`TauCeti.IsRootPlane.rootCharacter_map_conj_apply`);
* **coroots**: `c ∈ 𝔱` satisfies `α(c) = 2` and is `B`-orthogonal to `ker α` exactly when
  `e c ∈ 𝔱'` has these properties for `α ∘ e⁻¹` (`TauCeti.Lie.coroot_map_conj_iff`);
* **period lattices and integral functionals**: `exp(e X) = 1` exactly when `exp X = 1`
  (`TauCeti.Lie.lieExp_lieSubalgebraOfSubgroupMapConjEquiv_eq_one_iff`), so `e` carries the period
  lattice `(2π)⁻¹ ker(exp)` of `T` onto that of `T'`, and
  `ℓ ∈ 𝔱*` takes values in `2πℤ` on the kernel of the exponential exactly when `ℓ ∘ e⁻¹` does
  (`TauCeti.Lie.exists_apply_eq_intCast_mul_map_conj_iff`);
* **rank-one homomorphisms**: if `φ : SU(2) → G` is a rank-one homomorphism of the root `α` and
  the root vector `v`, in the sense of `TauCeti.IsRootPlane.exists_contMDiffMonoidMorphism`, then
  `x ↦ g φ(x) g⁻¹` is a rank-one homomorphism of the root `α ∘ e⁻¹` and the root vector `Ad g v`
  (`TauCeti.Lie.exists_contMDiffMonoidMorphism_map_conj`). Its differential is
  `Ad g ∘ dφ` (`lieMap_eq_Ad_comp_of_apply_eq`), so it sends `diag(i, -i)` to the conjugate coroot.

An invariant form obtained by averaging over a compact group, as in
`TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant`, is `Ad g`-invariant for every `g`. Nothing here
uses compactness, maximality or connectedness of `T` beyond what the root character itself needs.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 1 and Chapter V, §§ 1–2.
* B. Conrad and C. Landesman, *Compact Lie Groups*, Appendix R (roots, coroots and their
  integrality).
-/

public section

noncomputable section

open Module (Dual)
open Real
open scoped ContDiff Manifold

/-! ### Root planes, root characters, coroots and integrality -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} {T : Subgroup G} {g : G}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti.IsRootPlane

open Lie

variable {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
  {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}

/-- **Root planes of a conjugate subgroup.** Let `B` be invariant under `Ad g`. If `V` is a root
plane of the Lie algebra `𝔱` of `T` with root `α` and rotation `J`, then `Ad g V` is a root plane of
the Lie algebra `Ad g 𝔱` of `g T g⁻¹`, with root `α ∘ Ad g⁻¹` and rotation `Ad g ∘ J ∘ Ad g⁻¹`. -/
theorem map_conj (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
    (hB : ∀ X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y) :
    IsRootPlane B
      (lieSubalgebraOfSubgroup (I := I) (T.map (MulAut.conj g).toMonoidHom)).toSubmodule
      (α ∘ₗ (lieSubalgebraOfSubgroupMapConjEquiv T g).symm.toLinearMap)
      (V.map ((Ad (I := I) g).toLinearEquiv : LeftInvariantDerivation I G →ₗ[ℝ] _))
      (((Ad (I := I) g).toLinearEquiv.submoduleMap V).conj J) :=
  h.map (Ad (I := I) g) hB _ (coe_lieSubalgebraOfSubgroupMapConjEquiv_apply T g) _
    (LinearEquiv.submoduleMap_apply _ V)

variable [IsMulCommutative T]
  (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
  (hB : ∀ X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y)
  (hT : IsClosed (T : Set G)) (hconn : IsPreconnected (T : Set G)) (hV : V ≠ ⊥)
  (hT' : IsClosed (T.map (MulAut.conj g).toMonoidHom : Set G))
  (hconn' : IsPreconnected (T.map (MulAut.conj g).toMonoidHom : Set G))
  (hV' : V.map ((Ad (I := I) g).toLinearEquiv :
    LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I G) ≠ ⊥)

/-- **Root characters of a conjugate torus.** The root character of the conjugate root plane
`Ad g V` of `g T g⁻¹` takes the value `χ(x)` at `g x g⁻¹`, where `χ` is the root character of `V`:
conjugation by `g` carries `χ` to the root character of `Ad g V`. -/
theorem rootCharacter_map_conj_apply (x : T) :
    (h.map_conj hB).rootCharacter hT' hconn' hV'
        ⟨g * x * g⁻¹, Subgroup.mem_map.2 ⟨x, x.property, rfl⟩⟩ =
      h.rootCharacter hT hconn hV x := by
  -- Both sides are determined by their values on exponentials.
  have key := (h.eq_rootCharacter_iff hT hconn hV
    (ψ := fun x ↦ (h.map_conj hB).rootCharacter hT' hconn' hV'
      ⟨g * x * g⁻¹, Subgroup.mem_map.2 ⟨x, x.property, rfl⟩⟩)).2 fun X ↦ by
    rw [(h.map_conj hB).rootCharacter_apply_of_lieExp_eq hT' hconn' hV' _
      (lieSubalgebraOfSubgroupMapConjEquiv T g X), LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rw [coe_lieSubalgebraOfSubgroupMapConjEquiv_apply, ← conj_lieExp]
  exact congrFun key x

end TauCeti.IsRootPlane

namespace TauCeti.Lie

/-- **Torus conjugation transports coroots.** Let `B` be invariant under `Ad g`, let `α` be a
functional on the Lie algebra `𝔱` of `T`, and let `e = Ad g : 𝔱 ≃ Ad g 𝔱` be the isomorphism onto
the Lie algebra of `g T g⁻¹`. Then `e c` satisfies the coroot conditions for `α ∘ e⁻¹`, value `2`
and `B`-orthogonality to the kernel, exactly when `c` satisfies them for `α`. -/
theorem coroot_map_conj_iff (hB : ∀ X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y)
    (α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (c : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    ((α ∘ₗ (lieSubalgebraOfSubgroupMapConjEquiv T g).symm.toLinearMap)
          (lieSubalgebraOfSubgroupMapConjEquiv T g c) = 2 ∧
        ∀ X : (lieSubalgebraOfSubgroup (I := I) (T.map (MulAut.conj g).toMonoidHom)).toSubmodule,
          (α ∘ₗ (lieSubalgebraOfSubgroupMapConjEquiv T g).symm.toLinearMap) X = 0 →
            B (X : LeftInvariantDerivation I G) (lieSubalgebraOfSubgroupMapConjEquiv T g c) = 0) ↔
      α c = 2 ∧ ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        α X = 0 → B (X : LeftInvariantDerivation I G) c = 0 := by
  set e := lieSubalgebraOfSubgroupMapConjEquiv (I := I) T g
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  refine and_congr_right fun _ ↦ ⟨fun hc X hX ↦ ?_, fun hc X hX ↦ ?_⟩
  · have hX' := hc (e X) (by rwa [LinearEquiv.symm_apply_apply])
    rwa [coe_lieSubalgebraOfSubgroupMapConjEquiv_apply,
      coe_lieSubalgebraOfSubgroupMapConjEquiv_apply, hB] at hX'
  · obtain ⟨X, rfl⟩ := e.surjective X
    rw [LinearEquiv.symm_apply_apply] at hX
    rw [coe_lieSubalgebraOfSubgroupMapConjEquiv_apply,
      coe_lieSubalgebraOfSubgroupMapConjEquiv_apply, hB]
    exact hc X hX

/-- **Torus conjugation transports the kernel of the exponential.** For `X` in the Lie algebra of
`T`, `exp(Ad g X) = 1` exactly when `exp X = 1`. So `Ad g` carries the period lattice
`(2π)⁻¹ ker(exp)` of `T` onto that of `g T g⁻¹`, and integral cocharacters to integral
cocharacters. -/
theorem lieExp_lieSubalgebraOfSubgroupMapConjEquiv_eq_one_iff
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    lieExp (I := I) (lieSubalgebraOfSubgroupMapConjEquiv T g X : LeftInvariantDerivation I G) = 1 ↔
      lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 := by
  rw [coe_lieSubalgebraOfSubgroupMapConjEquiv_apply, ← conj_lieExp, conj_eq_one_iff]

/-- **Torus conjugation transports integral functionals.** A functional `ℓ` on the Lie algebra of
`T` takes values in `2πℤ` on the kernel of the exponential exactly when `ℓ ∘ Ad g⁻¹` does on the
Lie algebra of `g T g⁻¹`. -/
theorem exists_apply_eq_intCast_mul_map_conj_iff
    (ℓ : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    (∀ X : (lieSubalgebraOfSubgroup (I := I) (T.map (MulAut.conj g).toMonoidHom)).toSubmodule,
        lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 →
          ∃ n : ℤ, ℓ ((lieSubalgebraOfSubgroupMapConjEquiv T g).symm X) = n * (2 * π)) ↔
      ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 → ∃ n : ℤ, ℓ X = n * (2 * π) := by
  set e := lieSubalgebraOfSubgroupMapConjEquiv (I := I) T g
  refine ⟨fun hℓ X hX ↦ ?_, fun hℓ X hX ↦ ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply] using
      hℓ (e X) ((lieExp_lieSubalgebraOfSubgroupMapConjEquiv_eq_one_iff X).2 hX)
  · obtain ⟨X, rfl⟩ := e.surjective X
    rw [LinearEquiv.symm_apply_apply]
    exact hℓ X ((lieExp_lieSubalgebraOfSubgroupMapConjEquiv_eq_one_iff X).1 hX)

end TauCeti.Lie

end General

/-! ### Rank-one homomorphisms -/

section RankOne

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)} {T : Subgroup G} {g : G}
  {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}
  {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.LieGroup`.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal

open scoped Matrix.Norms.Operator

/-- **Torus conjugation transports rank-one homomorphisms.** Let `B` be invariant under `Ad g`,
and let `φ : SU(2) → G` be a rank-one homomorphism of the root `α` of the Lie algebra `𝔱` of `T`
and the vector `v` of the plane `V` with rotation `J`, in the sense of
`TauCeti.IsRootPlane.exists_contMDiffMonoidMorphism`: its differential is injective, sends
`diag(i, -i)` to the coroot of `α` and the real root vectors of `𝔰𝔲(2)` to the same positive
multiple of `J v` and `v`. Then `ψ(x) = g φ(x) g⁻¹` is a rank-one homomorphism, in the same sense,
of the root `α ∘ Ad g⁻¹` of the Lie algebra of `g T g⁻¹` and the vector `Ad g v` of the plane
`Ad g V` with rotation `Ad g ∘ J ∘ Ad g⁻¹`. -/
theorem exists_contMDiffMonoidMorphism_map_conj
    (hB : ∀ X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y) {v : V}
    {φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
      (GLSpecialUnitary (Fin 2) ℂ) G}
    (hφ : Function.Injective (lieMap φ) ∧
      (∃ h : lieMap φ SU2.torusGenerator ∈ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        α ⟨_, h⟩ = 2 ∧ ∀ H : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
          α H = 0 → B H (lieMap φ SU2.torusGenerator) = 0) ∧
      ∃ c : ℝ, 0 < c ∧
        lieMap φ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 0 1))) =
          c • (J v : LeftInvariantDerivation I G) ∧
        lieMap φ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 1 1))) =
          c • (v : LeftInvariantDerivation I G)) :
    ∃ ψ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
        (GLSpecialUnitary (Fin 2) ℂ) G,
      (∀ x, ψ x = g * φ x * g⁻¹) ∧ Function.Injective (lieMap ψ) ∧
      (∃ h : lieMap ψ SU2.torusGenerator ∈
          (lieSubalgebraOfSubgroup (I := I) (T.map (MulAut.conj g).toMonoidHom)).toSubmodule,
        (α ∘ₗ (lieSubalgebraOfSubgroupMapConjEquiv T g).symm.toLinearMap) ⟨_, h⟩ = 2 ∧
        ∀ H : (lieSubalgebraOfSubgroup (I := I) (T.map (MulAut.conj g).toMonoidHom)).toSubmodule,
          (α ∘ₗ (lieSubalgebraOfSubgroupMapConjEquiv T g).symm.toLinearMap) H = 0 →
            B H (lieMap ψ SU2.torusGenerator) = 0) ∧
      ∃ c : ℝ, 0 < c ∧
        lieMap ψ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 0 1))) =
          c • ((((Ad (I := I) g).toLinearEquiv.submoduleMap V).conj J
            ((Ad (I := I) g).toLinearEquiv.submoduleMap V v)) : LeftInvariantDerivation I G) ∧
        lieMap ψ (SU2.nativeLieEquiv.symm (suTwoEquiv (Pi.single 1 1))) =
          c • ((Ad (I := I) g).toLinearEquiv.submoduleMap V v : LeftInvariantDerivation I G) := by
  obtain ⟨hinj, ⟨hφt, hφα, hφB⟩, c, hc, hφ₀, hφ₁⟩ := hφ
  set e := lieSubalgebraOfSubgroupMapConjEquiv (I := I) T g
  let ψ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
      (GLSpecialUnitary (Fin 2) ℂ) G :=
    { (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom with
      contMDiff_toFun := (contMDiff_const.mul φ.contMDiff_toFun).mul contMDiff_const }
  have hψ (x) : ψ x = g * φ x * g⁻¹ := (rfl)
  -- The differential of `ψ` is `Ad g ∘ dφ`.
  have hL (X) : lieMap ψ X = Ad (I := I) g (lieMap φ X) := by
    rw [lieMap_eq_Ad_comp_of_apply_eq φ ψ g hψ, LieHom.comp_apply, LieEquiv.coe_toLieHom]
  have hψt : lieMap ψ SU2.torusGenerator = e ⟨_, hφt⟩ := by
    rw [hL, coe_lieSubalgebraOfSubgroupMapConjEquiv_apply]
  refine ⟨ψ, hψ,
    fun X Y hXY ↦ hinj (EquivLike.injective (Ad (I := I) g) (by simpa only [hL] using hXY)),
    ⟨hψt ▸ (e ⟨_, hφt⟩).property, ?_, fun H hH ↦ ?_⟩, c, hc, ?_, ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hφα]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hψt
  · obtain ⟨H, rfl⟩ := e.surjective H
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hH
    rw [hL, coe_lieSubalgebraOfSubgroupMapConjEquiv_apply, hB]
    exact hφB H hH
  · simp only [hL, hφ₀, map_smul, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.submoduleMap_apply, LieEquiv.coe_toLinearEquiv]
  · simp only [hL, hφ₁, map_smul, LinearEquiv.submoduleMap_apply, LieEquiv.coe_toLinearEquiv]

end TauCeti.Lie

end RankOne
