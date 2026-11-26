/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.Geometry.Lie.Subgroup.Torus
public import Mathlib.Analysis.Complex.Circle
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic

/-!
# Root characters of a torus

Let `G` be a finite-dimensional real Lie group with Lie algebra `𝔤` of left-invariant derivations,
and let `V ⊆ 𝔤` be a real root plane of a subspace `t ⊆ 𝔤` (`TauCeti.IsRootPlane`): a plane with a
complex structure `J` on which every `H ∈ t` acts by `ad H = α(H) J`. Since
`Ad (exp H) = exp (ad H)`, the exponential of `H` acts on the plane by the rotation through the
angle `α(H)`:

`Ad (exp H) v = cos (α H) • v + sin (α H) • J v`

(`TauCeti.IsRootPlane.Ad_lieExp_apply`).

Now let `T` be a closed connected commutative subgroup of `G`, for instance a torus, with Lie
algebra `t = Lie(T)`, and let `V ≠ 0`. Every element of `T` is an exponential of an element of `t`,
so `T` acts on `V` by rotations, and these rotations define a continuous character
`χ_α : T → S¹`, the **root character** of the plane
(`TauCeti.IsRootPlane.rootCharacter`), with

`Ad g v = Re (χ_α g) • v + Im (χ_α g) • J v`  and  `χ_α (exp H) = e^{i α(H)}`

(`TauCeti.IsRootPlane.Ad_apply`, `TauCeti.IsRootPlane.rootCharacter_lieExp`). The second identity
is the normalization `dχ_α = i α` of the root character against its root. It
characterizes `χ_α` among all maps `T → S¹` (`TauCeti.IsRootPlane.eq_rootCharacter_iff`). Its
kernel is the subgroup of `T` acting trivially on the plane
(`TauCeti.IsRootPlane.rootCharacter_eq_one_iff`).

Well-definedness of `χ_α` is the integrality of the root on the kernel of the exponential: if
`exp H = 1` for `H ∈ t`, then `α(H) ∈ 2πℤ`, since the rotation through `α(H)` is the identity on
the nonzero plane `V` (`TauCeti.IsRootPlane.exists_apply_eq_intCast_mul_of_lieExp_eq_one`). The
plane must be nonzero: on the zero plane every functional `α` satisfies the root-plane equations.

For a maximal torus of a compact Lie group, this applies to each plane of the real root
decomposition `TauCeti.Lie.IsMaximalTorus.exists_isInternal_isRootPlane`.

## Main definitions

* `TauCeti.IsRootPlane.rootCharacter`: the root character `χ_α : T → S¹` of a nonzero root plane.

## Main results

* `TauCeti.IsRootPlane.Ad_lieExp_apply`: `exp H` rotates a root plane through the angle `α(H)`.
* `TauCeti.IsRootPlane.circleExp_eq_of_lieExp_eq`,
  `TauCeti.IsRootPlane.exists_apply_eq_intCast_mul_of_lieExp_eq_one`: on a nonzero root plane,
  `e^{i α(H)}` depends only on `exp H`, and `α` takes values in `2πℤ` on the kernel of `exp`.
* `TauCeti.IsRootPlane.rootCharacter_apply_of_lieExp_eq`,
  `TauCeti.IsRootPlane.rootCharacter_lieExp`: `χ_α (exp H) = e^{i α(H)}`.
* `TauCeti.IsRootPlane.Ad_apply`, `TauCeti.IsRootPlane.Ad_apply_mem`: `T` acts on the root plane
  by the rotations `χ_α`, and in particular preserves it.
* `TauCeti.IsRootPlane.eq_rootCharacter_iff`: `χ_α` is the only map with `χ_α (exp H) = e^{i α(H)}`.
* `TauCeti.IsRootPlane.rootCharacter_eq_one_iff`: the kernel of `χ_α` is the subgroup acting
  trivially on the plane.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 1 and Chapter V, § 1.
-/

public section

noncomputable section

open Module (Dual)
open Real
open scoped ContDiff Manifold

namespace TauCeti.IsRootPlane

open Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
  {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### The exponential on a root plane -/

section Exponential

variable {t : Submodule ℝ (LeftInvariantDerivation I G)} {α : Dual ℝ t}

/-- **The exponential rotates a root plane.** If every `H ∈ t` acts on the plane `V` by
`ad H = α(H) J`, then `Ad (exp H) v = cos (α H) • v + sin (α H) • J v`. -/
theorem Ad_lieExp_apply (h : IsRootPlane B t α V J) (X : t) (v : V) :
    Ad (I := I) (lieExp (I := I) (X : LeftInvariantDerivation I G)) v =
      cos (α X) • (v : LeftInvariantDerivation I G) +
        sin (α X) • (J v : LeftInvariantDerivation I G) := by
  have : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  have := FiniteDimensional.completeSpace ℝ (LeftInvariantDerivation I G)
  have hAd := LeftInvariantDerivation.Ad_lieExp_apply (I := I) (X : LeftInvariantDerivation I G) v
  dsimp only at hAd
  rw [hAd]
  refine ContinuousLinearMap.exp_apply_eq_cos_smul_add_sin_smul _ ?_ ?_
  · simp [h.lie_apply]
  · simp [h.lie_apply, h.apply_apply]

omit [FiniteDimensional ℝ E] [T2Space G] in
/-- The real-linear map `z ↦ re z • v + im z • J v` from `ℂ` to the Lie algebra, which reads a
rotation of a root plane in the basis `v, J v`. -/
private def reImMap (J : Module.End ℝ V) (v : V) : ℂ →ₗ[ℝ] LeftInvariantDerivation I G :=
  Complex.reLm.smulRight (v : LeftInvariantDerivation I G) +
    Complex.imLm.smulRight (J v : LeftInvariantDerivation I G)

omit [FiniteDimensional ℝ E] [T2Space G] in
private theorem reImMap_apply (J : Module.End ℝ V) (v : V) (z : ℂ) :
    reImMap J v z =
      z.re • (v : LeftInvariantDerivation I G) + z.im • (J v : LeftInvariantDerivation I G) :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] in
/-- For a nonzero `v` in a root plane, `z ↦ re z • v + im z • J v` is injective, since `v` and
`J v` are linearly independent. -/
private theorem injective_reImMap (h : IsRootPlane B t α V J) {v : V} (hv : v ≠ 0) :
    Function.Injective (reImMap J v) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  have := LinearIndependent.pair_iff.1 (h.linearIndependent_pair hv) z.re z.im
    (Subtype.ext (by simpa [reImMap_apply] using hz))
  exact Complex.ext this.1 this.2

/-- The exponential of `X` acts on a root plane by `e^{i α(X)}`, read in the basis `v, J v`. -/
private theorem Ad_lieExp_apply_eq_circleExp (h : IsRootPlane B t α V J) (X : t) (v : V) :
    Ad (I := I) (lieExp (I := I) (X : LeftInvariantDerivation I G)) v =
      reImMap J v (Circle.exp (α X)) := by
  rw [reImMap_apply, h.Ad_lieExp_apply, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- **On a nonzero root plane, `e^{i α(X)}` depends only on `exp X`.** -/
theorem circleExp_eq_of_lieExp_eq (h : IsRootPlane B t α V J) (hV : V ≠ ⊥) {X Y : t}
    (hXY : lieExp (I := I) (X : LeftInvariantDerivation I G) = lieExp (I := I) (Y : _)) :
    Circle.exp (α X) = Circle.exp (α Y) := by
  have := Submodule.nontrivial_iff_ne_bot.2 hV
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hX := h.Ad_lieExp_apply_eq_circleExp X v
  rw [hXY, h.Ad_lieExp_apply_eq_circleExp] at hX
  exact Circle.ext (h.injective_reImMap hv hX.symm)

/-- **Roots are integral on the kernel of the exponential.** On a nonzero root plane, if
`exp X = 1` then `α(X) / (2π)` is an integer. -/
theorem exists_apply_eq_intCast_mul_of_lieExp_eq_one (h : IsRootPlane B t α V J) (hV : V ≠ ⊥)
    {X : t} (hX : lieExp (I := I) (X : LeftInvariantDerivation I G) = 1) :
    ∃ n : ℤ, α X = n * (2 * π) := by
  rw [← Circle.exp_eq_one,
    h.circleExp_eq_of_lieExp_eq hV (Y := 0) (by rw [hX, ZeroMemClass.coe_zero, lieExp_zero]),
    map_zero, Circle.exp_zero]

end Exponential

/-! ### The root character of a closed connected commutative subgroup -/

section Character

variable {T : Subgroup G} [IsMulCommutative T]
  {α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule}

omit [IsMulCommutative T] in
/-- Every element of a closed connected commutative subgroup is the exponential of an element of
its Lie algebra. -/
private theorem exists_lieExp_eq [IsMulCommutative T] (hT : IsClosed (T : Set G))
    (hconn : IsPreconnected (T : Set G)) (g : T) :
    ∃ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
      lieExp (I := I) (X : LeftInvariantDerivation I G) = g := by
  have hg : (g : G) ∈ lieExp (I := I) ''
      (lieSubalgebraOfSubgroup (I := I) T : Set (LeftInvariantDerivation I G)) := by
    rw [image_lieExp_lieSubalgebraOfSubgroup_of_isPreconnected hT hconn]
    exact g.property
  obtain ⟨X, hX, hXg⟩ := hg
  exact ⟨⟨X, hX⟩, hXg⟩

/-- The value `e^{i α(X)}` of the root character at `g = exp X`, for a chosen `X`. -/
private def rootCharacterFun (α : Dual ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (hT : IsClosed (T : Set G)) (hconn : IsPreconnected (T : Set G)) (g : T) : Circle :=
  Circle.exp (α (exists_lieExp_eq (I := I) hT hconn g).choose)

variable (h : IsRootPlane B (lieSubalgebraOfSubgroup (I := I) T).toSubmodule α V J)
  (hT : IsClosed (T : Set G)) (hconn : IsPreconnected (T : Set G)) (hV : V ≠ ⊥)

include h hV in
private theorem rootCharacterFun_eq (g : T) (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (hX : lieExp (I := I) (X : LeftInvariantDerivation I G) = g) :
    rootCharacterFun α hT hconn g = Circle.exp (α X) :=
  h.circleExp_eq_of_lieExp_eq hV
    (((exists_lieExp_eq (I := I) hT hconn g).choose_spec).trans hX.symm)

include h hV in
/-- The value of the root character depends continuously on `g`: it is read off from `Ad g v`
through the injective linear map `reImMap J v`, a closed embedding of `ℂ` into the Lie algebra. -/
private theorem continuous_rootCharacterFun : Continuous (rootCharacterFun α hT hconn) := by
  have := Submodule.nontrivial_iff_ne_bot.2 hV
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hΦ :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2 (h.injective_reImMap hv))
  have hAd : Continuous fun g : T ↦ Ad (I := I) (g : G) (v : LeftInvariantDerivation I G) :=
    (contMDiff_Ad_apply (I := I) (G := G)).continuous.comp
      (continuous_subtypeVal.prodMk continuous_const)
  have hval (g : T) : Ad (I := I) (g : G) (v : LeftInvariantDerivation I G) =
      reImMap J v (rootCharacterFun α hT hconn g) := by
    obtain ⟨X, hX⟩ := exists_lieExp_eq (I := I) hT hconn g
    rw [h.rootCharacterFun_eq hT hconn hV g X hX, ← hX]
    exact h.Ad_lieExp_apply_eq_circleExp X v
  exact continuous_induced_rng.2 (hΦ.continuous_iff.2 (hAd.congr hval))

/-- **The root character** `χ_α : T → S¹` of a nonzero root plane `V` of the Lie algebra of a closed
connected commutative subgroup `T`, for instance a torus: the continuous character by which `T`
rotates `V`, characterized by `χ_α (exp H) = e^{i α(H)}` (`rootCharacter_lieExp`) and
`Ad g v = Re (χ_α g) • v + Im (χ_α g) • J v` (`Ad_apply`). -/
def rootCharacter : T →ₜ* Circle where
  toFun := rootCharacterFun α hT hconn
  map_one' := by
    rw [h.rootCharacterFun_eq hT hconn hV 1 0 (by simp), map_zero, Circle.exp_zero]
  map_mul' g g' := by
    obtain ⟨X, hX⟩ := exists_lieExp_eq (I := I) hT hconn g
    obtain ⟨Y, hY⟩ := exists_lieExp_eq (I := I) hT hconn g'
    have hXY : lieExp (I := I) ((X + Y : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
        LeftInvariantDerivation I G) = (g * g' : T) := by
      rw [Submodule.coe_add, lieExp_add_of_lie_eq_zero
        (lie_eq_zero_of_mem_lieSubalgebraOfSubgroup
          ((LieSubalgebra.mem_toSubmodule _).1 X.property)
          ((LieSubalgebra.mem_toSubmodule _).1 Y.property)), hX, hY, Subgroup.coe_mul]
    rw [h.rootCharacterFun_eq hT hconn hV _ _ hXY, h.rootCharacterFun_eq hT hconn hV _ _ hX,
      h.rootCharacterFun_eq hT hconn hV _ _ hY, map_add, Circle.exp_add]
  continuous_toFun := h.continuous_rootCharacterFun hT hconn hV

/-- **The root character at an exponential**: `χ_α g = e^{i α(X)}` for any `X` with
`exp X = g`. -/
theorem rootCharacter_apply_of_lieExp_eq (g : T)
    (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)
    (hX : lieExp (I := I) (X : LeftInvariantDerivation I G) = g) :
    h.rootCharacter hT hconn hV g = Circle.exp (α X) :=
  h.rootCharacterFun_eq hT hconn hV g X hX

/-- **The root character on exponentials**: `χ_α (exp H) = e^{i α(H)}`, that is, `dχ_α = i α`. -/
@[simp]
theorem rootCharacter_lieExp (X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    h.rootCharacter hT hconn hV
        ⟨lieExp (I := I) (X : LeftInvariantDerivation I G),
          lieExp_mem_of_mem_lieSubalgebraOfSubgroup hT
            ((LieSubalgebra.mem_toSubmodule _).1 X.property)⟩ =
      Circle.exp (α X) :=
  h.rootCharacter_apply_of_lieExp_eq hT hconn hV _ X rfl

/-- **`T` rotates the root plane by its root character**:
`Ad g v = Re (χ_α g) • v + Im (χ_α g) • J v`. -/
theorem Ad_apply (g : T) (v : V) :
    Ad (I := I) (g : G) v =
      (h.rootCharacter hT hconn hV g : ℂ).re • (v : LeftInvariantDerivation I G) +
        (h.rootCharacter hT hconn hV g : ℂ).im • (J v : LeftInvariantDerivation I G) := by
  obtain ⟨X, hX⟩ := exists_lieExp_eq (I := I) hT hconn g
  rw [h.rootCharacter_apply_of_lieExp_eq hT hconn hV g X hX, ← hX]
  exact (h.Ad_lieExp_apply_eq_circleExp X v).trans (reImMap_apply J v _)

include h hT hconn hV in
/-- The adjoint action of `T` preserves each of its nonzero root planes. -/
theorem Ad_apply_mem (g : T) (v : V) : Ad (I := I) (g : G) v ∈ V := by
  rw [h.Ad_apply hT hconn hV]
  exact add_mem (V.smul_mem _ v.property) (V.smul_mem _ (J v).property)

/-- **The root character is determined by its values on exponentials**: a map `ψ : T → S¹` is the
root character exactly when `ψ (exp H) = e^{i α(H)}` for every `H ∈ Lie(T)`. -/
theorem eq_rootCharacter_iff {ψ : T → Circle} :
    ψ = h.rootCharacter hT hconn hV ↔
      ∀ X : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule,
        ψ ⟨lieExp (I := I) (X : LeftInvariantDerivation I G),
            lieExp_mem_of_mem_lieSubalgebraOfSubgroup hT
              ((LieSubalgebra.mem_toSubmodule _).1 X.property)⟩ =
          Circle.exp (α X) := by
  refine ⟨fun hψ X ↦ hψ ▸ h.rootCharacter_lieExp hT hconn hV X, fun hψ ↦ funext fun g ↦ ?_⟩
  obtain ⟨X, hX⟩ := exists_lieExp_eq (I := I) hT hconn g
  rw [h.rootCharacter_apply_of_lieExp_eq hT hconn hV g X hX, ← hψ X]
  exact congrArg ψ (Subtype.ext hX.symm)

/-- **The kernel of the root character** is the subgroup of `T` acting trivially on the root
plane. -/
theorem rootCharacter_eq_one_iff (g : T) :
    h.rootCharacter hT hconn hV g = 1 ↔ ∀ v : V, Ad (I := I) (g : G) v = v := by
  refine ⟨fun hg v ↦ by simp [h.Ad_apply hT hconn hV, hg], fun hg ↦ ?_⟩
  have := Submodule.nontrivial_iff_ne_bot.2 hV
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h₁ := h.Ad_apply hT hconn hV g v
  rw [hg] at h₁
  refine Circle.ext (h.injective_reImMap hv ?_)
  simpa [reImMap_apply] using h₁.symm

end Character

end TauCeti.IsRootPlane
