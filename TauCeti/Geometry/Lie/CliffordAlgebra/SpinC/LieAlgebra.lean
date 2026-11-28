/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.SpinC.Determinant
public import TauCeti.Geometry.Lie.Adjoint.Naturality
public import TauCeti.Geometry.Lie.Prod
import TauCeti.Geometry.Lie.Subgroup.Center
import TauCeti.Algebra.Lie.Basic

/-!
# The Lie algebra of compact Spinᶜ and its Spin–determinant splitting

The defining central quotient `mk : Spin(n) × U(1) → Spinᶜ(n)` is a smooth local diffeomorphism,
so its differential identifies `Lie(Spinᶜ(n))` as a Lie algebra with `Lie(Spin(n)) × Lie(U(1))`.
Under this identification:

* the Lie map of `ofSpin : Spin(n) → Spinᶜ(n)` is injective and its image is the Lie subalgebra
  `ker(d det)` of elements of determinant weight zero;
* combining `ofSpin_* : Lie(Spin(n)) ≃ₗ⁅ℝ⁆ ker(d det)` with the half-speed central determinant
  lift `realDetLieLift` refines `realDetLieLinearEquiv` to a linear isomorphism
  `realSpinProdDetLinearEquiv : Lie(Spin(n)) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))` in which the second factor
  is the normalized determinant parameter `d det(Y)`.

Because the central determinant lift commutes with every element of `Spinᶜ(n)`, this coordinate
splitting preserves Lie brackets via `⁅(X, a), (X', a')⁆ = (⁅X, X'⁆, 0)`, exponentiates to
`[exp X, exp(i a / 2)]`, and intertwines the group adjoint action of `[s, z]` with `(Ad(s) X, a)`.

## Main definitions

* `CliffordAlgebra.spinCGroup.realMkLieEquiv`: the Lie-algebra isomorphism induced by the quotient
  homomorphism `Spin(n) × Circle → Spinᶜ(n)`.
* `CliffordAlgebra.spinCGroup.realSpinProdCircleLieEquiv`: the Lie-algebra isomorphism
  `Lie(Spin(n)) × Lie(Circle) ≃ₗ⁅ℝ⁆ Lie(Spinᶜ(n))`.
* `CliffordAlgebra.spinCGroup.realSpinLieEquivDetKer`: the Lie-algebra isomorphism from
  `Lie(Spin(n))` onto the kernel Lie ideal of `(detContinuousMonoidHom _ hQ).lieMap`.
* `CliffordAlgebra.spinCGroup.realSpinProdDetLinearEquiv`: the Spin–determinant splitting
  `Lie(Spin(n)) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))`.
* `CliffordAlgebra.spinCGroup.realQuadraticProdDetLinearEquiv`: the same splitting in quadratic
  Clifford coordinates `quadraticLieSubalgebra (realCliffordForm n 0) × ℝ ≃ₗ[ℝ] Lie(Spinᶜ(n))`.

## Main results

* `CliffordAlgebra.spinCGroup.range_lieMap_ofSpinContinuousMonoidHom`: the image of `ofSpin_*` is
  `ker(d det)`.
* `CliffordAlgebra.spinCGroup.lie_realSpinProdDetLinearEquiv`: Lie brackets in Spin–determinant
  coordinates vanish in the central determinant slot and agree with the Spin bracket in the first
  slot.
* `CliffordAlgebra.spinCGroup.lieExp_realSpinProdDetLinearEquiv`: the Lie exponential of `(X, a)`
  is `mk (exp X, Circle.exp (a / 2))`.
* `CliffordAlgebra.spinCGroup.Ad_mk_realSpinProdDetLinearEquiv`: the adjoint action of `[s, z]`
  acts as `Ad(s)` on the Spin component and fixes the determinant component.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds* (1996), §3.1.
-/

public section

noncomputable section

open CliffordAlgebra Manifold TauCeti TauCeti.CliffordAlgebra
open scoped Manifold ContDiff

namespace CliffordAlgebra.spinCGroup

variable (n : ℕ) (hQ : realCliffordForm n 0 ≠ 0)

local notation "IS" => 𝓘(ℝ, realSpinLieModel n)
local notation "IC" => ModelWithCorners.prod IS (𝓡 1)
local notation "G" => spinCGroup (realCliffordForm n 0) hQ
local notation "𝔤" => LeftInvariantDerivation IC G
local notation "𝔰" => LeftInvariantDerivation IS (spinGroup (realCliffordForm n 0))
local notation "d" => ContinuousMonoidHom.lieWeight (I := IC) (detContinuousMonoidHom _ hQ)
local notation "ιS" =>
  ContinuousMonoidHom.lieMap (I := IS) (I' := IC) (ofSpinContinuousMonoidHom _ hQ)
local notation "ιC" =>
  ContinuousMonoidHom.lieMap (I := 𝓡 1) (I' := IC) (ofCircleContinuousMonoidHom _ hQ)

/-- The Lie differential of the defining central quotient `Spin(n) × U(1) → Spinᶜ(n)` is
bijective. -/
theorem lieMap_mkContinuousMonoidHom_bijective :
    Function.Bijective
      (ContinuousMonoidHom.lieMap (I := IC) (I' := IC) (mkContinuousMonoidHom _ hQ)) :=
  ContinuousMonoidHom.lieMap_bijective_of_isLocalDiffeomorphAt _ <| by
    have hcoe : (mkContinuousMonoidHom (realCliffordForm n 0) hQ :
        spinGroup (realCliffordForm n 0) × Circle → G) = mk _ hQ :=
      funext (mkContinuousMonoidHom_apply _ hQ)
    exact hcoe.symm ▸ isLocalDiffeomorph_realMk n hQ 1

/-- The Lie-algebra equivalence induced by the central double-cover quotient homomorphism
`Spin(n) × U(1) → Spinᶜ(n)`. -/
def realMkLieEquiv :
    LeftInvariantDerivation IC (spinGroup (realCliffordForm n 0) × Circle) ≃ₗ⁅ℝ⁆ 𝔤 :=
  LieEquiv.ofBijective
    (ContinuousMonoidHom.lieMap (I := IC) (I' := IC) (mkContinuousMonoidHom _ hQ))
    (lieMap_mkContinuousMonoidHom_bijective n hQ)

/-- `realMkLieEquiv` acts by the Lie differential of `mkContinuousMonoidHom`. -/
@[simp]
theorem realMkLieEquiv_apply
    (D : LeftInvariantDerivation IC (spinGroup (realCliffordForm n 0) × Circle)) :
    realMkLieEquiv n hQ D =
      ContinuousMonoidHom.lieMap (I := IC) (I' := IC) (mkContinuousMonoidHom _ hQ) D :=
  LieEquiv.ofBijective_apply _ _ D

/-- The Lie-algebra isomorphism `Lie(Spin(n)) × Lie(U(1)) ≃ₗ⁅ℝ⁆ Lie(Spinᶜ(n))` induced by the
defining central quotient. -/
def realSpinProdCircleLieEquiv : (𝔰 × LeftInvariantDerivation (𝓡 1) Circle) ≃ₗ⁅ℝ⁆ 𝔤 :=
  TauCeti.Lie.prodLieEquiv.symm.trans (realMkLieEquiv n hQ)

/-- `realSpinProdCircleLieEquiv` reconstructs a pair `(X, Z)` by adding its Spin and central-circle
images in `Lie(Spinᶜ(n))`. -/
@[simp]
theorem realSpinProdCircleLieEquiv_apply (p : 𝔰 × LeftInvariantDerivation (𝓡 1) Circle) :
    realSpinProdCircleLieEquiv n hQ p = ιS p.1 + ιC p.2 := by
  rw [realSpinProdCircleLieEquiv, LieEquiv.trans_apply, realMkLieEquiv_apply,
    TauCeti.Lie.lieMap_prodLieEquiv_symm, mkContinuousMonoidHom_comp_inl,
    mkContinuousMonoidHom_comp_inr]

/-- The Lie differential of the Spin inclusion `Spin(n) → Spinᶜ(n)` is injective. -/
theorem lieMap_ofSpinContinuousMonoidHom_injective : Function.Injective ιS := by
  rw [← mkContinuousMonoidHom_comp_inl (realCliffordForm n 0) hQ]
  exact TauCeti.Lie.lieMap_comp_inl_injective
    (lieMap_mkContinuousMonoidHom_bijective n hQ).injective

/-- The Lie differential of the central circle inclusion `U(1) → Spinᶜ(n)` is injective. -/
theorem lieMap_ofCircleContinuousMonoidHom_injective : Function.Injective ιC := by
  rw [← mkContinuousMonoidHom_comp_inr (realCliffordForm n 0) hQ]
  exact TauCeti.Lie.lieMap_comp_inr_injective
    (lieMap_mkContinuousMonoidHom_bijective n hQ).injective

/-- The determinant differential vanishes on the image of the Spin Lie algebra. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_lieMap_ofSpinContinuousMonoidHom (X : 𝔰) :
    d (ιS X) = 0 := by
  have h := LinearMap.congr_fun
    (ContinuousMonoidHom.lieWeight_comp (I := IS) (I' := IC)
      (detContinuousMonoidHom _ hQ) (ofSpinContinuousMonoidHom _ hQ)) X
  simpa only [detContinuousMonoidHom_comp_ofSpinContinuousMonoidHom,
    ContinuousMonoidHom.lieWeight_one, LinearMap.zero_apply, LinearMap.comp_apply,
    LieHom.coe_toLinearMap] using h.symm

local notation "δ" =>
  ContinuousMonoidHom.lieMap (I := IC) (I' := 𝓡 1) (detContinuousMonoidHom _ hQ)

private theorem toSubmodule_ker_detLieMap :
    (δ).ker.toLieSubalgebra.toSubmodule = LinearMap.ker d := by
  have hd : d = circleLieAlgebraEquiv.toLinearMap ∘ₗ (δ).toLinearMap :=
    LinearMap.ext (ContinuousMonoidHom.lieWeight_apply _)
  rw [LieIdeal.toLieSubalgebra_toSubmodule, LieHom.ker_toSubmodule, hd]
  exact (LinearMap.ker_comp_of_ker_eq_bot (δ).toLinearMap
    (LinearEquiv.ker circleLieAlgebraEquiv)).symm

/-- **Exactness at `Lie(Spinᶜ(n))`**: the image of `ofSpin_*` is precisely the kernel of the
determinant Lie differential. -/
@[simp]
theorem range_lieMap_ofSpinContinuousMonoidHom :
    (ιS).range = (δ).ker.toLieSubalgebra := by
  ext Y
  rw [LieHom.mem_range, LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker]
  constructor
  · rintro ⟨X, rfl⟩
    refine circleLieAlgebraEquiv.injective ?_
    rw [← ContinuousMonoidHom.lieWeight_apply,
      lieWeight_detContinuousMonoidHom_lieMap_ofSpinContinuousMonoidHom, map_zero]
  · intro hY
    have hYd : d Y = 0 := by
      rw [ContinuousMonoidHom.lieWeight_apply, hY, map_zero]
    let p := (realSpinProdCircleLieEquiv n hQ).symm Y
    have hp : ιS p.1 + ιC p.2 = Y := by
      rw [← realSpinProdCircleLieEquiv_apply, (realSpinProdCircleLieEquiv n hQ).apply_symm_apply]
    have hd : 2 * circleLieAlgebraEquiv p.2 = 0 := by
      have hsum : d (ιS p.1) + d (ιC p.2) = 0 := by
        rw [← map_add, hp, hYd]
      simpa only [lieWeight_detContinuousMonoidHom_lieMap_ofSpinContinuousMonoidHom,
        lieWeight_detContinuousMonoidHom_lieMap_ofCircleContinuousMonoidHom, zero_add] using hsum
    have hp2 : p.2 = 0 := circleLieAlgebraEquiv.injective <|
      (mul_eq_zero.mp hd).resolve_left two_ne_zero |>.trans (map_zero _).symm
    exact ⟨p.1, by simpa [hp2] using hp⟩

/-- Linear-map form of exactness: the linear range of `ofSpin_*` equals `ker(d det)`. -/
theorem range_lieMap_ofSpinContinuousMonoidHom_toLinearMap :
    LinearMap.range (ιS).toLinearMap = LinearMap.ker d :=
  (congrArg LieSubalgebra.toSubmodule (range_lieMap_ofSpinContinuousMonoidHom n hQ)).trans
    (toSubmodule_ker_detLieMap n hQ)

/-- The Spin inclusion identifies `Lie(Spin(n))` as a Lie algebra with the kernel of the
determinant differential. -/
def realSpinLieEquivDetKer : 𝔰 ≃ₗ⁅ℝ⁆ (δ).ker.toLieSubalgebra :=
  ((ιS).equivRangeOfInjective (lieMap_ofSpinContinuousMonoidHom_injective n hQ)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (range_lieMap_ofSpinContinuousMonoidHom n hQ)))

/-- Coercing `realSpinLieEquivDetKer` to `Lie(Spinᶜ(n))` recovers `ofSpin_*`. -/
@[simp]
theorem coe_realSpinLieEquivDetKer_apply (X : 𝔰) : (realSpinLieEquivDetKer n hQ X : 𝔤) = ιS X :=
  (rfl)

/-- Applying `ofSpin_*` to the inverse equivalence recovers the ambient kernel element. -/
@[simp]
theorem lieMap_ofSpinContinuousMonoidHom_realSpinLieEquivDetKer_symm_apply
    (Y : (δ).ker.toLieSubalgebra) :
    ιS ((realSpinLieEquivDetKer n hQ).symm Y) = (Y : 𝔤) :=
  congrArg Subtype.val ((realSpinLieEquivDetKer n hQ).apply_symm_apply Y)

/-- **The Spin–determinant splitting of `Lie(Spinᶜ(n))`**. It refines `realDetLieLinearEquiv` by
identifying `ker(d det)` with `Lie(Spin(n))`, while keeping the normalized determinant weight on
the second factor via `realDetLieLift`. -/
def realSpinProdDetLinearEquiv : (𝔰 × ℝ) ≃ₗ[ℝ] 𝔤 :=
  (LinearEquiv.prodCongr
    ((realSpinLieEquivDetKer n hQ).toLinearEquiv.trans
      (LinearEquiv.ofEq _ (LinearMap.ker d) (toSubmodule_ker_detLieMap n hQ)))
    (LinearEquiv.refl ℝ ℝ)).trans (realDetLieLinearEquiv n hQ)

/-- Reconstruction adds the Spin Lie-algebra image to the half-speed central determinant lift. -/
theorem realSpinProdDetLinearEquiv_apply (p : 𝔰 × ℝ) :
    realSpinProdDetLinearEquiv n hQ p = ιS p.1 + realDetLieLift n hQ p.2 := by
  dsimp only [realSpinProdDetLinearEquiv]
  rw [LinearEquiv.trans_apply, realDetLieLinearEquiv_apply]
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply,
    LieEquiv.coe_toLinearEquiv, LinearEquiv.refl_apply]
  rw [LinearEquiv.coe_ofEq_apply, coe_realSpinLieEquivDetKer_apply]

/-- Evaluating the determinant weight on `realSpinProdDetLinearEquiv (X, a)` recovers `a`. -/
@[simp]
theorem lieWeight_detContinuousMonoidHom_realSpinProdDetLinearEquiv (p : 𝔰 × ℝ) :
    d (realSpinProdDetLinearEquiv n hQ p) = p.2 := by
  rw [realSpinProdDetLinearEquiv_apply]
  simp only [map_add, lieWeight_detContinuousMonoidHom_lieMap_ofSpinContinuousMonoidHom,
    lieWeight_detContinuousMonoidHom_realDetLieLift, zero_add]

/-- The second component of `(realSpinProdDetLinearEquiv n hQ).symm Y` is the determinant weight
`d det(Y)`. -/
@[simp]
theorem realSpinProdDetLinearEquiv_symm_snd (Y : 𝔤) :
    ((realSpinProdDetLinearEquiv n hQ).symm Y).2 = d Y :=
  (lieWeight_detContinuousMonoidHom_realSpinProdDetLinearEquiv n hQ _).symm.trans
    (congrArg d ((realSpinProdDetLinearEquiv n hQ).apply_symm_apply Y))

/-- Pushing the Spin component of `(realSpinProdDetLinearEquiv n hQ).symm Y` back into
`Lie(Spinᶜ(n))` removes the central determinant lift `realDetLieLift (d det(Y))`. -/
@[simp]
theorem lieMap_ofSpinContinuousMonoidHom_realSpinProdDetLinearEquiv_symm_fst (Y : 𝔤) :
    ιS ((realSpinProdDetLinearEquiv n hQ).symm Y).1 = Y - realDetLieLift n hQ (d Y) := by
  apply eq_sub_of_add_eq
  rw [← realSpinProdDetLinearEquiv_symm_snd n hQ Y, ← realSpinProdDetLinearEquiv_apply,
    (realSpinProdDetLinearEquiv n hQ).apply_symm_apply]

/-- The inverse splitting sends `ofSpin_* X` to `(X, 0)`. -/
@[simp]
theorem realSpinProdDetLinearEquiv_symm_lieMap_ofSpinContinuousMonoidHom (X : 𝔰) :
    (realSpinProdDetLinearEquiv n hQ).symm (ιS X) = (X, 0) := by
  apply (realSpinProdDetLinearEquiv n hQ).injective
  simp only [LinearEquiv.apply_symm_apply, realSpinProdDetLinearEquiv_apply, map_zero, add_zero]

/-- The inverse splitting sends `realDetLieLift a` to `(0, a)`. -/
@[simp]
theorem realSpinProdDetLinearEquiv_symm_realDetLieLift (a : ℝ) :
    (realSpinProdDetLinearEquiv n hQ).symm (realDetLieLift n hQ a) = (0, a) := by
  apply (realSpinProdDetLinearEquiv n hQ).injective
  simp only [LinearEquiv.apply_symm_apply, realSpinProdDetLinearEquiv_apply, map_zero, zero_add]

/-- **Lie bracket in Spin–determinant coordinates**: the central determinant component brackets
trivially, while the Spin component carries the native Spin Lie bracket. -/
@[simp]
theorem lie_realSpinProdDetLinearEquiv (p q : 𝔰 × ℝ) :
    ⁅realSpinProdDetLinearEquiv n hQ p, realSpinProdDetLinearEquiv n hQ q⁆ =
      realSpinProdDetLinearEquiv n hQ (⁅p.1, q.1⁆, 0) := by
  simp only [realSpinProdDetLinearEquiv_apply, lie_add, add_lie, realDetLieLift_lie,
    lie_realDetLieLift, LieHom.map_lie, map_zero, add_zero]

/-- Transporting `realSpinProdDetLinearEquiv` along a Lie-algebra equivalence `e : L ≃ₗ⁅ℝ⁆ 𝔰` on
the Spin factor preserves Lie brackets in the first slot and annihilates the central determinant
parameter. -/
theorem lie_realSpinProdDetLinearEquiv_comp_lieEquiv
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] (e : L ≃ₗ⁅ℝ⁆ 𝔰) (p q : L × ℝ) :
    ⁅realSpinProdDetLinearEquiv n hQ (e p.1, p.2),
        realSpinProdDetLinearEquiv n hQ (e q.1, q.2)⁆ =
      realSpinProdDetLinearEquiv n hQ (e ⁅p.1, q.1⁆, 0) :=
  (lie_realSpinProdDetLinearEquiv n hQ (e p.1, p.2) (e q.1, q.2)).trans <|
    congrArg (fun X ↦ realSpinProdDetLinearEquiv n hQ (X, 0)) (e.map_lie p.1 q.1).symm

/-- **Lie exponential in Spin–determinant coordinates**: `(X, a)` exponentiates to the class
`[exp X, exp(i a / 2)]` in `Spinᶜ(n)`. -/
@[simp]
theorem lieExp_realSpinProdDetLinearEquiv (p : 𝔰 × ℝ) :
    lieExp (realSpinProdDetLinearEquiv n hQ p) =
      mk _ hQ (lieExp p.1, Circle.exp (p.2 / 2)) := by
  calc
    lieExp (realSpinProdDetLinearEquiv n hQ p)
        = lieExp (ιS p.1 + realDetLieLift n hQ p.2) := by
          rw [realSpinProdDetLinearEquiv_apply]
    _ = lieExp (ιS p.1) * ofCircle _ hQ (Circle.exp (p.2 / 2)) :=
          lieExp_add_realDetLieLift n hQ _ p.2
    _ = ofSpin _ hQ (lieExp p.1) * ofCircle _ hQ (Circle.exp (p.2 / 2)) := by
          rw [← ContinuousMonoidHom.map_lieExp]
          simp only [ofSpinContinuousMonoidHom_apply]
    _ = mk _ hQ (lieExp p.1, Circle.exp (p.2 / 2)) :=
          ofSpin_mul_ofCircle _ hQ _ _

/-- Conjugating by `[s, z]` in `Spinᶜ(n)` acts on `ofSpin_* X` as `ofSpin_* (Ad(s) X)`: the central
circle factor acts trivially. -/
@[simp]
theorem Ad_mk_lieMap_ofSpinContinuousMonoidHom
    (s : spinGroup (realCliffordForm n 0)) (z : Circle) (X : 𝔰) :
    Lie.Ad (I := IC) (mk _ hQ (s, z)) (ιS X) = ιS (Lie.Ad (I := IS) s X) := by
  let _ : T2Space G := (IC).t2Space_of_lieGroup ∞
  calc
    Lie.Ad (I := IC) (mk _ hQ (s, z)) (ιS X)
        = Lie.Ad (I := IC) (ofSpin _ hQ s * ofCircle _ hQ z) (ιS X) := by
          rw [ofSpin_mul_ofCircle]
    _ = Lie.Ad (I := IC) (ofSpin _ hQ s) (ιS X) :=
          Lie.Ad_mul_right_of_mem_center (ofSpin _ hQ s) (ofCircle_mem_center _ hQ z) (ιS X)
    _ = Lie.Ad (I := IC) (ofSpinContinuousMonoidHom _ hQ s) (ιS X) := by
          simp only [ofSpinContinuousMonoidHom_apply]
    _ = ιS (Lie.Ad (I := IS) s X) :=
          (ContinuousMonoidHom.lieMap_Ad (ofSpinContinuousMonoidHom _ hQ) s X).symm

/-- **Adjoint action in Spin–determinant coordinates**: `[s, z]` acts as `Ad(s)` on the Spin
component and fixes the determinant parameter. -/
@[simp]
theorem Ad_mk_realSpinProdDetLinearEquiv
    (s : spinGroup (realCliffordForm n 0)) (z : Circle) (p : 𝔰 × ℝ) :
    Lie.Ad (I := IC) (mk _ hQ (s, z)) (realSpinProdDetLinearEquiv n hQ p) =
      realSpinProdDetLinearEquiv n hQ (Lie.Ad (I := IS) s p.1, p.2) := by
  rw [realSpinProdDetLinearEquiv_apply, realSpinProdDetLinearEquiv_apply]
  simp only [map_add, Ad_mk_lieMap_ofSpinContinuousMonoidHom, Ad_realDetLieLift]

/-- The Spin–determinant splitting of `Lie(Spinᶜ(n))` in quadratic Clifford coordinates. -/
def realQuadraticProdDetLinearEquiv :
    (quadraticLieSubalgebra (realCliffordForm n 0) × ℝ) ≃ₗ[ℝ] 𝔤 :=
  (LinearEquiv.prodCongr (realSpinLieEquivQuadratic n).symm.toLinearEquiv
    (LinearEquiv.refl ℝ ℝ)).trans (realSpinProdDetLinearEquiv n hQ)

/-- Evaluation of `realQuadraticProdDetLinearEquiv` via `realSpinProdDetLinearEquiv`. -/
theorem realQuadraticProdDetLinearEquiv_apply
    (p : quadraticLieSubalgebra (realCliffordForm n 0) × ℝ) :
    realQuadraticProdDetLinearEquiv n hQ p =
      realSpinProdDetLinearEquiv n hQ ((realSpinLieEquivQuadratic n).symm p.1, p.2) :=
  (rfl)

/-- Lie brackets in quadratic Clifford–determinant coordinates preserve the quadratic Clifford
bracket and annihilate the determinant component. -/
@[simp]
theorem lie_realQuadraticProdDetLinearEquiv
    (p q : quadraticLieSubalgebra (realCliffordForm n 0) × ℝ) :
    ⁅realQuadraticProdDetLinearEquiv n hQ p, realQuadraticProdDetLinearEquiv n hQ q⁆ =
      realQuadraticProdDetLinearEquiv n hQ (⁅p.1, q.1⁆, 0) := by
  simp only [realQuadraticProdDetLinearEquiv_apply, lie_realSpinProdDetLinearEquiv_comp_lieEquiv]

end CliffordAlgebra.spinCGroup
