/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Algebra.Star.Projection.Family
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Projection
import TauCeti.Analysis.RCLike.Basic

/-!
# Central projection C⋆-ideals and minimal star projections

In a C⋆-algebra `B`, a nonzero star projection `p` is **minimal** (in the sense that its corner
`p * B * p` is `ℂ • p`) when compression by `p` takes scalar values along `p`:
`∀ b : B, p * b * p = ψ b • p` for a linear functional `ψ : B →ₗ[ℂ] ℂ`.

This file provides two pieces of general C⋆-algebra projection infrastructure used in the
finite-dimensional Artin--Wedderburn `⋆`-upgrade and independently reusable in infinite dimension:

1. **Central `⋆`-ideals (`IsStarProjection.instCStarAlgebraCentralSubalgebra`)**: for a
   multiplicatively central star projection `z` in a `NonUnitalCStarAlgebra A`, the principal
   `⋆`-ideal `hz.centralSubalgebra ℂ hc = {a : A | z * a = a}` is norm-closed and carries a
   canonical unital `CStarAlgebra` structure with identity `z`.
2. **Minimal projections and their Hilbert-space left ideals**:
   * `IsIdempotentElem.exists_isStarProjection_of_forall_mul_eq_smul`: any nonzero idempotent `q`
     with scalar corner `q * B * q ⊆ ℂ • q` normalizes via `(φ (star q))⁻¹ • (star q * q)` to a
     nonzero minimal star projection `p` generating the same left ideal (`p * q = p` and
     `q * p = q`).
   * `TauCeti.leftIdealSubmodule`: the principal left ideal `{x : B | x * p = x}` as a closed
     submodule of `B`.
   * `IsStarProjection.leftIdealInnerProductSpace` and
     `IsStarProjection.leftMulNonUnitalStarAlgHom` / `IsStarProjection.leftMulStarAlgHom`: the
     `p`-valued inner product `⟪x, y⟫ = ψ (star x * y)` makes `leftIdealSubmodule ℂ p` a Hilbert
     space compatible with the C⋆-norm of `B`, on which `B` acts by bounded operators via a
     `⋆`-representation.

## Main definitions

* `IsStarProjection.instCStarAlgebraCentralSubalgebra`: unital `CStarAlgebra` structure on
  `hz.centralSubalgebra ℂ hc`.
* `TauCeti.leftIdealSubmodule`: the principal left ideal `{x : B | x * p = x}` as an `R`-submodule.
* `IsStarProjection.leftIdealInnerProductSpace`: `InnerProductSpace ℂ` structure on
  `TauCeti.leftIdealSubmodule ℂ p` induced by a scalar corner `p * b * p = ψ b • p`.
* `IsStarProjection.leftMulNonUnitalStarAlgHom`, `IsStarProjection.leftMulStarAlgHom`: the
  left-multiplication `⋆`-representation of `B` on `TauCeti.leftIdealSubmodule ℂ p`.

## Main results

* `IsStarProjection.norm_eq_one`: every nonzero star projection in a C⋆-ring has norm `1`.
* `IsIdempotentElem.exists_isStarProjection_of_forall_mul_eq_smul`: normalize a nonzero
  scalar-corner idempotent to a left-equivalent minimal star projection.
* `IsStarProjection.star_mul_of_mem_leftIdealSubmodule`: for `x, y ∈ leftIdealSubmodule R p`,
  `star x * y = ψ (star x * y) • p`.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace IsStarProjection

/-- The principal `⋆`-ideal `{a : A | z * a = a}` cut out by a central star projection in a
Hausdorff topological semiring with continuous multiplication is closed. -/
instance isClosed_centralSubalgebra {R A : Type*} [CommSemiring R] [TopologicalSpace A]
    [T2Space A] [NonUnitalSemiring A] [StarRing A] [ContinuousMul A] [Module R A]
    [SMulCommClass R A A] {z : A} (hz : IsStarProjection z) (hc : IsMulCentral z) :
    IsClosed (hz.centralSubalgebra R hc : Set A) := by
  have hset : (hz.centralSubalgebra R hc : Set A) = {a : A | z * a = a} :=
    Set.ext fun _ ↦ hz.mem_centralSubalgebra R hc
  rw [hset]
  exact isClosed_eq (by fun_prop) continuous_id

/-- For a central star projection `z` in a `NonUnitalCStarAlgebra A`, the principal `⋆`-ideal
`hz.centralSubalgebra ℂ hc` is a unital `CStarAlgebra` with identity `z`. -/
noncomputable instance instCStarAlgebraCentralSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    {z : A} (hz : IsStarProjection z) (hc : IsMulCentral z) :
    CStarAlgebra (hz.centralSubalgebra ℂ hc) where
  __ : NonUnitalCStarAlgebra (hz.centralSubalgebra ℂ hc) := inferInstance
  __ : Ring (hz.centralSubalgebra ℂ hc) := inferInstance
  __ : Algebra ℂ (hz.centralSubalgebra ℂ hc) := inferInstance
  norm_smul_le := NormedSpace.norm_smul_le

/-- Every nonzero star projection in a C⋆-ring has norm `1`. -/
theorem norm_eq_one {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] {p : E}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) : ‖p‖ = 1 := by
  have hmul : ‖p‖ * ‖p‖ = ‖p‖ := by
    rw [← CStarRing.norm_star_mul_self, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hp_ne) (hmul.trans (mul_one ‖p‖).symm)

end IsStarProjection

/-- In a `NonUnitalCStarAlgebra`, any nonzero idempotent `q` whose corner `q * B * q` is scalar
along `q` normalizes via `p = (φ (star q))⁻¹ • (star q * q)` to a nonzero star projection with
scalar corner `p * B * p ⊆ ℂ • p` that is left-equivalent to `q` (`p * q = p` and `q * p = q`). -/
theorem IsIdempotentElem.exists_isStarProjection_of_forall_mul_eq_smul {B : Type*}
    [NonUnitalCStarAlgebra B] {q : B} (hq : IsIdempotentElem q) (hq_ne : q ≠ 0)
    (φ : B →ₗ[ℂ] ℂ) (hcorner : ∀ b : B, q * b * q = φ b • q) :
    ∃ (p : B) (ψ : B →ₗ[ℂ] ℂ),
      IsStarProjection p ∧ p ≠ 0 ∧ (∀ b : B, p * b * p = ψ b • p) ∧
      p * q = p ∧ q * p = q := by
  let _ := CStarAlgebra.spectralOrder B
  have _ := CStarAlgebra.spectralOrderedRing B
  set c : ℂ := φ (Star.star q)
  set a : B := Star.star q * q
  -- `a = star q * q` is strictly positive with `a * a = c • a`, forcing `c` real and positive.
  have ha_ne : a ≠ 0 := star_mul_self_ne_zero.mpr hq_ne
  have ha_pos : 0 < a := lt_of_le_of_ne (star_mul_self_nonneg q) ha_ne.symm
  have ha_sa : IsSelfAdjoint a := .star_mul_self q
  have ha_sq : a * a = c • a := by
    calc
      a * a = Star.star q * (q * Star.star q * q) := by simp only [a, mul_assoc]
      _ = c • a := by rw [hcorner (Star.star q), mul_smul_comm]
  have ha2_star : Star.star a * a = c • a := by rw [ha_sa.star_eq, ha_sq]
  have hc_nonneg : 0 ≤ c :=
    nonneg_of_smul_nonneg_of_pos_right (ha2_star ▸ star_mul_self_nonneg a) ha_pos
  have hc_conj : Star.star c = c := (IsSelfAdjoint.of_nonneg hc_nonneg).star_eq
  have hc_ne : c ≠ 0 := fun hc0 ↦ ha_ne <| star_mul_self_eq_zero.mp <| by
    rw [ha2_star, hc0, zero_smul]
  -- Rescale `a` by `c⁻¹` to obtain the minimal star projection `p`.
  set p : B := c⁻¹ • a
  have hp_proj : IsStarProjection p := ⟨by
    rw [IsIdempotentElem]
    calc
      p * p = (c⁻¹ * (c⁻¹ * c)) • a := by
        simp only [p, smul_mul_assoc, mul_smul_comm, smul_smul, ha_sq]
      _ = p := by rw [inv_mul_cancel₀ hc_ne, mul_one],
    by rw [IsSelfAdjoint, star_smul, ha_sa.star_eq, star_inv₀, hc_conj]⟩
  have hpq : p * q = p := by simp only [p, a, smul_mul_assoc, mul_assoc, hq.eq]
  have hqp : q * p = q := by
    calc
      q * p = c⁻¹ • (q * Star.star q * q) := by
        simp only [p, a, mul_smul_comm]; rw [← mul_assoc]
      _ = (c⁻¹ * c) • q := by rw [hcorner (Star.star q), smul_smul]
      _ = q := by rw [inv_mul_cancel₀ hc_ne, one_smul]
  have hp_ne : p ≠ 0 := fun hp0 ↦ hq_ne (by rw [← hqp, hp0, mul_zero])
  let ψ : B →ₗ[ℂ] ℂ :=
    { toFun b := c⁻¹ * φ (b * Star.star q)
      map_add' b₁ b₂ := by simp [add_mul, mul_add]
      map_smul' r b := by simp [smul_mul_assoc, mul_left_comm] }
  have hp_corner (b : B) : p * b * p = ψ b • p := by
    have haba : a * b * a = φ (b * Star.star q) • a := by
      calc
        a * b * a = Star.star q * (q * (b * Star.star q) * q) := by simp only [a, mul_assoc]
        _ = φ (b * Star.star q) • a := by rw [hcorner (b * Star.star q), mul_smul_comm]
    calc
      p * b * p = (c⁻¹ * c⁻¹) • (a * b * a) := by
        simp only [p, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = ψ b • p := by rw [haba, smul_smul, smul_smul, mul_right_comm]; rfl
  exact ⟨p, ψ, hp_proj, hp_ne, hp_corner, hpq, hqp⟩

namespace TauCeti

/-- The principal left ideal `{x : B | x * p = x}` of elements fixed on the right by `p`, bundled as
an `R`-submodule of `B`. -/
def leftIdealSubmodule (R : Type*) [Semiring R] {B : Type*} [NonUnitalNonAssocSemiring B]
    [Module R B] [IsScalarTower R B B] (p : B) : Submodule R B where
  carrier := {x : B | x * p = x}
  add_mem' {x y} hx hy := by dsimp at hx hy ⊢; rw [add_mul, hx, hy]
  zero_mem' := zero_mul p
  smul_mem' r {x} hx := by dsimp at hx ⊢; rw [smul_mul_assoc, hx]

@[simp]
theorem mem_leftIdealSubmodule {R : Type*} [Semiring R] {B : Type*}
    [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] {p x : B} :
    x ∈ leftIdealSubmodule R p ↔ x * p = x :=
  Iff.rfl

/-- In a Hausdorff topological semiring with continuous multiplication, `leftIdealSubmodule R p` is
closed. -/
instance isClosed_leftIdealSubmodule {R : Type*} [Semiring R] {B : Type*} [TopologicalSpace B]
    [T2Space B] [NonUnitalNonAssocSemiring B] [ContinuousMul B] [Module R B]
    [IsScalarTower R B B] (p : B) : IsClosed (leftIdealSubmodule R p : Set B) := by
  have hset : (leftIdealSubmodule R p : Set B) = {x : B | x * p = x} :=
    Set.ext fun _ ↦ mem_leftIdealSubmodule
  rw [hset]
  exact isClosed_eq (by fun_prop) continuous_id

end TauCeti

namespace IsStarProjection

/-- For `x, y` in `TauCeti.leftIdealSubmodule R p` of a star projection `p` with scalar corner
`p * b * p = ψ b • p`, the product `star x * y` lies in `R • p`. -/
theorem star_mul_of_mem_leftIdealSubmodule {R B : Type*} [Semiring R] [NonUnitalSemiring B]
    [StarRing B] [Module R B] [IsScalarTower R B B] {p : B} (hp : IsStarProjection p)
    {ψ : B →ₗ[R] R} (hcorner : ∀ b : B, p * b * p = ψ b • p)
    (x y : TauCeti.leftIdealSubmodule R p) :
    star (x : B) * (y : B) = ψ (star (x : B) * (y : B)) • p := by
  have hx : p * star (x : B) = star (x : B) := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using
      congrArg star (TauCeti.mem_leftIdealSubmodule.mp x.2)
  calc
    star (x : B) * (y : B) = p * (star (x : B) * (y : B)) * p := by
      rw [← mul_assoc, hx, mul_assoc, TauCeti.mem_leftIdealSubmodule.mp y.2]
    _ = ψ (star (x : B) * (y : B)) • p := hcorner _

-- `InnerProductSpace` extends `NormedSpace`; `@[expose]` lets `toNormedSpace` reduce to
-- `Submodule.normedSpace` across modules, matching Lean's automatic exposure on `instance`s.
/-- Equip `TauCeti.leftIdealSubmodule ℂ p` with the `p`-valued complex inner product
`⟪x, y⟫ = ψ (star x * y)` compatible with the C⋆-norm inherited from `B`. -/
@[expose, instance_reducible]
noncomputable def leftIdealInnerProductSpace {B : Type*} [NonUnitalCStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) {ψ : B →ₗ[ℂ] ℂ}
    (hcorner : ∀ b : B, p * b * p = ψ b • p) :
    InnerProductSpace ℂ (TauCeti.leftIdealSubmodule ℂ p) where
  inner x y := ψ (star (x : B) * (y : B))
  norm_sq_eq_re_inner x := by
    let _ := CStarAlgebra.spectralOrder B
    have _ := CStarAlgebra.spectralOrderedRing B
    have hp_pos : 0 < p := lt_of_le_of_ne hp.nonneg hp_ne.symm
    set z : ℂ := ψ (star (x : B) * (x : B))
    have hxx : star (x : B) * (x : B) = z • p :=
      hp.star_mul_of_mem_leftIdealSubmodule hcorner x x
    have hz_nonneg : 0 ≤ z :=
      nonneg_of_smul_nonneg_of_pos_right (hxx ▸ star_mul_self_nonneg (x : B)) hp_pos
    have ⟨hz_re, hz_im⟩ := Complex.nonneg_iff.mp hz_nonneg
    have hz_eq : (z.re : ℂ) = z := RCLike.re_eq_self_of_im_eq_zero (K := ℂ) hz_im.symm
    calc
      ‖x‖ ^ 2 = ‖(x : B)‖ * ‖(x : B)‖ := sq ‖(x : B)‖
      _ = ‖star (x : B) * (x : B)‖ := CStarRing.norm_star_mul_self.symm
      _ = ‖(z.re : ℂ) • p‖ := by conv_lhs => rw [hxx, ← hz_eq]
      _ = ‖(z.re : ℂ)‖ * ‖p‖ := norm_smul _ _
      _ = z.re := by
        rw [hp.norm_eq_one hp_ne, mul_one, Complex.norm_real, Real.norm_of_nonneg hz_re]
  conj_inner_symm x y := by
    apply smul_left_injective ℂ hp_ne
    have h1 := congrArg star (hp.star_mul_of_mem_leftIdealSubmodule hcorner y x)
    rw [star_mul, star_star, star_smul, hp.isSelfAdjoint.star_eq, Complex.star_def] at h1
    exact h1.symm.trans (hp.star_mul_of_mem_leftIdealSubmodule hcorner x y)
  add_left x y w := by simp [star_add, add_mul]
  smul_left x y r := by simp [star_smul, smul_mul_assoc]

/-- Bounded left multiplication of a `NonUnitalCStarAlgebra B` on the Hilbert space
`TauCeti.leftIdealSubmodule ℂ p` of a nonzero minimal star projection `p`, bundled as a
`NonUnitalStarAlgHom`. -/
noncomputable def leftMulNonUnitalStarAlgHom {B : Type*} [NonUnitalCStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) {ψ : B →ₗ[ℂ] ℂ}
    (hcorner : ∀ b : B, p * b * p = ψ b • p) :
    letI := hp.leftIdealInnerProductSpace hp_ne hcorner
    B →⋆ₙₐ[ℂ] (TauCeti.leftIdealSubmodule ℂ p →L[ℂ] TauCeti.leftIdealSubmodule ℂ p) :=
  letI := hp.leftIdealInnerProductSpace hp_ne hcorner
  let leftMul (b : B) : TauCeti.leftIdealSubmodule ℂ p →L[ℂ] TauCeti.leftIdealSubmodule ℂ p :=
    LinearMap.mkContinuous
      { toFun x := ⟨b * x.1, by
          rw [TauCeti.mem_leftIdealSubmodule, mul_assoc, TauCeti.mem_leftIdealSubmodule.mp x.2]⟩
        map_add' x y := Subtype.ext (mul_add b x.1 y.1)
        map_smul' r x := Subtype.ext (mul_smul_comm r b x.1) }
      ‖b‖ fun x ↦ norm_mul_le b x.1
  { toFun := leftMul
    map_smul' r b := by ext x : 2; exact smul_mul_assoc r b x.1
    map_zero' := by ext x : 2; exact zero_mul x.1
    map_add' a b := by ext x : 2; exact add_mul a b x.1
    map_mul' a b := by ext x : 2; exact mul_assoc a b x.1
    map_star' b := by
      refine (ContinuousLinearMap.eq_adjoint_iff (leftMul (star b)) (leftMul b)).mpr fun x y ↦
        smul_left_injective ℂ hp_ne ?_
      change ψ (star (leftMul (star b) x : B) * (y : B)) • p =
        ψ (star (x : B) * (leftMul b y : B)) • p
      rw [← hp.star_mul_of_mem_leftIdealSubmodule hcorner (leftMul (star b) x) y,
        ← hp.star_mul_of_mem_leftIdealSubmodule hcorner x (leftMul b y)]
      change star (star b * x.1) * y.1 = star x.1 * (b * y.1)
      rw [star_mul, star_star, mul_assoc] }

@[simp]
theorem coe_leftMulNonUnitalStarAlgHom_apply {B : Type*} [NonUnitalCStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) {ψ : B →ₗ[ℂ] ℂ}
    (hcorner : ∀ b : B, p * b * p = ψ b • p)
    (b : B) (x : TauCeti.leftIdealSubmodule ℂ p) :
    letI := hp.leftIdealInnerProductSpace hp_ne hcorner
    ((hp.leftMulNonUnitalStarAlgHom hp_ne hcorner b x : TauCeti.leftIdealSubmodule ℂ p) : B) =
      b * x.1 :=
  (rfl)

/-- Bounded left multiplication of a unital `CStarAlgebra B` on the Hilbert space
`TauCeti.leftIdealSubmodule ℂ p` of a nonzero minimal star projection `p`, bundled as a unital
`StarAlgHom`. -/
noncomputable def leftMulStarAlgHom {B : Type*} [CStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) {ψ : B →ₗ[ℂ] ℂ}
    (hcorner : ∀ b : B, p * b * p = ψ b • p) :
    letI := hp.leftIdealInnerProductSpace hp_ne hcorner
    B →⋆ₐ[ℂ] (TauCeti.leftIdealSubmodule ℂ p →L[ℂ] TauCeti.leftIdealSubmodule ℂ p) :=
  letI := hp.leftIdealInnerProductSpace hp_ne hcorner
  let φ := hp.leftMulNonUnitalStarAlgHom hp_ne hcorner
  { φ with
    map_one' := by ext x : 2; exact one_mul x.1
    commutes' r := by ext x : 2; exact (Algebra.smul_def r x.1).symm }

@[simp]
theorem coe_leftMulStarAlgHom_apply {B : Type*} [CStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) {ψ : B →ₗ[ℂ] ℂ}
    (hcorner : ∀ b : B, p * b * p = ψ b • p)
    (b : B) (x : TauCeti.leftIdealSubmodule ℂ p) :
    letI := hp.leftIdealInnerProductSpace hp_ne hcorner
    ((hp.leftMulStarAlgHom hp_ne hcorner b x : TauCeti.leftIdealSubmodule ℂ p) : B) = b * x.1 :=
  (rfl)

end IsStarProjection
