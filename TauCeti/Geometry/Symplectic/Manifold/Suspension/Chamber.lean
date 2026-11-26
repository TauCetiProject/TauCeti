/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.HyperbolicPair
import TauCeti.LinearAlgebra.QuadraticForm.LightCone

/-!
# Line labels and chambers of a symplectic suspension with `b₁ = 1`

Let `φ` be an area-preserving diffeomorphism of a closed connected oriented surface `F` of genus
`g`, let `Y_φ` be its mapping torus, with `b₁(Y_φ) = 1`, and let `X = (ℝ / ℤ)_s × Y_φ` carry the
symplectic form `Ω = ds ∧ dt + ω_v`. Choose a lift `v ∈ H²(Y_φ; ℤ)` with `⟨v, [F]⟩ = 1`, pulled
back to `X`, and put `t = [ds ∧ dt]`. Their intersection numbers are those of a hyperbolic pair:

`v · v = 0`, `t · t = 0`, `v · t = t · v = 1`.

Modulo torsion the canonical class is `κ = (2g - 2) v` and the cohomology class of the
symplectic form is `[Ω] = t + L v` with `L > 0`. A Seiberg–Witten line label `e ∈ H²(X; ℤ)` is
written `e = a v + c t` modulo torsion, and `q = a + 1 - g`. The determinant line of the twisted
`Spinᶜ` structure has class `l = 2e - κ`, and the real dimension of its moduli space is
`d(e) = e · e - κ · e`. This file proves the numerical identities

`l = 2q v + 2c t` (modulo torsion),  `d(e) = 2cq`,  `l · t = 2q`,  `l · [Ω] = 2(q + L c)`,

and that `l · [Ω]` has the sign of `c` when `c ≠ 0` and `d(e) ≥ 0`. A pullback label `p^* e_Y`
has `c = 0` and so `d(e) = 0`.

The Seiberg–Witten wall coordinate of the unperturbed equations for a metric `g` is
`w(g, 0) = -2π l · [ω_g]`, where `ω_g` is a self-dual harmonic form, normalized so that `[ω_g]`
pairs positively with `[Ω]`. When `g` is compatible with `Ω`, `ω_g` is a positive multiple of `Ω`.
For an arbitrary metric, such as a product metric `ds² + g_Y` with any metric `g_Y` on `Y_φ`,
`ω_g` need not be a multiple of `Ω`, but `[ω_g]` still has positive square and lies in the same
half of the positive cone as `[Ω]`. Since the
intersection form has `b₂⁺ = 1`
(`LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`) and
`l · l = 4 d(e) ≥ 0`, the light-cone lemma `QuadraticForm.sign_polar_eq_sign_polar` shows
that `l · [ω_g]` has the sign of `c` as well. So, for every metric, the unperturbed equations of a
nonpullback label (`c ≠ 0`) of nonnegative dimension lie in the chamber where `w` has the sign of
`-c`.

Every class `x = a v + c t` (modulo torsion) also has even square `x · x = 2ac`
(`LinearMap.BilinForm.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub`). When `v` and `t` span
`H²(X; ℤ)` modulo torsion, the intersection form of `X` is therefore even
(`LinearMap.BilinForm.even_apply_self_of_isOfFinAddOrder_span`); in particular no class has
square `-1`.

The statements are about an arbitrary `ℤ`-valued bilinear form `B` on an abelian group `H`,
playing the role of the intersection form on `H²(X; ℤ)`. The statements take any `Module ℤ H`
instance, such as the one on a cohomology group, which agrees with the default
`AddCommGroup.toIntModule` only propositionally. Torsion is retained: the classes `e` and `κ` are
only assumed to agree with their coordinate expressions up to elements of finite order, which
every `ℤ`-valued bilinear form annihilates.

## Main results

* `TauCeti.SmoothMappingTorus.isOfFinAddOrder_two_smul_sub_sub`: `l = 2q v + 2c t` modulo
  torsion.
* `TauCeti.SmoothMappingTorus.apply_self_sub_apply_canonical_eq`: `d(e) = 2cq`.
* `TauCeti.SmoothMappingTorus.apply_two_smul_sub_right_eq`: `l · t = 2q`.
* `TauCeti.SmoothMappingTorus.apply_two_smul_sub_add_mul_apply_eq`: `l · [Ω] = 2(q + L c)`.
* `TauCeti.SmoothMappingTorus.sign_apply_two_smul_sub_add_mul_apply`: for `c ≠ 0`,
  `d(e) ≥ 0` and `L > 0`, the sign of `l · [Ω]` is the sign of `c`.
* `TauCeti.SmoothMappingTorus.sign_baseChange_tmul_two_smul_sub_apply`: under the same
  hypotheses, for a hyperbolic pair spanning `H` modulo torsion, the sign of `l · y` is the sign of
  `c` for every real class `y` with `y · y > 0` and `y · [Ω] > 0`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

open LinearMap (BilinForm)
open scoped TensorProduct

namespace TauCeti

namespace SmoothMappingTorus

variable {H : Type*} [AddCommGroup H] [Module ℤ H] {B : BilinForm ℤ H} {v t e κ : H} {a c g : ℤ}

omit [Module ℤ H] in
/-- The determinant class `l = 2e - κ` of the label `e = a v + c t` is `2q v + 2c t` modulo
torsion, where `κ = (2g - 2) v` and `q = a + 1 - g`. -/
theorem isOfFinAddOrder_two_smul_sub_sub (he : IsOfFinAddOrder (e - (a • v + c • t)))
    (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v)) :
    IsOfFinAddOrder ((2 : ℤ) • e - κ - ((2 * (a + 1 - g)) • v + (2 * c) • t)) := by
  have h := (he.zsmul (i := 2)).add hκ.neg
  convert h using 1
  simp only [smul_sub, smul_add, smul_smul, neg_sub, add_smul, sub_smul, mul_add, mul_sub,
    mul_one]
  abel

/-- The dimension `d(e) = e · e - κ · e` of the label `e = a v + c t` is `2cq`, where
`κ = (2g - 2) v` and `q = a + 1 - g`. -/
theorem apply_self_sub_apply_canonical_eq (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1)
    (htv : B t v = 1) (he : IsOfFinAddOrder (e - (a • v + c • t)))
    (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v)) :
    B e e - B κ e = 2 * c * (a + 1 - g) := by
  rw [B.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub hv ht hvt htv he,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_left hκ,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_right he]
  simp only [map_add, map_zsmul, LinearMap.smul_apply, smul_eq_mul, hv, hvt]
  ring

/-- The pairing of the determinant class `l = 2e - κ` with `t` is `l · t = 2q`, where
`e = a v + c t`, `κ = (2g - 2) v` and `q = a + 1 - g`. Only `t · t = 0` and `v · t = 1` are
needed. -/
theorem apply_two_smul_sub_right_eq (ht : B t t = 0) (hvt : B v t = 1)
    (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v)) :
    B ((2 : ℤ) • e - κ) t = 2 * (a + 1 - g) := by
  rw [B.apply_eq_apply_of_isOfFinAddOrder_sub_left (isOfFinAddOrder_two_smul_sub_sub he hκ)]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ht, hvt]
  ring

/-- The pairing of the determinant class `l = 2e - κ` with `[Ω] = t + L v` is `2(q + L c)`,
where `e = a v + c t`, `κ = (2g - 2) v` and `q = a + 1 - g`. The coefficient `L` lies in any
commutative ring, typically `ℝ`. -/
theorem apply_two_smul_sub_add_mul_apply_eq {R : Type*} [CommRing R] (hv : B v v = 0)
    (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v))
    (L : R) :
    (B ((2 : ℤ) • e - κ) t : R) + L * B ((2 : ℤ) • e - κ) v = 2 * ((a + 1 - g : ℤ) + L * c) := by
  rw [apply_two_smul_sub_right_eq ht hvt he hκ,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_left (isOfFinAddOrder_two_smul_sub_sub he hκ)]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv, htv]
  push_cast
  ring

/-- For a nonpullback label `e = a v + c t` (`c ≠ 0`) of nonnegative dimension, the pairing of
`l = 2e - κ` with `[Ω] = t + L v`, `L > 0`, has the sign of `c`. -/
theorem sign_apply_two_smul_sub_add_mul_apply {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v))
    (hc : c ≠ 0) (hd : 0 ≤ B e e - B κ e) {L : R} (hL : 0 < L) :
    SignType.sign ((B ((2 : ℤ) • e - κ) t : R) + L * B ((2 : ℤ) • e - κ) v) = SignType.sign c := by
  rw [apply_two_smul_sub_add_mul_apply_eq hv ht hvt htv he hκ]
  rw [apply_self_sub_apply_canonical_eq hv ht hvt htv he hκ] at hd
  rcases hc.lt_or_gt with hc | hc
  · have hq : a + 1 - g ≤ 0 := by nlinarith
    have hq' : ((a + 1 - g : ℤ) : R) ≤ 0 := by exact_mod_cast hq
    have hc' : (c : R) < 0 := by exact_mod_cast hc
    rw [sign_neg hc, sign_neg (by nlinarith)]
  · have hq : 0 ≤ a + 1 - g := by nlinarith
    have hq' : 0 ≤ ((a + 1 - g : ℤ) : R) := by exact_mod_cast hq
    have hc' : 0 < (c : R) := by exact_mod_cast hc
    rw [sign_pos hc, sign_pos (by nlinarith)]

/-- **The chamber of a nonpullback label is the same for every metric.** Let `v, t` be a
hyperbolic pair spanning `H` modulo torsion, and let `e = a v + c t` be a label with `c ≠ 0` and
`d(e) ≥ 0`. Let `y` be a class of `𝕜 ⊗[ℤ] H` with `y · y > 0` which pairs positively with
`[Ω] = t + L v`, `L > 0`; for `𝕜 = ℝ` this is the class `[ω_g]` of a self-dual harmonic form of
any metric `g`, normalized to pair positively with `[Ω]`. Then `l · y`, with `l = 2e - κ`, has the
sign of `c`.

In the wall coordinate `w(g, 0) = -2π l · [ω_g]` of the unperturbed equations, this says that
`w(g, 0)` has the sign of `-c` for every metric `g`. -/
theorem sign_baseChange_tmul_two_smul_sub_apply {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1)
    (htv : B t v = 1) (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t)))
    (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v))
    (hc : c ≠ 0) (hd : 0 ≤ B e e - B κ e) {L : 𝕜} (hL : 0 < L) {y : 𝕜 ⊗[ℤ] H}
    (hy : 0 < B.baseChange 𝕜 y y)
    (hyΩ : 0 < B.baseChange 𝕜 y ((1 : 𝕜) ⊗ₜ t + L • (1 : 𝕜) ⊗ₜ v)) :
    SignType.sign (B.baseChange 𝕜 ((1 : 𝕜) ⊗ₜ ((2 : ℤ) • e - κ)) y) = SignType.sign c := by
  set Bk := B.baseChange 𝕜
  set Q := Bk.toQuadraticMap
  set Ω := (1 : 𝕜) ⊗ₜ[ℤ] t + L • (1 : 𝕜) ⊗ₜ[ℤ] v
  have : FiniteDimensional 𝕜 (𝕜 ⊗[ℤ] H) := Module.finite_of_finrank_eq_succ
    (BilinForm.finrank_tensorProduct_eq_two_of_isOfFinAddOrder_span ht hvt htv hspan)
  have hsymm : Bk.IsSymm := BilinForm.isSymm_iff.mpr <| BilinForm.IsSymm.baseChange 𝕜 <|
    BilinForm.isSymm_iff.mp (BilinForm.isSymm_of_isOfFinAddOrder_span (hvt.trans htv.symm) hspan)
  have hpolar (x z : 𝕜 ⊗[ℤ] H) : QuadraticMap.polar Q x z = 2 * Bk x z := by
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hsymm.eq z x]
    ring
  have hone (x z : H) : Bk ((1 : 𝕜) ⊗ₜ x) ((1 : 𝕜) ⊗ₜ z) = B x z := by
    simp [Bk]
  have hl := isOfFinAddOrder_two_smul_sub_sub he hκ
  -- `l · l = 4 d(e) ≥ 0` and `l · v = 2c ≠ 0`.
  have hx : 0 ≤ Q ((1 : 𝕜) ⊗ₜ ((2 : ℤ) • e - κ)) := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hone,
      B.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub hv ht hvt htv hl]
    rw [apply_self_sub_apply_canonical_eq hv ht hvt htv he hκ] at hd
    exact_mod_cast (by nlinarith : (0 : ℤ) ≤ 2 * (2 * (a + 1 - g)) * (2 * c))
  have hx0 : (1 : 𝕜) ⊗ₜ[ℤ] ((2 : ℤ) • e - κ) ≠ 0 := by
    intro h0
    have h := hone ((2 : ℤ) • e - κ) v
    rw [h0, map_zero, LinearMap.zero_apply, B.apply_eq_apply_of_isOfFinAddOrder_sub_left hl] at h
    have h2 : 2 * c = 0 := by simpa [hv, htv] using h.symm
    omega
  have hΩ : 0 < Q Ω := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    simp only [Bk, Ω, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      BilinForm.baseChange_tmul, hv, ht, hvt, htv, smul_eq_mul, zero_smul, one_smul, mul_one]
    linarith
  have hxΩ : Bk ((1 : 𝕜) ⊗ₜ ((2 : ℤ) • e - κ)) Ω =
      (B ((2 : ℤ) • e - κ) t : 𝕜) + L * B ((2 : ℤ) • e - κ) v := by
    simp only [Bk, Ω, map_add, map_smul, BilinForm.baseChange_tmul, smul_eq_mul, mul_one,
      zsmul_eq_mul]
  -- Light-cone lemma for `B_𝕜`, of positive index one: since `l · l ≥ 0` and `l ≠ 0`, `l · y`
  -- has the same sign as `l · [Ω]`, which is the sign of `c`.
  have key := QuadraticForm.sign_polar_eq_sign_polar (Q := Q)
    (BilinForm.nondegenerate_toQuadraticMap_baseChange_of_isOfFinAddOrder_span ht hvt htv hspan)
    (BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span hv ht hvt htv
      hspan).le hx hx0 hΩ (z := y) (by rwa [LinearMap.BilinMap.toQuadraticMap_apply])
    (by rw [hpolar, hsymm.eq]; positivity)
  rw [hpolar, hpolar, sign_mul, sign_mul, hxΩ,
    sign_apply_two_smul_sub_add_mul_apply hv ht hvt htv he hκ hc hd hL] at key
  simpa using key.symm

end SmoothMappingTorus

end TauCeti
