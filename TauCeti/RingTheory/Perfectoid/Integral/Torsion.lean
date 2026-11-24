/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.RingTheory.Perfectoid.Integral.Tilt

/-!
# Torsion of an integral perfectoid ring and of its tilt

Let `A` be a nonzero integral perfectoid ring (`TauCeti.Perfectoid.IsIntegralPerfectoid`), with
tilt `A♭ = PreTilt A p`, sharp map `x ↦ x♯ = x.untilt` and Fontaine's map `θ : W(A♭) → A`. No
torsion-freeness is assumed. This file shows that the sharp map identifies torsion in the tilt with
torsion in `A`: if `t : A♭` has `t♯` associated to a divisor `π` of `p`, then `x ↦ x♯` restricts to
an additive isomorphism `A♭[t] ≃+ A[π]` between the `t`-torsion of `A♭` and the `π`-torsion of `A`
(Česnavičius–Scholze, *Purity for flat cohomology*, (2.1.2.5)).

Two cases are singled out there. If `ξ` generates `ker θ`, its zeroth Witt coordinate `ξ₀ = p♭`
has `(p♭)♯` associated to `p`
(`TauCeti.Perfectoid.IsIntegralPerfectoid.associated_untilt_coeff_zero`, in
`TauCeti.RingTheory.Perfectoid.Integral.Tilt`), so `A♭[p♭] ≅ A[p]`. If `A` is
`ϖ`-adically complete with `ϖ ^ p ∣ p` and `ϖ` is associated to `(ϖ♭)♯`, then `A♭[ϖ♭] ≅ A[ϖ]`; in
particular `A♭` is `ϖ♭`-torsion-free if and only if `A` is `ϖ`-torsion-free.

The sharp map is multiplicative but not additive on `A♭`. Fix a generator `ξ = [ξ₀] + p u` of
`ker θ`; it is distinguished, so `u` is a unit, and `t ∣ ξ₀` because `t♯ ∣ p`
(`dvd_coeff_zero_of_ker_fontaineTheta_eq_span`). Everything happens inside `A♭[ξ₀]`:

* If `[ξ₀] w = 0` in `W(A♭)`, then `ξ w = p u w` lies in `ker θ`, so `p θ(w) = 0`.
* For `a, b ∈ A♭[ξ₀]`, the defect `[a + b] - [a] - [b]` has vanishing zeroth Witt coordinate, so it
  is `p w` with `[ξ₀] w = 0` (since `p` is a nonzerodivisor of `W(A♭)`), and
  `(a + b)♯ - a♯ - b♯ = θ(p w) = 0`.
* If `a ∈ A♭[ξ₀]` and `a♯ = 0`, then `[a] ∈ (ξ)`, so `ξ₀ ∣ a` and `a ^ 2 = 0`; as `A♭` is perfect,
  hence reduced, `a = 0`.
* If `p y = 0` in `A`, write `y = θ(w)` and `p w = z ξ` with `z = [z₀] + p z'`. Comparing zeroth
  Witt coordinates gives `ξ₀ z₀ = 0`, and cancelling `p` gives `w = u [z₀] + z' ξ`, so
  `y = θ(u) z₀♯ = (u₀ z₀)♯`, since `θ(u) ≡ u₀♯` modulo `p`.

The isomorphism is linear over `A_inf(A) = W(A♭)`, which acts on `A♭` through the zeroth Witt
coordinate and on `A` through `θ` (`PreTilt.torsionByEquiv_coeff_zero_smul`): `p` kills `A[π]`, and
`θ(w) ≡ (w₀)♯` modulo `p` (`WittVector.natCast_dvd_fontaineTheta_sub_untilt`).

## Main definitions

* `PreTilt.torsionByEquiv`: for `t♯` associated to `π` and `π ∣ p`, the sharp map
  `A♭[t] ≃+ A[π]`.

## Main results

* `PreTilt.coe_torsionByEquiv_apply`, `PreTilt.untilt_torsionByEquiv_symm_apply`:
  `PreTilt.torsionByEquiv` is the sharp map.
* `PreTilt.torsionByEquiv_coeff_zero_smul`: `PreTilt.torsionByEquiv` is `W(A♭)`-linear.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.isSMulRegular_iff_isSMulRegular_untilt`: for
  `t♯ ∣ p`, `A♭` is `t`-torsion-free if and only if `A` is `t♯`-torsion-free.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, (2.1.2.5).
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Remark 3.11.
-/

public section

open Ideal WittVector

namespace TauCeti.Perfectoid.IsIntegralPerfectoid

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsIntegralPerfectoid p A]
  [Fact ¬IsUnit (p : A)]

section Generator

variable {ξ : WittVector p (PreTilt A p)} (hξ : RingHom.ker (fontaineTheta A p) = span {ξ})
include hξ

/-- If `[ξ₀] w = 0`, then `p` kills `θ(w)`: with `ξ = [ξ₀] + p u`, `ξ w = p u w` lies in `ker θ`,
so `p θ(u) θ(w) = 0`, and `θ(u)` is a unit. -/
private theorem natCast_mul_fontaineTheta_eq_zero {w : WittVector p (PreTilt A p)}
    (hw : teichmuller p (ξ.coeff 0) * w = 0) : (p : A) * fontaineTheta A p w = 0 := by
  have hξk : ξ ∈ RingHom.ker (fontaineTheta A p) := hξ ▸ mem_span_singleton_self ξ
  obtain ⟨u, hu⟩ :=
    isDistinguished_iff_exists_unit.mp (isDistinguished_of_ker_fontaineTheta_eq_span hξ)
  have h : fontaineTheta A p (ξ * w) = 0 := RingHom.mem_ker.mp (mul_mem_right w _ hξk)
  rw [hu, add_mul, hw, zero_add, map_mul, map_mul, map_natCast] at h
  have hθu : IsUnit (fontaineTheta A p u) := u.isUnit.map _
  rw [← hθu.mul_right_eq_zero]
  linear_combination h

/-- **The sharp map is additive on `ξ₀`-torsion.** -/
private theorem untilt_add_of_coeff_zero_mul_eq_zero {a b : PreTilt A p} (ha : ξ.coeff 0 * a = 0)
    (hb : ξ.coeff 0 * b = 0) : (a + b).untilt = a.untilt + b.untilt := by
  -- The defect `[a + b] - [a] - [b]` has vanishing zeroth Witt coordinate, so it is `p w`.
  obtain ⟨w, hw⟩ := mem_span_singleton.mp
    ((mem_span_p_iff_coeff_zero_eq_zero
      (teichmuller p (a + b) - teichmuller p a - teichmuller p b)).mpr (by
        simp [sub_coeff_zero, teichmuller_coeff_zero]))
  -- `[ξ₀]` kills `p w`, hence `w`.
  have hξw : teichmuller p (ξ.coeff 0) * w = 0 := by
    refine (mul_cancel_left_mem_nonZeroDivisors (p_mem_nonZeroDivisors (R := PreTilt A p))).mp ?_
    rw [mul_zero, mul_left_comm, ← hw]
    simp [mul_sub, ← map_mul, mul_add, ha, hb]
  have h := congrArg (fontaineTheta A p) hw
  rw [map_sub, map_sub, fontaineTheta_teichmuller, fontaineTheta_teichmuller,
    fontaineTheta_teichmuller, map_mul, map_natCast,
    natCast_mul_fontaineTheta_eq_zero hξ hξw] at h
  linear_combination h

/-- **The sharp map is injective on `ξ₀`-torsion.** If `ξ₀ a = 0` and `a♯ = 0`, then `[a] ∈ (ξ)`,
so `ξ₀ ∣ a` and `a ^ 2 = 0`; the tilt is perfect, hence reduced. -/
private theorem eq_zero_of_coeff_zero_mul_eq_zero_of_untilt_eq_zero {a : PreTilt A p}
    (ha : ξ.coeff 0 * a = 0) (h : a.untilt = 0) : a = 0 := by
  have := TauCeti.isReduced_of_perfectRing (PreTilt A p) p
  have hmem : teichmuller p a ∈ span {ξ} := by
    rw [← hξ, RingHom.mem_ker, fontaineTheta_teichmuller, h]
  obtain ⟨z, hz⟩ := mem_span_singleton'.mp hmem
  have hcoeff := congrArg (WittVector.coeff · 0) hz
  simp only [mul_coeff_zero, teichmuller_coeff_zero] at hcoeff
  exact IsReduced.eq_zero a ⟨2, by linear_combination -a * hcoeff + z.coeff 0 * ha⟩

/-- **The sharp map is onto `p`-torsion from `ξ₀`-torsion.** If `p y = 0`, write `y = θ(w)` and
`p w = z ξ` with `z = [z₀] + p z'`; then `ξ₀ z₀ = 0` and `w = u [z₀] + z' ξ`, so
`y = θ(u) z₀♯ = (u₀ z₀)♯`. -/
private theorem exists_untilt_eq_of_natCast_mul_eq_zero {y : A} (hy : (p : A) * y = 0) :
    ∃ a : PreTilt A p, ξ.coeff 0 * a = 0 ∧ a.untilt = y := by
  have hξk : ξ ∈ RingHom.ker (fontaineTheta A p) := hξ ▸ mem_span_singleton_self ξ
  obtain ⟨u, hu⟩ :=
    isDistinguished_iff_exists_unit.mp (isDistinguished_of_ker_fontaineTheta_eq_span hξ)
  obtain ⟨w, rfl⟩ := surjective_fontaineTheta (p := p) y
  have hpw : (p : WittVector p (PreTilt A p)) * w ∈ span {ξ} := by
    rw [← hξ, RingHom.mem_ker, map_mul, map_natCast, hy]
  obtain ⟨z, hz⟩ := mem_span_singleton'.mp hpw
  obtain ⟨z', hz'⟩ := mem_span_singleton.mp
    ((mem_span_p_iff_coeff_zero_eq_zero (z - teichmuller p (z.coeff 0))).mpr (by
      simp [sub_coeff_zero, teichmuller_coeff_zero]))
  -- Zeroth Witt coordinates: `z₀ ξ₀ = (p w)₀ = 0`.
  have hz₀ : ξ.coeff 0 * z.coeff 0 = 0 := by
    rw [mul_comm, ← mul_coeff_zero, hz,
      (mem_span_p_iff_coeff_zero_eq_zero _).mp (mem_span_singleton.mpr (dvd_mul_right _ w))]
  have hξz : teichmuller p (ξ.coeff 0) * teichmuller p (z.coeff 0) = 0 := by
    rw [← map_mul, hz₀, teichmuller_zero]
  -- Cancelling `p` from `p w = z ξ` gives `w = u [z₀] + z' ξ`.
  have hw : w = ↑u * teichmuller p (z.coeff 0) + z' * ξ := by
    refine (mul_cancel_left_mem_nonZeroDivisors (p_mem_nonZeroDivisors (R := PreTilt A p))).mp ?_
    linear_combination -hz + ξ * hz' + teichmuller p (z.coeff 0) * hu + hξz
  -- So `y = θ(u) z₀♯`, and `θ(u) ≡ u₀♯` modulo `p`, which kills `z₀♯`.
  have hpz := natCast_mul_fontaineTheta_eq_zero hξ hξz
  rw [fontaineTheta_teichmuller] at hpz
  obtain ⟨c, hc⟩ := natCast_dvd_fontaineTheta_sub_untilt (u : WittVector p (PreTilt A p))
  refine ⟨(u : WittVector p (PreTilt A p)).coeff 0 * z.coeff 0, by
    rw [mul_left_comm, hz₀, mul_zero], ?_⟩
  rw [hw, map_add, map_mul (fontaineTheta A p), map_mul (fontaineTheta A p),
    RingHom.mem_ker.mp hξk, mul_zero, add_zero, fontaineTheta_teichmuller, map_mul PreTilt.untilt]
  linear_combination -(z.coeff 0).untilt * hc - c * hpz

end Generator

section Torsion

variable {t : PreTilt A p} (ht : t.untilt ∣ (p : A))
include ht

/-- If `t♯ ∣ p`, the `t`-torsion of the tilt lies in its `ξ₀`-torsion for every generator `ξ` of
`ker θ`, since `t ∣ ξ₀`. -/
private theorem coeff_zero_mul_eq_zero {ξ : WittVector p (PreTilt A p)}
    (hξ : RingHom.ker (fontaineTheta A p) = span {ξ}) {a : PreTilt A p} (ha : t * a = 0) :
    ξ.coeff 0 * a = 0 := by
  obtain ⟨c, hc⟩ := dvd_coeff_zero_of_ker_fontaineTheta_eq_span hξ ht
  rw [hc, mul_right_comm, ha, zero_mul]

/-- **The sharp map is additive on `t`-torsion** when `t♯ ∣ p`. -/
private theorem untilt_add_of_mul_eq_zero {a b : PreTilt A p} (ha : t * a = 0) (hb : t * b = 0) :
    (a + b).untilt = a.untilt + b.untilt := by
  obtain ⟨ξ, -, hξ⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := A)
  exact untilt_add_of_coeff_zero_mul_eq_zero hξ (coeff_zero_mul_eq_zero ht hξ ha)
    (coeff_zero_mul_eq_zero ht hξ hb)

/-- **The sharp map is injective on `t`-torsion** when `t♯ ∣ p`. -/
private theorem eq_zero_of_mul_eq_zero_of_untilt_eq_zero {a : PreTilt A p} (ha : t * a = 0)
    (h : a.untilt = 0) : a = 0 := by
  obtain ⟨ξ, -, hξ⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := A)
  exact eq_zero_of_coeff_zero_mul_eq_zero_of_untilt_eq_zero hξ (coeff_zero_mul_eq_zero ht hξ ha) h

/-- **Every `t♯`-torsion element of `A` is a sharp of `t`-torsion** when `t♯ ∣ p`. -/
private theorem exists_mul_eq_zero_untilt_eq {y : A} (hy : t.untilt * y = 0) :
    ∃ a : PreTilt A p, t * a = 0 ∧ a.untilt = y := by
  obtain ⟨ξ, -, hξ⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := A)
  obtain ⟨c, hc⟩ := ht
  obtain ⟨a, hξa, rfl⟩ := exists_untilt_eq_of_natCast_mul_eq_zero hξ
    (by rw [hc, mul_right_comm, hy, zero_mul])
  -- `t a` lies in the `ξ₀`-torsion and has sharp `t♯ a♯ = 0`, so it vanishes.
  refine ⟨a, eq_zero_of_coeff_zero_mul_eq_zero_of_untilt_eq_zero hξ
    (by rw [mul_left_comm, hξa, mul_zero]) (by rw [map_mul, hy]), rfl⟩

end Torsion

end TauCeti.Perfectoid.IsIntegralPerfectoid

namespace PreTilt

open TauCeti.Perfectoid IsIntegralPerfectoid

/-- In a commutative ring `R`, `x` lies in the `a`-torsion `R[a]` exactly when `a * x = 0`: the
scalar action of `R` on itself is multiplication. -/
private theorem mem_torsionBy_self_iff {R : Type*} [CommRing R] {a x : R} :
    x ∈ Submodule.torsionBy R R a ↔ a * x = 0 := by
  rw [Submodule.mem_torsionBy_iff, smul_eq_mul]

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsIntegralPerfectoid p A]
  [Fact ¬IsUnit (p : A)] {t : PreTilt A p} {π : A}

/-- **Torsion of an integral perfectoid ring and of its tilt** (Česnavičius–Scholze, *Purity for
flat cohomology*, (2.1.2.5)). If `t : A♭` has `t♯` associated to a divisor `π` of `p`, the sharp
map `x ↦ x♯` restricts to an additive isomorphism from the `t`-torsion of `A♭` to the `π`-torsion
of `A` (`PreTilt.coe_torsionByEquiv_apply`), linear over `W(A♭)`
(`PreTilt.torsionByEquiv_coeff_zero_smul`). With `t = p♭` this is `A♭[p♭] ≅ A[p]`; with `t = ϖ♭`
for `ϖ` associated to `(ϖ♭)♯` and `ϖ ^ p ∣ p` it is `A♭[ϖ♭] ≅ A[ϖ]`. -/
noncomputable def torsionByEquiv (ht : Associated t.untilt π) (hπ : π ∣ (p : A)) :
    Submodule.torsionBy (PreTilt A p) (PreTilt A p) t ≃+ Submodule.torsionBy A A π :=
  have htp : t.untilt ∣ (p : A) := ht.dvd.trans hπ
  have hmem (x : PreTilt A p) (hx : t * x = 0) : π * x.untilt = 0 := by
    obtain ⟨u, rfl⟩ := ht
    rw [mul_right_comm, ← map_mul, hx, untilt_zero, zero_mul]
  let f : Submodule.torsionBy (PreTilt A p) (PreTilt A p) t →+ Submodule.torsionBy A A π :=
    AddMonoidHom.mk' (fun x ↦ ⟨(x : PreTilt A p).untilt,
      mem_torsionBy_self_iff.mpr (hmem x (mem_torsionBy_self_iff.mp x.property))⟩) fun x y ↦
      Subtype.ext (untilt_add_of_mul_eq_zero htp (mem_torsionBy_self_iff.mp x.property)
        (mem_torsionBy_self_iff.mp y.property))
  AddEquiv.ofBijective f
    ⟨(injective_iff_map_eq_zero f).mpr fun x hx ↦ Subtype.ext
      (eq_zero_of_mul_eq_zero_of_untilt_eq_zero htp (mem_torsionBy_self_iff.mp x.property)
        (congrArg Subtype.val hx)),
    fun y ↦ by
      obtain ⟨u, rfl⟩ := ht
      obtain ⟨x, hx, hxy⟩ := exists_mul_eq_zero_untilt_eq htp (y := y) (by
        have hy := mem_torsionBy_self_iff.mp y.property
        rw [mul_right_comm, u.mul_left_eq_zero] at hy
        exact hy)
      exact ⟨⟨x, mem_torsionBy_self_iff.mpr hx⟩, Subtype.ext hxy⟩⟩

/-- `PreTilt.torsionByEquiv` is the sharp map. -/
@[simp]
theorem coe_torsionByEquiv_apply (ht : Associated t.untilt π) (hπ : π ∣ (p : A))
    (x : Submodule.torsionBy (PreTilt A p) (PreTilt A p) t) :
    (torsionByEquiv ht hπ x : A) = (x : PreTilt A p).untilt :=
  (rfl)

/-- The inverse of `PreTilt.torsionByEquiv` is a section of the sharp map. -/
@[simp]
theorem untilt_torsionByEquiv_symm_apply (ht : Associated t.untilt π) (hπ : π ∣ (p : A))
    (y : Submodule.torsionBy A A π) :
    ((torsionByEquiv ht hπ).symm y : PreTilt A p).untilt = y := by
  rw [← coe_torsionByEquiv_apply ht hπ, AddEquiv.apply_symm_apply]

/-- **`PreTilt.torsionByEquiv` is linear over `A_inf(A) = W(A♭)`**, which acts on `A♭` through
the zeroth Witt coordinate and on `A` through Fontaine's map `θ`. Indeed `p` kills the `π`-torsion
of `A`, and `θ(w) ≡ (w₀)♯` modulo `p`. -/
theorem torsionByEquiv_coeff_zero_smul (ht : Associated t.untilt π) (hπ : π ∣ (p : A))
    (w : WittVector p (PreTilt A p)) (x : Submodule.torsionBy (PreTilt A p) (PreTilt A p) t) :
    torsionByEquiv ht hπ (w.coeff 0 • x) =
      WittVector.fontaineTheta A p w • torsionByEquiv ht hπ x := by
  obtain ⟨c, hc⟩ := WittVector.natCast_dvd_fontaineTheta_sub_untilt w
  obtain ⟨d, hd⟩ := hπ
  have hx : π * (x : PreTilt A p).untilt = 0 :=
    mem_torsionBy_self_iff.mp (torsionByEquiv ht ⟨d, hd⟩ x).property
  ext
  simp only [coe_torsionByEquiv_apply, Submodule.coe_smul, smul_eq_mul, map_mul]
  linear_combination
    -(x : PreTilt A p).untilt * hc - c * d * hx - c * (x : PreTilt A p).untilt * hd

end PreTilt

namespace TauCeti.Perfectoid.IsIntegralPerfectoid

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsIntegralPerfectoid p A]
  [Fact ¬IsUnit (p : A)]

/-- **Torsion-freeness transfers along tilting** (Česnavičius–Scholze, *Purity for flat
cohomology*, (2.1.2.5)). If `t : A♭` has `t♯ ∣ p`, then `A♭` is `t`-torsion-free if and only if `A`
is `t♯`-torsion-free. For instance `A♭` is `ϖ♭`-torsion-free if and only if `A` is
`(ϖ♭)♯`-torsion-free. -/
theorem isSMulRegular_iff_isSMulRegular_untilt {t : PreTilt A p} (ht : t.untilt ∣ (p : A)) :
    IsSMulRegular (PreTilt A p) t ↔ IsSMulRegular A t.untilt := by
  rw [isSMulRegular_iff_torsionBy_eq_bot, isSMulRegular_iff_torsionBy_eq_bot,
    ← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (PreTilt.torsionByEquiv (Associated.refl _) ht).subsingleton_congr

end TauCeti.Perfectoid.IsIntegralPerfectoid
