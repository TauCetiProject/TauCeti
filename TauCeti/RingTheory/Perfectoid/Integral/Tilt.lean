/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Frobenius.RootClosure
public import TauCeti.RingTheory.Perfectoid.Integral.Basic

/-!
# An integral perfectoid ring and its tilt modulo divisors of `p`

Let `A` be a nonzero integral perfectoid ring (`TauCeti.Perfectoid.IsIntegralPerfectoid`), with
tilt `A♭ = PreTilt A p`, sharp map `x ↦ x♯ = x.untilt` and Fontaine's map `θ : W(A♭) → A`. No
nonzerodivisor hypothesis is made: `A` may have `p`-torsion and zero divisors. This file shows that
`A` and `A♭` agree modulo every divisor of `p` that is a sharp, and deduces that relative Frobenius
`A ⧸ π → A ⧸ π ^ p` is bijective.

* **Generators of `ker θ`.** The zeroth Witt coordinate of every element of `ker θ` lies in the
  Jacobson radical of `A♭` (`WittVector.coeff_zero_mem_jacobson_of_mem_ker_fontaineTheta`), so a
  distinguished multiple `y ξ` of an element `ξ ∈ ker θ` forces `y` to be a unit and `ξ` to be
  distinguished (`WittVector.isDistinguished_mul_iff_of_coeff_zero_mem_jacobson`). As `ker θ` is
  principal and contains a distinguished element, an element of `ker θ` generates it exactly when
  it is distinguished. A generator `ξ = [ξ₀] + p u` then has `(ξ₀)♯ = -p θ(u)`, a unit multiple of
  `p`, so `A♭` is `(ξ₀)`-adically complete and `ξ` is a nonzerodivisor of `W(A♭)`.
* **The tilt modulo `t`.** Let `t : A♭` with `t♯ ∣ p`, and let `g = [g₀] + p u` be a distinguished
  generator of `ker θ`. Comparing Witt coordinates modulo `t` in `p = z g + [t] w` shows `t ∣ g₀`.
  Hence `ker θ = (p + [t] α)` for some `α` and `ker θ + ([t]) = (p, [t])`, so
  `A ⧸ t♯ = W(A♭) ⧸ (ker θ, [t])` is `W(A♭) ⧸ (p, [t]) = A♭ ⧸ t`: divisibility by `t` in `A♭` is
  detected by the sharp map, and `x ↦ x♯` induces a ring isomorphism `A♭ ⧸ (t) ≃+* A ⧸ (t♯)`. For
  `t = (ϖ♭) ^ p` with `((ϖ♭)♯) ^ p ∣ p` this is `A♭ ⧸ (ϖ♭) ^ p ≅ A ⧸ ((ϖ♭)♯) ^ p`; for `t = p♭`
  with `(p♭)♯` a unit multiple of `p`, it is `A♭ ⧸ p♭ ≅ A ⧸ p`. Divisibility also shows that the
  ideal `(t)` of `A♭` depends only on the ideal `(t♯)` of `A`.
* **Relative Frobenius.** For `π` with `π ^ p ∣ p` and `A` `π`-adically complete, `π` is a unit
  multiple of some `ϖ♯`, and Frobenius `A ⧸ π → A ⧸ π ^ p` is identified with the Frobenius
  `A♭ ⧸ ϖ → A♭ ⧸ ϖ ^ p` of the perfect ring `A♭`, which is bijective.

## Main results

* `TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_iff_isDistinguished`: an
  element of `ker θ` generates `ker θ` if and only if it is distinguished.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_isDistinguished_ker_fontaineTheta_eq_span`:
  `ker θ` has a distinguished generator.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.dvd_coeff_zero_of_ker_fontaineTheta_eq_span`: for
  `t♯ ∣ p`, `t` divides the zeroth Witt coordinate of every generator of `ker θ`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_ker_fontaineTheta_eq_span_p_add_teichmuller_mul`:
  for `t♯ ∣ p`, `ker θ = (p + [t] α)` for some `α`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_sup_span_teichmuller`: for `t♯ ∣ p`,
  `ker θ + ([t]) = (p, [t])`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.dvd_iff_untilt_dvd`: for `t♯ ∣ p`, `t ∣ x` in `A♭` if
  and only if `t♯ ∣ x♯` in `A`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.span_singleton_eq_span_singleton_iff_untilt`: for
  `s♯ ∣ p` and `t♯ ∣ p`, `(s) = (t)` in `A♭` if and only if `(s♯) = (t♯)` in `A`.
* `PreTilt.quotientSpanEquiv`: for `t♯ ∣ p`, the sharp map induces `A♭ ⧸ (t) ≃+* A ⧸ (t♯)`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.associated_untilt_coeff_zero`: for a generator `g` of
  `ker θ`, `(g₀)♯` is a unit multiple of `p`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.isAdicComplete_span_coeff_zero`: for a generator `g` of
  `ker θ`, `A♭` is `(g₀)`-adically complete.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.mem_nonZeroDivisors_of_ker_fontaineTheta_eq_span`: every
  generator of `ker θ` is a nonzerodivisor of `W(A♭)`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_injective`,
  `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_bijective`: for `π ^ p ∣ p` with `A`
  `π`-adically complete, relative Frobenius `A ⧸ π → A ⧸ π ^ p` is bijective.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.10(i) and its proof,
  and Remark 3.11.
* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, (2.1.2.2).
-/

public section

open Ideal WittVector
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid.IsIntegralPerfectoid

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [IsIntegralPerfectoid p A]

section Tilt

variable [Fact ¬IsUnit (p : A)]

/-- `ker θ` contains a distinguished element. If `π ^ p ∣ p` and `A` is `π`-adically complete, then
`π` is a unit multiple of some `ϖ♯` (Bhatt–Morrow–Scholze, Lemma 3.9), `A♭` is `(ϖ)`-adically
complete, and writing `p = ϖ♯ θ(γ)` gives the distinguished element `p - [ϖ] γ` of `ker θ`. -/
private theorem exists_mem_ker_isDistinguished :
    ∃ ξ ∈ RingHom.ker (fontaineTheta A p), ξ.IsDistinguished := by
  obtain ⟨π, hπ, hπc⟩ := exists_adic_element (p := p) (A := A)
  obtain ⟨ϖ, -, hassoc⟩ := exists_associated_untilt hπ
  have hϖ : ϖ.untilt ∣ (p : A) := hassoc.symm.dvd.trans ((dvd_pow_self π hp.out.ne_zero).trans hπ)
  have : IsAdicComplete (span {ϖ.untilt}) A := by
    obtain ⟨u, hu⟩ := hassoc
    rwa [← hu, span_singleton_mul_right_unit u.isUnit]
  have := PreTilt.isAdicComplete_span_singleton hϖ
  obtain ⟨c, hc⟩ := hϖ
  obtain ⟨γ, rfl⟩ := surjective_fontaineTheta (p := p) c
  refine ⟨(p : WittVector p (PreTilt A p)) + teichmuller p ϖ * -γ, ?_,
    isDistinguished_p_add_teichmuller_mul_of_isAdicComplete (mem_span_singleton_self ϖ) _⟩
  rw [RingHom.mem_ker, map_add, map_mul, map_neg, map_natCast, fontaineTheta_teichmuller, hc]
  ring

/-- **Generators of `ker θ` are the distinguished elements of `ker θ`** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Remark 3.11). For an integral perfectoid ring `A`, possibly with
`p`-torsion, an element `ξ ∈ ker θ` generates `ker θ` if and only if its first Witt coordinate is a
unit. -/
theorem ker_fontaineTheta_eq_span_iff_isDistinguished {ξ : WittVector p (PreTilt A p)}
    (hξ : ξ ∈ RingHom.ker (fontaineTheta A p)) :
    RingHom.ker (fontaineTheta A p) = span {ξ} ↔ ξ.IsDistinguished := by
  have hξ₀ := coeff_zero_mem_jacobson_of_mem_ker_fontaineTheta hξ
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- A distinguished element of `ker θ` is a multiple `y ξ` of `ξ`.
    obtain ⟨d, hd, hdd⟩ := exists_mem_ker_isDistinguished (p := p) (A := A)
    rw [h] at hd
    obtain ⟨y, rfl⟩ := mem_span_singleton'.mp hd
    exact ((isDistinguished_mul_iff_of_coeff_zero_mem_jacobson hξ₀ y).mp hdd).2
  · -- `ξ` is a multiple `y g` of a generator `g` of `ker θ`, and `y` is a unit.
    obtain ⟨g, hg⟩ := (isPrincipal_ker_fontaineTheta (p := p) (A := A)).principal
    rw [submodule_span_eq] at hg
    have hg₀ := coeff_zero_mem_jacobson_of_mem_ker_fontaineTheta
      (hg ▸ mem_span_singleton_self g : g ∈ RingHom.ker (fontaineTheta A p))
    obtain ⟨y, rfl⟩ := mem_span_singleton'.mp (hg ▸ hξ)
    rw [hg, span_singleton_mul_left_unit
      ((isDistinguished_mul_iff_of_coeff_zero_mem_jacobson hg₀ y).mp h).1]

/-- `ker θ` is generated by a distinguished element. -/
theorem exists_isDistinguished_ker_fontaineTheta_eq_span :
    ∃ g : WittVector p (PreTilt A p),
      g.IsDistinguished ∧ RingHom.ker (fontaineTheta A p) = span {g} := by
  obtain ⟨g, hg⟩ := (isPrincipal_ker_fontaineTheta (p := p) (A := A)).principal
  rw [submodule_span_eq] at hg
  exact ⟨g, (ker_fontaineTheta_eq_span_iff_isDistinguished (hg ▸ mem_span_singleton_self g)).mp hg,
    hg⟩

/-- **The zeroth Witt coordinate of a generator of `ker θ` is divisible by `t`** whenever
`t♯ ∣ p`. For instance `(ϖ♭) ^ p ∣ ξ₀` for a generator `ξ` of `ker θ` when `((ϖ♭)♯) ^ p ∣ p`.
The generator `g = [g₀] + p u` is distinguished
(`ker_fontaineTheta_eq_span_iff_isDistinguished`). Writing `p = z g + [t] w` gives
`p (1 - u z) = [g₀] z + [t] w`; modulo `t` the zeroth and first Witt coordinates give
`t ∣ g₀ z₀` and `t ∣ (1 - u₀ z₀) ^ p - g₀ ^ p z₁`, hence `t ∣ g₀ (1 - g₀ ^ p z₁)`, and
`1 - g₀ ^ p z₁` is a unit as `g₀` lies in the Jacobson radical. -/
theorem dvd_coeff_zero_of_ker_fontaineTheta_eq_span {g : WittVector p (PreTilt A p)}
    (hg : RingHom.ker (fontaineTheta A p) = span {g}) {t : PreTilt A p}
    (ht : t.untilt ∣ (p : A)) : t ∣ g.coeff 0 := by
  have hgk : g ∈ RingHom.ker (fontaineTheta A p) := hg ▸ mem_span_singleton_self g
  have hg₀ := coeff_zero_mem_jacobson_of_mem_ker_fontaineTheta hgk
  have hgd := (ker_fontaineTheta_eq_span_iff_isDistinguished hgk).mp hg
  obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp hgd
  obtain ⟨c, hc⟩ := ht
  obtain ⟨w, rfl⟩ := surjective_fontaineTheta (p := p) c
  have hmem : (p : WittVector p (PreTilt A p)) - teichmuller p t * w ∈ span {g} := by
    rw [← hg, RingHom.mem_ker, map_sub, map_mul, map_natCast, fontaineTheta_teichmuller, hc,
      sub_self]
  obtain ⟨z, hz⟩ := mem_span_singleton'.mp hmem
  generalize g.coeff 0 = g₀ at hu hg₀ ⊢
  have heq : (p : WittVector p (PreTilt A p)) * (1 - ↑u * z) =
      teichmuller p g₀ * z + teichmuller p t * w := by
    linear_combination -hz + z * hu
  -- Modulo `t`, the Witt coordinates of `p (1 - u z)` and `[g₀] z` agree.
  have hmod (n : ℕ) :
      t ∣ ((p : WittVector p (PreTilt A p)) * (1 - ↑u * z)).coeff n -
        (teichmuller p g₀ * z).coeff n := by
    have h := congrArg (fun x ↦ (WittVector.map (Ideal.Quotient.mk (span {t})) x).coeff n) heq
    simp only [map_add, map_mul (WittVector.map _) (teichmuller p t), map_teichmuller,
      Ideal.Quotient.mk_singleton_self, teichmuller_zero, zero_mul, add_zero, map_coeff] at h
    rw [← mem_span_singleton, ← Ideal.Quotient.eq]
    exact h
  have h₀ : t ∣ g₀ * z.coeff 0 := by
    simpa [mul_coeff_zero, coeff_p_zero] using hmod 0
  -- The first Witt coordinates of `p (1 - u z)` and of `[g₀] z`.
  have hp₁ : ((p : WittVector p (PreTilt A p)) * (1 - ↑u * z)).coeff 1 =
      1 - (u : WittVector p (PreTilt A p)).coeff 0 ^ p * z.coeff 0 ^ p := by
    rw [mul_comm, mul_charP_coeff_succ, sub_coeff_zero, one_coeff_zero, mul_coeff_zero,
      sub_pow_char, one_pow, mul_pow]
  have hg₁ : (teichmuller p g₀ * z).coeff 1 = g₀ ^ p * z.coeff 1 := by
    rw [mul_coeff_one_charP, teichmuller_coeff_pos p g₀ 1 one_pos, teichmuller_coeff_zero,
      mul_zero, add_zero]
  have h₁ := hmod 1
  rw [hp₁, hg₁] at h₁
  have hz₀ : z.coeff 0 ^ p = z.coeff 0 ^ (p - 1) * z.coeff 0 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  have hunit : IsUnit (1 - g₀ ^ p * z.coeff 1) := by
    have h := Ring.mem_jacobson_iff.mp
      (mul_mem_right (z.coeff 1) _ (pow_mem_of_mem _ hg₀ p hp.out.pos)) (-1)
    rwa [mul_neg_one, neg_add_eq_sub] at h
  refine (hunit.dvd_mul_right).mp ?_
  have h := dvd_add (h₁.mul_left g₀)
    (h₀.mul_right ((u : WittVector p (PreTilt A p)).coeff 0 ^ p * z.coeff 0 ^ (p - 1)))
  convert h using 1
  linear_combination g₀ * (u : WittVector p (PreTilt A p)).coeff 0 ^ p * hz₀

/-- **`ker θ + ([t]) = (p, [t])`** for `t : A♭` with `t♯ ∣ p`. Thus
`A ⧸ t♯ = W(A♭) ⧸ (ker θ, [t])` is `W(A♭) ⧸ (p, [t]) = A♭ ⧸ t`. -/
theorem ker_fontaineTheta_sup_span_teichmuller {t : PreTilt A p} (ht : t.untilt ∣ (p : A)) :
    RingHom.ker (fontaineTheta A p) ⊔ span {teichmuller p t} =
      span {(p : WittVector p (PreTilt A p)), teichmuller p t} := by
  obtain ⟨g, hgd, hg⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := A)
  rw [hg, ← span_insert]
  exact hgd.span_pair_teichmuller_eq (dvd_coeff_zero_of_ker_fontaineTheta_eq_span hg ht)

/-- **A generator of `ker θ` of the form `p + [t] α`** (Bhatt–Morrow–Scholze, *Integral `p`-adic
Hodge theory*, proof of Lemma 3.10). If `t : A♭` has `t♯ ∣ p`, then `ker θ` is generated by
`p + [t] α` for some `α : W(A♭)`. -/
theorem exists_ker_fontaineTheta_eq_span_p_add_teichmuller_mul {t : PreTilt A p}
    (ht : t.untilt ∣ (p : A)) :
    ∃ α : WittVector p (PreTilt A p),
      RingHom.ker (fontaineTheta A p) =
        span {(p : WittVector p (PreTilt A p)) + teichmuller p t * α} := by
  obtain ⟨g, hgd, hg⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := A)
  obtain ⟨h, hh⟩ := dvd_coeff_zero_of_ker_fontaineTheta_eq_span hg ht
  obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp hgd
  -- `g = [t h] + p u = u (p + [t] [h] u⁻¹)`.
  have hgu : g = ↑u * ((p : WittVector p (PreTilt A p)) +
      teichmuller p t * (teichmuller p h * ↑u⁻¹)) := by
    rw [hu, hh, map_mul]
    linear_combination -(teichmuller p t * teichmuller p h) * u.mul_inv
  exact ⟨_, by rw [hg, hgu, span_singleton_mul_left_unit u.isUnit]⟩

/-- **Divisibility in the tilt is detected by the sharp map.** If `t : A♭` has `t♯ ∣ p`, then
`t ∣ x` in `A♭` if and only if `t♯ ∣ x♯` in `A` (Česnavičius–Scholze, *Purity for flat
cohomology*, (2.1.2.2)). For instance `(ϖ♭) ^ p ∣ p♭` whenever `((ϖ♭)♯) ^ p ∣ p` and `(p♭)♯` is a
unit multiple of `p`. -/
theorem dvd_iff_untilt_dvd {t : PreTilt A p} (ht : t.untilt ∣ (p : A)) {x : PreTilt A p} :
    t ∣ x ↔ t.untilt ∣ x.untilt := by
  refine ⟨map_dvd PreTilt.untilt, fun ⟨a, ha⟩ ↦ ?_⟩
  obtain ⟨b, rfl⟩ := surjective_fontaineTheta (p := p) a
  -- `[x] = ([x] - [t] b) + [t] b` with `θ([x] - [t] b) = x♯ - t♯ θ(b) = 0`.
  have hker : teichmuller p x - teichmuller p t * b ∈ RingHom.ker (fontaineTheta A p) := by
    rw [RingHom.mem_ker, map_sub, map_mul, fontaineTheta_teichmuller, fontaineTheta_teichmuller,
      ha, sub_self]
  have hmem := Submodule.add_mem_sup (T := span {teichmuller p t}) hker
    (mem_span_singleton.mpr (dvd_mul_right (teichmuller p t) b))
  rw [sub_add_cancel, ker_fontaineTheta_sup_span_teichmuller ht, mem_span_p_teichmuller_iff,
    teichmuller_coeff_zero] at hmem
  exact hmem

/-- **The ideal `(t)` of the tilt depends only on `(t♯)`** (Česnavičius–Scholze, *Purity for flat
cohomology*, (2.1.2.2)). If `s, t : A♭` have `s♯ ∣ p` and `t♯ ∣ p`, then `(s) = (t)` in `A♭` if
and only if `(s♯) = (t♯)` in `A`. -/
theorem span_singleton_eq_span_singleton_iff_untilt {s t : PreTilt A p}
    (hs : s.untilt ∣ (p : A)) (ht : t.untilt ∣ (p : A)) :
    span {s} = span {t} ↔ span {s.untilt} = span {t.untilt} := by
  simp only [le_antisymm_iff, span_singleton_le_span_singleton, dvd_iff_untilt_dvd hs,
    dvd_iff_untilt_dvd ht]

/-- **The sharp of `p♭` is a unit multiple of `p`.** If `g` generates `ker θ`, then `(g₀)♯` is
associated to `p`: writing the distinguished generator as `g = [g₀] + p u` with `u` a unit,
`0 = θ(g) = (g₀)♯ + p θ(u)`. So `g₀` is a choice of `p♭`. -/
theorem associated_untilt_coeff_zero {g : WittVector p (PreTilt A p)}
    (hg : RingHom.ker (fontaineTheta A p) = span {g}) :
    Associated (g.coeff 0).untilt (p : A) := by
  have hgk : g ∈ RingHom.ker (fontaineTheta A p) := hg ▸ mem_span_singleton_self g
  obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp
    ((ker_fontaineTheta_eq_span_iff_isDistinguished hgk).mp hg)
  have h := RingHom.mem_ker.mp hgk
  rw [hu, map_add, map_mul, map_natCast, fontaineTheta_teichmuller] at h
  have hθu : IsUnit (fontaineTheta A p u) := u.isUnit.map _
  refine Associated.symm ⟨-hθu.unit, ?_⟩
  rw [Units.val_neg, hθu.unit_spec]
  linear_combination -h

/-- **The tilt is complete for the zeroth Witt coordinate of a generator of `ker θ`.** If `g`
generates `ker θ`, then `A♭` is `(g₀)`-adically complete and separated: `(g₀)♯` is a unit multiple
of `p` (`associated_untilt_coeff_zero`; Česnavičius–Scholze, *Purity for flat cohomology*,
§2.1.2). -/
theorem isAdicComplete_span_coeff_zero {g : WittVector p (PreTilt A p)}
    (hg : RingHom.ker (fontaineTheta A p) = span {g}) :
    IsAdicComplete (span {g.coeff 0}) (PreTilt A p) := by
  have h := associated_untilt_coeff_zero hg
  have : IsAdicComplete (span {(g.coeff 0).untilt}) A := by
    obtain ⟨u, hu⟩ := h
    rw [← span_singleton_mul_right_unit u.isUnit, hu]
    infer_instance
  exact PreTilt.isAdicComplete_span_singleton h.dvd

/-- **Generators of `ker θ` are nonzerodivisors** (Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge
theory*, Lemma 3.10 and Remark 3.11). For an integral perfectoid ring `A`, possibly with
`p`-torsion, every generator of `ker θ` is a nonzerodivisor of `W(A♭)`. -/
theorem mem_nonZeroDivisors_of_ker_fontaineTheta_eq_span {g : WittVector p (PreTilt A p)}
    (hg : RingHom.ker (fontaineTheta A p) = span {g}) : g ∈ (WittVector p (PreTilt A p))⁰ := by
  have := isAdicComplete_span_coeff_zero hg
  exact ((ker_fontaineTheta_eq_span_iff_isDistinguished (hg ▸ mem_span_singleton_self g)).mp
    hg).mem_nonZeroDivisors (le_radical (mem_span_singleton_self _))

end Tilt

/-- **Relative Frobenius of an integral perfectoid ring is injective** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10(i)). If `π ^ p ∣ p` and `A` is `π`-adically
complete, then Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is injective: `π ^ p ∣ y ^ p` implies `π ∣ y`.
No nonzerodivisor hypothesis on `π` is needed. -/
theorem frobeniusModPow_injective {π : A} (h : π ^ p ∣ (p : A)) [IsAdicComplete (span {π}) A] :
    Function.Injective (frobeniusModPow p h) := by
  rw [frobeniusModPow_injective_iff]
  intro y hy
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : Fact ¬IsUnit (p : A) := ⟨not_isUnit_natCast⟩
  -- Replace `π` by an associated sharp `ϖ♯`.
  obtain ⟨ϖ, -, hassoc⟩ := exists_associated_untilt h
  have hϖp : ϖ.untilt ^ p ∣ (p : A) := (pow_dvd_pow_of_dvd hassoc.symm.dvd p).trans h
  have hϖy : ϖ.untilt ^ p ∣ y ^ p := (pow_dvd_pow_of_dvd hassoc.symm.dvd p).trans hy
  refine hassoc.dvd.trans ?_
  -- Write `y = x♯ + p z`; then `ϖ♯ ^ p ∣ (x ^ p)♯`, so `ϖ ^ p ∣ x ^ p` and `ϖ ∣ x` in `A♭`.
  obtain ⟨x, hx⟩ := coeff_surjective (p := p) 0 (Ideal.Quotient.mk (span {(p : A)}) y)
  have hpy : (p : A) ∣ y - x.untilt := by
    rw [← mem_span_singleton, ← Ideal.Quotient.eq, PreTilt.mk_untilt_eq_coeff_zero]
    exact hx.symm
  have hxp : (ϖ ^ p).untilt ∣ (x ^ p).untilt := by
    rw [map_pow, map_pow, ← sub_sub_cancel (y ^ p) (x.untilt ^ p)]
    exact dvd_sub hϖy (hϖp.trans (hpy.trans (sub_dvd_pow_sub_pow _ _ p)))
  obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd (by rwa [map_pow]) (x := x ^ p)).mpr hxp
  have hϖx : ϖ ∣ x :=
    (FrobeniusSplitting.ofPerfect (R := PreTilt A p) (p := p)).dvd_of_pow_dvd_pow ⟨c, hc⟩
  simpa using dvd_add (map_dvd PreTilt.untilt hϖx)
    (((dvd_pow_self _ hp.out.ne_zero).trans hϖp).trans hpy)

/-- **Relative Frobenius of an integral perfectoid ring is bijective** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10(i)). If `π ^ p ∣ p` and `A` is `π`-adically
complete, then Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is bijective. -/
theorem frobeniusModPow_bijective {π : A} (h : π ^ p ∣ (p : A)) [IsAdicComplete (span {π}) A] :
    Function.Bijective (frobeniusModPow p h) :=
  ⟨frobeniusModPow_injective h, frobeniusModPow_surjective h⟩

end TauCeti.Perfectoid.IsIntegralPerfectoid

namespace PreTilt

open TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsIntegralPerfectoid p A]
  [Fact ¬IsUnit (p : A)]

/-- **The tilt and the ring agree modulo `t`** (Česnavičius–Scholze, *Purity for flat
cohomology*, (2.1.2.2); Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, proof of
Lemma 3.10(i)). For an integral perfectoid ring `A` and `t : PreTilt A p` with `t♯ ∣ p`, the sharp
map induces a ring isomorphism `PreTilt A p ⧸ (t) ≃+* A ⧸ (t♯)`
(`PreTilt.quotientSpanEquiv_mk`). With `t = (ϖ♭) ^ p` and `((ϖ♭)♯) ^ p ∣ p` this is
`A♭ ⧸ (ϖ♭) ^ p ≅ A ⧸ ((ϖ♭)♯) ^ p`, and with `t = p♭` and `(p♭)♯` a unit multiple of `p` it is
`A♭ ⧸ p♭ ≅ A ⧸ p`. -/
noncomputable def quotientSpanEquiv {t : PreTilt A p} (ht : t.untilt ∣ (p : A)) :
    PreTilt A p ⧸ span {t} ≃+* A ⧸ span {t.untilt} := by
  have hle : span {(p : A)} ≤ span {t.untilt} :=
    span_le.mpr <| Set.singleton_subset_iff.mpr <| mem_span_singleton.mpr ht
  set ψ : PreTilt A p →+* A ⧸ span {t.untilt} := (Ideal.Quotient.factor hle).comp (coeff 0)
  have hψ (x : PreTilt A p) : ψ x = Ideal.Quotient.mk (span {t.untilt}) x.untilt := by
    simp [ψ, ← mk_untilt_eq_coeff_zero]
  have hker : RingHom.ker ψ = span {t} := by
    ext x
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton,
      mem_span_singleton, IsIntegralPerfectoid.dvd_iff_untilt_dvd ht]
  have hsurj : Function.Surjective ψ :=
    (Ideal.Quotient.factor_surjective hle).comp (IsIntegralPerfectoid.coeff_surjective 0)
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-- `PreTilt.quotientSpanEquiv` sends the class of `x` to the class of `x♯`. -/
@[simp]
theorem quotientSpanEquiv_mk {t : PreTilt A p} (ht : t.untilt ∣ (p : A)) (x : PreTilt A p) :
    quotientSpanEquiv ht (Ideal.Quotient.mk (span {t}) x) =
      Ideal.Quotient.mk (span {t.untilt}) x.untilt := by
  simp [quotientSpanEquiv, ← mk_untilt_eq_coeff_zero]

end PreTilt
