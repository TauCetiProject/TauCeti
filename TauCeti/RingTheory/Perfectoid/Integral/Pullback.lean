/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Pow
public import TauCeti.RingTheory.AdicCompletion.Pullback
public import TauCeti.RingTheory.Perfectoid.Integral.Pi
public import TauCeti.RingTheory.Perfectoid.Integral.PowerTorsion
public import TauCeti.RingTheory.Perfectoid.PreTilt.Pullback
public import TauCeti.RingTheory.Pullback

import Mathlib.Tactic.LinearCombination

/-!
# Fibre products of integral perfectoid rings

Let `f : A →+* A'` be a surjection of integral perfectoid rings
(`TauCeti.Perfectoid.IsIntegralPerfectoid`) and `g : B →+* A'` any ring homomorphism from an
integral perfectoid ring. This file shows that the fibre product `C = A ×_{A'} B`, the subring
`f.pullback g` of `A × B` on which `f` and `g` agree, is integral perfectoid
(Česnavičius–Scholze, *Purity for flat cohomology*, Proposition 2.1.4). No torsion-freeness is
assumed, and `f` need not have a section.

The tilt and `A_inf` of the fibre product are the fibre products of the tilts and of the `A_inf`
(`PreTilt.pullbackEquiv`, `PreTilt.wittVectorPullbackEquiv`), compatibly with Fontaine's maps,
once `C` is `p`-adically complete; and `C` is `p`-adically complete because the `p`-power torsion
of `A'` is killed by `p` (`IsAdicComplete.pullback_span_natCast`). The three defining conditions
of `C` are then checked on `A_inf(C) = A_inf(A) ×_{A_inf(A')} A_inf(B)`.

* **Fontaine's map is surjective.** Given `(a, b) ∈ C`, lift `b` to `w ∈ A_inf(B)`; since `A_inf(A)`
  surjects onto `A_inf(A') ×_{A'} A` (`WittVector.exists_map_eq_and_fontaineTheta_eq`), some
  `v ∈ A_inf(A)` has `θ_A(v) = a` and the same image as `w` in `A_inf(A')`. So `θ_C` is surjective,
  and every element of `C` is a `p`-th power modulo `p`.
* **Compatible generators of `ker θ`.** Normalise a generator of `ker θ_B` to `ξ_B = p + [b] β` with
  `β` a unit, and let `a ∈ A♭` have `a♯` a unit multiple of `p`. In `A'♭`, `f♭ a` divides `g♭ b`,
  as both have sharp a unit multiple of `p`; so the image of `ξ_B` in `A_inf(A')` is
  `p + [f♭ a] w'`. It lifts to an element `ξ_A = p + [a] w` of `ker θ_A`
  (`WittVector.exists_map_teichmuller_mul_eq_and_fontaineTheta_eq`), which is distinguished,
  hence generates `ker θ_A`. The pair `ξ_C = (ξ_A, ξ_B)` lies in `A_inf(C)` and generates `ker θ_C`:
  for `(y_A ξ_A, y_B ξ_B)` in `A_inf(C)`, the images of `y_A` and `y_B` in `A_inf(A')` agree,
  because the image of `ξ_B` is a nonzerodivisor.
* **An adic element.** `ξ_C` is distinguished, so the sharp of its zeroth Witt coordinate `t` is a
  unit multiple of `p` in `C`; then `π = (t ^ (1 / p))♯` has `π ^ p = t♯`, and the `π`-adic and
  `p`-adic topologies of `C` agree.

When `A'` is the zero ring, `C` is the product `A × B` (`IsIntegralPerfectoid.prod`).

## Main results

* `TauCeti.Perfectoid.IsIntegralPerfectoid.isAdicComplete_pullback_span_natCast`: for integral
  perfectoid `A'` and `p`-adically complete `A` and `B`, the fibre product `A ×_{A'} B` is
  `p`-adically complete.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.pullback`: the fibre product of integral perfectoid
  rings along a surjection `f : A →+* A'` and any `g : B →+* A'` is integral perfectoid.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, Proposition 2.1.4 and its proof,
  Example 2.1.5.
-/

public section

open Ideal WittVector

namespace TauCeti.Perfectoid.IsIntegralPerfectoid

variable {p : ℕ} [hp : Fact p.Prime] {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]

/-- **Fibre products over an integral perfectoid ring are `p`-adically complete**: if `A` and `B`
are `p`-adically complete and `A'` is integral perfectoid, then so is `A ×_{A'} B` for any
`f : A →+* A'` and `g : B →+* A'`. The `p`-power torsion of `A'` is killed by `p`
(`IsIntegralPerfectoid.natCast_mul_eq_zero_of_natCast_pow_mul_eq_zero`). -/
instance isAdicComplete_pullback_span_natCast [IsIntegralPerfectoid p A']
    [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B] (f : A →+* A')
    (g : B →+* A') : IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g) :=
  .pullback_span_natCast fun _ _ ↦ natCast_mul_eq_zero_of_natCast_pow_mul_eq_zero (p := p)

section Nontrivial

variable [IsIntegralPerfectoid p A] [IsIntegralPerfectoid p A'] [IsIntegralPerfectoid p B]
  [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : A')] [Fact ¬IsUnit (p : B)] {f : A →+* A'}
  (hf : Function.Surjective f) (g : B →+* A')

include hf

/-- Fontaine's map of `A ×_{A'} B` is surjective. -/
private theorem surjective_fontaineTheta_pullback :
    Function.Surjective (fontaineTheta (f.pullback g) p) := by
  rintro ⟨⟨a, b⟩, hab⟩
  obtain ⟨w, rfl⟩ := surjective_fontaineTheta (p := p) (A := B) b
  obtain ⟨v, hv, rfl⟩ := exists_map_eq_and_fontaineTheta_eq hf
    (w := WittVector.map (PreTilt.map p g) w) (a := a)
    (by rw [theta_natural]; exact (RingHom.mem_pullback.mp hab).symm)
  refine ⟨(PreTilt.wittVectorPullbackEquiv p f g).symm ⟨(v, w), RingHom.mem_pullback.mpr hv⟩,
    Subtype.ext ?_⟩
  rw [PreTilt.coe_fontaineTheta_wittVectorPullbackEquiv_symm]

/-- A generator `p + [b] β` of `ker θ_B`, with `β` a unit, has image `p + [f♭ a] w'` in `A_inf(A')`
for every `a ∈ A♭` with `a♯` a unit multiple of `p`, and so lifts to a generator of `ker θ_A`. -/
private theorem exists_ker_fontaineTheta_eq_span_map_eq_map :
    ∃ ξA ξB, RingHom.ker (fontaineTheta A p) = span {ξA} ∧ ξA.IsDistinguished ∧
      RingHom.ker (fontaineTheta B p) = span {ξB} ∧ ξB.IsDistinguished ∧
      WittVector.map (PreTilt.map p f) ξA = WittVector.map (PreTilt.map p g) ξB := by
  -- normalise a distinguished generator `η = [b] + p u` of `ker θ_B` to `ξB = p + [b] u⁻¹`
  obtain ⟨η, hηd, hη⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := B)
  have hb := associated_untilt_coeff_zero hη
  obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp hηd
  set b := η.coeff 0
  set ξB : WittVector p (PreTilt B p) := p + teichmuller p b * ↑u⁻¹ with hξB
  have hξBη : ξB = ↑u⁻¹ * η := by
    rw [hu]
    linear_combination (-(p : WittVector p (PreTilt B p))) * u.inv_mul
  have hξBk : RingHom.ker (fontaineTheta B p) = span {ξB} := by
    rw [hξBη, span_singleton_mul_left_unit u⁻¹.isUnit, hη]
  have hξBθ : fontaineTheta B p ξB = 0 := RingHom.mem_ker.mp (hξBk ▸ mem_span_singleton_self ξB)
  -- `a = p♭` for `A`; its image in `A'♭` divides the image of `b`
  obtain ⟨ζ, -, hζ⟩ := exists_isDistinguished_ker_fontaineTheta_eq_span (p := p) (A := A)
  set a := ζ.coeff 0
  have ha := associated_untilt_coeff_zero hζ
  have := isAdicComplete_span_coeff_zero hζ
  have hab : PreTilt.map p f a ∣ PreTilt.map p g b := by
    have ha' := ha.map f
    have hb' := hb.map g
    rw [map_natCast, ← PreTilt.untilt_natural] at ha' hb'
    exact (dvd_iff_untilt_dvd ha'.dvd).mpr (ha'.dvd.trans hb'.symm.dvd)
  obtain ⟨r, hr⟩ := hab
  -- lift `map ξB = p + [f♭ a] ([r] β')` to `ξA = p + [a] w` in `ker θ_A`
  have hθ : fontaineTheta A' p (teichmuller p (PreTilt.map p f a) *
      (teichmuller p r * WittVector.map (PreTilt.map p g) ↑u⁻¹)) = f (p * -1) := by
    have h := congr(g $hξBθ)
    simp only [← theta_natural, hξB, map_add, map_natCast, map_mul, map_teichmuller, hr,
      map_zero] at h
    simp only [← mul_assoc, map_mul, map_natCast, map_neg, map_one]
    linear_combination h
  obtain ⟨w, hwmap, hwθ⟩ := exists_map_teichmuller_mul_eq_and_fontaineTheta_eq hf ha hθ
  have hξAd : ((p : WittVector p (PreTilt A p)) + teichmuller p a * w).IsDistinguished :=
    isDistinguished_p_add_teichmuller_mul_of_isAdicComplete (mem_span_singleton_self a) w
  have hξAθ : (p : WittVector p (PreTilt A p)) + teichmuller p a * w ∈
      RingHom.ker (fontaineTheta A p) := by
    rw [RingHom.mem_ker, map_add, hwθ, map_natCast]
    ring
  refine ⟨_, ξB, (ker_fontaineTheta_eq_span_iff_isDistinguished hξAθ).mpr hξAd, hξAd, hξBk,
    (isDistinguished_of_ker_fontaineTheta_eq_span hξBk), ?_⟩
  rw [map_add, map_natCast, hwmap]
  simp [hξB, hr, mul_assoc, a]

/-- `ker θ` of `A ×_{A'} B` is generated by a distinguished element. -/
private theorem exists_ker_fontaineTheta_pullback_eq_span :
    ∃ ξ : WittVector p (PreTilt (f.pullback g) p),
      RingHom.ker (fontaineTheta (f.pullback g) p) = span {ξ} ∧ ξ.IsDistinguished := by
  obtain ⟨ξA, ξB, hA, hAd, hB, hBd, hmap⟩ :=
    exists_ker_fontaineTheta_eq_span_map_eq_map (p := p) hf g
  set e := PreTilt.wittVectorPullbackEquiv p f g
  set ξ := e.symm ⟨(ξA, ξB), RingHom.mem_pullback.mpr hmap⟩
  have hξ : (e ξ : WittVector p (PreTilt A p) × WittVector p (PreTilt B p)) = (ξA, ξB) := by
    simp [ξ]
  have hreg := mem_nonZeroDivisors_of_ker_fontaineTheta_eq_span
    (ker_fontaineTheta_eq_span_map (p := p) g hB)
  refine ⟨ξ, le_antisymm (fun v hv ↦ ?_) ?_,
    PreTilt.isDistinguished_iff_wittVectorPullbackEquiv.mpr (hξ ▸ ⟨hAd, hBd⟩)⟩
  · -- write the components of `v` as multiples `yA ξA` and `yB ξB`
    rw [PreTilt.mem_ker_fontaineTheta_iff_wittVectorPullbackEquiv, hA, hB, mem_span_singleton',
      mem_span_singleton'] at hv
    obtain ⟨⟨yA, hyA⟩, ⟨yB, hyB⟩⟩ := hv
    have hy : WittVector.map (PreTilt.map p f) yA = WittVector.map (PreTilt.map p g) yB := by
      have h := RingHom.mem_pullback.mp (e v).property
      rw [← hyA, ← hyB, map_mul, map_mul, hmap, ← sub_eq_zero, ← sub_mul] at h
      exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hreg).mp h)
    refine mem_span_singleton'.mpr ⟨e.symm ⟨(yA, yB), RingHom.mem_pullback.mpr hy⟩,
      e.injective (Subtype.ext ?_)⟩
    rw [map_mul, RingEquiv.apply_symm_apply, Subring.coe_mul, hξ, Prod.mk_mul_mk, hyA, hyB]
  · rw [span_singleton_le_iff_mem, PreTilt.mem_ker_fontaineTheta_iff_wittVectorPullbackEquiv, hξ,
      hA, hB]
    exact ⟨mem_span_singleton_self _, mem_span_singleton_self _⟩

/-- The fibre product of nonzero integral perfectoid rings along a surjection is integral
perfectoid. -/
private theorem pullback_of_nontrivial : IsIntegralPerfectoid p (f.pullback g) := by
  obtain ⟨ξ, hξ, hd⟩ := exists_ker_fontaineTheta_pullback_eq_span (p := p) hf g
  have ht := associated_untilt_coeff_zero_of_isDistinguished (A := f.pullback g) (p := p)
    (hξ ▸ mem_span_singleton_self ξ) hd
  -- `π = (ξ₀ ^ (1 / p))♯` has `π ^ p = ξ₀♯`, a unit multiple of `p`
  set π := ((frobeniusEquiv (PreTilt (f.pullback g) p) p).symm (ξ.coeff 0)).untilt
  have hπ : π ^ p = (ξ.coeff 0).untilt := by rw [← map_pow, frobeniusEquiv_symm_pow_p]
  refine ⟨⟨π, hπ ▸ ht.dvd, ?_⟩, ?_, fun _ _ ↦ ⟨⟨ξ, hξ⟩⟩⟩
  · refine .of_pow_le_of_pow_le (I := span {(p : f.pullback g)}) (k := p) (l := 1) ?_ ?_
    · rw [span_singleton_pow, hπ, span_singleton_le_span_singleton]
      exact ht.symm.dvd
    · rw [pow_one, span_singleton_le_span_singleton]
      exact (dvd_pow_self π hp.out.ne_zero).trans (hπ ▸ ht.dvd)
  · refine (surjective_pow_modP_iff _).mpr fun x ↦ ?_
    obtain ⟨w, rfl⟩ := surjective_fontaineTheta_pullback (p := p) hf g x
    refine ⟨((frobeniusEquiv _ p).symm (w.coeff 0)).untilt, ?_⟩
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
    exact natCast_dvd_fontaineTheta_sub_untilt w

end Nontrivial

/-- **Fibre products of integral perfectoid rings** (Česnavičius–Scholze, *Purity for flat
cohomology*, Proposition 2.1.4). If `f : A →+* A'` is a surjection of integral perfectoid rings and
`g : B →+* A'` is any ring homomorphism from an integral perfectoid ring, then the fibre product
`A ×_{A'} B` (the subring `f.pullback g` of `A × B`) is integral perfectoid. -/
theorem pullback [IsIntegralPerfectoid p A] [IsIntegralPerfectoid p A'] [IsIntegralPerfectoid p B]
    {f : A →+* A'} (hf : Function.Surjective f) (g : B →+* A') :
    IsIntegralPerfectoid p (f.pullback g) := by
  cases subsingleton_or_nontrivial A' with
  | inl _ =>
    -- over the zero ring, the fibre product is all of `A × B`
    exact .of_ringEquiv (RingHom.pullbackEquivProdOfSubsingleton f g).symm
  | inr _ =>
    have : Nontrivial A := hf.nontrivial
    have : Nontrivial B := g.domain_nontrivial
    have : Fact ¬IsUnit (p : A) := ⟨not_isUnit_natCast⟩
    have : Fact ¬IsUnit (p : A') := ⟨not_isUnit_natCast⟩
    have : Fact ¬IsUnit (p : B) := ⟨not_isUnit_natCast⟩
    exact pullback_of_nontrivial hf g

end TauCeti.Perfectoid.IsIntegralPerfectoid
