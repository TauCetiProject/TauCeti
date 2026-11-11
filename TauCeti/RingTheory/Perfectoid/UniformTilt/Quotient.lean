/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Complete
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
import Mathlib.Algebra.CharP.Basic

/-!
# Quotients of the integral tilt

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with
tilt `B♭` and integral tilt `B♭⁺ = lim_{x ↦ x ^ p} B⁺` for a ring of integral elements `B⁺`. The
sharp map `x ↦ x♯ = x⁽⁰⁾` sends `B♭⁺` multiplicatively to `B⁺`, and it is additive modulo `p`
(`TauCeti.Perfectoid.uniformTilt.plusSharp_add_sub_mem`), so for every ideal `I` of `B⁺`
containing `p` it induces a ring homomorphism `B♭⁺ → B⁺ ⧸ I`.

For an element `π ∈ B♭⁺` such that `π♯` is a unit of `B` dividing `p` in `B⁺`, the kernel of
`B♭⁺ → B⁺ ⧸ (π♯)` is the principal ideal `(π)`. When `B⁺` is `I`-adically complete, the map
`B♭⁺ → B⁺ ⧸ I` is surjective exactly when every element of `B⁺` is a `p`-th power modulo `I`.

If `B` is a perfectoid Tate ring and `B⁺ = B°`, every element of `B°` is a `p`-th power modulo `p`,
so the reduction of `♯` modulo any ideal containing `p` is surjective. Hence `♯` induces a ring
isomorphism `B♭° ⧸ (π) ≃+* B° ⧸ (π♯)`. For a pseudouniformiser `ϖ♭` with compatible `p`-power roots
and `ϖ = ϖ♭♯` this is the isomorphism `B♭° ⧸ (ϖ♭) ≅ B° ⧸ (ϖ)` through which the tilt sees the
reduction of `B°` modulo `ϖ`, and the same holds for the powers `ϖ♭ ^ q` with `q ∈ ℤ[1/p]` and
`0 < q ≤ p`, whose images under `♯` divide `p`.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.sharpQuot h I hI`: the ring homomorphism `B♭⁺ →+* B⁺ ⧸ I`,
  `x ↦ x♯ mod I`, for an ideal `I` containing `p`.
* `TauCeti.Perfectoid.uniformTilt.sharpQuotEquiv`: the ring isomorphism `B♭⁺ ⧸ (π) ≃+* B⁺ ⧸ (π♯)`
  when `B♭⁺ → B⁺ ⧸ (π♯)` is surjective, for instance `B♭° ⧸ (π) ≃+* B° ⧸ (π♯)` for a perfectoid
  Tate ring `B`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.coeff_zero_plusEquiv`: for `B⁺` complete along `I`, the map
  `B♭⁺ → B⁺ ⧸ I` is the zeroth coordinate of `plusEquiv h I : B♭⁺ ≃+* Perfection (B⁺ ⧸ I) p`.
* `TauCeti.Perfectoid.uniformTilt.ker_sharpQuot`: the kernel of `B♭⁺ → B⁺ ⧸ (π♯)` is `(π)`.
* `TauCeti.Perfectoid.uniformTilt.sharpQuot_surjective_iff`: for `B⁺` complete along `I`,
  `B♭⁺ → B⁺ ⧸ I` is surjective iff every element of `B⁺` is a `p`-th power modulo `I`.
* `TauCeti.Perfectoid.uniformTilt.sharpQuot_surjective`: for a perfectoid Tate ring, every element
  of `B°` is congruent to some `x♯` with `x ∈ B♭°` modulo every ideal containing `p`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and the text after it.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Lemma 6.2.2.
* P. Scholze, *Perfectoid spaces*, Lemma 3.4(iii).
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} {B : Type*} [CommRing B] [hp : Fact p.Prime] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

variable {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)

/-- The reduction `B♭⁺ → B⁺ ⧸ I`, `x ↦ x♯ mod I`, for an ideal `I` of `B⁺` containing `p`: a ring
homomorphism, as the sharp map is multiplicative and additive modulo `p`. -/
noncomputable def sharpQuot (I : Ideal Bplus) (hI : (p : Bplus) ∈ I) :
    plusSubring p h →+* Bplus ⧸ I where
  toFun x := Ideal.Quotient.mk I (plusSharp p h x)
  map_zero' := by rw [map_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add' x y := by
    rw [← sub_eq_zero, ← map_add, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← sub_sub]
    exact (Ideal.span_singleton_le_iff_mem I).mpr hI (plusSharp_add_sub_mem h x y)

@[simp]
theorem sharpQuot_apply (I : Ideal Bplus) (hI : (p : Bplus) ∈ I) (x : plusSubring p h) :
    sharpQuot h I hI x = Ideal.Quotient.mk I (plusSharp p h x) :=
  (rfl)

/-- When `B⁺` is `I`-adically complete, `sharpQuot` is the zeroth coordinate of `plusEquiv`. -/
theorem coeff_zero_plusEquiv (I : Ideal Bplus) (hI : (p : Bplus) ∈ I) [CharP (Bplus ⧸ I) p]
    [IsAdicComplete I Bplus] (x : plusSubring p h) :
    Perfection.coeff (Bplus ⧸ I) p 0 (plusEquiv h I x) = sharpQuot h I hI x := by
  rw [coeff_plusEquiv, sharpQuot_apply]
  exact congrArg _ (Subtype.ext (coe_plusSharp h x).symm)

/-- **The kernel of `B♭⁺ → B⁺ ⧸ (π♯)` is `(π)`** for `π ∈ B♭⁺` such that `π♯` is a unit of `B`
dividing `p` in `B⁺`. -/
theorem ker_sharpQuot {π : plusSubring p h} (hπ : IsUnit (coeff p B 0 π))
    (hπp : plusSharp p h π ∣ p) :
    RingHom.ker (sharpQuot h _ (Ideal.mem_span_singleton.mpr hπp)) = Ideal.span {π} := by
  ext x
  rw [RingHom.mem_ker, sharpQuot_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, map_dvd (plusSharp p h)⟩
  -- if `x♯ = π♯ c`, then `x = π (π⁻¹ x)`, where `π` is a unit of the tilt and `π⁻¹ x` has zeroth
  -- coordinate `x♯ / π♯ = c ∈ B⁺`, so lies in `B♭⁺`
  obtain ⟨u, hu⟩ := isUnit_iff_coeff_zero.mpr hπ
  have hc' : coeff p B 0 x = coeff p B 0 π * c := by
    simpa using congrArg Subtype.val hc
  have hy : coeff p B 0 (↑u⁻¹ * (x : uniformTilt p B)) ∈ Bplus := by
    rw [map_mul, hc', ← mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
    exact c.2
  refine ⟨⟨_, mem_plusSubring_iff_coeff_zero.mpr hy⟩, Subtype.ext ?_⟩
  rw [Subring.coe_mul, ← hu, Units.mul_inv_cancel_left]

/-- **Surjectivity of `B♭⁺ → B⁺ ⧸ I`**: if `B⁺` is `I`-adically complete for an ideal `I ∋ p`, the
reduction of the sharp map modulo `I` is surjective iff every element of `B⁺` is a `p`-th power
modulo `I`. -/
theorem sharpQuot_surjective_iff (I : Ideal Bplus) (hI : (p : Bplus) ∈ I)
    [IsAdicComplete I Bplus] :
    Function.Surjective (sharpQuot h I hI) ↔ ∀ a : Bplus, ∃ b : Bplus, a - b ^ p ∈ I := by
  constructor
  · intro hs a
    obtain ⟨x, hx⟩ := hs (Ideal.Quotient.mk I a)
    -- `x♯ = (x⁽¹⁾) ^ p` with `x⁽¹⁾ ∈ B⁺`
    refine ⟨⟨coeff p B 1 x, mem_plusSubring_iff.mp x.2 1⟩, ?_⟩
    rw [← Ideal.Quotient.eq, ← hx, sharpQuot_apply]
    congr 1
    refine Subtype.ext ?_
    rw [coe_plusSharp, SubmonoidClass.coe_pow]
    exact (coeff_pow_p (x : uniformTilt p B) 0).symm
  · intro hroot
    rcases eq_or_ne I ⊤ with rfl | hItop
    · intro a
      exact ⟨0, Subsingleton.elim (h := Ideal.Quotient.subsingleton_iff.mpr rfl) _ _⟩
    have : Nontrivial (Bplus ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    have : CharP (Bplus ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
      rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
      exact hI
    have hfrob : Function.Surjective (frobenius (Bplus ⧸ I) p) := by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, hb⟩ := hroot a
      exact ⟨Ideal.Quotient.mk I b, by rw [frobenius_def, ← map_pow, Ideal.Quotient.eq.mpr hb]⟩
    -- a compatible system of `p`-th roots in `B⁺ ⧸ I` lifts to `B♭⁺` by `plusEquiv`
    intro a
    obtain ⟨y, hy⟩ := Perfection.coeff_surjective hfrob 0 a
    refine ⟨(plusEquiv h I).symm y, ?_⟩
    rw [← hy, ← RingEquiv.apply_symm_apply (plusEquiv h I) y, coeff_zero_plusEquiv h I hI,
      RingEquiv.apply_symm_apply]

/-- **The tilt modulo `π` is `B⁺` modulo `π♯`**: for `π ∈ B♭⁺` such that `π♯` is a unit of `B`
dividing `p` in `B⁺`, and such that the reduction `B♭⁺ → B⁺ ⧸ (π♯)` of the sharp map is surjective,
the sharp map induces a ring isomorphism `B♭⁺ ⧸ (π) ≃+* B⁺ ⧸ (π♯)`. Surjectivity holds for
`B⁺ = B°` when `B` is perfectoid (`sharpQuot_surjective`), for instance with `π` a
pseudouniformiser `ϖ♭` with compatible `p`-power roots. -/
noncomputable def sharpQuotEquiv {π : plusSubring p h} (hπ : IsUnit (coeff p B 0 π))
    (hπp : plusSharp p h π ∣ p)
    (hs : Function.Surjective (sharpQuot h _ (Ideal.mem_span_singleton.mpr hπp))) :
    plusSubring p h ⧸ Ideal.span {π} ≃+* Bplus ⧸ Ideal.span {plusSharp p h π} :=
  (Ideal.quotEquivOfEq (ker_sharpQuot h hπ hπp).symm).trans
    (RingHom.quotientKerEquivOfSurjective hs)

@[simp]
theorem sharpQuotEquiv_mk {π : plusSubring p h} (hπ : IsUnit (coeff p B 0 π))
    (hπp : plusSharp p h π ∣ p)
    (hs : Function.Surjective (sharpQuot h _ (Ideal.mem_span_singleton.mpr hπp)))
    (x : plusSubring p h) :
    sharpQuotEquiv h hπ hπp hs (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (plusSharp p h x) :=
  (rfl)

section Perfectoid

variable [IsPerfectoidTateRing p B]

/-- **The sharp map is surjective modulo `p`** on a perfectoid Tate ring, hence modulo every
ideal `I` of `B°` containing `p`: every element of `B°` is congruent modulo `I` to `x♯` for some
`x ∈ B♭°`. -/
theorem sharpQuot_surjective (I : Ideal (powerBoundedSubring B))
    (hI : (p : powerBoundedSubring B) ∈ I) :
    Function.Surjective (sharpQuot (isRingOfIntegralElements_powerBoundedSubring B) I hI) := by
  have hsurj := (sharpQuot_surjective_iff (isRingOfIntegralElements_powerBoundedSubring B)
    (Ideal.span {(p : powerBoundedSubring B)}) (Ideal.mem_span_singleton_self _)).mpr fun a ↦
      (IsPerfectoidTateRing.exists_natCast_dvd_sub_pow (p := p) a).imp fun _ hb ↦
        Ideal.mem_span_singleton.mpr hb
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨x, hx⟩ := hsurj (Ideal.Quotient.mk _ a)
  refine ⟨x, ?_⟩
  rw [sharpQuot_apply, Ideal.Quotient.eq]
  rw [sharpQuot_apply, Ideal.Quotient.eq] at hx
  exact (Ideal.span_singleton_le_iff_mem I).mpr hI hx

end Perfectoid

end TauCeti.Perfectoid.uniformTilt
