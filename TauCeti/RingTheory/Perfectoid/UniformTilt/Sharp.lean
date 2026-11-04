/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
public import TauCeti.RingTheory.Perfectoid.Plus

/-!
# The sharp map on the integral tilt

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with
tilt `B♭ = uniformTilt p B`, and let `B⁺` be a ring of integral elements with integral tilt
`B♭⁺ = lim_{x ↦ x ^ p} B⁺`. The *sharp map* `x ↦ x♯ = x⁽⁰⁾` is the zeroth coordinate. It is
multiplicative and vanishes only at `0`, but it is not additive; on `B♭⁺` it is additive modulo
`p`. So for every `ϖ ∈ B⁺` dividing `p`, reducing the sharp map modulo `ϖ` is a ring homomorphism
`B♭⁺ → B⁺ ⧸ (ϖ)`.

If `ϖ♭ ∈ B♭⁺` has a unit of `B` as zeroth coordinate, the kernel of the reduction modulo
`ϖ = ϖ♭♯` is the principal ideal `(ϖ♭)`: membership in `B♭⁺` is tested on the zeroth coordinate,
so `ϖ♭⁻¹ x` lies in `B♭⁺` once `x♯ ∈ ϖ B⁺`. If moreover Frobenius is surjective on `B⁺ ⧸ p` and
`B⁺` is `p`-adically complete, as for every ring of integral elements of a perfectoid Tate ring,
every element of `B⁺` is congruent modulo `p` to a sharp, through the Teichmüller lift of
`plusEquiv`. Hence for a perfectoid Tate ring `B` the sharp map induces a ring isomorphism
`B♭⁺ ⧸ (ϖ♭) ≃+* B⁺ ⧸ (ϖ♭♯)` whenever `ϖ♭♯` is a unit of `B` dividing `p` in `B⁺`. For
`B⁺ = B°` and a compatible system of roots `ϖ♭` of a pseudouniformiser `ϖ` with `ϖ ^ p ∣ p` in
`B°`, every power `ϖ♭ ^ q`, `q ∈ ℤ[1/p]` with `0 < q ≤ p`, qualifies; so `B♭° ⧸ (ϖ♭ ^ q)` is
identified with `B° ⧸ (ϖ ^ q)`.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.sharpPlus h`: the sharp map `B♭⁺ → B⁺`, `x ↦ x⁽⁰⁾`, as a
  multiplicative map.
* `TauCeti.Perfectoid.uniformTilt.sharpQuot h hϖ`: for `ϖ ∣ p` in `B⁺`, the ring homomorphism
  `B♭⁺ → B⁺ ⧸ (ϖ)`, `x ↦ x♯ mod ϖ`.
* `TauCeti.Perfectoid.uniformTilt.sharpQuotEquiv h hu hϖ`: for `B` perfectoid, the ring
  isomorphism `B♭⁺ ⧸ (ϖ♭) ≃+* B⁺ ⧸ (ϖ♭♯)`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.coeff_zero_eq_zero_iff`: `x♯ = 0` iff `x = 0`.
* `TauCeti.Perfectoid.uniformTilt.sharpPlus_add_sub_mem`: `(x + y)♯ - x♯ - y♯ ∈ p B⁺`.
* `TauCeti.Perfectoid.uniformTilt.ker_sharpQuot`: the kernel of `x ↦ x♯ mod ϖ♭♯` is `(ϖ♭)`.
* `TauCeti.Perfectoid.uniformTilt.exists_sub_sharpPlus_mem`: for `B` perfectoid, every element of
  `B⁺` is congruent modulo `p` to a sharp.
* `TauCeti.Perfectoid.uniformTilt.sharpQuot_surjective`: for `B` perfectoid, `x ↦ x♯ mod ϖ` is
  surjective.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and the text after it.
* P. Scholze, *Perfectoid spaces*, Lemma 3.4.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.10.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [hp : Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-- The sharp map `x ↦ x⁽⁰⁾` vanishes only at `0`: the coordinates of `x` are `p`-power roots of
`x⁽⁰⁾`, and a Hausdorff uniform Tate ring is reduced. -/
@[simp]
theorem coeff_zero_eq_zero_iff {x : uniformTilt p B} : coeff p B 0 x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ext fun n ↦ ?_, fun hx ↦ hx ▸ coeff_zero 0⟩
  have := IsUniform.isReduced (A := B)
  rw [coeff_zero]
  refine IsNilpotent.eq_zero ⟨p ^ n, ?_⟩
  rw [← hx, ← coeff_pow_p_pow x 0 n, zero_add]

variable {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)

/-- The sharp map on the integral tilt: the zeroth coordinate `B♭⁺ → B⁺`, `x ↦ x⁽⁰⁾`. It is
multiplicative, but only additive modulo `p` (`sharpPlus_add_sub_mem`). -/
noncomputable def sharpPlus : plusSubring p h →*₀ Bplus where
  toFun x := ⟨coeff p B 0 x, mem_plusSubring_iff.mp x.2 0⟩
  map_zero' := Subtype.ext (coeff_zero 0)
  map_one' := Subtype.ext (map_one (coeff p B 0))
  map_mul' x y := Subtype.ext (map_mul (coeff p B 0) (x : uniformTilt p B) y)

/-- The sharp of `x ∈ B♭⁺`, viewed in `B`, is the zeroth coordinate of `x`. -/
@[simp]
theorem coe_sharpPlus (x : plusSubring p h) : (sharpPlus h x : B) = coeff p B 0 x := (rfl)

/-- **The sharp map is additive modulo `p`** on the integral tilt:
`(x + y)♯ - x♯ - y♯ ∈ p B⁺`. -/
theorem sharpPlus_add_sub_mem (x y : plusSubring p h) :
    sharpPlus h (x + y) - sharpPlus h x - sharpPlus h y ∈ Ideal.span {(p : Bplus)} := by
  obtain ⟨z, hz, he⟩ := Set.mem_smul_set.mp <| coeff_add_sub_mem_of_forall_mem
    (Bplus.toAddSubgroup.isClosed_of_isOpen h.isOpen) h.le_powerBoundedSubring
    (mem_plusSubring_iff.mp x.2) (mem_plusSubring_iff.mp y.2) 0
  refine Ideal.mem_span_singleton'.mpr ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  rw [smul_eq_mul] at he
  simp only [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, coe_sharpPlus,
    Subring.coe_add]
  linear_combination he

/-- The reduction of the sharp map modulo an element `ϖ` of `B⁺` dividing `p`: the ring
homomorphism `B♭⁺ → B⁺ ⧸ (ϖ)`, `x ↦ x♯ mod ϖ`. -/
noncomputable def sharpQuot {ϖ : Bplus} (hϖ : ϖ ∣ (p : Bplus)) :
    plusSubring p h →+* Bplus ⧸ Ideal.span {ϖ} where
  toFun x := Ideal.Quotient.mk _ (sharpPlus h x)
  map_zero' := by rw [map_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add' x y := by
    rw [← map_add, Ideal.Quotient.eq, ← sub_sub]
    exact Ideal.span_singleton_le_span_singleton.mpr hϖ (sharpPlus_add_sub_mem h x y)

/-- `sharpQuot` sends `x` to the class of its sharp. -/
@[simp]
theorem sharpQuot_apply {ϖ : Bplus} (hϖ : ϖ ∣ (p : Bplus)) (x : plusSubring p h) :
    sharpQuot h hϖ x = Ideal.Quotient.mk _ (sharpPlus h x) := (rfl)

/-- **The kernel of the sharp map modulo `ϖ♭♯` is `(ϖ♭)`**, for `ϖ♭ ∈ B♭⁺` whose zeroth
coordinate is a unit of `B` dividing `p` in `B⁺`. -/
theorem ker_sharpQuot {ϖ : plusSubring p h} (hu : IsUnit (coeff p B 0 ϖ))
    (hϖ : sharpPlus h ϖ ∣ (p : Bplus)) :
    RingHom.ker (sharpQuot h hϖ) = Ideal.span {ϖ} := by
  ext x
  rw [RingHom.mem_ker, sharpQuot_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨sharpPlus h a, by rw [← ha, map_mul]⟩⟩
  -- `ϖ♭⁻¹ x` has zeroth coordinate `a ∈ B⁺`, hence lies in `B♭⁺`
  have hU : IsUnit (ϖ : uniformTilt p B) := isUnit_iff_coeff_zero.mpr hu
  have ha' : (a : B) * coeff p B 0 ϖ = coeff p B 0 x := by
    simpa only [Subring.coe_mul, coe_sharpPlus] using congrArg Subtype.val ha
  have hinv : coeff p B 0 (↑hU.unit⁻¹ : uniformTilt p B) * coeff p B 0 ϖ = 1 := by
    rw [← map_mul, hU.val_inv_mul, map_one]
  have hy : coeff p B 0 (↑hU.unit⁻¹ * x) = a := by
    rw [map_mul, ← ha']
    linear_combination (a : B) * hinv
  refine ⟨⟨_, mem_plusSubring_iff_coeff_zero.mpr (hy ▸ a.2)⟩, Subtype.ext ?_⟩
  rw [Subring.coe_mul, mul_comm, ← mul_assoc, hU.mul_val_inv, one_mul]

/-- If `B⁺` is `p`-adically complete and every element of `B⁺` is a `p`-th power modulo `p`, then
every element of `B⁺` is congruent modulo `p` to a sharp. The sharp is the Teichmüller lift of a
compatible system of `p`-th roots in `B⁺ ⧸ p`. -/
theorem exists_sub_sharpPlus_mem_of_forall_exists_natCast_dvd_sub_pow
    [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus]
    (hs : ∀ x : Bplus, ∃ y : Bplus, (p : Bplus) ∣ x - y ^ p) (x : Bplus) :
    ∃ y : plusSubring p h, x - sharpPlus h y ∈ Ideal.span {(p : Bplus)} := by
  by_cases hpu : IsUnit (p : Bplus)
  · exact ⟨0, by rw [Ideal.span_singleton_eq_top.mpr hpu]; trivial⟩
  have : Fact (¬ IsUnit (p : Bplus)) := ⟨hpu⟩
  obtain ⟨z, hz⟩ := Perfection.coeff_surjective ((surjective_frobenius_modP_iff Bplus).mpr hs) 0
    (Ideal.Quotient.mk _ x)
  refine ⟨(plusEquiv h (Ideal.span {(p : Bplus)})).symm z, Ideal.Quotient.eq.mp ?_⟩
  have hsharp : sharpPlus h ((plusEquiv h (Ideal.span {(p : Bplus)})).symm z) =
      Perfection.teichmuller₀ p _ z :=
    Subtype.ext (by rw [coe_sharpPlus, coeff_zero_plusEquiv_symm])
  rw [hsharp, Perfection.mk_teichmuller₀, ← hz]

section Perfectoid

variable [IsPerfectoidTateRing p B]

/-- **Every element of `B⁺` is congruent modulo `p` to a sharp**, for a ring of integral elements
`B⁺` of a perfectoid Tate ring `B`. -/
theorem exists_sub_sharpPlus_mem (x : Bplus) :
    ∃ y : plusSubring p h, x - sharpPlus h y ∈ Ideal.span {(p : Bplus)} :=
  have := h.isAdicComplete_span_natCast (p := p)
  exists_sub_sharpPlus_mem_of_forall_exists_natCast_dvd_sub_pow h
    (h.exists_natCast_dvd_sub_pow (p := p)) x

/-- For a perfectoid Tate ring `B`, the sharp map modulo any `ϖ ∈ B⁺` dividing `p` is
surjective onto `B⁺ ⧸ (ϖ)`. -/
theorem sharpQuot_surjective {ϖ : Bplus} (hϖ : ϖ ∣ (p : Bplus)) :
    Function.Surjective (sharpQuot h hϖ) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := exists_sub_sharpPlus_mem (p := p) h x
  exact ⟨y, (Ideal.Quotient.eq.mpr
    (Ideal.span_singleton_le_span_singleton.mpr hϖ hy)).symm⟩

/-- **The sharp map identifies `B♭⁺ ⧸ (ϖ♭)` with `B⁺ ⧸ (ϖ♭♯)`** for a perfectoid Tate ring `B`
and `ϖ♭ ∈ B♭⁺` whose zeroth coordinate `ϖ♭♯` is a unit of `B` dividing `p` in `B⁺`. -/
noncomputable def sharpQuotEquiv {ϖ : plusSubring p h} (hu : IsUnit (coeff p B 0 ϖ))
    (hϖ : sharpPlus h ϖ ∣ (p : Bplus)) :
    plusSubring p h ⧸ Ideal.span {ϖ} ≃+* Bplus ⧸ Ideal.span {sharpPlus h ϖ} :=
  (Ideal.quotEquivOfEq (ker_sharpQuot h hu hϖ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (sharpQuot_surjective h hϖ))

/-- `sharpQuotEquiv` sends the class of `x` to the class of its sharp. -/
@[simp]
theorem sharpQuotEquiv_mk {ϖ : plusSubring p h} (hu : IsUnit (coeff p B 0 ϖ))
    (hϖ : sharpPlus h ϖ ∣ (p : Bplus)) (x : plusSubring p h) :
    sharpQuotEquiv h hu hϖ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sharpPlus h x) :=
  (rfl)

end Perfectoid

end TauCeti.Perfectoid.uniformTilt
