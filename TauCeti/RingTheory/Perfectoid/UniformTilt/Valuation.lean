/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.CharP
public import TauCeti.RingTheory.Valuation.Continuous.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Pulling back continuous valuations along the sharp map

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with
tilt `B♭ = uniformTilt p B` and sharp map `♯ = coeff p B 0 : B♭ →* B`. Although `♯` is only a
monoid homomorphism and not additive, composing a *continuous* valuation `v : Valuation B Γ₀`
with `♯` yields an honest continuous valuation `comapSharp hv : Valuation B♭ Γ₀`.

The ultrametric inequality for `(x + y)♯` comes from the limit formula
`(x + y)♯ = lim_{m → ∞} (x⁽ᵐ⁾ + y⁽ᵐ⁾) ^ p ^ m` (`coeff_add`): for each `m`,
```text
v((x⁽ᵐ⁾ + y⁽ᵐ⁾) ^ p ^ m) ≤ max(v(x⁽ᵐ⁾), v(y⁽ᵐ⁾)) ^ p ^ m = max(v(x♯), v(y♯)),
```
and closed valuation balls `{a : B | v a ≤ γ}` of a continuous valuation are topologically closed
(`Valuation.IsContinuous.isClosed_le`), so the bound passes to the limit. Continuity of the
pulled-back valuation then follows immediately from continuity of `♯`.

No Tate or perfectoid assumption on `B♭` is needed here, and the value codomain `Γ₀` need only be
a `LinearOrderedCommMonoidWithZero`.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.comapSharp`: the continuous valuation `x ↦ v (x♯)` on
  `uniformTilt p B` attached to a continuous valuation `v` on `B`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.valuation_coeff_zero_add_le`: the ultrametric inequality
  `v ((x + y)♯) ≤ max (v (x♯)) (v (y♯))` for a continuous valuation `v`.
* `TauCeti.Perfectoid.uniformTilt.isContinuous_comapSharp`: `comapSharp hv` is continuous.
* `TauCeti.Perfectoid.uniformTilt.comapSharp_le_one_of_mem_plusSubring`: if `v ≤ 1` on `B⁺`, then
  `comapSharp hv ≤ 1` on the integral tilt `B♭⁺`.
* `TauCeti.Perfectoid.uniformTilt.isEquiv_comapSharp`: `comapSharp` preserves valuation
  equivalence.
* `TauCeti.Perfectoid.uniformTilt.comapSharp_comap`: naturality under continuous ring
  homomorphisms `g : B →+* C`.
* `TauCeti.Perfectoid.uniformTilt.comapSharp_eq_comap_equivOfCharP`: on a perfect ring of
  characteristic `p`, `comapSharp` agrees with `Valuation.comap` along `equivOfCharP`.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.6.12.
* P. Scholze, *Perfectoid spaces*, proof of Theorem 6.3.
* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.12.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommMonoidWithZero Γ₀']

/-- Raising the valuation of the `(n + m)`-th coordinate to the `p ^ m`-th power recovers the
valuation of the `n`-th coordinate. -/
@[simp]
theorem valuation_coeff_pow (v : Valuation B Γ₀) (x : uniformTilt p B) (n m : ℕ) :
    v (coeff p B (n + m) x) ^ p ^ m = v (coeff p B n x) := by
  rw [← map_pow, coeff_pow_p_pow]

/-- Raising the valuation of the `m`-th coordinate to the `p ^ m`-th power recovers `v (x♯)`. -/
theorem valuation_coeff_pow_zero (v : Valuation B Γ₀) (x : uniformTilt p B) (m : ℕ) :
    v (coeff p B m x) ^ p ^ m = v (coeff p B 0 x) := by
  simpa only [zero_add] using valuation_coeff_pow v x 0 m

/-- **The ultrametric inequality for the sharp map under a continuous valuation.** Each term
`(x⁽ᵐ⁾ + y⁽ᵐ⁾) ^ p ^ m` of the limit defining `(x + y)♯` has `v`-value bounded by
`max (v (x♯)) (v (y♯))`, and closed valuation balls of `v` are topologically closed. -/
theorem valuation_coeff_zero_add_le {v : Valuation B Γ₀} (hv : v.IsContinuous)
    (x y : uniformTilt p B) :
    v (coeff p B 0 (x + y)) ≤ max (v (coeff p B 0 x)) (v (coeff p B 0 y)) := by
  refine (hv.isClosed_le _).mem_of_tendsto (coeff_add x y 0)
    (Eventually.of_forall fun m ↦ ?_)
  simp only [Set.mem_ofPred_eq, zero_add, map_pow]
  calc v (coeff p B m x + coeff p B m y) ^ p ^ m
      ≤ max (v (coeff p B m x)) (v (coeff p B m y)) ^ p ^ m :=
        pow_le_pow_left' (v.map_add _ _) (p ^ m)
    _ = max (v (coeff p B m x) ^ p ^ m) (v (coeff p B m y) ^ p ^ m) :=
        (pow_left_mono (p ^ m)).map_max
    _ = max (v (coeff p B 0 x)) (v (coeff p B 0 y)) := by
        rw [valuation_coeff_pow_zero, valuation_coeff_pow_zero]

/-- **Pullback of a continuous valuation along the sharp map.** Although `coeff p B 0` is not a
ring homomorphism, composing it with a continuous valuation `v` on `B` gives a valuation on
`uniformTilt p B`. -/
noncomputable def comapSharp {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    Valuation (uniformTilt p B) Γ₀ where
  toFun x := v (coeff p B 0 x)
  map_zero' := by rw [coeff_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add_le_max' x y := valuation_coeff_zero_add_le hv x y

/-- `comapSharp hv` evaluates `v` on the zeroth coordinate `x♯`. -/
@[simp]
theorem comapSharp_apply {v : Valuation B Γ₀} (hv : v.IsContinuous) (x : uniformTilt p B) :
    comapSharp (p := p) hv x = v (coeff p B 0 x) := (rfl)

/-- The valuation pulled back along sharp is continuous: its attained-value open balls are the
preimages under the continuous map `coeff p B 0` of attained-value open balls of `v`. -/
theorem isContinuous_comapSharp {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    (comapSharp (p := p) hv).IsContinuous :=
  Valuation.isContinuous_def.mpr fun y ↦
    (Valuation.isContinuous_def.mp hv (coeff p B 0 y)).preimage (continuous_coeff 0)

/-- An element of the tilt lies in the support of `comapSharp hv` iff its zeroth coordinate lies
in the support of `v`. -/
theorem mem_supp_comapSharp_iff {v : Valuation B Γ₀} (hv : v.IsContinuous)
    (x : uniformTilt p B) :
    x ∈ (comapSharp (p := p) hv).supp ↔ coeff p B 0 x ∈ v.supp := by
  simp only [Valuation.mem_supp_iff, comapSharp_apply]

/-- As a set, the support of `comapSharp hv` is the preimage of `v.supp` under sharp. -/
theorem coe_supp_comapSharp {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    ((comapSharp (p := p) hv).supp : Set (uniformTilt p B)) = coeff p B 0 ⁻¹' (v.supp : Set B) :=
  Set.ext (mem_supp_comapSharp_iff hv)

/-- If `v` is bounded by `1` on a ring of integral elements `B⁺`, then `comapSharp hv` is bounded
by `1` on its integral tilt `B♭⁺`. -/
theorem comapSharp_le_one_of_mem_plusSubring {Bplus : Subring B}
    (hplus : IsRingOfIntegralElements Bplus) {v : Valuation B Γ₀} (hv : v.IsContinuous)
    (hv_plus : ∀ b ∈ Bplus, v b ≤ 1) {x : uniformTilt p B} (hx : x ∈ plusSubring p hplus) :
    comapSharp (p := p) hv x ≤ 1 :=
  hv_plus _ (mem_plusSubring_iff_coeff_zero.mp hx)

/-- Equivalent continuous valuations induce equivalent valuations on the tilt. -/
theorem isEquiv_comapSharp {v : Valuation B Γ₀} {w : Valuation B Γ₀'}
    (hv : v.IsContinuous) (hw : w.IsContinuous) (heq : v.IsEquiv w) :
    (comapSharp (p := p) hv).IsEquiv (comapSharp (p := p) hw) :=
  fun x y ↦ heq (coeff p B 0 x) (coeff p B 0 y)

section Map

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))]

/-- Pulling a continuous valuation back along a continuous ring homomorphism `g : B →+* C` and then
along sharp is the same as pulling it back along sharp and then along `g♭`. -/
theorem comapSharp_comap {g : B →+* C} (hg : Continuous g) {w : Valuation C Γ₀}
    (hw : w.IsContinuous) :
    comapSharp (p := p) (hw.comap hg) = (comapSharp (p := p) hw).comap (map g hg) := by
  ext x
  simp

end Map

section CharP

variable [CharP B p] [PerfectRing B p]

/-- On a perfect ring of characteristic `p`, `comapSharp` coincides with ordinary valuation
pullback along the ring isomorphism `equivOfCharP p B`. -/
theorem comapSharp_eq_comap_equivOfCharP {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    comapSharp (p := p) hv = v.comap (equivOfCharP p B).toRingHom := by
  ext x
  simp

end CharP

end TauCeti.Perfectoid.uniformTilt
