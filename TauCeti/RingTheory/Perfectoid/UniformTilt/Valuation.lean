/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.CharP
public import TauCeti.RingTheory.Valuation.Continuous.Limit

/-!
# Pulling continuous valuations back to the tilt along the sharp map

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, and let
`v : Valuation B Γ₀` be a *continuous* valuation (`Valuation.IsContinuous`). Although the sharp map
`♯ = coeff p B 0 : uniformTilt p B →* B` is only multiplicative, composing `v` with `♯` defines a
valuation `v ∘ ♯` on the tilt `B♭ = uniformTilt p B`, which is again continuous (Scholze,
*Perfectoid spaces*, Lemma 6.2; *Étale cohomology of diamonds*, Lemma 3.16).

Continuity of `v` enters directly into the ultrametric inequality for `v ∘ ♯`: by definition of the
limit addition on `B♭`, the zeroth coordinate `(f + g)♯` is the limit as `m → ∞` of
`(f⁽ᵐ⁾ + g⁽ᵐ⁾) ^ p ^ m`. At stage `m`,

```text
v((f⁽ᵐ⁾ + g⁽ᵐ⁾) ^ p ^ m) ≤ max(v(f⁽ᵐ⁾), v(g⁽ᵐ⁾)) ^ p ^ m
                         = max(v(f⁽ᵐ⁾ ^ p ^ m), v(g⁽ᵐ⁾ ^ p ^ m))
                         = max(v(f♯), v(g♯)),
```

and `Valuation.IsContinuous.le_of_tendsto` passes this closed upper bound to the limit `(f + g)♯`.
Continuity of `v ∘ ♯` itself is immediate from continuity of `♯`: the attained-value open balls
`{f | (v ∘ ♯) f < (v ∘ ♯) g}` are the preimages under `♯` of `{b | v b < v (g♯)}`.

No group hypothesis on `Γ₀`, no base field, and no perfectoid hypothesis on `B` are needed.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.comapValuation p hv` : the valuation `f ↦ v (f♯)` on
  `uniformTilt p B` associated to a continuous valuation `v : Valuation B Γ₀`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.isContinuous_comapValuation` : `comapValuation p hv` is
  continuous.
* `TauCeti.Perfectoid.uniformTilt.isEquiv_comapValuation` : equivalent continuous valuations pull
  back to equivalent valuations on the tilt.
* `TauCeti.Perfectoid.uniformTilt.coe_supp_comapValuation` : the support of `comapValuation p hv`
  has underlying set `(coeff p B 0) ⁻¹' v.supp`, making `(coeff p B 0) ⁻¹' v.supp` a prime ideal of
  `B♭` despite `coeff p B 0` not being additive.
* `TauCeti.Perfectoid.uniformTilt.comapValuation_comap` : functoriality along `uniformTilt.map`.
* `TauCeti.Perfectoid.uniformTilt.comapValuation_eq_comap_equivOfCharP` : when `B` is perfect of
  characteristic `p`, `comapValuation` agrees with ordinary ring-homomorphism pullback along
  `equivOfCharP p B`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Lemma 6.2.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, Lemma 3.16.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, §2.7.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
  {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommMonoidWithZero Γ₀']

variable (p) in
/-- **Pullback of a continuous valuation to the tilt along `♯`.** For a continuous valuation
`v : Valuation B Γ₀`, `f ↦ v (coeff p B 0 f)` satisfies the ultrametric inequality on
`uniformTilt p B` because `(f + g)⁽⁰⁾ = lim_m (f⁽ᵐ⁾ + g⁽ᵐ⁾) ^ p ^ m` and closed upper bounds for a
continuous valuation pass to topological limits (`Valuation.IsContinuous.le_of_tendsto`). -/
noncomputable def comapValuation {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    Valuation (uniformTilt p B) Γ₀ where
  toFun f := v (coeff p B 0 f)
  map_zero' := by rw [coeff_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' f g := by rw [map_mul, map_mul]
  map_add_le_max' f g := by
    have hlim : Tendsto (fun m ↦ (coeff p B m f + coeff p B m g) ^ p ^ m)
        atTop (𝓝 (coeff p B 0 (f + g))) := by
      simpa only [zero_add] using coeff_add f g 0
    refine hv.le_of_tendsto hlim (Eventually.of_forall fun m ↦ ?_)
    have hf : coeff p B m f ^ p ^ m = coeff p B 0 f := by
      simpa only [zero_add] using coeff_pow_p_pow f 0 m
    have hg : coeff p B m g ^ p ^ m = coeff p B 0 g := by
      simpa only [zero_add] using coeff_pow_p_pow g 0 m
    calc v ((coeff p B m f + coeff p B m g) ^ p ^ m)
        = v (coeff p B m f + coeff p B m g) ^ p ^ m := map_pow _ _ _
      _ ≤ max (v (coeff p B m f)) (v (coeff p B m g)) ^ p ^ m :=
          pow_le_pow_left' (v.map_add _ _) _
      _ = max (v (coeff p B m f) ^ p ^ m) (v (coeff p B m g) ^ p ^ m) :=
          max_pow _ _ _
      _ = max (v (coeff p B 0 f)) (v (coeff p B 0 g)) := by
          rw [← v.map_pow, ← v.map_pow, hf, hg]

/-- `comapValuation` evaluates `v` on the zeroth coordinate `f♯ = coeff p B 0 f`. -/
@[simp]
theorem comapValuation_apply {v : Valuation B Γ₀} (hv : v.IsContinuous) (f : uniformTilt p B) :
    comapValuation p hv f = v (coeff p B 0 f) :=
  (rfl)

/-- **The pulled-back valuation on the tilt is continuous**: its attained-value open balls are the
preimages under the continuous map `coeff p B 0` of attained-value open balls of `v`. -/
theorem isContinuous_comapValuation {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    (comapValuation p hv).IsContinuous :=
  Valuation.isContinuous_def.mpr fun g ↦
    (Valuation.isContinuous_def.mp hv (coeff p B 0 g)).preimage (continuous_coeff 0)

/-- Equivalent continuous valuations induce equivalent valuations on the tilt. -/
theorem isEquiv_comapValuation {v : Valuation B Γ₀} {w : Valuation B Γ₀'}
    (hv : v.IsContinuous) (hw : w.IsContinuous) (h : v.IsEquiv w) :
    (comapValuation p hv).IsEquiv (comapValuation p hw) :=
  fun f g ↦ h (coeff p B 0 f) (coeff p B 0 g)

/-- Membership in the support of `comapValuation p hv` is tested on the zeroth coordinate. -/
theorem mem_supp_comapValuation_iff {v : Valuation B Γ₀} (hv : v.IsContinuous)
    (f : uniformTilt p B) :
    f ∈ (comapValuation p hv).supp ↔ coeff p B 0 f ∈ v.supp := by
  rw [Valuation.mem_supp_iff, Valuation.mem_supp_iff, comapValuation_apply]

/-- The support of `comapValuation p hv` has underlying set `(coeff p B 0) ⁻¹' v.supp`. -/
@[simp]
theorem coe_supp_comapValuation {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    ((comapValuation p hv).supp : Set (uniformTilt p B)) = coeff p B 0 ⁻¹' (v.supp : Set B) :=
  Set.ext (mem_supp_comapValuation_iff hv)

section Map

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))]

/-- **Naturality of `comapValuation` under continuous ring homomorphisms.** Pulling `w` back along
`g : B →+* C` and then to `B♭` agrees with pulling `w` back to `C♭` and then along `g♭`. -/
theorem comapValuation_comap (g : B →+* C) (hg : Continuous g) {w : Valuation C Γ₀}
    (hw : w.IsContinuous) :
    comapValuation p (hw.comap hg) = (comapValuation p hw).comap (map g hg) :=
  Valuation.ext fun f ↦ by simp

end Map

section CharP

variable [CharP B p] [PerfectRing B p]

/-- **In characteristic `p`, `comapValuation` is pullback along `equivOfCharP p B`.** -/
theorem comapValuation_eq_comap_equivOfCharP {v : Valuation B Γ₀} (hv : v.IsContinuous) :
    comapValuation p hv = v.comap (equivOfCharP p B : uniformTilt p B →+* B) :=
  Valuation.ext fun f ↦ by simp

end CharP

end TauCeti.Perfectoid.uniformTilt
