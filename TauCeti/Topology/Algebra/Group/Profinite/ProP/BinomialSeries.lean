/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.BinomialSeries
public import TauCeti.NumberTheory.Padics.PowerSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits

/-!
# The binomial series evaluated along a character of a pro-`p` group

Let `A` be a pro-`p` group and `χ : A →ₜ* ℤ_pˣ` a continuous character. Every value `χ a` is a
principal unit, `χ a ≡ 1 mod p` (`TauCeti.IsProP.mem_unitsPrincipal_one`), so a power series over
`ℤ_[p]` can be evaluated at `χ a - 1` (`PowerSeries.aeval`). This file identifies the value of the
binomial series `(1 + X) ^ u`, `u ∈ ℤ_[p]`, at `χ a - 1` with the image under `χ` of the `p`-adic
power `a ^ u` of `TauCeti.IsProP.padicPow`:

```text
(1 + (χ a - 1)) ^ u = χ (a ^ u)   in ℤ_[p].
```

Both sides are continuous in `u` and agree on the natural numbers, where the binomial series is
`(1 + X) ^ k` and the `p`-adic power is the `k`-th power, so they agree everywhere by density of
`ℕ` in `ℤ_[p]`. This is the scalar counterpart of
`TauCeti.completedGroupAlgebra.aeval_binomialSeries`, which evaluates the same series at `γ - 1` in
the completed group algebra `ℤ_p[[Γ]]`; the two together turn a divisibility question in `ℤ_p[[Γ]]`
about group elements and their `p`-adic powers into an equation between `p`-adic numbers, which is
how the basis corrections of Labute's classification of Demushkin groups are found.

## Main results

* `TauCeti.IsProP.hasEval_coe_apply_sub_one`: power series over `ℤ_[p]` can be evaluated at
  `χ a - 1`.
* `TauCeti.IsProP.aeval_binomialSeries`: the binomial series `(1 + X) ^ u` evaluated at `χ a - 1`
  is `χ (a ^ u)`, for the `p`-adic power `a ^ u`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, p. 122.
-/

public section

open PowerSeries.WithPiTopology

namespace TauCeti.IsProP

variable {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [TopologicalSpace A] (hA : IsProP p A)
  (χ : A →ₜ* ℤ_[p]ˣ)
include hA

/-- The values of a continuous character of a pro-`p` group into `ℤ_pˣ` are principal units, so
power series over `ℤ_[p]` can be evaluated at `χ a - 1`. -/
theorem hasEval_coe_apply_sub_one (a : A) : PowerSeries.HasEval ((χ a : ℤ_[p]) - 1) :=
  TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr
    (by simpa using mem_unitsPrincipal_iff.mp (hA.mem_unitsPrincipal_one χ a))

variable [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- **The binomial series `(1 + X) ^ u` evaluated at `χ a - 1` is `χ (a ^ u)`**, for a continuous
character `χ` of a pro-`p` group into `ℤ_pˣ` and the `p`-adic power `a ^ u` of
`TauCeti.IsProP.padicPow`. -/
@[simp]
theorem aeval_binomialSeries (a : A) (u : ℤ_[p]) :
    PowerSeries.aeval (hA.hasEval_coe_apply_sub_one χ a) (PowerSeries.binomialSeries ℤ_[p] u) =
      (χ (hA.padicPow a u) : ℤ_[p]) := by
  -- Both sides are continuous in `u` and agree on the dense subset `ℕ`, where the binomial
  -- series is `(1 + X) ^ k` and the `p`-adic power is `a ^ k`.
  have hpow : Continuous fun u : ℤ_[p] ↦ (χ (hA.padicPow a u) : ℤ_[p]) :=
    Units.continuous_val.comp (χ.continuous.comp
      (hA.continuous_padicPow.comp (continuous_id.prodMk continuous_const)))
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    ((PowerSeries.continuous_aeval _).comp PadicInt.continuous_binomialSeries) hpow
    (funext fun k ↦ ?_)) u
  simp [hA.padicPow_natCast, PowerSeries.binomialSeries_nat, PowerSeries.aeval_X]

end TauCeti.IsProP
