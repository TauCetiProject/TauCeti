/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.NumberField.DedekindZeta
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# Reading off the residue of a Dedekind zeta function from a factorization

When the Dedekind zeta function `ζ_K` of a number field `K` factors as `ζ_K(s) = ζ(s) g(s)` near
`1` along the real ray `s > 1`, multiplying by `s - 1` and passing to the limit `s → 1⁺` matches
Mathlib's `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` against
`TauCeti.tendsto_sub_one_mul_riemannZeta_nhdsGT` and identifies `NumberField.dedekindZeta_residue K`
with the right-hand limit of `g` at `1`.

## Main results

* `TauCeti.NumberField.dedekindZeta_residue_eq_of_eventuallyEq_riemannZeta_mul`: if
  `dedekindZeta K s = riemannZeta s * g s` eventually as `s → 1⁺` in `ℝ` and `g s → c`, then
  `(dedekindZeta_residue K : ℂ) = c`.
-/

public section

open Filter NumberField
open scoped Topology

namespace TauCeti.NumberField

/-- **Residue of `ζ_K` from a factorization `ζ_K = ζ · g`.** If `dedekindZeta K s =
riemannZeta s * g s` on a right neighborhood of `1` along the real axis and `g s → c` as `s → 1⁺`,
then `(NumberField.dedekindZeta_residue K : ℂ) = c`. -/
theorem dedekindZeta_residue_eq_of_eventuallyEq_riemannZeta_mul
    (K : Type*) [Field K] [NumberField K] {g : ℝ → ℂ} {c : ℂ}
    (hfac : (fun s : ℝ ↦ dedekindZeta K s) =ᶠ[𝓝[>] 1] fun s : ℝ ↦ riemannZeta s * g s)
    (hg : Tendsto g (𝓝[>] 1) (𝓝 c)) :
    (dedekindZeta_residue K : ℂ) = c := by
  have hF : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 c) :=
    (one_mul c ▸ TauCeti.tendsto_sub_one_mul_riemannZeta_nhdsGT.mul hg).congr'
      (hfac.mono fun s hs ↦ by dsimp only at hs ⊢; rw [hs, mul_assoc])
  exact tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) hF

end TauCeti.NumberField
