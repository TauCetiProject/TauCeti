/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.FieldTheory.IntermediateField.AdjoinEqTop
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic

/-!
# The Frobenius acts on multiquadratic generators by Legendre symbols

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of
integers `d i`, and let `p` be an odd prime dividing none of the `d i`. The multiquadratic
roadmap's Layer 1 states the splitting law in two forms: `p` splits completely iff every `d i`
is a quadratic residue mod `p` (`TauCeti.NumberField.ncard_primesOver_multiquadratic_iff`),
and, more precisely, the Frobenius at `p` acts on the generators by the Legendre symbols. This
file supplies the second, finer form. An arithmetic Frobenius exists at every prime `Q` of
`𝓞 K` above `p` and acts on each generator by the corresponding symbol,

`σ (r i) = legendreSym p (d i) • r i`

(`TauCeti.NumberField.exists_isArithFrobAt_multiquadratic`), and the Frobenius is trivial iff
every symbol is `1` (`isArithFrobAt_multiquadratic_eq_one_iff`). The resulting sign-vector
description under the identification `Gal(K/ℚ) ≅ (ℤ/2)ⁿ` of
`TauCeti.Multiquadratic.galoisGroupEquiv` is then a composition, not a further theorem: feeding
the generator action `σ (r i) = legendreSym p (d i) • r i` into the bridge
`TauCeti.Multiquadratic.signPattern_eq_ite_of_zsmul_gen` gives
`signPattern root σ i = if legendreSym p (d i) = 1 then 0 else 1`, which `galoisGroupEquiv_apply`
packages as the vector `((d₁/p), …, (dₙ/p))`.

## Main results

* `TauCeti.NumberField.exists_isArithFrobAt_multiquadratic`: at every prime `Q` over `p` there
  is a Frobenius, and it sends each generator `r i` to `legendreSym p (d i) • r i`.
* `TauCeti.NumberField.isArithFrobAt_multiquadratic_eq_one_iff`: a Frobenius at `Q` is the
  identity iff every `d i` is a quadratic residue mod `p`.
-/

public section

open NumberField Ideal

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}
  {p : ℕ} [Fact p.Prime]

/-- **A multiquadratic Frobenius is trivial iff every radicand is a residue.** Let
`K = ℚ(√d₁, …, √dₙ)` be generated over `ℚ` by the square roots `r i` of the integers `d i`,
let `p` be an odd prime with `p ∤ d i` for all `i`, and let `σ` be an arithmetic Frobenius at
an ideal `Q` of `𝓞 K` above `p`. Then `σ = 1` iff every `d i` is a quadratic residue mod `p`.
Combined with the splitting law, this is the Frobenius-theoretic reading of complete
splitting. -/
theorem isArithFrobAt_multiquadratic_eq_one_iff (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ = 1 ↔ ∀ i, legendreSym p (d i) = 1 := by
  constructor
  · rintro rfl i
    exact (isArithFrobAt_apply_sqrt_eq_self_iff hodd (hcop i) (hr i) Q hσ).mp
      (AlgEquiv.one_apply (r i))
  · intro hqr
    refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
    rintro x ⟨i, rfl⟩
    exact (isArithFrobAt_apply_sqrt_eq_self_iff hodd (hcop i) (hr i) Q hσ).mpr (hqr i)

/-- **The Frobenius of a multiquadratic field acts on each generator by a Legendre symbol.**
For a Galois number field `K` with elements `r i` satisfying `r i ² = d i ∈ ℤ`, an odd prime
`p` with `p ∤ d i` for all `i`, and any prime `Q` of `𝓞 K` above `p`, there is an arithmetic
Frobenius `σ ∈ Gal(K/ℚ)` at `Q`, and it sends each generator to the corresponding Legendre
multiple: `σ (r i) = legendreSym p (d i) • r i`. This is the generator-wise Frobenius input of
the multiquadratic splitting law; the sign-vector description under `galoisGroupEquiv` is not
formed here (see the module docstring). The `IsGalois ℚ K` hypothesis holds in particular when
the `r i` generate `K`, via `TauCeti.Multiquadratic.isGalois_of_adjoin_eq_top`. -/
theorem exists_isArithFrobAt_multiquadratic [IsGalois ℚ K] (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q ∧
      ∀ i, σ (r i) = legendreSym p (d i) • r i := by
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_of_liesOver (p := p) Q
  exact ⟨σ, hσ, fun i => isArithFrobAt_apply_sqrt hodd (hcop i) (hr i) Q hσ⟩

end TauCeti.NumberField
