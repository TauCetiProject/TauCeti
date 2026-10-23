/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
-- Proof-only: the degree bound on the exponent of a finite purely inseparable extension.
import TauCeti.FieldTheory.PurelyInseparable.Exponent

/-!
# The factorisation of an isogeny through a Frobenius power

Every isogeny `φ : W₁ → W₂` over a field `F` of exponential characteristic `p` factors as
`φ = φ_sep ∘ F^r`, where `F^r : W₁ → W₁⁽ᵖʳ⁾` is the `r`-fold relative Frobenius and `φ_sep` is a
**separable** isogeny (Silverman II.2.12). The power `p ^ r` is determined by `φ`: it is the
inseparable degree of `φ`, so for `p > 1` the exponent `r` is determined as well. The factor
`φ_sep` is unique, and its degree is the separable degree of `φ`. In characteristic zero `p = 1`,
every `r` has `p ^ r = 1`, the inseparable degree of `φ`, and the statement says that every isogeny
is separable.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq_iff`: `φ` factors
  through `F^n`, by a unique isogeny, exactly when `p ^ n` divides its inseparable degree; with
  `TauCeti.Isogeny.fieldRange_le_fieldRange_iterateRelativeFrobeniusIsogeny_iff` as its
  subfield-criterion form.
* `TauCeti.Isogeny.existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq`: **the factorisation
  theorem**, that `φ` factors through `F^r` by a unique isogeny when `p ^ r` is its inseparable
  degree.
* `TauCeti.Isogeny.isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq` and
  `TauCeti.Isogeny.inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq`: a factor
  of `φ` through `F^r` is separable exactly when `p ^ r` is the inseparable degree of `φ`, the two
  directions of the equivalence
  `isSeparable_iff_inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq`.
* `TauCeti.Isogeny.separableDegree_eq_of_comp_iterateRelativeFrobeniusIsogeny_eq` and
  `TauCeti.Isogeny.degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq`: a
  factor through `F^r` has the separable degree of `φ`, which is its degree when it is separable.
* `TauCeti.Isogeny.exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq`: **every isogeny
  is a separable isogeny after a Frobenius power** (Silverman II.2.12).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p] {W₁ W₂ : WeierstrassCurve.Affine F}
  (φ : Isogeny W₁ W₂)

-- The exact case `p ^ r = deg_i φ` of the subfield criterion below, where the separable closure
-- enters: `F(W₁)/S` is purely inseparable of degree `p ^ r`, so `S` contains every `p ^ r`-th
-- power and with them the pulled-back `F(W₁⁽ᵖʳ⁾)`; the two have the same degree under `F(W₁)`,
-- hence coincide.
private theorem fieldRange_le_of_inseparableDegree_eq_pow {r : ℕ}
    (hr : φ.inseparableDegree = p ^ r) :
    φ.fieldPullback.fieldRange ≤
      (iterateRelativeFrobeniusIsogeny p W₁ r).fieldPullback.fieldRange := by
  -- `S`: the separable closure of `φ^*F(W₂)` in `F(W₁)`, read over the constants
  set S : IntermediateField F W₁.FunctionField :=
    (separableClosure φ.fieldPullback.fieldRange W₁.FunctionField).restrictScalars F with hS_def
  -- `F(W₁)/S` is purely inseparable of degree `p ^ r`
  have hS : Module.finrank (separableClosure φ.fieldPullback.fieldRange W₁.FunctionField)
      W₁.FunctionField = p ^ r := by
    rwa [inseparableDegree_def] at hr
  -- so every `p ^ r`-th power lies in `S`, and with them the pulled-back `F(W₁⁽ᵖʳ⁾)`
  have hle : (iterateRelativeFrobeniusIsogeny p W₁ r).fieldPullback.fieldRange ≤ S := by
    rw [fieldRange_iterateRelativeFrobeniusIsogeny_le_iff]
    intro z
    obtain ⟨y, hy⟩ := TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow _ _ p hS.le z
    rw [hS_def, IntermediateField.mem_restrictScalars, ← hy]
    exact y.2
  -- both have degree `p ^ r` under `F(W₁)`, so they coincide
  have heq : (iterateRelativeFrobeniusIsogeny p W₁ r).fieldPullback.fieldRange = S :=
    IntermediateField.eq_of_le_of_finrank_eq' hle <| by
      rw [← degree_def, degree_iterateRelativeFrobeniusIsogeny]
      exact hS.symm
  rw [heq]
  intro z hz
  exact (separableClosure _ _).algebraMap_mem (⟨z, hz⟩ : φ.fieldPullback.fieldRange)

/-- **The pulled-back function field of `W₂` lies in that of the `n`-th Frobenius twist of `W₁`
exactly when `p ^ n` divides the inseparable degree of `φ`**: the subfield-criterion form of
`existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq_iff`. -/
theorem fieldRange_le_fieldRange_iterateRelativeFrobeniusIsogeny_iff {n : ℕ} :
    φ.fieldPullback.fieldRange ≤
        (iterateRelativeFrobeniusIsogeny p W₁ n).fieldPullback.fieldRange ↔
      p ^ n ∣ φ.inseparableDegree := by
  constructor
  · -- a factor `χ` through `F^n` has `deg_i φ = deg_i χ · p ^ n`
    intro h
    obtain ⟨χ, hχ, -⟩ := (existsUnique_comp_eq_iff_fieldRange_le _ φ).2 h
    exact ⟨χ.inseparableDegree, by
      rw [← hχ, inseparableDegree_comp,
        inseparableDegree_eq_degree_of_isPurelyInseparable (iterateRelativeFrobeniusIsogeny p W₁ n),
        degree_iterateRelativeFrobeniusIsogeny, mul_comm]⟩
  · intro h
    obtain ⟨r, hr⟩ : ∃ r : ℕ, φ.inseparableDegree = p ^ r :=
      φ.inseparableDegree_def ▸ finInsepDegree_eq_pow _ _ p
    rcases ‹ExpChar F p› with _ | ⟨hp⟩
    · -- in characteristic zero the inseparable degree is `1 = 1 ^ n`
      exact fieldRange_le_of_inseparableDegree_eq_pow 1 φ (by rw [hr, one_pow, one_pow])
    · -- `p ^ n ∣ p ^ r` forces `n ≤ r`, and the pulled-back twists decrease along the tower
      rw [hr] at h
      exact (fieldRange_le_of_inseparableDegree_eq_pow p φ hr).trans
        (fieldRange_iterateRelativeFrobeniusIsogeny_antitone p W₁
          ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h))

/-- **`φ` factors through the `n`-fold relative Frobenius exactly when `p ^ n` divides its
inseparable degree**, and then by a unique isogeny. -/
theorem existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq_iff {n : ℕ} :
    (∃! χ : Isogeny (W₁.map (iterateFrobenius F p n)) W₂,
        χ.comp (iterateRelativeFrobeniusIsogeny p W₁ n) = φ) ↔
      p ^ n ∣ φ.inseparableDegree := by
  rw [existsUnique_comp_eq_iff_fieldRange_le,
    fieldRange_le_fieldRange_iterateRelativeFrobeniusIsogeny_iff]

/-- **The factorisation theorem for isogenies** (Silverman II.2.12): when `p ^ r` is the
inseparable degree of `φ : W₁ → W₂`, it factors through the `r`-fold relative Frobenius
`F^r : W₁ → W₁⁽ᵖʳ⁾` as `φ = χ ∘ F^r` for a unique isogeny `χ : W₁⁽ᵖʳ⁾ → W₂`. The factor is
separable (`isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq`), of degree the separable
degree of `φ` (`degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq`). -/
theorem existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq {r : ℕ}
    (hr : φ.inseparableDegree = p ^ r) :
    ∃! χ : Isogeny (W₁.map (iterateFrobenius F p r)) W₂,
      χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ :=
  (existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq_iff p φ).2 (by rw [hr])

section Factor

variable {p φ} {r : ℕ} {χ : Isogeny (W₁.map (iterateFrobenius F p r)) W₂}

/-- **A factor through a Frobenius power has the separable degree of the composite**:
`deg_s χ = deg_s φ` when `φ = χ ∘ F^r`. -/
theorem separableDegree_eq_of_comp_iterateRelativeFrobeniusIsogeny_eq
    (hχ : χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ) :
    χ.separableDegree = φ.separableDegree := by
  rw [← hχ, separableDegree_comp,
    separableDegree_eq_one_of_isPurelyInseparable (iterateRelativeFrobeniusIsogeny p W₁ r), mul_one]

/-- **A factor of `φ` through `F^r` is separable when `p ^ r` is the inseparable degree of
`φ`.** -/
theorem isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq (hr : φ.inseparableDegree = p ^ r)
    (hχ : χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ) :
    Algebra.IsSeparable χ.fieldPullback.fieldRange
      (W₁.map (iterateFrobenius F p r)).FunctionField := by
  rw [← inseparableDegree_eq_one_iff_isSeparable]
  have h := congrArg inseparableDegree hχ
  rw [inseparableDegree_comp,
    inseparableDegree_eq_degree_of_isPurelyInseparable (iterateRelativeFrobeniusIsogeny p W₁ r),
    degree_iterateRelativeFrobeniusIsogeny, hr] at h
  exact Nat.eq_of_mul_eq_mul_right (expChar_pow_pos F p r) (h.trans (one_mul _).symm)

/-- **If `φ` has a separable factor through `F^r`, then `p ^ r` is its inseparable degree**: the
power `p ^ r` in a factorisation `φ = φ_sep ∘ F^r` with `φ_sep` separable is determined by `φ`, and
with it the exponent `r` when `p > 1`. -/
theorem inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq
    [Algebra.IsSeparable χ.fieldPullback.fieldRange (W₁.map (iterateFrobenius F p r)).FunctionField]
    (hχ : χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ) :
    φ.inseparableDegree = p ^ r := by
  rw [← hχ, inseparableDegree_comp, inseparableDegree_eq_one_of_isSeparable, one_mul,
    inseparableDegree_eq_degree_of_isPurelyInseparable (iterateRelativeFrobeniusIsogeny p W₁ r),
    degree_iterateRelativeFrobeniusIsogeny]

/-- **A factor of `φ` through `F^r` is separable exactly when `p ^ r` is the inseparable degree of
`φ`**: a factorisation `φ = φ_sep ∘ F^r` with `φ_sep` separable has `p ^ r` the inseparable degree
of `φ`, which determines `r` when `p > 1`, and the factor through that `F^r` is separable. -/
theorem isSeparable_iff_inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq
    (hχ : χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ) :
    Algebra.IsSeparable χ.fieldPullback.fieldRange
        (W₁.map (iterateFrobenius F p r)).FunctionField ↔
      φ.inseparableDegree = p ^ r :=
  ⟨fun _ ↦ inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ,
    fun hr ↦ isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq hr hχ⟩

/-- **The separable factor of `φ` through `F^r` has degree the separable degree of `φ`**
(Silverman II.2.12): `deg φ_sep = deg_s φ`. -/
theorem degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq
    [Algebra.IsSeparable χ.fieldPullback.fieldRange (W₁.map (iterateFrobenius F p r)).FunctionField]
    (hχ : χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ) :
    χ.degree = φ.separableDegree := by
  rw [← separableDegree_eq_degree_of_isSeparable,
    separableDegree_eq_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ]

end Factor

/-- **Every isogeny is a separable isogeny after a Frobenius power** (Silverman II.2.12):
`φ = φ_sep ∘ F^r` with `φ_sep : W₁⁽ᵖʳ⁾ → W₂` separable, where `p ^ r` is the inseparable degree of
`φ` (`inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq`) and `φ_sep` is unique
(`existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq`). -/
theorem exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq :
    ∃ r : ℕ, ∃ χ : Isogeny (W₁.map (iterateFrobenius F p r)) W₂,
      Algebra.IsSeparable χ.fieldPullback.fieldRange
          (W₁.map (iterateFrobenius F p r)).FunctionField ∧
        χ.comp (iterateRelativeFrobeniusIsogeny p W₁ r) = φ := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, φ.inseparableDegree = p ^ r :=
    φ.inseparableDegree_def ▸ finInsepDegree_eq_pow _ _ p
  obtain ⟨χ, hχ, -⟩ := existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq p φ hr
  exact ⟨r, χ, isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq hr hχ, hχ⟩

end TauCeti.Isogeny

end
