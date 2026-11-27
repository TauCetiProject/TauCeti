/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Complex
public import TauCeti.Analysis.Complex.AppellHumbert.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Pair
import TauCeti.LinearAlgebra.Complex.Determinant
import Mathlib.Algebra.Ring.Int.Parity

/-!
# The Appell–Humbert data of a lattice in `ℂ`

Let `Λ ⊂ ℂ` be a lattice with covolume `A = ZLattice.covolume Λ`, the area of `ℂ / Λ`. Its
**Hermitian form** (`ZLattice.hermitianForm`) is `H (z, u) = z ū / A`, complex linear in `z` and
conjugate linear in `u`. Its imaginary part `E (u, v) = Im (u conj(v)) / A` is integer valued on
`Λ × Λ` (`ZLattice.exists_im_hermitianForm_eq_intCast`) and `±1` on every `ℤ`-basis of `Λ`
(`ZLattice.im_hermitianForm_basis_eq_one_or_eq_neg_one`), and the diagonal of `H` is
`H (u, u) = |u|² / A` (`ZLattice.hermitianForm_self`).

An **Appell–Humbert multiplier** for `H` (`ZLattice.IsAppellHumbertMultiplier`) is a map
`χ : Λ → U(1)` with `χ (l + m) = (-1) ^ E (l, m) χ (l) χ (m)`; with `H` it forms an Appell–Humbert
datum `ZLattice.appellHumbertData Λ χ hχ`, whose form is `B (l, z) = (π / A) conj(l) z` and whose
Riemann form is `E`. The theta functions of degree `m` and the twisted translations of degree `m`
are those of the datum `m • ZLattice.appellHumbertData Λ χ hχ`, that is,
`(m • D).thetaSpace` and `(m • D).twistedTranslate y`, and the automorphy factor of degree `m` is
`χ (l) ^ m exp (m π (z conj(l) + |l|² / 2) / A)` (`ZLattice.factor_nsmul_appellHumbertData`).

The sign `ε (l)`, equal to `1` for `l ∈ 2Λ` and to `-1` otherwise (`ZLattice.sigmaSign`), is an
Appell–Humbert multiplier (`ZLattice.isAppellHumbertMultiplier_sigmaSign`). It is the sign in the
quasi-periodicity `σ (z + l) = ε (l) exp (η (l) (z + l / 2)) σ (z)` of the Weierstrass sigma
function (`PeriodPair.weierstrassSigma_add_coe_of_div_two_mem` and
`PeriodPair.weierstrassSigma_add_coe_of_div_two_notMem`). The datum `ZLattice.sigmaSignData Λ` of
`(H, ε)` is intended for the reduced sigma function `σ (z) exp (-s₂ z² / 2)`, for a suitable
constant `s₂` of `Λ`, which is expected to be a theta function of degree one for it; this file does
not prove that.

The area of `Λ` is Mathlib's Lebesgue covolume `ZLattice.covolume Λ`, which for a `ℤ`-basis `a, b`
is `|Im (ā b)|` (`ZLattice.covolume_eq_abs_im`); no separate notion of area is introduced. The
statements are for any lattice `Λ` in `ℂ` (a discrete `ℤ`-submodule spanning `ℂ` over `ℝ`); for a
period pair `L` they apply to `L.lattice`.

## Conventions

Following `TauCeti.AppellHumbertData.ofHermitian`, the Hermitian form is complex linear in the
first variable and the Riemann form is `E = Im H`, so `E (u, v) = Im (u conj(v)) / A`. This is the
negative of the form `Im (ū v) / A` of the convention in which the Hermitian form is complex
linear in the second variable, under which positivity reads `E (u, i u) > 0`; here it reads
`E (i u, u) > 0`
(`ZLattice.riemannForm_appellHumbertData_I_mul_self_pos`). The form `B` of the datum, and hence
the theta functions, are the same in both conventions.

## Main declarations

* `ZLattice.hermitianForm`: the Hermitian form `H (z, u) = z ū / A` of a lattice in `ℂ`.
* `ZLattice.exists_im_hermitianForm_eq_intCast`: `Im H` is integral on `Λ`.
* `ZLattice.im_hermitianForm_basis_eq_one_or_eq_neg_one`: `Im H = ±1` on a basis.
* `ZLattice.IsAppellHumbertMultiplier`, `ZLattice.appellHumbertData`: Appell–Humbert multipliers
  for `H` and their data.
* `ZLattice.sigmaSign`, `ZLattice.isAppellHumbertMultiplier_sigmaSign`, `ZLattice.sigmaSignData`:
  the sign `ε` and the datum `(H, ε)`, whose semicharacter, form, Riemann form and factor are
  `simp` lemmas (`ZLattice.semichar_sigmaSignData`, `ZLattice.form_sigmaSignData_apply`,
  `ZLattice.riemannForm_sigmaSignData_apply`, `ZLattice.factor_sigmaSignData`).

## Provenance

`ZLattice.hermitianForm`, `ZLattice.sigmaSign`, `ZLattice.isAppellHumbertMultiplier_sigmaSign`,
`ZLattice.riemannForm_appellHumbertData_apply`,
and `ZLattice.im_hermitianForm_basis_eq_one_or_eq_neg_one` are adapted from
`PeriodPair.hermitianForm`, `New.sigmaSign`, `New.isAppellHumbert_hermitianForm`,
`New.riemannForm_hermitianForm` and `New.exists_riemannForm_periods_eq_sign` (file
`src/Lib/CM/Sigma/Basic.lean`) in grh-lean (https://github.com/lsernau/grh-lean, commit `72fead1`,
Apache 2.0, Copyright 2026 Anthropic, PBC). There the objects are attached to a period pair and
the area is `|Im (conj(ω₁) ω₂)|`; here they are attached to the lattice, with the area its
covolume. The isogenies of that file are in `TauCeti.Algebra.Module.ZLattice.Complex`.

## References

* A. Weil, *Elliptic Functions according to Eisenstein and Kronecker*, Springer, 1976.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer,
  1994, I.5.
* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 2.
-/

public section

open Complex Module
open scoped Real ComplexConjugate Pointwise

namespace ZLattice

variable (Λ : Submodule ℤ ℂ)

/-! ### The Hermitian form of a lattice -/

/-- The **Hermitian form** `H (z, u) = z ū / A` of a lattice `Λ` in `ℂ` of covolume `A`, complex
linear in `z` and conjugate linear in `u`. In the Appell–Humbert datum of `Λ` it gives the form
`B (l, z) = π H (z, l) = (π / A) conj(l) z`. -/
noncomputable def hermitianForm : ℂ →L[ℂ] ℂ →L⋆[ℂ] ℂ :=
  ((covolume Λ)⁻¹ : ℂ) • innerSLFlip ℂ

/-- The defining formula `H (z, u) = z ū / A`. -/
@[simp]
theorem hermitianForm_apply (z u : ℂ) : hermitianForm Λ z u = z * conj u / covolume Λ := by
  simp [hermitianForm, innerSLFlip_apply_apply, div_eq_inv_mul]

/-- The Hermitian form of a lattice is Hermitian: `conj (H (z, u)) = H (u, z)`. -/
theorem conj_hermitianForm (z u : ℂ) : conj (hermitianForm Λ z u) = hermitianForm Λ u z := by
  simp [hermitianForm_apply, mul_comm]

/-- The imaginary part `E (u, v) = Im (u conj(v)) / A` of the Hermitian form. -/
theorem im_hermitianForm (u v : ℂ) :
    (hermitianForm Λ u v).im = (u * conj v).im / covolume Λ := by
  rw [hermitianForm_apply, div_ofReal_im]

/-- The diagonal of the Hermitian form of a lattice is `H (u, u) = |u|² / A`. -/
theorem hermitianForm_self (u : ℂ) : hermitianForm Λ u u = (‖u‖ ^ 2 / covolume Λ : ℝ) := by
  rw [hermitianForm_apply, mul_conj', ofReal_div]
  push_cast
  ring

variable [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- `Im H (b 0, b 1) = ±1` for every `ℤ`-basis `b` of the lattice. -/
theorem im_hermitianForm_basis_eq_one_or_eq_neg_one (b : Basis (Fin 2) ℤ Λ) :
    (hermitianForm Λ (b 0) (b 1)).im = 1 ∨ (hermitianForm Λ (b 0) (b 1)).im = -1 := by
  -- The numerator `Im (b 0 conj (b 1))` and the covolume `|Im (conj (b 0) b 1)|` agree up to sign.
  have hA := covolume_eq_abs_im Λ b
  have hpos := covolume_pos Λ
  rw [im_hermitianForm, TauCeti.im_mul_conj_eq_neg_im_conj_mul, hA]
  rw [hA] at hpos
  rcases abs_cases (conj (b 0 : ℂ) * b 1).im with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hpos ⊢
  · exact Or.inr (by rw [neg_div, div_self hpos.ne'])
  · exact Or.inl (div_self hpos.ne')

/-- In the coordinates of a period pair, `E (a ω₁ + b ω₂, c ω₁ + d ω₂) = ±(a d - b c)`. -/
private theorem im_hermitianForm_periods (L : PeriodPair) (a b c d : ℤ) :
    (hermitianForm L.lattice (a * L.ω₁ + b * L.ω₂) (c * L.ω₁ + d * L.ω₂)).im = (a * d - b * c : ℤ) ∨
      (hermitianForm L.lattice (a * L.ω₁ + b * L.ω₂) (c * L.ω₁ + d * L.ω₂)).im =
        (-(a * d - b * c) : ℤ) := by
  rw [im_hermitianForm, TauCeti.im_mul_conj_eq_neg_im_conj_mul,
    TauCeti.im_conj_intCast_mul_add_mul_intCast_mul_add, ← mul_neg,
    ← TauCeti.im_mul_conj_eq_neg_im_conj_mul, mul_div_assoc]
  rcases im_hermitianForm_basis_eq_one_or_eq_neg_one L.lattice L.latticeBasis with hk | hk <;>
    rw [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one, im_hermitianForm] at hk <;>
    rw [hk]
  · exact Or.inl (mul_one _)
  · exact Or.inr (by push_cast; ring)

/-- **The imaginary part of `H` is integral on `Λ`.** -/
theorem exists_im_hermitianForm_eq_intCast (l m : Λ) :
    ∃ n : ℤ, (hermitianForm Λ l m).im = n := by
  obtain ⟨L, rfl⟩ := Submodule.exists_periodPair_lattice_eq_of_isZLattice Λ
  obtain ⟨a, b, hl⟩ := PeriodPair.mem_lattice.mp l.property
  obtain ⟨c, d, hm⟩ := PeriodPair.mem_lattice.mp m.property
  rw [← hl, ← hm]
  rcases im_hermitianForm_periods L a b c d with h | h <;> exact ⟨_, h⟩

/-! ### Appell–Humbert multipliers -/

/-- An **Appell–Humbert multiplier** for the Hermitian form `H` of a lattice `Λ` in `ℂ`: a map
`χ : Λ → U(1)` with `χ (l + m) = (-1) ^ E (l, m) χ (l) χ (m)`, where `E = Im H` is integer valued
on `Λ`. These are the semicharacters `χ` for which `(H, χ)` is an Appell–Humbert datum
(`ZLattice.appellHumbertData`). -/
abbrev IsAppellHumbertMultiplier (χ : Λ → Circle) : Prop :=
  ∀ (l m : Λ) (n : ℤ), (hermitianForm Λ l m).im = n → (χ (l + m) : ℂ) = (-1) ^ n * χ l * χ m

/-- The **Appell–Humbert datum** `(H, χ)` of a lattice `Λ` in `ℂ` and an Appell–Humbert
multiplier `χ` for its Hermitian form. Its form is `B (l, z) = (π / A) conj(l) z`
(`ZLattice.form_appellHumbertData_apply`) and its Riemann form is `E (u, v) = Im (u conj(v)) / A`
(`ZLattice.riemannForm_appellHumbertData_apply`). The theta functions of degree `m` for `χ` are
`(m • appellHumbertData Λ χ hχ).thetaSpace`. -/
noncomputable def appellHumbertData (χ : Λ → Circle) (hχ : IsAppellHumbertMultiplier Λ χ) :
    TauCeti.AppellHumbertData Λ :=
  .ofHermitian (hermitianForm Λ) (conj_hermitianForm Λ) (exists_im_hermitianForm_eq_intCast Λ)
    χ hχ

variable {Λ} {χ : Λ → Circle} (hχ : IsAppellHumbertMultiplier Λ χ)

/-- The form of the Appell–Humbert datum of a lattice is `B (l, z) = (π / A) conj(l) z`. -/
@[simp]
theorem form_appellHumbertData_apply (l z : ℂ) :
    (appellHumbertData Λ χ hχ).form l z = π / covolume Λ * (conj l * z) := by
  rw [appellHumbertData, TauCeti.AppellHumbertData.form_ofHermitian_apply, hermitianForm_apply]
  ring

/-- The semicharacter of the Appell–Humbert datum of a lattice is the multiplier `χ`. -/
@[simp]
theorem semichar_appellHumbertData : (appellHumbertData Λ χ hχ).semichar = χ := by
  rw [appellHumbertData, TauCeti.AppellHumbertData.semichar_ofHermitian]

/-- The Riemann form of the Appell–Humbert datum of a lattice is `E (u, v) = Im (u conj(v)) / A`. -/
@[simp]
theorem riemannForm_appellHumbertData_apply (u v : ℂ) :
    (appellHumbertData Λ χ hχ).riemannForm u v = (u * conj v).im / covolume Λ := by
  rw [appellHumbertData, TauCeti.AppellHumbertData.riemannForm_ofHermitian_apply,
    im_hermitianForm]

/-- **The Riemann form is positive**: `E (i u, u) = |u|² / A > 0` for `u ≠ 0`. -/
theorem riemannForm_appellHumbertData_I_mul_self_pos {u : ℂ} (hu : u ≠ 0) :
    0 < (appellHumbertData Λ χ hχ).riemannForm (I * u) u := by
  simp only [riemannForm_appellHumbertData_apply, mul_assoc, mul_conj', ← ofReal_pow, I_mul_im,
    ofReal_re]
  exact div_pos (by positivity) (covolume_pos Λ)

/-- The Riemann form of the Appell–Humbert datum of a lattice is `±1` on every `ℤ`-basis. -/
theorem riemannForm_appellHumbertData_basis_eq_one_or_eq_neg_one (b : Basis (Fin 2) ℤ Λ) :
    (appellHumbertData Λ χ hχ).riemannForm (b 0) (b 1) = 1 ∨
      (appellHumbertData Λ χ hχ).riemannForm (b 0) (b 1) = -1 := by
  simpa only [appellHumbertData, TauCeti.AppellHumbertData.riemannForm_ofHermitian_apply] using
    im_hermitianForm_basis_eq_one_or_eq_neg_one Λ b

/-- The factor of automorphy of the Appell–Humbert datum of a lattice is
`e_l (z) = χ (l) exp (π (z conj(l) + |l|² / 2) / A)`. -/
@[simp]
theorem factor_appellHumbertData (l : Λ) (z : ℂ) :
    (appellHumbertData Λ χ hχ).factor l z =
      χ l * exp (π * (z * conj (l : ℂ) + ‖(l : ℂ)‖ ^ 2 / 2) / covolume Λ) := by
  rw [appellHumbertData, TauCeti.AppellHumbertData.factor_ofHermitian, hermitianForm_apply,
    hermitianForm_apply, mul_conj']
  congr 2
  ring

/-- **The factor of automorphy of degree `m`**: for the datum `m • (H, χ)`,
`e_l (z) = χ (l) ^ m exp (m π (z conj(l) + |l|² / 2) / A)`. -/
theorem factor_nsmul_appellHumbertData (m : ℕ) (l : Λ) (z : ℂ) :
    (m • appellHumbertData Λ χ hχ).factor l z =
      χ l ^ m * exp (m * π * (z * conj (l : ℂ) + ‖(l : ℂ)‖ ^ 2 / 2) / covolume Λ) := by
  rw [TauCeti.AppellHumbertData.factor_nsmul, factor_appellHumbertData, mul_pow,
    ← exp_natCast_mul]
  congr 2
  ring

/-- **The theta functions of degree `m`** for an Appell–Humbert multiplier `χ`: the entire `f` with
`f (z + l) = χ (l) ^ m exp (m π (z conj(l) + |l|² / 2) / A) f (z)` for `l ∈ Λ`. -/
theorem mem_thetaSpace_nsmul_appellHumbertData_iff (m : ℕ) {f : ℂ → ℂ} :
    f ∈ (m • appellHumbertData Λ χ hχ).thetaSpace ↔ Differentiable ℂ f ∧ ∀ (l : Λ) (z : ℂ),
      f (z + l) =
        χ l ^ m * exp (m * π * (z * conj (l : ℂ) + ‖(l : ℂ)‖ ^ 2 / 2) / covolume Λ) * f z := by
  simp only [TauCeti.AppellHumbertData.mem_thetaSpace_iff, factor_nsmul_appellHumbertData]

/-! ### The sign `ε` -/

variable (Λ) in
open Classical in
/-- The sign `ε (l)` of a lattice `Λ` in `ℂ`: `1` if `l ∈ 2Λ`, that is `l / 2 ∈ Λ`, and `-1`
otherwise. It is an Appell–Humbert multiplier (`ZLattice.isAppellHumbertMultiplier_sigmaSign`),
and it is the sign in the transformation law of the (reduced) sigma function of `Λ`. -/
noncomputable def sigmaSign (l : Λ) : Circle :=
  if (l : ℂ) / 2 ∈ Λ then 1 else -1

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
/-- `ε (l) = 1` for `l ∈ 2Λ`. -/
theorem sigmaSign_of_div_two_mem {l : Λ} (hl : (l : ℂ) / 2 ∈ Λ) : sigmaSign Λ l = 1 := by
  classical
  simp [sigmaSign, hl]

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
/-- `ε (l) = -1` for `l ∉ 2Λ`. -/
theorem sigmaSign_of_div_two_notMem {l : Λ} (hl : (l : ℂ) / 2 ∉ Λ) : sigmaSign Λ l = -1 := by
  classical
  simp [sigmaSign, hl]

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
/-- `ε` is even: `ε (-l) = ε (l)`. -/
@[simp]
theorem sigmaSign_neg (l : Λ) : sigmaSign Λ (-l) = sigmaSign Λ l := by
  classical
  simp [sigmaSign, neg_div]

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
/-- The value of `ε` as a complex number. -/
theorem coe_sigmaSign (l : Λ) :
    (sigmaSign Λ l : ℂ) = (open Classical in if (l : ℂ) / 2 ∈ Λ then 1 else -1) := by
  classical
  unfold sigmaSign
  split_ifs <;> simp

variable (Λ) in
/-- **The sign `ε` is an Appell–Humbert multiplier**: `ε (l + m) = (-1) ^ E (l, m) ε (l) ε (m)`
for `l, m ∈ Λ`. -/
theorem isAppellHumbertMultiplier_sigmaSign : IsAppellHumbertMultiplier Λ (sigmaSign Λ) := by
  -- In coordinates `l = a ω₁ + b ω₂`, `m = c ω₁ + d ω₂` for a basis, `E (l, m) = ±(a d - b c)` and
  -- `ε` depends only on the parities of the coordinates, so the law is a parity check.
  intro l m n hn
  obtain ⟨L, rfl⟩ := Submodule.exists_periodPair_lattice_eq_of_isZLattice Λ
  obtain ⟨a, b, hl⟩ := PeriodPair.mem_lattice.mp l.property
  obtain ⟨c, d, hm⟩ := PeriodPair.mem_lattice.mp m.property
  have hlm : ((l + m : L.lattice) : ℂ) = (a + c : ℤ) * L.ω₁ + (b + d : ℤ) * L.ω₂ := by
    rw [Submodule.coe_add, ← hl, ← hm]
    push_cast
    ring
  -- `n = ±(a d - b c)`, so `n` has the parity of `a d - b c`.
  have hn' : Even n ↔ Even (a * d - b * c) := by
    rw [← hl, ← hm] at hn
    rcases im_hermitianForm_periods L a b c d with h | h <;>
      obtain rfl := Int.cast_injective (α := ℝ) (hn.symm.trans h)
    · rfl
    · exact even_neg
  simp only [coe_sigmaSign, hlm, ← hl, ← hm, PeriodPair.div_two_mem_lattice_iff,
    neg_one_zpow_eq_ite]
  grind [Int.even_add, Int.even_sub]

variable (Λ) in
/-- The **Appell–Humbert datum `(H, ε)`** of a lattice `Λ` in `ℂ`. Its intended use is the reduced
sigma function `σ (z) exp (-s₂ z² / 2)` of `Λ`, expected to be a theta function of degree one for
this datum; that is not proved here. -/
noncomputable def sigmaSignData : TauCeti.AppellHumbertData Λ :=
  appellHumbertData Λ (sigmaSign Λ) (isAppellHumbertMultiplier_sigmaSign Λ)

variable (Λ) in
/-- The datum `(H, ε)` is the Appell–Humbert datum of `Λ` for the multiplier `ε`. -/
theorem sigmaSignData_def : sigmaSignData Λ =
    appellHumbertData Λ (sigmaSign Λ) (isAppellHumbertMultiplier_sigmaSign Λ) := by
  rw [sigmaSignData]

variable (Λ) in
/-- The semicharacter of the datum `(H, ε)` is the sign `ε`. -/
@[simp]
theorem semichar_sigmaSignData : (sigmaSignData Λ).semichar = sigmaSign Λ := by
  rw [sigmaSignData_def, semichar_appellHumbertData]

variable (Λ) in
/-- The form of the datum `(H, ε)` is `B (l, z) = (π / A) conj(l) z`. -/
@[simp]
theorem form_sigmaSignData_apply (l z : ℂ) :
    (sigmaSignData Λ).form l z = π / covolume Λ * (conj l * z) := by
  rw [sigmaSignData_def, form_appellHumbertData_apply]

variable (Λ) in
/-- The Riemann form of the datum `(H, ε)` is `E (u, v) = Im (u conj(v)) / A`. -/
@[simp]
theorem riemannForm_sigmaSignData_apply (u v : ℂ) :
    (sigmaSignData Λ).riemannForm u v = (u * conj v).im / covolume Λ := by
  rw [sigmaSignData_def, riemannForm_appellHumbertData_apply]

variable (Λ) in
/-- The factor of automorphy of the datum `(H, ε)` is
`e_l (z) = ε (l) exp (π (z conj(l) + |l|² / 2) / A)`. -/
@[simp]
theorem factor_sigmaSignData (l : Λ) (z : ℂ) :
    (sigmaSignData Λ).factor l z =
      sigmaSign Λ l * exp (π * (z * conj (l : ℂ) + ‖(l : ℂ)‖ ^ 2 / 2) / covolume Λ) := by
  rw [sigmaSignData_def, factor_appellHumbertData]

end ZLattice
