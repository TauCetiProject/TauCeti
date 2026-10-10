/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.FieldTheory.FunctionField.Frobenius
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.ChangeOfUniformizer

/-!
# Laurent expansions of derivatives, and residues of differentials

Let `P` be a rational place of `F / k` and let `t` have order one at `P`, with `F` separable over
`k(t)`. Differentiation with respect to `t` (`TauCeti.derivativeOfSeparating`) is then compatible
with Laurent expansion in `t`: the expansion of `dz/dt` is the formal derivative of the expansion
of `z`. Both sides are `k`-derivations of `F` into `k((T))` taking `t` to `1`, and a derivation of
`F` is determined by its value at a separating element
(`Derivation.apply_eq_derivativeOfSeparating_smul`).

This identifies the function-field derivative `ds/dt` with the series `s'(T)` used in the
change-of-uniformizer formula (`TauCeti.Place.residue_eq_residue_mul`), giving Stichtenoth's
transformation formula `res_{P,s}(z) = res_{P,t}(z · ds/dt)` for two uniformizers `s` and `t`
(Proposition 4.2.9). It holds in every characteristic.

The formula makes the residue of a Kähler differential well defined (Definition 4.2.10). Writing
`ω = z dt`, the residue `res_P(ω) := res_{P,t}(z)` does not depend on the separating uniformizer
`t`, since `z dt = (z · dt/ds) ds`. An exact differential `dy` has residue zero, because the formal
derivative of a Laurent series has no `T⁻¹` term.

Over a perfect field every prime element of a place is separating
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`), so the residue of a
differential at a rational place needs no choice of uniformizer at all:
`TauCeti.Place.kaehlerResidueOfPerfectField` computes it with any prime element.

The compatibility with expansions also gives the order of a derivative:
if `z` vanishes to order at least `m` at `P`, then `dz/dt ≡ m z / t` modulo functions vanishing to
order at least `m`, and iterating, `dⁱz/dtⁱ` is congruent to `m (m - 1) ⋯ (m - i + 1) z / tⁱ`.
This is the local input for computing orders of Wronskians at rational places.

## Main definitions

* `TauCeti.Place.kaehlerResidue`: the residue `res_P(ω)` of a Kähler differential `ω` at a
  rational place, computed with a separating uniformizer.
* `TauCeti.Place.kaehlerResidueOfPerfectField`: the residue `res_P(ω)` at a rational place of a
  function field over a perfect field, with no uniformizer in its signature.

## Main results

* `TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating`: the Laurent expansion of `dz/dt`
  in `t` is the derivative of the Laurent expansion of `z`.
* `TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`: **the transformation formula**
  `res_{P,s}(z) = res_{P,t}(z · ds/dt)`.
* `TauCeti.Place.residue_derivativeOfSeparating`: `res_{P,t}(dy/dt) = 0`.
* `TauCeti.Place.iterate_derivativeOfSeparating_sub_zsmul_mem_filtration`: if `z` vanishes to
  order at least `m`, then `dⁱz/dtⁱ ≡ m (m - 1) ⋯ (m - i + 1) z / tⁱ` modulo order `m - i + 1`.
* `TauCeti.Place.kaehlerResidue_eq_kaehlerResidue`: the residue of a differential is independent
  of the uniformizer used to compute it.
* `TauCeti.Place.kaehlerResidue_D`: exact differentials have residue zero.
* `TauCeti.Place.kaehlerResidueOfPerfectField_smul_D`: over a perfect field, `res_P(z dt)` is
  `res_{P,t}(z)` for every prime element `t`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9 and Definition 4.2.10.
-/

public section

open scoped LaurentSeries IntermediateField

open KaehlerDifferential

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

section Expansion

variable (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

/-- **The Laurent expansion of a derivative.** At a rational place `P` at which the separating
element `t` has order one, the Laurent expansion in `t` of `dz/dt` is the formal derivative of the
Laurent expansion of `z`. -/
theorem laurentSeriesExpansion_derivativeOfSeparating (z : F) :
    P.laurentSeriesExpansion hP ht (derivativeOfSeparating htr z) =
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht z) := by
  set e := P.laurentSeriesExpansion hP ht
  -- Make `k⸨X⸩` an `F`-module through the expansion, so that `z ↦ (e z)'` is a derivation.
  let _ : Module F k⸨X⸩ := Module.compHom _ e.toRingHom
  have hsmul (z : F) (f : k⸨X⸩) : z • f = e z * f := rfl
  -- The `k`-module structure on `k⸨X⸩` found by instance search is the coefficientwise one.
  have he (c : k) (z : F) : e (c • z) = c • e z := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, laurentSeries_algebraMap_mul_eq_smul]
  have _ : IsScalarTower k F k⸨X⸩ := ⟨fun c z f ↦ by
    -- `z • f` is `e z * f` by the definition of `Module.compHom`.
    change e (c • z) * f = c • (e z * f)
    rw [he, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]⟩
  let D : Derivation k F k⸨X⸩ :=
    { toFun z := LaurentSeries.derivative k (e z)
      map_add' := by simp
      map_smul' := by simp [he]
      map_one_eq_zero' := by
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, map_one, laurentSeriesDerivation_apply] using
          (laurentSeriesDerivation k).map_one_eq_zero
      leibniz' a b := by
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, hsmul, smul_eq_mul,
          laurentSeriesDerivation_apply] using
          (laurentSeriesDerivation k).leibniz (e a) (e b) }
  -- By the chain rule `D z = (dz/dt) • D t`, and `D t = (X)' = 1`. Unfolding `D` and the
  -- `Module.compHom` scalar action turns the chain rule into an identity of Laurent series.
  have h := D.apply_eq_derivativeOfSeparating_smul htr z
  change LaurentSeries.derivative k (e z) =
    e (derivativeOfSeparating htr z) * LaurentSeries.derivative k (e t) at h
  rw [h, laurentSeriesExpansion_uniformizer]
  simp

/-- **Stichtenoth's transformation formula** `res_{P,s}(z) = res_{P,t}(z · ds/dt)` for two
uniformizers `s` and `t` at a rational place, with `t` separating (Proposition 4.2.9). -/
theorem residue_eq_residue_mul_derivativeOfSeparating (hs : P.ord s = 1) (z : F) :
    P.residue hP hs z = P.residue hP ht (z * derivativeOfSeparating htr s) :=
  P.residue_eq_residue_mul hP ht hs (P.laurentSeriesExpansion_derivativeOfSeparating hP ht htr s) z

/-- The derivative `dy/dt` has residue zero with respect to `t`: the formal derivative of a
Laurent series has no `T⁻¹` term. -/
@[simp]
theorem residue_derivativeOfSeparating (y : F) :
    P.residue hP ht (derivativeOfSeparating htr y) = 0 := by
  rw [residue_apply, laurentSeriesExpansion_derivativeOfSeparating, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp

/-! ### Orders of derivatives -/

include hP ht in
/-- **The leading term of a derivative.** If `z` vanishes to order at least `m` at `P`, then
`dz/dt ≡ m z / t` modulo functions vanishing to order at least `m`. This holds in every
characteristic. -/
theorem derivativeOfSeparating_sub_zsmul_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) :
    derivativeOfSeparating htr z - m • (t⁻¹ * z) ∈ P.filtration m := by
  have hinv : (HahnSeries.single (1 : ℤ) (1 : k))⁻¹ = HahnSeries.single (-1) 1 :=
    inv_eq_of_mul_eq_one_right (by simp [HahnSeries.single_mul_single])
  rw [mem_filtration_iff, ← P.valuation_laurentSeriesExpansion hP ht, map_sub, map_zsmul,
    map_mul, map_inv₀, laurentSeriesExpansion_uniformizer,
    laurentSeriesExpansion_derivativeOfSeparating, hinv]
  apply LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le
  rw [valuation_laurentSeriesExpansion]
  exact (P.mem_filtration_iff).mp hz

include hP ht in
/-- Differentiation with respect to a prime element lowers the order at `P` by at most one. -/
theorem derivativeOfSeparating_mem_filtration {m : ℤ} {z : F} (hz : z ∈ P.filtration m) :
    derivativeOfSeparating htr z ∈ P.filtration (m - 1) := by
  have ht' : t⁻¹ ∈ P.filtration (-1) := by
    simpa [ht] using P.mem_filtration_ord t⁻¹
  have h : m • (t⁻¹ * z) ∈ P.filtration (m - 1) :=
    zsmul_mem (by simpa [neg_add_eq_sub] using P.mul_mem_filtration ht' hz) m
  simpa using add_mem (P.filtration_antitone (by omega)
    (P.derivativeOfSeparating_sub_zsmul_mem_filtration hP ht htr hz)) h

include hP ht in
/-- The `i`-th derivative with respect to a prime element lowers the order at `P` by at most
`i`. -/
theorem iterate_derivativeOfSeparating_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) (i : ℕ) :
    (⇑(derivativeOfSeparating htr))^[i] z ∈ P.filtration (m - i) := by
  induction i with
  | zero => simpa using hz
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    simpa [sub_sub] using P.derivativeOfSeparating_mem_filtration hP ht htr ih

include hP ht in
/-- **The leading term of an iterated derivative.** If `z` vanishes to order at least `m` at `P`,
then `dⁱz/dtⁱ ≡ m (m - 1) ⋯ (m - i + 1) z / tⁱ` modulo functions vanishing to order at least
`m - i + 1`. The coefficient is the descending Pochhammer symbol evaluated at `m`. -/
theorem iterate_derivativeOfSeparating_sub_zsmul_mem_filtration {m : ℤ} {z : F}
    (hz : z ∈ P.filtration m) (i : ℕ) :
    (⇑(derivativeOfSeparating htr))^[i] z - (descPochhammer ℤ i).eval m • (t⁻¹ ^ i * z) ∈
      P.filtration (m - i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hti : t⁻¹ ^ i ∈ P.filtration (-i) := by
      simpa [ht] using P.mem_filtration_ord (t⁻¹ ^ i)
    have hw : t⁻¹ ^ i * z ∈ P.filtration (m - i) := by
      convert P.mul_mem_filtration hti hz using 2
      ring
    have h1 := P.derivativeOfSeparating_mem_filtration hP ht htr ih
    have h2 := zsmul_mem (P.derivativeOfSeparating_sub_zsmul_mem_filtration hP ht htr hw)
      ((descPochhammer ℤ i).eval m)
    -- Differentiate the `i`-th congruence, and use the leading term of `d(t⁻ⁱ z)/dt`.
    have key : (⇑(derivativeOfSeparating htr))^[i + 1] z -
          (descPochhammer ℤ (i + 1)).eval m • (t⁻¹ ^ (i + 1) * z) =
        derivativeOfSeparating htr ((⇑(derivativeOfSeparating htr))^[i] z -
            (descPochhammer ℤ i).eval m • (t⁻¹ ^ i * z)) +
          (descPochhammer ℤ i).eval m • (derivativeOfSeparating htr (t⁻¹ ^ i * z) -
            (m - i : ℤ) • (t⁻¹ * (t⁻¹ ^ i * z))) := by
      rw [Function.iterate_succ_apply', descPochhammer_succ_eval, map_sub, map_zsmul]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [key]
    refine add_mem (P.filtration_antitone ?_ h1) (P.filtration_antitone ?_ h2) <;> omega

end Expansion

/-! ### Residues of Kähler differentials -/

section Kaehler

variable (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

/-- The **residue** `res_P(ω)` of a Kähler differential `ω` at a rational place `P`
(Stichtenoth, Definition 4.2.10): writing `ω = z dt` for a separating uniformizer `t` at `P`, it
is the residue `res_{P,t}(z)`. It does not depend on `t`
(`TauCeti.Place.kaehlerResidue_eq_kaehlerResidue`). -/
noncomputable def kaehlerResidue : Ω[F⁄k] →ₗ[k] k :=
  P.residue hP ht ∘ₗ ((kaehlerBasisOfSeparating htr).coord ()).restrictScalars k

/-- The residue of `ω` is the residue of its coordinate `ω / dt` in the basis `dt`. -/
theorem kaehlerResidue_apply (ω : Ω[F⁄k]) :
    P.kaehlerResidue hP ht htr ω = P.residue hP ht ((kaehlerBasisOfSeparating htr).coord () ω) :=
  (rfl)

/-- The residue of `z dt` is `res_{P,t}(z)`. -/
@[simp]
theorem kaehlerResidue_smul_D (z : F) : P.kaehlerResidue hP ht htr (z • D k F t) =
    P.residue hP ht z := by
  simp [kaehlerResidue_apply]

/-- **Exact differentials have residue zero**: `res_P(dy) = 0`. -/
@[simp]
theorem kaehlerResidue_D (y : F) : P.kaehlerResidue hP ht htr (D k F y) = 0 := by
  rw [← derivativeOfSeparating_smul_D htr y, kaehlerResidue_smul_D,
    residue_derivativeOfSeparating]

/-- **The residue of a differential is well defined** (Stichtenoth, Definition 4.2.10): it does not
depend on the separating uniformizer used to compute it. -/
theorem kaehlerResidue_eq_kaehlerResidue (hs : P.ord s = 1) (hstr : Transcendental k s)
    [Algebra.IsSeparable k⟮s⟯ F] :
    P.kaehlerResidue hP hs hstr = P.kaehlerResidue hP ht htr := by
  -- Both sides are `F`-semilinear in `ω`, so it suffices to compare them on `ω = z ds`, where
  -- `z ds = (z · ds/dt) dt`.
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z : F, z • D k F s = ω :=
    ⟨(kaehlerBasisOfSeparating hstr).coord () ω, by
      simpa using (kaehlerBasisOfSeparating hstr).sum_repr ω⟩
  rw [kaehlerResidue_smul_D, ← derivativeOfSeparating_smul_D htr s, smul_smul,
    kaehlerResidue_smul_D, P.residue_eq_residue_mul_derivativeOfSeparating hP ht htr hs]

end Kaehler

/-! ### Residues of Kähler differentials over a perfect field -/

section PerfectField

variable [PerfectField k] (hF : IsFunctionField k F)

/-- The **residue** `res_P(ω)` of a Kähler differential `ω` at a rational place `P` of a function
field over a perfect field (Stichtenoth, Definition 4.2.10). Over a perfect field every prime
element of `P` is separating
(`TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`), so this is
`TauCeti.Place.kaehlerResidue` computed with some prime element; it does not depend on the choice
(`TauCeti.Place.kaehlerResidueOfPerfectField_eq_kaehlerResidue`). -/
noncomputable def kaehlerResidueOfPerfectField : Ω[F⁄k] →ₗ[k] k :=
  have ht := (P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅).choose_spec.1
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  letI := hsep.2
  P.kaehlerResidue hP ht hsep.1

/-- Over a perfect field, the residue of a differential is `TauCeti.Place.kaehlerResidue` computed
with any separating uniformizer. -/
theorem kaehlerResidueOfPerfectField_eq_kaehlerResidue (htr : Transcendental k t)
    [Algebra.IsSeparable k⟮t⟯ F] :
    P.kaehlerResidueOfPerfectField hP hF = P.kaehlerResidue hP ht htr :=
  -- The left side unfolds to `kaehlerResidue` at the prime element chosen in the definition.
  have ht' := (P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅).choose_spec.1
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht'
  letI := hsep.2
  P.kaehlerResidue_eq_kaehlerResidue hP ht htr ht' hsep.1

/-- Over a perfect field, the residue of `z dt` is `res_{P,t}(z)` for every prime element `t`
of `P`. -/
theorem kaehlerResidueOfPerfectField_smul_D (z : F) :
    P.kaehlerResidueOfPerfectField hP hF (z • D k F t) = P.residue hP ht z := by
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep.2
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF hsep.1, kaehlerResidue_smul_D]

/-- **Exact differentials have residue zero**: `res_P(dy) = 0`. -/
@[simp]
theorem kaehlerResidueOfPerfectField_D (y : F) :
    P.kaehlerResidueOfPerfectField hP hF (D k F y) = 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  have hsep := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep.2
  rw [P.kaehlerResidueOfPerfectField_eq_kaehlerResidue hP ht hF hsep.1, kaehlerResidue_D]

end PerfectField

end TauCeti.Place
