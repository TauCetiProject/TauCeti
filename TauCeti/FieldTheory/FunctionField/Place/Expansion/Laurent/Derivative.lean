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
(`Derivation.apply_eq_derivativeOfSeparating_smul`). The argument applies to any `k`-algebra map
from `F` to Laurent series sending `t` to the variable
(`TauCeti.map_derivativeOfSeparating_eq_derivative`).

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

The expansion of a derivative, the transformation formula and the residue of a differential carry
over to a place `P` of arbitrary degree whose residue field `F_P` is separable over `k`, with
Laurent expansions and residues taking values in `F_P`
(`TauCeti.Place.laurentSeriesExpansionResidueField`, `TauCeti.Place.residueResidueField`).
The residue `res_P(ω) ∈ F_P` of a Kähler differential is again well defined, and so is its trace
`Tr_{F_P/k} res_P(ω) ∈ k`, the `k`-valued residue at a place of higher degree (Stichtenoth,
Remark 4.3.7). At a rational place the latter is the residue `TauCeti.Place.kaehlerResidue`.

## Main definitions

* `TauCeti.Place.kaehlerResidue`: the residue `res_P(ω)` of a Kähler differential `ω` at a
  rational place, computed with a separating uniformizer.
* `TauCeti.Place.kaehlerResidueOfPerfectField`: the residue `res_P(ω)` at a rational place of a
  function field over a perfect field, with no uniformizer in its signature.
* `TauCeti.Place.kaehlerResidueResidueField`: the residue `res_P(ω) ∈ F_P` at a place with
  separable residue field, computed with a separating uniformizer.
* `TauCeti.Place.kaehlerTraceResidue`: its trace `Tr_{F_P/k} res_P(ω) ∈ k`.

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
* `TauCeti.Place.laurentSeriesExpansionResidueField_derivativeOfSeparating` and
  `TauCeti.Place.residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating`: the
  expansion of a derivative and the transformation formula at a place with separable residue
  field.
* `TauCeti.Place.kaehlerResidueResidueField_eq_kaehlerResidueResidueField` and
  `TauCeti.Place.kaehlerTraceResidue_eq_kaehlerTraceResidue`: there too, the residue of a
  differential is independent of the uniformizer used to compute it.
* `TauCeti.Place.kaehlerTraceResidue_eq_kaehlerResidue`: at a rational place the `k`-valued
  residue is `TauCeti.Place.kaehlerResidue`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, Proposition 4.2.9 and Definition 4.2.10, and Remark 4.3.7.
-/

public section

open scoped LaurentSeries IntermediateField

open KaehlerDifferential

namespace TauCeti

section Derivation

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {t : F}
  (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

/-- **Differentiation commutes with expansion.** If a `k`-algebra map `e` from `F` to Laurent
series over a commutative ring `K` sends the separating element `t` to the variable `T`, then it
carries `dz/dt` to the formal derivative of `e z`. -/
theorem map_derivativeOfSeparating_eq_derivative {K : Type*} [CommRing K] [Algebra k K]
    (e : F →ₐ[k] K⸨X⸩) (he : e t = HahnSeries.single 1 1) (z : F) :
    e (derivativeOfSeparating htr z) = LaurentSeries.derivative K (e z) := by
  -- Both `z ↦ e (dz/dt)` and `z ↦ (e z)'` are `k`-derivations of `F` taking `t` to `1`, and a
  -- derivation of `F` is determined by its value at a separating element. Make `K⸨X⸩` an
  -- `F`-module through `e`, so that `z ↦ (e z)'` is a derivation.
  let _ : Module F K⸨X⸩ := Module.compHom _ e.toRingHom
  have hsmul (z : F) (f : K⸨X⸩) : z • f = e z * f := rfl
  -- The `k`-module structure on `K⸨X⸩` found by instance search is the coefficientwise one.
  have hk (c : k) (f : K⸨X⸩) : algebraMap k K⸨X⸩ c * f = c • f := by
    ext n
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.smul_def]
  have he' (c : k) (z : F) : e (c • z) = c • e z := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, hk]
  have _ : IsScalarTower k F K⸨X⸩ := ⟨fun c z f ↦ by
    -- `z • f` is `e z * f` by the definition of `Module.compHom`.
    change e (c • z) * f = c • (e z * f)
    rw [he', ← hk, ← hk, mul_assoc]⟩
  let D : Derivation k F K⸨X⸩ :=
    { toFun z := LaurentSeries.derivative K (e z)
      map_add' := by simp
      map_smul' c z := by
        rw [RingHom.id_apply, he', ← algebraMap_smul K c (e z), map_smul, algebraMap_smul]
      map_one_eq_zero' := by
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, map_one, laurentSeriesDerivation_apply] using
          (laurentSeriesDerivation K).map_one_eq_zero
      leibniz' a b := by
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, hsmul, smul_eq_mul,
          laurentSeriesDerivation_apply] using
          (laurentSeriesDerivation K).leibniz (e a) (e b) }
  -- By the chain rule `D z = (dz/dt) • D t`, and `D t = (X)' = 1`. Unfolding `D` and the
  -- `Module.compHom` scalar action turns the chain rule into an identity of Laurent series.
  have h := D.apply_eq_derivativeOfSeparating_smul htr z
  change LaurentSeries.derivative K (e z) =
    e (derivativeOfSeparating htr z) * LaurentSeries.derivative K (e t) at h
  rw [h, he]
  simp

end Derivation

end TauCeti

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
      LaurentSeries.derivative k (P.laurentSeriesExpansion hP ht z) :=
  map_derivativeOfSeparating_eq_derivative htr _ (P.laurentSeriesExpansion_uniformizer hP ht) z

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
/-- Differentiation with respect to a separating uniformizer preserves the valuation ring
at a rational place, in every characteristic. -/
theorem derivativeOfSeparating_mem_integers {z : F} (hz : z ∈ P.integers) :
    derivativeOfSeparating htr z ∈ P.integers := by
  have hz' : z ∈ P.filtration 0 := by
    simpa [P.mem_filtration_iff, P.mem_integers_iff] using hz
  have h := P.derivativeOfSeparating_sub_zsmul_mem_filtration hP ht htr hz'
  simpa [P.mem_filtration_iff, P.mem_integers_iff] using h

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

/-! ### Places with separable residue field -/

section ResidueField

variable [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable k⟮t⟯ F]

/-- **The Laurent expansion of a derivative at a place with separable residue field.** If the
separating element `t` has order one at `P`, the Laurent expansion in `t` of `dz/dt`, with
coefficients in `F_P`, is the formal derivative of that of `z`. -/
theorem laurentSeriesExpansionResidueField_derivativeOfSeparating (z : F) :
    P.laurentSeriesExpansionResidueField ht (derivativeOfSeparating htr z) =
      LaurentSeries.derivative P.ResidueField (P.laurentSeriesExpansionResidueField ht z) :=
  map_derivativeOfSeparating_eq_derivative htr _
    (P.laurentSeriesExpansionResidueField_uniformizer ht) z

/-- **Stichtenoth's transformation formula** `res_{P,s}(z) = res_{P,t}(z · ds/dt)` at a place
with separable residue field, for two uniformizers `s` and `t` with `t` separating, the residues
taking values in `F_P` (Proposition 4.2.9). -/
theorem residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating
    (hs : P.ord s = 1) (z : F) :
    P.residueResidueField hs z = P.residueResidueField ht (z * derivativeOfSeparating htr s) :=
  P.residueResidueField_eq_residueResidueField_mul ht hs
    (P.laurentSeriesExpansionResidueField_derivativeOfSeparating ht htr s) z

/-- **The transformation formula for `k`-valued residues** at a place with separable residue
field: `Tr_{F_P/k} res_{P,s}(z) = Tr_{F_P/k} res_{P,t}(z · ds/dt)`. -/
theorem traceResidue_eq_traceResidue_mul_derivativeOfSeparating (hs : P.ord s = 1) (z : F) :
    P.traceResidue hs z = P.traceResidue ht (z * derivativeOfSeparating htr s) :=
  P.traceResidue_eq_traceResidue_mul ht hs
    (P.laurentSeriesExpansionResidueField_derivativeOfSeparating ht htr s) z

/-- The derivative `dy/dt` has residue zero with respect to `t` at a place with separable residue
field: the formal derivative of a Laurent series has no `T⁻¹` term. -/
@[simp]
theorem residueResidueField_derivativeOfSeparating (y : F) :
    P.residueResidueField ht (derivativeOfSeparating htr y) = 0 := by
  rw [residueResidueField_apply, laurentSeriesExpansionResidueField_derivativeOfSeparating,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp

/-- The derivative `dy/dt` has `k`-valued residue zero with respect to `t`. -/
@[simp]
theorem traceResidue_derivativeOfSeparating (y : F) :
    P.traceResidue ht (derivativeOfSeparating htr y) = 0 := by
  rw [traceResidue_apply, residueResidueField_derivativeOfSeparating, map_zero]

/-- The **residue** `res_P(ω) ∈ F_P` of a Kähler differential `ω` at a place with separable
residue field (Stichtenoth, Definition 4.2.10 and Remark 4.3.7): writing `ω = z dt` for a
separating uniformizer `t` at `P`, it is the residue `res_{P,t}(z)`. It does not depend on `t`
(`TauCeti.Place.kaehlerResidueResidueField_eq_kaehlerResidueResidueField`). -/
noncomputable def kaehlerResidueResidueField : Ω[F⁄k] →ₗ[k] P.ResidueField :=
  P.residueResidueField ht ∘ₗ ((kaehlerBasisOfSeparating htr).coord ()).restrictScalars k

/-- The residue of `ω` is the residue of its coordinate `ω / dt` in the basis `dt`. -/
theorem kaehlerResidueResidueField_apply (ω : Ω[F⁄k]) :
    P.kaehlerResidueResidueField ht htr ω =
      P.residueResidueField ht ((kaehlerBasisOfSeparating htr).coord () ω) :=
  (rfl)

/-- The residue of `z dt` is `res_{P,t}(z)`. -/
@[simp]
theorem kaehlerResidueResidueField_smul_D (z : F) :
    P.kaehlerResidueResidueField ht htr (z • D k F t) = P.residueResidueField ht z := by
  simp [kaehlerResidueResidueField_apply]

/-- **Exact differentials have residue zero**: `res_P(dy) = 0`. -/
@[simp]
theorem kaehlerResidueResidueField_D (y : F) :
    P.kaehlerResidueResidueField ht htr (D k F y) = 0 := by
  rw [← derivativeOfSeparating_smul_D htr y, kaehlerResidueResidueField_smul_D,
    residueResidueField_derivativeOfSeparating]

/-- **The residue of a differential at a place with separable residue field is well defined**
(Stichtenoth, Definition 4.2.10): it does not depend on the separating uniformizer used to
compute it. -/
theorem kaehlerResidueResidueField_eq_kaehlerResidueResidueField (hs : P.ord s = 1)
    (hstr : Transcendental k s) [Algebra.IsSeparable k⟮s⟯ F] :
    P.kaehlerResidueResidueField hs hstr = P.kaehlerResidueResidueField ht htr := by
  -- Both sides are `F`-semilinear in `ω`, so it suffices to compare them on `ω = z ds`, where
  -- `z ds = (z · ds/dt) dt`.
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z : F, z • D k F s = ω :=
    ⟨(kaehlerBasisOfSeparating hstr).coord () ω, by
      simpa using (kaehlerBasisOfSeparating hstr).sum_repr ω⟩
  rw [kaehlerResidueResidueField_smul_D, ← derivativeOfSeparating_smul_D htr s, smul_smul,
    kaehlerResidueResidueField_smul_D,
    P.residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating ht htr hs]

/-- The `k`-valued **residue** `Tr_{F_P/k} res_P(ω)` of a Kähler differential `ω` at a place with
separable residue field (Stichtenoth, Remark 4.3.7). It does not depend on the separating
uniformizer `t` (`TauCeti.Place.kaehlerTraceResidue_eq_kaehlerTraceResidue`), and at a rational
place it is `TauCeti.Place.kaehlerResidue` (`TauCeti.Place.kaehlerTraceResidue_eq_kaehlerResidue`).
-/
noncomputable def kaehlerTraceResidue : Ω[F⁄k] →ₗ[k] k :=
  (Algebra.trace k P.ResidueField).comp (P.kaehlerResidueResidueField ht htr)

/-- The `k`-valued residue is the trace of the residue. -/
theorem kaehlerTraceResidue_apply (ω : Ω[F⁄k]) :
    P.kaehlerTraceResidue ht htr ω =
      Algebra.trace k P.ResidueField (P.kaehlerResidueResidueField ht htr ω) :=
  (rfl)

/-- The `k`-valued residue of `z dt` is `Tr_{F_P/k} res_{P,t}(z)`. -/
@[simp]
theorem kaehlerTraceResidue_smul_D (z : F) :
    P.kaehlerTraceResidue ht htr (z • D k F t) = P.traceResidue ht z := by
  rw [kaehlerTraceResidue_apply, kaehlerResidueResidueField_smul_D, traceResidue_apply]

/-- **Exact differentials have `k`-valued residue zero.** -/
@[simp]
theorem kaehlerTraceResidue_D (y : F) : P.kaehlerTraceResidue ht htr (D k F y) = 0 := by
  rw [kaehlerTraceResidue_apply, kaehlerResidueResidueField_D, map_zero]

/-- **The `k`-valued residue of a differential is well defined**: it does not depend on the
separating uniformizer used to compute it. -/
theorem kaehlerTraceResidue_eq_kaehlerTraceResidue (hs : P.ord s = 1)
    (hstr : Transcendental k s) [Algebra.IsSeparable k⟮s⟯ F] :
    P.kaehlerTraceResidue hs hstr = P.kaehlerTraceResidue ht htr := by
  rw [kaehlerTraceResidue, kaehlerTraceResidue,
    P.kaehlerResidueResidueField_eq_kaehlerResidueResidueField ht htr hs hstr]

/-- At a rational place the `k`-valued residue of a differential is its residue
`TauCeti.Place.kaehlerResidue`. -/
theorem kaehlerTraceResidue_eq_kaehlerResidue :
    P.kaehlerTraceResidue ht htr = P.kaehlerResidue hP ht htr :=
  LinearMap.ext fun ω ↦ by
    rw [kaehlerTraceResidue_apply, kaehlerResidueResidueField_apply, ← traceResidue_apply,
      traceResidue_eq_residue _ _ hP, kaehlerResidue_apply]

end ResidueField

end TauCeti.Place
