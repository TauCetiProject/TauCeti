/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
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

## Main definitions

* `TauCeti.Place.kaehlerResidue`: the residue `res_P(ω)` of a Kähler differential `ω` at a
  rational place, computed with a separating uniformizer.

## Main results

* `TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating`: the Laurent expansion of `dz/dt`
  in `t` is the derivative of the Laurent expansion of `z`.
* `TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`: **the transformation formula**
  `res_{P,s}(z) = res_{P,t}(z · ds/dt)`.
* `TauCeti.Place.residue_derivativeOfSeparating`: `res_{P,t}(dy/dt) = 0`.
* `TauCeti.Place.kaehlerResidue_eq_kaehlerResidue`: the residue of a differential is independent
  of the uniformizer used to compute it.
* `TauCeti.Place.kaehlerResidue_D`: exact differentials have residue zero.

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
  -- The `k`-module structure on `k⸨X⸩` found by instance search is the coefficientwise one.
  have he (c : k) (z : F) : e (c • z) = c • e z := by
    ext n
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, TauCeti.LaurentSeries.coeff_algebraMap_mul,
      HahnSeries.coeff_smul, smul_eq_mul]
  have _ : IsScalarTower k F k⸨X⸩ := ⟨fun c z f ↦ by
    -- `z • f` is `e z * f` by the definition of `Module.compHom`.
    change e (c • z) * f = c • (e z * f)
    rw [he, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]⟩
  let D : Derivation k F k⸨X⸩ :=
    { toFun z := LaurentSeries.derivative k (e z)
      map_add' := by simp
      map_smul' := by simp [he]
      map_one_eq_zero' := by
        -- Unfold the derivation to its defining formula `z ↦ (e z)'`.
        change LaurentSeries.derivative k (e 1) = 0
        rw [map_one, ← HahnSeries.single_zero_one, LaurentSeries.derivative_apply,
          LaurentSeries.hasseDeriv_single]
        simp
      leibniz' a b := by
        -- `a • m` is `e a * m` by the definition of `Module.compHom`.
        change LaurentSeries.derivative k (e (a * b)) =
          e a * LaurentSeries.derivative k (e b) + e b * LaurentSeries.derivative k (e a)
        rw [map_mul, LaurentSeries.derivative_mul]
        ring }
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
  rw [kaehlerResidue_apply, LinearMap.map_smul, ← kaehlerBasisOfSeparating_apply htr (),
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

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

end TauCeti.Place
