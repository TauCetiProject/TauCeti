/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Basic
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Cartier's homothety operator on curves

For a formal group law `F` over a commutative ring `R` and `r : R`, **Cartier's homothety
operator** `[r]` (`FormalGroup.homothetyCurve F r`) sends `γ(T)` to `γ(r T)`
(`PowerSeries.rescale r`). It is an additive endomorphism of `F.Curve` satisfying `[1] = id`,
`[0] = 0`, `[r] ∘ [s] = [r * s]`, commutes with base change and formal-group homomorphisms, and
satisfies `[r] ∘ V_n = V_n ∘ [r^n]` and `f_n ∘ [r] = [r^n] ∘ f_n`.

## Main definitions and results

* `FormalGroup.homothetyCurve`: Cartier's homothety operator `[r] : γ(T) ↦ γ(r T)` on `F.Curve`.
* `FormalGroup.homothetyCurve_homothetyCurve`, `FormalGroup.map_homothetyCurve`,
  `TauCeti.FormalGroupHom.mapCurve_homothetyCurve`: multiplicativity and naturality of `[r]`.
* `FormalGroup.homothetyCurve_verschiebungCurve`, `FormalGroup.frobeniusCurve_homothetyCurve`:
  Cartier's commutation relations `[r] ∘ V_n = V_n ∘ [r^n]` and `f_n ∘ [r] = [r^n] ∘ f_n`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), Appendix A2.1.19.
-/

public section

namespace FormalGroup

open TauCeti (FormalGroupHom FormalGroupIso)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Cartier's homothety operator** `[r]` on curves of `F`, sending `γ(T)` to `γ(r T)`. -/
noncomputable def homothetyCurve (F : FormalGroup R) (r : R) : F.Curve →+ F.Curve where
  toFun γ := ⟨PowerSeries.rescale r γ.toPowerSeries, by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]; simp⟩
  map_zero' := Curve.ext (by simp)
  map_add' γ₁ γ₂ := Curve.ext <| by
    have ha := PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries
      γ₂.constantCoeff_toPowerSeries
    simp only [Curve.toPowerSeries_add, PowerSeries.rescale_eq_subst, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply ha (PowerSeries.HasSubst.smul_X' r).const]
    congr 1; exact funext <| Fin.forall_fin_two.mpr ⟨by simp, by simp⟩

/-- The underlying power series of `F.homothetyCurve r γ` is
`PowerSeries.rescale r γ.toPowerSeries`. -/
@[simp]
theorem toPowerSeries_homothetyCurve (F : FormalGroup R) (r : R) (γ : F.Curve) :
    (F.homothetyCurve r γ).toPowerSeries = PowerSeries.rescale r γ.toPowerSeries := (rfl)

/-- Homothety by `1` is the identity on curves. -/
@[simp]
theorem homothetyCurve_one (F : FormalGroup R) (γ : F.Curve) : F.homothetyCurve 1 γ = γ :=
  Curve.ext (by simp)

/-- Homothety by `0` sends every curve to `0`. -/
@[simp]
theorem homothetyCurve_zero (F : FormalGroup R) (γ : F.Curve) : F.homothetyCurve 0 γ = 0 :=
  Curve.ext (by simp [Curve.toPowerSeries_zero])

/-- Composing curve homotheties multiplies the scalars: `[r] ([s] γ) = [r * s] γ`. -/
@[simp]
theorem homothetyCurve_homothetyCurve (F : FormalGroup R) (r s : R) (γ : F.Curve) :
    F.homothetyCurve r (F.homothetyCurve s γ) = F.homothetyCurve (r * s) γ :=
  Curve.ext <| by simp only [toPowerSeries_homothetyCurve, PowerSeries.rescale_rescale, mul_comm]

/-- Base change commutes with Cartier's homothety operator on curves. -/
theorem map_homothetyCurve (F : FormalGroup R) (φ : R →+* S) (r : R) (γ : F.Curve) :
    Curve.map φ (F.homothetyCurve r γ) = (F.map φ).homothetyCurve (φ r) (Curve.map φ γ) :=
  Curve.ext <| by
    simp only [Curve.toPowerSeries_map, toPowerSeries_homothetyCurve, PowerSeries.rescale_map]

/-- Formal-group homomorphisms commute with Cartier's homothety operator on curves. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_homothetyCurve {F G : FormalGroup R}
    (f : FormalGroupHom F G) (r : R) (γ : F.Curve) :
    f.mapCurve (F.homothetyCurve r γ) = G.homothetyCurve r (f.mapCurve γ) :=
  Curve.ext <| by
    rw [FormalGroupHom.toPowerSeries_mapCurve, toPowerSeries_homothetyCurve,
      toPowerSeries_homothetyCurve, FormalGroupHom.toPowerSeries_mapCurve,
      PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
      PowerSeries.subst_comp_subst_apply γ.hasSubst (PowerSeries.HasSubst.smul_X' r)]

/-- Cartier's commutation relation `[r] ∘ V_n = V_n ∘ [r^n]`. -/
theorem homothetyCurve_verschiebungCurve (F : FormalGroup R) (r : R) {n : ℕ} (hn : n ≠ 0)
    (γ : F.Curve) :
    F.homothetyCurve r (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.homothetyCurve (r ^ n) γ) :=
  Curve.ext <| by
    simp only [toPowerSeries_homothetyCurve, toPowerSeries_verschiebungCurve,
      PowerSeries.rescale_expand]

/-- Cartier's commutation relation `f_n ∘ [r] = [r^n] ∘ f_n`. -/
theorem frobeniusCurve_homothetyCurve (F : FormalGroup R) [F.IsComm] (r : R) {n : ℕ} (hn : n ≠ 0)
    (γ : F.Curve) :
    F.frobeniusCurve n hn (F.homothetyCurve r γ) =
      F.homothetyCurve (r ^ n) (F.frobeniusCurve n hn γ) := by
  obtain ⟨A, Q, _, _, _, j, hj, _, F₀, _, γ₀, π, e, hγ₀⟩ :=
    Curve.exists_lift_of_isUnit_natCast F γ ∅ (by simp) (by simp)
  let F₁ : FormalGroup (Polynomial A) := F₀.map Polynomial.C
  let γ₁ : F₁.Curve := Curve.map Polynomial.C γ₀
  have h₁ : F₁.frobeniusCurve n hn (F₁.homothetyCurve Polynomial.X γ₁) =
      F₁.homothetyCurve (Polynomial.X ^ n) (F₁.frobeniusCurve n hn γ₁) := by
    refine Curve.map_injective (φ := Polynomial.mapRingHom j)
      (by simpa using Polynomial.map_injective j hj) ?_
    rw [F₁.map_frobeniusCurve, F₁.map_homothetyCurve, F₁.map_homothetyCurve,
      F₁.map_frobeniusCurve, map_pow]
    apply (F₁.map (Polynomial.mapRingHom j)).logIso.curveEquiv.injective
    refine Curve.ext <| PowerSeries.ext fun k ↦ ?_
    simp only [FormalGroupIso.curveEquiv_apply, logIso_toHom,
      FormalGroupHom.mapCurve_frobeniusCurve, FormalGroupHom.mapCurve_homothetyCurve,
      toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_homothetyCurve, PowerSeries.coeff_smul,
      PowerSeries.coeff_cartier, Nat.add_zero, PowerSeries.coeff_rescale, smul_eq_mul, pow_mul]
    ring
  let πP : Polynomial A →+* R := Polynomial.eval₂RingHom π r
  have hπC : πP.comp Polynomial.C = π := RingHom.ext fun _ ↦ Polynomial.eval₂_C _ _
  suffices ∀ (G : FormalGroup R) [G.IsComm], F₁.map πP = G → ∀ δ : G.Curve,
      δ.toPowerSeries = (Curve.map πP γ₁).toPowerSeries →
      G.frobeniusCurve n hn (G.homothetyCurve r δ) =
        G.homothetyCurve (r ^ n) (G.frobeniusCurve n hn δ) by
    rw [← hγ₀, ← e.toHom.mapCurve_homothetyCurve, ← e.toHom.mapCurve_frobeniusCurve,
      ← e.toHom.mapCurve_frobeniusCurve, ← e.toHom.mapCurve_homothetyCurve]
    refine congrArg e.toHom.mapCurve (this (F₀.map π) ?_ (Curve.map π γ₀) ?_)
    · rw [← hπC, FormalGroup.map_comp]
    · rw [Curve.toPowerSeries_map, Curve.toPowerSeries_map, Curve.toPowerSeries_map,
        ← RingHom.comp_apply, ← PowerSeries.map_comp, hπC]
  rintro _ _ rfl δ hδ
  obtain rfl : δ = Curve.map πP γ₁ := Curve.ext hδ
  have hπX : πP Polynomial.X = r := Polynomial.eval₂_X _ _
  simpa only [F₁.map_frobeniusCurve, F₁.map_homothetyCurve, map_pow, hπX] using
    congrArg (Curve.map πP) h₁

end FormalGroup
