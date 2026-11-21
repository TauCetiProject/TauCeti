/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector
public import TauCeti.RingTheory.FormalGroup.Rescale.Hom
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Homothety operators on curves of formal group laws

For a formal group law `F` over a commutative ring `R` and a scalar `c ∈ R`, substituting `c T`
for the curve parameter `T` defines Cartier's homothety endomorphism `[c]`
(`FormalGroup.rescaleCurve`) on the group of curves `F.Curve`. Together with Verschiebung `V_n`
and Frobenius `f_n`, the homotheties `[c]` generate Cartier's operator ring acting on `F.Curve`.

Over a `ℚ`-algebra, `[c]` acts on the formal logarithm of a curve by `PowerSeries.rescale c`.
Over any commutative ring `R` (including rings with torsion or zero divisors), `[c]` satisfies
Cartier's operator identities `[c] ∘ V_n = V_n ∘ [c^n]` and `f_n ∘ [c] = [c^n] ∘ f_n`, commutes
with every elementary Cartier projector `FormalGroup.cartierProjectorCurve`, and identifies the
pushforward of the tautological curve along `FormalGroup.rescaleHom F s` with `[s] γ_0`.

## Main definitions

* `FormalGroup.rescaleCurve`: Cartier's homothety operator `[c] : F.Curve →+ F.Curve`, sending
  `γ(T)` to `γ(c T)` (`PowerSeries.rescale c`).

## Main results

* `FormalGroup.rescaleCurve_one`, `FormalGroup.rescaleCurve_zero`, and
  `FormalGroup.rescaleCurve_rescaleCurve`: multiplicative monoid action laws on curves.
* `FormalGroup.rescaleCurve_injective`: `[c]` is injective whenever `c` is left-regular.
* `FormalGroup.toPowerSeries_mapCurve_rescaleHom` and
  `FormalGroup.mapCurve_rescaleHom_tautologicalCurve`: interaction between `FormalGroup.rescaleHom`
  and curves on `F.rescale s`.
* `FormalGroup.rescaleCurve_verschiebungCurve`: `[c] (V_n γ) = V_n ([c^n] γ)`.
* `FormalGroup.frobeniusCurve_rescaleCurve`: `f_n ([c] γ) = [c^n] (f_n γ)` over any commutative
  ring.
* `FormalGroup.cartierProjectorCurve_rescaleCurve`: elementary Cartier projectors commute with
  curve homotheties `[c]`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.1–16.2.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.19.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Cartier's homothety operator** `[c]` on curves of a formal group law `F`, sending `γ(T)` to
`γ(c T)` (`PowerSeries.rescale c`). -/
noncomputable def rescaleCurve (F : FormalGroup R) (c : R) : F.Curve →+ F.Curve where
  toFun γ :=
    ⟨PowerSeries.rescale c γ.toPowerSeries, by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        γ.coeff_zero_toPowerSeries, mul_zero]⟩
  map_zero' := Curve.ext (by simp)
  map_add' γ₁ γ₂ := Curve.ext <| by
    have ha := PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries
      γ₂.constantCoeff_toPowerSeries
    have hc : PowerSeries.HasSubst (c • PowerSeries.X : PowerSeries R) :=
      .of_constantCoeff_zero' (by simp)
    simp only [Curve.toPowerSeries_add, PowerSeries.rescale_eq_subst, PowerSeries.subst_def,
      subst_comp_subst_apply ha hc.const]
    congr 1
    exact funext <| Fin.forall_fin_two.mpr ⟨by simp, by simp⟩

/-- Forgetting a rescaled curve recovers `PowerSeries.rescale`. -/
@[simp]
theorem toPowerSeries_rescaleCurve (F : FormalGroup R) (c : R) (γ : F.Curve) :
    (F.rescaleCurve c γ).toPowerSeries = PowerSeries.rescale c γ.toPowerSeries := (rfl)

/-- Rescaling the curve parameter by `1` is the identity on curves. -/
@[simp]
theorem rescaleCurve_one (F : FormalGroup R) (γ : F.Curve) :
    F.rescaleCurve 1 γ = γ :=
  Curve.ext (by simp)

/-- Rescaling the curve parameter by `0` sends every curve to `0`. -/
@[simp]
theorem rescaleCurve_zero (F : FormalGroup R) (γ : F.Curve) :
    F.rescaleCurve 0 γ = 0 :=
  Curve.ext (by simp)

/-- Successive curve parameter rescalings multiply their scalars. -/
@[simp]
theorem rescaleCurve_rescaleCurve (F : FormalGroup R) (a b : R) (γ : F.Curve) :
    F.rescaleCurve a (F.rescaleCurve b γ) = F.rescaleCurve (a * b) γ :=
  Curve.ext <| by
    rw [toPowerSeries_rescaleCurve, toPowerSeries_rescaleCurve, toPowerSeries_rescaleCurve,
      PowerSeries.rescale_rescale, mul_comm]

/-- Rescaling the curve parameter by a left-regular scalar is injective. -/
theorem rescaleCurve_injective (F : FormalGroup R) {c : R} (hc : IsLeftRegular c) :
    Function.Injective (F.rescaleCurve c) := by
  intro γ δ h
  apply Curve.ext
  ext k
  rcases eq_or_ne k 0 with rfl | _
  · rw [γ.coeff_zero_toPowerSeries, δ.coeff_zero_toPowerSeries]
  · have hk' := congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries) h
    simp only [Function.comp_apply, toPowerSeries_rescaleCurve, PowerSeries.coeff_rescale] at hk'
    exact (hc.pow k) hk'

/-- Base change commutes with rescaling the curve parameter. -/
theorem map_rescaleCurve (F : FormalGroup R) (φ : R →+* S) (c : R) (γ : F.Curve) :
    Curve.map φ (F.rescaleCurve c γ) = (F.map φ).rescaleCurve (φ c) (Curve.map φ γ) :=
  Curve.ext <| by
    ext k
    simp [PowerSeries.coeff_rescale]

/-- Homomorphisms of formal group laws commute with rescaling the curve parameter. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_rescaleCurve {F G : FormalGroup R}
    (f : TauCeti.FormalGroupHom F G) (c : R) (γ : F.Curve) :
    f.mapCurve (F.rescaleCurve c γ) = G.rescaleCurve c (f.mapCurve γ) := by
  ext : 1
  have hc : PowerSeries.HasSubst (c • PowerSeries.X : PowerSeries R) :=
    .of_constantCoeff_zero' (by simp)
  simp only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, toPowerSeries_rescaleCurve,
    PowerSeries.rescale_eq_subst]
  exact (PowerSeries.subst_comp_subst_apply γ.hasSubst hc f.toPowerSeries).symm

/-- Pushing a curve on `F.rescale s` forward along `F.rescaleHom s` scales its power series by
`s`. -/
theorem toPowerSeries_mapCurve_rescaleHom (F : FormalGroup R) (s : R)
    (γ : (F.rescale s).Curve) :
    ((F.rescaleHom s).mapCurve γ).toPowerSeries = s • γ.toPowerSeries := by
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, rescaleHom_toPowerSeries,
    PowerSeries.subst_smul γ.hasSubst, PowerSeries.subst_X γ.hasSubst]

/-- Pushing the tautological curve of `F.rescale s` forward along `F.rescaleHom s` produces the
homothety `[s]` of the tautological curve of `F`. -/
theorem mapCurve_rescaleHom_tautologicalCurve (F : FormalGroup R) (s : R) :
    (F.rescaleHom s).mapCurve (F.rescale s).tautologicalCurve =
      F.rescaleCurve s F.tautologicalCurve :=
  Curve.ext (by simp [PowerSeries.smul_eq_C_mul])

/-- **Cartier's homothety–Verschiebung relation `[c] ∘ V_n = V_n ∘ [c^n]`** on curves of any
formal group law. -/
theorem rescaleCurve_verschiebungCurve (F : FormalGroup R) (c : R) (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    F.rescaleCurve c (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.rescaleCurve (c ^ n) γ) :=
  Curve.ext <| by
    rw [toPowerSeries_rescaleCurve, toPowerSeries_verschiebungCurve,
      toPowerSeries_verschiebungCurve, toPowerSeries_rescaleCurve,
      PowerSeries.rescale_expand n hn c γ.toPowerSeries]

/-- Over a `ℚ`-algebra, rescaling the curve parameter rescales the formal logarithm of the curve:
`log_F((γ(c T))) = (log_F(γ))(c T)`. -/
theorem subst_rescaleCurve_log [Algebra ℚ R] (F : FormalGroup R) (c : R) (γ : F.Curve) :
    PowerSeries.subst (F.rescaleCurve c γ).toPowerSeries F.log =
      PowerSeries.rescale c (PowerSeries.subst γ.toPowerSeries F.log) := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    toPowerSeries_rescaleCurve] using
    congrArg Curve.toPowerSeries (F.logHom.mapCurve_rescaleCurve c γ)

private theorem frobeniusCurve_rescaleCurve_of_ratAlgebra [Algebra ℚ R] (F : FormalGroup R)
    [F.IsComm] (c : R) (n : ℕ) (hn : n ≠ 0) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.rescaleCurve c γ) =
      F.rescaleCurve (c ^ n) (F.frobeniusCurve n hn γ) := by
  apply F.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    subst_frobeniusCurve_log, subst_rescaleCurve_log, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero, PowerSeries.coeff_rescale, smul_eq_mul, ← pow_mul]
  ring

/-- **Cartier's homothety–Frobenius relation `f_n ∘ [c] = [c^n] ∘ f_n`** on curves of a commutative
formal group law over any commutative ring. -/
theorem frobeniusCurve_rescaleCurve (F : FormalGroup R) [F.IsComm] (c : R) (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    F.frobeniusCurve n hn (F.rescaleCurve c γ) =
      F.rescaleCurve (c ^ n) (F.frobeniusCurve n hn γ) := by
  obtain ⟨A, Q, _, _, _, j, hj, -, F₀, _, γ₀, π, e, rfl⟩ :=
    Curve.exists_lift_of_isUnit_natCast F γ ∅ (by simp) (by simp)
  let jP : Polynomial A →+* Polynomial Q := Polynomial.mapRingHom j
  have hjP : Function.Injective jP := Polynomial.map_injective j hj
  let F_A : FormalGroup (Polynomial A) := F₀.map Polynomial.C
  let γ_A : F_A.Curve := Curve.map Polynomial.C γ₀
  have hA : F_A.frobeniusCurve n hn (F_A.rescaleCurve Polynomial.X γ_A) =
      F_A.rescaleCurve (Polynomial.X ^ n) (F_A.frobeniusCurve n hn γ_A) := by
    apply Curve.map_injective hjP
    rw [F_A.map_frobeniusCurve jP, F_A.map_rescaleCurve jP, F_A.map_rescaleCurve jP,
      F_A.map_frobeniusCurve jP, map_pow]
    exact frobeniusCurve_rescaleCurve_of_ratAlgebra (F_A.map jP) (jP Polynomial.X) n hn
      (Curve.map jP γ_A)
  let πP : Polynomial A →+* R := Polynomial.eval₂RingHom π c
  have hπC : πP.comp Polynomial.C = π := Polynomial.eval₂RingHom_comp_C π c
  have hFA : F_A.map πP = F₀.map π := by
    dsimp only [F_A]
    rw [FormalGroup.map_comp, hπC]
  let f' : TauCeti.FormalGroupHom (F_A.map πP) F := e.toHom.ofSourceEq hFA.symm
  have hmap_γ : (Curve.map πP γ_A).toPowerSeries = (Curve.map π γ₀).toPowerSeries := by
    ext k
    dsimp only [γ_A]
    rw [Curve.toPowerSeries_map, Curve.toPowerSeries_map, Curve.toPowerSeries_map,
      PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map,
      ← RingHom.comp_apply, hπC]
  have hγ : f'.mapCurve (Curve.map πP γ_A) = e.toHom.mapCurve (Curve.map π γ₀) := by
    ext : 1
    rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
      TauCeti.FormalGroupHom.toPowerSeries_mapCurve, hmap_γ,
      TauCeti.FormalGroupHom.ofSourceEq_toPowerSeries]
  have hc : πP Polynomial.X = c := Polynomial.eval₂_X π c
  rw [← hγ, ← f'.mapCurve_rescaleCurve, ← f'.mapCurve_frobeniusCurve,
    ← f'.mapCurve_frobeniusCurve, ← f'.mapCurve_rescaleCurve, ← hc, ← map_pow,
    ← F_A.map_rescaleCurve πP, ← F_A.map_frobeniusCurve πP,
    ← F_A.map_frobeniusCurve πP, ← F_A.map_rescaleCurve πP, hA]

/-- Elementary Cartier projectors commute with rescaling the curve parameter. -/
theorem cartierProjectorCurve_rescaleCurve (F : FormalGroup R) [F.IsComm] (c : R) (n : ℕ)
    (hn : n ≠ 0) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit (F.rescaleCurve c γ) =
      F.rescaleCurve c (F.cartierProjectorCurve n hn hunit γ) := by
  rw [cartierProjectorCurve_apply, cartierProjectorCurve_apply, map_sub,
    frobeniusCurve_rescaleCurve,
    ← F.map_nsmulCurveEquiv_symm (F.rescaleCurve (c ^ n)) n hunit hunit,
    ← rescaleCurve_verschiebungCurve]

end FormalGroup
