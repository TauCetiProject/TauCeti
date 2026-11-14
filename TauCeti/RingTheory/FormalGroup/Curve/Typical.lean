/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector

/-!
# Cartier's `p`-typical projector on curves

Let `F` be a commutative formal group law over a commutative ring `R`, and let `p` be a natural
number such that every prime `ℓ ≠ p` is invertible in `R` (for `p` prime: `R` is a
`ℤ_(p)`-algebra). A curve `γ` on `F` is **`p`-typical** if Cartier's Frobenius operator `f_ℓ`
kills it for every prime `ℓ ≠ p`.

Cartier's projector `ε_p` onto the `p`-typical curves is the infinite composite of the elementary
projectors `1 - V_ℓ [ℓ]⁻¹ f_ℓ` over the primes `ℓ ≠ p`. The elementary projector of index `ℓ`
preserves the coefficients of degree `< ℓ`, so the composite over the primes `ℓ < N` stabilizes in
each degree below `N`, and `ε_p` is defined coefficientwise as this stable value. It is additive,
natural for base change and for homomorphisms of formal group laws, preserves the linear
coefficient, and is an idempotent with image exactly the `p`-typical curves. On the formal
logarithm it keeps precisely the degrees all of whose prime factors equal `p`; for `p` prime,
these are the powers of `p`.

Applied to the tautological curve, `ε_p` produces the `p`-typical coordinate whose formal group
law has a logarithm of the form `∑ mᵢ X^(pⁱ)`, the algebraic source of Quillen's idempotent on the
`p`-localized Lazard ring and of the Brown–Peterson coefficient ring.

## Main definitions

* `FormalGroup.typicalCurves`: the additive subgroup of `p`-typical curves, killed by `f_ℓ` for
  every prime `ℓ ≠ p`.
* `FormalGroup.typicalProjectorCurve`: Cartier's projector `ε_p` onto the `p`-typical curves.

## Main results

* `FormalGroup.frobeniusCurve_typicalProjectorCurve` and
  `FormalGroup.typicalProjectorCurve_verschiebungCurve`: `f_ℓ ∘ ε_p = 0` and `ε_p ∘ V_ℓ = 0` for
  every prime `ℓ ≠ p`.
* `FormalGroup.typicalProjectorCurve_eq_self_iff` and `FormalGroup.range_typicalProjectorCurve`:
  `ε_p` fixes exactly the `p`-typical curves, and its image is the group of `p`-typical curves.
* `FormalGroup.map_typicalProjectorCurve` and
  `TauCeti.FormalGroupHom.mapCurve_typicalProjectorCurve`: naturality.
* `FormalGroup.coeff_subst_typicalProjectorCurve_log` and
  `FormalGroup.coeff_subst_typicalProjectorCurve_log_of_prime`: over a `ℚ`-algebra, `ε_p` keeps
  exactly the terms of the logarithm in degrees whose prime factors are all `p`, that is, in
  degrees `pⁱ` when `p` is prime.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Typical curves -/

section TypicalCurves

variable (F : FormalGroup R) [F.IsComm]

/-- The **`p`-typical curves** on a commutative formal group law: the curves killed by Cartier's
Frobenius operator `f_ℓ` for every prime `ℓ ≠ p`. -/
noncomputable def typicalCurves (p : ℕ) : AddSubgroup F.Curve :=
  ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ≠ p), (F.frobeniusCurve ℓ hℓ.ne_zero).ker

/-- A curve is `p`-typical exactly when `f_ℓ` kills it for every prime `ℓ ≠ p`. -/
@[simp]
theorem mem_typicalCurves {p : ℕ} {γ : F.Curve} :
    γ ∈ F.typicalCurves p ↔ ∀ ℓ (hℓ : ℓ.Prime), ℓ ≠ p → F.frobeniusCurve ℓ hℓ.ne_zero γ = 0 := by
  simp [typicalCurves, AddSubgroup.mem_iInf]

end TypicalCurves

/-! ### The finite stages of the projector -/

section Stage

variable (F : FormalGroup R) [F.IsComm] (p : ℕ)
  (hR : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → IsUnit (ℓ : R))

/-- The composite of the elementary Cartier projectors at the primes `ℓ < N` with `ℓ ≠ p`. -/
private noncomputable def typicalProjectorStage : ℕ → F.Curve →+ F.Curve
  | 0 => AddMonoidHom.id F.Curve
  | N + 1 =>
    if h : N.Prime ∧ N ≠ p then
      (F.cartierProjectorCurve N h.1.ne_zero (hR N h.1 h.2)).comp (typicalProjectorStage N)
    else typicalProjectorStage N

/-- The stages of the projector are eventually constant in each degree. -/
private theorem coeff_typicalProjectorStage_of_lt {k N M : ℕ} (hk : k < N) (hNM : N ≤ M)
    (γ : F.Curve) :
    PowerSeries.coeff k (typicalProjectorStage F p hR M γ).toPowerSeries =
      PowerSeries.coeff k (typicalProjectorStage F p hR N γ).toPowerSeries := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [← ih, typicalProjectorStage]
    split_ifs with h
    · exact F.coeff_cartierProjectorCurve_of_lt M h.1.ne_zero _ (by omega) _
    · rfl

/-- The stages fix every curve on which all their factors act trivially. -/
private theorem typicalProjectorStage_eq_self {γ : F.Curve} (hγ : γ ∈ F.typicalCurves p)
    (N : ℕ) : typicalProjectorStage F p hR N γ = γ := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [typicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, ih]
      exact F.cartierProjectorCurve_eq_self N h.1.ne_zero _
        ((F.mem_typicalCurves).mp hγ N h.1 h.2)
    · exact ih

/-- A coefficient in a degree `k` whose primes `ℓ ≤ k` all equal `p` is left unchanged by the
stages. -/
private theorem coeff_typicalProjectorStage_of_forall_prime_le {k : ℕ}
    (hk : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ k → ℓ = p) (γ : F.Curve) {N : ℕ} (hN : N ≤ k + 1) :
    PowerSeries.coeff k (typicalProjectorStage F p hR N γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [typicalProjectorStage]
    split_ifs with h
    · exact absurd (hk N h.1 (by omega)) h.2
    · exact ih (by omega)

private theorem map_typicalProjectorStage (φ : R →+* S)
    (hS : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → IsUnit (ℓ : S)) (N : ℕ) (γ : F.Curve) :
    Curve.map φ (typicalProjectorStage F p hR N γ) =
      typicalProjectorStage (F.map φ) p hS N (Curve.map φ γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [typicalProjectorStage, typicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, map_cartierProjectorCurve, ih]
    · exact ih

private theorem mapCurve_typicalProjectorStage {G : FormalGroup R} [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (N : ℕ) (γ : F.Curve) :
    f.mapCurve (typicalProjectorStage F p hR N γ) =
      typicalProjectorStage G p hR N (f.mapCurve γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [typicalProjectorStage, typicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

/-- On the additive formal group, the stage `N` deletes the coefficients in the degrees divisible
by a prime `ℓ < N` other than `p`. -/
private theorem coeff_typicalProjectorStage_𝔾ₐ
    (hR : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → IsUnit (ℓ : R)) (N k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k (typicalProjectorStage 𝔾ₐ p hR N γ).toPowerSeries =
      if ∀ ℓ < N, ℓ.Prime → ℓ ∣ k → ℓ = p then PowerSeries.coeff k γ.toPowerSeries else 0 := by
  induction N with
  | zero => rw [ite_eq_left (by simp)]; rfl
  | succ N ih =>
    rw [typicalProjectorStage]
    -- Split on whether `N` is a prime other than `p`, and on both coefficient conditions.
    split_ifs
    · rw [AddMonoidHom.comp_apply, coeff_cartierProjectorCurve_𝔾ₐ, ih]
      grind
    · rw [AddMonoidHom.comp_apply, coeff_cartierProjectorCurve_𝔾ₐ, ih]
      grind
    · rw [ih]
      grind
    · rw [ih]
      grind

end Stage

/-! ### Cartier's projector -/

section Projector

variable (F : FormalGroup R) [F.IsComm] (p : ℕ)
  (hR : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → IsUnit (ℓ : R))

/-- **Cartier's `p`-typical projector** `ε_p` on curves of a commutative formal group law, when
every prime `ℓ ≠ p` is invertible: the infinite composite of the elementary Cartier projectors
`1 - V_ℓ [ℓ]⁻¹ f_ℓ` over the primes `ℓ ≠ p`, computed coefficientwise. Its degree-`k`
coefficient is that of the composite over the primes `ℓ ≤ k`. -/
noncomputable def typicalProjectorCurve : F.Curve →+ F.Curve where
  toFun γ :=
    ⟨PowerSeries.mk fun k ↦
        PowerSeries.coeff k (typicalProjectorStage F p hR (k + 1) γ).toPowerSeries, by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
        Curve.coeff_zero_toPowerSeries]⟩
  map_zero' := Curve.ext <| PowerSeries.ext fun k ↦ by simp
  map_add' γ δ := Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [PowerSeries.coeff_mk, map_add]
    refine Curve.coeff_add_congr (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;>
      rw [PowerSeries.coeff_mk,
        coeff_typicalProjectorStage_of_lt F p hR (Nat.lt_succ_self i) (by omega)]

/-- The degree-`k` coefficient of `ε_p γ` is that of every finite stage beyond `k`. -/
private theorem coeff_typicalProjectorCurve_eq_stage {k N : ℕ} (hk : k < N) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorCurve p hR γ).toPowerSeries =
      PowerSeries.coeff k (typicalProjectorStage F p hR N γ).toPowerSeries := by
  simp only [typicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk]
  exact (coeff_typicalProjectorStage_of_lt F p hR (Nat.lt_succ_self k) hk γ).symm

/-- The projector leaves unchanged every coefficient in a degree `k` such that all primes
`ℓ ≤ k` equal `p`; in particular every coefficient below the least prime other than `p`. -/
theorem coeff_typicalProjectorCurve_of_forall_prime_le {k : ℕ}
    (hk : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ k → ℓ = p) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorCurve p hR γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  rw [coeff_typicalProjectorCurve_eq_stage F p hR (Nat.lt_succ_self k)]
  exact coeff_typicalProjectorStage_of_forall_prime_le F p hR hk γ le_rfl

/-- The projector preserves the linear coefficient. -/
@[simp]
theorem coeff_one_typicalProjectorCurve (γ : F.Curve) :
    PowerSeries.coeff 1 (F.typicalProjectorCurve p hR γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_typicalProjectorCurve_of_forall_prime_le p hR
    (fun _ hℓ h ↦ absurd (hℓ.two_le.trans h) (by norm_num)) γ

/-- A `p`-typical curve is fixed by Cartier's projector. -/
theorem typicalProjectorCurve_eq_self {γ : F.Curve} (hγ : γ ∈ F.typicalCurves p) :
    F.typicalProjectorCurve p hR γ = γ :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [coeff_typicalProjectorCurve_eq_stage F p hR (Nat.lt_succ_self k),
      typicalProjectorStage_eq_self F p hR hγ]

/-- Base change commutes with Cartier's projector. -/
theorem map_typicalProjectorCurve (φ : R →+* S) (γ : F.Curve) :
    Curve.map φ (F.typicalProjectorCurve p hR γ) =
      (F.map φ).typicalProjectorCurve p
        (fun ℓ hℓ hℓp ↦ by simpa using (hR ℓ hℓ hℓp).map φ) (Curve.map φ γ) :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
      coeff_typicalProjectorCurve_eq_stage F p hR (Nat.lt_succ_self k),
      coeff_typicalProjectorCurve_eq_stage _ p _ (Nat.lt_succ_self k),
      ← map_typicalProjectorStage, Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- Formal-group homomorphisms commute with Cartier's projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_typicalProjectorCurve {G : FormalGroup R}
    [G.IsComm] (f : TauCeti.FormalGroupHom F G) (γ : F.Curve) :
    f.mapCurve (F.typicalProjectorCurve p hR γ) = G.typicalProjectorCurve p hR (f.mapCurve γ) :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [coeff_typicalProjectorCurve_eq_stage G p hR (Nat.lt_succ_self k),
      ← mapCurve_typicalProjectorStage]
    exact f.coeff_mapCurve_congr fun i hi ↦
      coeff_typicalProjectorCurve_eq_stage F p hR (by omega) γ

open scoped Classical in
/-- On the additive formal group, Cartier's projector keeps exactly the coefficients in the
degrees all of whose prime factors equal `p`. -/
theorem coeff_typicalProjectorCurve_𝔾ₐ (k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).typicalProjectorCurve p hR γ).toPowerSeries =
      if ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ k → ℓ = p then PowerSeries.coeff k γ.toPowerSeries else 0 := by
  rw [coeff_typicalProjectorCurve_eq_stage _ p hR (Nat.lt_succ_self k),
    coeff_typicalProjectorStage_𝔾ₐ]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · congr 1
    exact propext ⟨fun h ℓ hℓ hdvd ↦
      h ℓ (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hdvd)) hℓ hdvd, fun h ℓ _ ↦ h ℓ⟩

open scoped Classical in
/-- Over a `ℚ`-algebra, Cartier's projector keeps exactly the terms of the formal logarithm in the
degrees all of whose prime factors equal `p`. -/
theorem coeff_subst_typicalProjectorCurve_log [Algebra ℚ R] (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hR γ).toPowerSeries F.log) =
      if ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ k → ℓ = p then
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) else 0 := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] using
    (congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff k δ.toPowerSeries)
      (F.logHom.mapCurve_typicalProjectorCurve F p hR γ)).trans
      (coeff_typicalProjectorCurve_𝔾ₐ p hR k _)

open scoped Classical in
/-- Over a `ℚ`-algebra and for `p` prime, Cartier's projector keeps exactly the terms of the
formal logarithm in the degrees `pⁱ`. -/
theorem coeff_subst_typicalProjectorCurve_log_of_prime [Algebra ℚ R] (hp : p.Prime) (k : ℕ)
    (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hR γ).toPowerSeries F.log) =
      if ∃ i, p ^ i = k then PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rw [coeff_subst_typicalProjectorCurve_log]
  congr 1
  refine propext ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne k 0 with rfl | hk
    · -- Both `2` and `3` divide `0`, so they cannot both equal `p`.
      have h2 := h 2 Nat.prime_two (dvd_zero 2)
      have h3 := h 3 Nat.prime_three (dvd_zero 3)
      omega
    · exact ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hk fun hd hdvd ↦ h _ hd hdvd).symm⟩
  · rintro ⟨i, rfl⟩ ℓ hℓ hdvd
    exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hdvd)

/-- **Cartier's Frobenius kills the projection**: `f_ℓ ∘ ε_p = 0` for every prime `ℓ ≠ p`. -/
@[simp]
theorem frobeniusCurve_typicalProjectorCurve {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (γ : F.Curve) :
    F.frobeniusCurve ℓ hℓ.ne_zero (F.typicalProjectorCurve p hR γ) = 0 := by
  let P : Set ℕ := {n | n.Prime ∧ n ≠ p}
  refine Curve.eq_of_forall_ratAlgebra F γ P (fun n hn ↦ hR n hn.1 hn.2)
    (fun G _ h δ ↦ G.frobeniusCurve ℓ hℓ.ne_zero
      (G.typicalProjectorCurve p (fun n hn hnp ↦ h n ⟨hn, hnp⟩) δ))
    (fun _ _ _ _ ↦ 0) (fun G _ h δ ↦ ?_)
    (fun G _ _ _ φ δ ↦ by rw [map_frobeniusCurve, map_typicalProjectorCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_typicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)
  apply G.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    G.logHom.mapCurve_frobeniusCurve, toPowerSeries_frobeniusCurve_𝔾ₐ, map_zero,
    Curve.toPowerSeries_zero, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_subst_typicalProjectorCurve_log, smul_eq_mul]
  split_ifs with h
  · exact absurd (h ℓ hℓ (dvd_mul_right ℓ k)) hℓp
  · rw [mul_zero]

/-- **Cartier's projector kills Verschiebung**: `ε_p ∘ V_ℓ = 0` for every prime `ℓ ≠ p`. -/
@[simp]
theorem typicalProjectorCurve_verschiebungCurve {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (γ : F.Curve) :
    F.typicalProjectorCurve p hR (F.verschiebungCurve ℓ hℓ.ne_zero γ) = 0 := by
  let P : Set ℕ := {n | n.Prime ∧ n ≠ p}
  refine Curve.eq_of_forall_ratAlgebra F γ P (fun n hn ↦ hR n hn.1 hn.2)
    (fun G _ h δ ↦ G.typicalProjectorCurve p (fun n hn hnp ↦ h n ⟨hn, hnp⟩)
      (G.verschiebungCurve ℓ hℓ.ne_zero δ))
    (fun _ _ _ _ ↦ 0) (fun G _ h δ ↦ ?_)
    (fun G _ _ _ φ δ ↦ by rw [map_typicalProjectorCurve, map_verschiebungCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_typicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)
  apply G.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom, map_zero,
    Curve.toPowerSeries_zero, TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_subst_typicalProjectorCurve_log, subst_verschiebungCurve_log, PowerSeries.coeff_expand]
  split_ifs with h hdvd
  · exact absurd (h ℓ hℓ hdvd) hℓp
  · rfl
  · rfl

/-- The image of Cartier's projector consists of `p`-typical curves. -/
theorem typicalProjectorCurve_mem_typicalCurves (γ : F.Curve) :
    F.typicalProjectorCurve p hR γ ∈ F.typicalCurves p :=
  (F.mem_typicalCurves).mpr fun _ hℓ hℓp ↦ F.frobeniusCurve_typicalProjectorCurve p hR hℓ hℓp γ

/-- The fixed curves of Cartier's projector are exactly the `p`-typical curves. -/
@[simp]
theorem typicalProjectorCurve_eq_self_iff (γ : F.Curve) :
    F.typicalProjectorCurve p hR γ = γ ↔ γ ∈ F.typicalCurves p :=
  ⟨fun h ↦ h ▸ F.typicalProjectorCurve_mem_typicalCurves p hR γ,
    F.typicalProjectorCurve_eq_self p hR⟩

/-- Cartier's projector is idempotent. -/
@[simp]
theorem typicalProjectorCurve_typicalProjectorCurve (γ : F.Curve) :
    F.typicalProjectorCurve p hR (F.typicalProjectorCurve p hR γ) =
      F.typicalProjectorCurve p hR γ :=
  F.typicalProjectorCurve_eq_self p hR (F.typicalProjectorCurve_mem_typicalCurves p hR γ)

/-- Cartier's projector is an idempotent in the endomorphism ring of curves. -/
@[simp]
theorem isIdempotentElem_typicalProjectorCurve :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.typicalProjectorCurve p hR) :=
  AddMonoidHom.ext (F.typicalProjectorCurve_typicalProjectorCurve p hR)

/-- The image of Cartier's projector is precisely the group of `p`-typical curves. -/
@[simp]
theorem range_typicalProjectorCurve :
    (F.typicalProjectorCurve p hR).range = F.typicalCurves p := by
  ext γ
  rw [AddMonoidHom.mem_range]
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.typicalProjectorCurve_mem_typicalCurves p hR δ,
    fun hγ ↦ ⟨γ, F.typicalProjectorCurve_eq_self p hR hγ⟩⟩

end Projector

end FormalGroup
