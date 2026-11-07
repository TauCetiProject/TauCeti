/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Algebra.Module.ZLattice.Family.CyclicQuotient

/-!
# The logarithmic gauge of a cyclic quotient of a family of tori

Let `D_t` be the disc of radius `r ^ m` about `0` and `P : D_t → (Λ →ₗ[ℤ] E)` a family of
periods, with family of tori `Y = (D_t × E)/Λ`. Its pullback along the power map
`β_m : D_z → D_t`, `z ↦ z ^ m`, from the disc `D_z` of radius `r` is the family
`X = (D_z × E)/Λ` with periods `P (z ^ m)` (`TauCeti.powPullbackPeriod`). Fix `l : Λ`. The
rotation by an `m`-th root of unity `ζ` acts on `X` by
`ζ • [z, e] = [ζ z, e + (log ζ / 2πi) • P (z ^ m) l]`
(`TauCeti.logTranslationMulAction`): the linear part is trivial and the translation part is the
normalized pure translation. Any logarithm of `ζ` may be used in this formula, since two of them
change the translation by a period (`TauCeti.logTranslationMulAction_smul_mk_of_exp_eq`); for the
generator `ζ = exp (2πi / m)` the translation is `(1 / m) • P (z ^ m) l`. Let
`Q = X / C_m` be the orbit space, with its coordinate `t = z ^ m`
(`TauCeti.torusFamilyCyclicQuotientProjection`).

Over the punctured disc `D_t*` the cyclic quotient is canonically the family `Y` itself, by the
*logarithmic gauge*
`G [z, e] = [z ^ m, e - (log z / 2πi) • P (z ^ m) l]`.
Here too the logarithm of `z` is any branch: a change of branch by `2πi k` changes `G` by the
period `k • P (z ^ m) l` (`TauCeti.torusFamilyLogGauge_mk_of_exp_eq`), so the local formulas
patch to a single map `X* → Y*`. Replacing `z` by `ζ z` adds `log ζ` to the logarithm, which
cancels the translation of the action, so `G` is invariant under the rotations
(`TauCeti.torusFamilyLogGauge_smul`) and descends to `Q* → Y*`. Its inverse sends `[t, e]` to the
class of `[z, e + (log z / 2πi) • P t l]` for any `m`-th root `z` of `t` and any logarithm of `z`
(`TauCeti.torusFamilyLogGaugeEquiv_symm_mk`). The result is an equivalence over `D_t*`
(`TauCeti.torusFamilyLogGaugeEquiv`), and for continuous periods a homeomorphism
(`TauCeti.torusFamilyLogGaugeHomeomorph`). The period family `P` remains varying throughout.

Over the centre the gauge has no meaning: the logarithm has no limit at `0`, and the cyclic
quotient need not be locally a family of tori there.

## Main definitions

* `TauCeti.powPullbackPeriod`: the pullback of a family of periods along `z ↦ z ^ m`.
* `TauCeti.logTranslationMulAction`: the action of the `m`-th roots of unity on the pulled-back
  family by rotation and normalized translation.
* `TauCeti.torusFamilyLogGauge`: the logarithmic gauge `X → Y`, meaningful over `z ≠ 0`.
* `TauCeti.torusFamilyLogGaugeEquiv`: the equivalence `Q* ≃ Y*` over `D_t*`.
* `TauCeti.torusFamilyLogGaugeHomeomorph`: the same equivalence as a homeomorphism.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*.
-/

public section

open MulAction Set Filter Topology Complex
open scoped Real

namespace TauCeti

/-! ### Changing the branch of a logarithm -/

section Branch

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Two logarithms of the same number, divided by `2πi`, differ by an integer; so the vectors
`(a / 2πi) • v` and `(b / 2πi) • v` differ by an integer multiple of `v`. -/
theorem exists_div_two_pi_I_smul_eq_add_zsmul {a b : ℂ} (h : exp a = exp b) (v : E) :
    ∃ k : ℤ, (a / (2 * π * I)) • v = (b / (2 * π * I)) • v + k • v := by
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 h
  refine ⟨k, ?_⟩
  have h2 : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  rw [hk, ← Int.cast_smul_eq_zsmul ℂ, ← add_smul, add_div, mul_div_cancel_right₀ _ h2]

end Branch

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)

/-! ### The pulled-back family and its normalized translation action -/

variable (m r) in
/-- The pullback of a family of periods over the disc of radius `r ^ m` along the power map
`z ↦ z ^ m` from the disc of radius `r`: the periods at `z` are those of `P` at `z ^ m`. -/
noncomputable def powPullbackPeriod : rootsOfUnityBall m r → Λ →ₗ[ℤ] E :=
  fun z ↦ P (rootsOfUnityBall.powMap m r z)

/-- The periods of the pullback at `z` are those of `P` at `z ^ m`. -/
@[simp] theorem powPullbackPeriod_apply (z : rootsOfUnityBall m r) :
    powPullbackPeriod m r P z = P (rootsOfUnityBall.powMap m r z) := (rfl)

/-- The pulled-back periods are invariant under the rotations. This is the period-equivariance
law of `TauCeti.torusFamilyAffineMulAction` for the trivial linear part and the trivial
representation on `Λ`. -/
theorem powPullbackPeriod_smul_apply (ζ : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ) :
    powPullbackPeriod m r P (ζ • z) (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ ζ l) =
      AddMonoidHom.id E (powPullbackPeriod m r P z l) := by
  simp

variable [Module ℂ E] (l : Λ)

/-- The translation part of the normalized pure translation action: the rotation by `ζ` sends
the fibre over `z` to the fibre over `ζ z`, translating by `(log ζ / 2πi) • P (z ^ m) l`. -/
noncomputable def logTranslationSection (ζ : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) :
    letI := periodAddAction (powPullbackPeriod m r P)
    AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E) :=
  Quotient.mk _ (ζ • z, (log ((ζ : ℂˣ) : ℂ) / (2 * π * I)) • powPullbackPeriod m r P z l)

/-- The translation section of `ζ` at `z` lies over `ζ z`. -/
theorem torusFamilyProjection_logTranslationSection (ζ : rootsOfUnity m ℂ)
    (z : rootsOfUnityBall m r) :
    torusFamilyProjection (powPullbackPeriod m r P) (logTranslationSection P l ζ z) = ζ • z :=
  torusFamilyProjection_mk _ _

/-- The identity rotation translates by zero. -/
theorem logTranslationSection_one (z : rootsOfUnityBall m r) :
    logTranslationSection P l 1 z = Quotient.mk _ (z, 0) := by
  simp [logTranslationSection]

/-- **Changing the logarithm.** The class of the translation section does not depend on the
logarithm of `ζ`: any `L` with `exp L = ζ` gives the same point. -/
theorem logTranslationSection_eq_mk_of_exp_eq {ζ : rootsOfUnity m ℂ} {L : ℂ}
    (hL : exp L = ((ζ : ℂˣ) : ℂ)) (z : rootsOfUnityBall m r) :
    logTranslationSection P l ζ z =
      Quotient.mk _ (ζ • z, (L / (2 * π * I)) • powPullbackPeriod m r P z l) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  obtain ⟨k, hk⟩ := exists_div_two_pi_I_smul_eq_add_zsmul
    (hL.trans (exp_log (ζ : ℂˣ).ne_zero).symm) (powPullbackPeriod m r P z l)
  rw [logTranslationSection, Quotient.eq, AddAction.orbitRel_apply,
    mem_orbit_periodAddAction_iff]
  refine ⟨rfl, -k • l, ?_⟩
  rw [hk, sub_add_cancel_left, map_zsmul, neg_zsmul, powPullbackPeriod_apply,
    powPullbackPeriod_apply, rootsOfUnityBall.powMap_smul]

/-- **The cocycle law** of the translation section: translating by the section of `g * h` is
translating by the section of `h` and then applying the affine map of `g`. Both sides differ by
`(log (g h) - log g - log h) / 2πi`, an integer, times a period. -/
theorem logTranslationSection_mul (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) :
    logTranslationSection P l (g * h) z =
      torusFamilyAffineMap (fun _ _ ↦ AddMonoidHom.id E) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l) g
        (logTranslationSection P l h z) := by
  have hL : exp (log ((g : ℂˣ) : ℂ) + log ((h : ℂˣ) : ℂ)) =
      (((g * h : rootsOfUnity m ℂ) : ℂˣ) : ℂ) := by
    rw [Complex.exp_add, exp_log (g : ℂˣ).ne_zero, exp_log (h : ℂˣ).ne_zero, Subgroup.coe_mul,
      Units.val_mul]
  rw [logTranslationSection_eq_mk_of_exp_eq P l hL, logTranslationSection,
    torusFamilyAffineMap_mk_of_eq _ _ _ _ _ _ (logTranslationSection_eq_mk_of_exp_eq P l
      (exp_log (g : ℂˣ).ne_zero) _)]
  simp only [AddMonoidHom.id_apply, powPullbackPeriod_apply, rootsOfUnityBall.powMap_smul,
    mul_smul, add_div, add_smul]
  rw [add_comm]

/-- **The normalized pure translation action** of the `m`-th roots of unity on the family of
tori pulled back along `z ↦ z ^ m`: the rotation by `ζ` sends `[z, e]` to
`[ζ z, e + (log ζ / 2πi) • P (z ^ m) l]`. It is the affine action
`TauCeti.torusFamilyAffineMulAction` with trivial linear part and translation section
`TauCeti.logTranslationSection`. -/
@[expose, instance_reducible]
noncomputable def logTranslationMulAction :
    letI := periodAddAction (powPullbackPeriod m r P)
    MulAction (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :=
  torusFamilyAffineMulAction (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
    (powPullbackPeriod m r P) (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ)
    (powPullbackPeriod_smul_apply P) (logTranslationSection P l)
    (torusFamilyProjection_logTranslationSection P l) (logTranslationSection_one P l)
    (logTranslationSection_mul P l)

/-- The normalized action on representatives, with any logarithm `L` of `ζ`. -/
theorem logTranslationMulAction_smul_mk_of_exp_eq {ζ : rootsOfUnity m ℂ} {L : ℂ}
    (hL : exp L = ((ζ : ℂˣ) : ℂ)) (z : rootsOfUnityBall m r) (e : E) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ζ • (Quotient.mk _ (z, e) : AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) =
      Quotient.mk _ (ζ • z, e + (L / (2 * π * I)) • P (rootsOfUnityBall.powMap m r z) l) := by
  rw [logTranslationMulAction, torusFamilyAffineMulAction_smul,
    torusFamilyAffineMap_mk_of_eq _ _ _ _ _ _ (logTranslationSection_eq_mk_of_exp_eq P l hL z),
    AddMonoidHom.id_apply, powPullbackPeriod_apply]

/-- The normalized action on representatives, with the principal logarithm of `ζ`. -/
theorem logTranslationMulAction_smul_mk (ζ : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r)
    (e : E) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ζ • (Quotient.mk _ (z, e) : AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) =
      Quotient.mk _ (ζ • z, e + (log ((ζ : ℂˣ) : ℂ) / (2 * π * I)) •
        P (rootsOfUnityBall.powMap m r z) l) :=
  logTranslationMulAction_smul_mk_of_exp_eq P l (exp_log (ζ : ℂˣ).ne_zero) z e

/-- **The generator.** The rotation by `ζ = exp (2πi / m)` acts by the normalized translation
`[z, e] ↦ [ζ z, e + (1 / m) • P (z ^ m) l]`, the normal form produced by cyclic averaging
(`TauCeti.exists_torusFamilyGaugeDiffeomorph_cyclic_normalization`). -/
theorem logTranslationMulAction_smul_mk_of_exp_two_pi_I_div_eq {ζ : rootsOfUnity m ℂ}
    (hζ : exp (2 * π * I / m) = ((ζ : ℂˣ) : ℂ)) (z : rootsOfUnityBall m r) (e : E) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ζ • (Quotient.mk _ (z, e) : AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) =
      Quotient.mk _ (ζ • z, e + (m : ℂ)⁻¹ • P (rootsOfUnityBall.powMap m r z) l) := by
  rw [logTranslationMulAction_smul_mk_of_exp_eq P l hζ, div_div_cancel_left' two_pi_I_ne_zero]

/-! ### The logarithmic gauge -/

/-- **The logarithmic gauge** `[z, e] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` from the
pulled-back family `X` to the family `Y`. It is meaningful over `z ≠ 0`, where it does not depend
on the branch of the logarithm (`TauCeti.torusFamilyLogGauge_mk_of_exp_eq`) and is invariant
under the normalized action (`TauCeti.torusFamilyLogGauge_smul`); over `z = 0` it uses
`log 0 = 0`. -/
noncomputable def torusFamilyLogGauge :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E) →
      AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E) :=
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := periodAddAction P
  Quotient.lift (fun p ↦ Quotient.mk _ (rootsOfUnityBall.powMap m r p.1,
      p.2 - (log (p.1 : ℂ) / (2 * π * I)) • P (rootsOfUnityBall.powMap m r p.1) l))
    fun p q hpq ↦ by
      obtain ⟨h1, h2⟩ := (mem_orbit_periodAddAction_iff _).1 (AddAction.orbitRel_apply.1 hpq)
      rw [Quotient.eq, AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff]
      refine ⟨by rw [h1], ?_⟩
      rw [h1, sub_sub_sub_cancel_right]
      exact h2

/-- The logarithmic gauge on representatives, with the principal logarithm. -/
@[simp] theorem torusFamilyLogGauge_mk (z : rootsOfUnityBall m r) (e : E) :
    letI := periodAddAction (powPullbackPeriod m r P)
    torusFamilyLogGauge P l (Quotient.mk _ (z, e)) =
      Quotient.mk _ (rootsOfUnityBall.powMap m r z,
        e - (log (z : ℂ) / (2 * π * I)) • P (rootsOfUnityBall.powMap m r z) l) := (rfl)

/-- The logarithmic gauge lies over the power map `z ↦ z ^ m`. -/
@[simp] theorem torusFamilyProjection_torusFamilyLogGauge
    (x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
    torusFamilyProjection P (torusFamilyLogGauge P l x) =
      rootsOfUnityBall.powMap m r (torusFamilyProjection (powPullbackPeriod m r P) x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨z, e⟩ := p
    rw [torusFamilyLogGauge_mk, torusFamilyProjection_mk, torusFamilyProjection_mk]

/-- **Independence of the branch.** Over `z ≠ 0`, the logarithmic gauge may be computed with any
logarithm `L` of `z`: two branches differ by `2πi k`, which changes the result by the period
`k • P (z ^ m) l`. -/
theorem torusFamilyLogGauge_mk_of_exp_eq {z : rootsOfUnityBall m r} {L : ℂ}
    (hL : exp L = (z : ℂ)) (e : E) :
    letI := periodAddAction (powPullbackPeriod m r P)
    torusFamilyLogGauge P l (Quotient.mk _ (z, e)) =
      Quotient.mk _ (rootsOfUnityBall.powMap m r z,
        e - (L / (2 * π * I)) • P (rootsOfUnityBall.powMap m r z) l) := by
  let _ := periodAddAction P
  have hz : (z : ℂ) ≠ 0 := hL ▸ exp_ne_zero L
  obtain ⟨k, hk⟩ := exists_div_two_pi_I_smul_eq_add_zsmul (hL.trans (exp_log hz).symm)
    (P (rootsOfUnityBall.powMap m r z) l)
  rw [torusFamilyLogGauge_mk, Quotient.eq, AddAction.orbitRel_apply,
    mem_orbit_periodAddAction_iff]
  refine ⟨rfl, k • l, ?_⟩
  rw [hk, map_zsmul, sub_sub_sub_cancel_left, add_sub_cancel_left]

/-- **Cyclic invariance.** Over `z ≠ 0` the logarithmic gauge is invariant under the normalized
action: rotating `z` by `ζ` adds `log ζ` to a logarithm of `z`, which cancels the translation. -/
theorem torusFamilyLogGauge_smul (ζ : rootsOfUnity m ℂ)
    {x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)}
    (hx : ((torusFamilyProjection (powPullbackPeriod m r P) x : rootsOfUnityBall m r) : ℂ) ≠ 0) :
    letI := logTranslationMulAction P l
    torusFamilyLogGauge P l (ζ • x) = torusFamilyLogGauge P l x := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨z, e⟩ := p
    have hz : (z : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at hx
    have hL : exp (log ((ζ : ℂˣ) : ℂ) + log (z : ℂ)) = ((ζ • z : rootsOfUnityBall m r) : ℂ) := by
      rw [Complex.exp_add, exp_log (ζ : ℂˣ).ne_zero, exp_log hz, SubMulAction.val_smul,
        rootsOfUnity.smul_eq_mul]
    rw [logTranslationMulAction_smul_mk, torusFamilyLogGauge_mk_of_exp_eq P l hL,
      torusFamilyLogGauge_mk, rootsOfUnityBall.powMap_smul, add_div, add_smul]
    congr 2
    abel

/-! ### The equivalence of the punctured cyclic quotient with the punctured family -/

/-- Two logarithms of the same number give the same point when used as translation coefficients
of a period, since they differ by `2πi k`. -/
private theorem mk_add_smul_eq_of_exp_eq {Y : Type*} (P' : Y → Λ →ₗ[ℤ] E) {a b : ℂ}
    (h : exp a = exp b) (y : Y) (e : E) :
    letI := periodAddAction P'
    (Quotient.mk _ (y, e + (a / (2 * π * I)) • P' y l) :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      Quotient.mk _ (y, e + (b / (2 * π * I)) • P' y l) := by
  let _ := periodAddAction P'
  obtain ⟨k, hk⟩ := exists_div_two_pi_I_smul_eq_add_zsmul h (P' y l)
  rw [Quotient.eq, AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff]
  refine ⟨rfl, k • l, ?_⟩
  rw [hk, map_zsmul, ← add_assoc, add_sub_cancel_left]

variable {P l} in
/-- On the punctured part, the logarithmic gauge of any representative of an orbit is the same. -/
private theorem torusFamilyLogGauge_out
    {x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)}
    (hx : ((torusFamilyProjection (powPullbackPeriod m r P) x : rootsOfUnityBall m r) : ℂ) ≠ 0) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    torusFamilyLogGauge P l
        (Quotient.out (Quotient.mk _ x : orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) =
      torusFamilyLogGauge P l x := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  obtain ⟨ζ, hζ⟩ := orbitRel_apply.1 (Quotient.mk_out (s := orbitRel (rootsOfUnity m ℂ) _) x)
  rw [← hζ, torusFamilyLogGauge_smul P l ζ hx]

variable (hr : 0 ≤ r)

/-- The inverse of the logarithmic gauge on representatives, `[t, e] ↦ [[z, e + (log z / 2πi) •
P t l]]` with `z` the principal `m`-th root of `t`. Over `t ≠ 0` any root and any logarithm may
be used instead (`TauCeti.torusFamilyLogGaugeEquiv_symm_mk`). -/
private noncomputable def torusFamilyLogGaugeInv :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E) →
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :=
  letI := periodAddAction P
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := logTranslationMulAction P l
  Quotient.lift (fun p ↦ Quotient.mk _ (Quotient.mk _ (rootsOfUnityBall.rootMap hr p.1,
      p.2 + (log (rootsOfUnityBall.rootMap hr p.1 : ℂ) / (2 * π * I)) • P p.1 l)))
    fun p q hpq ↦ by
      obtain ⟨h1, h2⟩ := (mem_orbit_periodAddAction_iff _).1 (AddAction.orbitRel_apply.1 hpq)
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      obtain rfl : p1 = q1 := h1
      congr 1
      rw [Quotient.eq, AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff]
      refine ⟨rfl, ?_⟩
      rw [add_sub_add_right_eq_sub, powPullbackPeriod_apply, rootsOfUnityBall.powMap_rootMap]
      exact h2

private theorem torusFamilyLogGaugeInv_mk (t : Metric.ball (0 : ℂ) (r ^ m)) (e : E) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    torusFamilyLogGaugeInv P l hr (Quotient.mk _ (t, e)) =
      Quotient.mk _ (Quotient.mk _ (rootsOfUnityBall.rootMap hr t,
        e + (log (rootsOfUnityBall.rootMap hr t : ℂ) / (2 * π * I)) • P t l)) := (rfl)

/-- **Independence of root and branch.** The inverse formula may use any `m`-th root `z` of
`t ≠ 0` and any logarithm `L` of `z`. -/
private theorem torusFamilyLogGaugeInv_mk_of_exp_eq {t : Metric.ball (0 : ℂ) (r ^ m)}
    {z : rootsOfUnityBall m r} (hz : rootsOfUnityBall.powMap m r z = t) {L : ℂ}
    (hL : exp L = (z : ℂ)) (e : E) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    torusFamilyLogGaugeInv P l hr (Quotient.mk _ (t, e)) =
      Quotient.mk _ (Quotient.mk _ (z, e + (L / (2 * π * I)) • P t l)) := by
  let _ := periodAddAction P
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  set z' := rootsOfUnityBall.rootMap hr t
  have hz0 : (z : ℂ) ≠ 0 := hL ▸ exp_ne_zero L
  have hpow : (z' : ℂ) ^ m = (z : ℂ) ^ m := by
    rw [← rootsOfUnityBall.coe_powMap, ← rootsOfUnityBall.coe_powMap, hz,
      rootsOfUnityBall.powMap_rootMap]
  have hz'0 : (z' : ℂ) ≠ 0 := fun h ↦ hz0 (pow_eq_zero_iff (NeZero.ne m) |>.1
    (hpow ▸ by rw [h, zero_pow (NeZero.ne m)]))
  obtain ⟨ζ, hζ⟩ := (pow_eq_pow_iff_exists_rootsOfUnity_smul (NeZero.ne m)).1 hpow
  have hζz : ζ • z' = z := Subtype.ext (by rw [SubMulAction.val_smul, hζ])
  have hexp : exp (log ((ζ : ℂˣ) : ℂ) + log (z' : ℂ)) = exp L := by
    rw [Complex.exp_add, exp_log (ζ : ℂˣ).ne_zero, exp_log hz'0, hL, ← hζ,
      rootsOfUnity.smul_eq_mul]
  symm
  refine Quotient.sound ⟨ζ, ?_⟩
  dsimp only
  rw [logTranslationMulAction_smul_mk, hζz, rootsOfUnityBall.powMap_rootMap, add_assoc,
    ← add_smul, ← add_div, add_comm (log (z' : ℂ)), ← hz, ← powPullbackPeriod_apply P,
    mk_add_smul_eq_of_exp_eq l _ hexp]

private theorem torusFamilyCyclicQuotientProjection_torusFamilyLogGaugeInv
    (y : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)) :
    torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_one P l) (logTranslationSection_mul P l)
        (torusFamilyLogGaugeInv P l hr y) =
      ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) := by
  induction y using Quotient.inductionOn with
  | h p =>
    obtain ⟨t, e⟩ := p
    rw [torusFamilyLogGaugeInv_mk, torusFamilyCyclicQuotientProjection_mk,
      torusFamilyProjection_mk, torusFamilyProjection_mk, ← rootsOfUnityBall.coe_powMap,
      rootsOfUnityBall.powMap_rootMap]

/-- **The logarithmic gauge** of the cyclic quotient. Let `Q = X / C_m` be the orbit space of the
normalized pure translation action `TauCeti.logTranslationMulAction` on the family `X` pulled back
along `z ↦ z ^ m`, with coordinate `t = z ^ m`. Over the punctured disc `t ≠ 0`, the map
`[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` is an equivalence onto the punctured
family `Y* = {t ≠ 0}` (`TauCeti.torusFamilyLogGaugeEquiv_mk`); it lies over the identity of the
punctured disc (`TauCeti.coe_torusFamilyProjection_torusFamilyLogGaugeEquiv`), and its inverse
sends `[t, e]` to `[[z, e + (log z / 2πi) • P t l]]` for any root `z ^ m = t` and any branch of
the logarithm (`TauCeti.torusFamilyLogGaugeEquiv_symm_mk`). -/
noncomputable def torusFamilyLogGaugeEquiv :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    {q : orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) //
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_one P l) (logTranslationSection_mul P l) q ≠ 0} ≃
      {y : AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E) //
        ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0} :=
  letI := periodAddAction P
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := logTranslationMulAction P l
  { toFun q := ⟨torusFamilyLogGauge P l q.1.out, by
      have h := q.2
      rw [← Quotient.out_eq q.1, torusFamilyCyclicQuotientProjection_mk] at h
      rwa [torusFamilyProjection_torusFamilyLogGauge, rootsOfUnityBall.coe_powMap]⟩
    invFun y := ⟨torusFamilyLogGaugeInv P l hr y.1, by
      rw [torusFamilyCyclicQuotientProjection_torusFamilyLogGaugeInv]
      exact y.2⟩
    left_inv q := by
      obtain ⟨q, hq⟩ := q
      induction q using Quotient.inductionOn with
      | h x =>
        induction x using Quotient.inductionOn with
        | h p =>
          obtain ⟨z, e⟩ := p
          have hz : (z : ℂ) ≠ 0 := by
            rw [torusFamilyCyclicQuotientProjection_mk, torusFamilyProjection_mk] at hq
            exact fun h ↦ hq (by rw [h, zero_pow (NeZero.ne m)])
          apply Subtype.ext
          simp only
          rw [torusFamilyLogGauge_out (by rwa [torusFamilyProjection_mk]),
            torusFamilyLogGauge_mk, torusFamilyLogGaugeInv_mk_of_exp_eq P l hr rfl (exp_log hz),
            sub_add_cancel]
    right_inv y := by
      obtain ⟨y, hy⟩ := y
      induction y using Quotient.inductionOn with
      | h p =>
        obtain ⟨t, e⟩ := p
        have hz : (rootsOfUnityBall.rootMap hr t : ℂ) ≠ 0 := by
          rw [torusFamilyProjection_mk] at hy
          intro h
          apply hy
          rw [← rootsOfUnityBall.powMap_rootMap hr t, rootsOfUnityBall.coe_powMap, h,
            zero_pow (NeZero.ne m)]
        apply Subtype.ext
        simp only
        rw [torusFamilyLogGaugeInv_mk_of_exp_eq P l hr (rootsOfUnityBall.powMap_rootMap hr t)
            (exp_log hz), torusFamilyLogGauge_out (by rwa [torusFamilyProjection_mk]),
          torusFamilyLogGauge_mk, rootsOfUnityBall.powMap_rootMap, add_sub_cancel_right] }

/-- The logarithmic gauge on the class of a point over `z ≠ 0`. -/
theorem torusFamilyLogGaugeEquiv_mk
    (x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) (hx) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    (torusFamilyLogGaugeEquiv P l hr ⟨Quotient.mk _ x, hx⟩ :
        AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)) =
      torusFamilyLogGauge P l x := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  refine torusFamilyLogGauge_out fun h ↦ hx ?_
  rw [torusFamilyCyclicQuotientProjection_mk, h, zero_pow (NeZero.ne m)]

/-- **The inverse of the logarithmic gauge**, with any root and branch: if `z ^ m = t` and
`exp L = z`, it sends `[t, e]` to the class of `[z, e + (L / 2πi) • P t l]`. -/
theorem torusFamilyLogGaugeEquiv_symm_mk {t : Metric.ball (0 : ℂ) (r ^ m)}
    {z : rootsOfUnityBall m r} (hz : rootsOfUnityBall.powMap m r z = t) {L : ℂ}
    (hL : exp L = (z : ℂ)) (e : E) (ht) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ((torusFamilyLogGaugeEquiv P l hr).symm ⟨Quotient.mk _ (t, e), ht⟩ :
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) =
      Quotient.mk _ (Quotient.mk _ (z, e + (L / (2 * π * I)) • P t l)) :=
  torusFamilyLogGaugeInv_mk_of_exp_eq P l hr hz hL e

/-- The logarithmic gauge lies over the identity of the punctured disc: the image of a point of
`Q` with coordinate `t` lies over `t`. -/
theorem coe_torusFamilyProjection_torusFamilyLogGaugeEquiv (q) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ((torusFamilyProjection P (torusFamilyLogGaugeEquiv P l hr q).1 :
      Metric.ball (0 : ℂ) (r ^ m)) : ℂ) =
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_one P l) (logTranslationSection_mul P l) q.1 := by
  obtain ⟨q, hq⟩ := (torusFamilyLogGaugeEquiv P l hr).symm.surjective q
  rw [← hq, Equiv.apply_symm_apply]
  exact (torusFamilyCyclicQuotientProjection_torusFamilyLogGaugeInv P l hr q.1).symm

/-! ### The logarithmic gauge is a homeomorphism -/

section Topology

/-- A branch of the `m`-th root near `z₀ ^ m`: `exp (log z₀ + (1 / m) log (t / z₀ ^ m))` is an
`m`-th root of every `t ≠ 0`. -/
private theorem exp_log_add_inv_mul_log_div_pow {z₀ t : ℂ} (hz₀ : z₀ ≠ 0) (ht : t ≠ 0) :
    exp (log z₀ + (m : ℂ)⁻¹ * log (t / z₀ ^ m)) ^ m = t := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  rw [← Complex.exp_nat_mul, mul_add, ← mul_assoc, mul_inv_cancel₀ hm, one_mul, Complex.exp_add,
    Complex.exp_nat_mul, exp_log hz₀, exp_log (div_ne_zero ht (pow_ne_zero m hz₀)),
    mul_div_cancel₀ _ (pow_ne_zero m hz₀)]

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  (hcont : ∀ l', Continuous fun t ↦ P t l')

include hcont in
/-- The orbit map `D_z × E → Q` of the cyclic quotient is an open quotient map. -/
private theorem isOpenQuotientMap_logTranslationQuotient_mk :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    IsOpenQuotientMap (fun p : rootsOfUnityBall m r × E ↦
      (Quotient.mk _ (Quotient.mk _ p : AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  have hcontX : ∀ l', Continuous fun z ↦ powPullbackPeriod m r P z l' :=
    fun l' ↦ (hcont l').comp rootsOfUnityBall.continuous_powMap
  have := continuousConstVAdd_periodAddAction _ hcontX
  have hb : ∀ ζ, Continuous (logTranslationSection P l ζ) := fun ζ ↦
    continuous_quotient_mk'.comp ((continuous_const_smul ζ).prodMk
      (continuous_const.smul (hcontX l)))
  have : ContinuousConstSMul (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :=
    continuousConstSMul_torusFamilyAffineMulAction (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) _ _ (powPullbackPeriod_smul_apply P) (logTranslationSection P l)
      (torusFamilyProjection_logTranslationSection P l) (logTranslationSection_one P l)
      (logTranslationSection_mul P l) hcontX (fun _ ↦ continuous_snd) hb
  exact MulAction.isOpenQuotientMap_quotientMk.comp AddAction.isOpenQuotientMap_quotientMk

include hcont in
/-- The logarithmic gauge is continuous on the punctured part of the cyclic quotient. Near a
point over `z₀ ≠ 0` it is computed with the continuous branch `log z₀ + log (z / z₀)`. -/
private theorem continuousAt_torusFamilyLogGauge_out
    {q₀ : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))}
    (hq₀ : torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_one P l) (logTranslationSection_mul P l) q₀ ≠ 0) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ContinuousAt (fun q ↦ torusFamilyLogGauge P l (Quotient.out q)) q₀ := by
  let _ := periodAddAction P
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  have hΨ := isOpenQuotientMap_logTranslationQuotient_mk P l hcont
  obtain ⟨⟨z₀, e₀⟩, rfl⟩ := hΨ.surjective q₀
  rw [← hΨ.continuousAt_comp_iff]
  have hz₀ : (z₀ : ℂ) ≠ 0 := by
    intro h
    apply hq₀
    rw [torusFamilyCyclicQuotientProjection_mk, torusFamilyProjection_mk, h,
      zero_pow (NeZero.ne m)]
  -- Near `z₀`, use the continuous branch `L z = log z₀ + log (z / z₀)` of the logarithm.
  let L : ℂ → ℂ := fun z ↦ log z₀ + log (z / z₀)
  have hL {z : ℂ} (hz : z ≠ 0) : exp (L z) = z := by
    simp only [L]
    rw [Complex.exp_add, exp_log hz₀, exp_log (div_ne_zero hz hz₀), mul_div_cancel₀ _ hz₀]
  have hopen : IsOpen {p : rootsOfUnityBall m r × E | (p.1 : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
  refine ContinuousAt.congr_of_eventuallyEq (f := fun p ↦ Quotient.mk _
      (rootsOfUnityBall.powMap m r p.1,
        p.2 - (L p.1 / (2 * π * I)) • P (rootsOfUnityBall.powMap m r p.1) l)) ?_ ?_
  · have hLc : ContinuousAt (fun p : rootsOfUnityBall m r × E ↦ L p.1) (z₀, e₀) :=
      continuousAt_const.add (((continuous_subtype_val.comp continuous_fst).div_const _
        ).continuousAt.clog (by
          simp only [Function.comp_apply, div_self hz₀]
          exact one_mem_slitPlane))
    have hpow := rootsOfUnityBall.continuous_powMap (m := m) (r := r)
    exact continuous_quotient_mk'.continuousAt.comp ((hpow.comp continuous_fst).continuousAt.prodMk
      (continuousAt_snd.sub ((hLc.div_const _).smul
        ((hcont l).comp (hpow.comp continuous_fst)).continuousAt)))
  · filter_upwards [hopen.mem_nhds hz₀] with p hp
    obtain ⟨z, e⟩ := p
    rw [Function.comp_apply, torusFamilyLogGauge_out (by rwa [torusFamilyProjection_mk]),
      torusFamilyLogGauge_mk_of_exp_eq P l (hL hp)]

include hcont in
/-- The inverse of the logarithmic gauge is continuous on the punctured family. Near `t₀ ≠ 0`
it is computed with the continuous branch `log z₀ + (1 / m) log (t / t₀)` of the logarithm of an
`m`-th root, for a root `z₀` of `t₀`. -/
private theorem continuousAt_torusFamilyLogGaugeInv
    {y₀ : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)}
    (hy₀ : ((torusFamilyProjection P y₀ : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0) :
    ContinuousAt (torusFamilyLogGaugeInv P l hr) y₀ := by
  let _ := periodAddAction P
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  have := continuousConstVAdd_periodAddAction P hcont
  have hq : IsOpenQuotientMap (Quotient.mk _ :
      Metric.ball (0 : ℂ) (r ^ m) × E →
        AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)) :=
    AddAction.isOpenQuotientMap_quotientMk
  obtain ⟨⟨t₀, e₀⟩, rfl⟩ := hq.surjective y₀
  rw [← hq.continuousAt_comp_iff]
  have ht₀ : (t₀ : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at hy₀
  set z₀ := rootsOfUnityBall.rootMap hr t₀
  have hz₀m : (z₀ : ℂ) ^ m = t₀ := by
    rw [← rootsOfUnityBall.coe_powMap, rootsOfUnityBall.powMap_rootMap]
  have hz₀ : (z₀ : ℂ) ≠ 0 := fun h ↦ ht₀ (by rw [← hz₀m, h, zero_pow (NeZero.ne m)])
  -- Near `t₀`, use the continuous branch `L t` of the logarithm of an `m`-th root of `t`.
  let L : ℂ → ℂ := fun t ↦ log z₀ + (m : ℂ)⁻¹ * log (t / (z₀ : ℂ) ^ m)
  have hmem (t : Metric.ball (0 : ℂ) (r ^ m)) : exp (L t) ∈ rootsOfUnityBall m r := by
    by_cases ht : (t : ℂ) = 0
    · simp only [L, ht, zero_div, log_zero, mul_zero, add_zero, exp_log hz₀]
      exact z₀.2
    · rw [mem_rootsOfUnityBall, ← pow_lt_pow_iff_left₀ (norm_nonneg _) hr (NeZero.ne m),
        ← norm_pow, exp_log_add_inv_mul_log_div_pow hz₀ ht, ← mem_ball_zero_iff]
      exact t.2
  let w : Metric.ball (0 : ℂ) (r ^ m) → rootsOfUnityBall m r := fun t ↦ ⟨exp (L t), hmem t⟩
  have hw {t : Metric.ball (0 : ℂ) (r ^ m)} (ht : (t : ℂ) ≠ 0) :
      rootsOfUnityBall.powMap m r (w t) = t :=
    Subtype.ext (by rw [rootsOfUnityBall.coe_powMap]; exact exp_log_add_inv_mul_log_div_pow hz₀ ht)
  have hopen : IsOpen {p : Metric.ball (0 : ℂ) (r ^ m) × E | (p.1 : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
  have hΨ := isOpenQuotientMap_logTranslationQuotient_mk P l hcont
  refine ContinuousAt.congr_of_eventuallyEq (f := fun p ↦ Quotient.mk _ (Quotient.mk _
      (w p.1, p.2 + (L p.1 / (2 * π * I)) • P p.1 l))) ?_ ?_
  · have hLc : ContinuousAt (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦ L p.1) (t₀, e₀) :=
      continuousAt_const.add (continuousAt_const.mul
        (((continuous_subtype_val.comp continuous_fst).div_const _).continuousAt.clog
          (by simp only [Function.comp_apply, hz₀m, div_self ht₀]; exact one_mem_slitPlane)))
    have hwc : ContinuousAt (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦ w p.1) (t₀, e₀) :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.2 hLc.cexp
    exact hΨ.continuous.continuousAt.comp (hwc.prodMk (continuousAt_snd.add
      ((hLc.div_const _).smul ((hcont l).comp continuous_fst).continuousAt)))
  · filter_upwards [hopen.mem_nhds ht₀] with p hp
    obtain ⟨t, e⟩ := p
    exact torusFamilyLogGaugeInv_mk_of_exp_eq P l hr (hw hp) rfl e

include hcont in
private theorem continuous_torusFamilyLogGaugeEquiv :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    Continuous (torusFamilyLogGaugeEquiv P l hr) := by
  let _ := periodAddAction P
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  refine continuous_induced_rng.2
    (continuous_iff_continuousAt.2 fun q ↦ ?_)
  exact (continuousAt_torusFamilyLogGauge_out P l hcont q.2).comp continuousAt_subtype_val

include hcont in
private theorem continuous_torusFamilyLogGaugeEquiv_symm :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    Continuous (torusFamilyLogGaugeEquiv P l hr).symm := by
  let _ := periodAddAction P
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  refine continuous_induced_rng.2
    (continuous_iff_continuousAt.2 fun y ↦ ?_)
  exact (continuousAt_torusFamilyLogGaugeInv P l hr hcont y.2).comp continuousAt_subtype_val

include hcont in
/-- **The logarithmic gauge as a homeomorphism.** For continuous periods, the equivalence
`TauCeti.torusFamilyLogGaugeEquiv` between the punctured cyclic quotient `Q*` and the punctured
family `Y*` is a homeomorphism. -/
noncomputable def torusFamilyLogGaugeHomeomorph :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    {q : orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) //
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_one P l) (logTranslationSection_mul P l) q ≠ 0} ≃ₜ
      {y : AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E) //
        ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0} :=
  letI := periodAddAction P
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := logTranslationMulAction P l
  { toEquiv := torusFamilyLogGaugeEquiv P l hr
    continuous_toFun := continuous_torusFamilyLogGaugeEquiv P l hr hcont
    continuous_invFun := continuous_torusFamilyLogGaugeEquiv_symm P l hr hcont }

/-- The homeomorphism has the underlying equivalence `TauCeti.torusFamilyLogGaugeEquiv`. -/
@[simp] theorem torusFamilyLogGaugeHomeomorph_toEquiv :
    (torusFamilyLogGaugeHomeomorph P l hr hcont).toEquiv = torusFamilyLogGaugeEquiv P l hr :=
  (rfl)

@[simp] theorem coe_torusFamilyLogGaugeHomeomorph :
    ⇑(torusFamilyLogGaugeHomeomorph P l hr hcont) = torusFamilyLogGaugeEquiv P l hr :=
  (rfl)

@[simp] theorem coe_torusFamilyLogGaugeHomeomorph_symm :
    ⇑(torusFamilyLogGaugeHomeomorph P l hr hcont).symm = (torusFamilyLogGaugeEquiv P l hr).symm :=
  (rfl)

end Topology

end TauCeti
