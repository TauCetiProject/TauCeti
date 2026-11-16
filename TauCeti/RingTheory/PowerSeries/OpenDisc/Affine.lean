/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.AnalyticSubst
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Affine changes of coordinates on open discs

Over a complete ultrametric commutative normed ring `R`, an interior centre `a` (`‖a‖ < R₀`) and a
scaling factor `u` (`‖u‖ * S₀ ≤ R₀`) define the affine coordinate change `f(X) ↦ f(a + u X)` from
series on the open disc of radius `R₀` to series on the open disc of radius `S₀`, obtained by
composing Taylor translation (`TauCeti.PowerSeries.OnOpenDisc.taylorHom`) with variable rescaling
(`TauCeti.PowerSeries.OnOpenDisc.rescaleHom`).

On smaller closed discs, `affineHom` satisfies `‖restrict s (affineHom ha u hu f)‖ ≤ ‖restrict r f‖`
whenever `‖a‖ ≤ r` and `‖u‖ * s ≤ r`, without assuming `‖1‖ = 1`, and is therefore continuous for
the open-disc Gauss topologies. When `0 < S₀`, `affineHom` agrees with analytic substitution
(`TauCeti.PowerSeries.OnOpenDisc.analyticSubst`) by the linear polynomial `a + u X`, specializing to
`rescaleHom` (for `0 < R₀`) and, when additionally `‖1‖ = 1`, to `taylorHom`. When `u` is a
multiplicative unit with `‖u‖ * S₀ = R₀`, composing `taylorEquiv` and `rescaleEquiv` upgrades
`affineHom` to a ring isomorphism (`affineEquiv`) and, for `0 < S₀`, a homeomorphism
(`affineHomeomorph`) of open-disc algebras.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.affineHom`: the continuous ring homomorphism `f(X) ↦ f(a + u X)`
  from `OnOpenDisc.subring R R₀` to `OnOpenDisc.subring R S₀`.
* `TauCeti.PowerSeries.OnOpenDisc.affineEquiv` and
  `TauCeti.PowerSeries.OnOpenDisc.affineHomeomorph`: the ring equivalence and homeomorphism induced
  when `u` is a multiplicative unit with `‖u‖ * S₀ = R₀`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_affineHom_le` and
  `TauCeti.PowerSeries.OnOpenDisc.continuous_affineHom`: closed-disc Gauss-norm bounds and
  continuity.
* `TauCeti.PowerSeries.OnOpenDisc.affineHom_eq_analyticSubst`,
  `TauCeti.PowerSeries.OnOpenDisc.taylorHom_eq_analyticSubst`, and
  `TauCeti.PowerSeries.OnOpenDisc.rescaleHom_eq_analyticSubst`: identification with analytic
  substitution.
* `TauCeti.PowerSeries.OnOpenDisc.affineHom_comp_affineHom`,
  `TauCeti.PowerSeries.OnOpenDisc.evalAt_affineHom`,
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_affineHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.derivative_affineHom`: composition, point evaluation, Hasse
  derivatives, and ordinary derivatives under affine coordinate changes.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S₀ T₀ : ℝ} {a b : R}

attribute [local instance] radius_pos

/-- Affine coordinate change `f(X) ↦ f(a + u X)` from the open disc of radius `R₀` to the open disc
of radius `S₀`, defined as Taylor translation at `a` followed by rescaling by `u`. -/
noncomputable def affineHom (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀ :=
  (rescaleHom u hu).comp (taylorHom ha)

/-- On underlying formal power series, `affineHom` translates by `a` and then rescales by `u`. -/
@[simp]
theorem coe_affineHom (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    (affineHom ha u hu f : R⟦X⟧) = PowerSeries.rescale u (PowerSeries.taylor a (f : R⟦X⟧)) := by
  simp [affineHom]

/-- `affineHom` fixes constant series. -/
theorem affineHom_C (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (c : R) :
    affineHom ha u hu (OnOpenDisc.polynomialHom (Polynomial.C c)) =
      OnOpenDisc.polynomialHom (Polynomial.C c) := by
  simp [affineHom]

/-- `affineHom` sends `X` to the linear polynomial `a + u X`. -/
theorem affineHom_X (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineHom ha u hu (OnOpenDisc.polynomialHom Polynomial.X) =
      OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X) := by
  rw [affineHom, RingHom.comp_apply, taylorHom_polynomialHom, Polynomial.taylor_X, map_add,
    map_add, rescaleHom_X, rescaleHom_C, add_comm, ← map_add]

/-- On polynomials, `affineHom` substitutes the linear polynomial `a + u X` for `X`. -/
@[simp]
theorem affineHom_polynomialHom (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (p : Polynomial R) :
    affineHom ha u hu (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (p.comp (Polynomial.C a + Polynomial.C u * Polynomial.X)) := by
  have heq : (affineHom ha u hu).comp OnOpenDisc.polynomialHom =
      OnOpenDisc.polynomialHom.comp
        (Polynomial.compRingHom (Polynomial.C a + Polynomial.C u * Polynomial.X)) :=
    Polynomial.ringHom_ext (fun c ↦ by simp [affineHom_C]) (by simp [affineHom_X])
  simpa only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply] using
    RingHom.congr_fun heq p

/-- At centre `0`, `affineHom` specializes to `rescaleHom`. -/
@[simp]
theorem affineHom_zero_left [Fact (0 < R₀)] (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    affineHom (a := 0) (by simpa using (Fact.out : 0 < R₀)) u hu f = rescaleHom u hu f := by
  simp [affineHom]

/-- With unit scale `1`, `affineHom` specializes to `taylorHom`. -/
@[simp]
theorem affineHom_one_right (ha : ‖a‖ < R₀) (h1 : ‖(1 : R)‖ * R₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    affineHom ha 1 h1 f = taylorHom ha f := by
  simp [affineHom]

/-- On smaller closed discs, `affineHom` is bounded by any source closed-disc Gauss norm whose
radius bounds both `‖a‖` and `‖u‖ s`. No `NormOneClass` hypothesis is needed. -/
theorem norm_restrict_affineHom_le (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (har : ‖a‖ ≤ r) (husr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (affineHom ha u hu f)‖ ≤ ‖restrict r f‖ :=
  (norm_restrict_rescaleHom_le u hu s r husr (taylorHom ha f)).trans_eq
    (norm_restrict_taylorHom ha r har f)

/-- Affine coordinate changes are continuous for the open-disc Gauss topologies. -/
@[continuity]
theorem continuous_affineHom (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (affineHom ha u hu) := by
  have : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
  exact (continuous_rescaleHom u hu).comp (continuous_taylorHom ha)

omit [CompleteSpace R] in
/-- On every positive closed disc of radius `s < S₀`, the linear polynomial `a + u X` has Gauss norm
strictly less than `R₀` whenever `‖a‖ < R₀` and `‖u‖ * S₀ ≤ R₀`. -/
theorem norm_restrict_affinePoly_lt (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (OnOpenDisc.polynomialHom
      (Polynomial.C a + Polynomial.C u * Polynomial.X) : OnOpenDisc.subring R S₀)‖ < R₀ := by
  have hus : ‖u‖ * (s : ℝ) < R₀ :=
    TauCeti.norm_mul_lt_of_mul_le ((norm_nonneg a).trans_lt ha) s.2.2 hu
  refine (TauCeti.PowerSeries.norm_le_iff.mpr fun n ↦ ?_).trans_lt (max_lt ha hus)
  rw [coe_restrict, OnOpenDisc.coe_polynomialHom, Polynomial.coeff_coe]
  rcases n with _ | _ | n
  · simp
  · simp
  · simp [(norm_nonneg a).trans (le_max_left _ _)]

/-- For `0 < S₀`, `affineHom` agrees with analytic substitution by `a + u X`. -/
theorem affineHom_eq_analyticSubst [Fact (0 < S₀)] (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineHom ha u hu =
      analyticSubst (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))
        (norm_restrict_affinePoly_lt ha u hu) :=
  eq_analyticSubst _ _ (affineHom ha u hu) (continuous_affineHom ha u hu)
    (fun c ↦ by simp) (by simp)

/-- Over an ultrametric ring with `‖1‖ = 1`, Taylor translation on an open disc agrees with analytic
substitution by `X + a`. -/
theorem taylorHom_eq_analyticSubst [Fact (0 < R₀)] [NormOneClass R] (ha : ‖a‖ < R₀) :
    taylorHom ha =
      analyticSubst (OnOpenDisc.polynomialHom (Polynomial.X + Polynomial.C a))
        (fun s ↦ by
          simpa [add_comm] using
            norm_restrict_affinePoly_lt ha 1 (by simp) s) :=
  eq_analyticSubst _ _ (taylorHom ha) (continuous_taylorHom ha)
    (fun c ↦ by simp) (by simp [Polynomial.taylor_X])

/-- For positive radii `R₀` and `S₀`, variable rescaling agrees with analytic substitution by
`u X` without assuming `‖1‖ = 1`. -/
theorem rescaleHom_eq_analyticSubst [Fact (0 < R₀)] [Fact (0 < S₀)] (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    rescaleHom u hu =
      analyticSubst (OnOpenDisc.polynomialHom (Polynomial.C u * Polynomial.X))
        (fun s ↦ by
          simpa using
            norm_restrict_affinePoly_lt (a := (0 : R)) (by simpa using (Fact.out : 0 < R₀))
              u hu s) :=
  eq_analyticSubst _ _ (rescaleHom u hu) (continuous_rescaleHom u hu)
    (fun c ↦ by simp) (by simp)

/-- Affine coordinate changes compose according to `(a + u Y) ∘ (b + v X) = (a + u b) + (u v) X`. -/
theorem affineHom_comp_affineHom [Fact (0 < T₀)] (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (hb : ‖b‖ < S₀) (v : R) (hv : ‖v‖ * T₀ ≤ S₀)
    (hab : ‖a + u * b‖ < R₀) (huv : ‖u * v‖ * T₀ ≤ R₀) :
    (affineHom hb v hv).comp (affineHom ha u hu) = affineHom hab (u * v) huv := by
  refine ringHom_ext ((continuous_affineHom hb v hv).comp (continuous_affineHom ha u hu))
    (continuous_affineHom hab (u * v) huv) (fun c ↦ by simp) ?_
  simp only [RingHom.comp_apply, affineHom_X, map_add, map_mul, affineHom_C]
  rw [← map_mul, ← map_add, ← map_mul, ← map_add]
  simp only [map_add, map_mul]
  ring

/-- Evaluating `affineHom ha u hu f` at an algebra point `x` with `‖x‖ < S₀` evaluates `f` at
`u • x + algebraMap R A a`, even in a noncommutative complete ultrametric `R`-algebra. -/
theorem evalAt_affineHom {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] {x : A}
    (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (hx : ‖x‖ < S₀)
    (f : OnOpenDisc.subring R R₀) :
    (affineHom ha u hu f : R⟦X⟧).evalAt x = (f : R⟦X⟧).evalAt (u • x + algebraMap R A a) := by
  have hux : ‖u • x‖ < R₀ :=
    (norm_smul_le u x).trans_lt
      (TauCeti.norm_mul_lt_of_mul_le ((norm_nonneg a).trans_lt ha) hx hu)
  rw [affineHom, RingHom.comp_apply, evalAt_rescaleHom, evalAt_taylorHom ha hux]

/-- Hasse derivatives under an affine coordinate change satisfy
`D⁽ᵏ⁾ (f(a + u X)) = uᵏ · (D⁽ᵏ⁾ f)(a + u X)`. -/
theorem hasseDeriv_affineHom (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (k : ℕ)
    (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (affineHom ha u hu f) = u ^ k • affineHom ha u hu (hasseDeriv k f) := by
  simp only [affineHom, RingHom.comp_apply, hasseDeriv_rescaleHom, hasseDeriv_taylorHom]

/-- The ordinary derivative under an affine coordinate change satisfies
`(f(a + u X))' = u · f'(a + u X)`. -/
theorem derivative_affineHom (ha : ‖a‖ < R₀) (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    derivative (affineHom ha u hu f) = u • affineHom ha u hu (derivative f) := by
  simp only [affineHom, RingHom.comp_apply, derivative_rescaleHom, derivative_taylorHom]

/-- Invertible affine coordinate change `f(X) ↦ f(a + u X)` between open-disc algebras when `u` is a
multiplicative unit with `‖u‖ * S₀ = R₀`. -/
noncomputable def affineEquiv (ha : ‖a‖ < R₀) (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃+* OnOpenDisc.subring R S₀ :=
  (taylorEquiv ha).trans (rescaleEquiv u hu hrs)

/-- `affineEquiv` acts by `affineHom`. -/
@[simp]
theorem affineEquiv_apply (ha : ‖a‖ < R₀) (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R R₀) :
    affineEquiv ha u hu hrs f = affineHom ha (u : R) hrs.le f :=
  Subtype.ext (by simp [affineEquiv, affineHom])

/-- The inverse of `affineEquiv` rescales by `u⁻¹` and translates by `-a`. -/
@[simp]
theorem affineEquiv_symm_apply (ha : ‖a‖ < R₀) (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) (g : OnOpenDisc.subring R S₀) :
    (affineEquiv ha u hu hrs).symm g =
      taylorHom (a := -a) (by simpa using ha) ((rescaleEquiv u hu hrs).symm g) := by
  simp [affineEquiv]

/-- On smaller closed discs with `‖a‖ ≤ r` and `‖u‖ * s = r`, `affineEquiv` preserves Gauss
norms. -/
theorem norm_restrict_affineEquiv (ha : ‖a‖ < R₀) (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀)
    (har : ‖a‖ ≤ r) (hsr : ‖(u : R)‖ * s = r) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (affineEquiv ha u hu hrs f)‖ = ‖restrict r f‖ := by
  rw [affineEquiv, RingEquiv.trans_apply, taylorEquiv_apply]
  exact (norm_restrict_rescaleEquiv u hu hrs s r hsr (taylorHom ha f)).trans
    (norm_restrict_taylorHom ha r har f)

/-- For `0 < S₀`, an invertible affine coordinate change is a homeomorphism for the open-disc Gauss
topologies. -/
noncomputable def affineHomeomorph [Fact (0 < S₀)] (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : TauCeti.IsNormMulUnit (u : R)) (hrs : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ₜ OnOpenDisc.subring R S₀ where
  toEquiv := (affineEquiv ha u hu hrs).toEquiv
  continuous_toFun :=
    (continuous_affineHom ha (u : R) hrs.le).congr fun f ↦
      (affineEquiv_apply ha u hu hrs f).symm
  continuous_invFun := by
    let : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
    exact ((continuous_taylorHom (a := -a) (by simpa using ha)).comp
      (rescaleUniformEquiv u hu hrs).symm.continuous).congr fun g ↦ by
        simp [affineEquiv_symm_apply]

/-- `affineHomeomorph` agrees with `affineEquiv` on elements. -/
@[simp]
theorem affineHomeomorph_apply [Fact (0 < S₀)] (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : TauCeti.IsNormMulUnit (u : R)) (hrs : ‖(u : R)‖ * S₀ = R₀)
    (f : OnOpenDisc.subring R R₀) :
    affineHomeomorph ha u hu hrs f = affineEquiv ha u hu hrs f :=
  (rfl)

/-- The inverse of `affineHomeomorph` agrees with `(affineEquiv ha u hu hrs).symm`. -/
@[simp]
theorem affineHomeomorph_symm_apply [Fact (0 < S₀)] (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : TauCeti.IsNormMulUnit (u : R)) (hrs : ‖(u : R)‖ * S₀ = R₀)
    (g : OnOpenDisc.subring R S₀) :
    (affineHomeomorph ha u hu hrs).symm g = (affineEquiv ha u hu hrs).symm g :=
  (rfl)

end TauCeti.PowerSeries.OnOpenDisc
