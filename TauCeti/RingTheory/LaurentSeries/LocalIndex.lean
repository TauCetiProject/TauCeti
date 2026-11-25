/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Primitive
public import TauCeti.RingTheory.LaurentSeries.ResiduePairing
import Mathlib.Tactic.Ring

/-!
# Laurent germs with one logarithmic term and their alternating local index

Let `L` be a formal logarithm of the parameter `X`, so that `dL = dX / X`. A formal germ with at
most one logarithmic term is `F = f + a L` with `f` a Laurent series and `a` a constant. We
represent it by the pair `(f, a) : LaurentSeries V × V`; the multiplication of such germs is never
used, so the product module is the whole structure. Equality of germs is equality of both
components.

The differential of `f + a L` is `(f' + a X⁻¹) dX`, and `TauCeti.logLaurentDerivative` records its
coefficient. Its residue is the logarithmic coefficient `a`, so `F` has no logarithmic term
exactly when `dF` has residue zero. In characteristic zero every Laurent differential `w dX` has a
primitive in this space, with logarithmic coefficient the residue `w₋₁` of `w`; the primitive is
unique up to a constant, and the germs with zero differential are exactly the constants
`(c, 0)`. This last statement needs coefficients without additive torsion: over `ZMod 2` the germ
`X²` has zero differential.

For coefficients in a commutative ring `R`, the **alternating local index** of two such germs is
`B(f + a L, g + b L) = Res(f dg) + b Res(f dX / X) - a Res(g dX / X)`, where `Res(f dX / X)` is
the constant coefficient of `f`. It is the bilinear form `TauCeti.logLaurentIndex`. When the
first germ is a Laurent series it is the residue `Res(f dG)` of `f` against the differential of
the second, and it is alternating: `B(F, F) = 0`, so `B(F, G) = -B(G, F)`. These two properties
determine it (`TauCeti.eq_logLaurentIndex_of_isAlt`): the residue rule fixes every term except
`B(L, L)`, which alternation forces to vanish. In particular `B(1, L) = 1`, `B(L, 1) = -1` and
`B(X, X⁻¹) = -1`. Adding constants `A` and `B'` to the two germs changes the index by
`A Res(dG) - B' Res(dF)`, and the index commutes with extension of coefficients along a ring
homomorphism.

A formal substitution `X ↦ φ`, by a nonzero power series `φ` of order `n` with zero constant
coefficient, pulls `f + a L` back to `f (φ) + a Λ`, where `Λ` is a chosen logarithm of `φ`: a germ
with `φ dΛ = dφ`. In characteristic zero such a germ exists, and it is unique up to a constant
since `dΛ = dφ / φ`; the constant is the choice of a logarithm of the leading coefficient of `φ`.
Its logarithmic coefficient is `n`. The pullback satisfies the chain rule and multiplies the local
index by `n`, so formal coordinate changes preserve the index.

The local index is the double index of Besser at an end of an annulus or a puncture: summed over
the ends of a wide open, it computes the cup product of the de Rham classes of two forms from
their local primitives.

## Main definitions

* `TauCeti.logLaurentDerivative`: the differential `(f, a) ↦ f' + a X⁻¹`.
* `TauCeti.logLaurentPrimitive`: the normalized primitive `w ↦ (∫ w, w₋₁)` in characteristic
  zero.
* `TauCeti.logLaurentIndex`: the alternating local index, as a bilinear form.
* `TauCeti.logLaurentSubst`: the pullback along `X ↦ φ` sending `L` to a chosen germ `Λ`.

## Main results

* `TauCeti.coeff_neg_one_logLaurentDerivative`: `Res(dF)` is the logarithmic coefficient.
* `TauCeti.logLaurentDerivative_eq_zero_iff`: without additive torsion the kernel of the
  differential is the constants.
* `TauCeti.logLaurentDerivative_eq_iff`: all primitives of `w` are the normalized primitive plus
  a constant; in particular the differential is surjective
  (`TauCeti.logLaurentDerivative_surjective`).
* `TauCeti.logLaurentIndex_mk_zero_left`: the index of a Laurent series `f` against `G` is
  `Res(f dG)`.
* `TauCeti.logLaurentIndex_mk_zero_right`: the index of `F` against a Laurent series `g` is
  `-Res(g dF)`.
* `TauCeti.logLaurentIndex_self`, `TauCeti.logLaurentIndex_eq_neg_swap`: alternation and
  skew-symmetry.
* `TauCeti.eq_logLaurentIndex_of_isAlt`: uniqueness of an alternating bilinear form with the
  Laurent-first residue rule, and `TauCeti.eq_smul_logLaurentIndex_of_isAlt` for a scaled rule.
* `TauCeti.logLaurentIndex_add_single_zero`: the change of the index under adding constants.
* `TauCeti.map_logLaurentIndex`: compatibility with coefficient extension.
* `TauCeti.exists_mul_logLaurentDerivative_eq`: in characteristic zero every power series has a
  logarithm.
* `TauCeti.snd_eq_order_of_mul_logLaurentDerivative_eq`: the logarithmic coefficient of a
  logarithm of `φ` is the order of `φ`.
* `TauCeti.logLaurentDerivative_logLaurentSubst`: the chain rule `d(φ*F) = dF (φ) dφ`.
* `TauCeti.logLaurentIndex_logLaurentSubst`: `B(φ*F, φ*G) = n B(F, G)` for `φ` of order `n`.

## References

* A. Besser, *p-adic heights and Vologodsky integration*, arXiv:1711.06957,
  Definition 3.1, Definition 3.2 and Lemma 3.3.
* A. Besser and R. de Jeu, *The syntomic regulator for K₄ of curves*, Pacific J. Math. 260
  (2012), §7, Definition 7.1.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti

section Module

variable (R : Type*) {V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

/-- The differential of a formal germ `f + a L` with one logarithmic term, where `dL = dX / X`.
The pair `(f, a)` goes to `f' + a X⁻¹`, the coefficient of `dX`. -/
noncomputable def logLaurentDerivative : LaurentSeries V × V →ₗ[R] LaurentSeries V :=
  (LaurentSeries.derivative R).coprod (single.linearMap (-1))

variable {R}

theorem logLaurentDerivative_apply (F : LaurentSeries V × V) :
    logLaurentDerivative R F = LaurentSeries.derivative R F.1 + single (-1) F.2 := (rfl)

/-- A Laurent series without logarithmic term is differentiated as a Laurent series. -/
@[simp]
theorem logLaurentDerivative_mk_zero (f : LaurentSeries V) :
    logLaurentDerivative R (f, 0) = LaurentSeries.derivative R f := by
  simp [logLaurentDerivative_apply]

/-- The logarithmic germ `a L` has differential `a X⁻¹ dX`. -/
@[simp]
theorem logLaurentDerivative_zero_mk (a : V) :
    logLaurentDerivative R ((0 : LaurentSeries V), a) = single (-1) a := by
  simp [logLaurentDerivative_apply]

/-- **The residue of a differential is its logarithmic coefficient**: `Res(d(f + a L)) = a`. -/
@[simp]
theorem coeff_neg_one_logLaurentDerivative (F : LaurentSeries V × V) :
    (logLaurentDerivative R F).coeff (-1) = F.2 := by
  rw [logLaurentDerivative_apply, coeff_add, LaurentSeries.coeff_neg_one_derivative]
  simp

/-- Constants have zero differential, in every characteristic. -/
theorem logLaurentDerivative_single_zero (c : V) :
    logLaurentDerivative R (single 0 c, 0) = 0 := by
  ext n
  simp

/-- **The kernel of the differential.** Without additive torsion, for instance over a field of
characteristic zero, the germs `f + a L` with zero differential are exactly the constants. -/
theorem logLaurentDerivative_eq_zero_iff [IsAddTorsionFree V] {F : LaurentSeries V × V} :
    logLaurentDerivative R F = 0 ↔ ∃ c : V, F = (single 0 c, 0) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h₂ : F.2 = 0 := by
      simpa using congrArg (fun w : LaurentSeries V ↦ w.coeff (-1)) h
    have h₁ : LaurentSeries.derivative R F.1 = 0 := by
      simpa [logLaurentDerivative_apply, h₂] using h
    exact ⟨F.1.coeff 0, Prod.ext (LaurentSeries.derivative_eq_zero_iff_eq_single.mp h₁) h₂⟩
  · rintro ⟨c, rfl⟩
    exact logLaurentDerivative_single_zero c

variable [Module ℚ V]

variable (R) in
/-- The normalized primitive of a Laurent differential `w dX` among germs with one logarithmic
term: termwise integration with constant coefficient zero, plus `w₋₁ L`. -/
noncomputable def logLaurentPrimitive : LaurentSeries V →ₗ[R] LaurentSeries V × V :=
  (laurentSeriesPrimitive R).prod (coeff.linearMap (-1))

theorem logLaurentPrimitive_apply (w : LaurentSeries V) :
    logLaurentPrimitive R w = (laurentSeriesPrimitive R w, w.coeff (-1)) := (rfl)

/-- The Laurent part of the normalized primitive is the termwise integral. -/
@[simp]
theorem fst_logLaurentPrimitive (w : LaurentSeries V) :
    (logLaurentPrimitive R w).1 = laurentSeriesPrimitive R w := (rfl)

/-- The logarithmic coefficient of the normalized primitive of `w` is the residue of `w`. -/
@[simp]
theorem snd_logLaurentPrimitive (w : LaurentSeries V) :
    (logLaurentPrimitive R w).2 = w.coeff (-1) := (rfl)

/-- **Every Laurent differential has a primitive with one logarithmic term**: the differential
of the normalized primitive of `w` is `w`. -/
@[simp]
theorem logLaurentDerivative_logLaurentPrimitive (w : LaurentSeries V) :
    logLaurentDerivative R (logLaurentPrimitive R w) = w := by
  rw [logLaurentPrimitive_apply, logLaurentDerivative_apply, derivative_laurentSeriesPrimitive,
    sub_add_cancel]

/-- Taking the normalized primitive of a differential removes exactly the constant term. -/
theorem logLaurentPrimitive_logLaurentDerivative (F : LaurentSeries V × V) :
    logLaurentPrimitive R (logLaurentDerivative R F) = F - (single 0 (F.1.coeff 0), 0) := by
  refine Prod.ext ?_ (by simp)
  rw [logLaurentPrimitive_apply, logLaurentDerivative_apply, map_add,
    laurentSeriesPrimitive_derivative, laurentSeriesPrimitive_single]
  simp

/-- In characteristic zero the differential of germs with one logarithmic term is surjective
onto Laurent differentials. -/
theorem logLaurentDerivative_surjective :
    Function.Surjective (logLaurentDerivative R : LaurentSeries V × V → LaurentSeries V) :=
  fun w ↦ ⟨logLaurentPrimitive R w, logLaurentDerivative_logLaurentPrimitive w⟩

/-- **All primitives of a Laurent differential**: they are the normalized primitive plus a
constant. -/
theorem logLaurentDerivative_eq_iff {F : LaurentSeries V × V} {w : LaurentSeries V} :
    logLaurentDerivative R F = w ↔ ∃ c : V, F = logLaurentPrimitive R w + (single 0 c, 0) := by
  refine ⟨fun h ↦ ⟨F.1.coeff 0, ?_⟩, ?_⟩
  · rw [← h, logLaurentPrimitive_logLaurentDerivative, sub_add_cancel]
  · rintro ⟨c, rfl⟩
    rw [map_add, logLaurentDerivative_logLaurentPrimitive, logLaurentDerivative_single_zero,
      add_zero]

/-- A Laurent differential has a unique primitive with one logarithmic term and constant
coefficient zero. -/
theorem existsUnique_logLaurentDerivative_eq (w : LaurentSeries V) :
    ∃! F : LaurentSeries V × V, logLaurentDerivative R F = w ∧ F.1.coeff 0 = 0 := by
  refine ⟨logLaurentPrimitive R w, ⟨logLaurentDerivative_logLaurentPrimitive w, by simp⟩, ?_⟩
  rintro F ⟨hF, hF₀⟩
  obtain ⟨c, rfl⟩ := logLaurentDerivative_eq_iff.mp hF
  simp_all

end Module

section Ring

variable (R : Type*) [CommRing R]

/-- **The alternating local index** of two germs with one logarithmic term:
`B(f + a L, g + b L) = Res(f dg) + b Res(f dX / X) - a Res(g dX / X)`, where `Res(f dX / X)` is
the constant coefficient of `f`. -/
noncomputable def logLaurentIndex : LinearMap.BilinForm R (R⸨X⸩ × R) :=
  LinearMap.mk₂ R
    (fun F G ↦ LaurentSeries.residuePairing R F.1 G.1 + G.2 * F.1.coeff 0 - F.2 * G.1.coeff 0)
    (fun F F' G ↦ by
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, coeff_add]
      ring)
    (fun c F G ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, coeff_smul,
        smul_eq_mul]
      ring)
    (fun F G G' ↦ by
      simp only [Prod.fst_add, Prod.snd_add, map_add, coeff_add]
      ring)
    (fun c F G ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, coeff_smul, smul_eq_mul]
      ring)

variable {R}

theorem logLaurentIndex_apply (F G : R⸨X⸩ × R) :
    logLaurentIndex R F G =
      LaurentSeries.residuePairing R F.1 G.1 + G.2 * F.1.coeff 0 - F.2 * G.1.coeff 0 := (rfl)

/-- The residue `Res(f X⁻¹ dX)` is the constant coefficient of `f`. -/
private theorem coeff_neg_one_mul_single_neg_one (f : R⸨X⸩) (b : R) :
    (f * single (-1) b).coeff (-1) = f.coeff 0 * b := by
  simp [coeff_mul_single]

/-- **The Laurent-first residue rule**: if the first germ is a Laurent series `f`, the local
index is the residue `Res(f dG)` of `f` against the differential of the second germ. -/
@[simp]
theorem logLaurentIndex_mk_zero_left (f : R⸨X⸩) (G : R⸨X⸩ × R) :
    logLaurentIndex R (f, 0) G = (f * logLaurentDerivative R G).coeff (-1) := by
  rw [logLaurentIndex_apply, logLaurentDerivative_apply, mul_add, coeff_add,
    coeff_neg_one_mul_single_neg_one, LaurentSeries.residuePairing_apply]
  ring

/-- The index of the logarithmic germ `a L` against `G` is `-a Res(g dX / X)`. -/
@[simp]
theorem logLaurentIndex_zero_mk_left (a : R) (G : R⸨X⸩ × R) :
    logLaurentIndex R (0, a) G = -(a * G.1.coeff 0) := by
  simp [logLaurentIndex_apply]

/-- **The local index is alternating**: `B(F, F) = 0` for every germ `F`, over every
commutative ring. -/
@[simp]
theorem logLaurentIndex_self (F : R⸨X⸩ × R) : logLaurentIndex R F F = 0 := by
  rw [logLaurentIndex_apply, LaurentSeries.residuePairing_self]
  ring

/-- The local index is an alternating bilinear form. -/
theorem logLaurentIndex_isAlt : (logLaurentIndex R).IsAlt :=
  logLaurentIndex_self

/-- The local index is skew-symmetric: `B(F, G) = -B(G, F)`. -/
theorem logLaurentIndex_eq_neg_swap (F G : R⸨X⸩ × R) :
    logLaurentIndex R F G = -logLaurentIndex R G F :=
  (logLaurentIndex_isAlt.neg_eq G F).symm

/-- **The Laurent-second residue rule**: if the second germ is a Laurent series `g`, the local
index is `-Res(g dF)`. -/
@[simp]
theorem logLaurentIndex_mk_zero_right (F : R⸨X⸩ × R) (g : R⸨X⸩) :
    logLaurentIndex R F (g, 0) = -(g * logLaurentDerivative R F).coeff (-1) := by
  rw [logLaurentIndex_eq_neg_swap, logLaurentIndex_mk_zero_left]

/-- The index of `F` against the logarithmic germ `b L` is `b Res(f dX / X)`. -/
@[simp]
theorem logLaurentIndex_zero_mk_right (F : R⸨X⸩ × R) (b : R) :
    logLaurentIndex R F (0, b) = b * F.1.coeff 0 := by
  simp [logLaurentIndex_apply]

/-- The index of a constant `c` against `G` is `c Res(dG)`. -/
theorem logLaurentIndex_single_zero_left (c : R) (G : R⸨X⸩ × R) :
    logLaurentIndex R (single 0 c, 0) G = c * G.2 := by
  rw [logLaurentIndex_mk_zero_left, single_zero_mul_eq_smul, coeff_smul,
    coeff_neg_one_logLaurentDerivative, smul_eq_mul]

/-- The index of `F` against a constant `c` is `-c Res(dF)`. -/
theorem logLaurentIndex_single_zero_right (F : R⸨X⸩ × R) (c : R) :
    logLaurentIndex R F (single 0 c, 0) = -(c * F.2) := by
  rw [logLaurentIndex_eq_neg_swap, logLaurentIndex_single_zero_left]

/-- **Changing primitives by constants**: adding constants `c` and `d` to the two germs changes
the local index by `c Res(dG) - d Res(dF)`. -/
theorem logLaurentIndex_add_single_zero (F G : R⸨X⸩ × R) (c d : R) :
    logLaurentIndex R (F + (single 0 c, 0)) (G + (single 0 d, 0)) =
      logLaurentIndex R F G + c * G.2 - d * F.2 := by
  simp only [map_add, LinearMap.add_apply, logLaurentIndex_single_zero_left,
    logLaurentIndex_single_zero_right]
  ring

/-- **Uniqueness of the local index, up to a scalar.** An alternating bilinear form `β` on germs
with one logarithmic term satisfying the scaled Laurent-first residue rule
`β(f, G) = c Res(f dG)` is `c` times the local index. -/
theorem eq_smul_logLaurentIndex_of_isAlt {β : LinearMap.BilinForm R (R⸨X⸩ × R)} (hβ : β.IsAlt)
    (c : R)
    (h : ∀ (f : R⸨X⸩) (G : R⸨X⸩ × R),
      β (f, 0) G = c * (f * logLaurentDerivative R G).coeff (-1)) :
    β = c • logLaurentIndex R := by
  -- Every germ is a Laurent series plus a multiple of `L = (0, 1)`.
  have hdecomp (F : R⸨X⸩ × R) : F = (F.1, 0) + F.2 • ((0 : R⸨X⸩), (1 : R)) := by
    ext <;> simp
  -- Alternation and the residue rule compute `β(L, G)`; the term `β(L, L)` vanishes.
  have hlog (G : R⸨X⸩ × R) : β (0, 1) G = -(c * G.1.coeff 0) := by
    rw [← hβ.neg_eq, hdecomp G, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hβ.self_eq_zero, h, logLaurentDerivative_zero_mk, coeff_neg_one_mul_single_neg_one]
    simp
  refine LinearMap.ext₂ fun F G ↦ ?_
  conv_lhs => rw [hdecomp F]
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h, hlog]
  simp only [LinearMap.smul_apply, logLaurentIndex_apply, logLaurentDerivative_apply, mul_add,
    coeff_add, coeff_neg_one_mul_single_neg_one, LaurentSeries.residuePairing_apply, smul_eq_mul]
  ring

/-- **Uniqueness of the local index.** An alternating bilinear form on germs with one
logarithmic term satisfying the Laurent-first residue rule `β(f, G) = Res(f dG)` is the local
index. -/
theorem eq_logLaurentIndex_of_isAlt {β : LinearMap.BilinForm R (R⸨X⸩ × R)} (hβ : β.IsAlt)
    (h : ∀ (f : R⸨X⸩) (G : R⸨X⸩ × R), β (f, 0) G = (f * logLaurentDerivative R G).coeff (-1)) :
    β = logLaurentIndex R := by
  simpa using eq_smul_logLaurentIndex_of_isAlt hβ 1 (by simpa using h)

/-- **Coefficient extension.** A ring homomorphism `φ : R →+* S` sends the local index of two
germs to the local index of their coefficientwise images. -/
theorem map_logLaurentIndex {S : Type*} [CommRing S] (φ : R →+* S) (F G : R⸨X⸩ × R) :
    φ (logLaurentIndex R F G) =
      logLaurentIndex S (Prod.map (mapRingHom φ) φ F) (Prod.map (mapRingHom φ) φ G) := by
  simp only [logLaurentIndex_apply, map_sub, map_add, map_mul, LaurentSeries.map_residuePairing,
    Prod.map_fst, Prod.map_snd, coeff_mapRingHom]

end Ring

section Substitution

variable {K : Type*} [Field K] {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

/-- The pullback of germs with one logarithmic term along the formal substitution `X ↦ φ`, given
the germ `Λ` chosen as the pullback of the logarithm `L`: it sends `f + a L` to `f (φ) + a Λ`.
The pullback laws hold when `Λ` is a logarithm of `φ`, that is `φ dΛ = dφ`. -/
noncomputable def logLaurentSubst (Λ : K⸨X⸩ × K) : K⸨X⸩ × K →ₗ[K] K⸨X⸩ × K where
  toFun F := (LaurentSeries.substAlgHom hφ hφ₀ F.1, 0) + F.2 • Λ
  map_add' F G := by
    ext <;> simp [add_smul, add_add_add_comm]
  map_smul' c F := by
    -- `substAlgHom` is linear for `Algebra.toModule`; compare it with the coefficientwise action.
    have hs : LaurentSeries.substAlgHom hφ hφ₀ (c • F.1) =
        c • LaurentSeries.substAlgHom hφ hφ₀ F.1 := by
      rw [← laurentSeries_algebraMap_mul_eq_smul, map_mul, AlgHom.commutes,
        laurentSeries_algebraMap_mul_eq_smul]
    ext <;> simp [hs, mul_smul]

theorem logLaurentSubst_apply (Λ F : K⸨X⸩ × K) :
    logLaurentSubst hφ hφ₀ Λ F = (LaurentSeries.substAlgHom hφ hφ₀ F.1, 0) + F.2 • Λ := (rfl)

/-- A Laurent series is pulled back by substitution. -/
@[simp]
theorem logLaurentSubst_mk_zero (Λ : K⸨X⸩ × K) (f : K⸨X⸩) :
    logLaurentSubst hφ hφ₀ Λ (f, 0) = (LaurentSeries.substAlgHom hφ hφ₀ f, 0) := by
  simp [logLaurentSubst_apply]

/-- The logarithm `L` is pulled back to the chosen germ `Λ`. -/
@[simp]
theorem logLaurentSubst_zero_mk_one (Λ : K⸨X⸩ × K) :
    logLaurentSubst hφ hφ₀ Λ (0, 1) = Λ := by
  simp [logLaurentSubst_apply]

variable {hφ hφ₀}

/-- **The chain rule for germs with one logarithmic term.** If `Λ` is a logarithm of `φ`, the
differential of the pullback of `F` is the pullback `dF (φ) dφ` of the differential of `F`. -/
theorem logLaurentDerivative_logLaurentSubst {Λ : K⸨X⸩ × K}
    (hΛ : (φ : K⸨X⸩) * logLaurentDerivative K Λ = LaurentSeries.derivative K (φ : K⸨X⸩))
    (F : K⸨X⸩ × K) :
    logLaurentDerivative K (logLaurentSubst hφ hφ₀ Λ F) =
      LaurentSeries.substAlgHom hφ hφ₀ (logLaurentDerivative K F) *
        LaurentSeries.derivative K (φ : K⸨X⸩) := by
  have hφ' : (φ : K⸨X⸩) ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr hφ₀
  -- The Laurent part `f` is differentiated by the chain rule for Laurent series.
  have hlaurent : logLaurentDerivative K (LaurentSeries.substAlgHom hφ hφ₀ F.1, 0) =
      LaurentSeries.substAlgHom hφ hφ₀ (LaurentSeries.derivative K F.1) *
        LaurentSeries.derivative K (φ : K⸨X⸩) := by
    rw [logLaurentDerivative_mk_zero, LaurentSeries.derivative_substAlgHom]
  -- The log part: `a X⁻¹ dX` pulls back to `a φ⁻¹ dφ`, which is `a dΛ` by the hypothesis `hΛ`.
  have hlog : LaurentSeries.substAlgHom hφ hφ₀ (single (-1) F.2) *
      LaurentSeries.derivative K (φ : K⸨X⸩) = F.2 • logLaurentDerivative K Λ := by
    rw [LaurentSeries.substAlgHom_single, ← hΛ, zpow_neg_one, mul_assoc,
      inv_mul_cancel_left₀ hφ', HahnSeries.C_mul_eq_smul]
  rw [logLaurentSubst_apply, map_add, map_smul, hlaurent, logLaurentDerivative_apply F, map_add,
    add_mul, hlog]

/-- The logarithmic coefficient of a logarithm of `φ` is the order of `φ`. -/
theorem snd_eq_order_of_mul_logLaurentDerivative_eq (hφ : PowerSeries.constantCoeff φ = 0)
    (hφ₀ : φ ≠ 0) {Λ : K⸨X⸩ × K}
    (hΛ : (φ : K⸨X⸩) * logLaurentDerivative K Λ = LaurentSeries.derivative K (φ : K⸨X⸩)) :
    Λ.2 = (φ.order.toNat : K) := by
  have h := logLaurentDerivative_logLaurentSubst (hφ := hφ) (hφ₀ := hφ₀) hΛ
    ((0 : K⸨X⸩), (1 : K))
  rw [logLaurentSubst_zero_mk_one, logLaurentDerivative_zero_mk] at h
  have h' := congrArg (fun w : K⸨X⸩ ↦ w.coeff (-1)) h
  simp only [coeff_neg_one_logLaurentDerivative] at h'
  rw [h', LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul, coeff_single_same,
    nsmul_eq_mul, mul_one]

/-- In characteristic zero every power series `φ` has a logarithm: some germ `Λ` with one
logarithmic term satisfies `φ dΛ = dφ`. -/
theorem exists_mul_logLaurentDerivative_eq [CharZero K] (φ : K⟦X⟧) :
    ∃ Λ : K⸨X⸩ × K,
      (φ : K⸨X⸩) * logLaurentDerivative K Λ = LaurentSeries.derivative K (φ : K⸨X⸩) := by
  obtain rfl | hφ₀ := eq_or_ne φ 0
  · exact ⟨0, by simp⟩
  have hφ' : (φ : K⸨X⸩) ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr hφ₀
  refine ⟨logLaurentPrimitive K (LaurentSeries.derivative K (φ : K⸨X⸩) / φ), ?_⟩
  rw [logLaurentDerivative_logLaurentPrimitive, mul_div_cancel₀ _ hφ']

/-- **Transport of the local index under substitution.** If `Λ` is a logarithm of `φ`, pulling
back both germs along `X ↦ φ` multiplies the local index by the order of `φ`; in particular a
formal coordinate change, of order one, preserves it. -/
theorem logLaurentIndex_logLaurentSubst {Λ : K⸨X⸩ × K}
    (hΛ : (φ : K⸨X⸩) * logLaurentDerivative K Λ = LaurentSeries.derivative K (φ : K⸨X⸩))
    (F G : K⸨X⸩ × K) :
    logLaurentIndex K (logLaurentSubst hφ hφ₀ Λ F) (logLaurentSubst hφ hφ₀ Λ G) =
      φ.order.toNat • logLaurentIndex K F G := by
  have h := eq_smul_logLaurentIndex_of_isAlt
    (β := (logLaurentIndex K).compl₁₂ (logLaurentSubst hφ hφ₀ Λ) (logLaurentSubst hφ hφ₀ Λ))
    (fun F ↦ by rw [LinearMap.compl₁₂_apply]; exact logLaurentIndex_self _)
    (φ.order.toNat : K) fun f G ↦ by
      rw [LinearMap.compl₁₂_apply, logLaurentSubst_mk_zero, logLaurentIndex_mk_zero_left,
        logLaurentDerivative_logLaurentSubst hΛ, ← mul_assoc, ← map_mul,
        LaurentSeries.coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul, nsmul_eq_mul]
  rw [← LinearMap.compl₁₂_apply, h, LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul,
    smul_eq_mul]

end Substitution

end TauCeti
