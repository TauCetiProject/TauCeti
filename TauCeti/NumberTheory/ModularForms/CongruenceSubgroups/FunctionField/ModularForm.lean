/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Holomorphic
public import TauCeti.NumberTheory.ModularForms.WeakForm
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Galois conjugates of weak forms of level `N` and weight divisible by `12`

Let `σ` be an automorphism of `ℂ`, not necessarily continuous, and expand functions on the upper
half-plane at `∞` in `q = exp (2πiτ / N)`. For a weak form `f` on `Γ(N)` of weight `12 m`,
applying `σ` to the coefficients of the Laurent expansion of `f` gives the Laurent expansion of
another weak form on `Γ(N)` of weight `12 m`. Since `σ` need not be continuous, the conjugate
cannot be computed from the values of `f`; it is constructed through the function field of
`X(N)`, following Shimura.

The quotient `f / Δ ^ m` has weight zero. It is holomorphic on `ℍ`, since `Δ` has no zero
there, so it is a meromorphic function on `X(N)` without poles on `Y(N)`. The coefficient action
`TauCeti.modularFunctionCoeffAction` conjugates its Fourier coefficients, and the conjugate again
has no poles on `Y(N)` (`TauCeti.forall_ne_infty_modularFunctionCoeffAction_iff`). Multiplying
back by `Δ ^ m`, whose `q`-expansion has integer coefficients and so is fixed by `σ`, gives a
weak form of weight `12 m` with the conjugate expansion at `∞`. This works at every cusp: if
`σ ζ_N = ζ_N ^ d`, the expansion of the conjugate at the cusp `γ ∞` is the conjugate of the
expansion of `f` at `γ' ∞`, where `γ' diag(1, d) = diag(1, d) γ` modulo `N`. This comes from the
twisted commutation `TauCeti.modularFunctionCoeffAction_unop_modularFunctionActionZMod` of the
coefficient action with fractional linear maps.

In weight divisible by `12` the twist is only needed modulo `N`. Conjugates in every weight,
including those of modular forms and cusp forms, are in `FunctionField/GaloisConjugate.lean`,
where the twist is taken modulo `12 N`.

## Main results

* `TauCeti.IsWeakForm.exists_laurentQExpansion_slash_eq_mapRingHom_twelve_mul`: conjugating the
  Fourier coefficients of a weak form of weight `12 m` on `Γ(N)`, at every cusp.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§6.1–6.2.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient Matrix.SpecialLinearGroup
open TauCeti.RiemannSurface OnePoint
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- Conjugating the Fourier coefficients of a weight-zero weak form on `Γ(N)`, at every cusp. -/
private theorem exists_isWeakForm_zero_laurentQExpansion_slash_eq {F : ℍ → ℂ}
    (hF : IsWeakForm (Gamma N) 0 F) (σ : ℂ ≃+* ℂ) {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N)) :
    ∃ G : ℍ → ℂ, IsWeakForm (Gamma N) 0 G ∧ ∀ γ γ' : SL(2, ℤ),
      ((γ' : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
          Matrix.diagonal ![1, (d : ZMod N)] =
        Matrix.diagonal ![1, (d : ZMod N)] * (γ : SL(2, ZMod N)) →
      UpperHalfPlane.laurentQExpansion N (G ∣[(0 : ℤ)] γ) =
        HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
          (UpperHalfPlane.laurentQExpansion N (F ∣[(0 : ℤ)] γ')) := by
  set Φ := hF.meromorphicFunction
  have hΨ : ∀ τ : ℍ, modularFunctionCoeffAction N σ Φ (ofQuotient (Quotient.mk _ τ)) ≠ ∞ :=
    (forall_ne_infty_modularFunctionCoeffAction_iff σ Φ).mpr fun τ ↦ by
      rw [hF.meromorphicFunction_ofQuotient_mk]
      exact coe_ne_infty _
  refine ⟨_, isWeakForm_finitePart_ofQuotient_mk hΨ, fun γ γ' hγ ↦ ?_⟩
  -- `F` is the pullback to `ℍ` of the finite part of `Φ`.
  have hFΦ : (fun τ ↦ Φ.finitePart (ofQuotient (Quotient.mk _ τ))) = F :=
    funext hF.finitePart_meromorphicFunction_ofQuotient_mk
  calc
    _ = laurentQExpansion (cuspDatumInftyGamma N)
        (unop (modularFunctionAction N γ) (modularFunctionCoeffAction N σ Φ)) := by
      rw [finitePart_ofQuotient_slash_zero, laurentQExpansion_cuspDatumInftyGamma]
    _ = laurentQExpansion (cuspDatumInftyGamma N)
        (modularFunctionCoeffAction N σ (unop (modularFunctionAction N γ') Φ)) := by
      rw [modularFunctionCoeffAction_unop_modularFunctionAction hσ hγ]
    _ = HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
        (laurentQExpansion (cuspDatumInftyGamma N) (unop (modularFunctionAction N γ') Φ)) :=
      laurentQExpansion_modularFunctionCoeffAction σ _
    _ = _ := by
      rw [← hFΦ, finitePart_ofQuotient_slash_zero, laurentQExpansion_cuspDatumInftyGamma]

/-- **Galois conjugates of weak forms of weight divisible by `12`.** Let `σ` be an automorphism
of `ℂ` with `σ ζ_N = ζ_N ^ d`. For a weak form `f` of weight `12 m` on `Γ(N)` there is a weak
form `g` of the same weight whose Laurent expansion at every cusp is obtained by applying `σ` to
the coefficients of that of `f` at the cusp twisted by `diag(1, d)`: if
`γ' diag(1, d) = diag(1, d) γ` modulo `N`, the expansion of `g ∣ γ` at `∞` is the
`σ`-conjugate of that of `f ∣ γ'`. For `γ = γ' = 1` this is the expansion at `∞`. -/
theorem IsWeakForm.exists_laurentQExpansion_slash_eq_mapRingHom_twelve_mul {m : ℤ} {f : ℍ → ℂ}
    (hf : IsWeakForm (Gamma N) (12 * m) f) (σ : ℂ ≃+* ℂ) {d : (ZMod N)ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod N)) = ZMod.stdAddChar (d : ZMod N)) :
    ∃ g : ℍ → ℂ, IsWeakForm (Gamma N) (12 * m) g ∧ ∀ γ γ' : SL(2, ℤ),
      ((γ' : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
          Matrix.diagonal ![1, (d : ZMod N)] =
        Matrix.diagonal ![1, (d : ZMod N)] * (γ : SL(2, ZMod N)) →
      UpperHalfPlane.laurentQExpansion N (g ∣[12 * m] γ) =
        HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
          (UpperHalfPlane.laurentQExpansion N (f ∣[12 * m] γ')) := by
  set D : ℤ → ℍ → ℂ := fun n τ ↦ ModularForm.discriminant τ ^ n
  have hD (n : ℤ) : IsWeakForm (Gamma N) (12 * n) (D n) :=
    (isWeakForm_discriminant_zpow n).mono le_top
  have hDslash (n : ℤ) (γ : SL(2, ℤ)) : D n ∣[12 * n] γ = D n :=
    (isWeakForm_discriminant_zpow n).slash_eq γ (Subgroup.mem_top γ)
  have hDD : D (-m) * D m = 1 := by
    funext τ
    simpa [D, zpow_neg] using
      inv_mul_cancel₀ (zpow_ne_zero m (ModularForm.discriminant_ne_zero τ))
  have hF : IsWeakForm (Gamma N) 0 (f * D (-m)) := by
    convert hf.mul (hD (-m)) using 1
    ring
  obtain ⟨G, hG, hGσ⟩ := exists_isWeakForm_zero_laurentQExpansion_slash_eq hF σ hσ
  -- `mul_slash_SL2` slashes a product in the sum of the weights of its factors, so each slash
  -- weight is written as such a sum.
  have hweight : (12 * m : ℤ) = 0 + 12 * m := by ring
  have hweight' : (0 : ℤ) = 12 * m + 12 * -m := by ring
  refine ⟨G * D m, hweight ▸ hG.mul (hD m), fun γ γ' hγ ↦ ?_⟩
  have hslash : (G * D m) ∣[12 * m] γ = (G ∣[(0 : ℤ)] γ) * D m := by
    rw [hweight, ModularForm.mul_slash_SL2, hDslash]
  have hslash' : (f * D (-m)) ∣[(0 : ℤ)] γ' = (f ∣[12 * m] γ') * D (-m) := by
    rw [hweight', ModularForm.mul_slash_SL2, hDslash]
  -- The strict level of `Γ(N)` is `N`, so the cusp germs are meromorphic in `q = exp (2πiτ / N)`.
  have hmeroSlash {l : ℤ} {u : ℍ → ℂ} (hu : IsWeakForm (Gamma N) l u) (γ : SL(2, ℤ)) :
      _root_.MeromorphicAt (cuspFunction N (u ∣[l] γ)) 0 := by
    simpa only [strictLevel_Gamma] using hu.meromorphicAt_cuspFunction_slash γ
  have hmero (n : ℤ) : _root_.MeromorphicAt (cuspFunction N (D n)) 0 := by
    simpa using hmeroSlash (hD n) 1
  calc
    _ = UpperHalfPlane.laurentQExpansion N (G ∣[(0 : ℤ)] γ) *
        UpperHalfPlane.laurentQExpansion N (D m) := by
      rw [hslash, UpperHalfPlane.laurentQExpansion_mul (hmeroSlash hG γ) (hmero m)]
    _ = HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
        (UpperHalfPlane.laurentQExpansion N (f ∣[12 * m] γ') *
          UpperHalfPlane.laurentQExpansion N (D (-m))) *
        UpperHalfPlane.laurentQExpansion N (D m) := by
      rw [hGσ γ γ' hγ, hslash',
        UpperHalfPlane.laurentQExpansion_mul (hmeroSlash hf γ') (hmero (-m))]
    _ = HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
        (UpperHalfPlane.laurentQExpansion N (f ∣[12 * m] γ')) *
        (UpperHalfPlane.laurentQExpansion N (D (-m)) *
          UpperHalfPlane.laurentQExpansion N (D m)) := by
      rw [map_mul, ModularForm.mapRingHom_laurentQExpansion_discriminant_zpow, mul_assoc]
    _ = _ := by
      rw [← UpperHalfPlane.laurentQExpansion_mul (hmero (-m)) (hmero m), hDD]
      simp only [UpperHalfPlane.laurentQExpansion_one, mul_one]

end TauCeti
