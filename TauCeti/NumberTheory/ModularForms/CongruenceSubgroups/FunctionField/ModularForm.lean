/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Holomorphic
public import TauCeti.NumberTheory.ModularForms.WeakForm
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Invariant
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Galois conjugates of modular forms of level `N` and weight divisible by `12`

Let `σ` be an automorphism of `ℂ`, not necessarily continuous, and expand functions on the upper
half-plane at `∞` in `q = exp (2πiτ / N)`. For a modular form `f` on `Γ(N)` of weight `12 m`,
applying `σ` to the coefficients of the `q`-expansion of `f` gives the `q`-expansion of another
modular form on `Γ(N)` of weight `12 m` (`ModularForm.exists_qExpansion_eq_map`), and the same
holds for cusp forms (`CuspForm.exists_qExpansion_eq_map`). Since `σ` need not be continuous,
the conjugate cannot be computed from the values of `f`; it is constructed through the function
field of `X(N)`, following Shimura.

The quotient `f / Δ ^ m` has weight zero. It is holomorphic on `ℍ`, since `Δ` has no zero
there, so it is a meromorphic function on `X(N)` without poles on `Y(N)`. The coefficient action
`TauCeti.modularFunctionCoeffAction` conjugates its Fourier coefficients, and the conjugate again
has no poles on `Y(N)` (`TauCeti.forall_ne_infty_modularFunctionCoeffAction_iff`). Multiplying
back by `Δ ^ m`, whose `q`-expansion has integer coefficients and so is fixed by `σ`, gives a
weak form of weight `12 m` with the conjugate expansion at `∞`. The same works for weak forms,
and at every cusp: if `σ ζ_N = ζ_N ^ d`, the expansion of the conjugate at the cusp `γ ∞` is the
conjugate of the expansion of `f` at `γ' ∞`, where `γ' diag(1, d) = diag(1, d) γ` modulo `N`
(`TauCeti.IsWeakForm.exists_laurentQExpansion_slash_eq_mapRingHom`). This comes from the twisted
commutation `TauCeti.modularFunctionCoeffAction_unop_modularFunctionActionZMod` of the
coefficient action with fractional linear maps. Since `f` is bounded at every cusp, its
expansions there have no negative powers of `q`, so neither do those of the conjugate. The
conjugate is therefore bounded at every cusp, and it vanishes at every cusp when `f` does.

Weight divisible by `12` is what the quotient by a power of `Δ` needs. For a form `f` of any
weight `k`, the forms `f ^ 12` and `f * f₀ ^ 11` have weight `12 k`, which is how the conjugates
constructed here enter the conjugation of forms of other weights.

## Main results

* `TauCeti.IsWeakForm.exists_laurentQExpansion_slash_eq_mapRingHom`: conjugating the Fourier
  coefficients of a weak form of weight `12 m` on `Γ(N)`, at every cusp.
* `ModularForm.exists_qExpansion_eq_map`, `CuspForm.exists_qExpansion_eq_map`: the conjugate of
  a modular form, resp. a cusp form, on `Γ(N)` of weight divisible by `12`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§6.1–6.2.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient Filter Matrix.SpecialLinearGroup
open TauCeti.RiemannSurface OnePoint
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- A weight-zero weak form on `Γ(N)` as a meromorphic function on `X(N)`. -/
private def weakFormMeromorphicFunction {F : ℍ → ℂ} (hF : IsWeakForm (Gamma N) 0 F) :
    MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient :=
  meromorphicFunctionOfGammaInvariant F hF.mdifferentiable
    (fun γ hγ τ ↦ by rw [← congrFun (ModularForm.SL_slash_zero F γ) τ, hF.slash_eq γ hγ])
    (fun γ ↦ by
      obtain ⟨c, hc⟩ := hF.exists_isBigO_exp γ
      exact ⟨c, by rwa [ModularForm.SL_slash_zero] at hc⟩)

private theorem weakFormMeromorphicFunction_ofQuotient_mk {F : ℍ → ℂ}
    (hF : IsWeakForm (Gamma N) 0 F) (τ : ℍ) :
    weakFormMeromorphicFunction hF (ofQuotient (Quotient.mk _ τ)) = F τ :=
  meromorphicFunctionOfGammaInvariant_ofQuotient_mk _ _ _ τ

/-- The pullback to `ℍ` of a function on `X(N)` without poles on `Y(N)` is a weak form of weight
`0` on `Γ(N)`. -/
private theorem isWeakForm_finitePart
    {Ψ : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hΨ : ∀ τ : ℍ, Ψ (ofQuotient (Quotient.mk _ τ)) ≠ ∞) :
    IsWeakForm (Gamma N) 0 fun τ ↦ Ψ.finitePart (ofQuotient (Quotient.mk _ τ)) := by
  have hslash (γ : SL(2, ℤ)) : (fun τ ↦ Ψ.finitePart (ofQuotient (Quotient.mk _ τ))) ∣[(0 : ℤ)] γ =
      fun τ ↦ (unop (modularFunctionAction N γ) Ψ).finitePart (ofQuotient (Quotient.mk _ τ)) := by
    rw [ModularForm.SL_slash_zero]
    funext τ
    rw [finitePart_unop_modularFunctionAction]
  have hinv : ∀ γ ∈ Gamma N,
      (fun τ ↦ Ψ.finitePart (ofQuotient (Quotient.mk _ τ))) ∣[(0 : ℤ)] γ =
        fun τ ↦ Ψ.finitePart (ofQuotient (Quotient.mk _ τ)) := fun γ hγ ↦ by
    rw [hslash, modularFunctionAction_eq_one_of_mem hγ, unop_one, AlgEquiv.one_apply]
  refine isWeakForm_iff_meromorphicAt_cuspFunction.mpr ⟨fun τ ↦ ?_, hinv, fun γ ↦ ?_⟩
  · exact (MeromorphicFunction.mdifferentiableAt_finitePart (hΨ τ)).comp τ
      ((mdifferentiable_ofQuotient _).comp τ (Subgroup.mdifferentiable_quotientMk _ τ))
  · refine ⟨N, NeZero.pos N, ?_, ?_⟩
    · simpa [strictLevel_Gamma] using periodic_slash_comp_ofComplex hinv γ
    · rw [hslash]
      simpa [cuspDatumInftyGamma_width, cuspDatumInftyGamma_scaling] using
        meromorphicAt_cuspFunction_finitePart (cuspDatumInftyGamma N)
          (unop (modularFunctionAction N γ) Ψ)

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
  set Φ := weakFormMeromorphicFunction hF
  have hΨ : ∀ τ : ℍ, modularFunctionCoeffAction N σ Φ (ofQuotient (Quotient.mk _ τ)) ≠ ∞ :=
    (forall_ne_infty_modularFunctionCoeffAction_iff σ Φ).mpr fun τ ↦ by
      rw [weakFormMeromorphicFunction_ofQuotient_mk]
      exact coe_ne_infty _
  refine ⟨_, isWeakForm_finitePart hΨ, fun γ γ' hγ ↦ ?_⟩
  have hF' : F ∣[(0 : ℤ)] γ' = fun τ ↦
      (unop (modularFunctionAction N γ') Φ).finitePart (ofQuotient (Quotient.mk _ τ)) := by
    rw [ModularForm.SL_slash_zero]
    funext τ
    rw [finitePart_unop_modularFunctionAction, MeromorphicFunction.finitePart_of_eq_coe
      (weakFormMeromorphicFunction_ofQuotient_mk hF _)]
  have hG : (fun τ ↦ (modularFunctionCoeffAction N σ Φ).finitePart
      (ofQuotient (Quotient.mk _ τ))) ∣[(0 : ℤ)] γ = fun τ ↦
      (unop (modularFunctionAction N γ) (modularFunctionCoeffAction N σ Φ)).finitePart
        (ofQuotient (Quotient.mk _ τ)) := by
    rw [ModularForm.SL_slash_zero]
    funext τ
    rw [finitePart_unop_modularFunctionAction]
  calc
    _ = laurentQExpansion (cuspDatumInftyGamma N)
        (unop (modularFunctionAction N γ) (modularFunctionCoeffAction N σ Φ)) := by
      rw [hG, laurentQExpansion_cuspDatumInftyGamma]
    _ = laurentQExpansion (cuspDatumInftyGamma N)
        (modularFunctionCoeffAction N σ (unop (modularFunctionAction N γ') Φ)) := by
      rw [modularFunctionCoeffAction_unop_modularFunctionAction hσ hγ]
    _ = HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
        (laurentQExpansion (cuspDatumInftyGamma N) (unop (modularFunctionAction N γ') Φ)) :=
      laurentQExpansion_modularFunctionCoeffAction σ _
    _ = _ := by rw [hF', laurentQExpansion_cuspDatumInftyGamma]

/-- **Galois conjugates of weak forms of weight divisible by `12`.** Let `σ` be an automorphism
of `ℂ` with `σ ζ_N = ζ_N ^ d`. For a weak form `f` of weight `12 m` on `Γ(N)` there is a weak
form `g` of the same weight whose Laurent expansion at every cusp is obtained by applying `σ` to
the coefficients of that of `f` at the cusp twisted by `diag(1, d)`: if
`γ' diag(1, d) = diag(1, d) γ` modulo `N`, the expansion of `g ∣ γ` at `∞` is the
`σ`-conjugate of that of `f ∣ γ'`. For `γ = γ' = 1` this is the expansion at `∞`. -/
theorem IsWeakForm.exists_laurentQExpansion_slash_eq_mapRingHom {m : ℤ} {f : ℍ → ℂ}
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

/-- The weak-form conjugate of a modular form on `Γ(N)` of weight `12 m`: its expansion at `∞`
is the conjugate of that of `f`, and at every cusp it tends to the conjugate of the value of `f`
at a twisted cusp. -/
private theorem exists_isWeakForm_tendsto_slash_atImInfty {m : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma N).map (mapGL ℝ)) (12 * m)] (f : F) (σ : ℂ ≃+* ℂ) :
    ∃ g : ℍ → ℂ, IsWeakForm (Gamma N) (12 * m) g ∧
      UpperHalfPlane.laurentQExpansion N g =
        (PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N f) : LaurentSeries ℂ) ∧
      ∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), Tendsto (g ∣[12 * m] γ) atImInfty
        (nhds (σ ((qExpansion N (f ∣[12 * m] γ')).coeff 0))) := by
  obtain ⟨d, hd⟩ := ZMod.exists_map_stdAddChar_one_eq (N := N) σ
  have han (γ : SL(2, ℤ)) : AnalyticAt ℂ (cuspFunction N (f ∣[12 * m] γ)) 0 := by
    simpa only [strictLevel_Gamma] using
      ModularFormClass.analyticAt_cuspFunction_slash (Γ := Gamma N) f γ
  obtain ⟨g, hg, hgσ⟩ :=
    (ModularFormClass.isWeakForm f).exists_laurentQExpansion_slash_eq_mapRingHom σ hd
  have hσ (γ γ' : SL(2, ℤ)) (hγ : ((γ' : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
      Matrix.diagonal ![1, (d : ZMod N)] = Matrix.diagonal ![1, (d : ZMod N)] *
        (γ : SL(2, ZMod N))) : UpperHalfPlane.laurentQExpansion N (g ∣[12 * m] γ) =
      (PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N (f ∣[12 * m] γ')) : LaurentSeries ℂ) := by
    rw [hgσ γ γ' hγ,
      UpperHalfPlane.laurentQExpansion_of_analyticAt (han γ'),
      HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries]
  refine ⟨g, hg, by simpa using hσ 1 1 (by simp), fun γ ↦ ?_⟩
  obtain ⟨γ', hγ'⟩ := exists_mul_diagonal_eq_diagonal_mul d γ
  refine ⟨γ', ?_⟩
  have h0 : 0 ≤ (UpperHalfPlane.laurentQExpansion N (g ∣[12 * m] γ)).orderTop := by
    rw [hσ γ γ' hγ', PowerSeries.orderTop_coe]
    cases (PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N (f ∣[12 * m] γ'))).order using
      ENat.recTopCoe <;> simp
  simpa [strictLevel_Gamma, hσ γ γ' hγ', PowerSeries.coeff_coe] using
    hg.tendsto_slash_atImInfty γ (by simpa only [strictLevel_Gamma] using h0)

/-- **Galois conjugates of modular forms of weight divisible by `12`.** For every automorphism
`σ` of `ℂ` and every modular form `f` on `Γ(N)` of weight `k` divisible by `12`, applying `σ` to
the coefficients of the `q`-expansion of `f` at `∞`, in `q = exp (2πiτ / N)`, gives the
`q`-expansion of a modular form on `Γ(N)` of the same weight. The automorphism `σ` need not be
continuous. -/
theorem _root_.ModularForm.exists_qExpansion_eq_map {k : ℤ} (hk : 12 ∣ k)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) (σ : ℂ ≃+* ℂ) :
    ∃ g : ModularForm ((Gamma N).map (mapGL ℝ)) k,
      qExpansion N g = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N f) := by
  obtain ⟨m, rfl⟩ := hk
  obtain ⟨g, hg, hg₀, hgσ⟩ := exists_isWeakForm_tendsto_slash_atImInfty f σ
  have hbdd (γ : SL(2, ℤ)) : IsBoundedAtImInfty (g ∣[12 * m] γ) := by
    obtain ⟨γ', hγ'⟩ := hgσ γ
    exact hγ'.isBigO_one ℝ
  obtain ⟨F, rfl⟩ := exists_modularForm_coe_eq_iff.mpr ⟨hg, hbdd⟩
  refine ⟨F, HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_⟩
  rw [← hg₀, UpperHalfPlane.laurentQExpansion_of_analyticAt]
  simpa [strictLevel_Gamma] using ModularFormClass.analyticAt_cuspFunction_slash (Γ := Gamma N) F 1

/-- **Galois conjugates of cusp forms of weight divisible by `12`.** For every automorphism `σ`
of `ℂ` and every cusp form `f` on `Γ(N)` of weight `k` divisible by `12`, applying `σ` to the
coefficients of the `q`-expansion of `f` at `∞`, in `q = exp (2πiτ / N)`, gives the
`q`-expansion of a cusp form on `Γ(N)` of the same weight. The automorphism `σ` need not be
continuous. -/
theorem _root_.CuspForm.exists_qExpansion_eq_map {k : ℤ} (hk : 12 ∣ k)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (σ : ℂ ≃+* ℂ) :
    ∃ g : CuspForm ((Gamma N).map (mapGL ℝ)) k,
      qExpansion N g = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N f) := by
  obtain ⟨m, rfl⟩ := hk
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨g, hg, hg₀, hgσ⟩ := exists_isWeakForm_tendsto_slash_atImInfty f σ
  have hzero (γ : SL(2, ℤ)) : IsZeroAtImInfty (g ∣[12 * m] γ) := by
    obtain ⟨γ', hγ'⟩ := hgσ γ
    have hf := ModularFormClass.isWeakForm f
    have hper : Function.Periodic ((f ∣[12 * m] γ') ∘ ofComplex) N := by
      simpa [strictLevel_Gamma] using periodic_slash_comp_ofComplex hf.slash_eq γ'
    have han : AnalyticAt ℂ (cuspFunction N (f ∣[12 * m] γ')) 0 := by
      simpa only [strictLevel_Gamma] using
        ModularFormClass.analyticAt_cuspFunction_slash (Γ := Gamma N) f γ'
    rwa [qExpansion_coeff_zero hN han hper,
      (CuspFormClass.zero_at_infty_slash f γ').valueAtInfty_eq_zero, map_zero] at hγ'
  let G : CuspForm ((Gamma N).map (mapGL ℝ)) (12 * m) :=
    { toFun := g
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        exact hg.slash_eq γ hγ
      holo' := hg.mdifferentiable
      zero_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        exact (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ hzero γ }
  -- `G` is built from `g` as a structure, so its coercion is `g`
  have hGg : ⇑G = g := rfl
  refine ⟨G, HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_⟩
  rw [← hg₀, ← hGg, UpperHalfPlane.laurentQExpansion_of_analyticAt]
  simpa [strictLevel_Gamma] using ModularFormClass.analyticAt_cuspFunction_slash (Γ := Gamma N) G 1

end TauCeti
