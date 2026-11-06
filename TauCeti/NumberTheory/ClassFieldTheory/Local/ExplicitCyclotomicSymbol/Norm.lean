/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ProductFormula
import TauCeti.NumberTheory.Cyclotomic.AbsoluteGaloisGroup
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Cyclotomic.NormValuation
import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
import TauCeti.NumberTheory.NumberField.SignApproximation
import TauCeti.NumberTheory.NumberField.TotallyPositive
import TauCeti.NumberTheory.Padics.AlgebraicClosure
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The explicit cyclotomic symbol kills local norms

Let `M` be a finite extension of `ℚ_p` inside `ℚ_p(μ_m) ⊆ AlgebraicClosure ℚ_[p]`. Every
`σ ∈ G_{ℚ_p}` acting on `μ_m` through the explicit symbol `cyclotomicSymbol m p (N_{M/ℚ_p} y)` of a
norm from `M` fixes `M`. This is the local input of the cyclotomic normalization of the local Artin
map: it establishes triviality of the explicit symbol on local norms and supplies an input to the
later comparison with the Artin map, with no reciprocity law and no Lubin–Tate theory.

The proof is global. The number field `K = ℚ(μ_m) ∩ M` cuts out in `Gal(ℚ_p(μ_m)/ℚ_p)` the same
subgroup as `M`, so it suffices to show that `σ` fixes `K`. Weak approximation gives `Y ∈ K` close
to `y` at the embedding `K ⊆ M`, close to `1` at the other `p`-adic places and at the places above
the other primes dividing `m`, and totally positive. In the product formula for `N_{K/ℚ}(Y)`, the
symbol at `p` is that of `N_{M/ℚ_p}(y)`, the symbols at the other primes dividing `m` and at the
real place are trivial, and the symbols at the primes not dividing `m` fix `K`. So the symbol of
`N_{M/ℚ_p}(y)` fixes `K` too.

## Main results

* `TauCeti.cyclotomicSymbol_norm_fixes`: the explicit symbol of a norm from `M` fixes `M`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Example 8.2, for the explicit symbols and their
  product formula.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §3, for weak approximation.
-/

public section

open NumberField

namespace TauCeti


/-- A global element of `K` that is `ρ`-close to `y` relative to `‖y‖` at the embedding
`K ⊆ M ⊆ AlgebraicClosure ℚ_[p]`, and `ρ`-close to `1` at the other embeddings, at the places above
the primes in `L` and at the infinite places. -/
private theorem exists_approx_of_le_adjoin (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])) [NumberField K] [IsGalois ℚ K]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hMK : M ≤ IntermediateField.adjoin ℚ_[p] (K : Set (AlgebraicClosure ℚ_[p])))
    {L : Finset ℕ} (hL : ∀ ℓ ∈ L, ℓ.Prime) (hpL : p ∉ L) (y : M) (hy0 : y ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Y : K, Y ≠ 0 ∧ ‖(Y : AlgebraicClosure ℚ_[p]) - y‖ < ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ ∧
      (∀ φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[p],
        (∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : K, φ x = h x) ∨
          ‖φ Y - 1‖ < ρ) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), haveI : Fact ℓ.Prime := ⟨hL ℓ hℓ⟩
        ∀ φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ], ‖φ Y - 1‖ < ρ) ∧
      ∀ w : InfinitePlace K, w (Y - 1) < ρ := by
  have hynorm : 0 < ‖(y : AlgebraicClosure ℚ_[p])‖ := norm_pos_iff.mpr (by simpa using hy0)
  obtain ⟨y₀, hy₀K, hy₀⟩ := exists_mem_norm_sub_lt_of_mem_adjoin p K (hMK y.2)
    (ε := ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ / 2) (by positivity)
  obtain ⟨Y, hY0, hYp, hYL, hYinf⟩ := GlobalNumberFields.exists_galois_padic_approximation p K hL
    hpL ⟨y₀, hy₀K⟩ (ρ := min (ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ / 2) ρ)
    (lt_min (by positivity) hρ)
  have hYy : ‖(Y : AlgebraicClosure ℚ_[p]) - y‖ < ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ := by
    calc ‖(Y : AlgebraicClosure ℚ_[p]) - y‖
        = ‖((Y : AlgebraicClosure ℚ_[p]) - y₀) + (y₀ - y)‖ := by ring_nf
      _ ≤ ‖(Y : AlgebraicClosure ℚ_[p]) - y₀‖ + ‖y₀ - (y : AlgebraicClosure ℚ_[p])‖ :=
        norm_add_le _ _
      _ < ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ / 2 + ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ / 2 :=
        add_lt_add (hY0.trans_le (min_le_left _ _)) (by rwa [norm_sub_rev])
      _ = ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ := by ring
  refine ⟨Y, ?_, hYy, fun φ ↦ (hYp φ).imp_right fun h ↦ h.trans_le (min_le_right _ _),
    fun ℓ hℓ φ ↦ (hYL ℓ hℓ φ).trans_le (min_le_right _ _),
    fun w ↦ (hYinf w).trans_le (min_le_right _ _)⟩
  rintro rfl
  have : ‖(y : AlgebraicClosure ℚ_[p])‖ < ρ * ‖(y : AlgebraicClosure ℚ_[p])‖ := by simpa using hYy
  nlinarith [mul_le_of_le_one_left hynorm.le hρ1]

/-- The explicit symbols of the norm `aU` of a global `Y` that is close to `y` at `p` and close to
`1` at the other primes dividing `m` and at the infinite places: at `p` it is that of the local
norm of `y`, at the other primes dividing `m` it is trivial, and `aU` is positive. -/
private theorem cyclotomicSymbol_norm_approx (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ_[p])) [NumberField K]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    (hKM : ∀ x ∈ K, x ∈ M) (hMK : M ≤ IntermediateField.adjoin ℚ_[p] (K : Set _))
    (y : Mˣ) (Y : K) (hY : Y ≠ 0) (aU : ℚˣ) (haU : (aU : ℚ) = Algebra.norm ℚ Y)
    (hYy : ‖(Y : AlgebraicClosure ℚ_[p]) - (y : M)‖ <
      (m : ℝ)⁻¹ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖)
    (hYp : ∀ φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[p],
      (∃ h : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x : K, φ x = h x) ∨
        ‖φ Y - 1‖ < (m : ℝ)⁻¹)
    (hYL : ∀ ℓ (hℓ : ℓ ∈ m.primeFactors.erase p), haveI : Fact ℓ.Prime :=
        ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)⟩
      ∀ φ : K →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ], ‖φ Y - 1‖ < (m : ℝ)⁻¹)
    (hYinf : ∀ w : InfinitePlace K, w (Y - 1) < (m : ℝ)⁻¹) :
    cyclotomicSymbol m p (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom aU) =
        cyclotomicSymbol m p (Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y) ∧
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ m → ℓ ≠ p →
        cyclotomicSymbol m ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom aU) = 1) ∧
      0 < (aU : ℚ) := by
  have hρ1 : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast NeZero.one_le)
  refine ⟨?_, ?_, ?_⟩
  · apply cyclotomicSymbol_eq_of_norm_sub_lt
    have hP := norm_algebraNorm_sub_algebraNorm_lt p K M hKM hMK Y (y : M) y.ne_zero hρ1 hYy hYp
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, haU, eq_ratCast]
    exact hP.trans_le (mul_le_mul_of_nonneg_right (Padic.inv_natCast_le_norm_natCast m)
      (norm_nonneg _))
  · intro ℓ _ hℓm hℓp
    have hℓL : ℓ ∈ m.primeFactors.erase p :=
      Finset.mem_erase.mpr ⟨hℓp, Nat.mem_primeFactors.mpr ⟨Fact.out, hℓm, NeZero.ne m⟩⟩
    apply cyclotomicSymbol_eq_one_of_norm_sub_one_lt
    have h := norm_algebraNorm_sub_one_lt ℓ Y hρ1 (hYL ℓ hℓL)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, haU, eq_ratCast]
    exact h.trans_le (Padic.inv_natCast_le_norm_natCast m)
  · rw [haU]
    refine norm_pos_of_isTotallyPositive hY (isTotallyPositive_iff.mpr fun w hw ↦ ?_)
    have h := mul_pos_of_infinitePlace_sub_lt hw (x := (Y : K)) (y := 1) (by simp)
      ((hYinf w).trans_le hρ1)
    simpa using h

/-- **The explicit symbol at `p` kills local norms.** Let `M` be a finite extension of `ℚ_p` inside
`ℚ_p(μ_m)`. For `y ∈ Mˣ`, every `σ ∈ G_{ℚ_p}` acting on `μ_m` through
`cyclotomicSymbol m p (N_{M/ℚ_p} y)` fixes `M`. -/
theorem cyclotomicSymbol_norm_fixes (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]
    (M : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [FiniteDimensional ℚ_[p] M]
    (hM : M ≤ IntermediateField.adjoin ℚ_[p] {z : AlgebraicClosure ℚ_[p] | z ^ m = 1})
    (y : Mˣ) (σ : Field.absoluteGaloisGroup ℚ_[p])
    (hσ : ∀ z : AlgebraicClosure ℚ_[p], z ^ m = 1 →
      σ.toRingEquiv z =
        z ^ ((cyclotomicSymbol m p (Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y) :
          ZMod m).val))
    (x : M) :
    σ.toRingEquiv (x : AlgebraicClosure ℚ_[p]) = x := by
  -- Intersect `M` with the global cyclotomic field, approximate a local norm by a global norm,
  -- and use the product formula to show that the resulting symbol fixes the intersection.
  refine apply_eq_self_of_forall_mem_adjoin_pow_eq_one m hM σ (fun x hxE hxM ↦ ?_) x
  set u := cyclotomicSymbol m p (Units.map (Algebra.norm ℚ_[p] : M →* ℚ_[p]) y)
  -- The cyclotomic field `E = ℚ(μ_m)` and its subfield `K = E ∩ M`.
  set E := IntermediateField.adjoin ℚ {z : AlgebraicClosure ℚ_[p] | z ^ m = 1}
  have : IsCyclotomicExtension {m} ℚ E :=
    (HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ_[p]) m).choose_spec
      |>.isCyclotomicExtension_adjoin_nth_roots
  have : NumberField E := IsCyclotomicExtension.numberField {m} ℚ E
  have : IsAbelianGalois ℚ E := IsCyclotomicExtension.isAbelianGalois {m} ℚ E
  set K : IntermediateField ℚ (AlgebraicClosure ℚ_[p]) := E ⊓ M.restrictScalars ℚ
  set K' : IntermediateField ℚ E := IntermediateField.restrict (inf_le_left : K ≤ E)
  let e : K ≃ₐ[ℚ] K' := IntermediateField.restrictAlgEquiv _
  have : FiniteDimensional ℚ K := e.symm.toLinearEquiv.finiteDimensional
  have : NumberField K := ⟨⟩
  have : IsGalois ℚ K := IsGalois.of_algEquiv e.symm
  have hMK := le_adjoin_inf_of_le_adjoin_pow_eq_one m hM
  -- A global `Y ∈ K` approximating `y`.
  have hL : ∀ ℓ ∈ m.primeFactors.erase p, ℓ.Prime := fun ℓ hℓ ↦
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)
  obtain ⟨Y, hY, hYy, hYp, hYL, hYinf⟩ := exists_approx_of_le_adjoin p K M hMK hL
    (Finset.notMem_erase p _) (y : M) y.ne_zero (ρ := (m : ℝ)⁻¹)
    (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)))
    (inv_le_one_of_one_le₀ (by exact_mod_cast NeZero.one_le))
  set aU : ℚˣ := Units.mk0 (Algebra.norm ℚ (Y : K)) (Algebra.norm_ne_zero_iff.mpr hY)
  obtain ⟨hpsym, hdvd, hpos⟩ := cyclotomicSymbol_norm_approx p m K M (fun x hx ↦ hx.2) hMK y Y hY
    aU rfl hYy hYp hYL hYinf
  -- The symbols at the primes not dividing `m` fix `K`.
  set T : Subgroup (ZMod m)ˣ := K'.fixingSubgroup.comap
    (IsCyclotomicExtension.Rat.galEquivZMod m E).symm.toMonoidHom
  have hcop : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
      cyclotomicSymbol m ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom aU) ∈ T := by
    intro ℓ _ hℓm
    have hcop := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓm
    rw [cyclotomicSymbol_of_coprime m ℓ hcop]
    have h := NumberField.galEquivZMod_symm_zpow_padicValRat_norm_mem_fixingSubgroup hcop K' (e Y)
    rw [Algebra.norm_eq_of_algEquiv] at h
    simpa [T, aU, Padic.valuation_ratCast] using h
  have huT : u ∈ T := by
    have h := cyclotomicSymbol_mem_of_forall_mem m p T aU hpos hdvd hcop
    rwa [hpsym] at h
  -- On `ℚ(μ_m)`, `σ` is the automorphism with exponent `u`, which fixes `K`.
  set σE : E ≃ₐ[ℚ] E :=
    ((σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).restrictScalars ℚ).restrictNormal
      E
  have hσE (z : E) : (σE z : AlgebraicClosure ℚ_[p]) = σ.toRingEquiv z :=
    AlgEquiv.restrictNormal_commutes _ E z
  have hgal : IsCyclotomicExtension.Rat.galEquivZMod m E σE = u :=
    AlgEquiv.galEquivZMod_restrictNormal _ u hσ
  have hfix := huT
  simp only [T, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ← hgal,
    MulEquiv.symm_apply_apply, IntermediateField.mem_fixingSubgroup_iff] at hfix
  have := hfix ⟨x, hxE⟩ ((IntermediateField.mem_restrict _ _).mpr ⟨hxE, hxM⟩)
  exact (hσE ⟨x, hxE⟩).symm.trans (congrArg Subtype.val this)

end TauCeti
