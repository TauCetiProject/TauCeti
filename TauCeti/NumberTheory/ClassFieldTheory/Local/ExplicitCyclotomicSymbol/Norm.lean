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
    (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ_[p]) m).choose_spec
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
  set ρ : ℝ := (m : ℝ)⁻¹
  have hρ0 : 0 < ρ := inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast NeZero.one_le)
  have hy0 : (y : M) ≠ 0 := y.ne_zero
  have hynorm : 0 < ‖((y : M) : AlgebraicClosure ℚ_[p])‖ :=
    norm_pos_iff.mpr (by simp)
  obtain ⟨y₀, hy₀K, hy₀⟩ := exists_mem_norm_sub_lt_of_mem_adjoin p K (hMK (y : M).2)
    (ε := ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ / 2) (by positivity)
  set L := m.primeFactors.erase p
  have hL : ∀ ℓ ∈ L, ℓ.Prime := fun ℓ hℓ ↦
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)
  obtain ⟨Y, hY0, hYp, hYL, hYinf⟩ :=
    GlobalNumberFields.exists_galois_padic_approximation p K hL (Finset.notMem_erase p _)
      ⟨y₀, hy₀K⟩ (ρ := min (ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ / 2) ρ)
      (lt_min (by positivity) hρ0)
  have hYy : ‖(Y : AlgebraicClosure ℚ_[p]) - (y : M)‖ <
      ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ := by
    calc ‖(Y : AlgebraicClosure ℚ_[p]) - (y : M)‖
        = ‖((Y : AlgebraicClosure ℚ_[p]) - y₀) + (y₀ - (y : M))‖ := by ring_nf
      _ ≤ ‖(Y : AlgebraicClosure ℚ_[p]) - y₀‖ + ‖y₀ - ((y : M) : AlgebraicClosure ℚ_[p])‖ :=
        norm_add_le _ _
      _ < ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ / 2 +
          ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ / 2 :=
        add_lt_add (hY0.trans_le (min_le_left _ _)) (by rwa [norm_sub_rev])
      _ = ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ := by ring
  have hY : (Y : K) ≠ 0 := by
    rintro rfl
    have : ‖((y : M) : AlgebraicClosure ℚ_[p])‖ < ρ * ‖((y : M) : AlgebraicClosure ℚ_[p])‖ := by
      simpa using hYy
    nlinarith
  set aU : ℚˣ := Units.mk0 (Algebra.norm ℚ (Y : K)) (Algebra.norm_ne_zero_iff.mpr hY)
  -- The symbol at `p`.
  have hpsym : cyclotomicSymbol m p (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom aU) = u := by
    apply cyclotomicSymbol_eq_of_norm_sub_lt
    have hP := norm_algebraNorm_sub_algebraNorm_lt p K M (fun x hx ↦ hx.2) hMK Y (y : M) hy0
      hρ1 hYy fun φ ↦ (hYp φ).imp_right fun h ↦ h.trans_le (min_le_right _ _)
    simp only [aU, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, eq_ratCast]
    exact hP.trans_le (mul_le_mul_of_nonneg_right (Padic.inv_natCast_le_norm_natCast m)
      (norm_nonneg _))
  -- The symbols at the primes `ℓ ≠ p` dividing `m` are trivial.
  have hdvd : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ m → ℓ ≠ p →
      cyclotomicSymbol m ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom aU) = 1 := by
    intro ℓ _ hℓm hℓp
    have hℓL : ℓ ∈ L :=
      Finset.mem_erase.mpr ⟨hℓp, Nat.mem_primeFactors.mpr ⟨Fact.out, hℓm, NeZero.ne m⟩⟩
    apply cyclotomicSymbol_eq_one_of_norm_sub_one_lt
    have h := norm_algebraNorm_sub_one_lt ℓ (Y : K) hρ1
      fun φ ↦ (hYL ℓ hℓL φ).trans_le (min_le_right _ _)
    simp only [aU, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, eq_ratCast]
    exact h.trans_le (Padic.inv_natCast_le_norm_natCast m)
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
  -- The real symbol is trivial.
  have hpos : 0 < (aU : ℚ) := by
    refine norm_pos_of_isTotallyPositive hY (isTotallyPositive_iff.mpr fun w hw ↦ ?_)
    have h := mul_pos_of_infinitePlace_sub_lt hw (x := (Y : K)) (y := 1) (by simp)
      ((hYinf w).trans_le ((min_le_right _ _).trans hρ1))
    simpa using h
  have huT : u ∈ T := hpsym ▸ cyclotomicSymbol_mem_of_forall_mem m p T aU hpos hdvd hcop
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
