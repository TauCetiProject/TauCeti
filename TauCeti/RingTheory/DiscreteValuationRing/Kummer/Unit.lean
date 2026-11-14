/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.Unramified.Field

/-!
# Adjoining a tame root of a unit to a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K`, let `u` be a unit of `A`, and let `n`
be invertible in `A`. Adjoining an `n`-th root `γ` of `u` to `K` produces a finite separable
extension `L = K(γ)` that is unramified with respect to `A`: `L` is a field quotient of the generic
fibre `K ⊗[A] A[x] ⧸ (x ^ n - u)` of the standard finite étale cover
`TauCeti.standardTameCover A u n`.

Together with the uniformizer root-extraction theorems of
`TauCeti.RingTheory.DiscreteValuationRing.Kummer.Basic`, this splits the root of `u ϖ ^ m` used in
base change of tamely ramified extensions into a tame uniformizer root followed by an unramified
unit root.

## Main results

* `TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_of_pow_eq_of_isUnit`: an extension `L = K(γ)`
  generated over `K` by an `n`-th root of a unit `u` of `A`, with `n` invertible in `A`, is finite
  and separable over `K` and unramified with respect to `A`.
* `TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_adjoin_of_pow_eq_of_isUnit`: the
  adjoined-subfield form for `K(γ)` inside an ambient extension of `K`.
-/

public section

open scoped TensorProduct
open _root_.IntermediateField Polynomial

namespace TauCeti.IsDiscreteValuationRing

variable {A K L : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

omit [_root_.IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- When `L = K(γ)` for an `n`-th root `γ` of `u ∈ A` with `n` invertible in `A`, the generic fibre
`K ⊗[A] A[x]/(x ^ n - u)` maps surjectively onto `L`. -/
private theorem exists_surjective_tensor_standardTameCover {u : A} {n : ℕ} (hn : IsUnit (n : A))
    {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    ∃ χ : K ⊗[A] standardTameCover A u n →ₐ[K] L, Function.Surjective χ := by
  have hn₀ : n ≠ 0 := hn.neZero_natCast.out
  let ψ : standardTameCover A u n →ₐ[A] L :=
    AdjoinRoot.liftAlgHom (X ^ n - C u) (Algebra.ofId A L) γ (by simp [hγ])
  let χ : K ⊗[A] standardTameCover A u n →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) ψ fun _ _ ↦ .all _ _
  refine ⟨χ, ?_⟩
  have hγ_int : IsIntegral K γ :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn₀) (hγ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hadj : Algebra.adjoin K ({γ} : Set L) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic hγ_int.isAlgebraic).mp hgen
  have hmem : γ ∈ χ.range :=
    ⟨1 ⊗ₜ[A] AdjoinRoot.root (X ^ n - C u), by simp [χ, ψ]⟩
  have htop : χ.range = ⊤ :=
    top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem))
  intro x
  have hx : x ∈ χ.range := htop ▸ Algebra.mem_top
  exact (AlgHom.mem_range χ).mp hx

include K in
/-- **Adjoining a tame root of a unit is unramified.** Let `A` be a discrete valuation ring with
fraction field `K`. If `L` is generated over `K` by an `n`-th root `γ` of a unit `u` of `A`, with
`n` invertible in `A`, then `L` is a finite separable extension of `K` that is unramified with
respect to `A`. -/
theorem isUnramifiedWRT_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u) {n : ℕ} (hn : IsUnit (n : A))
    {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    Algebra.IsUnramifiedWRT A L ∧ FiniteDimensional K L ∧ Algebra.IsSeparable K L := by
  have := hn.neZero_natCast
  have := standardTameCover_etale hu hn
  obtain ⟨χ, hχ⟩ := exists_surjective_tensor_standardTameCover hn hγ hgen
  obtain ⟨hfin, hsep⟩ := χ.finiteDimensional_and_isSeparable_of_surjective hχ
  exact ⟨χ.isUnramifiedWRT_of_surjective hχ, hfin, hsep⟩

/-- **Adjoining a tame root of a unit gives an unramified subfield.** Let `A` be a discrete
valuation ring with fraction field `K`. For an `n`-th root `γ` of a unit `u` of `A` in an
extension `L` of `K`, with `n` invertible in `A`, the subfield `K(γ)` is finite and separable over
`K` and unramified with respect to `A`. -/
theorem isUnramifiedWRT_adjoin_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u) {n : ℕ}
    (hn : IsUnit (n : A)) {γ : L} (hγ : γ ^ n = algebraMap A L u) :
    Algebra.IsUnramifiedWRT A K⟮γ⟯ ∧ FiniteDimensional K K⟮γ⟯ ∧ Algebra.IsSeparable K K⟮γ⟯ :=
  isUnramifiedWRT_of_pow_eq_of_isUnit hu hn
    ((AdjoinSimple.gen_pow_eq_algebraMap_iff K).mpr hγ)
    (adjoin_adjoinSimple_gen_eq_top γ)

end TauCeti.IsDiscreteValuationRing
