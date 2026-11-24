/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import TauCeti.Data.Nat.Cast.IsUnit
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

open _root_.IntermediateField

namespace TauCeti.IsDiscreteValuationRing

variable {A K L : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

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
  let χ := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K L) (standardTameCoverLift hγ)
  have hχ : Function.Surjective χ :=
    surjective_productLeftAlgHom_standardTameCoverLift_of_adjoin_eq_top (NeZero.ne n) hγ hgen
  exact ⟨χ.isUnramifiedWRT_of_surjective hχ, Module.Finite.of_surjective χ.toLinearMap hχ,
    χ.isSeparable_of_surjective hχ⟩

variable (K) in
/-- **Adjoining a tame root of a unit gives an unramified subfield.** Let `A` be a discrete
valuation ring with fraction field `K`. For an `n`-th root `γ` of a unit `u` of `A` in an
extension `L` of `K`, with `n` invertible in `A`, the subfield `K(γ)` is finite and separable over
`K` and unramified with respect to `A`. -/
theorem isUnramifiedWRT_adjoin_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u) {n : ℕ}
    (hn : IsUnit (n : A)) {γ : L} (hγ : γ ^ n = algebraMap A L u) :
    Algebra.IsUnramifiedWRT A K⟮γ⟯ ∧ FiniteDimensional K K⟮γ⟯ ∧ Algebra.IsSeparable K K⟮γ⟯ :=
  isUnramifiedWRT_of_pow_eq_of_isUnit hu hn
    ((AdjoinSimple.gen_pow_eq_algebraMap_iff (F := K)).mpr hγ)
    (adjoin_adjoinSimple_gen_eq_top γ)

end TauCeti.IsDiscreteValuationRing
