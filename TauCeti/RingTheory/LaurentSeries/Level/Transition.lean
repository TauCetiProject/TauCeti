/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.PNat.Basic
public import TauCeti.RingTheory.LaurentSeries.Level.Residue

/-!
# Transition maps between ramified Laurent levels and their residues

Let `K` be a field. For positive integers `n ∣ m`, the ramified level `K⸨u_n⸩`, `u_n ^ n = t`,
embeds into the level `K⸨u_m⸩`, `u_m ^ m = t`, by the substitution `u_n = u_m ^ (m / n)`. On
underlying Laurent series it is the expansion `X ↦ X ^ (m / n)`. This file constructs these
transition maps `TauCeti.LaurentSeries.Level.transition K h` as `K⸨t⸩`-algebra maps. They compose,
and under the embeddings of the levels into the Puiseux field they become the inclusions of the
actual levels.

Over every field `K` the transition maps describe all embeddings of levels, up to the Kummer
automorphisms `u_n ↦ η u_n`. If `φ : K⸨u_n⸩ → K⸨u_m⸩` is a `K⸨t⸩`-algebra map, then
`φ(u_n) ^ n = t = u_m ^ m`. Comparing orders gives `n * ord φ(u_n) = m`, so `n ∣ m`, and
`φ(u_n) / u_m ^ (m / n)` is an `n`-th root of unity of `K⸨X⸩`, hence a constant `η ∈ K`.

The residue of a form `x dt` on level `n` is `Res_{u_n} (x dt)`
(`TauCeti.LaurentSeries.Level.residue`). Since `dt = n u_n ^ (n - 1) du_n`, it is `n` times the
rational-exponent residue of `x` in the Puiseux field. The transition maps preserve the latter,
so `Res_{u_m} (x dt) = (m / n) Res_{u_n} (x dt)`. Kummer automorphisms preserve residues, so the
same formula holds along every embedding of levels. For `K` algebraically closed of
characteristic zero, every finite extension of `K⸨t⸩` is a level, which gives the formula
`Res_{L'} (f x dt) = (e' / e) Res_L (x dt)` for an embedding `f : L → L'` of finite extensions of
degrees `e` and `e'`.

## Main definitions

* `TauCeti.LaurentSeries.Level.transition K h`: for `h : n ∣ m`, the transition map from level `n`
  to level `m`, `u_n ↦ u_m ^ (m / n)`.

## Main results

* `TauCeti.LaurentSeries.Level.transition_parameter`: the transition map sends `u_n` to
  `u_m ^ (m / n)`.
* `TauCeti.LaurentSeries.Level.toPuiseux_transition` and
  `TauCeti.LaurentSeries.Level.levelEquiv_transition`: compatibility with the embeddings into the
  Puiseux field and with the inclusions of its actual levels.
* `TauCeti.LaurentSeries.Level.transition_comp_transition`: transition maps compose.
* `TauCeti.LaurentSeries.Level.exists_eq_transition_comp_kummer`: every embedding of level `n`
  into level `m` is a transition map after a Kummer automorphism.
* `TauCeti.LaurentSeries.Level.nonempty_algHom_iff`: level `n` embeds into level `m` over `K⸨t⸩`
  exactly when `n ∣ m`.
* `TauCeti.LaurentSeries.Level.residue_transition` and
  `TauCeti.LaurentSeries.Level.residue_algHom_apply`: `Res_{u_m} = (m / n) Res_{u_n}` along the
  transition map and along every embedding of levels.
* `TauCeti.LaurentSeries.Level.residueOfFinrankEq_algHom_apply`: the same formula
  `Res_{L'} = (e' / e) Res_L` for embeddings of finite extensions of `K⸨t⸩`.
-/

public section

open HahnSeries LaurentSeries Module
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

variable {K : Type*} [Field K] {n m l : ℕ+}

section Transition

variable (K) in
/-- The **transition map** from level `n` to level `m`, for `n ∣ m`: the `K⸨t⸩`-algebra map
`K⸨u_n⸩ → K⸨u_m⸩` substituting `u_n = u_m ^ (m / n)`. On underlying Laurent series it is the
expansion `X ↦ X ^ (m / n)`. -/
noncomputable def transition (h : n ∣ m) : Level K n →ₐ[K⸨X⸩] Level K m where
  toRingHom := (ringEquivLaurentSeries K m).symm.toRingHom.comp
    ((expand K (m.divExact n)).toRingHom.comp (ringEquivLaurentSeries K n).toRingHom)
  commutes' f := (ringEquivLaurentSeries K m).injective <| by
    simp [expand_expand, mul_comm _ n, PNat.mul_div_exact h]

/-- On underlying Laurent series, the transition map is the expansion `X ↦ X ^ (m / n)`. -/
@[simp]
theorem ringEquivLaurentSeries_transition (h : n ∣ m) (x : Level K n) :
    ringEquivLaurentSeries K m (transition K h x) =
      expand K (m.divExact n) (ringEquivLaurentSeries K n x) :=
  (ringEquivLaurentSeries K m).apply_symm_apply _

/-- The transition map substitutes `u_n = u_m ^ (m / n)`. -/
@[simp]
theorem transition_parameter (h : n ∣ m) :
    transition K h (parameter K n) = parameter K m ^ ((m : ℕ) / n) := by
  apply (ringEquivLaurentSeries K m).injective
  simp [single_pow, PNat.coe_divExact h]

/-- Under the embeddings of the levels into the Puiseux field, the transition map from level `n`
to level `m` becomes the identity: both send `u_n` to `t ^ (1 / n)`. -/
theorem toPuiseux_transition (h : n ∣ m) (x : Level K n) :
    toPuiseux K m (transition K h x) = toPuiseux K n x := by
  rw [toPuiseux_apply, toPuiseux_apply, ringEquivLaurentSeries_transition,
    puiseuxField.levelEmbedding_expand_divExact h]

/-- On the actual levels of the Puiseux field, the transition map from level `n` to level `m` is
the inclusion of level `n` into level `m`. -/
@[simp]
theorem levelEquiv_transition (h : n ∣ m) (x : Level K n) :
    puiseuxField.levelEquiv K m (transition K h x) =
      IntermediateField.inclusion (puiseuxField.level_le_level_of_dvd K h)
        (puiseuxField.levelEquiv K n x) := by
  apply Subtype.ext
  rw [puiseuxField.coe_levelEquiv_apply, IntermediateField.coe_inclusion,
    puiseuxField.coe_levelEquiv_apply, toPuiseux_transition]

/-- The transition map from a level to itself is the identity. -/
@[simp]
theorem transition_self : transition K (dvd_refl n) = AlgHom.id K⸨X⸩ (Level K n) :=
  AlgHom.ext fun x ↦ (toPuiseux K n).toRingHom.injective (toPuiseux_transition _ x)

/-- Transition maps compose: the transition from level `n` to level `m`, followed by the
transition from level `m` to level `l`, is the transition from level `n` to level `l`. -/
@[simp]
theorem transition_comp_transition (h₁ : n ∣ m) (h₂ : m ∣ l) :
    (transition K h₂).comp (transition K h₁) = transition K (h₁.trans h₂) :=
  AlgHom.ext fun x ↦ (toPuiseux K l).toRingHom.injective <| by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, toPuiseux_transition]

/-- **Embeddings of levels.** Every `K⸨t⸩`-algebra map `φ` from level `n` to level `m` forces
`n ∣ m`, and is the transition map after the Kummer automorphism `u_n ↦ η u_n` of level `n`
attached to an `n`-th root of unity `η` of `K`. So `φ(u_n) = η u_m ^ (m / n)`. -/
theorem exists_eq_transition_comp_kummer (φ : Level K n →ₐ[K⸨X⸩] Level K m) :
    ∃ (h : n ∣ m) (η : rootsOfUnity n K),
      φ = (transition K h).comp (kummer K n η).toAlgHom := by
  set w : K⸨X⸩ := ringEquivLaurentSeries K m (φ (parameter K n)) with hw_def
  have hw : w ^ (n : ℕ) = single (m : ℤ) 1 := by
    rw [hw_def, ← map_pow, ← map_pow, parameter_pow, AlgHom.commutes, algebraMap_apply,
      expand_single, mul_one]
  -- comparing orders in `w ^ n = t ^ m` gives `n * ord w = m`
  have h : n ∣ m := by
    have hord := congrArg HahnSeries.order hw
    rw [order_pow, order_single one_ne_zero, nsmul_eq_mul] at hord
    exact PNat.dvd_iff.2 (Int.natCast_dvd_natCast.1 ⟨w.order, hord.symm⟩)
  have hk : ((n : ℕ) • (((m : ℕ) / n : ℕ) : ℤ)) = m := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (PNat.dvd_iff.1 h)]
  -- `w / t ^ (m / n)` is an `n`-th root of unity of `K⸨X⸩`, hence a constant
  have hv : (w / single (((m : ℕ) / n : ℕ) : ℤ) 1) ^ (n : ℕ) = 1 := by
    rw [div_pow, hw, single_pow, one_pow, hk, div_self (single_ne_zero one_ne_zero)]
  obtain ⟨η, hη⟩ := exists_rootsOfUnity_algebraMap_eq hv
  refine ⟨h, η, ?_⟩
  -- both maps are determined by their value on the generator `u_n`
  apply (powerBasis K n).algHom_ext
  rw [powerBasis_gen, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    kummer_parameter, map_mul, AlgHom.commutes, transition_parameter]
  apply (ringEquivLaurentSeries K m).injective
  rw [map_mul, algebraMap_apply, AlgHom.commutes, hη]
  simp [single_pow, w]

/-- Level `n` embeds into level `m` over `K⸨t⸩` exactly when `n ∣ m`. -/
theorem nonempty_algHom_iff : Nonempty (Level K n →ₐ[K⸨X⸩] Level K m) ↔ n ∣ m :=
  ⟨fun ⟨φ⟩ ↦ (exists_eq_transition_comp_kummer φ).fst, fun h ↦ ⟨transition K h⟩⟩

end Transition

section Residue

/-- **Residues along transition maps.** For `n ∣ m`, the residue of a form `x dt` on level `m`,
computed in `u_m`, is `m / n` times its residue on level `n`, computed in `u_n`:
`Res_{u_m} (x dt) = (m / n) Res_{u_n} (x dt)`. -/
theorem residue_transition (h : n ∣ m) (x : Level K n) :
    residue K m (transition K h x) = ((m : ℕ) / n) • residue K n x := by
  rw [residue_eq_nsmul_residue_toPuiseux, residue_eq_nsmul_residue_toPuiseux, toPuiseux_transition,
    smul_smul, Nat.div_mul_cancel (PNat.dvd_iff.1 h)]

/-- **Residues along embeddings of levels.** For every `K⸨t⸩`-algebra map `φ` from level `n` to
level `m`, the residue of `φ(x) dt` on level `m` is `m / n` times the residue of `x dt` on level
`n`. -/
@[simp]
theorem residue_algHom_apply (φ : Level K n →ₐ[K⸨X⸩] Level K m) (x : Level K n) :
    residue K m (φ x) = ((m : ℕ) / n) • residue K n x := by
  obtain ⟨h, η, rfl⟩ := exists_eq_transition_comp_kummer φ
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, residue_transition,
    residue_algEquiv_apply]

end Residue

section FiniteExtension

variable [IsAlgClosed K] [CharZero K] {L L' : Type*} [Field L] [Algebra K⸨X⸩ L] [Field L']
  [Algebra K⸨X⸩ L'] {e e' : ℕ+}

/-- **Residues along embeddings of finite extensions.** For `K` algebraically closed of
characteristic zero and an embedding `f : L → L'` of finite extensions of `K⸨t⸩` of degrees `e`
and `e'`, the residue of `f(x) dt` on `L'` is `e' / e` times the residue of `x dt` on `L`. -/
theorem residueOfFinrankEq_algHom_apply (h : finrank K⸨X⸩ L = e) (h' : finrank K⸨X⸩ L' = e')
    (f : L →ₐ[K⸨X⸩] L') (x : L) :
    residueOfFinrankEq h' (f x) = ((e' : ℕ) / e) • residueOfFinrankEq h x := by
  set ψ := algEquivOfFinrankEq h
  rw [residueOfFinrankEq_apply h ψ, residueOfFinrankEq_apply h' (algEquivOfFinrankEq h'),
    ← residue_algHom_apply (((algEquivOfFinrankEq h').toAlgHom.comp f).comp ψ.symm.toAlgHom)]
  simp

end FiniteExtension

end TauCeti.LaurentSeries.Level
