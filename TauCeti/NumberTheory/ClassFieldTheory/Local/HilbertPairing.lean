/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.LocalH2Bound
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Nondegeneracy of the local Hilbert pairing

Let `K` be a nonarchimedean local field containing a primitive `n`-th root of unity `ζ`, with `n`
invertible in `K`. The local symbol `(a, b)`, the cup product of the Kummer classes of `a` and `b`
along `kummerCupPairing ζ hζ` followed by an identification `H²(G_K, μₙ) ≃+ ZMod n`, is a
`ZMod n`-bilinear pairing on `H¹(G_K, μₙ) ≃ Kˣ / (Kˣ)ⁿ`. This file proves that it is separating in
the second variable: `b` pairs to zero with every `a` exactly when `b` is an `n`-th power.

The argument is Serre's. Let `L = K(ⁿ√b)`. By the symbol–norm criterion
(`localSymbol_eq_zero_iff_mem_normGroup`) every `a` pairs to zero with `b` exactly when every
`a ∈ Kˣ` is a norm from `L`. The extension `L/K` is cyclic, so by the cyclic norm index
`[Kˣ : N_{L/K}(Lˣ)] = [L : K]` (`TauCeti.index_normGroup_of_isCyclic`) this forces `L = K`, that
is, `b` is an `n`-th power in `K`. No reciprocity is used, and the identification
`H²(G_K, μₙ) ≃+ ZMod n` is arbitrary.

## Main results

* `TauCeti.mem_powerSubgroup_of_normGroup_eq_top`: if a finite radical extension `L = K(s)` with
  `sⁿ = b` has `normGroup K L = ⊤`, then `b ∈ (Kˣ)ⁿ`.
* `TauCeti.ClassFieldTheory.forall_localSymbol_kummerClass_eq_zero_iff`: `(a, b) = 0` for every
  `a ∈ Kˣ` exactly when `b ∈ (Kˣ)ⁿ`.
* `TauCeti.ClassFieldTheory.separatingRight_localSymbol`: the local symbol along
  `kummerCupPairing ζ hζ` is separating in its second variable on `H¹(G_K, μₙ)`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §2.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.IntermediateField Module

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)

include hζ in
/-- **Serre's radical norm-top criterion.** Let `K` be a nonarchimedean local field containing a
primitive `n`-th root of unity `ζ`. If a finite radical extension `L = K(s)` with `sⁿ = b`
(`b ∈ Kˣ`) has full norm subgroup `N_{L/K}(Lˣ) = Kˣ`, then `[L : K] = 1` and `b ∈ (Kˣ)ⁿ`. -/
theorem _root_.TauCeti.mem_powerSubgroup_of_normGroup_eq_top {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] {b : Kˣ} {s : L} (hs : s ^ n = algebraMap K L b) (hgen : K⟮s⟯ = ⊤)
    (hnorm : normGroup K L = ⊤) :
    b ∈ powerSubgroup Kˣ n := by
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  set E := ι.fieldRange
  let e : L ≃ₐ[K] E := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  have hs' : (e s) ^ n = algebraMap K E b := by
    rw [← map_pow, hs, AlgEquiv.commutes]
  have hgen' : K⟮e s⟯ = ⊤ := by
    rw [← AlgEquiv.coe_toAlgHom, ← Set.image_singleton, ← adjoin_map, hgen, eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, trivial, rfl⟩
  have hnorm' : normGroup K E = ⊤ :=
    eq_top_iff.2 (hnorm.ge.trans e.symm.toAlgHom.normGroup_le_normGroup)
  let _ := algebraicExtensionValuativeRel K E
  let _ := algebraicExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := algebraicExtension_valuativeExtension K E
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ hs' hgen'
  have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ hs' hgen'
  have h1 : finrank K E = 1 := by
    rw [← index_normGroup_of_isCyclic K E, hnorm', Subgroup.index_top]
  obtain ⟨c, -, hcb⟩ := exists_pow_finrank_eq_algebraMap hζ hs' hgen'
  rw [h1, Nat.div_one] at hcb
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero (by rw [← hcb, zero_pow (NeZero.ne n)])
  exact (mem_powerSubgroup_iff n).2 ⟨Units.mk0 c hc0, Units.ext (by simpa using hcb)⟩

variable (tr : continuousCohomology 2 (muNRep n K) ≃+ ZMod n)

/-- **Nondegeneracy of the Hilbert pairing in the second variable.** Let `K` be a nonarchimedean
local field containing a primitive `n`-th root of unity `ζ`. Then `b ∈ Kˣ` pairs to zero under
the local symbol along `kummerCupPairing ζ hζ` with every `a ∈ Kˣ` exactly when `b` is an `n`-th
power. The identification `tr : H²(G_K, μₙ) ≃+ ZMod n` is arbitrary, and the Kummer classes use
the invertibility of `n` in `K` supplied by `ζ`. -/
theorem forall_localSymbol_kummerClass_eq_zero_iff (b : Kˣ) :
    (∀ a : Kˣ, localSymbol (kummerCupPairing ζ hζ) tr (kummerClass K hζ.neZero'.out.isUnit a)
        (kummerClass K hζ.neZero'.out.isUnit b) = 0) ↔
      b ∈ powerSubgroup Kˣ n := by
  have hn : IsUnit (n : K) := hζ.neZero'.out.isUnit
  refine ⟨fun h ↦ ?_, fun h a ↦ by rw [(kummerClass_eq_zero_iff K hn).2 h, map_zero]⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) b)
    (Nat.pos_of_neZero n)
  have : FiniteDimensional K K⟮s⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have ht : AdjoinSimple.gen K s ^ n = algebraMap K K⟮s⟯ b := Subtype.ext (by simpa using hs)
  have htop := adjoin_adjoinSimple_gen_eq_top (F := K) s
  exact mem_powerSubgroup_of_normGroup_eq_top hζ ht htop
    (eq_top_iff.2 fun a _ ↦ (localSymbol_eq_zero_iff_mem_normGroup hζ tr hn a b ht htop).1 (h a))

/-- **The Hilbert pairing is separating in the second variable.** For a nonarchimedean local field
`K` containing a primitive `n`-th root of unity `ζ`, with `n` invertible in `K`, the only class
`y ∈ H¹(G_K, μₙ)` with `(x, y) = 0` for every `x` under the local symbol along
`kummerCupPairing ζ hζ` is `y = 0`. The identification `tr : H²(G_K, μₙ) ≃+ ZMod n` is
arbitrary, and `n` is invertible in `K` because `K` contains a primitive `n`-th root of unity. -/
theorem separatingRight_localSymbol :
    (localSymbol (kummerCupPairing ζ hζ) tr).SeparatingRight := by
  have hn : IsUnit (n : K) := hζ.neZero'.out.isUnit
  intro y hy
  obtain ⟨b, rfl⟩ := kummerClass_surjective K hn y
  exact (kummerClass_eq_zero_iff K hn).2
    ((forall_localSymbol_kummerClass_eq_zero_iff hζ tr b).1 fun a ↦ hy _)

end TauCeti.ClassFieldTheory
