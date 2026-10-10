/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import TauCeti.Analysis.Normed.Algebra.NoSmallSubgroups
public import TauCeti.NumberTheory.LocalField.Norm.Open
public import TauCeti.NumberTheory.LocalField.Unramified.Basic

import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.NumberTheory.LocalField.Norm.Unramified.Basic

/-!
# Local conductors

Let `K` be a nonarchimedean local field with unit filtration `U(K,n)`. The steps `U(K,n)` form a
basis of open neighbourhoods of `1` in `Kˣ` consisting of subgroups, so every open subgroup of
`Kˣ` contains one of them, and so does the kernel of every continuous character `Kˣ → ℂˣ`. The
least such step is the conductor.

* For a finite separable extension `L/K` the norm group `N_{L/K}(Lˣ)` is open, and the
  **conductor exponent** `c(L/K)` is the least `n` with `U(K,n) ⊆ N_{L/K}(Lˣ)`. The
  **conductor** of `L/K` is the ideal `𝔪_K ^ c(L/K)` of `𝒪[K]`.
* For a continuous character `χ : Kˣ → ℂˣ`, the **character conductor exponent** is the least `n`
  with `U(K,n) ⊆ ker χ`. Attainment uses that `ℂˣ` has no small subgroups: continuity alone does
  not suffice, as the identity of `Kˣ` is trivial on no step of the filtration.

Both are attained minima (`unitFiltration_conductorExponent_le_normGroup`,
`unitFiltration_characterConductorExp_le_ker`), characterized by `conductorExponent_le_iff` and
`characterConductorExp_le_iff`.

The conductor detects ramification. If `L/K` is unramified, the norm maps the units of `L` onto
those of `K`, so the conductor exponent is `0`. Conversely, for a finite **abelian** extension,
local reciprocity gives `[Kˣ : N_{L/K}(Lˣ)] = [L : K]`. If the units of `K` are norms, the norm
group contains every element whose valuation is a multiple of the residue degree `f`, since the
norm of a uniformizer of `L` has valuation `f`. Its index is then at most `f`, so `[L : K] = f`
and `L/K` is unramified (`conductorExponent_eq_zero_iff`). The abelian hypothesis cannot be
dropped: by norm limitation a nonabelian extension has the norm group of its maximal abelian
subextension, which may be unramified while the extension itself is not.

## Main definitions

* `TauCeti.ClassFieldTheory.conductorExponent K L`: the least `n` with `U(K,n) ⊆ N_{L/K}(Lˣ)`.
* `TauCeti.ClassFieldTheory.conductorIdeal K L`: the conductor `𝔪_K ^ c(L/K)` of `L/K`.
* `TauCeti.ClassFieldTheory.characterConductorExp K χ`: the least `n` with `U(K,n) ⊆ ker χ`.

## Main results

* `TauCeti.ClassFieldTheory.conductorExponent_le_iff`: `c(L/K) ≤ n` exactly when
  `U(K,n) ⊆ N_{L/K}(Lˣ)`.
* `TauCeti.ClassFieldTheory.conductorExponent_eq_zero_of_isUnramified`: an unramified extension
  has conductor exponent `0`.
* `TauCeti.ClassFieldTheory.conductorExponent_eq_zero_iff`: a finite abelian extension has
  conductor exponent `0` exactly when it is unramified.
* `TauCeti.ClassFieldTheory.characterConductorExp_le_iff`: the character conductor exponent of
  `χ` is at most `n` exactly when `χ` is trivial on `U(K,n)`.

## References

* J.-P. Serre, *Local Fields*, Chapter XV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public section

noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti.ClassFieldTheory

/-! ### The conductor of a finite extension -/

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

open Classical in
/-- The **conductor exponent** of a finite separable extension `L/K` of a nonarchimedean local
field: the least `n` such that the step `U(K,n)` of the unit filtration consists of norms from
`L`. Such an `n` exists because the norm group is open (`exists_unitFiltration_le_normGroup`), so
the minimum is attained (`unitFiltration_conductorExponent_le_normGroup`). -/
def conductorExponent : ℕ :=
  Nat.find (exists_unitFiltration_le_normGroup (K := K) (L := L))

/-- The **conductor** of a finite separable extension `L/K` of a nonarchimedean local field: the
ideal `𝔪_K ^ c(L/K)` of `𝒪[K]`, where `c(L/K)` is the conductor exponent. -/
def conductorIdeal : Ideal 𝒪[K] :=
  𝓂[K] ^ conductorExponent K L

/-- The conductor is the power of the maximal ideal given by the conductor exponent. -/
theorem conductorIdeal_def : conductorIdeal K L = 𝓂[K] ^ conductorExponent K L :=
  (rfl)

/-- The conductor is the unit ideal exactly when the conductor exponent is `0`. -/
@[simp]
theorem conductorIdeal_eq_top_iff : conductorIdeal K L = ⊤ ↔ conductorExponent K L = 0 := by
  simp [conductorIdeal_def, (maximalIdeal.isMaximal 𝒪[K]).ne_top]

/-- **The conductor exponent is attained**: `U(K, c(L/K))` consists of norms from `L`. -/
theorem unitFiltration_conductorExponent_le_normGroup :
    unitFiltration K (conductorExponent K L) ≤ normGroup K L :=
  open Classical in Nat.find_spec (exists_unitFiltration_le_normGroup (K := K) (L := L))

/-- **The characterizing property of the conductor exponent**: `c(L/K) ≤ n` exactly when every
element of `U(K,n)` is a norm from `L`. -/
theorem conductorExponent_le_iff {n : ℕ} :
    conductorExponent K L ≤ n ↔ unitFiltration K n ≤ normGroup K L :=
  ⟨fun h ↦ (unitFiltration_antitone h).trans (unitFiltration_conductorExponent_le_normGroup K L),
    fun h ↦ open Classical in Nat.find_min' _ h⟩

/-! ### Ramification and the conductor -/

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

/-- **An unramified extension has conductor exponent `0`**: its norm maps the units of `L` onto
the units of `K`. -/
theorem conductorExponent_eq_zero_of_isUnramified [IsUnramified K L] :
    conductorExponent K L = 0 := by
  have h : unitFiltration K 0 ≤ normGroup K L := by
    rw [← map_normUnits_unitFiltration K L 0]
    rintro _ ⟨y, -, rfl⟩
    exact mem_normGroup_iff.2 ⟨y, by simp⟩
  exact Nat.eq_zero_of_le_zero ((conductorExponent_le_iff K L).2 h)

end Extension

/-! ### The unramified criterion for abelian extensions -/

section Abelian

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [IsAbelianGalois K L]

/-- **A finite abelian extension with conductor exponent `0` is unramified.** -/
theorem isUnramified_of_conductorExponent_eq_zero
    (h : conductorExponent K L = 0) : IsUnramified K L := by
  have hU : unitFiltration K 0 ≤ normGroup K L := (conductorExponent_le_iff K L).1 h.le
  have hf := inertiaDegree_pos (K := K) (L := L)
  have hdvd := Subgroup.index_dvd_of_le (comap_zmultiples_inertiaDegree_le_normGroup hU)
  rw [Subgroup.index_comap_of_surjective _ normalizedValuation_surjective,
    AddSubgroup.index_toSubgroup, Int.index_zmultiples, Int.natAbs_natCast,
    index_normGroup_of_isMulCommutative, ← ramificationIndex_mul_inertiaDegree K L] at hdvd
  rw [isUnramified_iff_ramificationIndex_eq_one]
  exact Nat.dvd_one.mp <| (Nat.mul_dvd_mul_iff_right hf).mp (by rwa [one_mul])

/-- **The unramified criterion for the conductor**: a finite abelian extension of nonarchimedean
local fields has conductor exponent `0`, that is, every unit of `K` is a norm, exactly when it is
unramified. -/
@[simp]
theorem conductorExponent_eq_zero_iff :
    conductorExponent K L = 0 ↔ IsUnramified K L :=
  ⟨isUnramified_of_conductorExponent_eq_zero K L,
    fun _ ↦ conductorExponent_eq_zero_of_isUnramified K L⟩

end Abelian

/-! ### The conductor of a character -/

section Character

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A continuous character `Kˣ → ℂˣ` is trivial on a step of the unit filtration: the steps are
arbitrarily small subgroups, and `ℂˣ` has no small subgroups. -/
theorem exists_unitFiltration_le_ker (χ : Kˣ →ₜ* ℂˣ) : ∃ n, unitFiltration K n ≤ χ.ker := by
  obtain ⟨N, hN, hNker⟩ := χ.exists_mem_nhds_one_forall_le_ker
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_one_unitFiltration.mem_iff.mp hN
  exact ⟨n, hNker _ hn⟩

/-- The **conductor exponent of a continuous character** `χ : Kˣ → ℂˣ`: the least `n` such that
`χ` is trivial on the step `U(K,n)` of the unit filtration. The minimum is attained
(`unitFiltration_characterConductorExp_le_ker`). -/
def characterConductorExp (χ : Kˣ →ₜ* ℂˣ) : ℕ :=
  sInf {n : ℕ | unitFiltration K n ≤ χ.ker}

/-- **The character conductor exponent is attained**: `χ` is trivial on
`U(K, characterConductorExp K χ)`. -/
theorem unitFiltration_characterConductorExp_le_ker (χ : Kˣ →ₜ* ℂˣ) :
    unitFiltration K (characterConductorExp K χ) ≤ χ.ker :=
  Nat.sInf_mem (exists_unitFiltration_le_ker K χ)

/-- **The characterizing property of the character conductor exponent**: it is at most `n`
exactly when `χ` is trivial on `U(K,n)`. -/
theorem characterConductorExp_le_iff (χ : Kˣ →ₜ* ℂˣ) {n : ℕ} :
    characterConductorExp K χ ≤ n ↔ unitFiltration K n ≤ χ.ker :=
  ⟨fun h ↦ (unitFiltration_antitone h).trans (unitFiltration_characterConductorExp_le_ker K χ),
    fun h ↦ Nat.sInf_le h⟩

/-- A continuous character has conductor exponent `0` exactly when it is **unramified**, that is,
trivial on the units `U(K,0)` of `𝒪[K]`. -/
@[simp]
theorem characterConductorExp_eq_zero_iff (χ : Kˣ →ₜ* ℂˣ) :
    characterConductorExp K χ = 0 ↔ unitFiltration K 0 ≤ χ.ker := by
  rw [← Nat.le_zero, characterConductorExp_le_iff]

end Character

end TauCeti.ClassFieldTheory
