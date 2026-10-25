/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Regular.ProjectiveDimension
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.RingTheory.LocalRing.ProjectiveDimension
import TauCeti.RingTheory.Regular.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Global dimension of regular rings

Let `R` be a regular ring of finite Krull dimension `d`. Every `R`-module, finitely generated or
not, has projective dimension at most `d`. For a regular local ring the bound is attained by the
residue field, so the global dimension of a regular local ring is its Krull dimension.

Conversely (Serre), a Noetherian local ring whose residue field has finite projective dimension
is regular. Together with the bound above, a Noetherian local ring has finite global dimension
exactly when it is regular.

## Main results

* `TauCeti.IsRegularLocalRing.hasProjectiveDimensionLE`: over a regular local ring of dimension
  at most `n`, every module has projective dimension at most `n`.
* `TauCeti.IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal_eq_ringKrullDim`: the
  residue field of a regular local ring has projective dimension exactly the dimension of the
  ring.
* `TauCeti.IsRegularRing.hasProjectiveDimensionLE`: over a regular ring of dimension at most `n`,
  every module has projective dimension at most `n`.
* `ModuleCat.projectiveDimension_le_ringKrullDim`: over a regular ring, the
  projective dimension of every module is at most the Krull dimension of the ring.
* `TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`: a Noetherian local ring whose residue
  field has finite projective dimension is regular.
* `TauCeti.isRegularLocalRing_iff_projectiveDimension_ne_top`: a Noetherian local ring is regular
  exactly when its residue field has finite projective dimension.

## Proof

For a finite module `M` over a regular local ring `R` of dimension `d + 1`, choose a parameter
`x ∈ 𝔪 \ 𝔪²`, so that `R ⧸ (x)` is regular of dimension `d`, and a finite free presentation
`0 → N → P → M → 0`. As `R` is a domain, `x` is regular on `N ⊆ P`. By induction `N ⧸ x N` has
projective dimension at most `d` over `R ⧸ (x)`, hence at most `d + 1` over `R` by change of
rings, while `pd_R (N ⧸ x N) = pd_R N + 1`. So `pd_R N ≤ d` and `pd_R M ≤ d + 1`. Cyclic modules
are finite, and their projective dimensions bound those of all modules by Baer's criterion. For a
regular ring the projective dimension of a finite module is the supremum of those of its
localizations at maximal ideals, and these localizations are regular local rings of dimension at
most that of the ring.

For the converse, induct on a bound `n` for the projective dimension of the residue field `κ`.
If `𝔪` is an associated prime of `R`, a finite module of finite projective dimension is free, so
`κ` is free and `R` is a field. Otherwise prime avoidance gives a nonzerodivisor `x ∈ 𝔪 \ 𝔪²`.
From `0 → 𝔪 → R → κ → 0`, the projective dimension of `𝔪` is at most `n - 1`. As `x` is regular
on `𝔪`, the projective dimension of `𝔪 ⧸ x 𝔪` over `R ⧸ (x)` is also at most `n - 1`. The residue
field of `R ⧸ (x)` is a direct summand of `𝔪 ⧸ x 𝔪`, so `R ⧸ (x)` is regular by induction. Then
`𝔪` needs at most `dim (R ⧸ (x)) + 1 = dim R` generators.

## References

* [Stacks Project, Section 10.110](https://stacks.math.columbia.edu/tag/00O7), Rings of finite
  global dimension: Proposition 10.110.1 (00O7), Proposition 10.110.5 (00OC) and
  Lemma 10.110.8 (00OE).
* [Stacks Project, Lemma 10.109.12](https://stacks.math.columbia.edu/tag/065T), reducing the
  global dimension to cyclic modules.
* H. Matsumura, *Commutative Ring Theory*, Section 19 (Regular rings), Theorem 19.2 for the
  converse.
-/

public section

universe v u

open CategoryTheory IsLocalRing Ideal Pointwise _root_.IsRegularLocalRing

namespace TauCeti

namespace IsRegularLocalRing

/-- The induction proving `TauCeti.IsRegularLocalRing.hasProjectiveDimensionLE_of_finite`, on the
exact dimension of the ring. -/
private theorem hasProjectiveDimensionLE_of_ringKrullDim_eq (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [Small.{v} R], ringKrullDim R = d →
      ∀ (M : ModuleCat.{v} R) [Module.Finite R M], HasProjectiveDimensionLE M d := by
  induction d with
  | zero =>
    intro R _ _ _ hd M _
    -- A regular local ring of dimension zero is a field, over which every module is projective.
    have hm : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp
        (by exact_mod_cast (spanFinrank_maximalIdeal (R := R)).trans hd)
    let := (isField_iff_maximalIdeal_eq.mpr hm).toField
    have : Module.Free R M := Module.Free.of_divisionRing R M
    have : Module.Projective R M := Module.Projective.of_free
    exact projective_iff_hasProjectiveDimensionLT_one.mp M.projective_of_categoryTheory_projective
  | succ d ih =>
    intro R _ _ _ hd M _
    -- A parameter `x ∈ 𝔪 \ 𝔪²` is a nonzerodivisor, and `R ⧸ (x)` is regular of dimension `d`.
    obtain ⟨x, hxm, hx, -⟩ :=
      TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R := R)
        (by rw [hd]; exact_mod_cast d.succ_pos)
    have hreg : x ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_of_ne_zero (by rintro rfl; exact hx (zero_mem _))
    have := quotient_span_singleton hxm hx
    have hd' : ringKrullDim (R ⧸ span {x}) = d := by
      have := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        hreg hxm
      rwa [hd, Nat.cast_succ, ENat.WithBot.add_one_cancel] at this
    have : Small.{v} (R ⧸ span {x}) := small_of_surjective Ideal.Quotient.mk_surjective
    -- A finite free presentation `0 → N → P → M → 0`, with `x` regular on `N ⊆ P`.
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    let N := LinearMap.ker f
    have hNreg : IsSMulRegular N x :=
      (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := P) hreg).submodule N x
    -- By induction and change of rings, `N ⧸ x N` has projective dimension at most `d + 1`.
    let L := N ⧸ span {x} • (⊤ : Submodule R N)
    have : IsScalarTower R (R ⧸ span {x}) L :=
      (Module.isTorsionBySet_quotient_ideal_smul N (span {x})).isScalarTower
    have : Module.Finite (R ⧸ span {x}) L := Module.Finite.of_restrictScalars_finite R _ _
    have := ih (R ⧸ span {x}) hd' (ModuleCat.of (R ⧸ span {x}) L)
    have : HasProjectiveDimensionLE (ModuleCat.of R L) (d + 1) :=
      ModuleCat.hasProjectiveDimensionLE_of_isScalarTower_quotient hreg d L
    -- As `pd_R (N ⧸ x N) = pd_R N + 1`, the kernel `N` has projective dimension at most `d`.
    have hN : HasProjectiveDimensionLE (ModuleCat.of R N) d := by
      have hQ : projectiveDimension (ModuleCat.of R (QuotSMulTop x N)) ≤ (d + 1 : ℕ) := by
        rw [projectiveDimension_le_iff]
        exact hasProjectiveDimensionLT_of_iso
          (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤)).toModuleIso
            (d + 1 + 1)
      rw [ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R N)
        x hNreg hxm, Nat.cast_succ, ENat.WithBot.add_le_add_one_right_iff] at hQ
      exact (projectiveDimension_le_iff _ d).mp hQ
    exact hS.hasProjectiveDimensionLT_X₃ (d + 1) hN
      (hasProjectiveDimensionLT_of_ge _ 1 (d + 1 + 1) (by omega))

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [Small.{v} R]

/-- Over a regular local ring of dimension at most `n`, every finite module has projective
dimension at most `n`. -/
theorem hasProjectiveDimensionLE_of_finite {n : ℕ} (hn : ringKrullDim R ≤ n)
    (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjectiveDimensionLE M n := by
  have hd := (spanFinrank_maximalIdeal (R := R)).symm
  have := hasProjectiveDimensionLE_of_ringKrullDim_eq _ R hd M
  have hle : (maximalIdeal R).spanFinrank ≤ n := by exact_mod_cast hd ▸ hn
  exact hasProjectiveDimensionLT_of_ge _ ((maximalIdeal R).spanFinrank + 1) (n + 1) (by omega)

/-- **The global dimension of a regular local ring is at most its dimension.** Over a regular
local ring of dimension at most `n`, every module, finitely generated or not, has projective
dimension at most `n`. -/
theorem hasProjectiveDimensionLE {n : ℕ} (hn : ringKrullDim R ≤ n) (M : ModuleCat.{v} R) :
    HasProjectiveDimensionLE M n :=
  ModuleCat.hasProjectiveDimensionLE_of_quotients n (fun I ↦
    have : Module.Finite R (Shrink.{v} (R ⧸ I)) :=
      Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
    hasProjectiveDimensionLE_of_finite hn _) M

/-- **The residue field of a regular local ring has projective dimension equal to the dimension
of the ring.** A minimal generating family of the maximal ideal is a regular sequence, whose
quotient has projective dimension its length. Together with
`TauCeti.IsRegularLocalRing.hasProjectiveDimensionLE`, the global dimension of a regular local
ring is its Krull dimension. -/
theorem projectiveDimension_quotient_maximalIdeal_eq_ringKrullDim :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) = ringKrullDim R := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have hrs : ofList s.toList = maximalIdeal R := by simpa [Ideal.ofList] using hspan
  have hreg := isRegular_of_ofList_eq_maximalIdeal hrs (by simp [hcard])
  rw [← spanFinrank_maximalIdeal (R := R), ← hcard, ← Finset.length_toList,
    ← ModuleCat.projectiveDimension_quotient_eq_length s.toList hreg]
  refine projectiveDimension_eq_of_iso (LinearEquiv.toModuleIso ?_)
  exact (Shrink.linearEquiv R _).trans
    ((Submodule.quotEquivOfEq _ _ hrs.symm).trans (Shrink.linearEquiv R _).symm)

end IsRegularLocalRing

namespace IsRegularRing

variable {R : Type u} [CommRing R] [IsRegularRing R] [Small.{v} R]

/-- **The global dimension of a regular ring is at most its dimension.** Over a regular ring of
Krull dimension at most `n`, every module, finitely generated or not, has projective dimension at
most `n`. -/
theorem hasProjectiveDimensionLE {n : ℕ} (hn : ringKrullDim R ≤ n) (M : ModuleCat.{v} R) :
    HasProjectiveDimensionLE M n := by
  refine ModuleCat.hasProjectiveDimensionLE_of_quotients n (fun I ↦ ?_) M
  have : Module.Finite R (Shrink.{v} (R ⧸ I)) :=
    Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
  -- Test on the localizations at maximal ideals, which are regular local of dimension `≤ n`.
  refine (ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n _).mpr fun m ↦ ?_
  have : Small.{v} (Localization.AtPrime m.1) := small_of_surjective Localization.mkHom_surjective
  have : Small.{v} (LocalizedModule m.1.primeCompl (Shrink.{v} (R ⧸ I))) :=
    small_of_surjective (IsLocalizedModule.mk'_surjective m.1.primeCompl
      (LocalizedModule.mkLinearMap m.1.primeCompl (Shrink.{v} (R ⧸ I))))
  have : Module.Finite (Localization.AtPrime m.1)
      ((ModuleCat.of R (Shrink.{v} (R ⧸ I))).localizedModule m.1.primeCompl) :=
    Module.Finite.equiv (Shrink.linearEquiv (Localization.AtPrime m.1) _).symm
  refine IsRegularLocalRing.hasProjectiveDimensionLE_of_finite ?_ _
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m.1]
  exact Ideal.height_le_ringKrullDim_of_isPrime.trans hn

/-- Over a regular ring, the projective dimension of every module is at most the Krull dimension
of the ring. -/
theorem _root_.ModuleCat.projectiveDimension_le_ringKrullDim (M : ModuleCat.{v} R) :
    projectiveDimension M ≤ ringKrullDim R := by
  induction h : ringKrullDim R with
  | bot =>
    -- The ring is zero, so every module is zero.
    have : Subsingleton R := ringKrullDim_eq_bot_iff_subsingleton.mp h
    have : Subsingleton M := Module.subsingleton R M
    exact (projectiveDimension_eq_bot_iff M).mpr (ModuleCat.isZero_of_subsingleton M) ▸ le_rfl
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      exact (projectiveDimension_le_iff M n).mpr (hasProjectiveDimensionLE (h ▸ le_rfl) M)

end IsRegularRing

/-! ### Serre's theorem: finite projective dimension of the residue field -/

namespace IsRegularLocalRing

/-- A Noetherian local ring over which the residue field is projective is a field, hence
regular. -/
private theorem of_projective_residueField {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Small.{v} R] [Module.Projective R (Shrink.{v} (R ⧸ maximalIdeal R))] :
    IsRegularLocalRing R := by
  -- `𝔪` kills the residue field, whose annihilator is zero as it is free and nonzero.
  have : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    Module.Finite.equiv (Shrink.linearEquiv R _).symm
  have : Module.Free R (Shrink.{v} (R ⧸ maximalIdeal R)) := Module.free_of_flat_of_isLocalRing
  have hm : maximalIdeal R = ⊥ := by
    rw [← (Module.annihilator_eq_bot (M := Shrink.{v} (R ⧸ maximalIdeal R))).mpr inferInstance,
      (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).annihilator_eq, Ideal.annihilator_quotient]
  refine of_spanFinrank_maximalIdeal_le R ?_
  rw [hm, Submodule.spanFinrank_bot, Nat.cast_zero]
  exact ringKrullDim_nonneg_of_nontrivial

/-- The induction proving `TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`, on the bound
for the projective dimension of the residue field. -/
private theorem of_hasProjectiveDimensionLE_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R],
      HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) n →
        IsRegularLocalRing R := by
  induction n with
  | zero =>
    intro R _ _ _ _ h
    have : Projective (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr h
    have : Module.Projective R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
      (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))).projective_of_module_projective
    exact of_projective_residueField
  | succ n ih =>
    intro R _ _ _ _ h
    have : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
      Module.Finite.equiv (Shrink.linearEquiv R _).symm
    by_cases hm : maximalIdeal R ∈ associatedPrimes R R
    · -- In depth zero the residue field is free, so `R` is a field.
      have := Module.free_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes hm
        (n + 1) (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
      exact of_projective_residueField
    -- Otherwise choose a nonzerodivisor `x ∈ 𝔪 \ 𝔪²`; then `R ⧸ (x)` is regular by induction.
    obtain ⟨x, hxm, hx2, hx⟩ :=
      TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors hm
    have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr fun h ↦
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hxm))
    have := IsLocalRing.of_surjective' (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective
    have : Small.{v} (R ⧸ span {x}) := small_of_surjective Ideal.Quotient.mk_surjective
    have := ih (R ⧸ span {x})
      (TauCeti.IsLocalRing.hasProjectiveDimensionLE_residueField_quotient hxm hx2 hx)
    -- Finally `𝔪` needs at most `dim (R ⧸ (x)) + 1 = dim R` generators.
    refine of_spanFinrank_maximalIdeal_le R ?_
    have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      hx hxm
    rw [← hdim, ← spanFinrank_maximalIdeal (R := R ⧸ span {x}),
      ← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact_mod_cast TauCeti.IsLocalRing.spanFinrank_maximalIdeal_le_spanFinrank_map_quotient_add_one
      (maximalIdeal R).fg_of_isNoetherianRing hxm

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

/-- **Serre's theorem.** A Noetherian local ring whose residue field has finite projective
dimension is a regular local ring. Its dimension is then that projective dimension, by
`TauCeti.IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal_eq_ringKrullDim`. -/
@[stacks 00OC]
theorem of_hasProjectiveDimensionLE (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) n] :
    IsRegularLocalRing R :=
  of_hasProjectiveDimensionLE_aux n R ‹_›

end IsRegularLocalRing

/-- **A Noetherian local ring is regular exactly when its residue field has finite projective
dimension.** -/
theorem isRegularLocalRing_iff_projectiveDimension_ne_top {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R] :
    IsRegularLocalRing R ↔
      projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≠ ⊤ := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · rw [IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal_eq_ringKrullDim]
    exact ringKrullDim_ne_top
  · obtain ⟨n, _⟩ := (projectiveDimension_ne_top_iff _).mp h
    exact IsRegularLocalRing.of_hasProjectiveDimensionLE n

end TauCeti
