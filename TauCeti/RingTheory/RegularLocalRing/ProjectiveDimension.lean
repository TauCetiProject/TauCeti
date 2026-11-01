/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.Flat.ProjectiveDimension
public import TauCeti.RingTheory.GlobalDimension
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
import TauCeti.RingTheory.RegularLocalRing.OfQuotient

/-!
# Global dimension of regular rings

Let `R` be a regular ring of finite Krull dimension `d`. Every `R`-module, finitely generated or
not, has projective dimension at most `d`. For a regular local ring the bound is attained by the
residue field, so the global dimension of a regular local ring is its Krull dimension.

Conversely (Serre), a Noetherian local ring whose residue field has finite projective dimension
is regular. Together with the bound above, a Noetherian local ring has finite global dimension
exactly when it is regular. As localization does not increase the global dimension, every
localization of a regular local ring at a prime is again a regular local ring, so a regular local
ring is a regular ring in Mathlib's sense.

## Main results

* `TauCeti.IsRegularLocalRing.hasProjectiveDimensionLE`: over a regular local ring of dimension
  at most `n`, every module has projective dimension at most `n`.
* `TauCeti.IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal_eq_ringKrullDim`: the
  residue field of a regular local ring has projective dimension exactly the dimension of the
  ring.
* `TauCeti.IsRegularLocalRing.globalDimension_eq_ringKrullDim`: the global dimension of a regular
  local ring is its Krull dimension.
* `TauCeti.IsRegularRing.hasProjectiveDimensionLE`: over a regular ring of dimension at most `n`,
  every module has projective dimension at most `n`.
* `ModuleCat.projectiveDimension_le_ringKrullDim`: over a regular ring, the
  projective dimension of every module is at most the Krull dimension of the ring.
* `TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`: a Noetherian local ring whose residue
  field has finite projective dimension is regular.
* `TauCeti.isRegularLocalRing_iff_projectiveDimension_ne_top`: a Noetherian local ring is regular
  exactly when its residue field has finite projective dimension.
* `TauCeti.isRegularLocalRing_iff_globalDimension_lt_top`: a Noetherian local ring is regular
  exactly when its global dimension is finite.
* `TauCeti.isRegularRing_of_globalDimension_lt_top`: a Noetherian ring of finite global dimension
  is a regular ring.
* `TauCeti.isRegularRing_of_isRegularLocalRing`: a regular local ring is a regular ring, so its
  localizations at primes are regular local rings (an instance).
* `TauCeti.IsRegularRing.projectiveDimension_le_ringKrullDim_of_faithfullyFlat`: if a regular
  ring `R` is faithfully flat over a Noetherian ring `A`, every finite `A`-module has projective
  dimension at most `dim R`.

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
field of `R ⧸ (x)` is a direct summand of `𝔪 ⧸ x 𝔪`, so `R ⧸ (x)` is regular by induction, and
regularity lifts along the nonzerodivisor `x`
(`TauCeti.IsRegularLocalRing.of_quotient_nonZeroDivisor`).

Along a faithfully flat map `A → R` from a Noetherian ring, base change preserves the projective
dimension of finite modules (`ModuleCat.projectiveDimension_tensorProduct`), so the bound over a
regular ring `R` also bounds the finite `A`-modules. For a flat local
homomorphism of Noetherian local rings and the residue field of `A`, this is the finite projective
dimension from which Serre's characterization of regular local rings deduces that `A` is regular
(H. Matsumura, *Commutative Ring Theory*, Theorem 23.7 (i)).

## References

* [Stacks Project, Section 10.110](https://stacks.math.columbia.edu/tag/00O7), Rings of finite
  global dimension: Proposition 10.110.1 (00O7), Proposition 10.110.5 (00OC),
  Lemma 10.110.6 (0AFS) and Lemma 10.110.8 (00OE).
* [Stacks Project, Lemma 10.109.12](https://stacks.math.columbia.edu/tag/065T), reducing the
  global dimension to cyclic modules.
* H. Matsumura, *Commutative Ring Theory*, Section 19 (Regular rings), Theorem 19.2 for the
  converse.
* The names and shapes of the global-dimension criteria follow Nailin Guan's Mathlib pull request
  [mathlib4#29802](https://github.com/leanprover-community/mathlib4/pull/29802),
  `Mathlib/RingTheory/RegularLocalRing/Localization.lean`.
-/

public section

universe v u w

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

/-- **The global dimension of a regular local ring is its Krull dimension.** The upper bound is
Stacks, Proposition 10.110.1 (00O7); the residue field attains it. -/
@[stacks 00O7]
theorem globalDimension_eq_ringKrullDim : globalDimension.{v} R = ringKrullDim R := by
  refine le_antisymm ?_ ?_
  · rw [← spanFinrank_maximalIdeal (R := R)]
    exact (globalDimension_le_iff_hasProjectiveDimensionLE R _).mpr
      (hasProjectiveDimensionLE (spanFinrank_maximalIdeal (R := R)).ge)
  · rw [← projectiveDimension_quotient_maximalIdeal_eq_ringKrullDim.{v}]
    exact ModuleCat.projectiveDimension_le_globalDimension _

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
    -- Regularity lifts along the nonzerodivisor `x`.
    exact of_quotient_nonZeroDivisor R hxm hx

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

namespace IsRegularLocalRing

/-- A regular local ring has finite global dimension. -/
theorem globalDimension_lt_top {R : Type u} [CommRing R] [IsRegularLocalRing R] [Small.{v} R] :
    globalDimension.{v} R < ⊤ := by
  rw [globalDimension_eq_ringKrullDim]
  exact ringKrullDim_lt_top

/-- **Serre's theorem, global dimension form.** A Noetherian local ring of finite global dimension
is a regular local ring: its residue field has finite projective dimension. -/
theorem of_globalDimension_lt_top {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (h : globalDimension.{v} R < ⊤) : IsRegularLocalRing R :=
  isRegularLocalRing_iff_projectiveDimension_ne_top.mpr
    ((ModuleCat.projectiveDimension_le_globalDimension _).trans_lt h).ne

end IsRegularLocalRing

/-- **A Noetherian local ring is regular exactly when its global dimension is finite.** The
global dimension is then the Krull dimension
(`TauCeti.IsRegularLocalRing.globalDimension_eq_ringKrullDim`). -/
@[stacks 0AFS "first sentence"]
theorem isRegularLocalRing_iff_globalDimension_lt_top {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Small.{v} R] : IsRegularLocalRing R ↔ globalDimension.{v} R < ⊤ :=
  ⟨fun _ ↦ IsRegularLocalRing.globalDimension_lt_top, IsRegularLocalRing.of_globalDimension_lt_top⟩

/-- **A Noetherian ring of finite global dimension is a regular ring.** Its localizations at
primes have global dimension at most that of the ring, so they are regular local rings. -/
@[stacks 00OE "(1) ⇒ (2), without the equality of dimensions"]
theorem isRegularRing_of_globalDimension_lt_top {R : Type u} [CommRing R] [IsNoetherianRing R]
    [Small.{v} R] (h : globalDimension.{v} R < ⊤) : IsRegularRing R := by
  refine isRegularRing_iff.mpr fun p _ ↦ ?_
  have : Small.{v} (Localization.AtPrime p) := small_of_surjective Localization.mkHom_surjective
  exact IsRegularLocalRing.of_globalDimension_lt_top
    ((Submonoid.globalDimension_localization_le p.primeCompl).trans_lt h)

/-- **A regular local ring is a regular ring**: its localizations at all primes are regular local
rings (Stacks, Lemma 10.110.6 (0AFS)). With Mathlib's instance
`IsRegularRing.isRegularLocalRing_localization`, this makes `Localization.AtPrime p` a regular
local ring for every prime `p` of a regular local ring. For any other localization `S` at `p`,
use `TauCeti.Excellence.mem_regularLocus_iff_of_isLocalization` with
`TauCeti.Excellence.regularLocus_eq_univ`. -/
@[stacks 0AFS "second sentence"]
instance isRegularRing_of_isRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R :=
  isRegularRing_of_globalDimension_lt_top IsRegularLocalRing.globalDimension_lt_top.{u}

section FaithfullyFlat

variable {A : Type w} [CommRing A] [IsNoetherianRing A] {R : Type u} [CommRing R]
  [Algebra A R] [Module.FaithfullyFlat A R]

/-- If a regular ring `R` is faithfully flat over a Noetherian ring `A`, every finite `A`-module
has projective dimension at most `dim R`. Since a regular local ring is a regular ring
(`TauCeti.isRegularRing_of_isRegularLocalRing`), this applies to a flat local homomorphism
`A → R` of Noetherian local rings with `R` regular (`Module.FaithfullyFlat.of_flat_of_isLocalHom`).
-/
theorem IsRegularRing.projectiveDimension_le_ringKrullDim_of_faithfullyFlat [IsRegularRing R]
    [Small.{v} A] (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    projectiveDimension (ModuleCat.of A M) ≤ ringKrullDim R := by
  have : Small.{max u v} R := small_max R
  rw [← ModuleCat.projectiveDimension_tensorProduct R M]
  exact ModuleCat.projectiveDimension_le_ringKrullDim _

end FaithfullyFlat

end TauCeti
