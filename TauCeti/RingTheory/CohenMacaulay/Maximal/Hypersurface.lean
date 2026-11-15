/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.RingTheory.CohenMacaulay.Maximal.Basic
public import TauCeti.RingTheory.Depth.AuslanderBuchsbaum
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.KrullDimension.Module

/-!
# Maximal Cohen–Macaulay modules over local hypersurfaces

Let `w` be a nonzerodivisor in the maximal ideal of a Noetherian local ring `S`, so that the
hypersurface quotient `R = S ⧸ (w)` is again a Noetherian local ring of Krull dimension
`dim S - 1`. Restriction of scalars along `S → R` preserves the depth of any finite `R`-module
(`IsLocalRing.depth_eq_depth_of_surjective`), so a finite `R`-module `M` is maximal Cohen–Macaulay
over `R` if and only if `dim S ≤ depth_S M + 1`
(`Module.isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ`).

Combined with the Auslander–Buchsbaum formula `pd_S M + depth_S M = depth S`
(`ModuleCat.projectiveDimension_add_depth_eq_depth`), this yields the homological characterization
behind Eisenbud's matrix factorization theorem:

* If `M` is maximal Cohen–Macaulay over `R` and has finite projective dimension over `S`, then
  `pd_S M ≤ 1` (`Module.IsMaximalCohenMacaulay.hasProjectiveDimensionLE_restrictScalars`).
* Conversely, if `S` is Cohen–Macaulay and `pd_S M ≤ 1`, then `M` is maximal Cohen–Macaulay over
  `R` (`Module.isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars`).
* When `S` is a regular local ring and `w ≠ 0`, `S` is Cohen–Macaulay of finite global dimension,
  so a finite `R`-module `M` is maximal Cohen–Macaulay if and only if its restriction of scalars
  to `S` has projective dimension at most `1`
  (`TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE`),
  and for nonzero `M` this projective dimension equals `1`.

## Main results

* `Module.isCohenMacaulay_quotient_span_singleton_iff`: for an `S`-regular element `w` with local
  quotient `S ⧸ (w)`, `S ⧸ (w)` is Cohen–Macaulay if and only if `S` is Cohen–Macaulay.
* `Module.isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ`: maximal
  Cohen–Macaulayness over `S ⧸ (w)` in terms of depth over `S` and `ringKrullDim S`.
* `Module.IsMaximalCohenMacaulay.hasProjectiveDimensionLE_restrictScalars` and
  `Module.isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars`: the two directions
  of the Auslander–Buchsbaum comparison with `pd_S M ≤ 1`.
* `TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE`:
  over a local hypersurface in a regular local ring, maximal Cohen–Macaulayness of a finite module
  is equivalent to projective dimension at most `1` over the ambient regular local ring.
* `TauCeti.IsRegularLocalRing.projectiveDimension_restrictScalars_eq_one_of_isMaximalCohenMacaulay`:
  a nonzero finite maximal Cohen–Macaulay module over `S ⧸ (w)` has projective dimension `1` over
  `S`.

## References

* David Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* Winfried Bruns and Jürgen Herzog, *Cohen–Macaulay Rings*, Cambridge Studies in Advanced
  Mathematics **39** (1993), Theorem 2.1.3 and Section 2.2.
-/

public section

universe v u

open CategoryTheory IsLocalRing
open scoped Pointwise

namespace TauCeti.IsLocalRing

variable {S : Type u} [CommRing S] [_root_.IsLocalRing S] {w : S}

/-- The quotient of a local ring by a principal ideal contained in the maximal ideal is a local
ring. -/
theorem quotient_span_singleton (hwm : w ∈ maximalIdeal S) :
    _root_.IsLocalRing (S ⧸ Ideal.span {w}) := by
  have hne : Ideal.span {w} ≠ ⊤ := fun h ↦
    (maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ (Ideal.span_singleton_le_iff_mem _).2 hwm))
  have : Nontrivial (S ⧸ Ideal.span {w}) := Ideal.Quotient.nontrivial_iff.2 hne
  exact .of_surjective' (Ideal.Quotient.mk (Ideal.span {w})) Ideal.Quotient.mk_surjective

/-- If the quotient `S ⧸ (w)` of a local ring `S` is a local ring (hence nontrivial), then `w` lies
in the maximal ideal of `S`. -/
theorem mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
    [_root_.IsLocalRing (S ⧸ Ideal.span {w})] : w ∈ maximalIdeal S :=
  le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance) (Ideal.mem_span_singleton_self w)

end TauCeti.IsLocalRing

namespace Module

section NoetherianLocal

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

/-- **Cohen–Macaulayness modulo a regular element.** For an `S`-regular element `w` of a Noetherian
local ring `S` with local quotient `S ⧸ (w)`, the hypersurface ring `S ⧸ (w)` is Cohen–Macaulay if
and only if `S` is Cohen–Macaulay. -/
theorem isCohenMacaulay_quotient_span_singleton_iff (hw : IsSMulRegular S w) :
    IsCohenMacaulay (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}) ↔ IsCohenMacaulay S S := by
  have hwm : w ∈ maximalIdeal S :=
    TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
  have hspan : w • (⊤ : Ideal S) = Ideal.span {w} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← isCohenMacaulay_iff_isCohenMacaulay_of_surjective Ideal.Quotient.mk_surjective,
    ← (Submodule.quotEquivOfEq _ _ hspan).isCohenMacaulay_iff,
    isCohenMacaulay_quotSMulTop_iff hw hwm]

/-- The quotient of a Noetherian Cohen–Macaulay local ring by a regular element in the maximal
ideal is Cohen–Macaulay. -/
theorem IsCohenMacaulay.quotient_span_singleton (hS : IsCohenMacaulay S S)
    (hw : IsSMulRegular S w) :
    IsCohenMacaulay (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}) :=
  (isCohenMacaulay_quotient_span_singleton_iff hw).2 hS

variable [Small.{v} S]

/-- Over a Noetherian local ring `S` and an `S`-regular element `w` with local quotient
`R = S ⧸ (w)`, a finite `R`-module `M` is maximal Cohen–Macaulay over `R` if and only if its
restriction of scalars `M_S` satisfies `ringKrullDim S ≤ depth M_S + 1`. -/
theorem isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ
    (hw : IsSMulRegular S w) (M : ModuleCat.{v} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M ↔
      ringKrullDim S ≤
        (depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :
          WithBot ℕ∞) + 1 := by
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) :=
    isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  have hwm : w ∈ maximalIdeal S :=
    TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
  have hdim : ringKrullDim (S ⧸ Ideal.span {w}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hw hwm
  let _ : Module S M := Module.compHom M (Ideal.Quotient.mk (Ideal.span {w}))
  have _ : IsScalarTower S (S ⧸ Ideal.span {w}) M := .of_algebraMap_smul fun _ _ ↦ rfl
  have hdepth : depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) =
      depth (ModuleCat.of (S ⧸ Ideal.span {w}) M) :=
    depth_eq_depth_of_surjective Ideal.Quotient.mk_surjective
  rw [isMaximalCohenMacaulay_iff_ringKrullDim_le_depth, ← hdim, hdepth]
  -- Both `ringKrullDim (S ⧸ (w))` and `1` are non-top in `WithBot ℕ∞`; cancel `+ 1`.
  refine ⟨fun h ↦ by gcongr, fun h ↦ ?_⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S ⧸ Ideal.span {w}) = d := by
    obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast
      (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
    exact ⟨d, (supportDim_self_eq_ringKrullDim (R := S ⧸ Ideal.span {w})).symm.trans hd⟩
  rw [hd] at h ⊢
  induction hdep : depth (ModuleCat.of (S ⧸ Ideal.span {w}) M) using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    rw [hdep] at h
    exact_mod_cast (by exact_mod_cast h : d + 1 ≤ k + 1) |> Nat.le_of_succ_le_succ

/-- For a nonzero finite maximal Cohen–Macaulay module `M` over `S ⧸ (w)`, the depth of `M` over
`S` satisfies `depth_S M + 1 = ringKrullDim S`. -/
theorem IsMaximalCohenMacaulay.depth_restrictScalars_add_one_eq_ringKrullDim
    (hw : IsSMulRegular S w) {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M) :
    (depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :
      WithBot ℕ∞) + 1 = ringKrullDim S := by
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) :=
    isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  have hwm : w ∈ maximalIdeal S :=
    TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
  let _ : Module S M := Module.compHom M (Ideal.Quotient.mk (Ideal.span {w}))
  have _ : IsScalarTower S (S ⧸ Ideal.span {w}) M := .of_algebraMap_smul fun _ _ ↦ rfl
  have hdepth : depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) =
      depth (ModuleCat.of (S ⧸ Ideal.span {w}) M) :=
    depth_eq_depth_of_surjective Ideal.Quotient.mk_surjective
  rw [hdepth, hM.depth_eq]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hw hwm

/-- The `S`-depth of a nonzero finite maximal Cohen–Macaulay `S ⧸ (w)`-module over a Noetherian
local ring is a natural number (equal to `ringKrullDim (S ⧸ (w))`). -/
private theorem IsMaximalCohenMacaulay.exists_depth_restrictScalars_eq_natCast
    {M : ModuleCat.{v} (S ⧸ Ideal.span {w})} [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M) :
    ∃ k : ℕ, (depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :
      WithBot ℕ∞) = k := by
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) :=
    isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast
    (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
  let _ : Module S M := Module.compHom M (Ideal.Quotient.mk (Ideal.span {w}))
  have _ : IsScalarTower S (S ⧸ Ideal.span {w}) M := .of_algebraMap_smul fun _ _ ↦ rfl
  refine ⟨k, ?_⟩
  rw [show depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) =
      depth (ModuleCat.of (S ⧸ Ideal.span {w}) M) from
    depth_eq_depth_of_surjective Ideal.Quotient.mk_surjective, hM.depth_eq,
    ← supportDim_self_eq_ringKrullDim, hk]

/-- **Auslander–Buchsbaum bound for maximal Cohen–Macaulay hypersurface modules.** Let `w` be an
`S`-regular element of a Noetherian local ring `S` with local quotient `S ⧸ (w)`. If a finite
`S ⧸ (w)`-module `M` is maximal Cohen–Macaulay and has finite projective dimension over `S`, then
its projective dimension over `S` is at most `1`. -/
theorem IsMaximalCohenMacaulay.hasProjectiveDimensionLE_restrictScalars
    (hw : IsSMulRegular S w) {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hM : IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M)
    (hpd : projectiveDimension
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) ≠ ⊤) :
    HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  cases subsingleton_or_nontrivial M
  · have : Subsingleton M' := ‹Subsingleton M›
    have hproj : CategoryTheory.Projective M' := (ModuleCat.isZero_of_subsingleton M').projective
    have : HasProjectiveDimensionLE M' 0 :=
      (projective_iff_hasProjectiveDimensionLE_zero M').1 hproj
    exact hasProjectiveDimensionLT_of_ge M' 1 2 (by omega)
  · have : Module.Finite S M' :=
      ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
        Ideal.Quotient.mk_surjective M).2 ‹_›
    have : Nontrivial M' := ‹Nontrivial M›
    have hab := ModuleCat.projectiveDimension_add_depth_eq_depth M' hpd
    have hle : (depth (ModuleCat.of S S) : WithBot ℕ∞) ≤ ringKrullDim S :=
      depth_le_supportDim.trans (by rw [supportDim_self_eq_ringKrullDim])
    have hdimM : (depth M' : WithBot ℕ∞) + 1 = ringKrullDim S :=
      hM.depth_restrictScalars_add_one_eq_ringKrullDim hw
    have hsum : projectiveDimension M' + (depth M' : WithBot ℕ∞) ≤
        (depth M' : WithBot ℕ∞) + 1 :=
      hab.le.trans (hle.trans hdimM.symm.le)
    -- Since `depth M = ringKrullDim (S ⧸ (w))` is a natural number, cancel `depth M'`.
    obtain ⟨k, hk⟩ := hM.exists_depth_restrictScalars_eq_natCast
    have hbot : projectiveDimension M' ≠ ⊥ := by
      rw [ne_eq, projectiveDimension_eq_bot_iff]
      exact fun h ↦ not_subsingleton M' (ModuleCat.subsingleton_of_isZero h)
    obtain ⟨p0, hp0⟩ := WithBot.ne_bot_iff_exists.1 hbot
    have hp0_top : p0 ≠ ⊤ := fun h ↦ hpd (hp0.symm.trans (by rw [h, WithBot.coe_top]))
    obtain ⟨p, rfl⟩ := ENat.ne_top_iff_exists.1 hp0_top
    have hp : p ≤ 1 := by
      rw [← hp0, hk] at hsum
      have hnat : p + k ≤ k + 1 := by exact_mod_cast hsum
      omega
    exact (projectiveDimension_le_iff M' 1).1 (by rw [← hp0]; exact_mod_cast hp)

/-- **Maximal Cohen–Macaulayness from projective dimension at most one.** Over a Noetherian
Cohen–Macaulay local ring `S` and an `S`-regular element `w` with local quotient `S ⧸ (w)`, every
finite `S ⧸ (w)`-module of projective dimension at most `1` over `S` is maximal Cohen–Macaulay
over `S ⧸ (w)`. -/
theorem isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars
    (hS : IsCohenMacaulay S S) (hw : IsSMulRegular S w)
    (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Module.Finite (S ⧸ Ideal.span {w}) M]
    [HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1] :
    IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M := by
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  cases subsingleton_or_nontrivial M
  · exact isMaximalCohenMacaulay_of_subsingleton
  · have : Module.Finite S M' :=
      ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
        Ideal.Quotient.mk_surjective M).2 ‹_›
    have : Nontrivial M' := ‹Nontrivial M›
    have hpd_le : projectiveDimension M' ≤ 1 := by
      simpa only [Nat.cast_one] using (projectiveDimension_le_iff M' 1).2 inferInstance
    have hpd_top : projectiveDimension M' ≠ ⊤ :=
      (lt_of_le_of_lt ((projectiveDimension_le_iff M' 1).2 inferInstance)
        (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top 1))).ne
    have hab := ModuleCat.projectiveDimension_add_depth_eq_depth M' hpd_top
    rw [hS.depth_eq, supportDim_self_eq_ringKrullDim] at hab
    rw [isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ hw, ← hab,
      add_comm]
    change (depth M' : WithBot ℕ∞) + projectiveDimension M' ≤ (depth M' : WithBot ℕ∞) + 1
    gcongr

end NoetherianLocal

end Module

namespace TauCeti.IsRegularLocalRing

variable {S : Type u} [CommRing S] [_root_.IsRegularLocalRing S] {w : S}
  [_root_.IsLocalRing (S ⧸ Ideal.span {w})]

/-- A local hypersurface `S ⧸ (w)` (`w ≠ 0`) in a regular local ring `S` is Cohen–Macaulay. -/
theorem isCohenMacaulay_quotient_span_singleton (hw : w ≠ 0) :
    Module.IsCohenMacaulay (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}) :=
  have := isDomain (R := S)
  isCohenMacaulay.quotient_span_singleton (.of_ne_zero hw)

variable [Small.{v} S]

/-- **Homological characterization of maximal Cohen–Macaulay modules on a hypersurface.** Over a
local hypersurface `S ⧸ (w)` (`w ≠ 0`) in a regular local ring `S`, a finite `S ⧸ (w)`-module `M`
is maximal Cohen–Macaulay if and only if its restriction of scalars to `S` has projective
dimension at most `1`. -/
theorem isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE
    (hw : w ≠ 0) (M : ModuleCat.{v} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M ↔
      HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  have := isDomain (R := S)
  have hreg : IsSMulRegular S w := .of_ne_zero hw
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  refine ⟨fun hM ↦ hM.hasProjectiveDimensionLE_restrictScalars hreg ?_,
    fun _ ↦ Module.isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars
      isCohenMacaulay hreg M⟩
  have : HasProjectiveDimensionLE M' (maximalIdeal S).spanFinrank :=
    hasProjectiveDimensionLE (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge M'
  have hle : projectiveDimension M' ≤ (maximalIdeal S).spanFinrank :=
    (projectiveDimension_le_iff M' _).2 this
  exact (lt_of_le_of_lt hle (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top _))).ne

/-- A nonzero finite maximal Cohen–Macaulay module over a local hypersurface `S ⧸ (w)` (`w ≠ 0`)
in a regular local ring `S` has projective dimension exactly `1` over `S`. -/
theorem projectiveDimension_restrictScalars_eq_one_of_isMaximalCohenMacaulay
    (hw : w ≠ 0) {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M) :
    projectiveDimension
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) = 1 := by
  have := isDomain (R := S)
  have hreg : IsSMulRegular S w := .of_ne_zero hw
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  have : Module.Finite S M' :=
    ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
  have : Nontrivial M' := ‹Nontrivial M›
  have : HasProjectiveDimensionLE M' 1 :=
    (isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE hw M).1 hM
  have hpd_top : projectiveDimension M' ≠ ⊤ :=
    (lt_of_le_of_lt ((projectiveDimension_le_iff M' 1).2 this)
      (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top 1))).ne
  have hab := ModuleCat.projectiveDimension_add_depth_eq_depth M' hpd_top
  have hdimM : (depth M' : WithBot ℕ∞) + 1 = ringKrullDim S :=
    hM.depth_restrictScalars_add_one_eq_ringKrullDim hreg
  rw [depth_eq_ringKrullDim, ← hdimM, add_comm] at hab
  -- Cancel `depth M'` in `WithBot ℕ∞` by lifting `depth M'` to `ℕ`.
  obtain ⟨k, hdep⟩ := hM.exists_depth_restrictScalars_eq_natCast
  have hbot : projectiveDimension M' ≠ ⊥ := by
    rw [ne_eq, projectiveDimension_eq_bot_iff]
    exact fun h ↦ not_subsingleton M' (ModuleCat.subsingleton_of_isZero h)
  obtain ⟨p0, hp0⟩ := WithBot.ne_bot_iff_exists.1 hbot
  have hp0_top : p0 ≠ ⊤ := fun h ↦ hpd_top (hp0.symm.trans (by rw [h, WithBot.coe_top]))
  obtain ⟨p, rfl⟩ := ENat.ne_top_iff_exists.1 hp0_top
  change projectiveDimension M' = 1
  rw [← hp0, hdep] at hab
  rw [← hp0]
  have hnat : k + p = k + 1 := by exact_mod_cast hab
  exact_mod_cast (by omega : p = 1)

end TauCeti.IsRegularLocalRing
