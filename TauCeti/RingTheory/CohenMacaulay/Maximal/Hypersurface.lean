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

For an `S`-regular element `w` in the maximal ideal of a Noetherian local ring `S` with quotient
`R = S ⧸ (w)`, scalar restriction preserves depth, so a finite `R`-module `M` is maximal
Cohen–Macaulay over `R` iff `dim S ≤ depth_S M + 1`
(`Module.isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ`). By
Auslander–Buchsbaum, over a regular local ring `S` (`w ≠ 0`) this is equivalent to
`HasProjectiveDimensionLE M_S 1`
(`TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Cambridge Univ. Press (1993), Sections 2.1–2.2.
-/

public section
universe v u
open CategoryTheory IsLocalRing
open scoped Pointwise

namespace TauCeti.IsLocalRing

variable {S : Type u} [CommRing S] [_root_.IsLocalRing S] {w : S}

/-- The quotient of a local ring by a principal ideal in the maximal ideal is a local ring. -/
theorem quotient_span_singleton (hwm : w ∈ maximalIdeal S) :
    _root_.IsLocalRing (S ⧸ Ideal.span {w}) := by
  have hne : Ideal.span {w} ≠ ⊤ := fun h ↦
    (maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ (Ideal.span_singleton_le_iff_mem _).2 hwm))
  have : Nontrivial (S ⧸ Ideal.span {w}) := Ideal.Quotient.nontrivial_iff.2 hne
  exact .of_surjective' (Ideal.Quotient.mk (Ideal.span {w})) Ideal.Quotient.mk_surjective

/-- If `S ⧸ (w)` is a local ring, then `w` lies in the maximal ideal of `S`. -/
theorem mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
    [_root_.IsLocalRing (S ⧸ Ideal.span {w})] : w ∈ maximalIdeal S :=
  le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance) (Ideal.mem_span_singleton_self w)

end TauCeti.IsLocalRing

namespace Module

section NoetherianLocal

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

/-- **Cohen–Macaulayness modulo a regular element.** For an `S`-regular element `w` of a Noetherian
local ring `S` with local quotient `S ⧸ (w)`, `S ⧸ (w)` is Cohen–Macaulay iff `S` is. -/
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

private theorem depth_restrictScalars_quotient (M : ModuleCat.{v} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) =
      depth (ModuleCat.of (S ⧸ Ideal.span {w}) M) := by
  let _ : Module S M := Module.compHom M (Ideal.Quotient.mk (Ideal.span {w}))
  have _ : IsScalarTower S (S ⧸ Ideal.span {w}) M := .of_algebraMap_smul fun _ _ ↦ rfl
  exact depth_eq_depth_of_surjective Ideal.Quotient.mk_surjective

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalRing (S ⧸ Ideal.span {w})] [Small.{v} S] in
private theorem exists_projectiveDimension_eq_natCast {N : ModuleCat.{v} S} [Nontrivial N]
    (hpd : projectiveDimension N ≠ ⊤) : ∃ p : ℕ, projectiveDimension N = p := by
  have hbot : projectiveDimension N ≠ ⊥ := fun h ↦
    not_subsingleton N (ModuleCat.subsingleton_of_isZero ((projectiveDimension_eq_bot_iff N).1 h))
  obtain ⟨p₀, hp₀⟩ := WithBot.ne_bot_iff_exists.1 hbot
  obtain ⟨p, rfl⟩ := (ENat.ne_top_iff_exists (n := p₀)).1 fun h ↦
    hpd (hp₀.symm.trans (by rw [h, WithBot.coe_top]))
  exact ⟨p, hp₀.symm⟩

/-- Over a Noetherian local ring `S` and an `S`-regular element `w` with local quotient
`R = S ⧸ (w)`, a finite `R`-module `M` is maximal Cohen–Macaulay over `R` iff
`ringKrullDim S ≤ depth_S M + 1`. -/
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
  rw [isMaximalCohenMacaulay_iff_ringKrullDim_le_depth,
    ← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hw hwm,
    depth_restrictScalars_quotient]
  refine ⟨fun h ↦ by gcongr, fun h ↦ ?_⟩
  obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast
    (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
  rw [← supportDim_self_eq_ringKrullDim, hd] at h ⊢
  induction hdep : depth (ModuleCat.of (S ⧸ Ideal.span {w}) M) using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    rw [hdep] at h
    exact_mod_cast Nat.le_of_succ_le_succ (by exact_mod_cast h : d + 1 ≤ k + 1)

/-- For a nonzero finite maximal Cohen–Macaulay module `M` over `S ⧸ (w)`,
`depth_S M + 1 = ringKrullDim S`. -/
theorem IsMaximalCohenMacaulay.depth_restrictScalars_add_one_eq_ringKrullDim
    (hw : IsSMulRegular S w) {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M) :
    (depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :
      WithBot ℕ∞) + 1 = ringKrullDim S := by
  rw [depth_restrictScalars_quotient, hM.depth_eq]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hw
    TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton

private theorem IsMaximalCohenMacaulay.exists_depth_restrictScalars_eq_natCast
    {M : ModuleCat.{v} (S ⧸ Ideal.span {w})} [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M) :
    ∃ k : ℕ, (depth ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :
      WithBot ℕ∞) = k := by
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) :=
    isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast
    (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
  exact ⟨k, by rw [depth_restrictScalars_quotient, hM.depth_eq,
    ← supportDim_self_eq_ringKrullDim, hk]⟩

/-- **Auslander–Buchsbaum bound for maximal Cohen–Macaulay hypersurface modules.** If a finite
maximal Cohen–Macaulay `S ⧸ (w)`-module `M` has finite projective dimension over `S`, then
`pd_S M ≤ 1`. -/
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
    have : HasProjectiveDimensionLE M' 0 := (projective_iff_hasProjectiveDimensionLE_zero M').1
      (ModuleCat.isZero_of_subsingleton M').projective
    exact hasProjectiveDimensionLT_of_ge M' 1 2 (by omega)
  · have : Module.Finite S M' := ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
    have : Nontrivial M' := ‹Nontrivial M›
    have hsum : projectiveDimension M' + (depth M' : WithBot ℕ∞) ≤ (depth M' : WithBot ℕ∞) + 1 :=
      (ModuleCat.projectiveDimension_add_depth_eq_depth M' hpd).le.trans <|
        (depth_le_supportDim.trans (supportDim_self_eq_ringKrullDim (R := S)).le).trans
          (hM.depth_restrictScalars_add_one_eq_ringKrullDim hw).symm.le
    obtain ⟨k, hk⟩ := hM.exists_depth_restrictScalars_eq_natCast
    obtain ⟨p, hp⟩ := exists_projectiveDimension_eq_natCast hpd
    rw [hp, hk] at hsum
    have hnat : p + k ≤ k + 1 := by exact_mod_cast hsum
    exact (projectiveDimension_le_iff M' 1).1 (hp ▸ by exact_mod_cast (by omega : p ≤ 1))

/-- **Maximal Cohen–Macaulayness from projective dimension at most one.** Over a Noetherian
Cohen–Macaulay local ring `S`, every finite `S ⧸ (w)`-module with `pd_S M ≤ 1` is maximal
Cohen–Macaulay over `S ⧸ (w)`. -/
theorem isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars
    (hS : IsCohenMacaulay S S) (hw : IsSMulRegular S w)
    (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Module.Finite (S ⧸ Ideal.span {w}) M]
    [HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1] :
    IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M := by
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  cases subsingleton_or_nontrivial M
  · exact isMaximalCohenMacaulay_of_subsingleton
  · have : Module.Finite S M' := ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
    have : Nontrivial M' := ‹Nontrivial M›
    have hpd_le : projectiveDimension M' ≤ 1 := by
      simpa only [Nat.cast_one] using (projectiveDimension_le_iff M' 1).2 inferInstance
    have hab := ModuleCat.projectiveDimension_add_depth_eq_depth M'
      (hpd_le.trans_lt (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top 1))).ne
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
is maximal Cohen–Macaulay iff `HasProjectiveDimensionLE M_S 1`. -/
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
  have hle := (projectiveDimension_le_iff M' (maximalIdeal S).spanFinrank).2
    (hasProjectiveDimensionLE (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge M')
  exact (hle.trans_lt (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top _))).ne

/-- A nonzero finite maximal Cohen–Macaulay module over a local hypersurface `S ⧸ (w)` (`w ≠ 0`)
in a regular local ring `S` has projective dimension `1` over `S`. -/
theorem projectiveDimension_restrictScalars_eq_one_of_isMaximalCohenMacaulay
    (hw : w ≠ 0) {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M) :
    projectiveDimension
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) = 1 := by
  have := isDomain (R := S)
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  have : Module.Finite S M' := ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
    Ideal.Quotient.mk_surjective M).2 ‹_›
  have : Nontrivial M' := ‹Nontrivial M›
  have hle := (projectiveDimension_le_iff M' 1).2
    ((isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE hw M).1 hM)
  have hpd_top : projectiveDimension M' ≠ ⊤ :=
    (hle.trans_lt (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top 1))).ne
  have hab := ModuleCat.projectiveDimension_add_depth_eq_depth M' hpd_top
  rw [depth_eq_ringKrullDim, ← hM.depth_restrictScalars_add_one_eq_ringKrullDim (.of_ne_zero hw),
    add_comm] at hab
  obtain ⟨k, hdep⟩ := hM.exists_depth_restrictScalars_eq_natCast
  obtain ⟨p, hp⟩ := Module.exists_projectiveDimension_eq_natCast hpd_top
  change projectiveDimension M' = 1
  rw [hp, hdep] at hab
  have hnat : k + p = k + 1 := by exact_mod_cast hab
  exact hp.trans (by exact_mod_cast (by omega : p = 1))

end TauCeti.IsRegularLocalRing
