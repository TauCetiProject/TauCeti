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
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.CohenMacaulay.Hypersurface
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.RegularLocalRing.AuslanderBuchsbaum
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Maximal Cohen–Macaulay modules over local hypersurfaces

For an `S`-regular element `w` in the maximal ideal of a Noetherian local ring `S` with quotient
`R = S ⧸ (w)`, scalar restriction preserves depth, so a finite `R`-module `M` is maximal
Cohen–Macaulay over `R` iff `dim S ≤ depth_S M + 1`
(`Module.isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ`), and any
nonzero finite maximal Cohen–Macaulay `R`-module of finite projective dimension over `S` has
projective dimension `1` over `S`
(`Module.IsMaximalCohenMacaulay.projectiveDimension_restrictScalars_eq_one`). Over a regular local
ring `S` (`w ≠ 0`), Auslander–Buchsbaum yields `HasProjectiveDimensionLE M_S 1`
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

namespace Module

section NoetherianLocal

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})] [Small.{v} S]

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
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) := Ideal.Quotient.isNoetherianRing _
  have : Small.{v} (S ⧸ Ideal.span {w}) := small_of_surjective Ideal.Quotient.mk_surjective
  have hwm : w ∈ maximalIdeal S :=
    (Ideal.span {w}).le_maximalIdeal_of_isLocalRing_quotient (Ideal.mem_span_singleton_self w)
  rw [isMaximalCohenMacaulay_iff_ringKrullDim_le_depth,
    ← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hw hwm,
    ModuleCat.depth_restrictScalars_of_surjective _ Ideal.Quotient.mk_surjective]
  refine ⟨fun h ↦ by gcongr, fun h ↦ ?_⟩
  obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast
    (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
  rw [← supportDim_self_eq_ringKrullDim, hd] at h ⊢
  induction hdep : depth M using ENat.recTopCoe with
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
  have : Small.{v} (S ⧸ Ideal.span {w}) := small_of_surjective Ideal.Quotient.mk_surjective
  have hwm : w ∈ maximalIdeal S :=
    (Ideal.span {w}).le_maximalIdeal_of_isLocalRing_quotient (Ideal.mem_span_singleton_self w)
  rw [ModuleCat.depth_restrictScalars_of_surjective _ Ideal.Quotient.mk_surjective, hM.depth_eq]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hw hwm

omit [IsLocalRing S] [IsNoetherianRing S] [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem not_projective_restrictScalars (hw : IsSMulRegular S w)
    (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Nontrivial M] :
    ¬ CategoryTheory.Projective
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) := by
  intro hP
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  have : Module.Projective S M' := (IsProjective.iff_projective M').2 hP
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let m' : M' := m
  have hw_smul : w • m' = w • (0 : M') := by
    have h0 : w • m' = 0 :=
      (ModuleCat.restrictScalars.smul_def (Ideal.Quotient.mk (Ideal.span {w})) w m).trans
        (by rw [Ideal.Quotient.mk_singleton_self]; exact zero_smul (S ⧸ Ideal.span {w}) m)
    rw [h0, smul_zero]
  exact hm (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M')
    (mem_nonZeroDivisors_iff_left.2 fun _ hx ↦ hw (by simpa [smul_eq_mul] using hx)) hw_smul)

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
  · have : IsNoetherianRing (S ⧸ Ideal.span {w}) := Ideal.Quotient.isNoetherianRing _
    have : Small.{v} (S ⧸ Ideal.span {w}) := small_of_surjective Ideal.Quotient.mk_surjective
    have : Module.Finite S M' := ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
    have : Nontrivial M' := ‹Nontrivial M›
    obtain ⟨p, hp⟩ := ModuleCat.exists_projectiveDimension_eq_natCast hpd
    have hp0 : p ≠ 0 := fun h0 ↦ not_projective_restrictScalars hw M <|
      (projective_iff_hasProjectiveDimensionLE_zero M').2 <|
        (projectiveDimension_le_iff M' 0).1 (by dsimp only [M']; simp [hp, h0])
    have h1 : (1 : WithBot ℕ∞) ≤ projectiveDimension M' := by
      dsimp only [M']
      rw [hp]
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp0)
    have hdim_le : ringKrullDim S ≤ (depth (ModuleCat.of S S) : WithBot ℕ∞) := by
      rw [← ModuleCat.projectiveDimension_add_depth_eq_depth M' hpd,
        ← hM.depth_restrictScalars_add_one_eq_ringKrullDim hw, add_comm (depth M' : WithBot ℕ∞)]
      gcongr
    have hS : IsCohenMacaulay S S :=
      isCohenMacaulay_iff_depth_eq.2 <| le_antisymm depth_le_supportDim
        ((supportDim_self_eq_ringKrullDim (R := S)).symm ▸ hdim_le)
    exact TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth hS
      (mem_nonZeroDivisors_iff_left.2 fun _ hx ↦ hw (by simpa [smul_eq_mul] using hx))
      M hpd hM.ringKrullDim_le_depth

/-- A nonzero finite maximal Cohen–Macaulay module over `S ⧸ (w)` (`w` regular) of finite
projective dimension over `S` has projective dimension `1` over `S`. -/
theorem IsMaximalCohenMacaulay.projectiveDimension_restrictScalars_eq_one
    (hw : IsSMulRegular S w) {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hM : IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M)
    (hpd : projectiveDimension
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) ≠ ⊤) :
    projectiveDimension
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) = 1 := by
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  have hle : projectiveDimension M' ≤ 1 := by
    simpa only [Nat.cast_one] using
      (projectiveDimension_le_iff M' 1).2 (hM.hasProjectiveDimensionLE_restrictScalars hw hpd)
  have : Nontrivial M' := ‹Nontrivial M›
  obtain ⟨p, hp⟩ := ModuleCat.exists_projectiveDimension_eq_natCast hpd
  have hp_le : p ≤ 1 := by
    dsimp only [M'] at hle
    rw [hp] at hle
    exact_mod_cast hle
  have hp_ne : p ≠ 0 := fun hp0 ↦ not_projective_restrictScalars hw M <|
    (projective_iff_hasProjectiveDimensionLE_zero M').2 <|
      (projectiveDimension_le_iff M' 0).1 (by dsimp only [M']; simp [hp, hp0])
  have hp1 : p = 1 := by omega
  simp [hp, hp1]

/-- **Maximal Cohen–Macaulayness from projective dimension at most one.** Over a Noetherian
Cohen–Macaulay local ring `S`, every finite `S ⧸ (w)`-module with `pd_S M ≤ 1` is maximal
Cohen–Macaulay over `S ⧸ (w)`. -/
theorem isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars
    (hS : IsCohenMacaulay S S) (hw : IsSMulRegular S w)
    (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Module.Finite (S ⧸ Ideal.span {w}) M]
    [HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1] :
    IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M :=
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) := Ideal.Quotient.isNoetherianRing _
  have : Small.{v} (S ⧸ Ideal.span {w}) := small_of_surjective Ideal.Quotient.mk_surjective
  isMaximalCohenMacaulay_iff_ringKrullDim_le_depth.2 <|
    TauCeti.ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient hS
      (mem_nonZeroDivisors_iff_left.2 fun _ hx ↦ hw (by simpa [smul_eq_mul] using hx))
      M inferInstance

end NoetherianLocal

end Module

namespace TauCeti.IsRegularLocalRing

variable {S : Type u} [CommRing S] [_root_.IsRegularLocalRing S] {w : S}
  [_root_.IsLocalRing (S ⧸ Ideal.span {w})] [Small.{v} S]

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
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) := Ideal.Quotient.isNoetherianRing _
  have : Small.{v} (S ⧸ Ideal.span {w}) := small_of_surjective Ideal.Quotient.mk_surjective
  exact Module.isMaximalCohenMacaulay_iff_ringKrullDim_le_depth.trans
    (TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth
      (mem_nonZeroDivisors_iff_ne_zero.2 hw) M).symm

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
  have hle := (projectiveDimension_le_iff M' (maximalIdeal S).spanFinrank).2
    (hasProjectiveDimensionLE (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge M')
  exact hM.projectiveDimension_restrictScalars_eq_one (.of_ne_zero hw)
    (hle.trans_lt (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top _))).ne

end TauCeti.IsRegularLocalRing
