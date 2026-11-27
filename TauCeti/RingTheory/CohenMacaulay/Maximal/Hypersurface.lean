/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.CohenMacaulay.Maximal.Basic
public import TauCeti.RingTheory.Depth.AuslanderBuchsbaum
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.LocalRing.Quotient

/-!
# Maximal Cohen–Macaulay modules over local hypersurfaces

Let `S` be a Cohen–Macaulay Noetherian local ring, let `w` be a non-zero-divisor of `S` with
`S/(w)` local (equivalently, `w` lies in the maximal ideal), and put `R = S/(w)`. A finitely
generated `R`-module `M` is *maximal Cohen–Macaulay* when `dim R ≤ depth M`; with this
formulation the zero module, whose depth is infinite, is included.

By the Auslander–Buchsbaum formula over `S`, together with `depth_S M = depth_R M` and
`dim R + 1 = dim S`, the depth of `M` measures its projective dimension over `S`:

* if `M` has projective dimension at most one over `S`, then `M` is maximal Cohen–Macaulay over
  `R` (`TauCeti.ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient`,
  `Module.isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars`);
* conversely, a maximal Cohen–Macaulay `R`-module of finite projective dimension over `S` has
  projective dimension at most one over `S`
  (`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth`,
  `Module.IsMaximalCohenMacaulay.hasProjectiveDimensionLE_restrictScalars`), and projective
  dimension `1` when nonzero
  (`Module.IsMaximalCohenMacaulay.projectiveDimension_restrictScalars_eq_one`);
* over a Noetherian local ring `S`, a finite `R`-module is maximal Cohen–Macaulay over `R` iff
  `dim S ≤ depth_S M + 1`
  (`Module.isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ`).

Over a regular local ring every module has finite projective dimension, so the two conditions
agree (`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth` and
`TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE` in
`TauCeti.RingTheory.RegularLocalRing.AuslanderBuchsbaum`). The comparison `depth_S M = depth_R M`
is `ModuleCat.depth_restrictScalars_of_surjective` from `TauCeti.RingTheory.Depth.Basic`.

## Main results

* `TauCeti.ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient`
  and
  `TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth`:
  the two depth implications over a Cohen–Macaulay local ring `S`.
* `Module.isMaximalCohenMacaulay_quotient_span_singleton_iff_ringKrullDim_le_depth_succ`:
  comparison of `IsMaximalCohenMacaulay (S ⧸ (w)) M` with `dim S ≤ depth_S M + 1`.
* `Module.IsMaximalCohenMacaulay.hasProjectiveDimensionLE_restrictScalars`,
  `Module.IsMaximalCohenMacaulay.projectiveDimension_restrictScalars_eq_one`, and
  `Module.isMaximalCohenMacaulay_of_hasProjectiveDimensionLE_restrictScalars`: the hypersurface
  Auslander–Buchsbaum implications in `IsMaximalCohenMacaulay` form.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Cambridge Univ. Press (1993), Theorem 1.3.3
  and Sections 2.1–2.2.
-/

public section

open CategoryTheory IsLocalRing
open ModuleCat (restrictScalars)
open scoped Pointwise

universe v u

namespace TauCeti

variable {S : Type u} [CommRing S] [Small.{v} S] {w : S}
  [_root_.IsLocalRing (S ⧸ Ideal.span {w})] [Small.{v} (S ⧸ Ideal.span {w})]

section CohenMacaulay

variable [_root_.IsLocalRing S] [IsNoetherianRing S]

/-- The Auslander–Buchsbaum formula over `S` for a nonzero finitely generated `S/(w)`-module of
finite projective dimension over `S`, written as `pd_S M + depth_R M = dim R + 1`. -/
private theorem projectiveDimension_add_depth_eq (hS : Module.IsCohenMacaulay S S)
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{v} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Nontrivial M]
    (hpd : projectiveDimension ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) ≠
      ⊤) :
    projectiveDimension ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) +
        (IsLocalRing.depth M : WithBot ℕ∞) = ringKrullDim (S ⧸ Ideal.span {w}) + 1 := by
  have : Module.Finite S ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :=
    ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
  have : Nontrivial ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :=
    inferInstanceAs (Nontrivial M)
  have hwm : w ∈ maximalIdeal S :=
    (Ideal.span {w}).le_maximalIdeal_of_isLocalRing_quotient (Ideal.mem_span_singleton_self w)
  rw [ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hw hwm,
    ← Module.supportDim_self_eq_ringKrullDim, ← hS.depth_eq,
    ← ModuleCat.depth_restrictScalars_of_surjective _ Ideal.Quotient.mk_surjective]
  exact ModuleCat.projectiveDimension_add_depth_eq_depth _ hpd

/-- **Modules of projective dimension at most one over `S` are maximal Cohen–Macaulay over
`S/(w)`.** Let `S` be a Cohen–Macaulay Noetherian local ring and `w` a non-zero-divisor with
`S/(w)` local. A finitely generated `S/(w)`-module of projective dimension at most one over `S`
has depth at least `dim S/(w)`. -/
theorem ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient
    (hS : Module.IsCohenMacaulay S S) (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hM : HasProjectiveDimensionLE
      ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1) :
    ringKrullDim (S ⧸ Ideal.span {w}) ≤ IsLocalRing.depth M := by
  cases subsingleton_or_nontrivial M
  · rw [IsLocalRing.depth_eq_top_of_subsingleton, WithBot.coe_top]
    exact le_top
  have hpd := (projectiveDimension_le_iff _ 1).2 hM
  have h := projectiveDimension_add_depth_eq hS hw M
    ((projectiveDimension_ne_top_iff _).2 ⟨1, hM⟩)
  refine ENat.WithBot.add_le_add_one_right_iff.mp ?_
  rw [← h, add_comm]
  exact add_le_add_right hpd _

/-- **Maximal Cohen–Macaulay modules of finite projective dimension over `S` have projective
dimension at most one.** Let `S` be a Cohen–Macaulay Noetherian local ring and `w` a
non-zero-divisor with `S/(w)` local. A finitely generated `S/(w)`-module of depth at least
`dim S/(w)` whose projective dimension over `S` is finite has projective dimension at most one
over `S`. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth
    (hS : Module.IsCohenMacaulay S S) (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hpd : projectiveDimension ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) ≠
      ⊤)
    (hM : ringKrullDim (S ⧸ Ideal.span {w}) ≤ IsLocalRing.depth M) :
    HasProjectiveDimensionLE ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  cases subsingleton_or_nontrivial M
  · have : Subsingleton ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :=
      inferInstanceAs (Subsingleton M)
    have := (ModuleCat.isZero_of_subsingleton
      ((restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M)).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 _ (by omega)
  have h := projectiveDimension_add_depth_eq hS hw M hpd
  -- The depth is finite, since it is bounded by the dimension of the support.
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℕ∞) = IsLocalRing.depth M := by
    refine ENat.ne_top_iff_exists.mp fun htop ↦ ?_
    have : (IsLocalRing.depth M : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.span {w}) :=
      depth_le_supportDim.trans (Module.supportDim_le_ringKrullDim _ M)
    rw [htop] at this
    exact ringKrullDim_ne_top (le_antisymm le_top (by exact_mod_cast this))
  rw [← projectiveDimension_le_iff]
  rw [← hd, show ((d : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) by norm_cast] at h hM
  refine ENat.WithBot.add_le_add_natCast_right_iff (c := d).mp ?_
  rw [h, Nat.cast_one, add_comm (1 : WithBot ℕ∞)]
  gcongr

end CohenMacaulay

end TauCeti

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
private theorem projectiveDimension_restrictScalars_ne_zero
    (hw : IsSMulRegular S w) (M : ModuleCat.{v} (S ⧸ Ideal.span {w})) [Nontrivial M]
    {p : ℕ}
    (hp : projectiveDimension
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) = p) :
    p ≠ 0 := fun h0 ↦
  ModuleCat.not_projective_restrictScalars_quotient_span_singleton hw M <|
    (projective_iff_hasProjectiveDimensionLE_zero _).2 <|
      (projectiveDimension_le_iff _ 0).1 (by simp [hp, h0])

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
    have hp0 := projectiveDimension_restrictScalars_ne_zero hw M hp
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
      (nonZeroDivisorsLeft_eq_nonZeroDivisors (M₀ := S) ▸ hw.mem_nonZeroSMulDivisors)
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
  have hp_ne := projectiveDimension_restrictScalars_ne_zero hw M hp
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
      (nonZeroDivisorsLeft_eq_nonZeroDivisors (M₀ := S) ▸ hw.mem_nonZeroSMulDivisors)
      M inferInstance

end NoetherianLocal

end Module
