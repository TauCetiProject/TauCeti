/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.RingTheory.Depth.AuslanderBuchsbaum
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.Algebra.Homology.Ext.Equivalence
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Auslander–Buchsbaum depth criterion over a local hypersurface

Let `(S, 𝔪)` be a regular local ring and `w` a nonzerodivisor of `S` such that `R = S ⧸ (w)` is
local (equivalently `w ∈ 𝔪`). Combining Serre's finite-global-dimension bound over `S` with the
Auslander–Buchsbaum formula `pd_S M + depth_R M = depth S = dim S = dim R + 1` characterizes when a
finitely generated `R`-module has projective dimension at most one over `S` in terms of maximal
depth over `R`.

## Main results

* `TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth`: for a
  finitely generated `S ⧸ (w)`-module `M`, `pd_S M ≤ 1 ↔ ringKrullDim (S ⧸ (w)) ≤ depth M`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Corollary 6.3.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys and
  Monographs **262**, American Mathematical Society (2021), Lemma 4.2.2.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Theorem 1.3.3 and Section 3.3.
-/

public section

universe v u

open CategoryTheory Ideal

namespace TauCeti

/-- **Auslander–Buchsbaum criterion for projective dimension one over a local hypersurface.** Let
`S` be a regular local ring and `w` a nonzerodivisor such that `R = S ⧸ (w)` is local (equivalently
`w ∈ 𝔪_S`). A finitely generated `R`-module `M` has projective dimension at most one over `S` if
and only if `dim R ≤ depth M` (maximal Cohen–Macaulayness). -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth
    {S : Type u} [CommRing S] [IsRegularLocalRing S] [Small.{v} S] {w : S}
    [_root_.IsLocalRing (S ⧸ span {w})] [Small.{v} (S ⧸ span {w})]
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{v} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M) 1 ↔
      ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) := by
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M
  cases subsingleton_or_nontrivial M
  · have hZ : Limits.IsZero M' :=
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).map_isZero
        (ModuleCat.isZero_of_subsingleton M)
    have := hZ.hasProjectiveDimensionLT_zero
    exact iff_of_true (hasProjectiveDimensionLT_of_ge M' 0 2 (by omega))
      (by rw [_root_.IsLocalRing.depth_eq_top_of_subsingleton M]; exact le_top)
  have hwm : w ∈ _root_.IsLocalRing.maximalIdeal S := by
    by_contra h
    exact not_subsingleton (S ⧸ span {w}) (Ideal.Quotient.subsingleton_iff.mpr
      (span_singleton_eq_top.mpr (_root_.IsLocalRing.notMem_maximalIdeal.mp h)))
  -- View `M` as an `S`-module through the standard quotient algebra so `IsScalarTower` applies.
  let : Module S M := Module.compHom M (algebraMap S (S ⧸ span {w}))
  have : IsScalarTower S (S ⧸ span {w}) M := .of_compHom S (S ⧸ span {w}) M
  have : Module.Finite S M := Module.Finite.trans (S ⧸ span {w}) M
  let MS : ModuleCat.{v} S := ModuleCat.of S M
  have hpd_iso : projectiveDimension M' = projectiveDimension MS :=
    projectiveDimension_eq_of_iso (ModuleCat.restrictScalarsAlgebraMapIso M)
  let d := (_root_.IsLocalRing.maximalIdeal S).spanFinrank
  have hdS : ringKrullDim S = d :=
    (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).symm
  have hpd_top : projectiveDimension MS ≠ ⊤ :=
    (((projectiveDimension_le_iff MS d).mpr
      (IsRegularLocalRing.hasProjectiveDimensionLE hdS.le MS)).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))).ne
  have hpd_bot : projectiveDimension MS ≠ ⊥ := fun h ↦ by
    have : Subsingleton MS :=
      ModuleCat.subsingleton_of_isZero ((projectiveDimension_eq_bot_iff MS).mp h)
    exact not_subsingleton M this
  have hab := ModuleCat.projectiveDimension_add_depth_eq_depth MS hpd_top
  have hdimQ : ringKrullDim (S ⧸ span {w}) + 1 = d :=
    (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hw hwm).trans
      hdS
  lift projectiveDimension MS to ℕ∞ using hpd_bot with e
  lift e to ℕ using fun h ↦ hpd_top (by simp [h]) with p
  lift _root_.IsLocalRing.depth M to ℕ using fun h ↦
    not_subsingleton M ((_root_.IsLocalRing.depth_eq_top_iff M).mp h) with q hq
  lift ringKrullDim (S ⧸ span {w}) to ℕ∞ using
    ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial with f
  lift f to ℕ using fun h ↦ by
    rw [h] at hdimQ
    exact (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)).ne hdimQ.symm with k
  rw [_root_.IsLocalRing.depth_eq_depth_of_surjective (R := S) (T := S ⧸ span {w})
      Ideal.Quotient.mk_surjective, IsRegularLocalRing.depth_eq_ringKrullDim, hdS, ← hdimQ,
    ← hq] at hab
  have hpqk : p + q = k + 1 := by exact_mod_cast hab
  rw [← projectiveDimension_le_iff M' 1, hpd_iso]
  norm_cast
  omega

end TauCeti
