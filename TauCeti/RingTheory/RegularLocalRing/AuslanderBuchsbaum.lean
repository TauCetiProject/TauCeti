/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Maximal.Hypersurface
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Auslander–Buchsbaum depth criterion over a local hypersurface

Over a regular local ring `S` and a nonzerodivisor `w` with local quotient `R = S ⧸ (w)`, Serre's
bound and the Auslander–Buchsbaum formula `pd_S M + depth_R M = dim S = dim R + 1` show that a
finitely generated `R`-module `M` satisfies `pd_S M ≤ 1 ↔ ringKrullDim R ≤ depth M`
(`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth`),
equivalently `IsMaximalCohenMacaulay R M ↔ HasProjectiveDimensionLE M_S 1`
(`TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE`), and
that nonzero finite maximal Cohen–Macaulay `R`-modules have `pd_S M = 1`
(`TauCeti.IsRegularLocalRing.projectiveDimension_restrictScalars_eq_one_of_isMaximalCohenMacaulay`).
The two directions hold over any Cohen–Macaulay local ring, given finite projective dimension over
`S` for the converse (`TauCeti.RingTheory.CohenMacaulay.Maximal.Hypersurface`); regularity supplies
that finiteness.

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

/-- **Auslander–Buchsbaum criterion for projective dimension one over a local hypersurface:** for a
nonzerodivisor `w` of a regular local ring `S` with local quotient `R = S ⧸ (w)`, a finitely
generated `R`-module `M` has `pd_S M ≤ 1` iff `dim R ≤ depth M`. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth
    {S : Type u} [CommRing S] [IsRegularLocalRing S] [Small.{v} S] {w : S}
    [_root_.IsLocalRing (S ⧸ span {w})] [Small.{v} (S ⧸ span {w})]
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{v} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M) 1 ↔
      ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) :=
  ⟨ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient
      IsRegularLocalRing.isCohenMacaulay hw M,
    hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth
      IsRegularLocalRing.isCohenMacaulay hw M ((projectiveDimension_ne_top_iff _).2
        ⟨_, IsRegularLocalRing.hasProjectiveDimensionLE_spanFinrank_maximalIdeal _⟩)⟩

namespace IsRegularLocalRing

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
  have hle := (projectiveDimension_le_iff M' (_root_.IsLocalRing.maximalIdeal S).spanFinrank).2
    (hasProjectiveDimensionLE (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge M')
  exact hM.projectiveDimension_restrictScalars_eq_one (.of_ne_zero hw)
    (hle.trans_lt (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top _))).ne

end IsRegularLocalRing

end TauCeti
