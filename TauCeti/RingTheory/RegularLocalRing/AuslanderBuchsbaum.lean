/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Hypersurface
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Auslander–Buchsbaum depth criterion over a local hypersurface

Over a regular local ring `S` and a nonzerodivisor `w` with local quotient `R = S ⧸ (w)`, Serre's
bound and the Auslander–Buchsbaum formula `pd_S M + depth_R M = dim S = dim R + 1` show that a
finitely generated `R`-module `M` satisfies `pd_S M ≤ 1 ↔ ringKrullDim R ≤ depth M`
(`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth`). The two
directions hold over any Cohen–Macaulay local ring, given finite projective dimension over `S`
for the converse (`TauCeti.RingTheory.CohenMacaulay.Hypersurface`); regularity supplies that
finiteness.

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

end TauCeti
