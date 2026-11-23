/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.Depth.AuslanderBuchsbaum
import TauCeti.RingTheory.LocalRing.Quotient

/-!
# Maximal Cohen–Macaulay modules over a hypersurface

Let `S` be a Cohen–Macaulay Noetherian local ring, let `w` be a non-zero-divisor of `S` with
`S/(w)` local (equivalently, `w` lies in the maximal ideal), and put `R = S/(w)`. A finitely
generated `R`-module `M` is *maximal Cohen–Macaulay* when `dim R ≤ depth M`; with this
formulation the zero module, whose depth is infinite, is included.

By the Auslander–Buchsbaum formula over `S`, together with `depth_S M = depth_R M` and
`dim R + 1 = dim S`, the depth of `M` measures its projective dimension over `S`:

* if `M` has projective dimension at most one over `S`, then `M` is maximal Cohen–Macaulay over
  `R`
  (`TauCeti.ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient`);
* conversely, a maximal Cohen–Macaulay `R`-module of finite projective dimension over `S` has
  projective dimension at most one over `S`
  (`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth`).

Over a regular local ring every module has finite projective dimension, so the two conditions
agree (`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth` in
`TauCeti.RingTheory.RegularLocalRing.AuslanderBuchsbaum`). The comparison `depth_S M = depth_R M`
is `ModuleCat.depth_restrictScalars_of_surjective` from `TauCeti.RingTheory.Depth.Basic`.

## Main results

* `TauCeti.ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient`
  and
  `TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_of_ringKrullDim_le_depth`:
  the two implications above, over a Cohen–Macaulay local ring `S`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 6.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 1.3.3 (the Auslander–Buchsbaum formula).
-/

public section

open CategoryTheory IsLocalRing
open ModuleCat (restrictScalars)

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
