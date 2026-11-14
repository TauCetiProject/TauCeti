/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.RingTheory.Depth.AuslanderBuchsbaum
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.KrullDimension.Module

/-!
# Maximal Cohen–Macaulay modules and matrix factorizations over a local hypersurface

Let `(S, 𝔪)` be a regular local ring and let `w ∈ 𝔪` be a nonzerodivisor, so that `R = S ⧸ (w)` is
a local hypersurface ring of Krull dimension `dim S - 1`. A finitely generated `R`-module `M` is
*maximal Cohen–Macaulay* when `dim R ≤ depth M` (with `depth 0 = ⊤`, and `depth M = dim R` when
`M ≠ 0`).

Over a Noetherian ambient ring `S` of finite global dimension, a finitely generated `R`-module is
Gorenstein-projective over `R` if and only if its projective dimension over `S` is at most one
(`TauCeti.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`): the forward direction is
`TauCeti.IsGorensteinProjective.hasProjectiveDimensionLE_restrictScalars_quotient`, and the reverse
direction constructs a matrix factorization from a length-one projective resolution
(`TauCeti.MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE`).

When `S` is regular local and `R = S ⧸ (w)` is local (`w ∈ 𝔪`), the Auslander–Buchsbaum formula over
`S`,

```text
pd_S M + depth_R M = depth S = dim S = dim R + 1,
```

translates `pd_S M ≤ 1` into `dim R ≤ depth_R M`. Consequently, for a finitely generated `R`-module
`M`, the following four conditions are equivalent (`TauCeti.isGorensteinProjective_quotient_tfae`):

1. `M` is Gorenstein-projective over `R`;
2. `M` has projective dimension at most one over `S`;
3. `M` is isomorphic to the cokernel of the reduction modulo `w` of a finite free (projective)
   matrix factorization of `w`;
4. `M` is maximal Cohen–Macaulay over `R` (`ringKrullDim R ≤ depth M`).

In particular, every Gorenstein-projective `R`-module is Cohen–Macaulay, and if `M` is nonzero its
depth equals the full Krull dimension `ringKrullDim R`. Together with
`quotientGorensteinProjectiveStableCokernel_isEquivalence_of_isRegularLocalRing` (in
`TauCeti.MatrixFactorization.HomotopyCategory`), this recovers Eisenbud's theorem in maximal
Cohen–Macaulay terms: `HMF(S, w)` is triangle equivalent to the stable category of maximal
Cohen–Macaulay `S ⧸ (w)`-modules.

## Main results

* `TauCeti.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`: over a Noetherian ring `S`
  of finite global dimension, a finite `S ⧸ (w)`-module is Gorenstein-projective iff `pd_S M ≤ 1`.
* `TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth`: over a
  regular local ring `S`, `pd_S M ≤ 1 ↔ dim (S ⧸ (w)) ≤ depth M`.
* `TauCeti.isGorensteinProjective_quotient_iff_ringKrullDim_le_depth`: **Buchweitz–Eisenbud
  characterization**, `IsGorensteinProjective (S ⧸ (w)) M ↔ dim (S ⧸ (w)) ≤ depth M`.
* `TauCeti.isGorensteinProjective_quotient_tfae`: the four-way equivalence between Gorenstein
  projectivity, `pd_S M ≤ 1`, matrix-factorization cokernels, and maximal Cohen–Macaulayness.
* `TauCeti.IsGorensteinProjective.depth_eq_ringKrullDim` and
  `TauCeti.IsGorensteinProjective.isCohenMacaulay`: depth and Cohen–Macaulayness of
  Gorenstein-projective modules over a local hypersurface.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Corollary 6.3.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys and
  Monographs **262**, American Mathematical Society (2021), Lemma 4.2.2 and Section 4.4.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

universe u

open CategoryTheory Ideal

namespace TauCeti

section FiniteGlobalDimension

variable {S : Type u} [CommRing S] [IsNoetherianRing S] {w : S}

/-- Over a Noetherian ring `S` of finite global dimension, a finitely generated module over the
hypersurface `S ⧸ (w)` (`w` a nonzerodivisor) is Gorenstein-projective if and only if its
projective dimension over `S` is at most one. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  have : Module.Finite S ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M) :=
    ((Ideal.Quotient.mk (span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
  have := Module.finitePresentation_of_finite S
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
  exact ⟨fun hM ↦ hM.hasProjectiveDimensionLE_restrictScalars_quotient hw d hd,
    MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE hw M⟩

end FiniteGlobalDimension

section RegularLocalRing

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}

/-- Over a regular local ring `S`, a finitely generated `S ⧸ (w)`-module (`w` a nonzerodivisor) is
Gorenstein-projective if and only if its projective dimension over `S` is at most one. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 :=
  isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE hw
    (_root_.IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge) M

variable [_root_.IsLocalRing (S ⧸ span {w})]

/-- **Auslander–Buchsbaum criterion for projective dimension one over a local hypersurface.** Let
`S` be a regular local ring and `w` a nonzerodivisor such that `R = S ⧸ (w)` is local (equivalently
`w ∈ 𝔪_S`). A finitely generated `R`-module `M` has projective dimension at most one over `S` if
and only if `dim R ≤ depth M` (maximal Cohen–Macaulayness). -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
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
  let MS : ModuleCat.{u} S := ModuleCat.of S M
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

/-- **Buchweitz–Eisenbud characterization of maximal Cohen–Macaulay modules.** Over the local
hypersurface `R = S ⧸ (w)` cut out by a nonzerodivisor `w` of a regular local ring `S`, a finitely
generated `R`-module `M` is Gorenstein-projective if and only if `dim R ≤ depth M`. -/
theorem isGorensteinProjective_quotient_iff_ringKrullDim_le_depth
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) :=
  (isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing hw M).trans
    (hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth hw M)

/-- **Four-way characterization of maximal Cohen–Macaulay modules over a local hypersurface**
(Eisenbud, Corollary 6.3; Buchweitz, Lemma 4.2.2). For a finitely generated module `M` over the
local hypersurface `R = S ⧸ (w)` in a regular local ring `S`, the following are equivalent:
1. `M` is Gorenstein-projective over `R`;
2. `M` has projective dimension at most one over `S`;
3. `M` is isomorphic to the cokernel of the reduction modulo `w` of a finite-projective matrix
   factorization of `w`;
4. `dim R ≤ depth M` (`M` is maximal Cohen–Macaulay). -/
theorem isGorensteinProjective_quotient_tfae
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    List.TFAE
      [IsGorensteinProjective (S ⧸ span {w}) M,
        HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
          1,
        ∃ X : MatrixFactorization S w, Nonempty
          ((MatrixFactorization.cokernelFunctor.obj
            ((MatrixFactorization.baseChangeFunctor (Ideal.Quotient.mk (span {w}))).obj X)).obj ≅
              M),
        ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞)] := by
  tfae_have 1 ↔ 2 :=
    isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing hw M
  tfae_have 3 ↔ 2 :=
    MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing
      hw M
  tfae_have 2 ↔ 4 :=
    hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth hw M
  tfae_finish

/-- A nonzero Gorenstein-projective module over the local hypersurface `S ⧸ (w)` has depth equal to
the full Krull dimension of `S ⧸ (w)`. -/
theorem IsGorensteinProjective.depth_eq_ringKrullDim
    {M : ModuleCat.{u} (S ⧸ span {w})} (hM : IsGorensteinProjective (S ⧸ span {w}) M)
    (hw : w ∈ nonZeroDivisors S) [Nontrivial M] :
    (_root_.IsLocalRing.depth M : WithBot ℕ∞) = ringKrullDim (S ⧸ span {w}) := by
  have := hM.finite
  have : IsNoetherianRing (S ⧸ span {w}) := inferInstance
  exact le_antisymm
    (_root_.IsLocalRing.depth_le_supportDim.trans (Module.supportDim_le_ringKrullDim _ M))
    ((isGorensteinProjective_quotient_iff_ringKrullDim_le_depth hw M).mp hM)

/-- Every Gorenstein-projective module over the local hypersurface `S ⧸ (w)` is Cohen–Macaulay. -/
theorem IsGorensteinProjective.isCohenMacaulay
    {M : ModuleCat.{u} (S ⧸ span {w})} (hM : IsGorensteinProjective (S ⧸ span {w}) M)
    (hw : w ∈ nonZeroDivisors S) :
    Module.IsCohenMacaulay (S ⧸ span {w}) M := by
  cases subsingleton_or_nontrivial M
  · exact Module.isCohenMacaulay_of_subsingleton
  have := hM.finite
  have : IsNoetherianRing (S ⧸ span {w}) := inferInstance
  exact Module.isCohenMacaulay_iff_supportDim_le_depth.mpr
    ((Module.supportDim_le_ringKrullDim _ M).trans
      ((isGorensteinProjective_quotient_iff_ringKrullDim_le_depth hw M).mp hM))

end RegularLocalRing

end TauCeti
