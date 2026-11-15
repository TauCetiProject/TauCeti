/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.CohenMacaulay
public import TauCeti.Algebra.Homology.GorensteinProjective.Hypersurface
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.RingTheory.RegularLocalRing.AuslanderBuchsbaum
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Maximal Cohen–Macaulay modules and matrix factorizations over a local hypersurface

Let `S` be a commutative ring and `w` a nonzerodivisor of `S`, with hypersurface quotient
`R = S ⧸ (w)`. Over an ambient ring `S` of finite global dimension, a finitely presented `R`-module
is Gorenstein-projective over `R` if and only if its projective dimension over `S` is at most one
(`TauCeti.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`): the forward direction is
`TauCeti.IsGorensteinProjective.hasProjectiveDimensionLE_restrictScalars_quotient`, and the reverse
direction constructs a matrix factorization from a length-one projective resolution
(`TauCeti.MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE`).

When `(S, 𝔪)` is a regular local ring and `R = S ⧸ (w)` is local (`w ∈ 𝔪`), a finitely generated
`R`-module `M` is *maximal Cohen–Macaulay* when `dim R ≤ depth M` (with `depth 0 = ⊤`, and
`depth M = dim R` when `M ≠ 0`). Combining the projective-dimension characterization with the
Auslander–Buchsbaum depth criterion
(`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth`),
the following four conditions on a finitely generated `R`-module `M` are equivalent
(`TauCeti.isGorensteinProjective_quotient_tfae`):

1. `M` is Gorenstein-projective over `R`;
2. `M` has projective dimension at most one over `S`;
3. `M` is isomorphic to the cokernel of the reduction modulo `w` of a finite free (projective)
   matrix factorization of `w`;
4. `M` is maximal Cohen–Macaulay over `R` (`ringKrullDim R ≤ depth M`).

In particular, since `R = S ⧸ (w)` is a Cohen–Macaulay local ring, every Gorenstein-projective
`R`-module (in any universe) is Cohen–Macaulay, and if `M` is nontrivial its depth equals the full
Krull dimension `ringKrullDim R` (specializing
`TauCeti.IsGorensteinProjective.depth_eq_ringKrullDim` and
`TauCeti.IsGorensteinProjective.isCohenMacaulay`). Together with
`quotientGorensteinProjectiveStableCokernel_isEquivalence_of_isRegularLocalRing` (in
`TauCeti.MatrixFactorization.HomotopyCategory`), this recovers Eisenbud's theorem in maximal
Cohen–Macaulay terms: `HMF(S, w)` is triangle equivalent to the stable category of maximal
Cohen–Macaulay `S ⧸ (w)`-modules.

## Main results

* `TauCeti.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`: over a commutative ring
  `S` of bounded projective dimension, a finitely presented `S ⧸ (w)`-module is
  Gorenstein-projective iff `pd_S M ≤ 1` (with Noetherian, regular, and regular-local
  specializations).
* `TauCeti.isGorensteinProjective_quotient_iff_ringKrullDim_le_depth`: **Buchweitz–Eisenbud
  characterization**, `IsGorensteinProjective (S ⧸ (w)) M ↔ dim (S ⧸ (w)) ≤ depth M`.
* `TauCeti.isGorensteinProjective_quotient_tfae`: the four-way equivalence between Gorenstein
  projectivity, `pd_S M ≤ 1`, matrix-factorization cokernels, and maximal Cohen–Macaulayness.
* `TauCeti.IsGorensteinProjective.depth_eq_ringKrullDim_quotient` and
  `TauCeti.IsGorensteinProjective.isCohenMacaulay_quotient`: depth and Cohen–Macaulayness of
  Gorenstein-projective modules over a local hypersurface in a regular local ring.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Corollary 6.3.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys and
  Monographs **262**, American Mathematical Society (2021), Lemma 4.2.2 and Section 4.4.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

universe v u

open CategoryTheory Ideal

namespace TauCeti

section FiniteGlobalDimension

variable {S : Type u} [CommRing S] {w : S}

/-- Over a commutative ring `S` whose modules have projective dimension bounded by `d`, a finitely
presented module over the hypersurface `S ⧸ (w)` (`w` a nonzerodivisor) is Gorenstein-projective if
and only if its projective dimension over `S` is at most one. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.FinitePresentation (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  have : Module.FinitePresentation S (S ⧸ span {w}) :=
    Module.finitePresentation_of_surjective (span {w}).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span_singleton w)
  let : Module S M := Module.compHom M (algebraMap S (S ⧸ span {w}))
  have : IsScalarTower S (S ⧸ span {w}) M := .of_compHom S (S ⧸ span {w}) M
  have : Module.FinitePresentation S M :=
    Module.FinitePresentation.trans (R := S) (M := M) (S ⧸ span {w})
  have : Module.FinitePresentation S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M) :=
    Module.FinitePresentation.of_equiv
      (ModuleCat.restrictScalarsAlgebraMapIso M).symm.toLinearEquiv
  exact ⟨fun hM ↦ hM.hasProjectiveDimensionLE_restrictScalars_quotient hw d hd,
    MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE hw M⟩

/-- Over a commutative ring `S` of bounded projective dimension with Noetherian quotient
`S ⧸ (w)`, a finitely generated `S ⧸ (w)`-module (`w` a nonzerodivisor) is Gorenstein-projective if
and only if its projective dimension over `S` is at most one. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isNoetherianRing
    [IsNoetherianRing (S ⧸ span {w})] (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  have := Module.finitePresentation_of_finite (S ⧸ span {w}) M
  exact isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE hw d hd M

end FiniteGlobalDimension

namespace IsRegularRing

variable {S : Type u} [CommRing S] [IsRegularRing S] {w : S}

/-- Over a commutative regular ring `S` of finite Krull dimension, a finitely generated
`S ⧸ (w)`-module (`w` a nonzerodivisor) is Gorenstein-projective if and only if its projective
dimension over `S` is at most one. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_ringKrullDim_lt_top
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim S ≤ d := by
    cases h : ringKrullDim S with
    | bot => exact ⟨0, bot_le⟩
    | coe e =>
      lift e to ℕ using fun he ↦ hdim.ne (by simp [h, he])
      exact ⟨e, le_rfl⟩
  exact isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw d
    (IsRegularRing.hasProjectiveDimensionLE hd) M

end IsRegularRing

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
  IsRegularRing.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_ringKrullDim_lt_top
    ringKrullDim_lt_top hw M

variable [_root_.IsLocalRing (S ⧸ span {w})]

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

/-- A nontrivial Gorenstein-projective module over the local hypersurface `S ⧸ (w)` in a regular
local ring `S` has depth equal to `ringKrullDim (S ⧸ (w))`. -/
theorem IsGorensteinProjective.depth_eq_ringKrullDim_quotient
    {M : ModuleCat.{v} (S ⧸ span {w})} [Small.{v} (S ⧸ span {w})]
    (hM : IsGorensteinProjective (S ⧸ span {w}) M) (hw : w ∈ nonZeroDivisors S) [Nontrivial M] :
    (_root_.IsLocalRing.depth M : WithBot ℕ∞) = ringKrullDim (S ⧸ span {w}) := by
  have hwm : w ∈ _root_.IsLocalRing.maximalIdeal S := by
    by_contra h
    exact not_subsingleton (S ⧸ span {w}) (Ideal.Quotient.subsingleton_iff.mpr
      (span_singleton_eq_top.mpr (_root_.IsLocalRing.notMem_maximalIdeal.mp h)))
  have hQ : Module.IsCohenMacaulay S (QuotSMulTop w S) :=
    (Module.isCohenMacaulay_quotSMulTop_iff
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hw) hwm).mpr
      IsRegularLocalRing.isCohenMacaulay
  have e : QuotSMulTop w S ≃ₗ[S] S ⧸ span {w} :=
    (Ideal.quotientEquivAlgOfEq S (by simp [← Submodule.ideal_span_singleton_smul])).toLinearEquiv
  have : Ring.IsCohenMacaulay (S ⧸ span {w}) :=
    Ring.isCohenMacaulay_iff_of_isLocalRing.mpr
      ((Module.isCohenMacaulay_iff_isCohenMacaulay_of_surjective
        Ideal.Quotient.mk_surjective).mp (e.isCohenMacaulay_iff.mp hQ))
  exact hM.depth_eq_ringKrullDim

/-- Every Gorenstein-projective module over the local hypersurface `S ⧸ (w)` in a regular local ring
`S` is Cohen–Macaulay. -/
theorem IsGorensteinProjective.isCohenMacaulay_quotient
    {M : ModuleCat.{v} (S ⧸ span {w})} [Small.{v} (S ⧸ span {w})]
    (hM : IsGorensteinProjective (S ⧸ span {w}) M) (hw : w ∈ nonZeroDivisors S) :
    Module.IsCohenMacaulay (S ⧸ span {w}) M := by
  cases subsingleton_or_nontrivial M
  · exact Module.isCohenMacaulay_of_subsingleton
  have := hM.finite
  exact Module.isCohenMacaulay_iff_supportDim_le_depth.mpr
    ((Module.supportDim_le_ringKrullDim _ M).trans
      (hM.depth_eq_ringKrullDim_quotient hw).symm.le)

end RegularLocalRing

end TauCeti
