/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Hypersurface
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.RingTheory.RegularLocalRing.AuslanderBuchsbaum

/-!
# Maximal Cohen–Macaulay modules and matrix factorizations over a local hypersurface

Over a commutative ring `S` of bounded projective dimension with `w ∈ nonZeroDivisors S`, a
finitely presented `S ⧸ (w)`-module is Gorenstein-projective iff `pd_S M ≤ 1`
(`TauCeti.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`). Over a local hypersurface
`R = S ⧸ (w)` in a regular local ring `S`, combining this with
`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth` yields the
Buchweitz–Eisenbud four-way equivalence (`TauCeti.isGorensteinProjective_quotient_tfae`). Since
Gorenstein-projective modules are finitely generated, the Gorenstein-projective `S ⧸ (w)`-modules
are exactly the finitely generated maximal Cohen–Macaulay ones, with no finiteness hypothesis on
the module (`TauCeti.isGorensteinProjective_quotient_iff_finite_and_ringKrullDim_le_depth`).

Over a Cohen–Macaulay local ring `S`, the cokernel of the reduction modulo `w` of a
finite-projective matrix factorization of `w` is already maximal Cohen–Macaulay
(`TauCeti.MatrixFactorization.ringKrullDim_quotient_le_depth_quotientCokernel`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Corollary 6.3.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Lemma 4.2.2.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

universe u

open CategoryTheory Ideal

namespace TauCeti

section FiniteGlobalDimension

variable {S : Type u} [CommRing S] {w : S}

/-- Over a commutative ring `S` of projective dimension bounded by `d`, a finitely presented
`S ⧸ (w)`-module (`w ∈ nonZeroDivisors S`) is Gorenstein-projective iff `pd_S M ≤ 1`. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE
    (hw : w ∈ nonZeroDivisors S) (d : ℕ) (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.FinitePresentation (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  have : Module.FinitePresentation S (S ⧸ span {w}) :=
    Module.finitePresentation_of_surjective (span {w}).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span_singleton w)
  let : Module S M := Module.compHom M (algebraMap S (S ⧸ span {w}))
  have : IsScalarTower S (S ⧸ span {w}) M := .of_compHom S (S ⧸ span {w}) M
  have : Module.FinitePresentation S M := .trans (R := S) (M := M) (S ⧸ span {w})
  have : Module.FinitePresentation S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M) :=
    .of_equiv (ModuleCat.restrictScalarsAlgebraMapIso M).symm.toLinearEquiv
  exact ⟨fun hM ↦ hM.hasProjectiveDimensionLE_restrictScalars_quotient hw d hd,
    MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE hw M⟩

/-- Noetherian specialization of `isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`. -/
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

namespace MatrixFactorization

/-- **Cokernels of matrix factorizations are maximal Cohen–Macaulay.** Let `S` be a
Cohen–Macaulay Noetherian local ring and `w` a non-zero-divisor with `S ⧸ (w)` local. The cokernel
of the reduction modulo `w` of a finite-projective matrix factorization of `w` has depth at least
`dim S ⧸ (w)`. -/
theorem ringKrullDim_quotient_le_depth_quotientCokernel {S : Type u} [CommRing S]
    [_root_.IsLocalRing S] [IsNoetherianRing S] {w : S} [_root_.IsLocalRing (S ⧸ span {w})]
    (hS : Module.IsCohenMacaulay S S) (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    ringKrullDim (S ⧸ span {w}) ≤
      _root_.IsLocalRing.depth (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (span {w}))).obj X)).obj :=
  ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient
    hS hw _
    ((exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw _).1
      ⟨X, ⟨Iso.refl _⟩⟩)

end MatrixFactorization

namespace IsRegularRing

variable {S : Type u} [CommRing S] [IsRegularRing S] {w : S}

/-- Regular-ring specialization (`ringKrullDim S < ⊤`) of
`isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_ringKrullDim_lt_top
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim S ≤ d := by
    cases h : ringKrullDim S with
    | bot => exact ⟨0, bot_le⟩
    | coe e => lift e to ℕ using fun he ↦ hdim.ne (by simp [h, he]); exact ⟨e, le_rfl⟩
  exact isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw d
    (IsRegularRing.hasProjectiveDimensionLE hd) M

end IsRegularRing

section RegularLocalRing

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}

/-- Regular-local specialization of `isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`.
-/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 :=
  IsRegularRing.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_ringKrullDim_lt_top
    ringKrullDim_lt_top hw M

variable [_root_.IsLocalRing (S ⧸ span {w})]

/-- **Buchweitz–Eisenbud characterization:** over the local hypersurface `S ⧸ (w)` in a regular
local ring `S`, a finitely generated module `M` is Gorenstein-projective iff
`dim (S ⧸ (w)) ≤ depth M`. -/
theorem isGorensteinProjective_quotient_iff_ringKrullDim_le_depth
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) :=
  (isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing hw M).trans
    (hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth hw M)

/-- Over the local hypersurface `S ⧸ (w)` in a regular local ring `S`, an `S ⧸ (w)`-module is
Gorenstein-projective iff it is finitely generated and `dim (S ⧸ (w)) ≤ depth M`. Unlike
`isGorensteinProjective_quotient_iff_ringKrullDim_le_depth`, no finiteness is assumed. -/
theorem isGorensteinProjective_quotient_iff_finite_and_ringKrullDim_le_depth
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w})) :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      Module.Finite (S ⧸ span {w}) M ∧
        ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) := by
  refine ⟨fun hM ↦ ?_, fun ⟨_, hM⟩ ↦ ?_⟩
  · have := hM.finite
    exact ⟨this, (isGorensteinProjective_quotient_iff_ringKrullDim_le_depth hw M).1 hM⟩
  · exact (isGorensteinProjective_quotient_iff_ringKrullDim_le_depth hw M).2 hM

/-- **Four-way characterization of maximal Cohen–Macaulay modules over a local hypersurface**
(Eisenbud, Corollary 6.3; Buchweitz, Lemma 4.2.2). -/
theorem isGorensteinProjective_quotient_tfae
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    List.TFAE
      [IsGorensteinProjective (S ⧸ span {w}) M,
        HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
          1,
        ∃ X : MatrixFactorization S w, Nonempty ((MatrixFactorization.cokernelFunctor.obj
          ((MatrixFactorization.baseChangeFunctor (Ideal.Quotient.mk (span {w}))).obj X)).obj ≅ M),
        ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞)] := by
  tfae_have 1 ↔ 2 :=
    isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing hw M
  tfae_have 3 ↔ 2 :=
    MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing
      hw M
  tfae_have 2 ↔ 4 :=
    hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth hw M
  tfae_finish

end RegularLocalRing

end TauCeti
