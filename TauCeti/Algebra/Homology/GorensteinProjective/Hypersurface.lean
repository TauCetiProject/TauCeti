/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Presentation
public import TauCeti.CategoryTheory.ObjectProperty.Syzygy
public import TauCeti.RingTheory.Regular.ProjectiveDimension
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Projective dimension over the ambient ring of a hypersurface

Let `w` be a nonzerodivisor of a commutative ring `S`. If `S` has finite global dimension `≤ d`,
every sufficiently high syzygy of an `S/(w)`-module—and hence every finitely generated
Gorenstein-projective `S/(w)`-module—has projective dimension at most one over `S`. In particular
this holds when `S` is regular local, or more generally regular of finite Krull dimension.

This is the projective-dimension input both to the construction of matrix factorizations from
Gorenstein-projective modules (over a Noetherian ambient ring such a module admits a length-one
resolution by finitely generated projectives) and to essential surjectivity onto the singularity
category `D_sg(mod-S/(w))`, whose objects are up to shift represented by `d`-th syzygies. It does
not assert that the module is projective over the hypersurface ring.

Restriction of scalars takes a projective `S/(w)`-module to an `S`-module of projective dimension
at most one. Each short exact projective presentation or copresentation step then lowers a uniform
finite bound on projective dimension over `S` by one until that bound reaches one.

## Main results

In the namespace `ModuleCat`:

* `hasProjectiveDimensionLE_restrictScalars_of_isSyzygy`: if every `S`-module has projective
  dimension at most `r + 1 + k`, every `k`-th projective syzygy over `S/(w)` has projective
  dimension at most `r + 1` over `S`.
* `hasProjectiveDimensionLE_one_restrictScalars_of_isSyzygy`: if every `S`-module has projective
  dimension at most `d` and `d ≤ k + 1`, every `k`-th projective syzygy over `S/(w)` has
  projective dimension at most `1` over `S`.

In the namespace `TauCeti.IsGorensteinProjective`:

* `hasProjectiveDimensionLE_restrictScalars_quotient`: a finitely generated Gorenstein-projective
  `S/(w)`-module has projective dimension at most `1` over `S` when `S` has finite global
  dimension, with specializations
  `hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularLocalRing` and
  `hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularRing`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Section 4.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), 227–248, Section 3.
-/

public section

open CategoryTheory

namespace ModuleCat

universe v u

variable {S : Type u} [CommRing S] [Small.{v} S] {w : S}

/-- Every `k`-th projective syzygy over a hypersurface `S/(w)`, for a nonzerodivisor `w`, lowers a
uniform projective-dimension bound `r + 1 + k` over `S` to `r + 1`: each projective syzygy step has
middle term of projective dimension at most one over `S`. -/
theorem hasProjectiveDimensionLE_restrictScalars_of_isSyzygy
    (hw : w ∈ nonZeroDivisors S) {k r : ℕ}
    {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    (hM : (isProjective (ModuleCat.{v} (S ⧸ Ideal.span {w}))).IsSyzygy k M)
    (hd : ∀ N : ModuleCat.{v} S, HasProjectiveDimensionLE N (r + 1 + k)) :
    HasProjectiveDimensionLE
      ((restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {w}))).obj M) (r + 1) := by
  let F := restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {w}))
  induction k generalizing r M with
  | zero => exact hd (F.obj M)
  | succ k ih =>
    obtain ⟨T, hT, ⟨e⟩, hP, hX₃⟩ :=
      ((isProjective (ModuleCat.{v} (S ⧸ Ideal.span {w}))).isSyzygy_succ_iff k M).1 hM
    have : Projective T.X₂ := hP
    have : HasProjectiveDimensionLT (F.obj T.X₂) 2 :=
      hasProjectiveDimensionLT_restrictScalars_of_projective hw T.X₂
    have hX₃_dim : HasProjectiveDimensionLE (F.obj T.X₃) ((r + 1) + 1) :=
      ih (r := r + 1) hX₃ fun N ↦
        hasProjectiveDimensionLT_of_ge N (r + 1 + (k + 1) + 1) ((r + 1) + 1 + k + 1)
          (have := hd N; by omega)
    have : HasProjectiveDimensionLT (F.obj T.X₁) (r + 2) :=
      (hT.map_of_exact F).hasProjectiveDimensionLT_X₁ (r + 2)
        (hasProjectiveDimensionLT_of_ge (F.obj T.X₂) 2 (r + 2) (by omega)) hX₃_dim
    exact hasProjectiveDimensionLT_of_iso (F.mapIso e.symm) (r + 2)

/-- Over a hypersurface `S/(w)` in a ring `S` of global dimension at most `d`, every `k`-th
projective syzygy of an `S/(w)`-module with `d ≤ k + 1` (in particular every `d`-th syzygy) has
projective dimension at most one over `S`. -/
theorem hasProjectiveDimensionLE_one_restrictScalars_of_isSyzygy
    (hw : w ∈ nonZeroDivisors S) {d k : ℕ} (hdk : d ≤ k + 1)
    {M : ModuleCat.{v} (S ⧸ Ideal.span {w})}
    (hM : (isProjective (ModuleCat.{v} (S ⧸ Ideal.span {w}))).IsSyzygy k M)
    (hd : ∀ N : ModuleCat.{v} S, HasProjectiveDimensionLE N d) :
    HasProjectiveDimensionLE
      ((restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 :=
  hasProjectiveDimensionLE_restrictScalars_of_isSyzygy (r := 0) hw hM fun N ↦
    hasProjectiveDimensionLT_of_ge N (d + 1) (0 + 1 + k + 1) (have := hd N; by omega)

end ModuleCat

namespace TauCeti.IsGorensteinProjective

universe u

variable {S : Type u} [CommRing S] {w : S}

/-- Over a hypersurface in a ring of finite global dimension, a finitely generated
Gorenstein-projective module has projective dimension at most one over the ambient ring.
The global-dimension hypothesis ranges over all modules in the universe of `S`. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (hM : IsGorensteinProjective (S ⧸ Ideal.span {w}) M)
    (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d) :
    HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  let F := ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (Ideal.span {w}))
  -- Each copresentation lowers the uniform bound by one, but never below two in the
  -- strict-bound convention `HasProjectiveDimensionLT`.
  have lower : ∀ k : ℕ,
      (∀ N : ModuleCat.{u} (S ⧸ Ideal.span {w}), IsGorensteinProjective _ N →
        HasProjectiveDimensionLT (F.obj N) (k + 2)) →
      ∀ N : ModuleCat.{u} (S ⧸ Ideal.span {w}), IsGorensteinProjective _ N →
        HasProjectiveDimensionLT (F.obj N) 2 := by
    intro k
    induction k with
    | zero => exact fun h ↦ h
    | succ k ih =>
      intro h
      apply ih
      intro N hN
      obtain ⟨T, hT, ⟨e⟩, _, hP, hQ⟩ := hN.exists_projectiveCopresentation
      have : Projective T.X₂ := hP
      have : HasProjectiveDimensionLT (F.obj T.X₂) 2 :=
        ModuleCat.hasProjectiveDimensionLT_restrictScalars_of_projective hw T.X₂
      have : HasProjectiveDimensionLT (F.obj T.X₁) (k + 2) :=
        (hT.map_of_exact F).hasProjectiveDimensionLT_X₁ (k + 2)
          (hasProjectiveDimensionLT_of_ge (F.obj T.X₂) 2 (k + 2) (by omega)) (h T.X₃ hQ)
      exact hasProjectiveDimensionLT_of_iso (F.mapIso e) (k + 2)
  exact lower d (fun N _ ↦ by
    have := hd (F.obj N)
    exact hasProjectiveDimensionLT_of_ge (F.obj N) (d + 1) (d + 2) (by omega)) M hM

/-- A finitely generated Gorenstein-projective module over a hypersurface in a regular local
ring has projective dimension at most one over that regular local ring. No hypothesis on the
characteristic, dimension, or nonvanishing of the module is needed. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularLocalRing
    [IsRegularLocalRing S] {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (hM : IsGorensteinProjective (S ⧸ Ideal.span {w}) M) (hw : w ∈ nonZeroDivisors S) :
    HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 :=
  hM.hasProjectiveDimensionLE_restrictScalars_quotient hw (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)

/-- A finitely generated Gorenstein-projective module over a hypersurface in a regular ring of
finite Krull dimension has projective dimension at most one over that regular ring. -/
theorem hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularRing
    [IsRegularRing S] (hdim : ringKrullDim S < ⊤) {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (hM : IsGorensteinProjective (S ⧸ Ideal.span {w}) M) (hw : w ∈ nonZeroDivisors S) :
    HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  obtain ⟨d, hd⟩ := IsRegularRing.exists_hasProjectiveDimensionLE.{u} hdim
  exact hM.hasProjectiveDimensionLE_restrictScalars_quotient hw d hd

end TauCeti.IsGorensteinProjective
