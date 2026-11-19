/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Presentation
public import TauCeti.RingTheory.Regular.ProjectiveDimension
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Projective dimension over the ambient ring of a hypersurface

Let `w` be a nonzerodivisor of a commutative ring `S`. If `S` has finite global dimension,
a finitely generated Gorenstein-projective module over `S/(w)` has projective dimension at most
one over `S`. In particular this holds when `S` is regular local.

This is the projective-dimension input to the construction of matrix factorizations from
Gorenstein-projective modules: over a Noetherian ambient ring such a module admits a length-one
resolution by finitely generated projectives. It does not assert that the module is projective
over the hypersurface ring.

Restriction of scalars takes a projective `S/(w)`-module to an `S`-module of projective dimension
at most one. The short exact copresentations from a complete resolution then lower any uniform
finite bound on the restricted Gorenstein-projective modules until that bound is one. Only the
copresentations are needed; no comparison of singularity categories is assumed.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

open CategoryTheory

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

end TauCeti.IsGorensteinProjective
