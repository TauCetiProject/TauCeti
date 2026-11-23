/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.RingTheory.RegularLocalRing.Locus
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.RegularLocalRing.Smooth
import TauCeti.RingTheory.Smooth.Field
import TauCeti.RingTheory.Smooth.Regular

/-!
# The regular locus of a scheme

The regular locus `X.regularLocus` of a scheme `X` is the set of points of `X` whose local ring
is a regular local ring. On `Spec R` it is the regular locus `TauCeti.Excellence.regularLocus R`
of the ring `R`, open immersions identify regular loci, and a locally Noetherian scheme is regular
exactly when its regular locus is everything.

For `X` locally of finite type over a perfect field `k`, the regular locus is the smooth locus of
the structure morphism `X ⟶ Spec k` (The Stacks Project, Section 10.140).
On an affine open `U` containing `x`, the local ring of `X` at `x` is the localization of `Γ(X, U)`
at the prime of `x`. If it is formally smooth over `k` it is regular
(`TauCeti.IsRegularLocalRing.of_formallySmooth`), and conversely a regular local ring essentially
of finite type over `k` is formally smooth over `k`, since its residue field is
(`TauCeti.formallySmooth_of_isRegularLocalRing`). Perfectness cannot be dropped: over
`𝔽_p(t)` with `p` an odd prime, the curve `y ^ 2 = x ^ p - t` is regular at its point `y = 0`
but not smooth there. In particular the regular locus over a perfect field is open, which fails
for general locally Noetherian schemes (Stacks, Section 15.48).

## Main declarations

* `AlgebraicGeometry.Scheme.regularLocus`: the points of `X` with regular local ring.
* `AlgebraicGeometry.Scheme.regularLocus_Spec`: on `Spec R` it is the regular locus of `R`.
* `AlgebraicGeometry.Scheme.Hom.preimage_regularLocus`: open immersions identify regular loci.
* `AlgebraicGeometry.Scheme.isRegular_iff_regularLocus_eq_univ`: a locally Noetherian scheme is
  regular exactly when its regular locus is everything.
* `AlgebraicGeometry.Scheme.Hom.regularLocus_eq_smoothLocus`: over a perfect field, the regular
  locus of a scheme locally of finite type is the smooth locus of its structure morphism.
-/

public section

open CategoryTheory TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The *regular locus* of a scheme `X`: the points of `X` whose local ring is a regular local
ring. It need not be open (Stacks, Section 15.48). -/
def regularLocus (X : Scheme.{u}) : Set X :=
  {x | IsRegularLocalRing (X.presheaf.stalk x)}

variable {X : Scheme.{u}}

@[simp]
theorem mem_regularLocus {x : X} :
    x ∈ X.regularLocus ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- The regular locus of `X` is everything exactly when all local rings of `X` are regular. -/
theorem regularLocus_eq_univ_iff :
    X.regularLocus = Set.univ ↔ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  Set.eq_univ_iff_forall

/-- A locally Noetherian scheme is regular exactly when its regular locus is everything. -/
theorem isRegular_iff_regularLocus_eq_univ [IsLocallyNoetherian X] :
    IsRegular X ↔ X.regularLocus = Set.univ := by
  rw [regularLocus_eq_univ_iff, isRegular_iff_forall_stalk]
  exact and_iff_right ‹_›

/-- The regular locus of a regular scheme is everything. -/
theorem regularLocus_eq_univ [IsRegular X] : X.regularLocus = Set.univ :=
  regularLocus_eq_univ_iff.mpr inferInstance

/-- The regular locus of `Spec R` is the regular locus of the ring `R`: the local ring of
`Spec R` at a prime `p` is `R_p`. -/
theorem regularLocus_Spec (R : CommRingCat.{u}) :
    (Spec R).regularLocus = Excellence.regularLocus R := by
  ext x
  exact (isRegularLocalRing_stalk_Spec_iff R x).trans
    (Excellence.mem_regularLocus (p := (x : PrimeSpectrum R))).symm

/-- An open immersion `f : X ⟶ Y` identifies the regular locus of `X` with the preimage of the
regular locus of `Y`. -/
theorem Hom.preimage_regularLocus {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f ⁻¹' Y.regularLocus = X.regularLocus := by
  ext x
  rw [Set.mem_preimage, mem_regularLocus, mem_regularLocus]
  exact isRegularLocalRing_stalk_iff_of_isOpenImmersion f x

/-- **Regular points over a perfect field are smooth points.** Let `k` be a perfect field and
`f : X ⟶ Spec k` locally of finite type. The local ring of `X` at `x` is regular exactly when `f`
is smooth at `x` (The Stacks Project, Section 10.140). -/
theorem Hom.mem_regularLocus_iff_mem_smoothLocus {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x : X} :
    x ∈ X.regularLocus ↔ x ∈ f.smoothLocus := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  rw [f.mem_smoothLocus_iff_isSmoothAt (U := ⟨U, hU⟩) hxU]
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_ΓSpecIso_inv_comp_appLE hU
  let q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  -- the local ring of `X` at `x` is the localization of `Γ(X, U)` at `q`
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let e : Localization.AtPrime q ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) _).toRingEquiv
  rw [mem_regularLocus]
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have : IsRegularLocalRing (Localization.AtPrime q) := .of_ringEquiv e.symm
    exact formallySmooth_of_isRegularLocalRing
  · have : Algebra.FormallySmooth k (Localization.AtPrime q) := h
    have : IsRegularLocalRing (Localization.AtPrime q) :=
      IsRegularLocalRing.of_formallySmooth (R := k)
    exact .of_ringEquiv e

/-- **The regular locus over a perfect field is the smooth locus.** If `k` is a perfect field and
`f : X ⟶ Spec k` is locally of finite type, the points of `X` with regular local ring are exactly
the points at which `f` is smooth. -/
theorem Hom.regularLocus_eq_smoothLocus {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    X.regularLocus = f.smoothLocus := by
  ext x
  exact f.mem_regularLocus_iff_mem_smoothLocus

/-- Over a perfect field, the regular locus of a scheme locally of finite type is open. -/
theorem isOpen_regularLocus_of_perfectField {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : IsOpen X.regularLocus := by
  rw [f.regularLocus_eq_smoothLocus]
  exact f.smoothLocus.isOpen

end AlgebraicGeometry.Scheme
