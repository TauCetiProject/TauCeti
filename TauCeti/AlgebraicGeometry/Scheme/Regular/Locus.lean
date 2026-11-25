/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.JacobsonSpace
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.RingTheory.RegularLocalRing.Locus
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.Smooth.Regular

/-!
# The regular locus of a scheme

The regular locus `X.regularLocus` of a scheme `X` is the set of points of `X` whose local ring
is a regular local ring. On `Spec R` it is the regular locus `TauCeti.Excellence.regularLocus R`
of the ring `R`, étale morphisms and open immersions identify regular loci, and a locally
Noetherian scheme is regular exactly when its regular locus is everything.

For `X` locally of finite type over a perfect field `k`, the regular locus is the smooth locus of
the structure morphism `X ⟶ Spec k` (The Stacks Project, Section 10.140).
For any morphism `f : X ⟶ Y` locally of finite presentation and smooth at `x`, the local ring of
`X` at `x` is essentially of finite type and formally smooth over the local ring of `Y` at `f x`,
so it is regular when the latter is (`TauCeti.IsRegularLocalRing.of_formallySmooth`). Conversely,
over a perfect field every regular point is smooth
(`AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk`), since a regular local
ring essentially of finite type over `k` is formally smooth over `k`. Perfectness cannot be
dropped: over
`𝔽_p(t)` with `p` an odd prime, the curve `y ^ 2 = x ^ p - t` is regular at its point `y = 0`
but not smooth there. In particular the regular locus over a perfect field is open, which fails
for general locally Noetherian schemes (Stacks, Section 15.48).

## Main declarations

* `AlgebraicGeometry.Scheme.regularLocus`: the points of `X` with regular local ring.
* `AlgebraicGeometry.Scheme.regularLocus_Spec`: on `Spec R` it is the regular locus of `R`.
* `AlgebraicGeometry.Scheme.Hom.mem_regularLocus_of_mem_smoothLocus`: a point at which a morphism
  is smooth and whose image is regular is regular.
* `AlgebraicGeometry.Scheme.Hom.preimage_regularLocus`: flat, formally unramified morphisms locally
  of finite type (for instance étale morphisms and open immersions) identify regular loci.
* `TauCeti.AlgebraicGeometry.isRegular_iff_regularLocus_eq_univ`: a locally Noetherian scheme is
  regular exactly when its regular locus is everything.
* `AlgebraicGeometry.Scheme.Hom.regularLocus_eq_smoothLocus`: over a perfect field, the regular
  locus of a scheme locally of finite type is the smooth locus of its structure morphism.
* `AlgebraicGeometry.Scheme.Hom.smooth_iff_isRegularLocalRing_closedPoints`: over a perfect field,
  a scheme locally of finite type is smooth exactly when its local rings at closed points are
  regular.
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

/-- A flat, formally unramified morphism `f : X ⟶ Y` locally of finite type (for instance an
étale morphism or an open immersion) identifies the regular locus of `X` with the preimage of the
regular locus of `Y`. -/
theorem Hom.preimage_regularLocus {Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [FormallyUnramified f]
    [LocallyOfFiniteType f] :
    f ⁻¹' Y.regularLocus = X.regularLocus := by
  ext x
  exact f.isRegularLocalRing_stalk_iff_of_flat_of_formallyUnramified x

/-- **Smooth points over regular points are regular.** Let `f : X ⟶ Y` be locally of finite
presentation and smooth at `x`. If the local ring of `Y` at `f x` is regular, then so is the local
ring of `X` at `x`: it is essentially of finite type and formally smooth over the local ring of
`Y` at `f x`. -/
theorem Hom.mem_regularLocus_of_mem_smoothLocus {Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {x : X} (hx : x ∈ f.smoothLocus)
    (hfx : f x ∈ Y.regularLocus) : x ∈ X.regularLocus := by
  let := (f.stalkMap x).hom.toAlgebra
  have := f.essFiniteType_stalkMap_toAlgebra x
  have := f.mem_smoothLocus_iff_formallySmooth_stalkMap_toAlgebra.mp hx
  have : IsRegularLocalRing (Y.presheaf.stalk (f x)) := hfx
  exact IsRegularLocalRing.of_formallySmooth (R := Y.presheaf.stalk (f x))

/-- **Regular points over a perfect field are smooth points.** Let `k` be a perfect field and
`f : X ⟶ Spec k` locally of finite type. The local ring of `X` at `x` is regular exactly when `f`
is smooth at `x` (The Stacks Project, Section 10.140). -/
theorem Hom.mem_regularLocus_iff_mem_smoothLocus {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x : X} :
    x ∈ X.regularLocus ↔ x ∈ f.smoothLocus :=
  ⟨fun (_ : IsRegularLocalRing _) ↦ f.mem_smoothLocus_of_isRegularLocalRing_stalk,
    fun h ↦ f.mem_regularLocus_of_mem_smoothLocus h (isRegularLocalRing_stalk_Spec _ _)⟩

/-- **The regular locus over a perfect field is the smooth locus.** If `k` is a perfect field and
`f : X ⟶ Spec k` is locally of finite type, the points of `X` with regular local ring are exactly
the points at which `f` is smooth. -/
theorem Hom.regularLocus_eq_smoothLocus {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    X.regularLocus = f.smoothLocus := by
  ext x
  exact f.mem_regularLocus_iff_mem_smoothLocus

/-- Over a perfect field, the regular locus of a scheme locally of finite type is open. -/
theorem Hom.isOpen_regularLocus_of_perfectField {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : IsOpen X.regularLocus := by
  rw [f.regularLocus_eq_smoothLocus]
  exact f.smoothLocus.isOpen

/-- **Smoothness over a perfect field is tested at closed points.** If `k` is a perfect field and
`f : X ⟶ Spec k` is locally of finite type, then `f` is smooth exactly when the local ring of `X`
at every closed point is regular (The Stacks Project, Lemma 33.25.8, tag 0B8X, for reduced `X`).
The regular locus is the open smooth locus, and a nonempty closed set in the Jacobson scheme `X`
contains a closed point. -/
theorem Hom.smooth_iff_isRegularLocalRing_closedPoints {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Smooth f ↔ ∀ x ∈ closedPoints X, IsRegularLocalRing (X.presheaf.stalk x) := by
  refine ⟨fun _ x _ ↦ ?_, fun h ↦ ?_⟩
  · have hx : x ∈ f.smoothLocus := f.smoothLocus_eq_top ▸ trivial
    exact f.mem_regularLocus_iff_mem_smoothLocus.mpr hx
  · have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
    by_contra hne
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (f.smoothLocus : Set X)ᶜ)
      (Set.nonempty_compl.mpr fun h ↦ hne fun x _ ↦ show x ∈ (f.smoothLocus : Set X) from
        h ▸ Set.mem_univ x)
      f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
    exact hx (f.mem_regularLocus_iff_mem_smoothLocus.mp (h x hxc))

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A locally Noetherian scheme is regular exactly when its regular locus is everything. -/
theorem isRegular_iff_regularLocus_eq_univ [IsLocallyNoetherian X] :
    IsRegular X ↔ X.regularLocus = Set.univ := by
  rw [Scheme.regularLocus_eq_univ_iff, isRegular_iff_forall_stalk]
  exact and_iff_right ‹_›

end TauCeti.AlgebraicGeometry
