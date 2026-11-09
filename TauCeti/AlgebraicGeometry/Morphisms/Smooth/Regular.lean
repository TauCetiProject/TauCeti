/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
public import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
public import TauCeti.RingTheory.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
import TauCeti.RingTheory.RegularLocalRing.Smooth
import TauCeti.RingTheory.Smooth.Field

/-!
# Smooth schemes over regular schemes are regular

If `f : X ⟶ Y` is a smooth morphism and `Y` is a locally Noetherian scheme all of whose local
rings are regular, then every local ring of `X` is regular. On affine opens `U ⊆ f⁻¹ V` this is
`TauCeti.IsRegularRing.of_smooth`, since the ring of sections of `Y` over an affine open is a
regular ring exactly when the local rings at its points are regular. In particular every local
ring of a scheme smooth over a field is regular, and so its local rings at codimension-one points
are discrete valuation rings.

Over a perfect field `k` the converse holds: a scheme locally of finite type over `k` whose local
rings are regular is smooth over `k`. Its local rings are then formally smooth over `k`
(`TauCeti.formallySmooth_of_isRegularLocalRing`), since every residue field is formally smooth
over a perfect field. Over an imperfect field a regular scheme need not be smooth: the regular
curve `y ^ 2 = x ^ p - t` over `𝔽_p(t)`, for an odd prime `p`, is not smooth at its point `y = 0`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth`: a scheme smooth over a
  locally Noetherian scheme with regular local rings has regular local rings.
* `TauCeti.AlgebraicGeometry.isDiscreteValuationRing_stalk_of_smooth`: the local rings of an
  integral scheme smooth over a field at its codimension-one points are discrete valuation rings.
* `AlgebraicGeometry.Scheme.Hom.smooth_of_isRegularLocalRing_stalk`: a scheme locally of finite
  type over a perfect field with regular local rings is smooth.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- If `f : X ⟶ Y` is smooth and `Y` is locally Noetherian with regular local rings, then the
local rings of `X` are regular. -/
theorem isRegularLocalRing_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [IsLocallyNoetherian Y] [∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (f.mem_preimage.mpr hxV)
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := (isRegularRing_iff_isRegularLocalRing_stalk hV).mpr fun y _ ↦ inferInstance
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Smooth Γ(Y, V) Γ(X, U) :=
    (HasRingHomProperty.appLE @Smooth f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV).toAlgebra
  have := IsRegularRing.of_smooth (R := Γ(Y, V)) (S := Γ(X, U))
  exact isRegularLocalRing_stalk_of_isRegularRing hU hxU

/-- The local ring of an integral scheme smooth over `k` at a codimension-one point is a discrete
valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsIntegral X] [Smooth (X ↘ Spec (.of k))]
    (y : CodimensionOnePoint X) : IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := by
  have := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) (y : X)
  infer_instance

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti TauCeti.AlgebraicGeometry

universe u

/-- **A regular scheme locally of finite type over a perfect field is smooth**: if `k` is perfect,
`f : X ⟶ Spec k` is locally of finite type and every local ring of `X` is regular, then `f` is
smooth. -/
theorem smooth_of_isRegularLocalRing_stalk {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)] : Smooth f := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine top_unique fun x _ ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  rw [f.mem_smoothLocus_iff_isSmoothAt (U := ⟨U, hU⟩) hxU]
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_ΓSpecIso_inv_comp_appLE hU
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k _
  have : IsRegularRing Γ(X, U) :=
    (isRegularRing_iff_isRegularLocalRing_stalk hU).mpr fun y _ ↦ inferInstance
  exact formallySmooth_of_isRegularLocalRing

end AlgebraicGeometry.Scheme.Hom
