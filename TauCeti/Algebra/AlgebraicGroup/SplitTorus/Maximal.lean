/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Chosen split maximal tori over a ring

`SplitMaximalTorus R H r` is a closed immersion of the standard rank-`r` split torus into
the affine group with coordinate algebra `H`, maximal on every geometric fiber. It carries
the coordinate morphism itself, rather than an existence assertion. The corresponding Hopf
ideal and its quotient presentation are recovered from that morphism.

Maximality on geometric fibers is essential: maximality merely among tori over the base
does not imply this condition. A chosen split maximal torus does not include a pinning or
trivializations of the root spaces over the base.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.2.1 and Example 3.2.3.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- A parametrized split maximal torus of an affine group over `R`. The coordinate map is
surjective, expressing a closed immersion, and its defining ideal is maximal as a torus
on every geometric fiber. -/
structure SplitMaximalTorus (R : Type u) [CommRing R]
    (H : CommHopfAlgCat.{u} R) [Algebra.FiniteType R H] (r : ℕ) where
  /-- Restriction of functions to the chosen rank-`r` split torus. -/
  coordinateMap : H ⟶
    (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj
  /-- The chosen torus is a closed subgroup. -/
  surjective : Function.Surjective coordinateMap.hom
  /-- The chosen torus is maximal in every geometric fiber. -/
  maximal : ∀ (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k],
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k)
        (HopfIdeal.kerOfSurjective coordinateMap.hom surjective))

namespace SplitMaximalTorus

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R}
    [Algebra.FiniteType R H] {r : ℕ}

/-- A chosen split maximal torus is determined by its coordinate map. -/
@[ext]
theorem ext {T U : SplitMaximalTorus R H r} (h : T.coordinateMap = U.coordinateMap) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- The Hopf ideal cutting out the chosen split maximal torus. -/
noncomputable def definingIdeal (T : SplitMaximalTorus R H r) : HopfIdeal R H :=
  HopfIdeal.kerOfSurjective T.coordinateMap.hom T.surjective

/-- A function belongs to the defining ideal exactly when its restriction to the torus is zero. -/
@[simp]
theorem mem_definingIdeal (T : SplitMaximalTorus R H r) (x : H) :
    x ∈ T.definingIdeal ↔ T.coordinateMap.hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective T.coordinateMap.hom T.surjective

/-- The quotient coordinate algebra of the chosen torus is the standard split-torus algebra. -/
noncomputable def coordinateIso (T : SplitMaximalTorus R H r) :
    FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _
    (CommHopfAlgCat.quotientKerOfSurjectiveIso T.coordinateMap T.surjective)

/-- The quotient presentation recovers restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_coordinateIso_hom (T : SplitMaximalTorus R H r) :
    FiniteTypeCommHopfAlgCat.mkQuotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal ≫
        T.coordinateIso.hom =
      ObjectProperty.homMk T.coordinateMap :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed subgroup defined by the chosen torus is a split torus over the base ring. -/
theorem splitTorus_quotient (T : SplitMaximalTorus R H r) :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of R H) T.definingIdeal) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨T.coordinateIso.symm⟩⟩

/-- The chosen torus is maximal after extension to any algebraically closed field over `R`. -/
theorem isMaximalTorus_geometricFiber (T : SplitMaximalTorus R H r)
    (k : Type u) [Field k] [Algebra R k] [IsAlgClosed k] :
    HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.baseChange (K := k) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := k) T.definingIdeal) :=
  T.maximal k

end SplitMaximalTorus

end TauCeti
