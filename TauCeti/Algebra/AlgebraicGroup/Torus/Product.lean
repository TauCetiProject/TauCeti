/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Product
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Product
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

/-!
# Products of tori

Products of split tori are split over any commutative base ring: the product of their character
groups is still finitely generated and torsion-free. After extending scalars to an algebraic
closure, this also proves that products of tori over a field are tori.

This supplies product closure for the ReductiveGroups roadmap Layer 4 target
"Tori: split and non-split".
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- Products of finite-rank split tori are split tori over any commutative ring. -/
theorem splitTorusCommHopfAlgProperty.tensorProduct (R : Type u) [CommRing R]
    (H K : FiniteTypeCommHopfAlgCat.{u, u} R)
    (hH : splitTorusCommHopfAlgProperty R H) (hK : splitTorusCommHopfAlgProperty R K) :
    splitTorusCommHopfAlgProperty R (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  rw [splitTorusCommHopfAlgProperty_iff] at hH hK
  obtain ⟨n, ⟨e⟩⟩ := hH
  obtain ⟨m, ⟨f⟩⟩ := hK
  let G := SplitTorus.characterGroup (ULift.{u} (Fin n))
  let G' := SplitTorus.characterGroup (ULift.{u} (Fin m))
  exact (splitTorusCommHopfAlgProperty R).prop_of_iso
    (DiagonalizableGroup.productCoordinateRingIso R G G' ≪≫
      FiniteTypeCommHopfAlgCat.tensorProductCongr e f)
    (splitTorusCommHopfAlgProperty_coordinateRing R (FGCommGrpCat.of (G × G')))

/-- Products of tori over a field are tori. -/
theorem torusCommHopfAlgProperty.tensorProduct (k : Type u) [Field k]
    (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) (hK : torusCommHopfAlgProperty k K) :
    torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  rw [torusCommHopfAlgProperty_iff] at hH hK ⊢
  have h := splitTorusCommHopfAlgProperty.tensorProduct (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) K)
    ((splitTorusCommHopfAlgProperty_iff _ _).2 hH)
    ((splitTorusCommHopfAlgProperty_iff _ _).2 hK)
  exact (splitTorusCommHopfAlgProperty_iff _ _).1 <|
    (splitTorusCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      (FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso (AlgebraicClosure k) H K).symm h

end TauCeti
