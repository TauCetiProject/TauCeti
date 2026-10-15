/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveExactOrder.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Locus
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The finite étale cover of points of naive exact order

For an elliptic curve `E/S` and a natural number `N` invertible on `S`, the scheme
`naiveExactOrderOpens E hN` represents points of naive exact order `N`. Its inclusion in
`E[N]` is both open and closed, so its structural morphism is finite étale. It is also
surjective: every geometric fibre has a point of exact order `N`.

Thus a point of naive exact order can be chosen after a finite étale surjective base change.
This cover is the relative parameter scheme for the naive single-point level problem.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 1.4.4 and §3.7.
* D. Loeffler, *Modular Curves*, lecture notes, Proposition 3.8.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {N : ℕ}
  (hN : ∀ s : S, (N : S.residueField s) ≠ 0)

/-- When `N` is invertible on the base, the exact-order locus is a closed subscheme of `E[N]`
as well as an open subscheme. -/
instance isClosedImmersion_naiveExactOrderOpens_ι :
    IsClosedImmersion (E.naiveExactOrderOpens hN).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι, coe_naiveExactOrderOpens]
  exact (E.isClopen_naiveExactOrderLocus hN).isClosed

/-- The scheme of points of naive exact order `N` is finite over the base when `N` is
invertible on the base. -/
instance isFinite_naiveExactOrderOpens :
    IsFinite ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s⟩⟩
  · have : IsEmpty (E.naiveExactOrderOpens hN : Scheme) :=
      Function.isEmpty ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom)
    infer_instance
  have hN₀ : (N : ℤ) ≠ 0 := by
    exact_mod_cast (fun h : N = 0 ↦ hN s (by simp [h]))
  have := E.isFinite_torsion_hom hN₀
  infer_instance

/-- The scheme of points of naive exact order `N` is étale over the base when `N` is
invertible on the base. -/
instance etale_naiveExactOrderOpens :
    Etale ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) := by
  have := E.etale_torsion_hom_of_forall_intCast_ne_zero (n := N) (by
    intro s
    exact_mod_cast hN s)
  infer_instance

/-- Every geometric fibre of the finite étale exact-order scheme has a point, so its
structural morphism is surjective. -/
instance surjective_naiveExactOrderOpens :
    Surjective ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) := by
  refine ⟨fun s ↦ ?_⟩
  let L := AlgebraicClosure (S.residueField s)
  let t : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫ S.fromSpecResidueField s
  have hNL : (N : L) ≠ 0 := by
    rw [← map_natCast (algebraMap (S.residueField s) L)]
    exact (map_ne_zero_iff _ (algebraMap (S.residueField s) L).injective).mpr (hN s)
  obtain ⟨P, hP⟩ := E.exists_isOfNaiveExactOrder_over t hNL
  let u := (E.naiveExactOrderRepresentableBy hN).homEquiv.symm
    ⟨P, mem_naiveExactOrderSubfunctor_obj.mpr hP⟩
  obtain ⟨a⟩ : Nonempty (Spec (.of L)) := inferInstance
  refine ⟨u.left a, ?_⟩
  have hu : u.left ≫ (E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom = t := Over.w u
  rw [← Scheme.Hom.comp_apply, hu]
  exact Scheme.fromSpecResidueField_apply s _

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
