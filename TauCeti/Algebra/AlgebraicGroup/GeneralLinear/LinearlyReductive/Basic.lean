/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.LinearlyReductive.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Complete reducibility for general linear groups in characteristic zero

Every finite-dimensional rational representation of `GLₙ` over a field of characteristic zero
is completely reducible. This includes rank zero and does not require the field to be
algebraically closed.

Over an algebraic closure, taking invariants under the scalar center preserves surjections,
because the center is a torus. These invariants are ambient subrepresentations. Taking their
`SLₙ`-invariants again preserves surjections, by complete reducibility for `SLₙ`. Since every
invertible matrix over an algebraically closed field is a product of a determinant-one matrix
and a central matrix, the resulting invariant vectors are exactly the `GLₙ`-invariant vectors.
Exactness of invariants gives complete reducibility, which then descends to the original field.

Unlike `SLₙ`, `GLₙ` does not have a semisimple Lie algebra in positive rank, so the
nondegenerate-Killing-form criterion alone does not apply.

## Main declaration

* `TauCeti.GeneralLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`:
  `GLₙ` is linearly reductive in characteristic zero.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.

The proof uses the existing special-linear complete-reducibility theorem, the scalar-center
coordinate isomorphism, and the exactness-of-invariants criterion for comodules.
-/

open CategoryTheory WithConv
open scoped TensorProduct LaurentPolynomial

namespace TauCeti.GeneralLinear

universe u

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Comodule k (coordinateHopfAlgebra k n) M]

private theorem fixed_of_center_and_specialLinear (hn : 0 < n) (m : M)
    (hc : ∀ z ∈ CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n)
      (CommAlgCat.of k k), Comodule.basePointsRepresentation M z m = m)
    (hs : ∀ s : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k),
      Comodule.basePointsRepresentation M
        (BialgHom.mapDomain (SpecialLinear.coordinateMap k n).hom s) m = m) :
    m ∈ Comodule.fixedSubcomodule k (coordinateHopfAlgebra k n) M := by
  rw [Comodule.mem_fixedSubcomodule,
    Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq]
  intro g
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- The inverse of Mathlib's isomorphism is the natural inclusion `toPGL` by construction.
  have hsurj : Function.Surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin n) (R := k)) :=
    (Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty
      (n := Fin n) (F := k)).symm.surjective
  obtain ⟨s, hs'⟩ := hsurj (Matrix.ProjGenLinGroup.mk (pointsMulEquiv n g))
  induction s using QuotientGroup.induction_on with
  | H s =>
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      Matrix.ProjGenLinGroup.mk_eq_mk_iff'] at hs'
    rcases hs' with ⟨z, hz, hsz⟩
    rw [← map_centerPointsSubgroup_pointsMulEquiv_eq_center n (CommAlgCat.of k k)] at hz
    obtain ⟨c, hc', hcz⟩ := hz
    let p := BialgHom.mapDomain (SpecialLinear.coordinateMap k n).hom
      ((SpecialLinear.pointsMulEquiv (A := k) k n).symm s)
    have hp : pointsMulEquiv n p = Matrix.SpecialLinearGroup.toGL s := by
      have hp' := SpecialLinear.quotientPointsHom_pointsMulEquiv_symm k n s
      rw [CommHopfAlgCat.quotientPointsHom_apply] at hp'
      simp only [p, BialgHom.mapDomain_apply, hp', MulEquiv.apply_symm_apply]
    have hg : p * c = g := by
      apply (pointsMulEquiv n).injective
      have hcval : pointsMulEquiv n c = z := hcz
      simpa only [map_mul, hp, hcval] using hsz
    rw [← hg, map_mul, mul_apply_eq_comp, hc c hc']
    exact hs _

variable [CharZero k]
variable {N : Type u} [AddCommGroup N] [Module k N]
  [Comodule k (coordinateHopfAlgebra k n) N]

omit [IsAlgClosed k] in
/-- A `GLₙ`-fixed vector `y` of a subcomodule `F` has, under a surjective comodule map from a
subcomodule `E`, a preimage in `E` fixed by every point of `SLₙ`, by complete reducibility
for `SLₙ`. -/
private theorem exists_specialLinear_fixed_preimage
    {E : Subcomodule k (coordinateHopfAlgebra k n) M}
    {F : Subcomodule k (coordinateHopfAlgebra k n) N}
    (a : Comodule.Hom k (coordinateHopfAlgebra k n) E F) (ha : Function.Surjective a) (y : F)
    (hy : (y : N) ∈ Comodule.fixedSubcomodule k (coordinateHopfAlgebra k n) N) :
    ∃ m : E, a m = y ∧ ∀ s : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k),
      Comodule.basePointsRepresentation M
        (BialgHom.mapDomain (SpecialLinear.coordinateMap k n).hom s) (m : M) = m := by
  -- Keep each corestricted instance local: the ambient and subgroup coactions differ.
  let s := (SpecialLinear.coordinateMap k n).hom
  let aS := Comodule.corestrictHom s.toCoalgHom a
  let _ : Comodule k (SpecialLinear.coordinateHopfAlgebra k n) E :=
    Comodule.Corestrict s.toCoalgHom
  let _ : Comodule k (SpecialLinear.coordinateHopfAlgebra k n) F :=
    Comodule.Corestrict s.toCoalgHom
  let _ : Comodule k (SpecialLinear.coordinateHopfAlgebra k n) N :=
    Comodule.Corestrict s.toCoalgHom
  have hyS : y ∈ @Comodule.fixedSubcomodule k (SpecialLinear.coordinateHopfAlgebra k n) F
      _ _ _ _ _ _ _ (Comodule.Corestrict s.toCoalgHom) := by
    apply ((Comodule.corestrictHom s.toCoalgHom F.subtype).mem_fixedSubcomodule_iff_of_injective
      (by
        intro a b hab
        apply Subtype.ext
        simpa only [Comodule.corestrictHom_apply, Subcomodule.subtype_apply] using hab) y).mp
    rw [Comodule.mem_fixedSubcomodule, Comodule.corestrictHom_apply,
      Subcomodule.subtype_apply, Comodule.corestrict_coact_apply]
    simp only [Comodule.mem_fixedSubcomodule.mp hy, TensorProduct.map_tmul,
      LinearMap.id_apply]
    exact congrArg (fun c ↦ (y : N) ⊗ₜ[k] c) (map_one s)
  obtain ⟨m, hm, hmy⟩ := aS.exists_fixed_preimage_of_isLinearlyReductive
    ((linearlyReductiveCommHopfAlgProperty_iff k _).mp
      (SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra k n)) hyS
        (by
          obtain ⟨m, hm⟩ := ha y
          exact ⟨m, by simpa only [Comodule.Hom.coe_toLinearMap, aS,
            Comodule.corestrictHom_apply] using hm⟩)
  refine ⟨m, by simpa only [aS, Comodule.corestrictHom_apply] using hmy, fun g ↦ ?_⟩
  let _ : Comodule k (SpecialLinear.coordinateHopfAlgebra k n) M :=
    Comodule.Corestrict s.toCoalgHom
  have hfixed := (Comodule.corestrictHom s.toCoalgHom E.subtype).mem_fixedSubcomodule hm
  have hfix := Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one
    (m : M) (by simpa only [Comodule.corestrictHom_apply, Subcomodule.subtype_apply] using
      Comodule.mem_fixedSubcomodule.mp hfixed) g
  rw [Comodule.basePointsRepresentation_corestrict s] at hfix
  exact hfix

private theorem fixedMap_surjective_of_pos (hn : 0 < n)
    (f : Comodule.Hom k (coordinateHopfAlgebra k n) M N) (hf : Function.Surjective f) :
    Function.Surjective f.fixedMap := by
  -- First take center invariants. Normality makes them ambient subcomodules, while
  -- the Laurent coordinate model makes invariant lifting exact.
  let H := coordinateHopfAlgebra k n
  let I := CommHopfAlgCat.centerDefiningIdeal H
  let hI : I.IsNormal := (CommHopfAlgCat.isCentral_centerDefiningIdeal H).isNormal
  let q := (CommHopfAlgCat.mkQuotient H I).hom
  have hC : Coalgebra.IsLinearlyReductive.{u, u, u} k (CommHopfAlgCat.quotient H I) := by
    let e := centerCoordinateLaurentIso (k := k) n hn ≪≫
      _root_.CommHopfAlgCat.isoMk (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ)
    exact (Coalgebra.isLinearlyReductive_iff_of_coalgEquiv k
      (_root_.CommHopfAlgCat.ofIso e).toCoalgEquiv).mpr
        (Coalgebra.isLinearlyReductive_monoidAlgebra k (Multiplicative ℤ))
  obtain ⟨a, ha, hfa⟩ := hI.exists_surjective_hom_weightSpaceOneSubcomodule hC f hf
  intro y
  have hyF : (y : N) ∈ hI.weightSpaceOneSubcomodule N := by
    apply (hI.mem_weightSpaceOneSubcomodule_iff_coact_corestrict N _).mpr
    rw [Comodule.corestrict_coact_apply, Comodule.mem_fixedSubcomodule.mp y.property]
    simp [BialgHom.toCoalgHom_apply]
  obtain ⟨m, hmy, hm⟩ := exists_specialLinear_fixed_preimage n a ha ⟨y, hyF⟩ y.property
  -- The lifted vector is fixed by both subgroups, hence by every ambient point.
  refine ⟨⟨m, fixed_of_center_and_specialLinear n hn (m : M) ?_ hm⟩, Subtype.ext ?_⟩
  · intro z hz
    obtain ⟨c, hc⟩ := hz
    let _ : Comodule k (CommHopfAlgCat.quotient H I) M := Comodule.Corestrict q.toCoalgHom
    have hfix := Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one
      (m : M) ((hI.mem_weightSpaceOneSubcomodule_iff_coact_corestrict M _).mp m.property) c
    rw [Comodule.basePointsRepresentation_corestrict q] at hfix
    exact hc ▸ hfix
  · simpa only [Comodule.Hom.fixedMap_apply] using (hfa m).symm.trans (congrArg Subtype.val hmy)

private theorem linearlyReductive_coordinateHopfAlgebra_algClosed :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [linearlyReductiveCommHopfAlgProperty_iff]
  apply Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective.mpr
  intro M N f hf
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  by_cases hn : 0 < n
  · exact fixedMap_surjective_of_pos n hn f.hom hf
  · have hn0 : n = 0 := by omega
    subst n
    intro y
    obtain ⟨m, hm⟩ := hf y
    refine ⟨⟨m, ?_⟩, Subtype.ext (by simpa using hm)⟩
    rw [Comodule.mem_fixedSubcomodule,
      Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq]
    intro g
    have hg : g = 1 := (pointsMulEquiv 0).injective (by
      simp only [map_one]
      exact Matrix.GeneralLinearGroup.ext fun i ↦ i.elim0)
    simp [hg]

end AlgClosed

public section

/-- **`GLₙ` is linearly reductive in characteristic zero.** Every finite-dimensional rational
representation is completely reducible, over any field of characteristic zero and in every rank. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  apply linearlyReductiveCommHopfAlgProperty.of_baseChange (AlgebraicClosure k)
  exact (linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    (coordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) n).symm
    (linearlyReductive_coordinateHopfAlgebra_algClosed n)

end

end TauCeti.GeneralLinear
