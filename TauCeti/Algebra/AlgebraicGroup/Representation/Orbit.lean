/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.VectorStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.StabilizerDimension
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dense
public import TauCeti.LinearAlgebra.Unimodular
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Orbits of vectors as homogeneous spaces

Let `G = Spec H` be an affine group over a field `k` acting on a finite-dimensional
representation `M`, and let `v ∈ M`. The orbit of `v` is realized inside the projective
completion `P(M × k)` of `M`, where `k` carries the trivial action: it is the orbit of the line
through `(v, 1)`. A point fixes that line exactly when it fixes `v`, because it cannot rescale the
trivial coordinate. So the projective orbit machinery applies with the stabilizer `Stab_G(v)` of
`v` as the line stabilizer.

* The whole orbit lies in the affine chart `M = {t ≠ 0}` of `P(M × k)`, where `t` is the trivial
  coordinate: `t` pulls back to the constant function `1` on `G`.
* The matrix coefficients of `(v, 1)` detect the left cosets of `Stab_G(v)` over every value
  algebra, including nonreduced ones.
* Hence, for a reduced group of finite type over an algebraically closed field, the orbit scheme
  represents the fppf homogeneous quotient `G / Stab_G(v)`.
* In the same setting the orbit satisfies `dim (G • v) + dim Stab_G(v) = dim G`. In
  characteristic zero every group of finite type is reduced and the stabilizer is smooth with Lie
  algebra the annihilator of `v`, so `dim (G • v) = dim 𝔤 • v`, the dimension of the image of the
  differentiated action on `v`.
* An orbit of dimension `dim M` is open and dense in `P(M × k)`, and any two vectors whose orbits
  have dimension `dim M` are carried to each other by a rational point of `G`. In characteristic
  zero this applies to every vector `v` with `𝔤 • v = M`: the orbit of such a vector is open, and
  any two such vectors are conjugate.

Applied to the adjoint representation, these statements describe the adjoint orbit of an element
of the Lie algebra as the homogeneous space of its centralizer.

## Main declarations

* `Comodule.range_projectiveOrbitMap_subset_basicOpen_snd`: the orbit lies in the affine
  chart `M` of `P(M × k)`.
* `Comodule.coset_stabilizerHopfIdeal_eq_iff_exists_units_matrixCoefficient`: the matrix
  coefficients of `(v, 1)` detect the cosets of the stabilizer of `v`.
* `Comodule.fppfHomogeneousQuotientIsoVectorOrbitPoints`: `G / Stab_G(v)` is represented
  by the orbit scheme of `v`.
* `Comodule.topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_stabilizerHopfIdeal`:
  `dim (G • v) + dim Stab_G(v) = dim G`.
* `Comodule.topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range`: in
  characteristic zero, `dim (G • v) = dim 𝔤 • v`.
* `Comodule.isOpen_range_projectiveOrbitMap_mk_one` and
  `Comodule.closure_range_projectiveOrbitMap_mk_one_eq_univ`: an orbit of dimension `dim M` is
  open and dense.
* `Comodule.exists_basePointsRepresentation_eq_of_finrank_le` and
  `Comodule.range_projectiveOrbitMap_mk_one_eq_of_finrank_le`: two vectors whose orbits have
  dimension `dim M` are conjugate under the rational points of `G` and have identical orbit
  schemes.
* `Comodule.isOpen_range_projectiveOrbitMap_mk_one_of_range_eq_top`,
  `Comodule.closure_range_projectiveOrbitMap_mk_one_eq_univ_of_range_eq_top`,
  `Comodule.exists_basePointsRepresentation_eq_of_range_eq_top`, and
  `Comodule.range_projectiveOrbitMap_mk_one_eq_of_range_eq_top`: in characteristic zero, a vector
  `v` with `𝔤 • v = M` has an open dense orbit, and any two such vectors are conjugate and share
  the same orbit image.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.c and §7.c, orbits and isotropy groups.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u v w x

attribute [local instance] prodTrivial

section Chart

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **The orbit of a vector lies in the affine chart.** The orbit of the line through `(v, 1)`
lies in the standard open `M = {t ≠ 0}` of `P(M × k)`, where `t` is the trivial coordinate. This
holds at every scheme point, since `t` pulls back to the constant function `1`. -/
theorem range_projectiveOrbitMap_subset_basicOpen_snd (v : M) :
    Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v)) ⊆
      (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
        (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v) ⁻¹ᵁ
        Proj.basicOpen _
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) := by
    rw [projectiveOrbitMap_preimage_basicOpen_ι, matrixCoefficient_prodTrivial]
    simp
  exact (Scheme.Hom.mem_preimage _).mp hx

/-- Acting on a vector by a rational point leaves its scheme-theoretic orbit in `P(M × k)`
unchanged. -/
@[simp]
theorem range_projectiveOrbitMap_mk_one_basePointsRepresentation
    (g : WithConv (H →ₐ[k] k)) (v : M) :
    Set.range (projectiveOrbitMap (H := H)
        ((basePointsRepresentation M g v, 1) : M × k)
        (Module.isUnimodular_mk_one (basePointsRepresentation M g v))) =
      Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v)) := by
  refine range_projectiveOrbitMap_eq_of_span_basePointsRepresentation_eq (g := g⁻¹)
    (Module.isUnimodular_mk_one (basePointsRepresentation M g v))
    (Module.isUnimodular_mk_one v) ?_
  rw [basePointsRepresentation_prodTrivial, Representation.inv_self_apply]

end Chart

section Coset

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}
  {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]

/-- **Matrix coefficients of `(v, 1)` detect the cosets of the stabilizer of `v`.** Two
algebra-valued points lie in the same left coset of `Stab_G(v)` exactly when the matrix
coefficients of `(v, 1)` at them differ by one common unit. The value algebra may be
nonreduced. -/
theorem coset_stabilizerHopfIdeal_eq_iff_exists_units_matrixCoefficient (v : M)
    (A : CommAlgCat.{x} k) (g h : HopfAlgebra.points (R := k) (H := H) A) :
    (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
        CommHopfAlgCat.quotientPointsSubgroup H (stabilizerHopfIdeal k H v) A) =
          QuotientGroup.mk h ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual k (M × k),
        h.ofConv (matrixCoefficient (C := H) φ ((v, 1) : M × k)) =
          c * g.ofConv (matrixCoefficient (C := H) φ ((v, 1) : M × k)) := by
  refine HopfIdeal.coset_eq_iff_exists_units_matrixCoefficient _ _
    (Module.isUnimodular_mk_one v) A (fun a ↦ ?_) g h
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, stabilizerHopfIdeal_def,
    ← Submodule.stabilizerHopfIdeal_le_ker_iff]
  exact ⟨fun ha x hx ↦ ha x hx, fun ha x hx ↦ ha hx⟩

end Coset

section Quotient

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [_root_.IsReduced H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **The orbit of a vector is the homogeneous space of its stabilizer.** For a reduced affine
group `G` of finite type over an algebraically closed field, the fppf homogeneous quotient
`G / Stab_G(v)` is isomorphic to the sheaf of points of the orbit scheme of `v`, the projective
orbit scheme of the line through `(v, 1)` in `P(M × k)`. -/
noncomputable def fppfHomogeneousQuotientIsoVectorOrbitPoints (v : M) :
    CommHopfAlgCat.fppfHomogeneousQuotient H (stabilizerHopfIdeal k H v) ≅
      projectiveOrbitPointsSheaf (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v) :=
  fppfHomogeneousQuotientIsoProjectiveOrbitPoints _ _ _
    (coset_stabilizerHopfIdeal_eq_iff_exists_units_matrixCoefficient v)

/-- The isomorphism `G / Stab_G(v) ≅ G • v` restricts to the orbit map along the projection
`G ⟶ G / Stab_G(v)`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_fppfHomogeneousQuotientIsoVectorOrbitPoints_hom
    (v : M) :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection H (stabilizerHopfIdeal k H v) ≫
        (fppfHomogeneousQuotientIsoVectorOrbitPoints v).hom.hom =
      toProjectiveOrbitPoints ((v, 1) : M × k) (Module.isUnimodular_mk_one v) := by
  rw [fppfHomogeneousQuotientIsoVectorOrbitPoints,
    fppfHomogeneousQuotientIsoProjectiveOrbitPoints_hom,
    fppfHomogeneousQuotientProjection_comp_toProjectiveOrbitPoints]

end Quotient

section Dimension

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **The dimension of the orbit of a vector.** For a reduced affine group `G` of finite type over
an algebraically closed field, `dim (G • v) + dim Stab_G(v) = dim G`, where `G • v` is the orbit
of the line through `(v, 1)` in `P(M × k)`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_stabilizerHopfIdeal
    [_root_.IsReduced H] (v : M) :
    topologicalKrullDim
        (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v))) +
      ringKrullDim (H ⧸ (stabilizerHopfIdeal k H v).toIdeal) = ringKrullDim H :=
  topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_eq _ _ _ fun a ↦ by
    rw [projectiveOrbitMap_kernelPoint_eq_one_iff, stabilizerHopfIdeal_def,
      Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff]

/-- **The dimension of an orbit in characteristic zero.** For an affine group `G` of finite type
over an algebraically closed field of characteristic zero, the orbit of `v` has the dimension of
the space `𝔤 • v` swept out by the differentiated action of the Lie algebra on `v`. No reducedness
hypothesis is needed: such a group is reduced by Cartier's theorem. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range [CharZero k]
    (v : M) :
    topologicalKrullDim
        (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v))) =
      Module.finrank k
        (LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v)) := by
  have := HopfAlgebra.isReduced_of_charZero k H
  have horbit := topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_stabilizerHopfIdeal
    (k := k) (H := H) v
  have hlie := ringKrullDim_quotient_stabilizerHopfIdeal_add_finrank_range (k := k) (H := H) v
  rw [← hlie, ringKrullDim_quotient_stabilizerHopfIdeal (k := k) (H := H) v] at horbit
  -- Cancel the finite stabilizer dimension; the orbit dimension is neither `⊥` nor `⊤`.
  generalize topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
    (Module.isUnimodular_mk_one v))) = d at horbit ⊢
  induction d using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← Nat.cast_add] at horbit
    exact absurd horbit (WithBot.bot_ne_natCast _)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => norm_cast at horbit
    | coe d => norm_cast at horbit ⊢; omega

end Dimension

section Dense

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- If the orbit of `v` has dimension `dim M`, the orbit of the line through `(v, 1)` has the
maximal dimension `dim (M × k) - 1`. -/
private theorem finrank_prod_le_of_finrank_le (v : M)
    (hv : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v)))) :
    (Module.finrank k (M × k) : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))) + 1 := by
  rw [Module.finrank_prod, Module.finrank_self, Nat.cast_add, Nat.cast_one]
  gcongr

/-- **An orbit of full dimension is dense.** If the orbit of `v` has dimension `dim M`, its
closure is the whole projective completion `P(M × k)` of `M`. -/
theorem closure_range_projectiveOrbitMap_mk_one_eq_univ (v : M)
    (hv : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v)))) :
    closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v))) = Set.univ :=
  closure_range_projectiveOrbitMap_eq_univ _ _ (finrank_prod_le_of_finrank_le v hv)

/-- **An orbit of full dimension is open.** If the orbit of `v` has dimension `dim M`, it is an
open subset of the projective completion `P(M × k)` of `M`. -/
theorem isOpen_range_projectiveOrbitMap_mk_one (v : M)
    (hv : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v)))) :
    IsOpen (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v))) :=
  isOpen_range_projectiveOrbitMap _ _ (finrank_prod_le_of_finrank_le v hv)

/-- **Two orbits of full dimension are conjugate.** If the orbits of `v` and `w` both have
dimension `dim M`, some rational point of `G` carries `v` to `w`. -/
theorem exists_basePointsRepresentation_eq_of_finrank_le (v w : M)
    (hv : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))))
    (hw : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((w, 1) : M × k)
        (Module.isUnimodular_mk_one w)))) :
    ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = w := by
  obtain ⟨g, hg⟩ := exists_span_basePointsRepresentation_eq _ _ _ _
    (finrank_prod_le_of_finrank_le v hv) (finrank_prod_le_of_finrank_le w hw)
  refine ⟨g, ?_⟩
  -- The line through `(g v, 1)` is the line through `(w, 1)`; comparing the trivial coordinates
  -- shows that the scalar relating them is `1`.
  rw [basePointsRepresentation_prodTrivial] at hg
  obtain ⟨c, hc⟩ := Submodule.span_singleton_eq_span_singleton.mp hg
  have h1 : (c : k) = 1 := by simpa [Units.smul_def] using congrArg Prod.snd hc
  simpa [Units.smul_def, h1] using congrArg Prod.fst hc

/-- **Two orbits of full dimension coincide.** If the orbits of `v` and `w` both have dimension
`dim M`, their scheme-theoretic orbit images in `P(M × k)` are equal. -/
theorem range_projectiveOrbitMap_mk_one_eq_of_finrank_le (v w : M)
    (hv : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))))
    (hw : (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((w, 1) : M × k)
        (Module.isUnimodular_mk_one w)))) :
    Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v)) =
      Set.range (projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)) :=
  range_projectiveOrbitMap_eq _ _ _ _ (finrank_prod_le_of_finrank_le v hv)
    (finrank_prod_le_of_finrank_le w hw)

/-- In characteristic zero, the orbit of a vector `v` with `𝔤 • v = M` has dimension `dim M`. -/
private theorem finrank_le_of_range_eq_top [CharZero k] (v : M)
    (hv : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v) = ⊤) :
    (Module.finrank k M : WithBot ℕ∞) ≤
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))) := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range, hv, finrank_top]

/-- **A vector with surjective orbit differential has a dense orbit.** In characteristic zero, if
the differentiated action `X ↦ X • v` of the Lie algebra `𝔤` of `G` is onto `M`, the closure of the
orbit of `v` is the whole projective completion `P(M × k)` of `M`. -/
theorem closure_range_projectiveOrbitMap_mk_one_eq_univ_of_range_eq_top [CharZero k] (v : M)
    (hv : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v) = ⊤) :
    closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v))) = Set.univ :=
  closure_range_projectiveOrbitMap_mk_one_eq_univ v (finrank_le_of_range_eq_top v hv)

/-- **A vector with surjective orbit differential has an open orbit.** In characteristic zero, if
the differentiated action `X ↦ X • v` of the Lie algebra `𝔤` of `G` is onto `M`, the orbit of `v`
is open in the projective completion `P(M × k)` of `M`. -/
theorem isOpen_range_projectiveOrbitMap_mk_one_of_range_eq_top [CharZero k] (v : M)
    (hv : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v) = ⊤) :
    IsOpen (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v))) :=
  isOpen_range_projectiveOrbitMap_mk_one v (finrank_le_of_range_eq_top v hv)

/-- **Vectors with surjective orbit differentials are conjugate.** In characteristic zero, if the
differentiated actions `X ↦ X • v` and `X ↦ X • w` of the Lie algebra `𝔤` of `G` are both onto
`M`, some rational point of `G` carries `v` to `w`. -/
theorem exists_basePointsRepresentation_eq_of_range_eq_top [CharZero k] (v w : M)
    (hv : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v) = ⊤)
    (hw : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip w) = ⊤) :
    ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = w :=
  exists_basePointsRepresentation_eq_of_finrank_le v w (finrank_le_of_range_eq_top v hv)
    (finrank_le_of_range_eq_top w hw)

/-- **Vectors with surjective orbit differentials have the same orbit.** In characteristic zero, if
the differentiated actions `X ↦ X • v` and `X ↦ X • w` of the Lie algebra `𝔤` of `G` are both onto
`M`, the scheme-theoretic orbits of `v` and `w` in `P(M × k)` coincide. -/
theorem range_projectiveOrbitMap_mk_one_eq_of_range_eq_top [CharZero k] (v w : M)
    (hv : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip v) = ⊤)
    (hw : LinearMap.range ((differential (R := k) (H := H) (M := M)).toLinearMap.flip w) = ⊤) :
    Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v)) =
      Set.range (projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)) :=
  range_projectiveOrbitMap_mk_one_eq_of_finrank_le v w (finrank_le_of_range_eq_top v hv)
    (finrank_le_of_range_eq_top w hw)

end Dense

end TauCeti.Comodule
