/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Radical.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading

/-!
# The first radical layer of a bound quiver algebra

For an admissible ideal `I` of `kQ`, the degree-one part of `kQ` maps isomorphically onto
`J/J²`, where `J` is the Jacobson radical of `kQ/I`. Thus the classes of the length-one
paths form a basis of the first radical layer. The identification uses the quotient map
itself and does not require the relations to be homogeneous.

This is the linear data used to recover the arrows in the quiver of a basic algebra:
admissible relations cannot identify arrows even after passing to the radical layer.

We use the path-length grading and the identification of the radical with the image of
the arrow ideal. The mathematical reference is Assem–Simson–Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter II, §2.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Finite Q]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

variable (k Q) in
/-- The first radical layer `J/J²` of a bound quiver algebra, as a module over its base field.
The square is pulled back to the radical before taking the module quotient. -/
def boundQuiverRadicalLayer (I : Ideal (pathAlgebra k Q)) [I.IsTwoSided] :=
  (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k ⧸
    ((Ring.jacobson (pathAlgebra k Q ⧸ I) ^ 2).restrictScalars k).comap
      ((Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k).subtype

namespace boundQuiverRadicalLayer

-- Keep the inherited instance bodies unexposed so the quotient representation stays abstract.
@[no_expose]
noncomputable instance : AddCommGroup (boundQuiverRadicalLayer k Q I) := by
  unfold boundQuiverRadicalLayer
  infer_instance

@[no_expose]
noncomputable instance : Module k (boundQuiverRadicalLayer k Q I) := by
  unfold boundQuiverRadicalLayer
  infer_instance

variable (I) in
/-- Send an element of the radical to its class in the first radical layer. -/
noncomputable def mk :
    (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k →ₗ[k]
      boundQuiverRadicalLayer k Q I :=
  Submodule.mkQ _

/-- A radical element has zero class exactly when it lies in the radical square. -/
@[simp]
theorem mk_eq_zero (x : (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k) :
    mk I x = 0 ↔ x.1 ∈ Ring.jacobson (pathAlgebra k Q ⧸ I) ^ 2 :=
  Submodule.Quotient.mk_eq_zero _

/-- Two radical elements have the same class exactly when their difference lies in the
radical square. -/
@[simp]
theorem mk_eq_mk (x y : (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k) :
    mk I x = mk I y ↔ x.1 - y.1 ∈ Ring.jacobson (pathAlgebra k Q ⧸ I) ^ 2 :=
  Submodule.Quotient.eq _

/-- Every first radical-layer class is represented by an element of the radical. -/
theorem mk_surjective : Function.Surjective (mk I) :=
  Submodule.mkQ_surjective _

end boundQuiverRadicalLayer

namespace IsAdmissibleIdeal

private noncomputable def radicalLayerMap (h : IsAdmissibleIdeal I) :
    grade k Q 1 →ₗ[k] boundQuiverRadicalLayer k Q I :=
  (boundQuiverRadicalLayer.mk I).comp
    (((Ideal.Quotient.mkₐ k I).toLinearMap.comp (grade k Q 1).subtype).codRestrict
      ((Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k)
      (fun x => h.mk_mem_jacobson_iff x.1 |>.2
        (by simpa only [Submodule.pow_one] using
          mem_arrowIdeal_pow.2 (grade_le_pathSpan k Q 1 x.2))))

private theorem radicalLayerMap_apply (h : IsAdmissibleIdeal I) (x : grade k Q 1) :
    radicalLayerMap h x = boundQuiverRadicalLayer.mk I
      (⟨Ideal.Quotient.mk I x.1, by
        simpa only [Submodule.restrictScalars_mem] using
          (h.mk_mem_jacobson_iff x.1).2
            (by simpa only [Submodule.pow_one] using
              mem_arrowIdeal_pow.2 (grade_le_pathSpan k Q 1 x.2))⟩ :
        (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k) := (rfl)

private theorem radicalLayerMap_bijective (h : IsAdmissibleIdeal I) :
    Function.Bijective (radicalLayerMap h) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [radicalLayerMap_apply, boundQuiverRadicalLayer.mk_eq_zero] at hx
    have hlong := mem_pathSpan_iff.1 (mem_arrowIdeal_pow.1
      ((h.mk_mem_jacobson_sq_iff x.1).1 hx))
    apply Subtype.ext
    simp only [Submodule.coe_zero]
    apply (pathAlgebraBasis k Q).repr.injective
    apply Finsupp.ext
    intro p
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_contra hp
    have := mem_grade_iff.1 x.2 p (Finsupp.mem_support_iff.2 hp)
    have := hlong p hp
    omega
  · intro y
    obtain ⟨y, rfl⟩ := boundQuiverRadicalLayer.mk_surjective y
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective y.1
    have hpos : f ∈ pathSpan k Q 1 := by
      exact mem_arrowIdeal_pow.1 (by
        simpa only [Submodule.pow_one] using (h.mk_mem_jacobson_iff f).1 (hf ▸ y.2))
    rw [pathSpan_eq_grade_sup_pathSpan_succ k Q 1] at hpos
    obtain ⟨g, hg, z, hz, hgz⟩ := Submodule.mem_sup.1 hpos
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [radicalLayerMap_apply, boundQuiverRadicalLayer.mk_eq_mk]
    -- Equality in `J/J²` is tested on the difference of the ambient representatives.
    have hdiff : Ideal.Quotient.mk I g - y.1 = Ideal.Quotient.mk I (-z) := by
      rw [← hf, ← map_sub, ← hgz]
      simp
    rw [hdiff]
    exact (h.mk_mem_jacobson_sq_iff (-z)).2
      (mem_arrowIdeal_pow.2 (Submodule.neg_mem _ hz))

/-- The quotient map identifies the arrow space with the first radical layer of a
bound quiver algebra. No homogeneity or acyclicity hypothesis is required. -/
noncomputable def radicalLayerEquiv (h : IsAdmissibleIdeal I) :
    grade k Q 1 ≃ₗ[k] boundQuiverRadicalLayer k Q I :=
  LinearEquiv.ofBijective (radicalLayerMap h) (radicalLayerMap_bijective h)

/-- The radical-layer equivalence sends a degree-one element to its quotient class. -/
@[simp]
theorem radicalLayerEquiv_apply (h : IsAdmissibleIdeal I) (x : grade k Q 1) :
    h.radicalLayerEquiv x = boundQuiverRadicalLayer.mk I
      (⟨Ideal.Quotient.mk I x.1, by
        simpa only [Submodule.restrictScalars_mem] using
          (h.mk_mem_jacobson_iff x.1).2
            (by simpa only [Submodule.pow_one] using
              mem_arrowIdeal_pow.2 (grade_le_pathSpan k Q 1 x.2))⟩ :
        (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k) :=
  radicalLayerMap_apply h x

/-- The arrow classes form a basis of `J/J²`. -/
noncomputable def radicalLayerBasis (h : IsAdmissibleIdeal I) :
    Module.Basis (Σ a b : Q, a ⟶ b) k
      (boundQuiverRadicalLayer k Q I) :=
  (arrowBasis k Q).map h.radicalLayerEquiv

/-- A radical-layer basis vector is the class of its arrow. -/
@[simp]
theorem radicalLayerBasis_apply (h : IsAdmissibleIdeal I) (e : Σ a b : Q, a ⟶ b) :
    h.radicalLayerBasis e = boundQuiverRadicalLayer.mk I
      (⟨Ideal.Quotient.mk I (ofArrow e.2.2), by
        simpa only [Submodule.restrictScalars_mem] using
          (h.mk_mem_jacobson_iff _).2 (ofArrow_mem_arrowIdeal e.2.2)⟩ :
        (Ring.jacobson (pathAlgebra k Q ⧸ I)).restrictScalars k) := by
  simp [radicalLayerBasis, coe_arrowBasis_apply]

/-- The `finrank` of the first radical layer is the number of arrows. For a quiver with
finitely many arrows this is its dimension; if there are infinitely many, both sides are zero. -/
theorem finrank_radicalLayer (h : IsAdmissibleIdeal I) :
    Module.finrank k (boundQuiverRadicalLayer k Q I) = Nat.card (Σ a b : Q, a ⟶ b) :=
  Module.finrank_eq_nat_card_basis h.radicalLayerBasis

end IsAdmissibleIdeal

end TauCeti
