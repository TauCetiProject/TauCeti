/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Restricting a symplectic form to a subspace

A symplectic form restricts to a subspace on which it stays nondegenerate. A subspace `L`
complementary to its symplectic complement `L^ω` is automatically of that kind, as is `L^ω`, and
then `ω` is the product of the two restrictions under the linear equivalence supplied by the
splitting. A pair of vectors with nonzero symplectic pairing spans such a subspace.

A compatible pair `(ω, J)` restricts to a compatible pair on a `J`-invariant subspace, using
`TauCeti.AlmostComplexStructure.restrict`.

## Main declarations

* `TauCeti.SymplecticForm.restrict`: the restriction of `ω` to a subspace on which it stays
  nondegenerate, again a symplectic form.
* `TauCeti.SymplecticForm.nondegenerate_restrict_orthogonal_of_isCompl`: the splitting
  `V = L ⊕ L^ω` already forces `ω` to restrict nondegenerately to `L^ω` (for `L` itself this is
  Mathlib's `LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal`).
* `TauCeti.SymplecticForm.disjoint_span_pair_orthogonal`: a pair with nonzero symplectic pairing
  spans a subspace disjoint from its symplectic complement.
* `TauCeti.SymplecticForm.orthogonalSpanPairProj`,
  `TauCeti.SymplecticForm.apply_eq_apply_orthogonalSpanPairProj_add`: for `ω e' e = 1`, the
  projection onto the symplectic complement of the plane of `e` and `e'` along that plane, and the
  splitting of `ω` it induces.
* `TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`: the equivalence associated to
  `V = L ⊕ L^ω` is a symplectomorphism from the product of the restricted forms to `ω`.
* `TauCeti.SymplecticForm.restrict_mem_skewAdjointLieSubalgebra`: an element of `sp(V, ω)`
  preserving such a subspace restricts to an element of the symplectic Lie algebra of the
  restricted form.
* `TauCeti.SymplecticForm.Compatible.restrict`: compatibility passes to these restrictions.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The restriction of a symplectic form to a subspace on which it remains nondegenerate.

Nondegeneracy is genuinely a hypothesis: `ω` restricts to `0` on any isotropic subspace. -/
@[expose] def restrict (ω : SymplecticForm V) (L : Submodule ℝ V)
    (h : (ω.toBilinForm.restrict L).Nondegenerate) : SymplecticForm L where
  toBilinForm := ω.toBilinForm.restrict L
  isAlt v := ω.isAlt (v : V)
  nondegenerate := h

lemma restrict_toBilinForm (ω : SymplecticForm V) (L : Submodule ℝ V)
    (h : (ω.toBilinForm.restrict L).Nondegenerate) :
    (ω.restrict L h).toBilinForm = ω.toBilinForm.restrict L :=
  rfl

@[simp]
lemma restrict_apply (ω : SymplecticForm V) (L : Submodule ℝ V)
    (h : (ω.toBilinForm.restrict L).Nondegenerate) (v w : L) :
    ω.restrict L h v w = ω (v : V) (w : V) :=
  rfl

/-- The restriction of `A ∈ sp(V, ω)` to a subspace `L` that it preserves, and on which `ω` stays
nondegenerate, lies in the symplectic Lie algebra of the restricted form. -/
theorem restrict_mem_skewAdjointLieSubalgebra {ω : SymplecticForm V} {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {L : Submodule ℝ V}
    (hL : (ω.toBilinForm.restrict L).Nondegenerate) (hAL : Set.MapsTo A L L) :
    A.restrict hAL ∈ skewAdjointLieSubalgebra (ω.restrict L hL).toBilinForm :=
  -- Both the restricted form and the restricted endomorphism evaluate on `L` as on `V`
  -- (`SymplecticForm.restrict_apply`, `LinearMap.restrict_apply`), definitionally.
  (LinearMap.mem_skewAdjointSubmodule _).2 fun u w ↦
    (LinearMap.mem_skewAdjointSubmodule A).1 hA u w

/-- The symplectic complement of a subspace complementary to it also carries a nondegenerate
restriction of `ω`: a vector of `L^ω` orthogonal to `L^ω` is orthogonal to `L` as well, hence to
`L ⊔ L^ω = V`, and nondegeneracy of `ω` makes it zero. Unlike
`LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` this needs no
finite-dimensionality. -/
lemma nondegenerate_restrict_orthogonal_of_isCompl (ω : SymplecticForm V) {L : Submodule ℝ V}
    (hcompl : IsCompl L (ω.orthogonal L)) :
    (ω.toBilinForm.restrict (ω.orthogonal L)).Nondegenerate :=
  ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl <| by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    refine ω.separatingLeft v fun u => ?_
    obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.1 hcompl.codisjoint u
    have h₁ : ω v a = 0 := mem_orthogonal_iff'.1 hv a ha
    have h₂ : ω v b = 0 := mem_orthogonal_iff'.1 hv' b hb
    simp [h₁, h₂]

/-- Along the splitting `V = L ⊕ L^ω`, the symplectic form is the product of its restrictions to
the two summands: the cross terms vanish by the very definition of the symplectic complement. -/
lemma isSymplectomorphism_prodEquivOfIsCompl (ω : SymplecticForm V) {L : Submodule ℝ V}
    (hcompl : IsCompl L (ω.orthogonal L)) :
    IsSymplectomorphism
      ((ω.restrict L (ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl
          hcompl.disjoint)).prod
        (ω.restrict (ω.orthogonal L) (ω.nondegenerate_restrict_orthogonal_of_isCompl hcompl))) ω
      (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl) := by
  rw [isSymplectomorphism_iff]
  intro p q
  have h₁ : ω (p.1 : V) (q.2 : V) = 0 := mem_orthogonal_iff.1 q.2.property _ p.1.property
  have h₂ : ω (p.2 : V) (q.1 : V) = 0 := mem_orthogonal_iff'.1 p.2.property _ q.1.property
  simp only [Submodule.coe_prodEquivOfIsCompl', prod_apply, restrict_apply, map_add,
    LinearMap.add_apply, h₁, h₂]
  ring

/-- A pair with nonzero symplectic pairing spans a symplectic plane: it is disjoint from its own
symplectic complement, so `ω` restricts to it nondegenerately. -/
lemma disjoint_span_pair_orthogonal (ω : SymplecticForm V) {x y : V} (h : ω x y ≠ 0) :
    Disjoint (Submodule.span ℝ ({x, y} : Set V))
      (ω.orthogonal (Submodule.span ℝ ({x, y} : Set V))) := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hxmem : x ∈ Submodule.span ℝ ({x, y} : Set V) := Submodule.subset_span (by simp)
  have hymem : y ∈ Submodule.span ℝ ({x, y} : Set V) := Submodule.subset_span (by simp)
  have ha : a = 0 := by simpa [h] using mem_orthogonal_iff'.1 hv' y hymem
  have hb : b = 0 := by simpa [h] using mem_orthogonal_iff.1 hv' x hxmem
  simp [ha, hb]

section SpanPair

variable (ω : SymplecticForm V) {e e' : V}

/-- On vectors `w + a e + b e'` with `w` in the symplectic complement of the plane of `e` and `e'`,
where `ω e' e = 1`, the form splits as the form on the complement plus the area form of the
plane: this is `isSymplectomorphism_prodEquivOfIsCompl` for that plane. -/
lemma apply_add_smul_add_smul (h : ω e' e = 1) {w w' : V}
    (hw : w ∈ ω.orthogonal (Submodule.span ℝ {e, e'}))
    (hw' : w' ∈ ω.orthogonal (Submodule.span ℝ {e, e'})) (a b a' b' : ℝ) :
    ω (w + a • e + b • e') (w' + a' • e + b' • e') = ω w w' - a * b' + b * a' := by
  have hp (c d : ℝ) : c • e + d • e' ∈ Submodule.span ℝ {e, e'} :=
    Submodule.mem_span_pair.2 ⟨c, d, rfl⟩
  -- The equivalence and the product of restrictions both unfold to sums, so the
  -- symplectomorphism statement is restated in these terms.
  have key : ω (a • e + b • e' + w) (a' • e + b' • e' + w') =
      ω (a • e + b • e') (a' • e + b' • e') + ω w w' :=
    (ω.isSymplectomorphism_prodEquivOfIsCompl (ω.isAlt.isCompl_span_pair_orthogonal h)).apply
      (⟨_, hp a b⟩, ⟨w, hw⟩) (⟨_, hp a' b'⟩, ⟨w', hw'⟩)
  have hee' : ω e e' = -1 := ω.isAlt.apply_eq_neg_one_of_apply_eq_one h
  rw [apply_smul_add_smul, hee'] at key
  rw [show w + a • e + b • e' = a • e + b • e' + w by abel,
    show w' + a' • e + b' • e' = a' • e + b' • e' + w' by abel, key]
  ring

/-- The projection onto the symplectic complement of the plane of `e` and `e'` along that plane,
where `ω e' e = 1`. It is `v ↦ v - ω(e', v) e + ω(e, v) e'` (`coe_orthogonalSpanPairProj_apply`).
-/
noncomputable def orthogonalSpanPairProj (h : ω e' e = 1) :
    V →ₗ[ℝ] ω.orthogonal (Submodule.span ℝ {e, e'}) :=
  Submodule.projectionOnto _ _ (ω.isAlt.isCompl_span_pair_orthogonal h).symm

/-- The projection is Mathlib's projection onto the symplectic complement along the plane. -/
lemma orthogonalSpanPairProj_def (h : ω e' e = 1) :
    ω.orthogonalSpanPairProj h =
      Submodule.projectionOnto _ _ (ω.isAlt.isCompl_span_pair_orthogonal h).symm :=
  (rfl)

/-- The projection is the identity on the symplectic complement of the plane. -/
lemma orthogonalSpanPairProj_apply_of_mem (h : ω e' e = 1) {w : V}
    (hw : w ∈ ω.orthogonal (Submodule.span ℝ {e, e'})) :
    ω.orthogonalSpanPairProj h w = ⟨w, hw⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hw

/-- The projection is the identity on the symplectic complement of the plane. -/
@[simp]
lemma orthogonalSpanPairProj_apply_coe (h : ω e' e = 1)
    (w : ω.orthogonal (Submodule.span ℝ {e, e'})) :
    ω.orthogonalSpanPairProj h w = w :=
  Submodule.projectionOnto_apply_left _ w

/-- The projection vanishes exactly on the plane of `e` and `e'`. -/
@[simp]
lemma orthogonalSpanPairProj_apply_eq_zero_iff (h : ω e' e = 1) {v : V} :
    ω.orthogonalSpanPairProj h v = 0 ↔ v ∈ Submodule.span ℝ {e, e'} :=
  Submodule.projectionOnto_apply_eq_zero_iff _

/-- The projection kills the first vector of the plane. -/
@[simp]
lemma orthogonalSpanPairProj_apply_left (h : ω e' e = 1) : ω.orthogonalSpanPairProj h e = 0 :=
  (ω.orthogonalSpanPairProj_apply_eq_zero_iff h).2 (Submodule.subset_span (by simp))

/-- The projection kills the second vector of the plane. -/
@[simp]
lemma orthogonalSpanPairProj_apply_right (h : ω e' e = 1) : ω.orthogonalSpanPairProj h e' = 0 :=
  (ω.orthogonalSpanPairProj_apply_eq_zero_iff h).2 (Submodule.subset_span (by simp))

/-- The kernel of the projection is the plane of `e` and `e'`. -/
@[simp]
lemma ker_orthogonalSpanPairProj (h : ω e' e = 1) :
    LinearMap.ker (ω.orthogonalSpanPairProj h) = Submodule.span ℝ {e, e'} :=
  Submodule.ker_projectionOnto _

/-- The projection is onto the symplectic complement. -/
@[simp]
lemma range_orthogonalSpanPairProj (h : ω e' e = 1) :
    LinearMap.range (ω.orthogonalSpanPairProj h) = ⊤ :=
  Submodule.range_projectionOnto _

/-- The formula for the projection. -/
@[simp]
lemma coe_orthogonalSpanPairProj_apply (h : ω e' e = 1) (v : V) :
    (ω.orthogonalSpanPairProj h v : V) = v - ω e' v • e + ω e v • e' := by
  have hw := ω.isAlt.sub_smul_add_smul_mem_orthogonal_span_pair h v
  have hp : ω e' v • e + (-ω e v) • e' ∈ Submodule.span ℝ {e, e'} :=
    Submodule.mem_span_pair.2 ⟨_, _, rfl⟩
  have hv : v = (v - ω e' v • e + ω e v • e') + (ω e' v • e + (-ω e v) • e') := by module
  conv_lhs => rw [hv, map_add, orthogonalSpanPairProj_apply_of_mem _ h hw,
    (orthogonalSpanPairProj_apply_eq_zero_iff _ h).2 hp]
  simp

/-- The splitting of `ω` along the plane of `e` and `e'` and its symplectic complement: `ω` is the
form on the projections to the complement plus the area form of the plane. -/
lemma apply_eq_apply_orthogonalSpanPairProj_add (h : ω e' e = 1) (u v : V) :
    ω u v = ω (ω.orthogonalSpanPairProj h u) (ω.orthogonalSpanPairProj h v) +
      (ω e' u * ω e v - ω e' v * ω e u) := by
  have hdec (x : V) : x = (ω.orthogonalSpanPairProj h x : V) + ω e' x • e + (-ω e x) • e' := by
    rw [coe_orthogonalSpanPairProj_apply]
    module
  have key := ω.apply_add_smul_add_smul h (ω.orthogonalSpanPairProj h u).property
    (ω.orthogonalSpanPairProj h v).property (ω e' u) (-ω e u) (ω e' v) (-ω e v)
  rw [← hdec, ← hdec] at key
  rw [key]
  ring

end SpanPair

/-- A compatible pair `(ω, J)` restricts to a compatible pair on a `J`-invariant subspace on which
`ω` stays nondegenerate. -/
lemma Compatible.restrict {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (hJ : ω.Compatible J) (L : Submodule ℝ V) (h : (ω.toBilinForm.restrict L).Nondegenerate)
    (hL : ∀ x ∈ L, J x ∈ L) : (ω.restrict L h).Compatible (J.restrict L hL) :=
  Compatible.of_tames ((invariant_iff _ _).2 fun x y ↦ by simp [hJ.invariant_apply])
    fun x hx ↦ by simpa using hJ.tames x (by simpa using hx)

end SymplecticForm

end TauCeti
