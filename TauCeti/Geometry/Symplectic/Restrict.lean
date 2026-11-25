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
* `TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`: the equivalence associated to
  `V = L ⊕ L^ω` is a symplectomorphism from the product of the restricted forms to `ω`.
* `TauCeti.SymplecticForm.IsSymplectic.two_le_finrank`: a nonzero symplectic subspace has
  dimension at least two.
* `TauCeti.SymplecticForm.restrict_mem_skewAdjointLieSubalgebra`: an element of `sp(V, ω)`
  preserving such a subspace restricts to an element of the symplectic Lie algebra of the
  restricted form.
* `TauCeti.SymplecticForm.orthogonal_mem_invtSubmodule`: an element of `sp(V, ω)` preserving a
  subspace `L` preserves its symplectic complement `L^ω`.
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

/-- A symplectic subspace containing a nonzero vector `v` has dimension at least two: `v` and a
vector of the subspace pairing with it to one are linearly independent. -/
theorem IsSymplectic.two_le_finrank [FiniteDimensional ℝ V] {ω : SymplecticForm V}
    {L : Submodule ℝ V} (hL : ω.IsSymplectic L) {v : V} (hv : v ∈ L) (hv0 : v ≠ 0) :
    2 ≤ Module.finrank ℝ L := by
  set ω' := ω.restrict L hL.nondegenerate_restrict
  obtain ⟨w, hw⟩ := ω'.exists_apply_eq_one (x := ⟨v, hv⟩) (by simpa using hv0)
  have hli : LinearIndependent ℝ ![(⟨v, hv⟩ : L), w] := by
    refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    have hs : s = 0 := by
      have h := congrArg (fun x ↦ ω' x w) hst
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hw, ω'.isAlt w,
        map_zero, LinearMap.zero_apply] at h
      simpa using h
    subst hs
    refine ⟨rfl, (by simpa using hst : t = 0 ∨ w = 0).resolve_right fun hw0 ↦ ?_⟩
    simp [hw0] at hw
  simpa using hli.fintype_card_le_finrank

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

/-- **Invariance of the symplectic complement.** An element `A ∈ sp(V, ω)` preserving a subspace
`L` preserves its symplectic complement `L^ω`: for `v ∈ L^ω` and `y ∈ L`,
`ω(y, A v) = -ω(A y, v) = 0`. -/
theorem orthogonal_mem_invtSubmodule {ω : SymplecticForm V} {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {L : Submodule ℝ V}
    (hL : L ∈ Module.End.invtSubmodule A) :
    ω.orthogonal L ∈ Module.End.invtSubmodule A :=
  (Module.End.mem_invtSubmodule _).2 fun v hv ↦ mem_orthogonal_iff.2 fun y hy ↦ by
    have h : ω (A y) v = -ω y (A v) :=
      ((LinearMap.mem_skewAdjointSubmodule A).1 hA y v).trans (map_neg _ _)
    rwa [mem_orthogonal_iff.1 hv _ ((Module.End.mem_invtSubmodule _).1 hL hy), eq_comm,
      neg_eq_zero] at h

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

/-- A compatible pair `(ω, J)` restricts to a compatible pair on a `J`-invariant subspace on which
`ω` stays nondegenerate. -/
lemma Compatible.restrict {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (hJ : ω.Compatible J) (L : Submodule ℝ V) (h : (ω.toBilinForm.restrict L).Nondegenerate)
    (hL : ∀ x ∈ L, J x ∈ L) : (ω.restrict L h).Compatible (J.restrict L hL) :=
  Compatible.of_tames ((invariant_iff _ _).2 fun x y ↦ by simp [hJ.invariant_apply])
    fun x hx ↦ by simpa using hJ.tames x (by simpa using hx)

end SymplecticForm

end TauCeti
