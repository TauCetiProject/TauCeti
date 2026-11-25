/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms

/-!
# Recovering a subspace from wedges

For a submodule `U` of the space of Plücker coordinates of `p` vectors, `recoverSpan p U`
consists of the vectors `u` such that every wedge having `u` as a factor lies in `U`.
This is a submodule: with all other factors fixed, taking a wedge is linear in `u`.

If `x` is a basis of an `N`-dimensional vector space and `k + p = N`, then
`recoverSpan p (wedgeSpan k p x)` is exactly the span of the first `k` basis vectors.
Thus a subspace can be recovered from the hyperplane spanned by the wedges meeting it,
without choosing a basis of that hyperplane. In particular, finiteness of a family of
such hyperplanes gives finiteness of the recovered subspaces by taking an image.

The recovery identity uses `mem_span_iff_forall_plucker_mem_wedgeSpan`, the coordinate
form of Bombieri–Gubler's Lemma 7.5.33 established in `LinearForms.lean`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), Lemma 7.5.33 and the end of the proof of Theorem 7.2.2.
-/

public section

open Module Set Set.powersetCard

namespace TauCeti

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι]

/-- The vectors all of whose `p`-fold wedges lie in `U`. Equivalently, the intersection,
over all choices of the other factors, of the inverse images of `U` under wedging with
those factors. -/
noncomputable def recoverSpan (p : ℕ) (U : Submodule R (powersetCard ι p → R)) :
    Submodule R (ι → R) :=
  ⨅ (ω : Fin p → ι → R) (b : Fin p), U.comap
    ((AlternatingMap.pi fun s : powersetCard ι p ↦
      Matrix.detRowAlternating.compLinearMap
        (LinearMap.funLeft R R (ofFinEmbEquiv.symm s))).toMultilinearMap.toLinearMap ω b)

/-- A vector is recovered exactly when every wedge containing it lies in the given submodule. -/
@[simp]
theorem mem_recoverSpan {p : ℕ} {U : Submodule R (powersetCard ι p → R)} {u : ι → R} :
    u ∈ recoverSpan p U ↔
      ∀ (ω : Fin p → ι → R) (b : Fin p), ω b = u → plucker ω ∈ U := by
  classical
  have heq (ω : Fin p → ι → R) :
      (AlternatingMap.pi fun s : powersetCard ι p ↦
        Matrix.detRowAlternating.compLinearMap
          (LinearMap.funLeft R R (ofFinEmbEquiv.symm s))) ω = plucker ω := by
    ext s
    rw [plucker_apply]
    rfl
  simp only [recoverSpan, Submodule.mem_iInf, Submodule.mem_comap,
    MultilinearMap.toLinearMap_apply]
  constructor
  · intro h ω b hb
    simpa only [AlternatingMap.coe_multilinearMap, heq, ← hb, Function.update_eq_self] using h ω b
  · intro h ω b
    simpa only [AlternatingMap.coe_multilinearMap, heq] using
      h (Function.update ω b u) b (Function.update_self _ _ _)

/-- Enlarging the submodule of wedges enlarges the recovered submodule. -/
theorem recoverSpan_mono (p : ℕ) :
    Monotone (recoverSpan (R := R) (ι := ι) p) := by
  intro U V h u hu
  exact mem_recoverSpan.mpr fun ω b hb ↦ h (mem_recoverSpan.mp hu ω b hb)

/-- Every vector is recovered from the whole space of wedges. -/
@[simp]
theorem recoverSpan_top (p : ℕ) :
    recoverSpan p (⊤ : Submodule R (powersetCard ι p → R)) = ⊤ := by
  ext u
  simp [mem_recoverSpan]

/-- Recovery commutes with intersections of submodules of wedges. -/
@[simp]
theorem recoverSpan_inf {p : ℕ} (U V : Submodule R (powersetCard ι p → R)) :
    recoverSpan p (U ⊓ V) = recoverSpan p U ⊓ recoverSpan p V := by
  ext u
  simp only [mem_recoverSpan, Submodule.mem_inf]
  simp only [forall_and]

/-- With no factors, the recovery condition has no distinguished factor and recovers every
vector, irrespective of `U`. -/
@[simp]
theorem recoverSpan_zero (U : Submodule R (powersetCard ι 0 → R)) : recoverSpan 0 U = ⊤ := by
  ext u
  simp [mem_recoverSpan]

/-- In positive degree, recovery preserves and reflects properness. The Plücker vectors
span the whole coordinate space, so recovering every vector forces `U` to be the whole space. -/
@[simp]
theorem recoverSpan_eq_top_iff [Finite ι] {p : ℕ} (hp : 0 < p)
    {U : Submodule R (powersetCard ι p → R)} : recoverSpan p U = ⊤ ↔ U = ⊤ := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  let e := ((Pi.basisFun R ι).exteriorPower p).equivFun
  have hU (ω : Fin p → ι → R) : plucker ω ∈ U :=
    mem_recoverSpan.mp (by rw [h]; trivial) ω ⟨0, hp⟩ rfl
  have hle : Submodule.map e.toLinearMap
      (Submodule.span R (range (exteriorPower.ιMulti R p))) ≤ U := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨ω, rfl⟩, rfl⟩
    have heq : e (exteriorPower.ιMulti R p ω) = plucker ω := by
      ext s
      simp only [e, Basis.equivFun_apply, plucker_eq_repr_ιMulti]
    simpa only [LinearEquiv.coe_coe, heq, SetLike.mem_coe] using hU ω
  simpa only [exteriorPower.ιMulti_span, Submodule.map_top, LinearEquiv.range,
    top_le_iff] using hle

section Field

variable {K : Type*} [Field K] [Fintype ι]

/-- Recover the span of the first `k` vectors of a basis from the hyperplane of `p`-fold
wedges meeting those vectors, where `k + p` is the ambient dimension. -/
theorem recoverSpan_wedgeSpan {p k : ℕ} {x : Fin (Fintype.card ι) → ι → K}
    (hx : LinearIndependent K x) (h : k + p = Fintype.card ι) :
    recoverSpan p (wedgeSpan k p x) = Submodule.span K (x '' {j | (j : ℕ) < k}) := by
  ext u
  exact mem_recoverSpan.trans (mem_span_iff_forall_plucker_mem_wedgeSpan hx h u).symm

/- Recovery in `ℚ³` returns the line spanned by the first basis vector from the plane
spanned by `e₀ ∧ e₁` and `e₀ ∧ e₂`. -/
example :
    let e : Fin (Fintype.card (Fin 3)) → Fin 3 → ℚ :=
      Pi.basisFun ℚ (Fin 3) ∘ Fin.cast (Fintype.card_fin 3)
    recoverSpan 2 (wedgeSpan 1 2 e) =
      Submodule.span ℚ {Pi.single (0 : Fin 3) 1} := by
  intro e
  have he : LinearIndependent ℚ e :=
    (Pi.basisFun ℚ (Fin 3)).linearIndependent.comp _ (Fin.cast_injective _)
  rw [recoverSpan_wedgeSpan he (by simp)]
  simp [e]

end Field

end TauCeti
