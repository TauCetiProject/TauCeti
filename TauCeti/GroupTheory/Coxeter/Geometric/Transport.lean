/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Restriction

/-!
# Transport of the geometric representation along maps of index types

Let `M : CoxeterMatrix B` and `M' : CoxeterMatrix B'` be Coxeter matrices and `f : B → B'` a map
along which they agree, `M i j = M' (f i) (f j)`. The linear map
`Finsupp.lmapDomain ℝ ℝ f : (B →₀ ℝ) →ₗ[ℝ] (B' →₀ ℝ)` sends the `i`-th simple root `αᵢ` to the
simple root `α'_{f i}`. It carries the canonical form of `M` to that of `M'`,
`B'(E u, E v) = B(u, v)` (`CoxeterMatrix.geometricForm_mapDomain_mapDomain`), and intertwines the
`i`-th simple reflection with the `f i`-th one, `E σᵢ = σ'_{f i} E`
(`CoxeterMatrix.mapDomain_geometricReflection`). This file shows that it is compatible with the
standard geometric representation (`CoxeterSystem.geometricRepresentation`) itself: it
intertwines the geometric representation of `W` with that of `W'` pulled back along the
homomorphism `CoxeterSystem.parabolicHom` sending `s i` to `s' (f i)`, `E ρ(w) = ρ'(φ w) E`.

Two instances are the ones that matter. When `f` is a bijection `e : B ≃ B'` and `M'` is
`M.reindex e`, the map is the coordinate equivalence `Finsupp.domLCongr e`, and the geometric
representation of the reindexed system is the conjugate of the original one
(`CoxeterSystem.geometricRepresentation_reindex`), also on the presented Coxeter groups through
the inverse of `CoxeterMatrix.reindexGroupEquiv`
(`CoxeterMatrix.geometricRepresentation_reindexGroupEquiv_symm`). When `f` is the inclusion
`Subtype.val` of a set of indices `J`, the map is extension by zero, and the geometric
representation of the standard parabolic subgroup on the span of the simple roots indexed by `J`
is the restriction of the ambient one. Composites of such maps are handled by
`Finsupp.lmapDomain_comp` together with `CoxeterSystem.parabolicHom_comp`.

## Main results

* `CoxeterSystem.mapDomain_geometricRepresentation`,
  `CoxeterSystem.lmapDomain_comp_geometricRepresentation`: the geometric representations are
  intertwined along `CoxeterSystem.parabolicHom`.
* `CoxeterSystem.geometricRepresentation_reindex` and
  `CoxeterMatrix.geometricRepresentation_reindexGroupEquiv_symm`: reindexing conjugates the
  geometric representation by the coordinate equivalence.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Sections 5.3 and 5.5.
-/

public section

namespace CoxeterSystem

variable {B B' W W' : Type*} [Group W] [Group W'] {M : CoxeterMatrix B} {M' : CoxeterMatrix B'}
  (cs : CoxeterSystem M W) {cs' : CoxeterSystem M' W'} {f : B → B'}

/-- **The geometric representations are intertwined by a map of index types** along which the
Coxeter matrices agree, the group homomorphism being `CoxeterSystem.parabolicHom`, which sends
`s i` to `s' (f i)`. For the inclusion of a set of indices this says that the geometric
representation of a standard parabolic subgroup is the restriction of the ambient one to the
span of its simple roots. -/
theorem mapDomain_geometricRepresentation (hf : ∀ i j, M i j = M' (f i) (f j)) (w : W)
    (v : B →₀ ℝ) :
    (cs.geometricRepresentation w v).mapDomain f =
      cs'.geometricRepresentation (cs.parabolicHom cs' hf w) (v.mapDomain f) := by
  induction w using cs.simple_induction generalizing v with
  | simple i =>
    rw [geometricRepresentation_simple, parabolicHom_simple, geometricRepresentation_simple,
      M.mapDomain_geometricReflection hf]
  | one => simp
  | mul w w' hw hw' => simp only [map_mul, mul_apply_eq_comp, hw, hw']

/-- The operator form of `CoxeterSystem.mapDomain_geometricRepresentation`:
`E ∘ ρ(w) = ρ'(φ w) ∘ E` for the extension map `E = Finsupp.lmapDomain ℝ ℝ f` and the
homomorphism `φ = CoxeterSystem.parabolicHom`. -/
theorem lmapDomain_comp_geometricRepresentation (hf : ∀ i j, M i j = M' (f i) (f j)) (w : W) :
    Finsupp.lmapDomain ℝ ℝ f ∘ₗ cs.geometricRepresentation w =
      cs'.geometricRepresentation (cs.parabolicHom cs' hf w) ∘ₗ Finsupp.lmapDomain ℝ ℝ f :=
  LinearMap.ext fun v ↦ cs.mapDomain_geometricRepresentation hf w v

/-- **Reindexing conjugates the geometric representation**: for a bijection `e : B ≃ B'`, the
geometric representation of the reindexed system `cs.reindex e` on the same group is the
conjugate of that of `cs` by the coordinate equivalence `Finsupp.domLCongr e`, which sends the
simple root `αᵢ` to `α'_{e i}`. -/
theorem geometricRepresentation_reindex (e : B ≃ B') (w : W) :
    (cs.reindex e).geometricRepresentation w =
      (Finsupp.domLCongr e).conj (cs.geometricRepresentation w) := by
  have he : ∀ i j, M i j = M.reindex e (e i) (e j) := fun i j ↦ by
    simp [CoxeterMatrix.reindex_apply]
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨u, rfl⟩ := (Finsupp.domLCongr (M := ℝ) (R := ℝ) e).surjective v
  have h := cs.mapDomain_geometricRepresentation (cs' := cs.reindex e) he w u
  rw [parabolicHom_reindex, MonoidHom.id_apply] at h
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa [Finsupp.equivMapDomain_eq_mapDomain] using h.symm

end CoxeterSystem

namespace CoxeterMatrix

variable {B B' : Type*} (M : CoxeterMatrix B)

/-- **Reindexing conjugates the geometric representation of the presented Coxeter group**: for
a bijection `e : B ≃ B'`, the geometric representation of `(M.reindex e).Group` at the image of
`w` under the inverse of `CoxeterMatrix.reindexGroupEquiv` is the conjugate of that of `M.Group`
at `w` by the coordinate equivalence `Finsupp.domLCongr e`. The inverse isomorphism sends the
`i`-th generator to the `e i`-th one (`CoxeterMatrix.reindexGroupEquiv_symm_apply_simple`). -/
theorem geometricRepresentation_reindexGroupEquiv_symm (e : B ≃ B') (w : M.Group) :
    (M.reindex e).toCoxeterSystem.geometricRepresentation ((M.reindexGroupEquiv e).symm w) =
      (Finsupp.domLCongr e).conj (M.toCoxeterSystem.geometricRepresentation w) := by
  have he : ∀ i j, M i j = M.reindex e (e i) (e j) := fun i j ↦ by simp [reindex_apply]
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨u, rfl⟩ := (Finsupp.domLCongr (M := ℝ) (R := ℝ) e).surjective v
  have h := M.toCoxeterSystem.mapDomain_geometricRepresentation
    (cs' := (M.reindex e).toCoxeterSystem) he w u
  rw [toCoxeterSystem_parabolicHom_reindex, MulEquiv.coe_toMonoidHom] at h
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simpa [Finsupp.equivMapDomain_eq_mapDomain] using h.symm

end CoxeterMatrix
