/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.GroupTheory.Coxeter.Geometric.Sign
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
`Finsupp.lmapDomain_comp` together with `CoxeterSystem.parabolicHom_comp`, and composites of
reindexings by `CoxeterSystem.geometricRepresentation_reindex_reindex`.

When `B` is finite, the coordinate equivalence `Finsupp.linearEquivFunOnFinite` identifies
`B →₀ ℝ` with the space `B → ℝ` of all coordinate functions. The transported representation
`CoxeterSystem.geometricRepresentationFun` acts by `T ρ(w) T⁻¹`, where `T` is that equivalence. It
has the same reflection formula `v ↦ v - 2 (∑ⱼ -cos (π / M i j) vⱼ) eᵢ`, and it is still
faithful.

## Main results

* `CoxeterSystem.mapDomain_geometricRepresentation`,
  `CoxeterSystem.lmapDomain_comp_geometricRepresentation`: the geometric representations are
  intertwined along `CoxeterSystem.parabolicHom`.
* `CoxeterSystem.geometricRepresentation_reindex` and
  `CoxeterMatrix.geometricRepresentation_reindexGroupEquiv_symm`: reindexing conjugates the
  geometric representation by the coordinate equivalence.
* `CoxeterSystem.geometricRepresentation_reindex_refl` and
  `CoxeterSystem.geometricRepresentation_reindex_reindex`: the identity reindexing changes nothing,
  and two reindexings conjugate by the coordinate equivalence of the composite bijection.
* `CoxeterSystem.geometricRepresentationFun`: the geometric representation of a Coxeter system with
  finitely many generators on `B → ℝ`. `CoxeterSystem.geometricRepresentationFun_apply` says that
  it is the conjugate by `Finsupp.linearEquivFunOnFinite`, and
  `CoxeterSystem.geometricRepresentationEquivFun` is the resulting equivalence of representations.
  `CoxeterSystem.geometricRepresentationFun_simple_apply` gives its reflection formula and
  `CoxeterSystem.geometricRepresentationFun_injective` its faithfulness.

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

/-- **The identity reindexing does not change the geometric representation.** -/
@[simp]
theorem geometricRepresentation_reindex_refl :
    (cs.reindex (Equiv.refl B)).geometricRepresentation = cs.geometricRepresentation :=
  MonoidHom.ext fun w ↦ by
    rw [geometricRepresentation_reindex, Finsupp.domLCongr_refl, LinearEquiv.conj_refl]

/-- **Reindexings compose**: reindexing along `e` and then along `e'` conjugates the geometric
representation by the coordinate equivalence of the composite bijection `e.trans e'`. -/
theorem geometricRepresentation_reindex_reindex {B'' : Type*} (e : B ≃ B') (e' : B' ≃ B'')
    (w : W) :
    ((cs.reindex e).reindex e').geometricRepresentation w =
      (Finsupp.domLCongr (e.trans e')).conj (cs.geometricRepresentation w) := by
  rw [geometricRepresentation_reindex, geometricRepresentation_reindex,
    ← Finsupp.domLCongr_trans, ← LinearEquiv.conj_trans, LinearEquiv.trans_apply]

/-! ### Coordinate functions on a finite index set -/

section Finite

variable [Finite B]

/-- **The geometric representation on coordinate functions.** For a finite index set `B`, this is
`CoxeterSystem.geometricRepresentation` transported along the coordinate equivalence
`Finsupp.linearEquivFunOnFinite` from `B →₀ ℝ` to `B → ℝ`, which sends the simple root `αᵢ` to
`Pi.single i 1`. -/
noncomputable def geometricRepresentationFun : Representation ℝ W (B → ℝ) :=
  ((Finsupp.linearEquivFunOnFinite ℝ ℝ B).conjAlgEquiv ℝ).toAlgHom.toMonoidHom.comp
    cs.geometricRepresentation

/-- **The transported representation is the conjugate** `T ρ(w) T⁻¹` by the coordinate
equivalence `T = Finsupp.linearEquivFunOnFinite`. -/
theorem geometricRepresentationFun_apply (w : W) :
    cs.geometricRepresentationFun w =
      (Finsupp.linearEquivFunOnFinite ℝ ℝ B).conj (cs.geometricRepresentation w) :=
  LinearMap.ext fun _ ↦ rfl

/-- The transported representation in coordinates: `ρ(w)` applied to the finitely supported
function with coordinates `v`. -/
@[simp]
theorem geometricRepresentationFun_apply_apply (w : W) (v : B → ℝ) :
    cs.geometricRepresentationFun w v =
      ⇑(cs.geometricRepresentation w (Finsupp.equivFunOnFinite.symm v)) :=
  (rfl)

/-- **The coordinate equivalence is an equivalence of representations** from the geometric
representation on `B →₀ ℝ` to its transport to `B → ℝ`. -/
noncomputable def geometricRepresentationEquivFun :
    Representation.Equiv cs.geometricRepresentation cs.geometricRepresentationFun :=
  .mk (Finsupp.linearEquivFunOnFinite ℝ ℝ B) fun w ↦ LinearMap.ext fun v ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, geometricRepresentationFun_apply,
      LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]

/-- The underlying linear equivalence of `CoxeterSystem.geometricRepresentationEquivFun` is the
coordinate equivalence. -/
@[simp]
theorem geometricRepresentationEquivFun_toLinearEquiv :
    cs.geometricRepresentationEquivFun.toLinearEquiv = Finsupp.linearEquivFunOnFinite ℝ ℝ B :=
  (rfl)

/-- The underlying linear equivalence of the inverse of
`CoxeterSystem.geometricRepresentationEquivFun` is the inverse coordinate equivalence. -/
@[simp]
theorem geometricRepresentationEquivFun_symm_toLinearEquiv :
    cs.geometricRepresentationEquivFun.symm.toLinearEquiv =
      (Finsupp.linearEquivFunOnFinite ℝ ℝ B).symm :=
  (rfl)

@[simp]
theorem geometricRepresentationEquivFun_apply (v : B →₀ ℝ) :
    cs.geometricRepresentationEquivFun v = ⇑v :=
  (rfl)

@[simp]
theorem geometricRepresentationEquivFun_symm_apply (v : B → ℝ) :
    cs.geometricRepresentationEquivFun.symm v = Finsupp.equivFunOnFinite.symm v :=
  (rfl)

/-- **The transported geometric representation is faithful**, by Tits' theorem
`CoxeterSystem.geometricRepresentation_injective`. -/
theorem geometricRepresentationFun_injective : Function.Injective cs.geometricRepresentationFun :=
  ((Finsupp.linearEquivFunOnFinite ℝ ℝ B).conjAlgEquiv ℝ).injective.comp
    cs.geometricRepresentation_injective

end Finite

/-- **The reflection formula on coordinate functions**: the `i`-th simple reflection acts by
`v ↦ v - 2 (∑ⱼ -cos (π / M i j) vⱼ) eᵢ`, where `eᵢ = Pi.single i 1` is the `i`-th simple root and
the sum is the value of the canonical form on `αᵢ` and `v`. -/
theorem geometricRepresentationFun_simple_apply [Fintype B] [DecidableEq B] (i : B)
    (v : B → ℝ) :
    cs.geometricRepresentationFun (cs.simple i) v =
      v - (2 * ∑ j, -Real.cos (Real.pi / M i j) * v j) • Pi.single i 1 := by
  have hform : M.geometricForm (Finsupp.single i 1) (Finsupp.equivFunOnFinite.symm v) =
      ∑ j, -Real.cos (Real.pi / M i j) * v j := by
    simp [Finsupp.equivFunOnFinite_symm_eq_sum, mul_comm]
  ext k
  simp [hform, Pi.single_apply, Finsupp.single_apply, eq_comm]

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
