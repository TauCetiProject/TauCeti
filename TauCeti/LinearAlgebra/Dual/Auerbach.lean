/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Auerbach's lemma for a compact family of linear forms

Let `U` be a vector space of finite dimension `n` over a field `K`, and let `(ℓ a)_{a ∈ 𝒜}` be a
family of linear forms on `U`, indexed by a compact space `𝒜`, whose only common zero is `0`.
Values in `K` are measured through a ring homomorphism `φ : K →+* L` into a normed field, and the
family is assumed continuous in the weak sense that `a ↦ φ (ℓ a v)` is continuous for each
`v ∈ U`. Then `n` members `ℓ (a 1), …, ℓ (a n)` of the family form the dual basis of a basis
`z 1, …, z n` of `U` all of whose vectors are small for the whole family:
`‖φ (ℓ a (z k))‖ ≤ 1` for every `a ∈ 𝒜` and every `k`
(`TauCeti.exists_basis_coord_eq_and_norm_le_one`).

This is the classical argument by a determinant of largest size. Against a fixed basis of the
dual space, the norm of `φ` of the determinant of `n` forms of the family is a continuous function
of their indices on the compact space `𝒜ⁿ`, so it attains its maximum; the maximum is positive
because the forms span the dual space. By Cramer's rule
(`Module.Basis.det_smul_mk_coord_eq_det_update`), replacing the `k`-th maximising form by `ℓ a`
multiplies the determinant by `ℓ a (z k)`, which therefore has norm at most `1`.

For `K = L = ℝ` or `ℂ`, `φ` the identity and `𝒜` the closed unit ball of the dual of a norm on
`U`, this is Auerbach's lemma: a finite-dimensional normed space has a basis of unit vectors whose
coordinate functionals have norm one (`TauCeti.exists_basis_norm_eq_one_and_norm_coord_eq_one`).
Over other fields, with `φ` an embedding into a completion such as `ℚ_p`, it gives bases whose
vectors have bounded values under a whole compact family of forms.

## Main statements

* `TauCeti.exists_basis_coord_eq_and_norm_le_one`: Auerbach's lemma for a compact family of
  linear forms with no common nonzero zero.
* `TauCeti.exists_basis_norm_eq_one_and_norm_coord_eq_one`: Auerbach's lemma for a
  finite-dimensional normed space over `ℝ` or `ℂ`.

## References

* H. Auerbach, *On the area of convex curves with conjugate diameters*, PhD thesis, University of
  Lwów, 1930.
* J. Lindenstrauss, L. Tzafriri, *Classical Banach Spaces I*, Springer, 1977, Section 1.c
  (Auerbach bases, by a determinant of largest size).
-/

public section

open Module Function

namespace TauCeti

variable {ι 𝒜 K U : Type*} [Fintype ι] [Field K] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U]

/-- If linear forms `ℓ a` on a finite-dimensional space have no common nonzero zero, then for every
basis `e` of the dual space some `#ι` of them have invertible determinant relative to `e`, that is,
form a basis of the dual space. -/
private theorem exists_isUnit_det_comp [DecidableEq ι] (e : Basis ι K (Dual K U))
    {ℓ : 𝒜 → Dual K U} (hℓ : ∀ v, (∀ a, ℓ a v = 0) → v = 0) :
    ∃ a : ι → 𝒜, IsUnit (e.det (ℓ ∘ a)) := by
  -- The forms span the dual space, so some subfamily of them is a basis of it.
  have hspan : Submodule.span K (Set.range ℓ) = ⊤ :=
    Submodule.span_eq_top_of_ne_zero fun v hv => by
      by_contra! h
      exact hv (hℓ v fun a => h _ ⟨a, rfl⟩)
  obtain ⟨κ, f, -, hsp, hli⟩ := exists_linearIndependent' K ℓ
  let w : Basis κ K (Dual K U) := Basis.mk hli (by rw [hsp, hspan])
  refine ⟨f ∘ (w.indexEquiv e).symm, e.is_basis_iff_det.1 ?_⟩
  have hw : ℓ ∘ f ∘ (w.indexEquiv e).symm = ⇑(w.reindex (w.indexEquiv e)) := by
    rw [Basis.coe_reindex, Basis.coe_mk, comp_assoc]
  rw [hw]
  exact ⟨Basis.linearIndependent _, Basis.span_eq _⟩

variable [TopologicalSpace 𝒜] {L : Type*} [NormedField L]

/-- The norm of `φ` of the determinant of `#ι` forms of a family, relative to a basis of the dual
space, is continuous in their indices when each `a ↦ φ (ℓ a v)` is continuous. -/
private theorem continuous_norm_map_det_comp [DecidableEq ι] (e : Basis ι K (Dual K U))
    {ℓ : 𝒜 → Dual K U} (φ : K →+* L) (hφ : ∀ v, Continuous fun a => φ (ℓ a v)) :
    Continuous fun a : ι → 𝒜 => ‖φ (e.det (ℓ ∘ a))‖ := by
  have hmat : ∀ a : ι → 𝒜, φ (e.det (ℓ ∘ a)) = ((e.toMatrix (ℓ ∘ a)).map φ).det := fun a => by
    rw [Basis.det_apply, RingHom.map_det, RingHom.mapMatrix_apply]
  simp_rw [hmat]
  refine (Continuous.matrix_det <| continuous_matrix fun i j => ?_).norm
  -- The entries of the matrix of the forms relative to `e` are their values at the vectors of
  -- `U` that the coordinate functionals of `e` evaluate at.
  simp only [Matrix.map_apply, Basis.toMatrix_apply, comp_apply, ← Basis.coord_apply,
    ← apply_evalEquiv_symm_apply K U _ (e.coord i)]
  exact (hφ _).comp (continuous_apply j)

/-- **Auerbach's lemma for a compact family of linear forms.** Let `U` be a vector space of finite
dimension over a field `K`, and let `ℓ a`, for `a` in a compact space `𝒜`, be linear forms on `U`
whose only common zero is `0`. Let `φ : K →+* L` be a ring homomorphism into a normed field such
that `a ↦ φ (ℓ a v)` is continuous for every `v`. Then for any index type `ι` with
`finrank K U` elements there are `a : ι → 𝒜` and a basis `z` of `U` such that the forms `ℓ (a j)`
are the coordinate functionals of `z`, that is, the dual basis of `z`
(`Module.Basis.coe_dualBasis`), and `‖φ (ℓ a' (z k))‖ ≤ 1` for all `a' ∈ 𝒜` and all `k`. -/
theorem exists_basis_coord_eq_and_norm_le_one [CompactSpace 𝒜] (ℓ : 𝒜 → Dual K U)
    (hℓ : ∀ v, (∀ a, ℓ a v = 0) → v = 0) (φ : K →+* L)
    (hφ : ∀ v, Continuous fun a => φ (ℓ a v)) (hι : Fintype.card ι = finrank K U) :
    ∃ (a : ι → 𝒜) (z : Basis ι K U),
      (∀ j, z.coord j = ℓ (a j)) ∧ ∀ a' k, ‖φ (ℓ a' (z k))‖ ≤ 1 := by
  classical
  -- A fixed basis `e` of the dual space, against which determinants are taken.
  let e : Basis ι K (Dual K U) :=
    ((finBasisOfFinrankEq K U hι.symm).reindex (Fintype.equivFin ι).symm).dualBasis
  set D : (ι → 𝒜) → ℝ := fun a => ‖φ (e.det (ℓ ∘ a))‖ with hD
  -- Choose indices maximising `D`; the maximum is positive, so these forms are a basis `w`.
  obtain ⟨a₀, ha₀⟩ := exists_isUnit_det_comp e hℓ
  obtain ⟨a, ha⟩ := (continuous_norm_map_det_comp e φ hφ).exists_forall_ge' a₀ (by
    simp [Filter.cocompact_eq_bot])
  have hpos : 0 < D a :=
    (norm_pos_iff.2 (φ.injective.ne_iff' (map_zero φ) |>.2 ha₀.ne_zero)).trans_le (ha a₀)
  obtain ⟨hli, hsp⟩ := (e.is_basis_iff_det (v := ℓ ∘ a)).2 <| isUnit_iff_ne_zero.2 fun h => by
    simp [hD, h] at hpos
  set w : Basis ι K (Dual K U) := Basis.mk hli hsp.ge with hw
  -- `z` is the basis of `U` whose dual basis is `w`.
  let z : Basis ι K U := w.dualBasis.map (evalEquiv K U).symm
  have hz : ∀ (f : Dual K U) k, f (z k) = w.coord k f := fun f k => by
    simp [z, Basis.coe_dualBasis]
  refine ⟨a, z, fun j => z.ext fun k => ?_, fun a' k => ?_⟩
  · rw [Basis.coord_apply, Basis.repr_self, hz,
      show ℓ (a j) = w j by rw [hw, Basis.mk_apply, comp_apply], Basis.coord_apply,
      Basis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  -- Cramer's rule: replacing the `k`-th form by `ℓ a'` multiplies the determinant by
  -- `w.coord k (ℓ a') = ℓ a' (z k)`, and the result is at most the maximum `D a`.
  have hcramer : D (update a k a') = D a * ‖φ (ℓ a' (z k))‖ := by
    have := LinearMap.congr_fun (e.det_smul_mk_coord_eq_det_update hli hsp.ge k) (ℓ a')
    rw [← hw] at this
    simp only [LinearMap.smul_apply, smul_eq_mul, MultilinearMap.toLinearMap_apply,
      AlternatingMap.coe_multilinearMap] at this
    simp only [hD, comp_update, ← this, hz, map_mul, norm_mul]
  have hle : D (update a k a') ≤ D a := ha _
  rw [hcramer] at hle
  exact (mul_le_iff_le_one_right hpos).1 hle

/-- **Auerbach's lemma.** A finite-dimensional normed space over `ℝ` or `ℂ` has a basis of unit
vectors whose coordinate functionals have operator norm one. -/
theorem exists_basis_norm_eq_one_and_norm_coord_eq_one {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (hι : Fintype.card ι = finrank 𝕜 E) :
    ∃ z : Basis ι 𝕜 E, ∀ k, ‖z k‖ = 1 ∧ ‖LinearMap.toContinuousLinearMap (z.coord k)‖ = 1 := by
  -- Apply the general statement to the closed unit ball of the dual space.
  have := FiniteDimensional.proper_rclike 𝕜 (StrongDual 𝕜 E)
  have : CompactSpace (Metric.closedBall (0 : StrongDual 𝕜 E) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  have hball (f : Metric.closedBall (0 : StrongDual 𝕜 E) 1) : ‖(f : StrongDual 𝕜 E)‖ ≤ 1 :=
    mem_closedBall_zero_iff.1 f.property
  obtain ⟨a, z, hcoord, hle⟩ := exists_basis_coord_eq_and_norm_le_one
    (fun f : Metric.closedBall (0 : StrongDual 𝕜 E) 1 => (f : StrongDual 𝕜 E).toLinearMap)
    (fun v hv => by
      obtain ⟨g, hg, hgv⟩ := exists_dual_vector'' 𝕜 v
      simpa [hgv] using hv ⟨g, by simpa using hg⟩)
    (RingHom.id 𝕜)
    (fun v => (ContinuousLinearMap.apply 𝕜 𝕜 v).continuous.comp continuous_subtypeVal) hι
  simp only [RingHom.id_apply, ContinuousLinearMap.coe_coe] at hle
  -- The coordinate functional `z.coord k` is the form `a k` of the unit ball.
  have hak : ∀ k, LinearMap.toContinuousLinearMap (z.coord k) = a k := fun k =>
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hcoord])
  have hone : ∀ k, (a k : StrongDual 𝕜 E) (z k) = 1 := fun k => by
    rw [← hak, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same]
  -- `1 = ‖(a k) (z k)‖ ≤ ‖a k‖ * ‖z k‖`, and both factors are at most `1`.
  have hz : ∀ k, ‖z k‖ ≤ 1 := fun k => by
    obtain ⟨g, hg, hgv⟩ := exists_dual_vector'' 𝕜 (z k)
    simpa [hgv] using hle ⟨g, by simpa using hg⟩ k
  have hmul : ∀ k, 1 ≤ ‖(a k : StrongDual 𝕜 E)‖ * ‖z k‖ := fun k => by
    simpa [hone] using (a k : StrongDual 𝕜 E).le_opNorm (z k)
  refine ⟨z, fun k => ⟨le_antisymm (hz k) ?_, ?_⟩⟩
  · nlinarith [hmul k, hball (a k), norm_nonneg (z k)]
  · rw [hak k]
    exact le_antisymm (hball _) (by nlinarith [hmul k, hz k, norm_nonneg (a k : StrongDual 𝕜 E)])

end TauCeti
