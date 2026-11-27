/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Averaging
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The invariants are a natural direct summand

Let `K` be a compact group (in practice a compact open subgroup `U` of a locally profinite group,
acting through the restriction) whose pro-order is invertible in the commutative ring `A`, and `V`
a smooth representation of `K` over `A`. The averaging projector `e_K` onto the invariants
(`Representation.smoothAverage`) commutes with the action, so it is an intertwining map
`Representation.smoothAverageHom`. Its range is `V^K` and its kernel is the span of the vectors
`σ k x - x`, so `V = V^K ⊕ ker e_K` as representations of `K`: the invariants are a direct
summand of `V` as an `A[K]`-module, with a complement given by the same formula for every `V`.
The splitting is natural: intertwining maps commute with `e_K`, hence preserve both summands.

## Main declarations

* `Representation.smoothAverageHom σ hK`: the averaging projector `e_K` as an intertwining map.
* `Representation.isCompl_range_ker_smoothAverageHom`: its range and kernel are complementary
  subrepresentations.
* `Representation.smoothAverageEquivProd σ hK`: the splitting `V ≃ V^K × ker e_K` as an equivalence
  of representations of `K`, with `K` acting trivially on the first factor.
* `Representation.IntertwiningMap.comp_smoothAverageHom`: naturality, `f ∘ e_K = e_K ∘ f`, with
  `Representation.IntertwiningMap.map_range_smoothAverageHom_le` and
  `Representation.IntertwiningMap.map_ker_smoothAverageHom_le`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §3.3, Proposition 10(2) and its proof, p. 17.
-/

public section

namespace Representation

variable {A K V W : Type*} [CommRing A] [Group K] [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W] [TopologicalSpace K] [SeparatelyContinuousMul K] [CompactSpace K]
  (σ : Representation A K V) [IsSmooth σ] (hK : TauCeti.HasUnitProOrder A K)

/-- The averaging projector `e_K` onto the invariants, as an intertwining map: it commutes with
the action since `e_K (σ k v) = e_K v = σ k (e_K v)`. -/
noncomputable def smoothAverageHom : σ.IntertwiningMap σ :=
  (σ.smoothAverage hK).intertwiningMap_of_isIntertwiningMap σ σ fun k v ↦ by
    rw [smoothAverage_apply_apply, apply_smoothAverage_apply]

@[simp]
theorem smoothAverageHom_apply (v : V) : σ.smoothAverageHom hK v = σ.smoothAverage hK v :=
  (rfl)

@[simp]
theorem toLinearMap_smoothAverageHom :
    (σ.smoothAverageHom hK).toLinearMap = σ.smoothAverage hK :=
  (rfl)

/-- The range of `e_K` is the subrepresentation of invariants. -/
theorem toSubmodule_range_smoothAverageHom :
    (σ.smoothAverageHom hK).range.toSubmodule = invariants σ := by
  rw [IntertwiningMap.range_toSubmodule, toLinearMap_smoothAverageHom, range_smoothAverage]

/-- The kernel of `e_K` is the span of the vectors `σ k x - x`. -/
theorem toSubmodule_ker_smoothAverageHom :
    (σ.smoothAverageHom hK).ker.toSubmodule = Coinvariants.ker σ := by
  rw [IntertwiningMap.ker_toSubmodule, toLinearMap_smoothAverageHom, ker_smoothAverage]

/-- `K` acts trivially on the range of `e_K`, the invariants. -/
instance isTrivial_range_smoothAverageHom :
    (σ.smoothAverageHom hK).range.toRepresentation.IsTrivial where
  out k := LinearMap.ext fun v ↦ Subtype.ext <| by
    have hv : (v : V) ∈ invariants σ := by
      rw [← toSubmodule_range_smoothAverageHom σ hK]
      exact v.property
    rw [Subrepresentation.coe_toRepresentation_apply, hv k, LinearMap.id_apply]

/-- **The invariants are a direct summand**: the range and the kernel of `e_K` are complementary
subrepresentations. -/
theorem isCompl_range_ker_smoothAverageHom :
    IsCompl (σ.smoothAverageHom hK).range (σ.smoothAverageHom hK).ker := by
  rw [← Subrepresentation.isCompl_toSubmodule, toSubmodule_range_smoothAverageHom,
    IntertwiningMap.ker_toSubmodule, toLinearMap_smoothAverageHom]
  exact (σ.isProj_smoothAverage hK).isCompl

/-- **`V = V^K ⊕ ker e_K` as representations of `K`**, with `K` acting trivially on `V^K`
(`Representation.isTrivial_range_smoothAverageHom`). -/
noncomputable def smoothAverageEquivProd :
    σ.Equiv ((σ.smoothAverageHom hK).range.toRepresentation.prod
      (σ.smoothAverageHom hK).ker.toRepresentation) :=
  Subrepresentation.equivProdOfIsCompl (σ.isCompl_range_ker_smoothAverageHom hK)

/-- The first component of the splitting of `v` is `e_K v`. -/
@[simp]
theorem coe_smoothAverageEquivProd_apply_fst (v : V) :
    ((σ.smoothAverageEquivProd hK v).1 : V) = σ.smoothAverage hK v := by
  have h1 : σ.smoothAverage hK v ∈ (σ.smoothAverageHom hK).range.toSubmodule := by
    rw [toSubmodule_range_smoothAverageHom]
    exact σ.smoothAverage_apply_mem_invariants hK v
  have h2 : v - σ.smoothAverage hK v ∈ (σ.smoothAverageHom hK).ker.toSubmodule := by
    rw [IntertwiningMap.ker_toSubmodule, toLinearMap_smoothAverageHom, LinearMap.mem_ker, map_sub,
      smoothAverage_smoothAverage, sub_self]
  rw [smoothAverageEquivProd, Subrepresentation.equivProdOfIsCompl_apply]
  conv_lhs => rw [show v = σ.smoothAverage hK v + (v - σ.smoothAverage hK v) by abel]
  rw [map_add, Submodule.prodEquivOfIsCompl_symm_apply_left _ _ _ ⟨_, h1⟩,
    Submodule.prodEquivOfIsCompl_symm_apply_right _ _ _ ⟨_, h2⟩]
  simp

variable {σ} in
/-- **The splitting is natural**: an intertwining map between smooth representations commutes with
`e_K`. -/
theorem IntertwiningMap.comp_smoothAverageHom {ρ : Representation A K W} [IsSmooth ρ]
    (f : σ.IntertwiningMap ρ) :
    f.comp (σ.smoothAverageHom hK) = (ρ.smoothAverageHom hK).comp f :=
  by
    ext v
    simpa using IntertwiningMap.map_smoothAverage σ hK f v

variable {σ} in
/-- An intertwining map sends the invariant summand into the invariant summand. -/
theorem IntertwiningMap.map_range_smoothAverageHom_le {ρ : Representation A K W} [IsSmooth ρ]
    (f : σ.IntertwiningMap ρ) {v : V} (hv : v ∈ (σ.smoothAverageHom hK).range) :
    f v ∈ (ρ.smoothAverageHom hK).range := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨f w, by simpa using (IntertwiningMap.map_smoothAverage σ hK f w).symm⟩

variable {σ} in
/-- An intertwining map sends the kernel summand into the kernel summand. -/
theorem IntertwiningMap.map_ker_smoothAverageHom_le {ρ : Representation A K W} [IsSmooth ρ]
    (f : σ.IntertwiningMap ρ) {v : V} (hv : v ∈ (σ.smoothAverageHom hK).ker) :
    f v ∈ (ρ.smoothAverageHom hK).ker := by
  rw [IntertwiningMap.mem_ker, smoothAverageHom_apply] at hv ⊢
  rw [← IntertwiningMap.map_smoothAverage σ hK f v, hv, map_zero]

end Representation
