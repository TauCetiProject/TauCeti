/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.Punctured
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The de Rham cohomology of spheres through Mayer–Vietoris

The unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space is covered by the
complements `U = Sⁿ \ {v}` and `V = Sⁿ \ {-v}` of two antipodal points. Stereographic projection
from `v` is a diffeomorphism from `U` onto `ℝⁿ` (`TauCeti.stereographicDiffeomorph`), so `U`, and
likewise `V`, has no de Rham cohomology in positive degree
(`TauCeti.subsingleton_deRhamCohomology_sphere_compl_singleton`), and it maps `U ⊓ V`
diffeomorphically onto the punctured space `ℝⁿ \ {0}`
(`TauCeti.stereographicPuncturedDiffeomorph`), whose cohomology is that of the sphere `Sⁿ⁻¹`
(`TauCeti.deRhamCohomology.puncturedSpaceEquivSphere`).

The Mayer–Vietoris connecting map of this cover is therefore an isomorphism
`H^k(U ⊓ V) ≃ H^{k+1}(Sⁿ)` for `k ≥ 1`. Composing it with the identifications above shows that
`H^k(Sⁿ⁻¹)` and `H^{k+1}(Sⁿ)` are isomorphic for `k ≥ 1`
(`TauCeti.nonempty_linearEquiv_deRhamCohomology_sphere_succ`, which records only that an
isomorphism exists). In degree `k = 0` the connecting map is still surjective, and for `n ≥ 2`
the intersection `U ⊓ V` is connected, so every class in `H⁰(U ⊓ V)` is constant and the
connecting map vanishes on it: `H¹(Sⁿ) = 0`
(`TauCeti.subsingleton_deRhamCohomology_sphere_one`). Induction on the degree then gives
`H^k(Sⁿ) = 0` for `0 < k < n` (`TauCeti.subsingleton_deRhamCohomology_sphere`).

For `n = 1` the intersection `U ⊓ V` is diffeomorphic to `ℝ \ {0}`, whose cohomology is that of
the two-point sphere `S⁰`, so `H⁰(U ⊓ V)` is two-dimensional. Since `U` and `V` are connected, the
kernel of the degree-zero connecting map is the line of constant classes
(`TauCeti.deRhamCohomology.ker_mayerVietorisδ_zero`), and the map is surjective, so `H¹(S¹)` is
one-dimensional. The suspension isomorphism carries this to `Hⁿ(Sⁿ)` for every `n ≥ 1`
(`TauCeti.finrank_deRhamCohomology_sphere_self`). Together with the connectedness of `Sⁿ` and the
vanishing of de Rham cohomology above the dimension, this computes `H^k(Sⁿ)` in every degree
(`TauCeti.finrank_deRhamCohomology_sphere`).

## Main results

* `TauCeti.subsingleton_deRhamCohomology_sphere_compl_singleton`: the sphere minus a point has no
  de Rham cohomology in positive degree.
* `TauCeti.nonempty_linearEquiv_deRhamCohomology_sphere_succ`: `H^{k+1}(Sⁿ) ≃ H^{k+2}(Sⁿ⁺¹)`.
* `TauCeti.subsingleton_deRhamCohomology_sphere_one`: `H¹(Sⁿ) = 0` for `n ≥ 2`.
* `TauCeti.subsingleton_deRhamCohomology_sphere`: `H^k(Sⁿ) = 0` for `0 < k < n`.
* `TauCeti.finrank_deRhamCohomology_zero_sphere_of_finrank_eq_one`: `H⁰(S⁰)` is two-dimensional.
* `TauCeti.finrank_deRhamCohomology_sphere_self`: `Hⁿ(Sⁿ)` is one-dimensional for `n ≥ 1`.
* `TauCeti.finrank_deRhamCohomology_sphere`: for `n ≥ 1`, `H^k(Sⁿ)` is one-dimensional when
  `k = 0` or `k = n`, and zero otherwise.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, Theorem 17.21 (the
  cohomology of spheres).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set TopologicalSpace Metric Module
open scoped ContDiff Manifold

namespace TauCeti

section Cover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The unit sphere of a real inner product space of positive dimension is nonempty. -/
private theorem nonempty_sphere {m : ℕ} (hE : finrank ℝ E = m + 1) :
    Nonempty (sphere (0 : E) 1) :=
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

/-- The sphere minus a point has no de Rham cohomology in positive degree: stereographic projection
identifies it with `ℝⁿ`, where every closed form of positive degree is exact. -/
theorem subsingleton_deRhamCohomology_sphere_compl_singleton (v : sphere (0 : E) 1) (k : ℕ) :
    Subsingleton (deRhamCohomology (𝓡 n)
      (⟨{v}ᶜ, isOpen_compl_singleton⟩ : Opens (sphere (0 : E) 1)) (k + 1)) := by
  have := subsingleton_deRhamCohomology_normedSpace (EuclideanSpace ℝ (Fin n)) k
  exact (deRhamCohomology.equivOfDiffeomorph (stereographicDiffeomorph v) (k + 1)).toEquiv.symm
    |>.subsingleton

/-- **The first de Rham cohomology of a sphere of dimension at least two vanishes.** For `n ≥ 2`,
`H¹` of the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space is zero. -/
theorem subsingleton_deRhamCohomology_sphere_one (hn : 1 < n) :
    Subsingleton (deRhamCohomology (𝓡 n) (sphere (0 : E) 1) 1) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨v⟩ := nonempty_sphere (E := E) (m := n) Fact.out
  set U : Opens (sphere (0 : E) 1) := ⟨{v}ᶜ, isOpen_compl_singleton⟩
  set V : Opens (sphere (0 : E) 1) := ⟨{-v}ᶜ, isOpen_compl_singleton⟩
  -- `U ⊓ V` is connected, as it is diffeomorphic to `ℝⁿ \ {0}` with `n ≥ 2`. The domain of
  -- `stereographicPuncturedDiffeomorph v` is the open set with carrier `{v}ᶜ ∩ {-v}ᶜ`, which
  -- `Opens.mk_inf_mk` identifies with `U ⊓ V`.
  have : ConnectedSpace (U ⊓ V : Opens (sphere (0 : E) 1)) := by
    simp only [U, V, Opens.mk_inf_mk, Set.inf_eq_inter]
    exact (stereographicPuncturedDiffeomorph v).toHomeomorph.connectedSpace_iff.mpr <|
      isConnected_iff_connectedSpace.mp <| isConnected_compl_singleton_of_one_lt_rank
        (by rw [← finrank_eq_rank, finrank_euclideanSpace_fin]; exact_mod_cast hn) 0
  rw [(deRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop _ (compl_singleton_sup_compl_singleton_neg_eq_top v)) 1).toEquiv
      |>.subsingleton_congr]
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨d, rfl⟩ := deRhamCohomology.mayerVietorisδ_surjective
    (subsingleton_deRhamCohomology_sphere_compl_singleton v 0)
    (subsingleton_deRhamCohomology_sphere_compl_singleton (-v) 0) c
  obtain ⟨r, rfl⟩ := deRhamCohomology.exists_eq_const d
  exact deRhamCohomology.mayerVietorisδ_const U V r

end Cover

section Suspension

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **The suspension isomorphism for the de Rham cohomology of spheres.** For every `k`, the de
Rham cohomology `H^{k+1}(Sⁿ)` of `Sⁿ`, the unit sphere of `ℝⁿ⁺¹`, is isomorphic to the de Rham
cohomology `H^{k+2}(Sⁿ⁺¹)` of `Sⁿ⁺¹`, the unit sphere of an `(n + 2)`-dimensional real inner
product space. The statement only asserts that an isomorphism exists. -/
theorem nonempty_linearEquiv_deRhamCohomology_sphere_succ [Fact (finrank ℝ E = n + 1 + 1)]
    (k : ℕ) :
    Nonempty (deRhamCohomology (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (k + 1) ≃ₗ[ℝ]
      deRhamCohomology (𝓡 (n + 1)) (sphere (0 : E) 1) (k + 2)) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
  obtain ⟨v⟩ := nonempty_sphere (E := E) (m := n + 1) Fact.out
  have e := deRhamCohomology.mayerVietorisδEquiv
    (subsingleton_deRhamCohomology_sphere_compl_singleton (n := n + 1) v k)
    (subsingleton_deRhamCohomology_sphere_compl_singleton (-v) k)
    (subsingleton_deRhamCohomology_sphere_compl_singleton v (k + 1))
    (subsingleton_deRhamCohomology_sphere_compl_singleton (-v) (k + 1))
  -- Identify the intersection of the cover with the domain `{v}ᶜ ∩ {-v}ᶜ` of
  -- `stereographicPuncturedDiffeomorph v`.
  simp only [Opens.mk_inf_mk, Set.inf_eq_inter] at e
  exact ⟨(deRhamCohomology.puncturedSpaceEquivSphere (EuclideanSpace ℝ (Fin (n + 1))) n
      (k + 1)).symm ≪≫ₗ
    deRhamCohomology.equivOfDiffeomorph (stereographicPuncturedDiffeomorph v) (k + 1) ≪≫ₗ e ≪≫ₗ
    (deRhamCohomology.equivOfDiffeomorph
      (Diffeomorph.ofTop _ (compl_singleton_sup_compl_singleton_neg_eq_top v))
      (k + 2)).symm⟩

/-- One suspension step: if `H^{k+1}(Sⁿ)` vanishes for the unit sphere of `ℝⁿ⁺¹`, then
`H^{k+2}(Sⁿ⁺¹)` vanishes for the unit sphere of an `(n + 2)`-dimensional space. -/
private theorem subsingleton_deRhamCohomology_sphere_succ_succ [Fact (finrank ℝ E = n + 1 + 1)]
    {k : ℕ} (h : Subsingleton
      (deRhamCohomology (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (k + 1))) :
    Subsingleton (deRhamCohomology (𝓡 (n + 1)) (sphere (0 : E) 1) (k + 2)) :=
  (nonempty_linearEquiv_deRhamCohomology_sphere_succ (E := E) k).some.toEquiv.symm.subsingleton

-- The induction on the degree passes through the spheres of the spaces `ℝⁿ⁺¹`, which all live in
-- one universe; `TauCeti.subsingleton_deRhamCohomology_sphere` transfers the result to any `E`.
/-- `H^k(Sⁿ) = 0` for `0 < k < n`, for the unit sphere `Sⁿ` of `ℝⁿ⁺¹`. -/
private theorem subsingleton_deRhamCohomology_sphere_euclideanSpace {n k : ℕ} (hk : 0 < k)
    (hkn : k < n) :
    Subsingleton (deRhamCohomology (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) k) := by
  induction k generalizing n with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases k with _ | k
    · exact subsingleton_deRhamCohomology_sphere_one hkn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact subsingleton_deRhamCohomology_sphere_succ_succ
        (E := EuclideanSpace ℝ (Fin (m + 1 + 1))) (ih k.succ_pos (by omega))

/-- **The de Rham cohomology of `Sⁿ` vanishes in degrees `0 < k < n`**, for the unit sphere `Sⁿ`
of any `(n + 1)`-dimensional real inner product space. -/
theorem subsingleton_deRhamCohomology_sphere [Fact (finrank ℝ E = n + 1)] {k : ℕ} (hk : 0 < k)
    (hkn : k < n) : Subsingleton (deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k) := by
  rcases k with _ | _ | k
  · exact absurd hk (lt_irrefl 0)
  · exact subsingleton_deRhamCohomology_sphere_one hkn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact subsingleton_deRhamCohomology_sphere_succ_succ (E := E)
      (subsingleton_deRhamCohomology_sphere_euclideanSpace k.succ_pos (by omega))

end Suspension

section TopDegree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **The de Rham cohomology of `S⁰` in degree zero.** The unit sphere `S⁰` of a one-dimensional
real inner product space consists of two points, so `H⁰(S⁰)` is two-dimensional. -/
theorem finrank_deRhamCohomology_zero_sphere_of_finrank_eq_one [Fact (finrank ℝ E = 1)] :
    finrank ℝ (deRhamCohomology (𝓡 0) (sphere (0 : E) 1) 0) = 2 := by
  obtain ⟨e⟩ := nonempty_sphere (E := E) (m := 0) Fact.out
  have hS := sphere_eq_pair_of_finrank_eq_one Fact.out e.2
  have := finite_sphere_of_finrank_eq_one (E := E) Fact.out 0 1
  have := discreteTopology_sphere_of_finrank_eq_one (E := E) Fact.out 0 1
  rw [finrank_deRhamCohomology_zero_of_discreteTopology, Nat.card_coe_set_eq, hS,
    Set.ncard_pair (fun h ↦ ne_neg_of_mem_unit_sphere ℝ e (Subtype.ext h) : (e : E) ≠ -e)]

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- `H¹(S¹)` is one-dimensional, for the unit circle `S¹` of a two-dimensional real inner product
space. -/
private theorem finrank_deRhamCohomology_sphere_one_one [Fact (finrank ℝ E = 1 + 1)] :
    finrank ℝ (deRhamCohomology (𝓡 1) (sphere (0 : E) 1) 1) = 1 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 1
  obtain ⟨v⟩ := nonempty_sphere (E := E) (m := 1) Fact.out
  set U : Opens (sphere (0 : E) 1) := ⟨{v}ᶜ, isOpen_compl_singleton⟩
  set V : Opens (sphere (0 : E) 1) := ⟨{-v}ᶜ, isOpen_compl_singleton⟩
  -- `U` and `V` are diffeomorphic to `ℝ`, hence connected.
  have hℝ : ConnectedSpace (EuclideanSpace ℝ (Fin 1)) := inferInstance
  have : PreconnectedSpace U :=
    ((stereographicDiffeomorph v).toHomeomorph.connectedSpace_iff.mpr hℝ).toPreconnectedSpace
  have : PreconnectedSpace V :=
    ((stereographicDiffeomorph (-v)).toHomeomorph.connectedSpace_iff.mpr hℝ).toPreconnectedSpace
  -- `U ⊓ V` is diffeomorphic to `ℝ \ {0}`, whose cohomology is that of `S⁰`.
  have h₂ : finrank ℝ (deRhamCohomology (𝓡 1) (U ⊓ V : Opens (sphere (0 : E) 1)) 0) = 2 := by
    simp only [U, V, Opens.mk_inf_mk, Set.inf_eq_inter]
    rw [← (deRhamCohomology.equivOfDiffeomorph (stereographicPuncturedDiffeomorph v) 0).finrank_eq,
      (deRhamCohomology.puncturedSpaceEquivSphere (EuclideanSpace ℝ (Fin 1)) 0 0).finrank_eq]
    exact finrank_deRhamCohomology_zero_sphere_of_finrank_eq_one
  have : Nonempty (U ⊓ V : Opens (sphere (0 : E) 1)) := by
    simp only [U, V, Opens.mk_inf_mk, Set.inf_eq_inter]
    exact ⟨(stereographicPuncturedDiffeomorph v).symm
      ⟨EuclideanSpace.single (0 : Fin 1) 1, by simp⟩⟩
  have : FiniteDimensional ℝ (deRhamCohomology (𝓡 1) (U ⊓ V : Opens (sphere (0 : E) 1)) 0) :=
    Module.finite_of_finrank_eq_succ h₂
  -- The connecting map `H⁰(U ⊓ V) → H¹(S¹)` is surjective, and its kernel is the line of
  -- constant classes.
  have h := LinearMap.finrank_range_add_finrank_ker (deRhamCohomology.mayerVietorisδ (𝓡 1) U V 0)
  rw [LinearMap.range_eq_top.mpr (deRhamCohomology.mayerVietorisδ_surjective
      (subsingleton_deRhamCohomology_sphere_compl_singleton v 0)
      (subsingleton_deRhamCohomology_sphere_compl_singleton (-v) 0)), finrank_top,
    deRhamCohomology.ker_mayerVietorisδ_zero,
    LinearMap.finrank_range_of_inj deRhamCohomology.const_injective, Module.finrank_self, h₂] at h
  rw [(deRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop _ (compl_singleton_sup_compl_singleton_neg_eq_top v)) 1).finrank_eq]
  -- `h` reads `dim H¹(U ⊔ V) + 1 = 2`.
  exact Nat.add_right_cancel h

/-- `Hⁿ⁺¹(Sⁿ⁺¹)` is one-dimensional, for the unit sphere `Sⁿ⁺¹` of `ℝⁿ⁺²`. -/
private theorem finrank_deRhamCohomology_sphere_euclideanSpace_self (m : ℕ) :
    finrank ℝ (deRhamCohomology (𝓡 (m + 1))
      (sphere (0 : EuclideanSpace ℝ (Fin (m + 1 + 1))) 1) (m + 1)) = 1 := by
  induction m with
  | zero => exact finrank_deRhamCohomology_sphere_one_one
  | succ m ih =>
    exact (nonempty_linearEquiv_deRhamCohomology_sphere_succ
      (E := EuclideanSpace ℝ (Fin (m + 1 + 1 + 1))) m).some.finrank_eq.symm.trans ih

/-- **The top de Rham cohomology of a sphere.** For `n ≥ 1`, `Hⁿ(Sⁿ)` is one-dimensional, for the
unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space. -/
theorem finrank_deRhamCohomology_sphere_self [Fact (finrank ℝ E = n + 1)] (hn : 0 < n) :
    finrank ℝ (deRhamCohomology (𝓡 n) (sphere (0 : E) 1) n) = 1 := by
  rcases n with _ | _ | m
  · exact absurd hn (lt_irrefl 0)
  · exact finrank_deRhamCohomology_sphere_one_one
  · exact (nonempty_linearEquiv_deRhamCohomology_sphere_succ (E := E) m).some.finrank_eq.symm.trans
      (finrank_deRhamCohomology_sphere_euclideanSpace_self m)

/-- **The de Rham cohomology of spheres.** For `n ≥ 1`, the de Rham cohomology `H^k(Sⁿ)` of the
unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space is one-dimensional in degrees
`0` and `n`, and zero in every other degree. -/
theorem finrank_deRhamCohomology_sphere [Fact (finrank ℝ E = n + 1)] (hn : 0 < n) (k : ℕ) :
    finrank ℝ (deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k) = if k = 0 ∨ k = n then 1 else 0 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  split_ifs with h
  · rcases h with rfl | rfl
    · -- The sphere of a space of dimension at least two is connected.
      have : ConnectedSpace (sphere (0 : E) 1) :=
        isConnected_iff_connectedSpace.mp <| isConnected_sphere
          (by rw [← finrank_eq_rank, (Fact.out : finrank ℝ E = n + 1)]; exact_mod_cast by omega)
          0 zero_le_one
      exact finrank_deRhamCohomology_zero _ _
    · exact finrank_deRhamCohomology_sphere_self hn
  · rw [not_or] at h
    have : Subsingleton (deRhamCohomology (𝓡 n) (sphere (0 : E) 1) k) := by
      rcases lt_or_gt_of_ne h.2 with hk | hk
      · exact subsingleton_deRhamCohomology_sphere (Nat.pos_of_ne_zero h.1) hk
      · exact subsingleton_deRhamCohomology_of_finrank_lt (𝓡 n) (sphere (0 : E) 1)
          (by rwa [finrank_euclideanSpace_fin])
    exact finrank_zero_of_subsingleton

end TopDegree

end TauCeti
