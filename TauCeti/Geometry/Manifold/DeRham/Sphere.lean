/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.DeRham.Punctured
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

## Main results

* `TauCeti.subsingleton_deRhamCohomology_sphere_compl_singleton`: the sphere minus a point has no
  de Rham cohomology in positive degree.
* `TauCeti.nonempty_linearEquiv_deRhamCohomology_sphere_succ`: `H^{k+1}(Sⁿ) ≃ H^{k+2}(Sⁿ⁺¹)`.
* `TauCeti.subsingleton_deRhamCohomology_sphere_one`: `H¹(Sⁿ) = 0` for `n ≥ 2`.
* `TauCeti.subsingleton_deRhamCohomology_sphere`: `H^k(Sⁿ) = 0` for `0 < k < n`.

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

end TauCeti
