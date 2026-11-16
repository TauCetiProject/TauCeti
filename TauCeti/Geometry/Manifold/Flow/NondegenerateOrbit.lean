/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.ReturnDerivative
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint

/-!
# Nondegenerate closed orbits are isolated

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold `M`, and let `p` be a
point returning to itself at time `T₀`. Choose a function `g` with `dg_p (v p) ≠ 0`, so that the
level `{g = g p}` is a local section transverse to `v`, and let `P = flowTransition v g T₀ p` be
the return branch of this section. The closed orbit through `p` is *nondegenerate* (at return time
`T₀`) when `1` is not an eigenvalue of the linearized return map
`TauCeti.returnDerivative v g T₀ p`. By `TauCeti.hasEigenvalue_returnDerivative_iff` this does
not depend on the section or on the base point, and by
`TauCeti.hasEigenvalue_normalReturnDerivative_iff` it is the same as asking that `1` is not an
eigenvalue of the normal return derivative.

The closed-orbit equation `Φ_t(z) = z` is underdetermined in the unknowns `(t, z)`: every point of
a closed orbit solves it, with the same period. Restricting `z` to the section removes this time
translation, and turns the equation into the fixed-point equation `P y = y` of the return branch,
whose unknown and target both have the dimension of the section. Nondegeneracy says exactly that
`p` is a nondegenerate fixed point of `P` in the sense of `TauCeti.IsNondegenerateFixedPt`
(`TauCeti.isNondegenerateFixedPt_flowTransition_iff`). The linearized return map vanishes on
`v p` and maps into `ker dg_p`, so `DP_p - 1` is injective on all of `T_pM` as soon as its
restriction to `ker dg_p` is.

Nondegenerate fixed points are isolated, so `p` is the only fixed point of `P` near `p`
(`TauCeti.eventually_eq_of_isFixedPt_flowTransition`). Flowing a nearby closed orbit for a short
time into the section, this becomes the statement that nondegenerate closed orbits are isolated
together with their periods (`TauCeti.eventually_fst_eq_and_exists_flowOf_eq_snd`): if `z` is
close to `p`, `t` is close to `T₀` and `Φ_t(z) = z`, then `t = T₀` and `z` lies on the trajectory
of `p`. The same holds near `k T₀` when the `k`-th power of the linearized return map has no
eigenvalue `1` (`TauCeti.eventually_fst_eq_natCast_mul_and_exists_flowOf_eq_snd`), the
nondegeneracy of the `k`-fold cover of the orbit.

A compact set `S` of pairs `(t, z)` in the flow domain all of whose closed-orbit solutions are
nondegenerate, typically `S = [a, b] × K` for a compact window `K` of a complete field or of a
compact manifold, contains only finitely many
closed orbits: there are finitely many representatives `(t, y)` such that every solution in `S`
has one of these periods and lies on the corresponding trajectory
(`TauCeti.exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd`), and in particular finitely many
periods occur (`TauCeti.finite_image_fst_setOf_flowOf_eq`). Equilibria solve `Φ_t(z) = z` for
every `t` and have no transverse section, so the hypothesis excludes zeros of `v` from `S`.

Isolation and finiteness of nondegenerate closed orbits are the fixed-field statements of the
Kupka–Smale theorem, whose perturbation arguments treat the closed orbits of bounded period in a
compact window one at a time.

## Main results

* `TauCeti.isNondegenerateFixedPt_flowTransition_iff`: the return branch has a nondegenerate fixed
  point at `p` exactly when the linearized return map has no eigenvalue `1`.
* `TauCeti.eventually_eq_of_isFixedPt_flowTransition`: then `p` is the only fixed point of the
  return branch near `p`.
* `TauCeti.eventually_fst_eq_and_exists_flowOf_eq_snd`: a nondegenerate closed orbit is isolated,
  and its period is locally unique.
* `TauCeti.eventually_fst_eq_natCast_mul_and_exists_flowOf_eq_snd`: the same for an iterate.
* `TauCeti.exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd`,
  `TauCeti.finite_image_fst_setOf_flowOf_eq`: a compact set of nondegenerate closed-orbit solutions
  in the flow domain meets finitely many closed orbits, with finitely many periods.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3
  (hyperbolic closed orbits and the Kupka–Smale theorem).
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2.
-/

public section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g : M → ℝ} {T₀ : ℝ} {p : M}

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
include hv

section Local

variable (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0)
include hP hp hg hgv

/-- **Nondegenerate return branches.** If `p` returns to itself at time `T₀`, the return branch
of a transverse section through `p` has a nondegenerate fixed point at `p` exactly when `1` is not
an eigenvalue of the linearized return map. -/
theorem isNondegenerateFixedPt_flowTransition_iff :
    IsNondegenerateFixedPt I (flowTransition v g T₀ p) p ↔
      ¬(returnDerivative v g T₀ p).HasEigenvalue 1 := by
  have hfix : IsFixedPt (flowTransition v g T₀ p) p := by
    rw [IsFixedPt, flowTransition_self, hp]
  have hdiff : MDifferentiableAt I I (flowTransition v g T₀ p) p :=
    mdifferentiableAt_flowTransition hv hP (by rwa [hp]) (by rwa [hp])
  rw [isNondegenerateFixedPt_iff]
  constructor
  · rintro ⟨-, -, h⟩ h1
    obtain ⟨w, hw⟩ := h1.exists_hasEigenvector
    have hw1 := hw.apply_eq_smul
    rw [one_smul, returnDerivative_apply] at hw1
    exact hw.2 (h w hw1)
  · refine fun h1 ↦ ⟨hfix, hdiff, fun w hw ↦ by_contra fun hw0 ↦ h1 ?_⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩
    rw [one_smul, returnDerivative_apply]
    exact hw

/-- **The fixed point of a nondegenerate return branch is isolated.** If `1` is not an eigenvalue
of the linearized return map, then `p` is the only fixed point of the return branch near `p`. -/
theorem eventually_eq_of_isFixedPt_flowTransition
    (hnd : ¬(returnDerivative v g T₀ p).HasEigenvalue 1) :
    ∀ᶠ y in 𝓝 p, IsFixedPt (flowTransition v g T₀ p) y → y = p := by
  have h := ((isNondegenerateFixedPt_flowTransition_iff hv hP hp hg hgv).2
    hnd).eventually_not_isFixedPt
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with y hy hfix
  by_contra hne
  exact hy (mem_compl_singleton_iff.2 hne) hfix

/-- **Nondegenerate closed orbits are isolated.** Let `p` return to itself at time `T₀`, and
suppose that for a transverse section through `p` the linearized return map has no eigenvalue `1`.
If `(t, z)` is close to `(T₀, p)` and `z` returns to itself at time `t`, then `t = T₀` and `z`
lies on the trajectory of `p`. -/
theorem eventually_fst_eq_and_exists_flowOf_eq_snd
    (hnd : ¬(returnDerivative v g T₀ p).HasEigenvalue 1) :
    ∀ᶠ x in 𝓝 (T₀, p), x ∈ flowDomain v → flowOf v x.1 x.2 = x.2 →
      x.1 = T₀ ∧ ∃ s, (s, p) ∈ flowDomain v ∧ flowOf v s p = x.2 := by
  have h0 : ((0 : ℝ), p) ∈ flowDomain v := mem_flowDomain_zero hv p
  have hp0 : flowOf v 0 p = p := flowOf_zero v p
  have hg0 : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v 0 p) := by rwa [hp0]
  have hgv0 : mvfderiv I g (flowOf v 0 p) (v (flowOf v 0 p)) ≠ 0 := by rwa [hp0]
  have hgP : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T₀ p) := by rwa [hp]
  have hgvP : mvfderiv I g (flowOf v T₀ p) (v (flowOf v T₀ p)) ≠ 0 := by rwa [hp]
  -- The time-`0` transition `π` flows each point near `p` for a short time into the section
  -- `{g = g p}`; it fixes `p`.
  set π := flowTransition v g 0 p
  have hπ : Tendsto π (𝓝 p) (𝓝 p) := by
    have h := (continuousAt_flowTransition hv h0 hg0 hgv0).tendsto
    rwa [flowTransition_self, hp0] at h
  have hsnd : Tendsto Prod.snd (𝓝 (T₀, p)) (𝓝 p) := continuousAt_snd.tendsto
  have hlift : Tendsto (fun x : ℝ × M ↦ (x.1, π x.2)) (𝓝 (T₀, p)) (𝓝 (T₀, p)) :=
    continuousAt_fst.tendsto.prodMk_nhds (hπ.comp hsnd)
  filter_upwards [hsnd.eventually (eventually_flowHittingTime hv h0 hg0 hgv0),
    hlift.eventually (eventually_eq_flowHittingTime_iff hv hP hgP hgvP),
    (hπ.comp hsnd).eventually (eventually_eq_of_isFixedPt_flowTransition hv hP hp hg hgv hnd)]
    with ⟨t, z⟩ ⟨hτ, hτg⟩ hiff hfix hx hper
  dsimp only [comp_apply] at hτ hτg hiff hfix hx hper ⊢
  -- The point `π z` of the section returns to itself at time `t`, so `t` is its hitting time of
  -- the section and `π z` is a fixed point of the return branch, hence `π z = p`.
  have hπz : π z = flowOf v (flowHittingTime v g 0 p z) z := flowTransition_apply v g 0 p z
  obtain ⟨-, hπper⟩ := flowOf_flowOf_of_flowOf_eq hv hτ hx hper
  rw [← hπz] at hπper
  have hlevel : g (flowOf v t (π z)) = g (flowOf v T₀ p) := by
    rw [hπper, hπz, hτg, hp0, hp]
  have ht := hiff.1 hlevel
  have hπp : π z = p := hfix (by rw [IsFixedPt, flowTransition_apply, ← ht, hπper])
  refine ⟨by rw [ht, hπp, flowHittingTime_self], -flowHittingTime v g 0 p z, ?_, ?_⟩
  · have h := neg_mem_flowDomain_flowOf hv hτ
    rwa [← hπz, hπp] at h
  · have h := flowOf_neg_flowOf hv hτ
    rwa [← hπz, hπp] at h

/-- **Nondegenerate iterates of closed orbits are isolated.** Let `p` return to itself at time
`T₀`, and suppose that for a transverse section through `p` the `k`-th power of the linearized
return map has no eigenvalue `1`, for some `k ≠ 0`. If `(t, z)` is close to `(k T₀, p)` and `z`
returns to itself at time `t`, then `t = k T₀` and `z` lies on the trajectory of `p`. -/
theorem eventually_fst_eq_natCast_mul_and_exists_flowOf_eq_snd {k : ℕ} (hk : k ≠ 0)
    (hnd : ¬(returnDerivative v g T₀ p ^ k).HasEigenvalue 1) :
    ∀ᶠ x in 𝓝 ((k : ℝ) * T₀, p), x ∈ flowDomain v → flowOf v x.1 x.2 = x.2 →
      x.1 = k * T₀ ∧ ∃ s, (s, p) ∈ flowDomain v ∧ flowOf v s p = x.2 := by
  obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
  rw [← returnDerivative_natCast_mul hv hP hp hg hgv hk] at hnd
  exact eventually_fst_eq_and_exists_flowOf_eq_snd hv hkP hkp hg hgv hnd

end Local

section Compact

variable {S : Set (ℝ × M)} (hS : IsCompact S) (hSD : S ⊆ flowDomain v)
  (hnd : ∀ x ∈ S, flowOf v x.1 x.2 = x.2 → ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
    mvfderiv I g x.2 (v x.2) ≠ 0 ∧ ¬(returnDerivative v g x.1 x.2).HasEigenvalue 1)
include hS hSD hnd

/-- **Finitely many nondegenerate closed orbits in a compact window.** Let `S` be a compact
subset of the flow domain, a set of pairs `(t, z)` such that whenever `z` returns to itself at
time `t`, the closed orbit through `z` is nondegenerate at return time `t` for some transverse
section. Then there are finitely many such pairs `(t, y)` in `S` such that every pair `(t', z)`
in `S` with `z` returning to itself at time `t'` has `t' = t` and `z` on the trajectory of `y` for
one of them. -/
theorem exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd :
    ∃ F : Finset (ℝ × M), (∀ y ∈ F, y ∈ S ∧ flowOf v y.1 y.2 = y.2) ∧
      ∀ x ∈ S, flowOf v x.1 x.2 = x.2 → ∃ y ∈ F, x.1 = y.1 ∧
        ∃ s, (s, y.2) ∈ flowDomain v ∧ flowOf v s y.2 = x.2 := by
  have hcont : ContinuousOn (fun x : ℝ × M ↦ (flowOf v x.1 x.2, x.2)) S :=
    ((contMDiffOn_flowOf le_rfl hv).continuousOn.mono hSD).prodMk continuous_snd.continuousOn
  set C := {x ∈ S | flowOf v x.1 x.2 = x.2}
  have hC : IsCompact C :=
    hS.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed hS.isClosed isClosed_diagonal)
      fun _ hx ↦ hx.1
  -- Around each solution, the other solutions share its period and lie on its trajectory.
  obtain ⟨F, hF⟩ := hC.elim_nhds_subcover' (fun y _ ↦ {x : ℝ × M | x ∈ flowDomain v →
      flowOf v x.1 x.2 = x.2 → x.1 = y.1 ∧ ∃ s, (s, y.2) ∈ flowDomain v ∧ flowOf v s y.2 = x.2})
    fun y hy ↦ by
      obtain ⟨g, hg, hgv, hndy⟩ := hnd y hy.1 hy.2
      exact eventually_fst_eq_and_exists_flowOf_eq_snd hv (hSD hy.1) hy.2 hg hgv hndy
  refine ⟨F.map (Embedding.subtype _), fun y hy ↦ ?_, fun x hxS hx ↦ ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hy
    exact y.2
  · obtain ⟨y, hyF, hxy⟩ := mem_iUnion₂.1 (hF ⟨hxS, hx⟩)
    exact ⟨y, Finset.mem_map_of_mem _ hyF, hxy (hSD hxS) hx⟩

/-- **Finitely many periods of nondegenerate closed orbits in a compact window.** Under the
hypotheses of `TauCeti.exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd`, only finitely many
return times `t` occur among the pairs `(t, z)` in `S` with `z` returning to itself at time `t`. -/
theorem finite_image_fst_setOf_flowOf_eq :
    (Prod.fst '' {x ∈ S | flowOf v x.1 x.2 = x.2}).Finite := by
  obtain ⟨F, -, hF⟩ := exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd hv hS hSD hnd
  refine (F.finite_toSet.image Prod.fst).subset ?_
  rintro _ ⟨x, ⟨hxS, hx⟩, rfl⟩
  obtain ⟨y, hyF, hfst, -⟩ := hF x hxS hx
  exact ⟨y, hyF, hfst.symm⟩

end Compact

end TauCeti
