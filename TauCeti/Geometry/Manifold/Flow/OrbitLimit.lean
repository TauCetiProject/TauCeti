/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.WhitneyEmbedding
public import TauCeti.Analysis.Calculus.Deriv.DominatedLimit
public import TauCeti.Analysis.Calculus.Equicontinuity
public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Manifold.LocallyEquiconnected
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorField.Regularity
public import TauCeti.Topology.Compactness.Compact
public import TauCeti.Topology.ContinuousMap.CompactConvergence
public import TauCeti.Topology.Homotopy.Homotopic.With
public import TauCeti.Topology.Homotopy.LocallyEquiconnected.MappingSpace
import TauCeti.Topology.Separation.InvFunOn

/-!
# Limits of periodic orbits of converging vector fields

Let `X a` be a family of time-dependent vector fields on a manifold `M`, indexed by the points `a`
of a topological space `P`, depending continuously on `(a, t, x)` as a map to the tangent bundle.
Let `a n → a₀`, and for each `n` let `γ n` be a `1`-periodic solution of `X (a n)`. If the orbits
stay in a compact set `K`, then a subsequence of them converges to a `1`-periodic solution `γ₀` of
the limit field `X a₀` (`TauCeti.exists_strictMono_mem_periodicSolutions_tendstoUniformly`). If
the orbits `γ n` are contractible, so is `γ₀`, provided `M` is locally equiconnected
(`TauCeti.exists_strictMono_mem_contractiblePeriodicSolutions_tendstoUniformly`), as every compact
Hausdorff boundaryless smooth manifold of finite dimension is
(`Manifold.locallyEquiconnectedSpace`).

Convergence is measured through a `C¹` map `e : M → F` into a finite-dimensional normed space,
injective on `K` and with injective differential at the points of `K`: the loops `e ∘ γ n`
converge uniformly to `e ∘ γ₀`, and the loops `γ n` converge pointwise in `M`. On a compact
boundaryless manifold such a map exists by Whitney's embedding theorem, and the contractible
`1`-periodic solutions of `X (a n)` have a subsequence converging pointwise to a contractible
`1`-periodic solution of `X a₀`
(`TauCeti.exists_strictMono_mem_contractiblePeriodicSolutions_tendsto`).

This is the compactness step in the spectrality of Floer-theoretic spectral invariants for
degenerate Hamiltonians: approximating a Hamiltonian `H` by nondegenerate Hamiltonians `Hₙ`, the
values of a spectral invariant at `Hₙ` are actions of contractible `1`-periodic orbits of `Hₙ`,
and by the Arzelà–Ascoli theorem a subsequence of these orbits converges to a contractible
`1`-periodic orbit of `H`. The family `X` is then the family of Hamiltonian vector fields, indexed
by a space of Hamiltonians.

## Implementation notes

The pushforward `G (a, t, p) = d e_p (X a t p)` is continuous, hence bounded on the compact sets
`{a n} ∪ {a₀} × [-T, T] × K`. So the loops `e ∘ γ n` have uniformly bounded velocities, and the
Arzelà–Ascoli theorem for periodic loops
(`TauCeti.exists_strictMono_tendstoUniformly_of_periodic_of_norm_deriv_le`) gives a subsequence
converging uniformly to a periodic loop `y` in the closed set `e(K)`. The integral equations
`e (γ n t) - e (γ n 0) = ∫₀ᵗ G (a n, τ, γ n τ) dτ` pass to the limit by dominated convergence,
since the integrands converge pointwise (`TauCeti.hasDerivAt_of_tendsto_of_norm_le`). So `y` solves
the pushforward of `X a₀` along `e`, and since `d e` is injective, `y = e ∘ γ₀` for a periodic
solution `γ₀` of `X a₀` in `K` (`TauCeti.exists_mem_periodicSolutions_comp_eq`).

For contractibility, the loops converge in the mapping space `C(ℝ ⧸ ℤ, M)`, measured through the
closed embedding `e` of `K` (`IsCompact.tendsto_of_tendstoLocallyUniformly_comp`). If `M` is locally
equiconnected, so is this mapping space (`TauCeti.instLocallyEquiconnectedSpaceContinuousMap`), so
the path component of the limit loop is
open, and the limit loop is joined to, hence homotopic to (`ContinuousMap.homotopic_iff_joined`),
the contractible loops `γ n` for large `n`.

## Main results

* `TauCeti.exists_strictMono_mem_periodicSolutions_tendstoUniformly`: periodic orbits in a compact
  set have a subsequence converging to a periodic orbit of the limit field.
* `TauCeti.exists_strictMono_mem_contractiblePeriodicSolutions_tendstoUniformly`: the same for
  contractible periodic orbits, on a locally equiconnected manifold.
* `TauCeti.exists_strictMono_mem_contractiblePeriodicSolutions_tendsto`: on a compact
  boundaryless manifold, contractible periodic orbits have a subsequence converging pointwise to
  a contractible periodic orbit of the limit field.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1.1, proof of Proposition 5.8.
* M. Schwarz, *On the action spectrum for closed symplectically aspherical manifolds*, Pacific J.
  Math. 193 (2000), 419–461.
-/

public section

open Set Filter Topology Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {P : Type*} [TopologicalSpace P] {X : P → ℝ → (x : M) → TangentSpace I x}
  {a : ℕ → P} {a₀ : P} {γ : ℕ → ℝ → M}

section Embedded

variable [IsManifold I 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

/-- **Periodic orbits of converging vector fields accumulate at a periodic orbit.** Let `X a` be a
family of time-dependent vector fields on `M`, continuous in `(a, t, x)` as a map to the tangent
bundle, let `a n → a₀`, and let `γ n` be `1`-periodic solutions of `X (a n)` with values in a
compact set `K`. Let `e : M → F` be a `C¹` map into a finite-dimensional normed space, injective
on `K` and with injective differential at the points of `K`. Then a subsequence `γ (ψ n)`
converges to a `1`-periodic solution `γ₀` of `X a₀` in `K`: uniformly after applying `e`, and
pointwise in `M`. -/
theorem exists_strictMono_mem_periodicSolutions_tendstoUniformly
    (hX : Continuous fun q : P × ℝ × M ↦ (⟨q.2.2, X q.1 q.2.1 q.2.2⟩ : TangentBundle I M))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (ha : Tendsto a atTop (𝓝 a₀))
    (hγ : ∀ n, γ n ∈ periodicSolutions (X (a n)) 1) (hγK : ∀ n t, γ n t ∈ K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ γ₀ ∈ periodicSolutions (X a₀) 1, (∀ t, γ₀ t ∈ K) ∧
      TendstoUniformly (fun n t ↦ e (γ (ψ n) t)) (e ∘ γ₀) atTop ∧
      ∀ t, Tendsto (fun n ↦ γ (ψ n) t) atTop (𝓝 (γ₀ t)) := by
  -- The pushforward `G (b, t, p) = d e_p (X b t p)` of the family is continuous, and bounded on
  -- the compact windows `({a n} ∪ {a₀}) × [-T, T] × K`.
  let G : P × ℝ × M → F := fun q ↦ mvfderiv I e q.2.2 (X q.1 q.2.1 q.2.2)
  have hG : Continuous G := (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp hX
  have hbound (T : ℝ) : ∃ B, ∀ n, ∀ t ∈ Icc (-T) T, ∀ p ∈ K, ‖G (a n, t, p)‖ ≤ B :=
    ((ha.isCompact_insert_range.prod (isCompact_Icc.prod hK)).exists_bound_of_continuousOn
      hG.continuousOn).imp fun _ hB n t ht p hp ↦
        hB _ ⟨mem_insert_of_mem _ (mem_range_self n), ht, hp⟩
  have hγc (n : ℕ) : Continuous (γ n) := continuous_of_mem_periodicSolutions (hγ n)
  -- Along each orbit, `e ∘ γ n` has velocity `G (a n, t, γ n t)`.
  have hy (n : ℕ) (t : ℝ) : HasDerivAt (e ∘ γ n) (G (a n, t, γ n t)) t := by
    have h := ((mem_periodicSolutions.1 (hγ n)).1 t).hasDerivAt_comp_graph (f := fun _ ↦ e)
      ((he.comp contMDiff_snd).mdifferentiableAt one_ne_zero)
    rw [deriv_const] at h
    exact h.congr_deriv (zero_add _)
  -- By Arzelà–Ascoli, a subsequence of the `e ∘ γ n` converges uniformly to a loop `y` in `e(K)`.
  obtain ⟨B₁, hB₁⟩ := hbound 1
  obtain ⟨ψ, hψ, y, hyper, hyc, hconv⟩ :=
    exists_strictMono_tendstoUniformly_of_periodic_of_norm_deriv_le (hK.image he.continuous)
      (fun n t ↦ by simp [(mem_periodicSolutions.1 (hγ n)).2 t])
      (fun n t ↦ mem_image_of_mem e (hγK n t)) hy
      fun n t ht ↦ hB₁ n t ⟨by linarith [ht.1], ht.2⟩ _ (hγK n t)
  have hyK (t : ℝ) : y t ∈ e '' K := (hK.image he.continuous).isClosed.mem_of_tendsto
    (hconv.tendsto_at t) (Eventually.of_forall fun n ↦ mem_image_of_mem e (hγK _ t))
  -- Read through `e`, the loops converge pointwise to the continuous loop `invFunOn e K ∘ y`.
  have : Nonempty M := ⟨γ 0 0⟩
  have hlim (t : ℝ) : Tendsto (fun n ↦ γ (ψ n) t) atTop (𝓝 (invFunOn e K (y t))) :=
    hK.tendsto_nhds_of_tendsto_comp he.continuous.continuousOn he_inj
      (Eventually.of_forall fun n ↦ hγK _ t) (invFunOn_mem (hyK t))
      (by rw [comp_def, invFunOn_eq (hyK t)]; exact hconv.tendsto_at t)
  have hinv : Continuous (invFunOn e K ∘ y) :=
    (he.continuous.continuousOn.continuousOn_invFunOn_image_of_isCompact hK subset_rfl
      he_inj (by simp)).comp_continuous hyc hyK
  -- The velocities converge pointwise and boundedly, so `y` solves the pushforward `Y` of `X a₀`.
  let Y : ℝ → F → F := fun t v ↦ G (a₀, t, invFunOn e K v)
  have hyd (t : ℝ) : HasDerivAt y (Y t (y t)) t :=
    hasDerivAt_of_tendsto_of_norm_le (fun n ↦ hy (ψ n))
      (fun n ↦ hG.comp (continuous_const.prodMk (continuous_id.prodMk (hγc _))))
      hconv.tendsto_at
      (fun τ ↦ hG.continuousAt.tendsto.comp ((ha.comp hψ.tendsto_atTop).prodMk_nhds
        (tendsto_const_nhds.prodMk_nhds (hlim τ))))
      (fun T ↦ (hbound T).imp fun _ hB ↦ Eventually.of_forall fun n τ hτ ↦ hB _ τ hτ _ (hγK _ τ))
      (hG.comp (continuous_const.prodMk (continuous_id.prodMk hinv))) t
  -- Since `d e` is injective, `y` is read through `e` from a periodic solution of `X a₀` in `K`.
  obtain ⟨x, hx, hxK, rfl⟩ := exists_mem_periodicSolutions_comp_eq (X := X a₀) hK he_inj
    hde (fun t p hp ↦ congrArg (fun q ↦ G (a₀, t, q)) (he_inj.leftInvOn_invFunOn hp)) hyper hyd hyK
  refine ⟨ψ, hψ, x, hx, hxK, hconv, fun t ↦ ?_⟩
  simpa only [comp_apply, he_inj.leftInvOn_invFunOn (hxK t)] using hlim t

/-- **Contractible periodic orbits of converging vector fields accumulate at a contractible
periodic orbit.** Under the hypotheses of
`TauCeti.exists_strictMono_mem_periodicSolutions_tendstoUniformly`, on a locally equiconnected
manifold, if the orbits `γ n` are contractible, then a subsequence converges to a contractible
`1`-periodic solution `γ₀` of `X a₀` in `K`: uniformly after applying `e`, and pointwise in
`M`. -/
theorem exists_strictMono_mem_contractiblePeriodicSolutions_tendstoUniformly
    [LocallyEquiconnectedSpace M]
    (hX : Continuous fun q : P × ℝ × M ↦ (⟨q.2.2, X q.1 q.2.1 q.2.2⟩ : TangentBundle I M))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (ha : Tendsto a atTop (𝓝 a₀))
    (hγ : ∀ n, γ n ∈ contractiblePeriodicSolutions (X (a n)) 1) (hγK : ∀ n t, γ n t ∈ K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ γ₀ ∈ contractiblePeriodicSolutions (X a₀) 1,
      (∀ t, γ₀ t ∈ K) ∧ TendstoUniformly (fun n t ↦ e (γ (ψ n) t)) (e ∘ γ₀) atTop ∧
      ∀ t, Tendsto (fun n ↦ γ (ψ n) t) atTop (𝓝 (γ₀ t)) := by
  obtain ⟨ψ, hψ, γ₀, hγ₀, hγ₀K, hunif, hlim⟩ :=
    exists_strictMono_mem_periodicSolutions_tendstoUniformly hX he hK he_inj hde ha
      (fun n ↦ (mem_contractiblePeriodicSolutions.1 (hγ n)).1) hγK
  refine ⟨ψ, hψ, γ₀, mem_contractiblePeriodicSolutions.2 ⟨hγ₀, ?_⟩, hγ₀K, hunif, hlim⟩
  choose g hg hgγ using fun n ↦ (mem_contractiblePeriodicSolutions.1 (hγ n)).2
  -- The limit loop, as a map from the circle `ℝ ⧸ ℤ`.
  have hper : Periodic γ₀ 1 := (mem_periodicSolutions.1 hγ₀).2
  let g₀ : C(AddCircle (1 : ℝ), M) := ⟨hper.lift,
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 <| by
      simpa [comp_def] using continuous_of_mem_periodicSolutions hγ₀⟩
  have hg₀ (t : ℝ) : g₀ t = γ₀ t := hper.lift_coe t
  refine ⟨g₀, ?_, hg₀⟩
  -- On the circle, the loops lie in `K` and converge uniformly after applying `e`, so they converge
  -- in the mapping space.
  have hconv : Tendsto (fun n ↦ g (ψ n)) atTop (𝓝 g₀) :=
    hK.tendsto_of_tendstoLocallyUniformly_comp he.continuous.continuousOn he_inj
      (fun n ↦ QuotientAddGroup.mk_surjective.forall.2 fun t ↦ by rw [hgγ]; exact hγK _ t)
      (QuotientAddGroup.mk_surjective.forall.2 fun t ↦ by rw [hg₀]; exact hγ₀K t)
      <| TendstoUniformly.tendstoLocallyUniformly fun u hu ↦ (hunif u hu).mono fun n hn ↦
        QuotientAddGroup.mk_surjective.forall.2 fun t ↦ by simpa [hg₀, hgγ] using hn t
  -- The mapping space is locally path-connected, so the path component of the limit is open and
  -- contains the contractible loops `g (ψ n)` for large `n`.
  obtain ⟨n, hn⟩ := (hconv.eventually
    ((IsOpen.pathComponent g₀).mem_nhds (mem_pathComponent_self g₀))).exists
  obtain ⟨c, hc⟩ := hg (ψ n)
  exact ⟨c, (ContinuousMap.homotopic_iff_joined.2 hn).trans hc⟩

end Embedded

/-- **Contractible periodic orbits of converging vector fields on a closed manifold.** Let `M` be
a compact boundaryless smooth manifold modelled on a finite-dimensional space, and `X a` a family
of time-dependent vector fields on `M`, continuous in `(a, t, x)` as a map to the tangent bundle.
If `a n → a₀` and `γ n` are contractible `1`-periodic solutions of `X (a n)`, then a subsequence
`γ (ψ n)` converges pointwise to a contractible `1`-periodic solution `γ₀` of `X a₀`. -/
theorem exists_strictMono_mem_contractiblePeriodicSolutions_tendsto [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [T2Space M]
    (hX : Continuous fun q : P × ℝ × M ↦ (⟨q.2.2, X q.1 q.2.1 q.2.2⟩ : TangentBundle I M))
    (ha : Tendsto a atTop (𝓝 a₀)) (hγ : ∀ n, γ n ∈ contractiblePeriodicSolutions (X (a n)) 1) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ γ₀ ∈ contractiblePeriodicSolutions (X a₀) 1,
      ∀ t, Tendsto (fun n ↦ γ (ψ n) t) atTop (𝓝 (γ₀ t)) := by
  have := Manifold.locallyEquiconnectedSpace I M
  obtain ⟨N, e, he, hemb, hde⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨ψ, hψ, γ₀, hγ₀, -, -, hlim⟩ :=
    exists_strictMono_mem_contractiblePeriodicSolutions_tendstoUniformly hX
      (he.of_le (by simp)) isCompact_univ hemb.injective.injOn
      (fun p _ ↦ injective_mvfderiv_iff.2 (hde p)) ha hγ fun _ _ ↦ mem_univ _
  exact ⟨ψ, hψ, γ₀, hγ₀, hlim⟩

end TauCeti
