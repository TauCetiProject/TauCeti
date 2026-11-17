/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.LiouvilleArnold.Torus

/-!
# Smooth period functions near a regular Liouville component

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2n`, and let
`F : M → (ι → ℝ)`, `|ι| = n`, be a smooth family of pairwise Poisson-commuting functions with
complete Hamiltonian vector fields. Their flows generate an action `v • y` of `ι → ℝ` on `M`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`), and the stabilizer `Λ_y` of a point
`y` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer`) is the group of its
**periods**: the `v` with `v • y = y`.

Fix a regular point `x` of `F` and a smooth local section `s` of `F` through `x`, defined on an
open set `t` of values: `F (s c) = c` for `c ∈ t` and `s (F x) = x`. This file shows that the
periods of the points `s c` depend smoothly on `c`, by the inverse function theorem applied to the
sweep `(v, c) ↦ v • s c`
(`TauCeti.SmoothTwoForm.IsSymplectic.isLocalDiffeomorphAt_hamiltonianFlowAction_section`).

* The stabilizers of the points `s c` are uniformly discrete near `x`: for `c` near `F x`, no
  period of `s c` other than `0` lies near `0`.
* Every period `v₀` of `x` continues to a smooth function `c ↦ λ(c)`, defined near `F x`, with
  `λ(F x) = v₀` and `λ(c)` a period of `s c`. Two such continuations which are continuous at
  `F x` and agree there coincide near `F x`.
* If the periods of `x` form a lattice with a basis `(bᵢ)`, the continuations `λ⁽ⁱ⁾` of the `bᵢ`
  form a basis of the period lattice of `s c` for every `c` near `F x`.
* In particular this applies when the connected component of `x` in its level is compact and
  consists of regular points, so that the periods of `x` form a lattice of rank `n`.

These smooth period functions are the input to the action-angle coordinates near a compact
Liouville torus, where the action variables are primitives of the one-forms
`(1 / 2π) ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `eventually_eq_zero_of_mem_hamiltonianFlowStabilizer_section`: the stabilizers of the points
  of a section are uniformly discrete.
* `exists_contDiffAt_mem_hamiltonianFlowStabilizer_section`: a period of `x` continues to a
  smooth family of periods of the points of a section.
* `eventuallyEq_of_mem_hamiltonianFlowStabilizer_section`: continuations of a period are locally
  unique.
* `exists_hamiltonianFlowStabilizer_section_eq_closure`: a basis of the period lattice of `x`
  continues to bases of the period lattices of the points of a section.
* `exists_hamiltonianFlowStabilizer_section_eq_closure_of_isCompact`: smooth period lattices near
  a compact regular component.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (the period lattice depends smoothly on the base point).
-/

public section

open Set Filter Module Topology Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M} {t : Set (ι → ℝ)} {s : (ι → ℝ) → M}

include hσ hF hcomm hc hdim

/-- **The stabilizers along a section are uniformly discrete.** Let `s` be a smooth local section
of `F` through a regular point `x`, defined on an open set `t`. For `(c, v)` near `(F x, 0)`, a
period `v` of `s c` is zero. -/
theorem eventually_eq_zero_of_mem_hamiltonianFlowStabilizer_section
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (ht : IsOpen t) (hxt : F x ∈ t) (hsx : s (F x) = x)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c) :
    ∀ᶠ q : (ι → ℝ) × (ι → ℝ) in 𝓝 (F x, 0),
      q.2 ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s q.1) → q.2 = 0 := by
  have hL := hσ.isLocalDiffeomorphAt_hamiltonianFlowAction_section hF hcomm hc hdim hx ht hxt hsx
    hs hFs
  set g := hL.localInverse
  -- The sweep `(v, c) ↦ v • s c` is injective near `(0, F x)`, where its local inverse `g` is a
  -- left inverse; `(v, c)` and `(0, c)` lie there for `(c, v)` near `(F x, 0)`.
  have hT : g.target ∈ 𝓝 ((0 : ι → ℝ), F x) :=
    g.open_target.mem_nhds hL.localInverse_mem_target
  have h₁ : ∀ᶠ q : (ι → ℝ) × (ι → ℝ) in 𝓝 (F x, 0), (q.2, q.1) ∈ g.target :=
    continuous_swap.continuousAt.preimage_mem_nhds hT
  have h₂ : ∀ᶠ q : (ι → ℝ) × (ι → ℝ) in 𝓝 (F x, 0), ((0 : ι → ℝ), q.1) ∈ g.target :=
    (continuous_const.prodMk continuous_fst).continuousAt.preimage_mem_nhds hT
  filter_upwards [h₁, h₂] with ⟨c, v⟩ h₁ h₂ hv
  have hv' : (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) =
      (hσ.hamiltonianFlowAction hF hcomm hc 0).toMul (s c) := by
    rw [hσ.hamiltonianFlowAction_zero_apply]
    exact (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hv
  have h := congrArg g hv'
  rw [hL.localInverse_left_inv h₁, hL.localInverse_left_inv h₂] at h
  exact (Prod.ext_iff.1 h).1

/-- **Periods continue smoothly along a section.** Let `s` be a smooth local section of `F`
through a regular point `x`, defined on an open set `t`. Every period `v₀` of `x` is the value at
`F x` of a function `λ`, smooth near `F x`, such that `λ c` is a period of `s c` for every `c`
near `F x`. -/
theorem exists_contDiffAt_mem_hamiltonianFlowStabilizer_section
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (ht : IsOpen t) (hxt : F x ∈ t) (hsx : s (F x) = x)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c) {v₀ : ι → ℝ}
    (hv₀ : v₀ ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x) :
    ∃ p : (ι → ℝ) → ι → ℝ, p (F x) = v₀ ∧ ∀ᶠ c in 𝓝 (F x),
      ContDiffAt ℝ ∞ p c ∧ p c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) := by
  have hL := hσ.isLocalDiffeomorphAt_hamiltonianFlowAction_section hF hcomm hc hdim hx ht hxt hsx
    hs hFs
  set P : (ι → ℝ) × (ι → ℝ) → M :=
    fun p ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.1).toMul (s p.2) with hP
  set g := hL.localInverse
  have hPx : P (0, F x) = x := by simp only [hP, hσ.hamiltonianFlowAction_zero_apply, hsx]
  -- Push the section by `v₀`: `Q c = v₀ • s c`, which passes through `v₀ • x = x`. Reading `Q c`
  -- through the local inverse of the sweep gives `Q c = w • s c` for a smooth `w` with
  -- `w (F x) = 0`, and the period is `v₀ - w`.
  set Q : (ι → ℝ) → M := fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc v₀).toMul (s c) with hQ
  have hQs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ Q t :=
    (hσ.hamiltonianFlowAction hF hcomm hc v₀).toMul.contMDiff.comp_contMDiffOn hs
  have hQx : Q (F x) = P (0, F x) := by
    rw [hPx, hQ]
    dsimp only
    rw [hsx]
    exact (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hv₀
  have hQc : ContinuousAt Q (F x) := (hQs.continuousOn.continuousAt (ht.mem_nhds hxt))
  have hgQ : ContinuousAt (fun c ↦ g (Q c)) (F x) :=
    ContinuousAt.comp (hQx ▸ hL.continuousAt_localInverse) hQc
  have hg0 : g (Q (F x)) = (0, F x) := by
    rw [hQx]
    exact hL.localInverse_left_inv hL.localInverse_mem_target
  refine ⟨fun c ↦ v₀ - (g (Q c)).1, by simp [hg0], ?_⟩
  have hsrc : ∀ᶠ c in 𝓝 (F x), Q c ∈ g.source :=
    hQc.preimage_mem_nhds (hQx ▸ g.open_source.mem_nhds hL.localInverse_mem_source)
  have htgt : ∀ᶠ c in 𝓝 (F x), (g (Q c)).2 ∈ t := by
    have h : Tendsto (fun c ↦ (g (Q c)).2) (𝓝 (F x)) (𝓝 (g (Q (F x))).2) :=
      (continuous_snd.tendsto _).comp hgQ
    rw [hg0] at h
    exact h.eventually_mem (ht.mem_nhds hxt)
  filter_upwards [hsrc, htgt, ht.mem_nhds hxt] with c hcs hct hc'
  refine ⟨?_, ?_⟩
  · -- `c ↦ (g (Q c)).1` is smooth at `c`, as `Q c` lies in the open source of `g`.
    have h : ContMDiffAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ (fun c ↦ (g (Q c)).1) c :=
      contMDiff_fst.contMDiffAt.comp c <|
        (hL.contMDiffOn_localInverse.contMDiffAt (g.open_source.mem_nhds hcs)).comp c
          (hQs.contMDiffAt (ht.mem_nhds hc'))
    exact contDiffAt_const.sub (contMDiffAt_iff_contDiffAt.1 h)
  · -- `P (g (Q c)) = Q c`, and `F` recovers the second coordinate of `g (Q c)` as `c`.
    have hPg : P (g (Q c)) = Q c := hL.localInverse_right_inv hcs
    have hPg' := hPg
    rw [hP] at hPg'
    dsimp only at hPg'
    have h2 : (g (Q c)).2 = c := by
      have := congrArg F hPg'
      rwa [hσ.apply_hamiltonianFlowAction hF hcomm hc, hσ.apply_hamiltonianFlowAction hF hcomm hc,
        hFs _ hct, hFs _ hc'] at this
    have h : (hσ.hamiltonianFlowAction hF hcomm hc (g (Q c)).1).toMul (s c) =
        (hσ.hamiltonianFlowAction hF hcomm hc v₀).toMul (s c) := by
      rwa [h2] at hPg'
    rw [sub_eq_neg_add]
    exact (hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc).1 h

/-- **Continuations of a period are locally unique.** Let `s` be a smooth local section of `F`
through a regular point `x`, defined on an open set `t`. Two functions `p` and `p'`, continuous at
`F x` and equal there, such that `p c` and `p' c` are periods of `s c` for `c` near `F x`, agree
near `F x`. -/
theorem eventuallyEq_of_mem_hamiltonianFlowStabilizer_section
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (ht : IsOpen t) (hxt : F x ∈ t) (hsx : s (F x) = x)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c)
    {p p' : (ι → ℝ) → ι → ℝ} (hp : ContinuousAt p (F x)) (hp' : ContinuousAt p' (F x))
    (hpp' : p (F x) = p' (F x))
    (hps : ∀ᶠ c in 𝓝 (F x), p c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c))
    (hps' : ∀ᶠ c in 𝓝 (F x), p' c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c)) :
    p =ᶠ[𝓝 (F x)] p' := by
  have hd : Tendsto (fun c ↦ (c, p c - p' c)) (𝓝 (F x)) (𝓝 (F x, 0)) := by
    have h := hp.tendsto.sub hp'.tendsto
    rw [hpp', sub_self] at h
    exact tendsto_id.prodMk_nhds h
  filter_upwards [hd.eventually (hσ.eventually_eq_zero_of_mem_hamiltonianFlowStabilizer_section
    hF hcomm hc hdim hx ht hxt hsx hs hFs), hps, hps'] with c hc hpc hpc'
  exact sub_eq_zero.1 (hc (sub_mem hpc hpc'))

/-- The local step of the proof of `exists_hamiltonianFlowStabilizer_section_eq_closure`: let the
`λ⁽ⁱ⁾` continue a basis `b` of the periods of `x`. For `(c, a)` near `(F x, a₀)`, if
`∑ aᵢ λ⁽ⁱ⁾ c` is a period of `s c`, then `a` has integer entries. When `a₀` is integral this is
the uniform discreteness of the stabilizers; otherwise `∑ a₀ᵢ bᵢ` does not fix `x`, and so
`∑ aᵢ λ⁽ⁱ⁾ c` does not fix `s c`. -/
private theorem eventually_exists_intCast_of_sum_smul_mem
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (ht : IsOpen t) (hxt : F x ∈ t) (hsx : s (F x) = x)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c)
    (b : Basis ι ℝ (ι → ℝ))
    (hb : hσ.hamiltonianFlowStabilizer hF hcomm hc x = AddSubgroup.closure (range b))
    {p : ι → (ι → ℝ) → ι → ℝ} (hpx : ∀ i, p i (F x) = b i) (hpc : ∀ i, ContinuousAt (p i) (F x))
    (hp : ∀ᶠ c in 𝓝 (F x), ∀ i, p i c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c))
    (hli : ∀ᶠ c in 𝓝 (F x), LinearIndependent ℝ fun i ↦ p i c) (a₀ : ι → ℝ) :
    ∀ᶠ z : (ι → ℝ) × (ι → ℝ) in 𝓝 (F x, a₀),
      ∑ i, z.2 i • p i z.1 ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s z.1) →
        ∃ n : ι → ℤ, z.2 = fun i ↦ (n i : ℝ) := by
  set Λ := hσ.hamiltonianFlowStabilizer hF hcomm hc
  have hpz (i : ι) : ContinuousAt (fun z : (ι → ℝ) × (ι → ℝ) ↦ p i z.1) (F x, a₀) :=
    ContinuousAt.comp (g := p i) (hpc i) continuousAt_fst
  have hT (a' : ι → ℝ) :
      ContinuousAt (fun z : (ι → ℝ) × (ι → ℝ) ↦ ∑ i, (z.2 i - a' i) • p i z.1) (F x, a₀) := by
    fun_prop
  by_cases ha : ∃ n : ι → ℤ, a₀ = fun i ↦ (n i : ℝ)
  · -- Near an integral `a₀ = n`, the period `∑ (aᵢ - nᵢ) λ⁽ⁱ⁾ c` of `s c` is near `0`, so it
    -- vanishes, and `a = n` by linear independence.
    obtain ⟨n, rfl⟩ := ha
    have hd : Tendsto (fun z : (ι → ℝ) × (ι → ℝ) ↦ (z.1, ∑ i, (z.2 i - n i) • p i z.1))
        (𝓝 (F x, fun i ↦ (n i : ℝ))) (𝓝 (F x, 0)) := by
      simpa using (continuousAt_fst.prodMk (hT fun i ↦ (n i : ℝ))).tendsto
    filter_upwards [hd.eventually (hσ.eventually_eq_zero_of_mem_hamiltonianFlowStabilizer_section
      hF hcomm hc hdim hx ht hxt hsx hs hFs), continuousAt_fst.tendsto.eventually hp,
      continuousAt_fst.tendsto.eventually hli] with z hz hpz hliz hmem
    have hsub : ∑ i, (z.2 i - n i) • p i z.1 ∈ Λ (s z.1) := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      refine sub_mem hmem (sum_mem fun i _ ↦ ?_)
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hpz i) _
    refine ⟨n, funext fun i ↦ sub_eq_zero.1 ?_⟩
    exact Fintype.linearIndependent_iff.1 hliz _ (hz hsub) i
  · -- Otherwise `∑ a₀ᵢ bᵢ` is not a period of `x`, and this persists near `(F x, a₀)`.
    have hnot : ∑ i, a₀ i • b i ∉ Λ x := by
      intro h
      rw [hb, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
        b.mem_span_iff_repr_mem ℤ, b.repr_sum_self] at h
      exact ha ⟨fun i ↦ (h i).choose, funext fun i ↦ by simpa using ((h i).choose_spec).symm⟩
    have hsc : ContinuousAt (fun z : (ι → ℝ) × (ι → ℝ) ↦ s z.1) (F x, a₀) :=
      ContinuousAt.comp (g := s) (hs.continuousOn.continuousAt (ht.mem_nhds hxt)) continuousAt_fst
    have hT₀ : ContinuousAt (fun z : (ι → ℝ) × (ι → ℝ) ↦ ∑ i, z.2 i • p i z.1) (F x, a₀) := by
      simpa using hT 0
    have hG : ContinuousAt (fun z : (ι → ℝ) × (ι → ℝ) ↦
        (hσ.hamiltonianFlowAction hF hcomm hc (∑ i, z.2 i • p i z.1)).toMul (s z.1)) (F x, a₀) :=
      (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).continuous.continuousAt.comp
        (f := fun z : (ι → ℝ) × (ι → ℝ) ↦ (∑ i, z.2 i • p i z.1, s z.1))
        (hT₀.prodMk hsc)
    have hne : ((hσ.hamiltonianFlowAction hF hcomm hc (∑ i, a₀ i • p i (F x))).toMul (s (F x)),
        s (F x)) ∈ (diagonal M)ᶜ := by
      rw [mem_compl_iff, mem_diagonal_iff]
      simp only [hpx, hsx]
      exact fun h ↦ hnot ((hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).2 h)
    filter_upwards [(hG.prodMk hsc).preimage_mem_nhds (isClosed_diagonal.isOpen_compl.mem_nhds
      hne)] with z hz hmem
    exact (hz (mem_diagonal_iff.2 ((hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hmem))).elim

/-- **A basis of periods continues to a basis of the nearby period lattices.** Let `s` be a smooth
local section of `F` through a regular point `x`, defined on an open set `t`, and let `b` be a basis
of `ι → ℝ` whose integer span is the stabilizer of `x`. Then there are functions `λ⁽ⁱ⁾`, smooth near
`F x`, with `λ⁽ⁱ⁾ (F x) = bᵢ`, such that for every `c` near `F x` the vectors `λ⁽ⁱ⁾ c` are linearly
independent and generate the stabilizer of `s c`. -/
theorem exists_hamiltonianFlowStabilizer_section_eq_closure
    (hx : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (ht : IsOpen t) (hxt : F x ∈ t) (hsx : s (F x) = x)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c)
    (b : Basis ι ℝ (ι → ℝ))
    (hb : hσ.hamiltonianFlowStabilizer hF hcomm hc x = AddSubgroup.closure (range b)) :
    ∃ p : ι → (ι → ℝ) → ι → ℝ, (∀ i, p i (F x) = b i) ∧ ∀ᶠ c in 𝓝 (F x),
      (∀ i, ContDiffAt ℝ ∞ (p i) c) ∧ LinearIndependent ℝ (fun i ↦ p i c) ∧
        hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
          AddSubgroup.closure (range fun i ↦ p i c) := by
  classical
  set Λ := hσ.hamiltonianFlowStabilizer hF hcomm hc
  have hbΛ (i : ι) : b i ∈ Λ x := hb ▸ AddSubgroup.subset_closure (mem_range_self i)
  choose p hpx hp using fun i ↦ hσ.exists_contDiffAt_mem_hamiltonianFlowStabilizer_section hF
    hcomm hc hdim hx ht hxt hsx hs hFs (hbΛ i)
  refine ⟨p, hpx, ?_⟩
  have hpc (i : ι) : ContinuousAt (p i) (F x) := ((hp i).self_of_nhds.1).continuousAt
  have hp' : ∀ᶠ c in 𝓝 (F x), ∀ i, ContDiffAt ℝ ∞ (p i) c ∧ p i c ∈ Λ (s c) := eventually_all.2 hp
  -- The vectors `λ⁽ⁱ⁾ c` stay linearly independent, an open condition.
  have hli : ∀ᶠ c in 𝓝 (F x), LinearIndependent ℝ fun i ↦ p i c := by
    have hcont : ContinuousAt (fun c i ↦ p i c) (F x) := continuousAt_pi.2 hpc
    have hb' : (fun i ↦ p i (F x)) = b := funext hpx
    exact hcont.preimage_mem_nhds
      (hb' ▸ isOpen_setOfPred_linearIndependent.mem_nhds b.linearIndependent)
  -- The key step: for `c` near `F x`, a period of `s c` with coefficients in `[0, 1]` on the
  -- `λ⁽ⁱ⁾ c` has integer coefficients.
  have hcube : ∀ᶠ c in 𝓝 (F x), ∀ a ∈ Icc (0 : ι → ℝ) 1, ∑ i, a i • p i c ∈ Λ (s c) →
      ∃ n : ι → ℤ, a = fun i ↦ (n i : ℝ) :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun a _ ↦
      hσ.eventually_exists_intCast_of_sum_smul_mem hF hcomm hc hdim hx ht hxt hsx hs hFs b hb hpx
        hpc (hp'.mono fun _ h i ↦ (h i).2) hli a
  filter_upwards [hp', hli, hcube] with c hpc' hlic hcubec
  have hcl : AddSubgroup.closure (range fun i ↦ p i c) ≤ Λ (s c) :=
    AddSubgroup.closure_le _ |>.2 <| range_subset_iff.2 fun i ↦ (hpc' i).2
  refine ⟨fun i ↦ (hpc' i).1, hlic, le_antisymm (fun v hv ↦ ?_) hcl⟩
  -- Reduce `v` modulo the lattice spanned by the basis `λ⁽ⁱ⁾ c`: its remainder `ZSpan.fract` is
  -- again a period of `s c`, with coefficients in `[0, 1)`, hence zero.
  set bc := basisOfPiSpaceOfLinearIndependent hlic
  have hbc : ⇑bc = fun i ↦ p i c := coe_basisOfPiSpaceOfLinearIndependent hlic
  have hfl : (ZSpan.floor bc v : ι → ℝ) ∈ AddSubgroup.closure (range fun i ↦ p i c) := by
    rw [← hbc, ← Submodule.span_int_eq_addSubgroupClosure]
    exact (ZSpan.floor bc v).2
  have hfr : ZSpan.fract bc v = ∑ i, Int.fract (bc.repr v i) • p i c := by
    conv_lhs => rw [← bc.sum_repr (ZSpan.fract bc v)]
    simp [ZSpan.repr_fract_apply, hbc]
  obtain ⟨n, hn⟩ := hcubec _ ⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩
    (hfr ▸ ZSpan.fract_apply bc v ▸ sub_mem hv (hcl hfl))
  have h0 : ZSpan.fract bc v = 0 := by
    rw [hfr]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Int.fract_fract, congrFun hn i, Int.fract_intCast, zero_smul]
  rw [ZSpan.fract_apply, sub_eq_zero] at h0
  exact h0 ▸ hfl

/-- **Smooth period lattices near a compact Liouville torus.** On a manifold of dimension
`2 · |ι|`, let the connected component of `x` in its level `F⁻¹(F x)` be compact and consist of
regular points of `F`, and let `s` be a smooth local section of `F` through `x`, defined on an open
set `t`. Then there are functions `λ⁽ⁱ⁾`, smooth near `F x`, such that for every `c` near `F x` the
vectors `λ⁽ⁱ⁾ c` are linearly independent and generate the stabilizer of `s c`. At `c = F x` they
form a basis of the period lattice of `x`. -/
theorem exists_hamiltonianFlowStabilizer_section_eq_closure_of_isCompact
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (ht : IsOpen t) (hxt : F x ∈ t)
    (hsx : s (F x) = x) (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c) :
    ∃ p : ι → (ι → ℝ) → ι → ℝ, ∀ᶠ c in 𝓝 (F x),
      (∀ i, ContDiffAt ℝ ∞ (p i) c) ∧ LinearIndependent ℝ (fun i ↦ p i c) ∧
        hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
          AddSubgroup.closure (range fun i ↦ p i c) := by
  have hx := hreg x (mem_connectedComponentIn (by simp))
  set Λ := hσ.hamiltonianFlowStabilizer hF hcomm hc x
  have : DiscreteTopology Λ := hσ.discreteTopology_hamiltonianFlowStabilizer hF hcomm hc hx
  have : IsZLattice ℝ Λ.toIntSubmodule :=
    hσ.isZLattice_hamiltonianFlowStabilizer hF hcomm hc hdim hreg hK
  -- A `ℤ`-basis of the period lattice of `x` is an `ℝ`-basis of `ι → ℝ` generating it.
  set bℤ := IsZLattice.basis Λ.toIntSubmodule
  have hb : Λ = AddSubgroup.closure (range (bℤ.ofZLatticeBasis ℝ Λ.toIntSubmodule)) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, bℤ.ofZLatticeBasis_span ℝ,
      AddSubgroup.toIntSubmodule_toAddSubgroup]
  obtain ⟨p, -, hp⟩ := hσ.exists_hamiltonianFlowStabilizer_section_eq_closure hF hcomm hc hdim hx
    ht hxt hsx hs hFs _ hb
  exact ⟨p, hp⟩

end IsSymplectic

end SmoothTwoForm

end TauCeti
