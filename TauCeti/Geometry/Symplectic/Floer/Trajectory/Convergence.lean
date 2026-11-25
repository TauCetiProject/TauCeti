/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Trajectory.BrokenLimit
public import TauCeti.Geometry.Symplectic.Floer.Trajectory.Limit
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
import TauCeti.Topology.Separation.Periodic
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Translate

/-!
# Floer trajectories converge to broken trajectories

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H` a `C³` Hamiltonian and `J_t(x)` a
family of almost complex structures tamed by `ω` on a compact set `K`, both `1`-periodic in time,
all of whose `1`-periodic orbits in `K` are nondegenerate. Let `u_k` be smooth Floer trajectories,
solutions of `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops in `K` and a common
Lipschitz constant, none of them stationary, all running from the orbit `x₀` at `s → -∞` to the
orbit `x₁` at `s → ∞`. This file proves Floer's compactness theorem up to breaking for such a
sequence, `exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_sum_setLIntegral_eq` in the
namespace `TauCeti.SymplecticForm`: there are a subsequence `u (φ n)` and a *broken trajectory*
from `x₀` to `x₁`, that is

* orbits `x₀ = y 0, y 1, …, y (p + 1) = x₁` in `K`, and
* nonstationary `C¹` Floer trajectories `g 0, …, g p`, the *levels*, with `g j` running from
  `y j` at `s → -∞` to `y (j + 1)` at `s → ∞`, uniformly in `t`,

such that for shifts `τ j n` with `τ (j + 1) n - τ j n → ∞` the translates
`(s, t) ↦ u (φ n) (s + τ j n, t)` converge to `g j` locally uniformly, and no energy is lost in
the limit: the energies of the levels add up to the energy of every `u (φ n)`, which is
`A_H(x₁) - A_H(x₀)`.

The proof assembles the levels at finitely many regular action values and the necks between
them (`TauCeti.Geometry.Symplectic.Floer.Trajectory.Breaking`), the matching of consecutive levels
at the neck orbits and of the first and last levels with `x₀` and `x₁`
(`TauCeti.Geometry.Symplectic.Floer.Trajectory.BrokenLimit`), and the regularity and energy of
limits of Floer trajectories (`TauCeti.Geometry.Symplectic.Floer.Trajectory.Limit`). Selecting
one level per gap between consecutive orbit actions may select the same level several times, up
to translation, when the sequence does not break at the orbit actions in between; this file
keeps one level from each run of translates, and the levels it keeps are joined at the orbits
where the sequence breaks. The energy of each level is the drop of action between its ends, so
the energies telescope to `A_H(x₁) - A_H(x₀)`.

As in `TauCeti.Geometry.Symplectic.Floer.Trajectory.Level`, the uniform bound on the derivatives of
the `u_k` excludes bubbling; it is assumed, not proved.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, on the convergence of sequences of trajectories to broken trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on compactness up to breaking.
* M. Audin and M. Damian, *Morse theory and Floer homology*, Springer Universitext (2014),
  Chapter 9, on the compactness of spaces of Floer trajectories.
-/

public section

open Set Filter Topology Function MeasureTheory
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {W : Set (ℝ × V)} {K : Set V} {L L' : ℝ≥0} {u : ℕ → ℝ × ℝ → V}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Keeping one level from each run of translates.** Let `G 0, …, G m` be maps with shifts
`σ 0, …, σ m` such that any two consecutive ones either differ by a translation `δ`, the
differences of their shifts converging to `δ`, or are joined at an orbit `x` satisfying `P`, the
differences of their shifts tending to infinity, `G i (s, ·)` converging to `x` as `s → ∞` and
`G (i + 1) (s, ·)` as `s → -∞`. If `G 0` starts at `x₀` and `G m` ends at `x₁`, both satisfying
`P`, then there are indices `ι 0, …, ι p` and a chain `x₀ = y 0, …, y (p + 1) = x₁` of orbits
satisfying `P` such that `G (ι j)` runs from `y j` to `y (j + 1)`, the differences of consecutive
selected shifts tend to infinity, and the last selected shift stays a convergent distance from
`σ m`. -/
private theorem exists_chain_of_forall_or {P : (ℝ → V) → Prop} {x₀ : ℝ → V} (hx₀ : P x₀) :
    ∀ {m : ℕ} {G : Fin (m + 1) → ℝ × ℝ → V} {σ : Fin (m + 1) → ℕ → ℝ} {x₁ : ℝ → V}, P x₁ →
    TendstoUniformly (fun s t ↦ G 0 (s, t)) x₀ atBot →
    TendstoUniformly (fun s t ↦ G (Fin.last m) (s, t)) x₁ atTop →
    (∀ i : Fin m,
      (∃ δ, Tendsto (fun n ↦ σ i.succ n - σ i.castSucc n) atTop (𝓝 δ) ∧
        ∀ z, G i.succ z = G i.castSucc (z + (δ, 0))) ∨
      (Tendsto (fun n ↦ σ i.succ n - σ i.castSucc n) atTop atTop ∧
        ∃ x, P x ∧ TendstoUniformly (fun s t ↦ G i.castSucc (s, t)) x atTop ∧
          TendstoUniformly (fun s t ↦ G i.succ (s, t)) x atBot)) →
    ∃ p, ∃ ι : Fin (p + 1) → Fin (m + 1), ∃ y : Fin (p + 2) → ℝ → V,
      y 0 = x₀ ∧ y (Fin.last (p + 1)) = x₁ ∧ (∀ j, P (y j)) ∧
      (∀ j, TendstoUniformly (fun s t ↦ G (ι j) (s, t)) (y j.castSucc) atBot ∧
        TendstoUniformly (fun s t ↦ G (ι j) (s, t)) (y j.succ) atTop) ∧
      (∀ j : Fin p, Tendsto (fun n ↦ σ (ι j.succ) n - σ (ι j.castSucc) n) atTop atTop) ∧
      ∃ δ, Tendsto (fun n ↦ σ (Fin.last m) n - σ (ι (Fin.last p)) n) atTop (𝓝 δ)
  | 0, G, σ, x₁, hx₁, h₀, h₁, _ => by
    refine ⟨0, fun _ ↦ 0, ![x₀, x₁], rfl, rfl, fun j ↦ ?_, fun j ↦ ?_, finZeroElim, 0, ?_⟩
    · fin_cases j <;> assumption
    · fin_cases j
      exact ⟨h₀, h₁⟩
    · simp
  | m + 1, G, σ, x₁, hx₁, h₀, h₁, hG => by
    rcases hG (Fin.last m) with ⟨δ, hδ, hGδ⟩ | ⟨hdiv, x, hx, hxtop, hxbot⟩
    · -- The last two maps differ by a translation: drop the last one.
      rw [Fin.succ_last] at hδ hGδ
      obtain ⟨p, ι, y, hy₀, hy₁, hP, hlev, hsh, δ', hδ'⟩ :=
        exists_chain_of_forall_or hx₀ (G := fun i ↦ G i.castSucc) (σ := fun i ↦ σ i.castSucc)
          hx₁ h₀ (tendstoUniformly_atTop_of_eq_comp_add hGδ h₁) fun i ↦ by
            simpa only [Fin.succ_castSucc] using hG i.castSucc
      refine ⟨p, fun j ↦ (ι j).castSucc, y, hy₀, hy₁, hP, hlev, hsh, δ + δ', ?_⟩
      exact (hδ.add hδ').congr fun n ↦ by ring
    · -- The last two maps are joined at `x`: keep the last one as a new level.
      rw [Fin.succ_last] at hdiv hxbot
      obtain ⟨p, ι, y, hy₀, hy₁, hP, hlev, hsh, δ', hδ'⟩ :=
        exists_chain_of_forall_or hx₀ (G := fun i ↦ G i.castSucc) (σ := fun i ↦ σ i.castSucc)
          hx h₀ hxtop fun i ↦ by simpa only [Fin.succ_castSucc] using hG i.castSucc
      refine ⟨p + 1, Fin.snoc (fun j ↦ (ι j).castSucc) (Fin.last (m + 1)), Fin.snoc y x₁,
        by simpa [← Fin.castSucc_zero] using hy₀, Fin.snoc_last _ _, fun j ↦ ?_, fun j ↦ ?_,
        fun j ↦ ?_, 0, by simp⟩
      · induction j using Fin.lastCases with
        | last => simpa using hx₁
        | cast j => simpa using hP j
      · induction j using Fin.lastCases with
        | last => simpa [Fin.succ_last, hy₁] using ⟨hxbot, h₁⟩
        | cast j =>
          simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
          exact hlev j
      · induction j using Fin.lastCases with
        | last =>
          simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
          exact (hdiv.atTop_add hδ').congr fun n ↦ by ring
        | cast j =>
          simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
          exact hsh j

/-- **A level of a broken limit.** Let `H` be a `C²` Hamiltonian and `J_t(x)` a family of almost
complex structures, `C¹` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `K` for a closed `K`, both
`1`-periodic in time. Let `u_k` be smooth `L`-Lipschitz Floer trajectories with `1`-periodic loops
in `K`, and let their translates at shifts `τ_k` converge locally uniformly to `g`. If the loops of
`g` converge uniformly to closed `C¹` loops `x₀` as `s → -∞` and `x₁` as `s → ∞`, then `g` is a
`C¹` Floer trajectory, `A_H(x₀) ≤ A_H(x₁)`, and the energy of `g` is `A_H(x₁) - A_H(x₀)`. -/
private theorem contDiff_and_setLIntegral_eq_of_comp_add
    (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsClosed K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {τ : ℕ → ℝ} {g : ℝ × ℝ → V}
    (hg : TendstoLocallyUniformly (fun k z ↦ u k (z + (τ k, 0))) g atTop)
    {x₀ x₁ : ℝ → V} (hx₀ : ContDiff ℝ 1 x₀) (hx₀per : x₀ 1 = x₀ 0) (hx₁ : ContDiff ℝ 1 x₁)
    (hx₁per : x₁ 1 = x₁ 0) (hbot : TendstoUniformly (fun s t ↦ g (s, t)) x₀ atBot)
    (htop : TendstoUniformly (fun s t ↦ g (s, t)) x₁ atTop) :
    ContDiff ℝ 1 g ∧
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (g z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) g z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      ω.hamiltonianAction H x₀ ≤ ω.hamiltonianAction H x₁ ∧
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) g z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) := by
  -- The translates `v_k` are smooth `L`-Lipschitz Floer trajectories for the same data.
  set v : ℕ → ℝ × ℝ → V := fun k z ↦ u k (z + (τ k, 0))
  have hvc (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (v k) := (hu k).comp (contDiff_id.add contDiff_const)
  have hvper (k : ℕ) (s : ℝ) : Periodic (fun t ↦ v k (s, t)) 1 := fun t ↦ by
    simpa [v] using hper k (s + τ k) t
  have hvfloer (k : ℕ) : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (v k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (v k) z : ℝ × ℝ →ₗ[ℝ] V) :=
    fun z hz ↦ by
      simpa using isComplexLinearMap_perturbedFDeriv_comp_add (τ k)
        (hfloer k _ ⟨mem_univ _, by simpa using hz.2⟩)
  have hvL (k : ℕ) : LipschitzWith L (v k) :=
    ((hL k).comp (IsometryEquiv.addRight ((τ k, 0) : ℝ × ℝ)).isometry.lipschitzWith).weaken
      (mul_one L).le
  have hgK (z : ℝ × ℝ) : g z ∈ K := hK.mem_of_tendsto
    (hg.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)) (.of_forall fun k ↦ huK k _)
  have hgW (z : ℝ × ℝ) : (z.2, g z) ∈ W := hKW ⟨mem_univ _, hgK z⟩
  -- The limit is a `C¹` Floer trajectory, and its energy is the drop of action between its ends.
  obtain ⟨hgc, -, hgeq⟩ := tendstoLocallyUniformly_fderiv_of_floer_of_periodic hH hHper hW hJ
    hJper hvc hvper hvfloer (fun _ _ ↦ ⟨L, fun k _ _ ↦ norm_fderiv_le_of_lipschitz ℝ (hvL k)⟩) hgW
    fun z ↦ hg.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  exact ⟨hgc, hgeq,
    hamiltonianAction_le_hamiltonianAction_of_tendstoUniformly hH hHper hW hJ hJper hvc hvper
      hvfloer hvL hgW (fun z ↦ hJt _ _ (hgK z)) hg hx₀ hx₀per hx₁ hx₁per hbot htop,
    setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub_of_tendstoUniformly hH hHper hW
      hJ hJper hvc hvper hvfloer hvL hgW (fun z ↦ hJt _ _ (hgK z)) hg hx₀ hx₀per hx₁ hx₁per hbot
      htop⟩

/-- **The levels of a sequence of trajectories from `x₀` to `x₁`.** Under the hypotheses of
`exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_sum_setLIntegral_eq`, there are a
subsequence `u (φ n)` and finitely many nonstationary levels `G 0, …, G m`, limits of translates of
the `u (φ n)` at shifts `σ i n`, such that `G 0` starts at `x₀`, `G m` ends at `x₁`, and any two
consecutive levels either differ by a translation, the differences of their shifts converging, or
are joined at a `1`-periodic orbit in `K`, the differences of their shifts tending to infinity. -/
private theorem exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_or
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hfin : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}).Finite)
    (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) (hns : ∀ k, ∃ s t, u k (s, t) ≠ u k (0, t))
    {x₀ x₁ : ℝ → V} (hbot : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₀ atBot)
    (htop : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₁ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ m : ℕ, ∃ σ : Fin (m + 1) → ℕ → ℝ,
      ∃ G : Fin (m + 1) → ℝ × ℝ → V,
      (∀ i, TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (σ i n, 0))) (G i) atTop ∧
        ∃ s t, G i (s, t) ≠ G i (0, t)) ∧
      TendstoUniformly (fun s t ↦ G 0 (s, t)) x₀ atBot ∧
      TendstoUniformly (fun s t ↦ G (Fin.last m) (s, t)) x₁ atTop ∧
      ∀ i : Fin m,
        (∃ δ, Tendsto (fun n ↦ σ i.succ n - σ i.castSucc n) atTop (𝓝 δ) ∧
          ∀ z, G i.succ z = G i.castSucc (z + (δ, 0))) ∨
        (Tendsto (fun n ↦ σ i.succ n - σ i.castSucc n) atTop atTop ∧
          ∃ x : ℝ → V, (Periodic x 1 ∧
            (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K) ∧
            TendstoUniformly (fun s t ↦ G i.castSucc (s, t)) x atTop ∧
            TendstoUniformly (fun s t ↦ G i.succ (s, t)) x atBot) := by
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hu2 (k : ℕ) : ContDiff ℝ 2 (u k) := (hu k).of_le (WithTop.coe_le_coe.2 le_top)
  have hu3 (k : ℕ) : ContDiff ℝ 3 (u k) := (hu k).of_le (WithTop.coe_le_coe.2 le_top)
  -- The action increases along each `u k`.
  have hmono (k : ℕ) : Monotone fun s ↦ ω.hamiltonianAction H (fun t ↦ u k (s, t)) :=
    ω.monotone_hamiltonianAction_of_floer (J := fun z ↦ J z.2 (u k z)) hH1 (hu2 k) (hper k)
      (fun z _ ↦ hJt _ _ (huK k z)) (hfloer k)
  -- Select regular action values `b 0 < ⋯ < b m` separating the orbit actions, and shifts.
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ.continuousOn.mono hKW) hJper hJt
  obtain ⟨φ₁, hφ₁, a₀, a₁, -, hends, m, b, hb, hbC, h0, h1, hgaps, σ, hσ⟩ :=
    exists_subseq_forall_hamiltonianAction_eq_of_floer (J := fun k z ↦ J z.2 (u k z)) hH1 hHper hK
      hfin hu2 hper huK hc (fun k z _ v ↦ (hcM z.2 _ (huK k z) v).1)
      (fun k z _ v ↦ (hcM z.2 _ (huK k z) v).2) hfloer hL hns
  -- The levels at these values, consecutive ones translates of each other or joined at an orbit.
  obtain ⟨φ₂, hφ₂, G, hG, hlev⟩ :=
    exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_tendstoUniformly (u := u ∘ φ₁) hH
    hHper hW hJ hJper hK hKW hJt hL' hnd (fun _ ↦ hu3 _) (fun _ ↦ hper _) (fun _ ↦ huK _)
    (fun _ ↦ hfloer _) (fun _ ↦ hL _) hb hbC
    (fun i ↦ by obtain ⟨c', hc'⟩ := hgaps i; rw [hc']; exact subsingleton_singleton) hσ
  -- The first level starts at `x₀` and the last one ends at `x₁`.
  have hfirst : TendstoUniformly (fun s t ↦ G 0 (s, t)) x₀ atBot :=
    tendstoUniformly_atBot_of_forall_tendstoUniformly_atBot (u := u ∘ φ₁ ∘ φ₂)
      (σ' := fun n ↦ σ 0 (φ₂ n)) hH hHper hW hJ hJper hK hKW hJt hL' hnd (fun _ ↦ hu3 _)
      (fun _ ↦ hper _) (fun _ ↦ huK _) (fun _ ↦ hfloer _) (fun _ ↦ hL _)
      (fun n ↦ (hσ 0 (φ₂ n)).le) (fun n s ↦ (hmono _).le_of_tendsto (hends (φ₂ n)).1 s)
      (by rw [h0]; exact subsingleton_singleton) (fun _ ↦ hbot _) fun z ↦ (hG 0).1.tendsto_at z
  have hlast : TendstoUniformly (fun s t ↦ G (Fin.last m) (s, t)) x₁ atTop :=
    tendstoUniformly_atTop_of_forall_tendstoUniformly_atTop (u := u ∘ φ₁ ∘ φ₂)
      (σ := fun n ↦ σ (Fin.last m) (φ₂ n)) hH hHper hW hJ hJper hK hKW hJt hL' hnd
      (fun _ ↦ hu3 _) (fun _ ↦ hper _) (fun _ ↦ huK _) (fun _ ↦ hfloer _) (fun _ ↦ hL _)
      (fun n ↦ (hσ _ (φ₂ n)).ge) (fun n s ↦ (hmono _).ge_of_tendsto (hends (φ₂ n)).2 s)
      (by rw [h1]; exact subsingleton_singleton) (fun _ ↦ htop _)
      fun z ↦ (hG _).1.tendsto_at z
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, m, fun i n ↦ σ i (φ₂ n), G, hG, hfirst, hlast,
    fun i ↦ (hlev i).imp_right fun ⟨hdiv, x, hxp, hxd, hxK, _, h₁, h₂⟩ ↦
      ⟨hdiv, x, ⟨hxp, hxd, hxK⟩, h₁, h₂⟩⟩

/-- **Floer trajectories converge to a broken trajectory.** Let `(V, ω)` be a finite-dimensional
symplectic vector space, `H` a `C³` Hamiltonian and `J_t(x)` a family of almost complex structures,
`C²` on an open set `W` containing `ℝ × K` for a compact `K ⊆ V`, both `1`-periodic in time, with
`J` tamed by `ω` on `ℝ × K`. Suppose that the suspension of the Hamiltonian vector field is
globally Lipschitz, that every `1`-periodic orbit in `K` is nondegenerate, and that these orbits
have finitely many actions. Let `u_k` be smooth Floer trajectories,
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0`, with `1`-periodic loops in `K` and a common Lipschitz
constant, none of them stationary, whose loops converge uniformly to a loop `x₀` as `s → -∞` and
to a loop `x₁` as `s → ∞`, both solving `x'(t) = X_{H_t}(x(t))`. Then there are a subsequence
`u (φ n)`, orbits `x₀ = y 0, y 1, …, y (p + 1) = x₁` in `K`, maps `g 0, …, g p` and shifts
`τ 0, …, τ p` such that

* the translates `(s, t) ↦ u (φ n) (s + τ j n, t)` converge locally uniformly to `g j`;
* each `g j` is a nonstationary `C¹` solution of the Floer equation whose loops converge uniformly
  to `y j` as `s → -∞` and to `y (j + 1)` as `s → ∞`;
* consecutive shifts drift apart, `τ (j + 1) n - τ j n → ∞`;
* no energy is lost: the energies of the `g j` add up to the energy of every `u (φ n)`. -/
theorem exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_sum_setLIntegral_eq
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hfin : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}).Finite)
    (hu : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) (hns : ∀ k, ∃ s t, u k (s, t) ≠ u k (0, t))
    {x₀ x₁ : ℝ → V} (hx₀d : ∀ t, HasDerivAt x₀ (ω.hamiltonianVectorField (H t) (x₀ t)) t)
    (hx₁d : ∀ t, HasDerivAt x₁ (ω.hamiltonianVectorField (H t) (x₁ t)) t)
    (hbot : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₀ atBot)
    (htop : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x₁ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : ℕ, ∃ τ : Fin (p + 1) → ℕ → ℝ,
      ∃ g : Fin (p + 1) → ℝ × ℝ → V, ∃ y : Fin (p + 2) → ℝ → V,
      y 0 = x₀ ∧ y (Fin.last (p + 1)) = x₁ ∧
      (∀ j, Periodic (y j) 1 ∧
        (∀ t, HasDerivAt (y j) (ω.hamiltonianVectorField (H t) (y j t)) t) ∧ ∀ t, y j t ∈ K) ∧
      (∀ j, TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (τ j n, 0))) (g j) atTop ∧
        ContDiff ℝ 1 (g j) ∧
        (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (g j z))
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (g j) z : ℝ × ℝ →ₗ[ℝ] V)) ∧
        (∃ s t, g j (s, t) ≠ g j (0, t)) ∧
        TendstoUniformly (fun s t ↦ g j (s, t)) (y j.castSucc) atBot ∧
        TendstoUniformly (fun s t ↦ g j (s, t)) (y j.succ) atTop) ∧
      (∀ j : Fin p, Tendsto (fun n ↦ τ j.succ n - τ j.castSucc n) atTop atTop) ∧
      ∀ n, ∑ j, ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (g j) z) =
        ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u (φ n)) z) := by
  obtain ⟨φ, hφ, m, σ, G, hG, hfirst, hlast, hlev⟩ :=
    exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_or hH hHper hW hJ hJper hK hKW hJt
      hL' hnd hfin hu hper huK hfloer hL hns hbot htop
  -- The end loops are `1`-periodic orbits in `K`, as limits of loops of `u 0`.
  have hx₀ : Periodic x₀ 1 := periodic_of_tendsto (.of_forall (hper 0)) (hbot 0).tendsto_at
  have hx₁ : Periodic x₁ 1 := periodic_of_tendsto (.of_forall (hper 0)) (htop 0).tendsto_at
  have hx₀K (t : ℝ) : x₀ t ∈ K :=
    hK.isClosed.mem_of_tendsto ((hbot 0).tendsto_at t) (.of_forall fun _ ↦ huK 0 _)
  have hx₁K (t : ℝ) : x₁ t ∈ K :=
    hK.isClosed.mem_of_tendsto ((htop 0).tendsto_at t) (.of_forall fun _ ↦ huK 0 _)
  -- Keep one level from each run of translates.
  obtain ⟨p, ι, y, hy₀, hy₁, hP, hends', hsh, -⟩ :=
    exists_chain_of_forall_or (P := fun x ↦ Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K)
      (x₀ := x₀) ⟨hx₀, hx₀d, hx₀K⟩ (G := G) (σ := σ) ⟨hx₁, hx₁d, hx₁K⟩ hfirst hlast hlev
  -- Each kept level is a `C¹` Floer trajectory whose energy is the drop of action between its ends.
  have hyc (j : Fin (p + 2)) : ContDiff ℝ 1 (y j) :=
    contDiff_one_of_hasDerivAt (X := fun t ↦ ω.hamiltonianVectorField (H t))
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (hH.of_le (by norm_num))).continuous
      (hP j).2.1
  have hyper (j : Fin (p + 2)) : y j 1 = y j 0 := by simpa using (hP j).1 0
  have hlevel (j : Fin (p + 1)) :=
    contDiff_and_setLIntegral_eq_of_comp_add (u := u ∘ φ) (hH.of_le (by norm_num)) hHper hW
      (hJ.of_le (by norm_num)) hJper hK.isClosed hKW hJt (fun _ ↦ hu _) (fun _ ↦ hper _)
      (fun _ ↦ huK _) (fun _ ↦ hfloer _) (fun _ ↦ hL _) (hG (ι j)).1 (hyc _) (hyper _) (hyc _)
      (hyper _) (hends' j).1 (hends' j).2
  -- The energy of every trajectory of the subsequence is `A_H(x₁) - A_H(x₀)`.
  have henergy (k : ℕ) := (contDiff_and_setLIntegral_eq_of_comp_add (u := fun _ ↦ u k) (τ := 0)
      (hH.of_le (by norm_num)) hHper hW (hJ.of_le (by norm_num)) hJper hK.isClosed hKW hJt
      (fun _ ↦ hu k) (fun _ ↦ hper k) (fun _ ↦ huK k) (fun _ ↦ hfloer k) (fun _ ↦ hL k) (g := u k)
      (by simpa only [Pi.zero_apply, Prod.mk_zero_zero, add_zero] using
        tendstoLocallyUniformly_const (ι := ℕ) (l := atTop) (u k))
      (hy₀ ▸ hyc 0) (hy₀ ▸ hyper 0) (hy₁ ▸ hyc _) (hy₁ ▸ hyper _) (hbot k) (htop k)).2.2.2
  refine ⟨φ, hφ, p, fun j ↦ σ (ι j), fun j ↦ G (ι j), y, hy₀, hy₁, hP,
    fun j ↦ ⟨(hG (ι j)).1, (hlevel j).1, (hlevel j).2.1, (hG (ι j)).2, hends' j⟩, hsh,
    fun n ↦ ?_⟩
  -- The energies of the levels telescope.
  rw [henergy, Finset.sum_congr rfl fun j _ ↦ (hlevel j).2.2.2,
    ← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sub_nonneg.2 (hlevel j).2.2.1]
  congr 1
  have huniv : Finset.Iic (Fin.last p) = Finset.univ := by ext; simp [Fin.le_last]
  rw [← huniv]
  exact (Fin.sum_Iic_sub (Fin.last p) fun j ↦ ω.hamiltonianAction H (y j)).trans
    (by rw [Fin.succ_last, hy₀, hy₁])

end TauCeti.SymplecticForm
