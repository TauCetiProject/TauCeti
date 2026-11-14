/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic
import TauCeti.Geometry.Symplectic.Floer.Translation.Basic

/-!
# The ends and the energy gap of finite-energy Floer trajectories

Let `(V, ω)` be a symplectic vector space and `H : ℝ → V → ℝ` a `C¹` Hamiltonian, `1`-periodic in
time. A *Floer trajectory* is a solution `u : ℝ × ℝ → V` of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt`, with
`1`-periodic loops `t ↦ u(s, t)`, for almost complex structures `J z` which may depend on the
domain point and are uniformly tame, `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` with `c > 0`.
Such trajectories are the cylinders counted by the Floer differential and inserted at the ends of a
pair of pants when it breaks.

If a `C²` Floer trajectory has finite energy and its loops stay in a compact set `K`, then the
limiting action at each of its two ends is realized by a `1`-periodic orbit of the Hamiltonian
vector field: there are orbits `x₀` and `x₁` in `K` such that the actions `A_H(u(s, ·))` tend to
`A_H(x₀)` as `s → -∞` and to `A_H(x₁)` as `s → ∞`, and the energy of `u` is `A_H(x₁) - A_H(x₀)`
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`). The end at
`+∞` is `TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer`,
the end at `-∞` is its reflection
`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer`, and
the energy identity is
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`. Only the
actions are asserted to converge: the half-cylinder results give uniform convergence of the loops
to these orbits along some sequences `s_n → ±∞`, and no convergence of the loops `u(s, ·)` as
`s → ±∞` is claimed here.

Consequently the energy of a trajectory in `K` only takes values in the set of action differences
of the orbits in `K`. A trajectory of zero energy is stationary,
`u(s, t) = u(0, t)` (`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`). Hence, if
the `1`-periodic orbits in `K` have only finitely many actions, for instance because there are
only finitely many of them, as happens when they are all nondegenerate, there is an **energy gap**:
a constant `δ > 0`, depending only on `ω`, `H` and `K`, such that every Floer trajectory in `K`
which is not stationary has energy at least `δ`
(`TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_lintegral_floerEnergyDensity`). No bound on
the derivative of `u` is assumed. In the compactness theory of Floer trajectories and of pairs of
pants, this lower bound on the energy of each nonstationary cylinder bounds the number of
cylinders that can break off at an end by the total energy divided by `δ`.

## Main results

* `TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`: periodic
  orbits realizing the limiting actions at the two ends of a finite-energy Floer trajectory, and
  its energy as the difference of their actions.
* `TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_lintegral_floerEnergyDensity`: the energy
  gap for Floer trajectories in a compact set whose `1`-periodic orbits have finitely many
  actions.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the energy of finite-energy Floer trajectories and their
  limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V}
  {c M : ℝ} {K : Set V}

/-- **The ends of a finite-energy Floer trajectory.** Let `u` be a `C²` solution of the Floer
equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]` for a `C¹` Hamiltonian `H`,
`1`-periodic in time, with `1`-periodic loops in a compact set `K`, uniformly tame almost complex
structures and finite energy. Then there are `1`-periodic orbits `x₀` and `x₁` of the Hamiltonian
vector field, with values in `K`, such that the actions `A_H(u(s, ·))` tend to `A_H(x₀)` as
`s → -∞` and to `A_H(x₁)` as `s → ∞`, and the energy of `u` is `A_H(x₁) - A_H(x₀)`. -/
theorem exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hu : ContDiff ℝ 2 u)
    (hper : ∀ s, Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K) (huK : ∀ s t, u (s, t) ∈ K)
    (hc : 0 < c) (hJc : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x₀ x₁ : ℝ → V,
      (Periodic x₀ 1 ∧ (∀ t, HasDerivAt x₀ (ω.hamiltonianVectorField (H t) (x₀ t)) t) ∧
        ∀ t, x₀ t ∈ K) ∧
      (Periodic x₁ 1 ∧ (∀ t, HasDerivAt x₁ (ω.hamiltonianVectorField (H t) (x₁ t)) t) ∧
        ∀ t, x₁ t ∈ K) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot
        (𝓝 (ω.hamiltonianAction H x₀)) ∧
      Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop
        (𝓝 (ω.hamiltonianAction H x₁)) ∧
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
        ENNReal.ofReal (ω.hamiltonianAction H x₁ - ω.hamiltonianAction H x₀) := by
  -- Both half-cylinders `s > 0` and `s < 0` inherit the hypotheses from the whole cylinder.
  have hsub {S : Set ℝ} : S ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  have hEsub {S : Set ℝ} : ∫⁻ z in S ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤ :=
    ne_top_of_le_ne_top hE (lintegral_mono_set hsub)
  -- A uniform limit of loops in the closed set `K` takes values in `K`.
  have hlimK {φ : ℕ → ℝ} {x : ℝ → V} (hux : TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop)
      (t : ℝ) : x t ∈ K :=
    hK.isClosed.mem_of_tendsto (hux.tendsto_at t) (Eventually.of_forall fun n ↦ huK _ _)
  obtain ⟨x₁, hx₁per, hx₁, ⟨φ₁, -, -, hux₁⟩, htop⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (a := 0) hH hHper hu.contDiffOn
      (fun s _ ↦ hper s) hK (fun s _ ↦ huK s) hc (fun z hz ↦ hJc z (hsub hz))
      (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz)) hEsub
  obtain ⟨x₀, hx₀per, hx₀, ⟨φ₀, -, -, hux₀⟩, hbot⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_atBot_of_floer (a := 0) hH hHper
      hu.contDiffOn (fun s _ ↦ hper s) hK (fun s _ ↦ huK s) hc (fun z hz ↦ hJc z (hsub hz))
      (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz)) hEsub
  refine ⟨x₀, x₁, ⟨hx₀per, hx₀, hlimK hux₀⟩, ⟨hx₁per, hx₁, hlimK hux₁⟩, hbot, htop, ?_⟩
  have hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  exact ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction hJ hH isOpen_univ
    hu.contDiffOn (subset_univ _) (fun s ↦ by simpa using hper s 0)
    (fun z hz ↦ by
      simpa using (ω.isComplexLinearMap_perturbedFDeriv_iff _ _ _ u z).1 (hfloer z hz))
    hbot htop

/-- **The energy gap of Floer trajectories.** Let `H` be a `C¹` Hamiltonian, `1`-periodic in time,
and `K` a compact set such that the `1`-periodic orbits of its Hamiltonian vector field with values
in `K` have only finitely many actions, for instance because there are only finitely many of them,
as happens when they are all nondegenerate. Then there is `δ > 0` such that every
`C²` Floer trajectory `u` with `1`-periodic loops in `K` and uniformly tame almost complex
structures which is not stationary, that is, `u(s, t) ≠ u(0, t)` for some `s` and `t`, has energy
at least `δ`. -/
theorem exists_pos_forall_ofReal_le_lintegral_floerEnergyDensity
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
    (hfin : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}).Finite) :
    ∃ δ > 0, ∀ {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ},
      ContDiff ℝ 2 u → (∀ s, Periodic (fun t ↦ u (s, t)) 1) → (∀ s t, u (s, t) ∈ K) → 0 < c →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∃ s t, u (s, t) ≠ u (0, t)) →
      ENNReal.ofReal δ ≤ ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  set O := {x : ℝ → V | Periodic x 1 ∧
    (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}
  set A : (ℝ → V) → ℝ := ω.hamiltonianAction H
  -- The positive differences of the finitely many actions of orbits in `K`, and `1`, form a
  -- finite nonempty set of positive numbers; `δ` is its least element.
  set D : Set ℝ := (fun p : ℝ × ℝ ↦ p.2 - p.1) '' (((A '' O) ×ˢ (A '' O)) ∩ {p | p.1 < p.2}) ∪ {1}
  have hD : D.Finite := (((hfin.prod hfin).subset inter_subset_left).image _).union
    (finite_singleton 1)
  obtain ⟨δ, hδD, hδ⟩ := hD.toFinset.exists_min_image id ⟨1, by simp [D]⟩
  simp only [Finite.mem_toFinset, id] at hδD hδ
  refine ⟨δ, ?_, fun {u J c M} hu hper huK hc hJc hJM hfloer hns ↦ ?_⟩
  · rcases hδD with ⟨p, hp, rfl⟩ | rfl
    · exact sub_pos.2 hp.2
    · exact one_pos
  by_cases hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = ⊤
  · simp [hE]
  obtain ⟨x₀, x₁, hx₀, hx₁, -, -, hEeq⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq hH hHper hu hper hK huK hc hJc hJM
      hfloer hE
  -- A trajectory whose ends have the same action has zero energy, so it is stationary.
  have hlt : A x₀ < A x₁ := by
    by_contra! hle
    obtain ⟨s, t, hst⟩ := hns
    have hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
      (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
    have hstat := (ω.lintegral_floerEnergyDensity_eq_zero_iff hH isOpen_univ
      (hu.of_le one_le_two).contDiffOn (subset_univ _) hJ hfloer).1
      (hEeq.trans (ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hle)))
    -- By periodicity it suffices to compare the loops at `t - ⌊t⌋ ∈ [0, 1)`.
    have hmem : t - ⌊t⌋ * 1 ∈ Icc (0 : ℝ) 1 := by
      rw [mul_one, Int.self_sub_floor]
      exact ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    refine hst ?_
    calc u (s, t) = u (s, t - ⌊t⌋ * 1) := ((hper s).sub_int_mul_eq ⌊t⌋).symm
      _ = u (0, t - ⌊t⌋ * 1) := hstat s _ hmem
      _ = u (0, t) := (hper 0).sub_int_mul_eq ⌊t⌋
  rw [hEeq]
  exact ENNReal.ofReal_le_ofReal
    (hδ _ (Or.inl ⟨(A x₀, A x₁), ⟨⟨mem_image_of_mem A hx₀, mem_image_of_mem A hx₁⟩, hlt⟩, rfl⟩))

end TauCeti.SymplecticForm
