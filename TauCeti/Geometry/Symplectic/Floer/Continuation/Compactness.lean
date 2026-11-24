/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.Continuation

/-!
# Compactness of continuation cylinders and Floer cylinders

Continuation maps between Floer complexes count *continuation cylinders*: maps
`u : ℝ × ℝ → V`, of period one in `t`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_{(s, t)}}(u)) = 0` for the continuation homotopy
`H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))` (`TauCeti.Floer.continuationHomotopy`) from `H₀` to
`H₁`. The Floer differential counts *Floer cylinders*, the solutions for the cylindrical
perturbation `H_t dt`, which is the continuation homotopy from `H` to itself
(`TauCeti.Floer.continuationHomotopy_self`). This file proves the interior part of Gromov–Floer
compactness for both kinds of cylinders, for a symplectic vector space target `(V, ω)`.

The input is the energy bound of continuation cylinders: if `H₀ - H₁ ≤ h` on `[0, 1]`, a solution
whose loop actions converge to `a₀` at the end `s → -∞` and to `a₁` at the end `s → ∞` has energy
at most `a₁ - a₀ + ∫₀¹ h` over the fundamental strip `ℝ × [0, 1]`
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_continuationHomotopy_le`). The energy
density of a cylinder is of period one in `t`
(`TauCeti.SymplecticForm.periodic_floerEnergyDensity`), so the same bound holds over
every strip `ℝ × [c, c + 1]`
(`TauCeti.SymplecticForm.setLIntegral_univ_prod_Icc_floerEnergyDensity_continuationHomotopy_le`).
A compact window `D` of height at most one lies in such a strip, and the compactness theorem for
Floer solutions of bounded energy
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) applies
on it. Every point of the cylinder lies in the interior of such a window, so this covers
the seam `t ∈ ℤ` as well. The two results, in the namespace `TauCeti.SymplecticForm`, are:

* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_continuationHomotopy`: for
  almost complex structures `J(z, x)` tamed by `ω` and `C²` near `D × K`, there is a threshold
  `δ > 0` such that every sequence of `C³` continuation cylinders with `a₁ - a₀ ≤ A` and image of
  an open `Ω ⊆ D` in `K` has a subsequence converging locally uniformly on `Ω` off a finite set `Z`
  of bubbling points, with `#Z * δ ≤ A + ∫₀¹ h`, derivatives bounded on compact subsets of
  `Ω \ Z`, and energy at least `δ` concentrating at each point of `Z`.
* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cylindrical`: the same for
  Floer cylinders, with `#Z * δ ≤ A`.

The action shift `a₀ ≤ a₁ + ∫₀¹ h` of a continuation cylinder
(`TauCeti.SymplecticForm.le_add_integral_of_tendsto_hamiltonianAction_continuationHomotopy`) makes
the bound `A + ∫₀¹ h` nonnegative. The regularity of the limit, the bubbles at the points of `Z`,
and breaking along the two ends are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the compactness of Floer cylinders and continuation
  cylinders.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H₀ H₁ : ℝ → V → ℝ}

/-- **Continuation cylinders with bounded action change converge off finitely many bubbling
points.** Let `H₀` and `H₁` be `C³` Hamiltonians of period one in time with `H₀ - H₁ ≤ h` on
`[0, 1]` for an integrable `h`, and let `J(z, x)` be almost complex structures on `V`, tamed by
`ω` and `C²` on an open set `W ⊇ D × K`, for compact `K ⊆ V` and a compact window `D` of the
strip `ℝ × [c, c + 1]`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
maps of period one in `t` solving the Floer equation for `J(z, u)` and the continuation homotopy
from `H₀` to `H₁`, whose loop actions converge to `a₀ₖ` for `H₀` at `s → -∞` and to `a₁ₖ` for
`H₁` at `s → ∞`, with `a₁ₖ - a₀ₖ ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a
subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + ∫₀¹ h`, and a continuous
`v : Ω \ Z → K` such that along `ψ` every disc about a point of `Z` eventually carries energy at
least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{ψ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_continuationHomotopy
    (ω : SymplecticForm V) (hH₀ : Periodic H₀ 1) (hH₁ : Periodic H₁ 1)
    (hH₀s : ContDiff ℝ 3 (uncurry H₀)) (hH₁s : ContDiff ℝ 3 (uncurry H₁)) {h : ℝ → ℝ}
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t) (hhi : IntegrableOn h (Icc 0 1))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)}
    {K : Set V} {c : ℝ} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ z x, ω.Tames (J z x)) (hD : IsCompact D) (hDc : D ⊆ univ ×ˢ Icc c (c + 1))
    (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a₀ a₁ : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContDiff ℝ 3 (u k)) → (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) (u k) z
          : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction H₀ (fun t ↦ u k (s, t))) atBot (𝓝 (a₀ k))) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction H₁ (fun t ↦ u k (s, t))) atTop (𝓝 (a₁ k))) →
      (∀ k, a₁ k - a₀ k ≤ A) → (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∫ t in Icc 0 1, h t ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω.floerEnergyDensity (fun _ _ ↦ 0) (continuationHomotopy H₀ H₁) (u (ψ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (ψ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (ψ n)) v atTop (Ω \ ↑Z) := by
  set Kt : ℝ × ℝ → V → ℝ := continuationHomotopy H₀ H₁
  have hKt := contDiff_uncurry_continuationHomotopy hH₀s hH₁s
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := Kt) hW contDiffOn_const hKt.contDiffOn hJ hD hK hDKW
    fun z _ x _ ↦ hJt z x
  refine ⟨δ, hδ, fun Ω u a₀ a₁ A hΩ hΩD hu hper hfl ha₀ ha₁ hA huK ↦ ?_⟩
  have hH₀₁ : ContDiff ℝ 1 (uncurry H₀) := hH₀s.of_le (by norm_num)
  have hH₁₁ : ContDiff ℝ 1 (uncurry H₁) := hH₁s.of_le (by norm_num)
  have hu₂ (k : ℕ) : ContDiff ℝ 2 (u k) := (hu k).of_le (by norm_num)
  -- The Floer equation in the form taken by the energy bound of continuation cylinders.
  have hfl' (k : ℕ) (z : ℝ × ℝ) : fderiv ℝ (u k) z stdComplexLineReal +
      J z (u k z) (fderiv ℝ (u k) z stdComplexLineImag -
        ω.hamiltonianVectorField (Kt z) (u k z)) = 0 := by
    simpa using (ω.isComplexLinearMap_perturbedFDeriv_iff _ _ _ _ z).1 (hfl k z)
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) Kt (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt z _) (hfl k z)
  -- The action shift of a continuation cylinder makes the energy bound `A + ∫₀¹ h` nonnegative.
  have hE0 : 0 ≤ A + ∫ t in Icc 0 1, h t := by
    linarith [hA 0, ω.le_add_integral_of_tendsto_hamiltonianAction_continuationHomotopy
      (J := fun z ↦ J z (u 0 z)) (fun z _ ↦ hJt z _) hH₀₁ hH₁₁ isOpen_univ (hu₂ 0).contDiffOn
      (subset_univ _) (fun s ↦ by simpa using hper 0 s 0) (fun z _ ↦ hfl' 0 z) hh hhi (ha₀ 0)
      (ha₁ 0)]
  -- The energy over `Ω` is at most the energy over the strip `ℝ × [c, c + 1]`, at most
  -- `a₁ - a₀ + ∫₀¹ h ≤ A + ∫₀¹ h`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) Kt (u k) z) ≤
      ENNReal.ofReal (A + ∫ t in Icc 0 1, h t) :=
    (lintegral_mono_set (hΩD.trans hDc)).trans <|
      (ω.setLIntegral_univ_prod_Icc_floerEnergyDensity_continuationHomotopy_le
        (J := fun z ↦ J z (u k z)) (fun z _ ↦ hJt z _) hH₀₁ hH₁₁ hH₀ hH₁ (hu₂ k) (hper k)
        (fun z _ ↦ hfl' k z) hh hhi (ha₀ k) (ha₁ k) c).trans
      (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) Kt (u k)) Ω :=
    (((ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) isOpen_univ
      ((hu₂ k).of_le one_le_two).contDiffOn contDiffOn_const
      (hKt.of_le (by norm_num)).contDiffOn).mono (subset_univ D)).integrableOn_compact hD).mono_set
      hΩD
  exact hconv hΩ hΩD (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK hint fun k ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hf0 k)) (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hE0 (hlin k)

/-- **Floer cylinders with bounded action change converge off finitely many bubbling points.**
Let `H` be a `C³` Hamiltonian of period one in time, and let `J(z, x)` be almost complex structures
on `V`, tamed by `ω` and `C²` on an open set `W ⊇ D × K`, for compact `K ⊆ V` and a compact window
`D` of the strip `ℝ × [c, c + 1]`. There is a threshold `δ > 0` with the following property. Let
`uₖ` be `C³` maps of period one in `t` solving the Floer equation
`∂_s u + J(z, u) (∂_t u - X_{H_t}(u)) = 0`, whose loop actions converge to `a₀ₖ` at `s → -∞` and
to `a₁ₖ` at `s → ∞`, with `a₁ₖ - a₀ₖ ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there
are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A`, and a continuous `v : Ω \ Z → K`
such that along `ψ` every disc about a point of `Z` eventually carries energy at least `δ`, the
differentials are uniformly bounded on every compact subset of `Ω \ Z`, and `u_{ψ n} → v` locally
uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cylindrical
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)}
    {K : Set V} {c : ℝ} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ z x, ω.Tames (J z x)) (hD : IsCompact D) (hDc : D ⊆ univ ×ˢ Icc c (c + 1))
    (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a₀ a₁ : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContDiff ℝ 3 (u k)) → (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u k (s, t))) atBot (𝓝 (a₀ k))) →
      (∀ k, Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u k (s, t))) atTop (𝓝 (a₁ k))) →
      (∀ k, a₁ k - a₀ k ≤ A) → (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u (ψ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (ψ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (ψ n)) v atTop (Ω \ ↑Z) := by
  -- The cylindrical perturbation is the continuation homotopy from `H` to itself, with `h = 0`.
  obtain ⟨δ, hδ, hconv⟩ :=
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_continuationHomotopy hH hH
      hHs hHs (h := 0) (fun _ _ _ ↦ by simp) (integrableOn_zero) hW hJ hJt hD hDc hK hDKW
  refine ⟨δ, hδ, fun Ω u a₀ a₁ A hΩ hΩD hu hper hfl ha₀ ha₁ hA huK ↦ ?_⟩
  simpa using hconv hΩ hΩD hu hper (by simpa using hfl) ha₀ ha₁ hA huK

end SymplecticForm

end TauCeti
