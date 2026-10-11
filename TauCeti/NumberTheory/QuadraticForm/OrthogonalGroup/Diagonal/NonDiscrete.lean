/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Finite
public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.BaseChange
import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Powers
import TauCeti.Topology.Algebra.QuadraticForm.Transvection
import TauCeti.NumberTheory.Padics.Factorial
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rational transvections accumulate in the finite adeles

For any compatible compact-open reference family, the factorial powers of a rational Eichler
transvection tend to the identity in the finite adelic special orthogonal group. Uniform
integrality is essential: all powers belong to the reference subgroups wherever the original
transvection does. The sequence therefore lies in one principal restricted-product stage,
where coordinatewise convergence implies convergence in the restricted-product topology.

If the transvection parameter is nonzero modulo the isotropic line and that line is not in the
radical, none of these factorial powers is the identity. Consequently the rational diagonal
in finite adelic `SO` is not discrete. This contrasts with the full adeles, where the real
component prevents this sequence from converging to the identity.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen* (1952).
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap Filter Topology
open scoped TensorProduct RestrictedProduct

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) {u w : V}

/-- Factorial powers of a rational Eichler transvection tend to the identity in finite adelic
`SO`, for every compatible compact-open reference family. -/
theorem tendsto_finiteAdelicSpecialOrthogonalDiagonal_transvection_factorial
    (hu : Q u = 0) (huw : polar Q u w = 0) :
    Tendsto (fun n : ℕ ↦ U.finiteAdelicSpecialOrthogonalDiagonal
      (⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩ ^ n.factorial))
      atTop (𝓝 1) := by
  let g : specialOrthogonalGroup Q :=
    ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩
  let φ (p : Nat.Primes) := specialOrthogonalGroupBaseChange (A := ℚ_[p]) Q
  -- All powers are integral on the same cofinite set, so use one principal stage.
  let S : Set Nat.Primes := {p | φ p g ∈ U.specialOrthogonal p}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr (U.eventually_specialOrthogonal g)
  let f (n : ℕ) : Πʳ (p : Nat.Primes), [specialOrthogonalGroup (Q.baseChange ℚ_[p]),
      (U.specialOrthogonal p : Set _)]_[𝓟 S] :=
    ⟨fun p ↦ φ p (g ^ n.factorial), eventually_principal.mpr fun p hp ↦ by
      -- Expose the beta-reduced coordinate and reference subgroup of the principal stage.
      change φ p (g ^ n.factorial) ∈ U.specialOrthogonal p
      rw [map_pow]
      exact (U.specialOrthogonal p).pow_mem hp _⟩
  -- At each prime, the powers are a continuous transvection family with parameter `n! → 0`.
  have hlocal (p : Nat.Primes) : Tendsto (fun n : ℕ ↦ φ p (g ^ n.factorial))
      atTop (𝓝 1) := by
    let : TopologicalSpace (ℚ_[p] ⊗[ℚ] V) := moduleTopology ℚ_[p] _
    let up : ℚ_[p] ⊗[ℚ] V := 1 ⊗ₜ[ℚ] u
    let wp : ℚ_[p] ⊗[ℚ] V := 1 ⊗ₜ[ℚ] w
    have hup : (Q.baseChange ℚ_[p]) up = 0 := by
      simp [up, QuadraticForm.baseChange_tmul, hu]
    have huwp : polar (Q.baseChange ℚ_[p]) up wp = 0 := by
      simp [up, wp, QuadraticForm.polar_baseChange_tmul, huw]
    let E (t : ℚ_[p]) : specialOrthogonalGroup (Q.baseChange ℚ_[p]) :=
      ⟨transvection (Q.baseChange ℚ_[p]) (w := t • wp) hup
          (by simp [polar_smul_right, huwp]),
        transvection_mem_specialOrthogonalGroup _ _⟩
    have hE : Continuous E :=
      (continuous_transvection (fun _ : ℚ_[p] ↦ up) (fun t ↦ t • wp)
        (fun _ ↦ hup) (fun t ↦ by simp [polar_smul_right, huwp])
        continuous_const
        ((continuous_id : Continuous (fun t : ℚ_[p] ↦ t)).smul
          (continuous_const : Continuous (fun _ : ℚ_[p] ↦ wp)))).subtype_mk _
    have hEn (n : ℕ) : E (n : ℚ_[p]) = (φ p g) ^ n := by
      apply Subtype.ext
      simpa only [E, Nat.cast_smul_eq_nsmul, g, φ, up, wp,
        specialOrthogonalGroupBaseChange_transvection, Subgroup.coe_pow] using
        (transvection_pow hup huwp n).symm
    have hzero : E 0 = 1 := by
      apply Subtype.ext
      simp [E]
    have ht := hE.continuousAt.tendsto.comp (tendsto_padic_natCast_factorial (p : ℕ))
    rw [hzero] at ht
    apply ht.congr
    intro n
    exact (hEn n.factorial).trans (map_pow (φ p) g n.factorial).symm
  have hf : Tendsto f atTop (𝓝 1) := by
    apply RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff.mpr
    exact tendsto_pi_nhds.mpr hlocal
  have hi := (RestrictedProduct.continuous_inclusion hS).continuousAt.tendsto.comp hf
  have hfactor : (fun n ↦ U.finiteAdelicSpecialOrthogonalDiagonal (g ^ n.factorial)) =
      RestrictedProduct.inclusion _ _ hS ∘ f := by
    funext n
    ext p : 1
    exact (U.finiteAdelicSpecialOrthogonalDiagonal_apply _ p).trans
      (RestrictedProduct.inclusion_apply _ _ hS (x := f n) p).symm
  have hone : RestrictedProduct.inclusion _ _ hS (1 : _) =
      (1 : U.finiteAdelicSpecialOrthogonal) := by
    ext p : 1
    exact RestrictedProduct.inclusion_apply _ _ hS (x := 1) p
  rw [hone] at hi
  exact hfactor.symm ▸ hi

/-- A nontrivial rational Eichler root subgroup prevents the rational diagonal in finite adelic
`SO` from being discrete. The hypotheses ensure that the parameter is nonzero modulo `ℚ ∙ u`. -/
theorem not_discreteTopology_range_finiteAdelicSpecialOrthogonalDiagonal_of_transvection
    (hu : Q u = 0) (huw : polar Q u w = 0) (hu₀ : Q.polarBilin u ≠ 0)
    (hw : w ∉ ℚ ∙ u) : ¬ DiscreteTopology U.finiteAdelicSpecialOrthogonalDiagonal.range := by
  intro hD
  let : DiscreteTopology U.finiteAdelicSpecialOrthogonalDiagonal.range := hD
  let g : specialOrthogonalGroup Q :=
    ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩
  have hne (n : ℕ) : g ^ n.factorial ≠ 1 := by
    intro hn
    have he := congrArg (fun x : specialOrthogonalGroup Q ↦ (x : V ≃ₗ[ℚ] V)) hn
    simp only [Subgroup.coe_pow, g, OneMemClass.coe_one, transvection_pow] at he
    have hmem := (transvection_eq_one_iff hu
      (by simp [← Nat.cast_smul_eq_nsmul ℚ, polar_smul_right, huw]) hu₀).mp he
    rw [← Nat.cast_smul_eq_nsmul ℚ, (ℚ ∙ u).smul_mem_iff
      (by exact_mod_cast n.factorial_ne_zero)] at hmem
    exact hw hmem
  let s (n : ℕ) : U.finiteAdelicSpecialOrthogonalDiagonal.range :=
    U.finiteAdelicSpecialOrthogonalDiagonal.rangeRestrict (g ^ n.factorial)
  have hs : Tendsto s atTop (𝓝 1) :=
    tendsto_subtype_rng.mpr (U.tendsto_finiteAdelicSpecialOrthogonalDiagonal_transvection_factorial
      hu huw)
  have hev : ∀ᶠ n in atTop, s n = 1 := by
    simpa only [nhds_discrete, tendsto_pure] using hs
  obtain ⟨n, hn⟩ := hev.exists
  apply hne n
  apply U.finiteAdelicSpecialOrthogonalDiagonal_injective
  simpa only [s, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, map_one] using
    congrArg Subtype.val hn

/-- For a nondegenerate isotropic rational quadratic space of dimension at least three, the
rational diagonal is not discrete in finite adelic `SO`. In dimension two the transvection
parameter quotient is zero, so the dimension hypothesis is essential to this argument. -/
theorem not_discreteTopology_range_finiteAdelicSpecialOrthogonalDiagonal
    (hQ : Q.Nondegenerate) (hdim : 3 ≤ Module.finrank ℚ V)
    (hiso : ∃ u : V, u ≠ 0 ∧ Q u = 0) :
    ¬ DiscreteTopology U.finiteAdelicSpecialOrthogonalDiagonal.range := by
  obtain ⟨u, hu₀, hu⟩ := hiso
  have hpolar := hQ.polarBilin_ne_zero hu₀
  have hdimker := Module.Dual.finrank_ker_add_one_of_ne_zero hpolar
  have hex : ∃ w ∈ LinearMap.ker (Q.polarBilin u), w ∉ ℚ ∙ u := by
    by_contra! h
    have hle : LinearMap.ker (Q.polarBilin u) ≤ ℚ ∙ u := h
    have hbound := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu₀] at hbound
    omega
  obtain ⟨w, huw, hw⟩ := hex
  exact U.not_discreteTopology_range_finiteAdelicSpecialOrthogonalDiagonal_of_transvection
    hu (by simpa only [LinearMap.mem_ker, polarBilin_apply_apply] using huw) hpolar hw

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
