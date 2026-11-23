/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.PointTopology.Localization

/-!
# Examples of the point topology on points of an affine algebra

Checks for the point topology on `A →ₐ[k] R`:

* without finite type, points over a discrete ring need not be discrete: the `𝔽₂`-points of a
  polynomial ring in countably many variables form the product space `𝔽₂^ℕ`;
* the hyperbola topology on `G_m(ℚ_p)`, the points of `ℤ[t, t⁻¹]`, is the subspace topology from
  `ℚ_p`, because inversion is continuous on `ℚ_pˣ`;
* over `ℝ` the points of `G_m` form `ℝˣ`, which is not totally disconnected, so the local-field
  hypothesis of total disconnectedness cannot be dropped;
* the quotient `k[t] → k`, `t ↦ 0`, induces the closed inclusion of the origin in a T1 ring;
* the points of `k[x] ⊗ k[y]` are the pairs of coordinate values;
* the coefficient inclusion `ℝ → ℂ` maps real points of the affine line continuously to complex
  points.
-/

open Polynomial Topology TensorProduct
open scoped TauCeti.PointTopology

namespace TauCeti.PointTopology

/-- The `𝔽₂`-points of a polynomial ring in countably many variables are the product space
`𝔽₂^ℕ`. -/
noncomputable example : (MvPolynomial ℕ (ZMod 2) →ₐ[ZMod 2] ZMod 2) ≃ₜ (ℕ → ZMod 2) :=
  mvPolynomialHomeomorph (ZMod 2) (ZMod 2) ℕ

/-- These points are not discrete, although `𝔽₂` is. -/
example : ¬DiscreteTopology (MvPolynomial ℕ (ZMod 2) →ₐ[ZMod 2] ZMod 2) :=
  have : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
  not_discreteTopology_mvPolynomial ℕ

/-- For comparison, the points of a finite type algebra over a discrete ring are discrete. -/
example : DiscreteTopology (MvPolynomial (Fin 3) (ZMod 2) →ₐ[ZMod 2] ZMod 2) :=
  discreteTopology_of_finiteType

/-- On `G_m(ℚ_p)`, the points of the localization `ℤ[t, t⁻¹]` of `ℤ[t]` away from `t`, the value
at `t` is an embedding into `ℚ_p`: the hyperbola topology is the subspace topology. -/
example (p : ℕ) [Fact p.Prime] :
    IsEmbedding fun x : Localization.Away (X : ℤ[X]) →ₐ[ℤ] ℚ_[p] ↦ x (algebraMap ℤ[X] _ X) := by
  have h := (polynomialHomeomorph ℤ ℚ_[p]).isEmbedding.comp
    (isEmbedding_localization (k := ℤ) (B := Localization.Away (X : ℤ[X])) (R := ℚ_[p]) X
      Units.isEmbedding_val₀)
  convert h using 1
  funext x
  simp

/-- The real points of `G_m` are not totally disconnected: they are `ℝˣ`, which contains the
connected half-line of positive reals. -/
example : ¬TotallyDisconnectedSpace (Localization.Away (X : ℝ[X]) →ₐ[ℝ] ℝ) := by
  intro _
  let e := localizationAwayXHomeomorph ℝ (Localization.Away (X : ℝ[X])) ℝ
  let u : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  have hu : Continuous u := Units.continuous_iff.2
    ⟨Real.continuous_exp, by
      simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact Real.continuous_exp.inv₀ fun t ↦ (Real.exp_pos t).ne'⟩
  have h01 := (isPreconnected_range (e.symm.continuous.comp hu)).subsingleton ⟨0, rfl⟩ ⟨1, rfl⟩
  have := congrArg Units.val (e.symm.injective h01)
  simp only [u, Units.val_mk0, Real.exp_zero] at this
  exact one_ne_zero (Real.exp_eq_one_iff 1 |>.1 this.symm)

/-- The quotient `k[t] → k`, `t ↦ 0`, induces a closed embedding of points over a T1 ring. -/
example {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [TopologicalSpace R]
    [IsTopologicalRing R] [T1Space R] :
    IsClosedEmbedding fun x : k →ₐ[k] R ↦ polynomialHomeomorph k R (x.comp (aeval 0)) :=
  (polynomialHomeomorph k R).isClosedEmbedding.comp
    (isClosedEmbedding_comap_of_surjective _ fun c ↦ ⟨C c, by simp⟩)

/-- Its image is the origin of `R`. -/
example {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    Set.range (fun x : k →ₐ[k] R ↦ polynomialHomeomorph k R (x.comp (aeval 0))) = {0} := by
  ext r
  simp only [polynomialHomeomorph_apply, AlgHom.comp_apply, aeval_X, map_zero, Set.mem_range,
    exists_const_iff, Set.mem_singleton_iff, eq_comm (a := (0 : R))]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨Algebra.ofId k R⟩, h⟩⟩

/-- The points of the affine plane `k[x] ⊗ k[y]` are the pairs of coordinate values. -/
example {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    IsHomeomorph fun x : k[X] ⊗[k] k[X] →ₐ[k] R ↦ (x (X ⊗ₜ 1), x (1 ⊗ₜ X)) := by
  convert ((tensorProductHomeomorph k k[X] k[X] R).trans
    ((polynomialHomeomorph k R).prodCongr (polynomialHomeomorph k R))).isHomeomorph using 1
  funext x
  ext <;> simp [polynomialHomeomorph_apply, tensorProductHomeomorph_apply_fst,
    tensorProductHomeomorph_apply_snd]

/-- The coefficient inclusion `ℝ → ℂ` maps the real points of the affine line continuously to its
complex points. -/
example : Continuous fun x : ℝ[X] →ₐ[ℝ] ℝ ↦ (Algebra.ofId ℝ ℂ).comp x :=
  continuous_map_codomain _ Complex.continuous_ofReal

end TauCeti.PointTopology
