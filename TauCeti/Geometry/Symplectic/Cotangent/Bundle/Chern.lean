/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern
public import TauCeti.Topology.VectorBundle.Smul

/-!
# The first Chern number of a cotangent bundle vanishes on spheres and tori

Let `T*M = TauCeti.CotangentBundle I M` be the cotangent bundle of a manifold with a
finite-dimensional model, with its canonical symplectic form `ω = -dλ`
(`TauCeti.CotangentBundle.symplecticForm`). This file proves that the first Chern number of `ω`
vanishes on every sphere: `c₁ : π₂(T*M, p) → ℤ` is zero at every point `p`
(`TauCeti.CotangentBundle.firstChernHom_symplecticForm_eq_zero`). Together with the exactness of
`ω`, which makes the symplectic area of every sphere vanish, this is the symplectic asphericity of
cotangent bundles that Hamiltonian Floer theory on `T*M` assumes.

The proof uses the fibre negation `ν(q, p) = (q, -p)`, the fibre dilation by `-1`
(`TauCeti.vectorBundleScalarDiffeomorph`).

* It is anti-symplectic, `ν^* ω = -ω` (`TauCeti.CotangentBundle.mpullback_fiberNeg_symplecticForm`),
  so it reverses the first Chern number
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_map_of_mpullback_eq_neg`).
* It is homotopic to the identity through the fibre dilations by `1 - 2t`, `t ∈ [0, 1]`
  (`TauCeti.CotangentBundle.fiberNegHomotopy`), so it preserves the first Chern number.

So the first Chern number of every sphere is its own negative
(`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_zero_of_mpullback_eq_neg`). Classically
the same vanishing is read off the zero section, along which `T(T*M)` is the complexification
`TM ⊗ ℂ` of `TM`, a bundle isomorphic to its own conjugate.

The same argument applies to maps of the torus, read as maps of the square agreeing on opposite
edges: for every almost complex structure `J` tamed by `ω`, the clutching number of
`(T(T*M), J)` (`TauCeti.torusClutchingNumber`) vanishes on every map of the torus
(`TauCeti.CotangentBundle.torusClutchingNumber_symplecticForm_eq_zero`). Together with the exactness
of `ω`, which makes the symplectic area of every torus vanish, this is the symplectic atoroidality
of cotangent bundles, under which Hamiltonian Floer theory on `T*M` is graded on every free
homotopy class of loops.

The first Chern number on spheres is defined on Hausdorff σ-compact manifolds, so the base is
assumed Hausdorff and σ-compact there; then so is `T*M`
(`TauCeti.CotangentBundle.sigmaCompactSpace`), and the model of the base is finite-dimensional. The
base may have boundary or corners.

## Main results

* `TauCeti.CotangentBundle.mpullback_fiberNeg_symplecticForm`: the fibre negation is
  anti-symplectic.
* `TauCeti.CotangentBundle.fiberNegHomotopy`: the fibre negation is homotopic to the identity.
* `TauCeti.CotangentBundle.firstChernHom_symplecticForm_eq_zero`: the first Chern number of the
  canonical symplectic form vanishes on `π₂(T*M, p)`.
* `TauCeti.CotangentBundle.torusClutchingNumber_symplecticForm_eq_zero`: the first Chern number of
  `(T(T*M), J)`, for `J` tamed by the canonical symplectic form, vanishes on every map of the
  torus.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of the Floer
  homology of `T*Q`, which uses `2 c₁(T(T*Q)) = 0`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (the first Chern class of a symplectic manifold).
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- The fibre negation `(q, p) ↦ (q, -p)` of the cotangent bundle, the fibre dilation by `-1`. -/
def fiberNeg : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
    CotangentBundle I M :=
  vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (fun _ ↦ (-1 : ℝ)) (contMDiff_const (n := ∞))
    fun _ ↦ neg_ne_zero.2 one_ne_zero

@[simp]
theorem fiberNeg_apply (p : CotangentBundle I M) : fiberNeg I M p = ⟨p.proj, -p.snd⟩ := by
  simp [fiberNeg]

/-- The fibre negation is an involution. -/
@[simp]
theorem fiberNeg_symm : (fiberNeg I M).symm = fiberNeg I M :=
  Diffeomorph.ext fun p ↦ by simp [fiberNeg, vectorBundleScalarDiffeomorph_symm]

/-- **The fibre negation is anti-symplectic**: it pulls the canonical symplectic form back to its
negative, `ν^* ω = -ω`. -/
theorem mpullback_fiberNeg_symplecticForm :
    SmoothForm.mpullback _ (fiberNeg I M).contMDiff (symplecticForm I M) = -symplecticForm I M := by
  rw [fiberNeg, mpullback_vectorBundleScalarDiffeomorph_symplecticForm (neg_ne_zero.2 one_ne_zero)]
  ext x v
  simp

variable (I M) in
/-- **The fibre negation is homotopic to the identity**, through the fibre dilations
`(q, p) ↦ (q, (1 - 2t) p)`, `t ∈ [0, 1]`. -/
def fiberNegHomotopy :
    (ContinuousMap.id (CotangentBundle I M)).Homotopy
      ⟨fiberNeg I M, (fiberNeg I M).continuous⟩ where
  toFun q := ⟨q.2.proj, (1 - 2 * (q.1 : ℝ)) • q.2.snd⟩
  continuous_toFun :=
    (continuous_const.sub (continuous_const.mul
      (continuous_subtypeVal.comp continuous_fst))).smul_totalSpace continuous_snd
  map_zero_left p := by simp
  map_one_left p := by
    rw [ContinuousMap.coe_mk, fiberNeg_apply]
    norm_num

@[simp]
theorem fiberNegHomotopy_apply (t : unitInterval) (p : CotangentBundle I M) :
    fiberNegHomotopy I M (t, p) = ⟨p.proj, (1 - 2 * (t : ℝ)) • p.snd⟩ :=
  (rfl)

variable [FiniteDimensional ℝ E]

/-- **The first Chern number of a cotangent bundle vanishes on tori.** For every almost complex
structure `J` on `T*M` tamed by the canonical symplectic form `ω`, regarded at any smoothness level
`n` and with any complex model fibre `G`, the clutching number of `(T(T*M), J)` vanishes on every
map `u` of the torus, read as a map of the square agreeing on opposite edges. -/
theorem torusClutchingNumber_symplecticForm_eq_zero (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) = 2 * Module.finrank ℂ G)]
    {J : SmoothAlmostComplexStructure (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M)}
    (hJ : (symplecticForm I M).Tames J) (n : ℕ∞)
    (u : C(Fin 2 → unitInterval, CotangentBundle I M)) (hR : ∀ t, u ![1, t] = u ![0, t])
    (hT : ∀ s, u ![s, 1] = u ![s, 0]) :
    torusClutchingNumber G (J.toContMDiff n).toContinuousComplexStructure.Fiber u = 0 :=
  hJ.torusClutchingNumber_eq_zero_of_mpullback_eq_neg G n (fiberNeg I M)
    mpullback_fiberNeg_symplecticForm (fiberNegHomotopy I M) u hR hT

variable [T2Space M] [SigmaCompactSpace M]

/-- **The first Chern number of a cotangent bundle vanishes on spheres.** For the canonical
symplectic form `ω` of `T*M`, the first Chern number `c₁ : π₂(T*M, p) → ℤ` is zero at every point
`p`. -/
theorem firstChernHom_symplecticForm_eq_zero (p : CotangentBundle I M) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.firstChernHom p = 0 :=
  SmoothTwoForm.IsNondegenerate.firstChernHom_eq_zero_of_mpullback_eq_neg _ (fiberNeg I M)
    mpullback_fiberNeg_symplecticForm (fiberNegHomotopy I M) p

end TauCeti.CotangentBundle
