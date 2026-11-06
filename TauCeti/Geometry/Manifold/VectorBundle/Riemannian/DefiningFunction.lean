/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.DefiningFunction
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Sphere

/-!
# Defining functions for closed disc images

Suppose smooth coordinates map a neighbourhood of closed fibre discs in a Riemannian vector
bundle into a manifold, with closed disc image closed in the ambient manifold. There is a global
smooth regular defining function whose negative, zero, and nonpositive loci are precisely the
open disc, sphere, and closed disc images. On the closed disc image its germ is the squared fibre
norm minus squared radius, read through the inverse coordinates. This turns a domain in bundle
coordinates into an ambient regular domain, as needed for exteriors of tubular neighbourhoods.

The construction uses `sphereBundleEquation` and
`PartialDiffeomorph.exists_contMDiffMap_regular_definingFunction`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 5.47
  (regular domains) and Theorem 6.24 (tubular neighbourhoods).
-/

public noncomputable section

open Bundle Set Function Topology
open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {B F E H X W G : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I ∞ F V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace G] {J : ModelWithCorners ℝ W G}
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]
  [T2Space X] [NormalSpace X] [SigmaCompactSpace X]

/-- Closed disc images in smooth bundle coordinates admit a global regular defining function.
The three sign loci are exactly the closed disc, open disc, and sphere images, respectively.
The function agrees near the closed disc image with the squared norm minus squared radius,
read through the inverse coordinates. -/
theorem exists_contMDiffMap_regular_definingFunction_norm_le
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, F)) J (TotalSpace F V) X ∞)
    {r : B → ℝ} (hr : ContMDiff I 𝓘(ℝ) ∞ r) (hrpos : ∀ b, 0 < r b)
    (hsource : {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} ⊆ Φ.source)
    (hclosed : IsClosed (Φ '' {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj})) :
    ∃ g : C^∞⟮J, X; 𝓘(ℝ), ℝ⟯, TauCeti.IsRegularValue J 𝓘(ℝ) g 0 ∧
      (∀ p : TotalSpace F V, ‖p.2‖ ≤ r p.proj →
        (g : X → ℝ) =ᶠ[𝓝 (Φ p)] TauCeti.sphereBundleEquation r ∘ Φ.symm) ∧
      {y | g y ≤ 0} = Φ '' {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} ∧
      {y | g y < 0} = Φ '' {p : TotalSpace F V | ‖p.2‖ < r p.proj} ∧
      {y | g y = 0} = Φ '' {p : TotalSpace F V | ‖p.2‖ = r p.proj} := by
  have hle : {p : TotalSpace F V | TauCeti.sphereBundleEquation r p ≤ 0} =
      {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} := by
    ext p
    simp only [TauCeti.sphereBundleEquation_apply, mem_ofPred_eq, sub_nonpos]
    exact sq_le_sq₀ (norm_nonneg _) (hrpos p.proj).le
  have hlt : {p : TotalSpace F V | TauCeti.sphereBundleEquation r p < 0} =
      {p : TotalSpace F V | ‖p.2‖ < r p.proj} := by
    ext p
    simp only [TauCeti.sphereBundleEquation_apply, mem_ofPred_eq, sub_neg]
    exact sq_lt_sq₀ (norm_nonneg _) (hrpos p.proj).le
  have heq : {p : TotalSpace F V | TauCeti.sphereBundleEquation r p = 0} =
      {p : TotalSpace F V | ‖p.2‖ = r p.proj} := by
    ext p
    exact TauCeti.sphereBundleEquation_eq_zero_iff r p (hrpos p.proj).le
  have hreg := TauCeti.isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le (by simp)) (fun b => (hrpos b).ne')
  obtain ⟨g, hg, hgerm, hgle, hglt, hgeq⟩ :=
    Φ.exists_contMDiffMap_regular_definingFunction
      (TauCeti.contMDiff_sphereBundleEquation hr).contMDiffOn (hle ▸ hsource)
      (hle ▸ hclosed) (TauCeti.isRegularValue_iff.mp hreg)
  refine ⟨g, hg, ?_, hle ▸ hgle, hlt ▸ hglt, heq ▸ hgeq⟩
  intro p hp
  exact hgerm p ((Set.ext_iff.mp hle p).mpr hp)

end PartialDiffeomorph

