/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Compact hypersurfaces with a unit position differential

A unit vector field with the same differential as a connected immersed hypersurface differs
from its position map by a constant centre. Compactness and the inverse function theorem make
the image the entire unit sphere. If the position map is injective, the unit field gives a
diffeomorphism onto the sphere, including for one-dimensional hypersurfaces.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8.
* [Poincaré formalization](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public noncomputable section

open Function Metric Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E F H S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace S] [ChartedSpace H S] [BoundarylessManifold I S]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- An immersion into the unit sphere is a local diffeomorphism when the source and sphere
have the same finite dimension. Injectivity may be checked after the ambient inclusion. -/
theorem _root_.ContMDiff.isLocalDiffeomorph_sphere_of_injective_mvfderiv
    {k : ℕ∞ω} [IsManifold I k S] {N : S → sphere (0 : E) 1}
    (hN : ContMDiff I (𝓡 n) k N) (hk : 1 ≤ k) (hdim : finrank ℝ F = n)
    (hinj : ∀ x, Injective (mvfderiv I (fun y ↦ (N y : E)) x)) :
    IsLocalDiffeomorph I (𝓡 n) k N := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [(Fact.out : finrank ℝ E = n + 1)]
    omega)
  rcases isEmpty_or_nonempty S with hS | ⟨⟨x₀⟩⟩
  · exact fun x ↦ isEmptyElim x
  have : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective (mvfderiv I (fun y ↦ (N y : E)) x₀).toLinearMap (hinj x₀)
  intro x
  apply isLocalDiffeomorphAt_of_injective_mfderiv hN.contMDiffOn isOpen_univ (mem_univ x)
    BoundarylessManifold.isInteriorPoint hk
  · have hcomp := mfderiv_comp x
      ((contMDiff_coe_sphere (m := k) (N x)).mdifferentiableAt
        (ne_of_gt (zero_lt_one.trans_le hk)))
      ((hN x).mdifferentiableAt (ne_of_gt (zero_lt_one.trans_le hk)))
    exact Injective.of_comp (hcomp ▸ injective_mvfderiv_iff.mp (hinj x))
  · simpa using hdim

/-- A compact nonempty immersed unit map onto a sphere of positive dimension is surjective. -/
theorem _root_.ContMDiff.surjective_codRestrict_sphere [IsManifold I 1 S]
    [CompactSpace S] [Nonempty S] {N : S → E} (hN : ContMDiff I 𝓘(ℝ, E) 1 N)
    (hdim : finrank ℝ F = n) (hn : 0 < n) (hunit : ∀ x, ‖N x‖ = 1)
    (hinj : ∀ x, Injective (mvfderiv I N x)) :
    Surjective (codRestrict N (sphere (0 : E) 1)
      (fun x ↦ mem_sphere_zero_iff_norm.mpr (hunit x))) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [(Fact.out : finrank ℝ E = n + 1)]
    omega)
  have hnat : 1 < n + 1 := by omega
  have hrank : 1 < Module.rank ℝ E := by
    rw [← finrank_eq_rank, (Fact.out : finrank ℝ E = n + 1)]
    exact_mod_cast hnat
  have : ConnectedSpace (sphere (0 : E) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  let N' := codRestrict N (sphere (0 : E) 1) (fun x ↦ mem_sphere_zero_iff_norm.mpr (hunit x))
  have hN' : ContMDiff I (𝓡 n) 1 N' := hN.codRestrict_sphere _
  have hlocal := hN'.isLocalDiffeomorph_sphere_of_injective_mvfderiv le_rfl hdim hinj
  exact range_eq_univ.mp
    (IsClopen.eq_univ ⟨(isCompact_range hN'.continuous).isClosed, hlocal.isOpen_range⟩
      (range_nonempty N'))

/-- Equal position and unit-field differentials identify a compact connected hypersurface's
image with a sphere about their constant difference. Injectivity of the position map is not
required for this image statement. -/
theorem _root_.ContMDiff.exists_center_range_sphere [IsManifold I 1 S]
    [CompactSpace S] [ConnectedSpace S] {f N : S → E}
    (hN : ContMDiff I 𝓘(ℝ, E) 1 N)
    (hdim : finrank ℝ F = n) (hn : 0 < n)
    (himm : ∀ x, Injective (mvfderiv I f x))
    (hunit : ∀ x, ‖N x‖ = 1)
    (hderiv : ∀ x, mvfderiv I N x = mvfderiv I f x) :
    ∃ c : E, (∀ x, f x - N x = c) ∧ range f = sphere c 1 := by
  have hf : MDifferentiable I 𝓘(ℝ, E) f := fun x ↦
    mdifferentiableAt_of_mfderiv_injective (injective_mvfderiv_iff.mp (himm x))
  have hconst := (hf.sub (hN.mdifferentiable one_ne_zero)).isLocallyConstant_of_mfderiv_eq_zero
    (fun x ↦ by
      apply mvfderiv_eq_zero_iff.mp
      rw [mvfderiv_sub (hf x) (hN.mdifferentiable one_ne_zero x), hderiv x, sub_self])
  obtain ⟨c, hc⟩ := hconst.exists_eq_const
  have hcenter (x : S) : f x - N x = c := congrFun hc x
  have hsurj := hN.surjective_codRestrict_sphere hdim hn hunit
    (fun x ↦ hderiv x ▸ himm x)
  refine ⟨c, hcenter, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [mem_sphere, dist_eq_norm, ← hcenter x, sub_sub_cancel, hunit x]
  · intro y hy
    have hmem : y - c ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere, dist_eq_norm, sub_zero] using hy
    obtain ⟨x, hx⟩ := hsurj ⟨y - c, hmem⟩
    have hx' : N x = y - c := congrArg Subtype.val hx
    refine ⟨x, ?_⟩
    rw [sub_eq_iff_eq_add.mp (hcenter x), hx']
    abel

/-- For an injective compact hypersurface, a `C^k` unit field with the position differential
is the sphere diffeomorphism. Injectivity rules out multiple coverings of the circle. -/
theorem _root_.ContMDiff.exists_diffeomorph_sphere {k : ℕ∞ω} [IsManifold I k S]
    [CompactSpace S] [ConnectedSpace S] {f N : S → E}
    (hN : ContMDiff I 𝓘(ℝ, E) k N) (hk : 1 ≤ k)
    (hdim : finrank ℝ F = n) (hn : 0 < n)
    (himm : ∀ x, Injective (mvfderiv I f x))
    (hunit : ∀ x, ‖N x‖ = 1)
    (hderiv : ∀ x, mvfderiv I N x = mvfderiv I f x)
    (hinj : Injective f) :
    ∃ e : S ≃ₘ^k⟮I, 𝓡 n⟯ sphere (0 : E) 1, ∀ x, (e x : E) = N x := by
  have : IsManifold I 1 S := IsManifold.of_le hk
  obtain ⟨c, hc, _⟩ := (hN.of_le hk).exists_center_range_sphere hdim hn himm hunit hderiv
  let N' := codRestrict N (sphere (0 : E) 1) (fun x ↦ mem_sphere_zero_iff_norm.mpr (hunit x))
  have hN' : ContMDiff I (𝓡 n) k N' := hN.codRestrict_sphere _
  have hlocal := hN'.isLocalDiffeomorph_sphere_of_injective_mvfderiv hk hdim
    (fun x ↦ hderiv x ▸ himm x)
  have hNi : Injective N' := by
    intro x y hxy
    apply hinj
    have hNxy : N x = N y := congrArg Subtype.val hxy
    rw [sub_eq_iff_eq_add.mp (hc x), sub_eq_iff_eq_add.mp (hc y), hNxy]
  have hNs : Surjective N' := (hN.of_le hk).surjective_codRestrict_sphere hdim hn hunit
    (fun x ↦ hderiv x ▸ himm x)
  refine ⟨hlocal.diffeomorphOfBijective ⟨hNi, hNs⟩, ?_⟩
  intro x
  exact congrArg Subtype.val
    (congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective hlocal ⟨hNi, hNs⟩) x)

end TauCeti
