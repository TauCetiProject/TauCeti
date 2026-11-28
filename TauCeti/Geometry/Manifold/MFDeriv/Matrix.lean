/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Matrix
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Maps whose differentials are integer multiples of those of a local diffeomorphism

Let `M` be a boundaryless manifold modelled on a finite-dimensional real space, and let
`a : M → ℝ^ι` be a `C¹` map all of whose differentials are bijective, so that `a` is a local
diffeomorphism. Let `f : M → ℝ^ι` be a `C¹` map whose differential at each point `x` is
`N_x ∘ da_x` for an integer matrix `N_x`. If `M` is preconnected, then `N_x` does not depend on
`x` and `f = N a + b` for a constant integer matrix `N` and a constant vector `b`
(`TauCeti.exists_eq_mulVec_add_of_forall_exists_mfderiv_eq`). In particular `f` is constant on
the fibres of `a`.

This is the manifold version of `TauCeti.exists_eq_mulVec_add_of_forall_exists_fderiv_eq`, which
is applied on a ball in the domain of a local inverse of `a`. There `f` becomes an integral affine
map, so the matrices `N_x` are locally constant, and so is `f - N a`; preconnectedness of `M`
makes both constant.

The statement describes the indeterminacy of action coordinates of a Lagrangian torus fibration
whose period lattice is spanned by the differentials of a global developing map `a`: any other
functions whose differentials lie in that lattice are integral affine functions of `a`.
-/

public section

open Set Function Filter Matrix
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {ι : Type*} [Fintype ι] {a f : M → ι → ℝ}

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- Read through a local inverse `ψ` of `a`, a map `f` whose differentials are `N_x ∘ da_x` has
derivative `N_(ψ y)` at each point `y` of the domain of `ψ`. -/
private theorem fderiv_comp_localInverse_apply (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 a)
    (hf : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 f) {N : M → Matrix ι ι ℤ}
    (hN : ∀ x v, mfderiv I 𝓘(ℝ, ι → ℝ) f x v = (N x).map (↑) *ᵥ mfderiv I 𝓘(ℝ, ι → ℝ) a x v)
    {x₀ : M} (hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, ι → ℝ) 1 a x₀) {y : ι → ℝ}
    (hy : y ∈ hloc.localInverse.source) (w : ι → ℝ) :
    fderiv ℝ (f ∘ hloc.localInverse) y w = (N (hloc.localInverse y)).map (↑) *ᵥ w := by
  set ψ := hloc.localInverse
  have hψy : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I ψ y :=
    (hloc.contMDiffOn_localInverse.contMDiffAt (ψ.open_source.mem_nhds hy)).mdifferentiableAt
      one_ne_zero
  -- Since `a ∘ ψ` is the identity near `y`, the differential of `a` inverts that of `ψ`.
  have hid : mfderiv I 𝓘(ℝ, ι → ℝ) a (ψ y) (mfderiv 𝓘(ℝ, ι → ℝ) I ψ y w) = w := by
    have h := (eventuallyEq_of_mem (ψ.open_source.mem_nhds hy)
      hloc.localInverse_eqOn_right).mfderiv_eq (I := 𝓘(ℝ, ι → ℝ)) (I' := 𝓘(ℝ, ι → ℝ))
    rw [mfderiv_comp y (ha.mdifferentiableAt one_ne_zero) hψy, mfderiv_id] at h
    exact congrArg (fun L ↦ L w) h
  have hfd : fderiv ℝ (f ∘ ψ) y w = mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (f ∘ ψ) y w := by
    rw [mfderiv_eq_fderiv]
    -- `rfl`: `NormedSpace.fromTangentSpace` is the identity equivalence of `ι → ℝ`.
    rfl
  rw [hfd, mfderiv_comp y (hf.mdifferentiableAt one_ne_zero) hψy]
  exact (hN (ψ y) _).trans (congrArg _ hid)

/-- **The local step.** Near an interior point `x₀`, a map `f` whose differentials are `N_x ∘ da_x`
for integer matrices `N_x` is `N_(x₀) a + b`, and `N_x = N_(x₀)`. -/
private theorem exists_eventually_eq_mulVec_add (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 a)
    (hda : ∀ x, Bijective (mfderiv I 𝓘(ℝ, ι → ℝ) a x)) (hf : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 f)
    {N : M → Matrix ι ι ℤ}
    (hN : ∀ x v, mfderiv I 𝓘(ℝ, ι → ℝ) f x v = (N x).map (↑) *ᵥ mfderiv I 𝓘(ℝ, ι → ℝ) a x v)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ b : ι → ℝ, ∀ᶠ x in 𝓝 x₀, f x = (N x₀).map (↑) *ᵥ a x + b ∧ N x = N x₀ := by
  classical
  -- `a` is a local diffeomorphism at `x₀`, with a local inverse `ψ` defined on a ball `D`.
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (ι → ℝ) :=
    (LinearEquiv.ofBijective (mfderiv I 𝓘(ℝ, ι → ℝ) a x₀).toLinearMap (hda x₀)).finrank_eq
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, ι → ℝ) 1 a x₀ :=
    isLocalDiffeomorphAt_of_injective_mfderiv ha.contMDiffOn isOpen_univ (mem_univ x₀) hx₀ le_rfl
      (hda x₀).1 hdim
  set ψ := hloc.localInverse
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ψ.open_source (a x₀) hloc.localInverse_mem_source
  -- Read in `ψ`, the map `f` has derivative `N (ψ y)` at each point `y` of the ball.
  have hfψ : ContDiffOn ℝ 1 (f ∘ ψ) (Metric.ball (a x₀) r) :=
    (contMDiffOn_iff_contDiffOn.1 (hf.comp_contMDiffOn hloc.contMDiffOn_localInverse)).mono hball
  have hderiv (y : ι → ℝ) (hy : y ∈ Metric.ball (a x₀) r) (w : ι → ℝ) :
      fderiv ℝ (f ∘ ψ) y w = (N (ψ y)).map (↑) *ᵥ w :=
    fderiv_comp_localInverse_apply ha hf hN hloc (hball hy) w
  -- So `f ∘ ψ` is integral affine on the ball, with derivative matrix `N₀`.
  obtain ⟨N₀, b, hb⟩ := exists_eq_mulVec_add_of_forall_exists_fderiv_eq (A := id) (A' := f ∘ ψ)
    Metric.isOpen_ball (convex_ball _ _).isPreconnected contDiffOn_id hfψ
    (fun _ _ ↦ by rw [fderiv_id]; exact injective_id) fun y hy ↦
      ⟨N (ψ y), fun w ↦ by rw [fderiv_id]; exact hderiv y hy w⟩
  have hNy (y : ι → ℝ) (hy : y ∈ Metric.ball (a x₀) r) : N (ψ y) = N₀ := by
    have hd := HasFDerivAt.of_eventuallyEq_mulVec_add (hasFDerivAt_id y)
      (eventually_of_mem (Metric.isOpen_ball.mem_nhds hy) hb)
    refine Matrix.map_injective (Int.cast_injective (α := ℝ)) (Matrix.ext_iff_mulVec.2 fun w ↦ ?_)
    rw [← hderiv y hy, hd.fderiv]
    simp
  have hN₀ : N x₀ = N₀ := by
    have hψx₀ : ψ (a x₀) = x₀ := hloc.localInverse_left_inv hloc.localInverse_mem_target
    rw [← hψx₀]
    exact hNy (a x₀) (Metric.mem_ball_self hr)
  -- Transport back along `a` to the neighbourhood `ψ.target ∩ a⁻¹ (ball)` of `x₀`.
  have hmem : ψ.target ∩ a ⁻¹' Metric.ball (a x₀) r ∈ 𝓝 x₀ :=
    inter_mem (ψ.open_target.mem_nhds hloc.localInverse_mem_target)
      (ha.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  refine ⟨b, mem_of_superset hmem fun x ⟨hxT, hxD⟩ ↦ ?_⟩
  have hψx : ψ (a x) = x := hloc.localInverse_left_inv hxT
  refine ⟨?_, ?_⟩
  · have hbx := hb (a x) hxD
    rw [Function.comp_apply, hψx] at hbx
    rw [hN₀]
    exact hbx
  · rw [hN₀, ← hNy (a x) hxD, hψx]

/-- **Differentials related by integer matrices force an integral affine relation on a
manifold.** Let `a : M → ℝ^ι` be a `C¹` map on a preconnected boundaryless manifold with bijective
differentials, and let `f : M → ℝ^ι` be a `C¹` map whose differential at each point `x` is
`N_x ∘ da_x` for some integer matrix `N_x`. Then `f = N a + b` for a constant integer matrix `N`
and a constant vector `b`. -/
theorem exists_eq_mulVec_add_of_forall_exists_mfderiv_eq [BoundarylessManifold I M]
    [PreconnectedSpace M] (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 a)
    (hda : ∀ x, Bijective (mfderiv I 𝓘(ℝ, ι → ℝ) a x)) (hf : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 f)
    (hpt : ∀ x, ∃ N : Matrix ι ι ℤ, ∀ v,
      mfderiv I 𝓘(ℝ, ι → ℝ) f x v = N.map (↑) *ᵥ mfderiv I 𝓘(ℝ, ι → ℝ) a x v) :
    ∃ (N : Matrix ι ι ℤ) (b : ι → ℝ), ∀ x, f x = N.map (↑) *ᵥ a x + b := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨0, 0, fun x ↦ isEmptyElim x⟩
  choose N hN using hpt
  have hloc (x : M) := exists_eventually_eq_mulVec_add ha hda hf hN
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  -- The matrices `N x` are locally constant, hence all equal to `N x₀`.
  have hNc : IsLocallyConstant N := (IsLocallyConstant.iff_eventually_eq N).2 fun x ↦ by
    obtain ⟨b, hb⟩ := hloc x
    exact hb.mono fun _ h ↦ h.2
  -- So `f - N x₀ a` is locally constant too.
  have hg : IsLocallyConstant fun x ↦ f x - (N x₀).map (↑) *ᵥ a x :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ by
      obtain ⟨b, hb⟩ := hloc x
      have hx := hb.self_of_nhds.1
      rw [hNc.apply_eq_of_preconnectedSpace x x₀] at hb hx
      exact hb.mono fun y hy ↦ by rw [hy.1, hx]; abel
  refine ⟨N x₀, f x₀ - (N x₀).map (↑) *ᵥ a x₀, fun x ↦ ?_⟩
  rw [← hg.apply_eq_of_preconnectedSpace x x₀]
  abel

end TauCeti
