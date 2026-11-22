/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Fibration
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Compact
public import TauCeti.Topology.VectorBundle.Lattice

/-!
# The linear monodromy of the period lattice

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
onto a boundaryless Hausdorff manifold `B` of dimension `n`, with period lattices
`Λ_b ⊆ T*_b B` (`IsLagrangianTorusFibration.periodLattice`). The covectors lying in the period
lattices form the **period lattice bundle** `Λ ⊆ T*B`, the domain of `TauCeti.latticeProj` for
the family `b ↦ Λ_b`; its fibrewise quotient `T*B/Λ` is the torus bundle associated with the
fibration.

Near every point of `B` there are action coordinates `a : B → ℝⁿ` with
`Λ_b = 2π (ℤ da₁(b) + ⋯ + ℤ daₙ(b))`
(`IsLagrangianTorusFibration.exists_periodLattice_eq_closure_mvfderiv`).
Their differentials are continuous covector fields, linearly independent because `Λ_b` is a full
lattice. So the period lattice bundle is a covering space of `B`
(`IsLagrangianTorusFibration.isCoveringMap_latticeProj_periodLattice`), by the general
`TauCeti.isCoveringMap_latticeProj`. Lifting paths to this covering transports periods along paths
in `B`: a homotopy class of paths from `x` to `y` gives a group isomorphism `Λ_x ≃+ Λ_y`
(`TauCeti.latticeMonodromy`), and loops at `x` give the **linear monodromy** of the fibration, the
representation `π₁(B, x) → GL(Λ_x) ≅ GL(n, ℤ)` (`TauCeti.latticeMonodromyHom`).

Transport follows differentials of functions which are periods: if `dg_b ∈ Λ_b` for `b` in a set
`U` on which `g` is `C¹`, then transport along a path in `U` carries `dg_x` to `dg_y`
(`IsLagrangianTorusFibration.latticeMonodromy_mk_mvfderiv`). Hence a fibration admitting global
action coordinates, whose period lattice is spanned over `ℤ` at every point by the differentials of
`C¹` functions on all of `B`, has trivial linear monodromy
(`IsLagrangianTorusFibration.latticeMonodromyHom_eq_one_of_periodLattice_eq_closure_mvfderiv`).
So nontrivial linear monodromy is an obstruction to global action coordinates.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the period lattice bundle and its monodromy).
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed)

/-- **The period lattice bundle is a covering space of the base.** The covectors of `T*B` lying
in the period lattices of a regular Lagrangian torus fibration form a covering space of `B`:
near every point, the integer coordinates in the frame `2π da₁, …, 2π daₙ` of local action
coordinates `a` identify it with the product of a neighbourhood and `ℤⁿ`. -/
theorem isCoveringMap_latticeProj_periodLattice [BoundarylessManifold J B] :
    IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc)) := by
  refine isCoveringMap_latticeProj _ (ι := Fin (finrank ℝ F))
    (by rw [Fintype.card_fin, ContinuousLinearMap.dual_finrank_eq]) fun b₀ ↦ ?_
  obtain ⟨a, V, hV, hb₀, -, hloc, hΛ⟩ := h.exists_periodLattice_eq_closure_mvfderiv hσc b₀
  refine ⟨fun i b ↦ (2 * Real.pi) • mvfderiv J (fun c ↦ a c i) b, V, hV, hb₀,
    fun i b hb ↦ ?_, fun b hb ↦ ⟨?_, hΛ b hb⟩⟩
  · have hai : ContMDiffAt J 𝓘(ℝ) (0 + 1) (fun c ↦ a c i) b :=
      ((contMDiffAt_pi_module_iff.1 (hloc b hb).contMDiffAt) i).of_le (by simp)
    exact (continuousAt_const.smul_section
      hai.contMDiffAt_totalSpaceMk_mvfderiv.continuousAt).continuousWithinAt
  · exact h.linearIndependent_of_periodLattice_le_closure hσc (by simp) (hΛ b hb).le

variable {U : Set B} {g : B → ℝ}

/-- **Transport of periods follows differentials.** Let `g` be a function on the base which is
`C¹` at every point of a set `U`, and whose differential `dg_b` is a period at every `b ∈ U`, such
as `2π` times an action coordinate. Then transporting periods along a path `γ` in `U` carries
`dg` at the start of `γ` to `dg` at its end. -/
theorem latticeMonodromy_mk_mvfderiv
    (hL : IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc)))
    (hg : ∀ b ∈ U, ContMDiffAt J 𝓘(ℝ) 1 g b)
    (hgΛ : ∀ b ∈ U, mvfderiv J g b ∈ h.periodLattice hσc b) {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ U) :
    latticeMonodromy hL (.mk γ) ⟨mvfderiv J g x, hgΛ x (γ.source ▸ hγ 0)⟩ =
      ⟨mvfderiv J g y, hgΛ y (γ.target ▸ hγ 1)⟩ :=
  latticeMonodromy_mk_of_continuousOn hL
    (fun b hb ↦ ((hg b hb).contMDiffAt_totalSpaceMk_mvfderiv (n := 0)).continuousAt
      |>.continuousWithinAt) hgΛ γ hγ

/-- **Global action coordinates force trivial monodromy.** If the period lattice of a regular
Lagrangian torus fibration is spanned over `ℤ` at every point of the base by the differentials of
finitely many `C¹` functions on the whole base, such as `2π` times global action coordinates, then
its linear monodromy is trivial. -/
theorem latticeMonodromyHom_eq_one_of_periodLattice_eq_closure_mvfderiv {ι : Type*} [Finite ι]
    (hL : IsCoveringMap (latticeProj (F →L[ℝ] ℝ) (E := fun b : B ↦ TangentSpace J b →L[ℝ] ℝ)
      (h.periodLattice hσc)))
    {g : ι → B → ℝ} (hg : ∀ i, ContMDiff J 𝓘(ℝ) 1 (g i))
    (hΛ : ∀ b, h.periodLattice hσc b = AddSubgroup.closure (range fun i ↦ mvfderiv J (g i) b))
    (x : B) : latticeMonodromyHom hL x = 1 :=
  latticeMonodromyHom_eq_one hL
    (fun i ↦ ((hg i).contMDiff_totalSpaceMk_mvfderiv (n := 0)).continuous) hΛ x

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
