/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Connected
public import TauCeti.Geometry.Manifold.Morse.FundamentalGroup
public import TauCeti.Geometry.Manifold.Morse.Perfect
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Isolated
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott

/-!
# Moment map components with isolated fixed points are perfect

Let a compact Lie group `G` act smoothly by symplectomorphisms on a compact manifold `M` with a
nondegenerate two-form `σ` and moment map `μ`. At every critical point, the component
`μ^ξ = ⟨μ, ξ⟩` has even Morse index and even coindex
(`TauCeti.SmoothTwoForm.IsMomentMap.even_manifoldMorseIndex`). So whenever `μ^ξ` is a Morse
function, the lacunary principle applies to it (`TauCeti.IsMorse.isPerfectMorse_of_even`), and
neither `μ^ξ` nor `-μ^ξ` has a critical point of index one:

* `μ^ξ` is a perfect Morse function for every division ring of coefficients `k`
  (`TauCeti.SmoothTwoForm.IsMomentMap.isPerfectMorse`);
* if `M` is connected, `μ^ξ` has a single local minimum, which is its global minimum, and a single
  local maximum, which is its global maximum, since a Morse function without critical points of
  index one has at most one local minimum
  (`TauCeti.IsMorse.subsingleton_setOf_isLocalMin_of_manifoldMorseIndex_ne_one`):
  see `TauCeti.SmoothTwoForm.IsMomentMap.subsingleton_setOf_isLocalMin`,
  `TauCeti.SmoothTwoForm.IsMomentMap.isMinOn_of_isLocalMin` and their counterparts for maxima.

When the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}` is the whole group, the critical points of `μ^ξ`
are the fixed points of `G`. If moreover every fixed point is isolated, it has no nonzero tangent
vector fixed by `G` (`TauCeti.eq_zero_of_forall_mfderiv_smul_eq_of_compactSpace`), so `μ^ξ` is a
Morse function (`TauCeti.SmoothTwoForm.IsMomentMap.isMorse_of_eq_top`), and the Betti number
`bⱼ(M; k)` is the number of fixed points at which `μ^ξ` has index `j`
(`TauCeti.SmoothTwoForm.IsMomentMap.bettiNumber_eq_ncard`).

For a torus, that is a compact connected abelian Lie group, such `ξ` exist, and the Betti numbers
of `M` are those of a space with only even cells, one for each fixed point:

* the fixed points are finite in number
  (`TauCeti.SmoothTwoForm.IsMomentMap.finite_fixedPoints`);
* the odd Betti numbers vanish (`TauCeti.SmoothTwoForm.IsMomentMap.bettiNumber_eq_zero_of_odd`);
* the sum of the Betti numbers is the number of fixed points
  (`TauCeti.SmoothTwoForm.IsMomentMap.sum_bettiNumber_eq_ncard_fixedPoints`);
* if `M` is connected, it is simply connected
  (`TauCeti.SmoothTwoForm.IsMomentMap.simplyConnectedSpace`), as there are no critical points of
  index one.

These conclusions use the isolation of the fixed points: a trivial action on a symplectic surface
of positive genus has one fixed component and nonzero first Betti number. The homology here is
singular homology with coefficients in a division ring; freeness of the integral homology, which
needs the even-cell structure itself, is not proved here.

Closedness of `σ` and equivariance of `μ` are not used.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* F. C. Kirwan, *Cohomology of quotients in symplectic and algebraic geometry*, Mathematical Notes
  31, Princeton University Press, 1984, § 5.
-/

public section

open Bundle Filter Manifold Module Set Topology
open scoped Manifold ContDiff

universe u

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [CompactSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ξ : GroupLieAlgebra I G}
  (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
  (hσG : ∀ (a : G) (x : M) (u v : TangentSpace I' x),
    σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) = σ.eval₂ x u v)
  (k : Type u) [DivisionRing k]

include h hσ hσG

/-! ### Morse components -/

/-- **Morse components of a moment map are perfect.** For a compact Lie group acting smoothly by
symplectomorphisms of a compact manifold, with moment map `μ`, every component `μ^ξ` which is a
Morse function is perfect for every division ring of coefficients: its indices are even. -/
theorem isPerfectMorse (hξ : IsMorse I' fun y ↦ μ y ξ) :
    IsPerfectMorse I' k fun y ↦ μ y ξ :=
  hξ.isPerfectMorse_of_even fun _ hp ↦ h.even_manifoldMorseIndex hσ hσG hp

/-- At a critical point, neither a moment map component nor its negative has Morse index one. -/
private theorem manifoldMorseIndex_ne_one {f : M → ℝ}
    (hf : f = (fun y ↦ μ y ξ) ∨ f = -fun y ↦ μ y ξ) {p : M} (hp : p ∈ criticalPoints I' f) :
    manifoldMorseIndex I' f p ≠ 1 := fun h1 ↦ by
  rcases hf with rfl | rfl
  · exact Nat.not_even_one (h1 ▸ h.even_manifoldMorseIndex hσ hσG hp)
  · rw [criticalPoints_neg] at hp
    exact Nat.not_even_one (h1 ▸ h.even_manifoldMorseIndex_neg hσ hσG hp)

/-- **A Morse component has a single local minimum.** For a compact Lie group acting smoothly by
symplectomorphisms of a compact connected manifold, with moment map `μ`, a component `μ^ξ` which
is a Morse function has at most one local minimum. -/
theorem subsingleton_setOf_isLocalMin [ConnectedSpace M] (hξ : IsMorse I' fun y ↦ μ y ξ) :
    {p | IsLocalMin (fun y ↦ μ y ξ) p}.Subsingleton :=
  hξ.subsingleton_setOf_isLocalMin_of_manifoldMorseIndex_ne_one
    fun _ ↦ h.manifoldMorseIndex_ne_one hσ hσG (.inl rfl)

/-- **A local minimum of a Morse component is the global minimum.** For a compact Lie group acting
smoothly by symplectomorphisms of a compact connected manifold, with moment map `μ`, every local
minimum of a component `μ^ξ` which is a Morse function is a global minimum. -/
theorem isMinOn_of_isLocalMin [ConnectedSpace M] (hξ : IsMorse I' fun y ↦ μ y ξ) {p : M}
    (hp : IsLocalMin (fun y ↦ μ y ξ) p) : IsMinOn (fun y ↦ μ y ξ) univ p :=
  hξ.isMinOn_of_isLocalMin_of_manifoldMorseIndex_ne_one
    (fun _ ↦ h.manifoldMorseIndex_ne_one hσ hσG (.inl rfl)) hp

/-- **A Morse component has a single local maximum.** For a compact Lie group acting smoothly by
symplectomorphisms of a compact connected manifold, with moment map `μ`, a component `μ^ξ` which
is a Morse function has at most one local maximum. -/
theorem subsingleton_setOf_isLocalMax [ConnectedSpace M] (hξ : IsMorse I' fun y ↦ μ y ξ) :
    {p | IsLocalMax (fun y ↦ μ y ξ) p}.Subsingleton := fun _ hp _ hq ↦
  hξ.neg.subsingleton_setOf_isLocalMin_of_manifoldMorseIndex_ne_one
    (fun _ ↦ h.manifoldMorseIndex_ne_one hσ hσG (.inr rfl)) (IsLocalMax.neg hp)
    (IsLocalMax.neg hq)

/-- **A local maximum of a Morse component is the global maximum.** For a compact Lie group acting
smoothly by symplectomorphisms of a compact connected manifold, with moment map `μ`, every local
maximum of a component `μ^ξ` which is a Morse function is a global maximum. -/
theorem isMaxOn_of_isLocalMax [ConnectedSpace M] (hξ : IsMorse I' fun y ↦ μ y ξ) {p : M}
    (hp : IsLocalMax (fun y ↦ μ y ξ) p) : IsMaxOn (fun y ↦ μ y ξ) univ p := fun y _ ↦
  neg_le_neg_iff.1 (hξ.neg.isMinOn_of_isLocalMin_of_manifoldMorseIndex_ne_one
    (fun _ ↦ h.manifoldMorseIndex_ne_one hσ hσG (.inr rfl)) hp.neg (mem_univ y))

/-! ### Isolated fixed points -/

omit hσG in
/-- **Generic components are Morse when fixed points are isolated.** For a compact Lie group acting
smoothly on a compact manifold, with moment map `μ`, all of whose fixed points are isolated, the
component `μ^ξ` is a Morse function whenever the closure of `{exp (t ξ) | t ∈ ℝ}` is the whole
group. -/
theorem isMorse_of_eq_top (hξ : Lie.closedOneParameterSubgroup ξ = ⊤)
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p) :
    IsMorse I' fun y ↦ μ y ξ :=
  (h.isMorse_iff_of_eq_top hσ hξ).2 fun p hp _ hv ↦
    eq_zero_of_forall_mfderiv_smul_eq_of_compactSpace I hp (hiso p hp) hv

/-- **Betti numbers count fixed points.** For a compact Lie group acting smoothly by
symplectomorphisms of a compact manifold, with moment map `μ`, all of whose fixed points are
isolated, and for `ξ` such that the closure of `{exp (t ξ) | t ∈ ℝ}` is the whole group, the
Betti number `bⱼ(M; k)` is the number of fixed points at which `μ^ξ` has Morse index `j`, for every
division ring `k`. -/
theorem bettiNumber_eq_ncard (hξ : Lie.closedOneParameterSubgroup ξ = ⊤)
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    (j : ℕ) :
    bettiNumber k M j =
      {p ∈ MulAction.fixedPoints G M | manifoldMorseIndex I' (fun y ↦ μ y ξ) p = j}.ncard := by
  rw [(h.isPerfectMorse hσ hσG k (h.isMorse_of_eq_top hσ hξ hiso)).bettiNumber_eq_ncard j,
    h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]

section Torus

variable [IsMulCommutative G] [PreconnectedSpace G]

omit hσG in
/-- **Isolated fixed points of a torus action are finite in number.** For a torus acting smoothly
on a compact manifold with a moment map, if every fixed point is isolated, then there are finitely
many fixed points. -/
theorem finite_fixedPoints
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p) :
    (MulAction.fixedPoints G M).Finite := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  rw [← h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]
  exact (h.isMorse_of_eq_top hσ hξ hiso).finite_criticalPoints

/-- **Odd Betti numbers vanish.** For a torus acting smoothly by symplectomorphisms of a compact
manifold, with a moment map and isolated fixed points, the odd Betti numbers of the manifold
vanish for every division ring of coefficients. -/
theorem bettiNumber_eq_zero_of_odd
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    {j : ℕ} (hj : Odd j) : bettiNumber k M j = 0 := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  exact (h.isMorse_of_eq_top hσ hξ hiso).bettiNumber_eq_zero_of_odd
    (fun _ hp ↦ h.even_manifoldMorseIndex hσ hσG hp) hj

/-- **The total Betti number is the number of fixed points.** For a torus acting smoothly by
symplectomorphisms of a compact manifold, with a moment map and isolated fixed points, the sum of
the Betti numbers of the manifold, for every division ring of coefficients, is the number of fixed
points. -/
theorem sum_bettiNumber_eq_ncard_fixedPoints
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p) :
    ∑ j ∈ Finset.range (finrank ℝ E' + 1), bettiNumber k M j =
      (MulAction.fixedPoints G M).ncard := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  rw [(h.isPerfectMorse hσ hσG k (h.isMorse_of_eq_top hσ hξ hiso)).sum_bettiNumber_eq_ncard,
    h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]

/-- **Isolated fixed points force simple connectivity.** A compact connected manifold carrying a
smooth symplectic torus action with a moment map and isolated fixed points is simply
connected. -/
theorem simplyConnectedSpace [ConnectedSpace M]
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p) :
    SimplyConnectedSpace M := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  have hM := h.isMorse_of_eq_top hσ hξ hiso
  exact hM.simplyConnectedSpace_of_manifoldMorseIndex_ne_one hM.contMDiff.continuous.isProperMap
    (isCompact_range hM.contMDiff.continuous).bddBelow
    fun _ ↦ h.manifoldMorseIndex_ne_one hσ hσG (.inl rfl)

end Torus

end TauCeti.SmoothTwoForm.IsMomentMap
