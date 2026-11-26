/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel.Lacunary
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Perfect

/-!
# The integral homology of a Hamiltonian torus manifold with isolated fixed points

Let a compact Lie group `G` act smoothly by symplectomorphisms on a compact boundaryless manifold
`M` with a nondegenerate two-form `σ` and moment map `μ`, and suppose that every fixed point of the
action is isolated. For `ξ` in the Lie algebra such that the closure of `{exp (t ξ) | t ∈ ℝ}` is
the whole group, the component `μ^ξ = ⟨μ, ξ⟩` is a Morse function whose critical points are the
fixed points, all of even Morse index (`TauCeti.SmoothTwoForm.IsMomentMap.isMorse_of_eq_top`,
`TauCeti.SmoothTwoForm.IsMomentMap.even_manifoldMorseIndex`). By Milnor's CW model, `M` is
therefore homotopy equivalent to a finite CW complex with one cell of even dimension for each fixed
point, and since no two cells have dimensions differing by one, all cellular differentials vanish
(`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma_of_even`). This file reads off the singular
homology of `M`, with arbitrary coefficients and in particular integrally, by specializing the
integral consequences of the lacunary principle for Morse functions in
`TauCeti/Geometry/Manifold/Morse/CWModel/Lacunary.lean` to `μ^ξ`:

* for coefficients `R` in any abelian category with coproducts, `Hₙ(M; R)` is the coproduct of
  one copy of `R` for each fixed point at which `μ^ξ` has Morse index `n`
  (`TauCeti.SmoothTwoForm.IsMomentMap.nonempty_singularHomology_iso_sigma`);
* the integral homology `Hₙ(M; ℤ)` is the free abelian group `ℤ^F` on the set `F` of these fixed
  points (`TauCeti.SmoothTwoForm.IsMomentMap.nonempty_singularHomology_int_linearEquiv_finsupp`),
  so its rank is the number of fixed points of index `n`
  (`TauCeti.SmoothTwoForm.IsMomentMap.finrank_singularHomology_int_eq_ncard`).

For a torus, that is a compact connected abelian Lie group, such `ξ` exist, and isolated fixed
points make the homology of `M` that of a space with only even cells:

* the homology vanishes in odd degrees, for every coefficient object
  (`TauCeti.SmoothTwoForm.IsMomentMap.isZero_singularHomology_of_odd`);
* the integral homology is a finitely generated free abelian group in every degree
  (`TauCeti.SmoothTwoForm.IsMomentMap.free_singularHomology_int`,
  `TauCeti.SmoothTwoForm.IsMomentMap.finite_singularHomology_int`);
* its rank is the Betti number over every division ring
  (`TauCeti.SmoothTwoForm.IsMomentMap.finrank_singularHomology_int_eq_bettiNumber`).

The integral coefficients are the integers lifted to the universe of `M`, as for the singular
homology of a space in an arbitrary universe. These conclusions use the isolation of the fixed
points: a trivial action on a symplectic two-torus has one fixed component, but `H₁` has rank two.
Closedness of `σ` and equivariance of `μ` are not used.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
* F. C. Kirwan, *Cohomology of quotients in symplectic and algebraic geometry*, Mathematical Notes
  31, Princeton University Press, 1984, § 5.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 (the CW model).
-/

public section

open AlgebraicTopology CategoryTheory Limits Module Set Topology
open scoped ContDiff Manifold

universe u v w

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

include h hσ hσG

/-- No two critical points of a moment map component have Morse indices differing by one: all of
them are even. -/
private theorem forall_manifoldMorseIndex_ne_add_one :
    ∀ x ∈ criticalPoints I' (fun y ↦ μ y ξ), ∀ y ∈ criticalPoints I' (fun y ↦ μ y ξ),
      manifoldMorseIndex I' (fun y ↦ μ y ξ) x ≠ manifoldMorseIndex I' (fun y ↦ μ y ξ) y + 1 :=
  forall_manifoldMorseIndex_ne_add_one_of_even fun _ hp ↦ h.even_manifoldMorseIndex hσ hσG hp

/-! ### Generic components -/

/-- **The homology of a Hamiltonian manifold with isolated fixed points.** For a compact Lie
group acting smoothly by symplectomorphisms of a compact manifold, with moment map `μ`, all of
whose fixed points are isolated, and for `ξ` such that the closure of `{exp (t ξ) | t ∈ ℝ}` is the
whole group, `Hₙ(M; R)` is the coproduct of one copy of `R` for each fixed point at which `μ^ξ` has
Morse index `n`, for coefficients `R` in any abelian category with coproducts. -/
theorem nonempty_singularHomology_iso_sigma (hξ : Lie.closedOneParameterSubgroup ξ = ⊤)
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{p ∈ MulAction.fixedPoints G M |
        manifoldMorseIndex I' (fun y ↦ μ y ξ) p = n} ↦ R) := by
  rw [← h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]
  exact (h.isMorse_of_eq_top hσ hξ hiso).nonempty_singularHomology_iso_sigma_of_even
    (fun _ hp ↦ h.even_manifoldMorseIndex hσ hσG hp) R n

/-- **Integral homology is free on the fixed points.** For a compact Lie group acting smoothly by
symplectomorphisms of a compact manifold, with moment map `μ`, all of whose fixed points are
isolated, and for `ξ` such that the closure of `{exp (t ξ) | t ∈ ℝ}` is the whole group, the
integral homology `Hₙ(M; ℤ)` is the free abelian group on the fixed points at which `μ^ξ` has Morse
index `n`. -/
theorem nonempty_singularHomology_int_linearEquiv_finsupp
    (hξ : Lie.closedOneParameterSubgroup ξ = ⊤)
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    (n : ℕ) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M) ≃ₗ[ℤ]
      (↥{p ∈ MulAction.fixedPoints G M | manifoldMorseIndex I' (fun y ↦ μ y ξ) p = n} →₀ ℤ)) := by
  rw [← h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]
  exact (h.isMorse_of_eq_top hσ hξ hiso)
    |>.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one
    (h.forall_manifoldMorseIndex_ne_add_one hσ hσG) n

/-- **The rank of integral homology counts fixed points.** For a compact Lie group acting smoothly
by symplectomorphisms of a compact manifold, with moment map `μ`, all of whose fixed points are
isolated, and for `ξ` such that the closure of `{exp (t ξ) | t ∈ ℝ}` is the whole group, the rank
of `Hₙ(M; ℤ)` is the number of fixed points at which `μ^ξ` has Morse index `n`. -/
theorem finrank_singularHomology_int_eq_ncard (hξ : Lie.closedOneParameterSubgroup ξ = ⊤)
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    (n : ℕ) :
    finrank ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) =
      {p ∈ MulAction.fixedPoints G M | manifoldMorseIndex I' (fun y ↦ μ y ξ) p = n}.ncard := by
  rw [← h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]
  exact (h.isMorse_of_eq_top hσ hξ hiso).finrank_singularHomology_int_eq_ncard_of_forall_ne_add_one
    (h.forall_manifoldMorseIndex_ne_add_one hσ hσG) n

/-! ### Torus actions -/

section Torus

variable [IsMulCommutative G] [PreconnectedSpace G]

/-- **Odd homology vanishes.** For a torus acting smoothly by symplectomorphisms of a compact
manifold, with a moment map and isolated fixed points, the homology of the manifold vanishes in
odd degrees, for coefficients in any abelian category with coproducts. -/
theorem isZero_singularHomology_of_odd
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) {n : ℕ}
    (hn : Odd n) : IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  exact (h.isMorse_of_eq_top hσ hξ hiso).isZero_singularHomology_of_odd
    (fun _ hp ↦ h.even_manifoldMorseIndex hσ hσG hp) R hn

/-- **Integral homology is free.** For a torus acting smoothly by symplectomorphisms of a compact
manifold, with a moment map and isolated fixed points, the integral homology of the manifold is a
free abelian group in every degree. -/
theorem free_singularHomology_int
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    (n : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  exact (h.isMorse_of_eq_top hσ hξ hiso).free_singularHomology_int_of_forall_ne_add_one
    (h.forall_manifoldMorseIndex_ne_add_one hσ hσG) n

/-- **Integral homology is finitely generated.** For a torus acting smoothly by symplectomorphisms
of a compact manifold, with a moment map and isolated fixed points, the integral homology of the
manifold is finitely generated in every degree. -/
theorem finite_singularHomology_int
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    (n : ℕ) :
    Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  exact (h.isMorse_of_eq_top hσ hξ hiso).finite_singularHomology_int_of_forall_ne_add_one
    (h.forall_manifoldMorseIndex_ne_add_one hσ hσG) n

/-- **Integral ranks are Betti numbers.** For a torus acting smoothly by symplectomorphisms of a
compact manifold, with a moment map and isolated fixed points, the rank of the integral homology in
each degree is the Betti number over every division ring `k`. -/
theorem finrank_singularHomology_int_eq_bettiNumber
    (hiso : ∀ p ∈ MulAction.fixedPoints G M, ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p)
    (k : Type u) [DivisionRing k] (n : ℕ) :
    finrank ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) = bettiNumber k M n := by
  obtain ⟨ξ, hξ⟩ := (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).nonempty
  rw [h.finrank_singularHomology_int_eq_ncard hσ hσG hξ hiso,
    h.bettiNumber_eq_ncard hσ hσG k hξ hiso]

end Torus

end TauCeti.SmoothTwoForm.IsMomentMap
