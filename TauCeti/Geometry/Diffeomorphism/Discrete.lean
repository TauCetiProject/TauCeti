/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Action

/-!
# Diffeomorphisms of a discrete manifold

Every map out of a discrete space is locally constant, hence `C^n` for every `n`
(`contMDiff_of_discreteTopology`). So on a discrete manifold `M`, for instance a manifold modelled
on a zero-dimensional space, every bijection is a diffeomorphism
(`Diffeomorph.ofDiscreteTopology`), and the group `Diff(M)` of self-diffeomorphisms is the full
permutation group of `M` (`Diffeomorph.mulEquivPermOfDiscreteTopology`).

This describes evaluation `Diff(M) → M`, `g ↦ g x₀`, at a point `x₀` of a discrete manifold. The
transpositions of `M` are diffeomorphisms, so the orbit of `x₀` is all of `M`
(`Diffeomorph.orbit_eq_univ_of_discreteTopology`), however many points `M` has. The stabilizer
`Diff(M, x₀)` of `x₀` permutes the other points freely, so it is trivial exactly when `x₀` has at
most one other point (`Diffeomorph.stabilizer_eq_bot_iff_of_discreteTopology`). For `M` consisting
of two points, evaluation is therefore a bijection `Diff(M) → M` with trivial fibre: the swap of
the two points carries `x₀` to the other point, and only the identity fixes `x₀`
(`Diffeomorph.stabilizer_eq_bot_of_natCard_eq_two`).
-/

public section

open MulAction Set
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [DiscreteTopology M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [DiscreteTopology N]

variable (I I' n) in
/-- **Every bijection of discrete manifolds is a diffeomorphism**: both it and its inverse are
locally constant, hence `C^n`. -/
def ofDiscreteTopology (e : M ≃ N) : M ≃ₘ^n⟮I, I'⟯ N where
  toEquiv := e
  contMDiff_toFun := contMDiff_of_discreteTopology
  contMDiff_invFun := contMDiff_of_discreteTopology

@[simp]
theorem coe_ofDiscreteTopology (e : M ≃ N) : ⇑(ofDiscreteTopology I I' n e) = e :=
  (rfl)

@[simp]
theorem toEquiv_ofDiscreteTopology (e : M ≃ N) : (ofDiscreteTopology I I' n e).toEquiv = e :=
  (rfl)

variable (I n M) in
/-- **The diffeomorphism group of a discrete manifold is its permutation group**, through the
underlying permutation of a diffeomorphism (`Diffeomorph.toPerm`). -/
noncomputable def mulEquivPermOfDiscreteTopology : (M ≃ₘ^n⟮I, I⟯ M) ≃* Equiv.Perm M :=
  .ofBijective toPerm ⟨toPerm_injective, fun e ↦ ⟨ofDiscreteTopology I I n e, by
    rw [toPerm_apply, toEquiv_ofDiscreteTopology]⟩⟩

@[simp]
theorem mulEquivPermOfDiscreteTopology_apply (g : M ≃ₘ^n⟮I, I⟯ M) :
    mulEquivPermOfDiscreteTopology I n M g = g.toEquiv :=
  toPerm_apply g

@[simp]
theorem mulEquivPermOfDiscreteTopology_symm_apply (e : Equiv.Perm M) :
    (mulEquivPermOfDiscreteTopology I n M).symm e = ofDiscreteTopology I I n e :=
  (mulEquivPermOfDiscreteTopology I n M).symm_apply_eq.2 (by
    rw [mulEquivPermOfDiscreteTopology_apply, toEquiv_ofDiscreteTopology])

variable (I n) in
/-- **Diffeomorphisms of a discrete manifold act transitively**: the transposition of `x` and `y`
is a diffeomorphism carrying `x` to `y`, so the orbit of every point is the whole manifold. -/
theorem orbit_eq_univ_of_discreteTopology (x : M) : orbit (M ≃ₘ^n⟮I, I⟯ M) x = univ := by
  classical
  exact eq_univ_of_forall fun y ↦ mem_orbit_iff.2 ⟨ofDiscreteTopology I I n (Equiv.swap x y), by
    rw [smul_def, coe_ofDiscreteTopology, Equiv.swap_apply_left]⟩

variable (I n) in
/-- **The stabilizer of a point of a discrete manifold is trivial exactly when there is at most one
other point.** A diffeomorphism fixing `x₀` permutes the other points; when there are two of them,
their transposition is a nontrivial diffeomorphism fixing `x₀`. -/
theorem stabilizer_eq_bot_iff_of_discreteTopology (x₀ : M) :
    stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀ = ⊥ ↔ Subsingleton {x // x ≠ x₀} := by
  classical
  refine ⟨fun h ↦ ⟨fun y z ↦ Subtype.ext ?_⟩,
    fun h ↦ (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ ?_⟩
  · -- The transposition of `y` and `z` fixes `x₀`, so it is the identity.
    by_contra hyz
    have hmem : ofDiscreteTopology I I n (Equiv.swap (y : M) z) ∈ stabilizer _ x₀ := by
      rw [mem_stabilizer_iff, smul_def, coe_ofDiscreteTopology,
        Equiv.swap_apply_of_ne_of_ne y.property.symm z.property.symm]
    rw [h, Subgroup.mem_bot] at hmem
    exact hyz (by simpa using (DFunLike.congr_fun hmem (y : M)).symm)
  · -- A diffeomorphism fixing `x₀` sends every other point to another point, which is itself.
    rw [mem_stabilizer_iff, smul_def] at hg
    refine Diffeomorph.ext fun y ↦ ?_
    rw [coe_one, id_eq]
    by_cases hy : y = x₀
    · rw [hy, hg]
    · have hgy : g y ≠ x₀ := fun h' ↦ hy (g.injective (h'.trans hg.symm))
      exact congrArg Subtype.val (Subsingleton.elim (⟨g y, hgy⟩ : {x // x ≠ x₀}) ⟨y, hy⟩)

variable (I n) in
/-- **A discrete manifold with two points has trivial point stabilizers**: the only diffeomorphism
fixing one point is the identity, while the swap of the two points carries it to the other one
(`Diffeomorph.orbit_eq_univ_of_discreteTopology`). -/
theorem stabilizer_eq_bot_of_natCard_eq_two (hM : Nat.card M = 2) (x₀ : M) :
    stabilizer (M ≃ₘ^n⟮I, I⟯ M) x₀ = ⊥ := by
  obtain ⟨a, b, -, hab⟩ := Nat.card_eq_two_iff.1 hM
  have hmem (x : M) : x = a ∨ x = b := by simpa [← hab] using mem_univ x
  refine (stabilizer_eq_bot_iff_of_discreteTopology I n x₀).2 ⟨fun y z ↦ Subtype.ext ?_⟩
  have hy := y.property
  have hz := z.property
  rcases hmem x₀ with rfl | rfl <;> rcases hmem y with h | h <;> rcases hmem z with h' | h' <;>
    simp_all

end Diffeomorph
