/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.RepresentationTheory.Basic

/-!
# Eigenvalues with a bounded coefficient

Let `ρ` be a representation of a monoid `G` and let `a = Σ_g a_g g` be an element of the monoid
algebra with eigenvector `x`: `Σ_g a_g ρ(g) x = θ x`. If some coefficient `g ↦ ℓ(ρ(g) x)` of `x`
is bounded and nonzero, then `‖θ‖ ≤ Σ_g ‖a_g‖`, the `ℓ¹` norm of `a`. The reason is that the
coefficient `f(g) = ℓ(ρ(g) x)` satisfies `θ f(g) = Σ_{g'} a_{g'} f(g g')`, so that
`‖θ‖ ‖f(g)‖ ≤ (Σ_{g'} ‖a_{g'}‖) sup ‖f‖` for every `g`, and taking the supremum over `g` gives the
bound. The same argument applies to the orbit map `g ↦ ρ(g) x` itself when the carrier is normed
and the orbit of `x` is bounded, for instance when `ρ` acts by isometries.

For a compact open subgroup `K` of a locally profinite group `G` and a function `h` on `G/K` with
finite support, the action `Σ_{c ∈ G/K} h(c) ρ(c) x` of `h` on a `K`-fixed vector `x` is the action
of the element `Σ_c h(c) c̃` of the monoid algebra, for any choice of representatives `c̃` of the
cosets, and its `ℓ¹` norm is `Σ_c |h(c)|`. The results below therefore give the bound
`|θ(h)| ≤ Σ_{c ∈ G/K} |h(c)|` for the eigenvalues `θ(h)` of the spherical Hecke algebra
`ℋ(G, K)` on a `K`-fixed vector with a bounded coefficient, or of a unitarisable representation.

## Main results

* `Finsupp.norm_le_sum_norm_of_bddAbove`: a bounded, nonzero eigenfunction of right convolution
  by a finitely supported `h` has eigenvalue of norm at most `Σ_g ‖h g‖`.
* `Representation.norm_le_sum_norm_of_bddAbove_coeff`: the bound for an eigenvector with a bounded
  nonzero coefficient.
* `Representation.norm_le_sum_norm_of_bddAbove_norm`: the bound for an eigenvector with a bounded
  orbit in a normed carrier.
* `Representation.norm_le_sum_norm_of_norm_apply_eq`: the bound for a representation by isometries.

## References

* The Tau Ceti roadmap `RiemannHypothesisForDirichletLFunctions/LocalFactorsOfTwistsAndTypes`,
  §3.1 (a) and (c).
-/

public section

open MonoidAlgebra

variable {𝕜 G E : Type*}

namespace Finsupp

/-- Let `f` be a bounded, not identically zero function on a magma `G` with values in a normed
group, and `h : G →₀ 𝕜` such that `Σ_{g'} h(g') f(g g') = θ f(g)` for every `g`. Then the
eigenvalue `θ` has norm at most the `ℓ¹` norm `Σ_g ‖h g‖` of `h`. -/
theorem norm_le_sum_norm_of_bddAbove [SeminormedRing 𝕜] [Mul G] [NormedAddCommGroup E]
    [Module 𝕜 E] [NormSMulClass 𝕜 E] {f : G → E} (hf : BddAbove (Set.range fun g ↦ ‖f g‖))
    (hf₀ : f ≠ 0) (h : G →₀ 𝕜) {θ : 𝕜}
    (hθ : ∀ g, (h.sum fun g' c ↦ c • f (g * g')) = θ • f g) :
    ‖θ‖ ≤ h.sum fun _ c ↦ ‖c‖ := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hf₀
  have hM : 0 < ⨆ g, ‖f g‖ := (norm_pos_iff.2 hg₀).trans_le (le_ciSup hf g₀)
  have key (g : G) : ‖θ‖ * ‖f g‖ ≤ (h.sum fun _ c ↦ ‖c‖) * ⨆ g, ‖f g‖ := by
    rw [← norm_smul, ← hθ g, Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g' _ ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (le_ciSup hf _) (norm_nonneg _)
  have : Nonempty G := ⟨g₀⟩
  refine le_of_mul_le_mul_right ?_ hM
  rw [Real.mul_iSup_of_nonneg (norm_nonneg θ)]
  exact ciSup_le key

end Finsupp

namespace Representation

variable [Monoid G]

/-- The translate by `g` of the action of `a` on `x` is `Σ_{g'} a_{g'} ρ(g g') x`. -/
private theorem apply_asAlgebraHom_apply {k V : Type*} [CommSemiring k] [AddCommMonoid V]
    [Module k V] (ρ : Representation k G V) (a : k[G]) (g : G) (x : V) :
    ρ g (ρ.asAlgebraHom a x) = a.coeff.sum fun g' c ↦ c • ρ (g * g') x := by
  simp [asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.coe_sum,
    Finset.sum_apply, map_mul]

/-- Let `x` be an eigenvector of `a = Σ_g a_g g` in a representation `ρ`, with eigenvalue `θ`.
If some linear form `ℓ` has `ℓ x ≠ 0` and the coefficient `g ↦ ℓ (ρ g x)` is bounded, then
`‖θ‖ ≤ Σ_g ‖a_g‖`. -/
theorem norm_le_sum_norm_of_bddAbove_coeff [NormedCommRing 𝕜] [NormMulClass 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (ρ : Representation 𝕜 G V) {a : 𝕜[G]} {x : V} {θ : 𝕜}
    (hθ : ρ.asAlgebraHom a x = θ • x) (ℓ : Module.Dual 𝕜 V) (hℓ : ℓ x ≠ 0)
    (hbdd : BddAbove (Set.range fun g ↦ ‖ℓ (ρ g x)‖)) :
    ‖θ‖ ≤ a.coeff.sum fun _ c ↦ ‖c‖ := by
  refine a.coeff.norm_le_sum_norm_of_bddAbove hbdd
    (Function.ne_iff.2 ⟨1, by simpa using hℓ⟩) fun g ↦ ?_
  have := congr(ℓ $(ρ.apply_asAlgebraHom_apply a g x))
  simp only [hθ, map_smul, Finsupp.sum, map_sum, smul_eq_mul] at this
  simpa only [Finsupp.sum, smul_eq_mul] using this.symm

/-- Let `x` be an eigenvector of `a = Σ_g a_g g` in a representation `ρ` on a normed space, with
eigenvalue `θ`. If the orbit of `x` is bounded, then `‖θ‖ ≤ Σ_g ‖a_g‖`. -/
theorem norm_le_sum_norm_of_bddAbove_norm [SeminormedCommRing 𝕜] {V : Type*}
    [NormedAddCommGroup V] [Module 𝕜 V] [NormSMulClass 𝕜 V] (ρ : Representation 𝕜 G V)
    {a : 𝕜[G]} {x : V} {θ : 𝕜} (hθ : ρ.asAlgebraHom a x = θ • x) (hx : x ≠ 0)
    (hbdd : BddAbove (Set.range fun g ↦ ‖ρ g x‖)) :
    ‖θ‖ ≤ a.coeff.sum fun _ c ↦ ‖c‖ := by
  refine a.coeff.norm_le_sum_norm_of_bddAbove hbdd
    (Function.ne_iff.2 ⟨1, by simpa using hx⟩) fun g ↦ ?_
  rw [← ρ.apply_asAlgebraHom_apply, hθ, map_smul]

/-- Let `x ≠ 0` be an eigenvector of `a = Σ_g a_g g` in a representation `ρ` by isometries of a
normed space, with eigenvalue `θ`. Then `‖θ‖ ≤ Σ_g ‖a_g‖`. -/
theorem norm_le_sum_norm_of_norm_apply_eq [SeminormedCommRing 𝕜] {V : Type*}
    [NormedAddCommGroup V] [Module 𝕜 V] [NormSMulClass 𝕜 V] (ρ : Representation 𝕜 G V)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) {a : 𝕜[G]} {x : V} {θ : 𝕜}
    (hθ : ρ.asAlgebraHom a x = θ • x) (hx : x ≠ 0) :
    ‖θ‖ ≤ a.coeff.sum fun _ c ↦ ‖c‖ :=
  ρ.norm_le_sum_norm_of_bddAbove_norm hθ hx ⟨‖x‖, by simp [upperBounds, hρ]⟩

end Representation
