/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import TauCeti.LinearAlgebra.Eigenspace.Range

/-!
# Dominant and subdominant subspaces

For an endomorphism `T` of a vector space over a normed field and a real level `α`, the
*dominant subspace* `T.dominantSubspace α` is the sum of the generalized eigenspaces of `T` for
the eigenvalues of modulus at least `α`, and the *subdominant subspace* `T.subdominantSubspace α`
is the sum of those for the eigenvalues of modulus less than `α`. These are the two invariant
subspaces into which a circle of radius `α` splits the space; power and subspace iteration converge
to the dominant one at a rate governed by the ratio between the moduli on the two sides.

Generalized eigenspaces, not eigenspaces, are needed: for the Jordan block `[[1, 1], [0, 1]]` and
`α = 1` the eigenspaces of the eigenvalues of modulus at least `1` span only a line, while the
subdominant subspace is `0`. The two subspaces are in general not orthogonal: for
`T = [[2, 1], [0, 1]]` on `ℂ²` and `α = 2` they are the lines of `(1, 0)` and `(1, -1)`.

## Main definitions

* `Module.End.dominantSubspace`: the sum of the generalized eigenspaces of `T` for the
  eigenvalues `μ` with `α ≤ ‖μ‖`.
* `Module.End.subdominantSubspace`: the sum of the generalized eigenspaces of `T` for the
  eigenvalues `μ` with `‖μ‖ < α`.

## Main results

* `Module.End.mapsTo_dominantSubspace_of_comm`, `Module.End.mapsTo_subdominantSubspace_of_comm`:
  both subspaces are invariant under every endomorphism commuting with `T`, in particular under
  `T` itself.
* `Module.End.disjoint_dominantSubspace_subdominantSubspace`: the two subspaces meet only in `0`.
* `Module.End.dominantSubspace_sup_subdominantSubspace`: together they span the sum of all
  generalized eigenspaces of `T`.
* `Module.End.isCompl_dominantSubspace_subdominantSubspace`: over an algebraically closed field in
  finite dimension, they are complementary.
* `Module.End.isUnit_restrict_dominantSubspace`: for `α > 0`, the restriction of `T` to its
  dominant subspace is invertible.

## References

* Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition, SIAM (2011),
  Chapters 4 and 5.
-/

public section

open Set

namespace Module.End

variable {K V : Type*} [NormedField K] [AddCommGroup V] [Module K V]

/-- The dominant subspace of `T` at level `α`: the sum of the generalized eigenspaces of `T` for
the eigenvalues of modulus at least `α`. -/
def dominantSubspace (T : End K V) (α : ℝ) : Submodule K V :=
  ⨆ (μ : K) (_ : α ≤ ‖μ‖), T.maxGenEigenspace μ

/-- The subdominant subspace of `T` at level `α`: the sum of the generalized eigenspaces of `T`
for the eigenvalues of modulus less than `α`. -/
def subdominantSubspace (T : End K V) (α : ℝ) : Submodule K V :=
  ⨆ (μ : K) (_ : ‖μ‖ < α), T.maxGenEigenspace μ

/-- The generalized eigenspace of an eigenvalue of modulus at least `α` lies in the dominant
subspace at level `α`. -/
theorem maxGenEigenspace_le_dominantSubspace (T : End K V) {α : ℝ} {μ : K} (hμ : α ≤ ‖μ‖) :
    T.maxGenEigenspace μ ≤ T.dominantSubspace α :=
  le_iSup₂ (f := fun μ (_ : α ≤ ‖μ‖) ↦ T.maxGenEigenspace μ) μ hμ

/-- The generalized eigenspace of an eigenvalue of modulus less than `α` lies in the subdominant
subspace at level `α`. -/
theorem maxGenEigenspace_le_subdominantSubspace (T : End K V) {α : ℝ} {μ : K} (hμ : ‖μ‖ < α) :
    T.maxGenEigenspace μ ≤ T.subdominantSubspace α :=
  le_iSup₂ (f := fun μ (_ : ‖μ‖ < α) ↦ T.maxGenEigenspace μ) μ hμ

/-- The dominant subspace at level `α` lies in `p` exactly when every generalized eigenspace of an
eigenvalue of modulus at least `α` does. -/
theorem dominantSubspace_le_iff {T : End K V} {α : ℝ} {p : Submodule K V} :
    T.dominantSubspace α ≤ p ↔ ∀ μ : K, α ≤ ‖μ‖ → T.maxGenEigenspace μ ≤ p :=
  iSup₂_le_iff

/-- The subdominant subspace at level `α` lies in `p` exactly when every generalized eigenspace of
an eigenvalue of modulus less than `α` does. -/
theorem subdominantSubspace_le_iff {T : End K V} {α : ℝ} {p : Submodule K V} :
    T.subdominantSubspace α ≤ p ↔ ∀ μ : K, ‖μ‖ < α → T.maxGenEigenspace μ ≤ p :=
  iSup₂_le_iff

/-- The dominant subspace of `T` is invariant under every endomorphism commuting with `T`; for
`T` itself, take `Commute.refl T`. -/
theorem mapsTo_dominantSubspace_of_comm {T g : End K V} (h : Commute T g) (α : ℝ) :
    MapsTo g (T.dominantSubspace α) (T.dominantSubspace α) := by
  have : T.dominantSubspace α ≤ (T.dominantSubspace α).comap g :=
    dominantSubspace_le_iff.2 fun μ hμ _ hx ↦
      T.maxGenEigenspace_le_dominantSubspace hμ (mapsTo_maxGenEigenspace_of_comm h μ hx)
  exact fun _ hx ↦ this hx

/-- The subdominant subspace of `T` is invariant under every endomorphism commuting with `T`; for
`T` itself, take `Commute.refl T`. -/
theorem mapsTo_subdominantSubspace_of_comm {T g : End K V} (h : Commute T g) (α : ℝ) :
    MapsTo g (T.subdominantSubspace α) (T.subdominantSubspace α) := by
  have : T.subdominantSubspace α ≤ (T.subdominantSubspace α).comap g :=
    subdominantSubspace_le_iff.2 fun μ hμ _ hx ↦
      T.maxGenEigenspace_le_subdominantSubspace hμ (mapsTo_maxGenEigenspace_of_comm h μ hx)
  exact fun _ hx ↦ this hx

/-- The dominant and subdominant subspaces meet only in `0`. -/
theorem disjoint_dominantSubspace_subdominantSubspace (T : End K V) (α : ℝ) :
    Disjoint (T.dominantSubspace α) (T.subdominantSubspace α) :=
  T.independent_maxGenEigenspace.disjoint_biSup_biSup (s := {μ | α ≤ ‖μ‖}) (t := {μ | ‖μ‖ < α})
    (disjoint_left.2 fun _ h₁ h₂ ↦ lt_irrefl α (lt_of_le_of_lt h₁ h₂))

/-- Together, the dominant and subdominant subspaces span the sum of all generalized eigenspaces
of `T`. -/
theorem dominantSubspace_sup_subdominantSubspace (T : End K V) (α : ℝ) :
    T.dominantSubspace α ⊔ T.subdominantSubspace α = ⨆ μ, T.maxGenEigenspace μ := by
  refine le_antisymm (sup_le (iSup₂_le fun μ _ ↦ le_iSup _ μ) (iSup₂_le fun μ _ ↦ le_iSup _ μ))
    (iSup_le fun μ ↦ ?_)
  rcases le_or_gt α ‖μ‖ with hμ | hμ
  · exact le_sup_of_le_left (T.maxGenEigenspace_le_dominantSubspace hμ)
  · exact le_sup_of_le_right (T.maxGenEigenspace_le_subdominantSubspace hμ)

/-- If the generalized eigenspaces of `T` span the space, its dominant and subdominant subspaces
are complementary. -/
theorem isCompl_dominantSubspace_subdominantSubspace_of_iSup_eq_top {T : End K V}
    (hT : ⨆ μ, T.maxGenEigenspace μ = ⊤) (α : ℝ) :
    IsCompl (T.dominantSubspace α) (T.subdominantSubspace α) :=
  ⟨T.disjoint_dominantSubspace_subdominantSubspace α,
    codisjoint_iff.2 (by rw [dominantSubspace_sup_subdominantSubspace, hT])⟩

/-- Over an algebraically closed field in finite dimension, the dominant and subdominant
subspaces of `T` are complementary. -/
theorem isCompl_dominantSubspace_subdominantSubspace [IsAlgClosed K] [FiniteDimensional K V]
    (T : End K V) (α : ℝ) : IsCompl (T.dominantSubspace α) (T.subdominantSubspace α) :=
  isCompl_dominantSubspace_subdominantSubspace_of_iSup_eq_top T.iSup_maxGenEigenspace_eq_top α

/-- For `α > 0`, the restriction of `T` to its dominant subspace at level `α` is invertible, in
any dimension. -/
theorem isUnit_restrict_dominantSubspace (T : End K V) {α : ℝ} (hα : 0 < α) :
    IsUnit (T.restrict fun _ hx ↦ mapsTo_dominantSubspace_of_comm (Commute.refl T) α hx) := by
  rw [isUnit_iff]
  refine ⟨(LinearMap.injective_restrict_iff _).2 ?_, LinearMap.range_eq_top.1 ?_⟩
  · have hdisj := T.independent_maxGenEigenspace.disjoint_biSup (y := {μ | α ≤ ‖μ‖}) (x := 0)
      (by simpa using hα)
    exact hdisj.symm.mono_right ((eigenspace_zero T).symm.le.trans eigenspace_le_maxGenEigenspace)
  · rw [LinearMap.range_restrict, Submodule.comap_subtype_eq_top]
    refine dominantSubspace_le_iff.2 fun μ hμ z hz ↦ ?_
    have hμ' : IsUnit μ := isUnit_iff_ne_zero.2 (norm_pos_iff.1 (hα.trans_le hμ))
    obtain ⟨u, hu, rfl⟩ := surjOn_pow_genEigenspace_of_isUnit hμ' ⊤ 1 hz
    exact ⟨u, T.maxGenEigenspace_le_dominantSubspace hμ hu, by simp⟩

end Module.End
