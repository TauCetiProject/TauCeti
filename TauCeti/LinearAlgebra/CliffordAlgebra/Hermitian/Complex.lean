/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.Analysis.InnerProductSpace.SesquilinearForm

/-!
# Compatible Hermitian forms on complexified Clifford modules

On the complexification of a real Clifford algebra, the adjoint relevant to Hermitian
representations is `CliffordAlgebra.conjStar`, not Mathlib's complex-linear Clifford `star`.
Skew-adjointness on the real vectors is equivalent to compatibility with this conjugate-linear
adjoint on the whole algebra.

If the action surjects onto the full complex endomorphism algebra, every positive definite
compatible Hermitian form is a unique positive real multiple of any given compatible inner
product. In particular this applies to an algebra isomorphism onto the endomorphisms of a
spinor space; see `CliffordAlgebra.existsUnique_pos_mul_inner_of_surjective`. The same holds
relative to a positive definite compatible Hermitian form instead of an inner product
(`CliffordAlgebra.existsUnique_pos_mul_of_surjective`). No existence of a compatible form is
asserted here; for an algebra isomorphism onto `End S` with `Q v = -‖v‖ ^ 2` on a Euclidean
space (necessarily of even dimension), it is `CliffordAlgebra.exists_sesqForm_map_eq_map_conjStar`.
Surjectivity is essential: reducible modules can have independently rescaled metrics on
multiplicity spaces.

The forms use Mathlib's conjugate-first convention. The uniqueness argument is the
full-matrix-algebra case of Schur's lemma, implemented using rank-one operators by
`LinearMap.existsUnique_pos_mul_inner_of_adjoint`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open scoped TensorProduct ComplexOrder

namespace CliffordAlgebra

variable {V S : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

section SesquilinearForm

variable [AddCommGroup S] [Module ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)

/-- A sesquilinear form for which the real Clifford generators are skew-adjoint is compatible
with the conjugate-linear adjoint on the whole algebra. Positivity is not needed. -/
theorem sesqForm_map_eq_map_conjStar (H : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ)
    (hH : ∀ (v : V) x y,
      H (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x) y =
        -H x (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) y))
    (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S) :
    H (ρ a x) y = H x (ρ (conjStar Q a) y) := by
  induction a using CliffordAlgebra.induction generalizing x y with
  | algebraMap z =>
    simp [AlgHom.commutes, Module.algebraMap_end_eq_smul_id]
  | ι w =>
    induction w using TensorProduct.inductionOn with
    | tmul z v =>
      have hw : z ⊗ₜ[ℝ] v = z • ((1 : ℂ) ⊗ₜ[ℝ] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hw]
      simp [hH]
    | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw']
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, conjStar_mul, ha, hb]

end SesquilinearForm

section Hermitian

variable [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)

/-- Skew-adjoint real generators make the action a representation of the conjugate-linear
Clifford adjoint on the entire complexified algebra. -/
theorem adjoint_map_eq_map_conjStar
    (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ a).adjoint = ρ (conjStar Q a) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right]
  apply sesqForm_map_eq_map_conjStar ρ (innerₛₗ ℂ)
  intro v x y
  rw [innerₛₗ_apply_apply, innerₛₗ_apply_apply, ← LinearMap.adjoint_inner_right, hρ]
  simp

/-- Compatibility with the conjugate-linear Clifford adjoint can be checked on real vectors.
The native complex-linear Clifford star is not the adjoint in this criterion. -/
theorem adjoint_map_eq_map_conjStar_iff :
    (∀ a, (ρ a).adjoint = ρ (conjStar Q a)) ↔
      ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
        -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) := by
  refine ⟨fun h v => ?_, fun h => adjoint_map_eq_map_conjStar ρ h⟩
  simpa using h (ι (Q.baseChange ℂ) (1 ⊗ₜ v))

/-- For a full endomorphism-algebra Clifford action, a positive definite compatible Hermitian
form differs from a given compatible inner product by a unique positive real scalar.

The surjectivity hypothesis applies, in particular, to any Clifford algebra isomorphism
`CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S`. The statement allows dimension zero
for `V`, but excludes the zero spinor module, on which a rescaling scalar is not unique. -/
theorem existsUnique_pos_mul_inner_of_surjective [Nontrivial S]
    (hsurj : Function.Surjective ρ)
    (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
    (H : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ) (hpos : H.IsNonneg)
    (hdef : ∀ x : S, x ≠ 0 → H x x ≠ 0)
    (hH : ∀ (v : V) x y,
      H (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x) y =
        -H x (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) y)) :
    ∃! r : ℝ, 0 < r ∧ ∀ x y, H x y = (r : ℂ) * inner ℂ x y := by
  apply H.existsUnique_pos_mul_inner_of_adjoint hpos hdef
  intro T x y
  obtain ⟨a, rfl⟩ := hsurj T
  rw [adjoint_map_eq_map_conjStar ρ hρ]
  exact sesqForm_map_eq_map_conjStar ρ H hH a x y

end Hermitian

section Uniqueness

variable [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)

/-- For a full endomorphism-algebra Clifford action, two positive definite compatible Hermitian
forms differ by a unique positive real scalar. This is
`CliffordAlgebra.existsUnique_pos_mul_inner_of_surjective` without a fixed inner product on `S`:
the reference form `H₀` takes its place. -/
theorem existsUnique_pos_mul_of_surjective [Nontrivial S] (hsurj : Function.Surjective ρ)
    (H₀ : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ) (hH₀ : H₀.IsPosSemidef) (hdef₀ : ∀ x : S, x ≠ 0 → H₀ x x ≠ 0)
    (hH₀ρ : ∀ (v : V) x y,
      H₀ (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x) y =
        -H₀ x (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) y))
    (H : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ) (hpos : H.IsNonneg) (hdef : ∀ x : S, x ≠ 0 → H x x ≠ 0)
    (hH : ∀ (v : V) x y,
      H (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x) y =
        -H x (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) y)) :
    ∃! r : ℝ, 0 < r ∧ ∀ x y, H x y = (r : ℂ) * H₀ x y := by
  -- Make `H₀` the inner product of `S`.
  let core : InnerProductSpace.Core ℂ S :=
    { inner x y := H₀ x y
      conj_inner_symm x y := hH₀.isSymm.eq y x
      re_inner_nonneg x := (RCLike.nonneg_iff.mp (hH₀.isNonneg.nonneg x)).1
      add_left x y z := by simp
      smul_left x y r := by simp
      definite x hx := by_contra fun h ↦ hdef₀ x h hx }
  let := core.toNormedAddCommGroup
  let := InnerProductSpace.ofCore core.toCore
  -- `InnerProductSpace.ofCore` takes its inner product from the core, which is `H₀`.
  have hinner (x y : S) : inner ℂ x y = H₀ x y := rfl
  simp_rw [← hinner]
  refine existsUnique_pos_mul_inner_of_surjective ρ hsurj (fun v ↦ ?_) H hpos hdef hH
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [hinner, hH₀ρ]

end Uniqueness

end CliffordAlgebra
