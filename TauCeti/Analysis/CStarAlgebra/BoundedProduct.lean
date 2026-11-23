/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The bounded product of C⋆-algebras

For a family of nonzero unital C⋆-algebras `A i`, the bounded product `lp A ∞` is a unital
C⋆-algebra, `lp.inftyCStarAlgebra`. Mathlib provides the nonunital instance and the unital
commutative one; nontriviality of the factors makes the unit `(1)ᵢ` have norm one.

With the closed `c₀` ideal `lp.c0Ideal` of `TauCeti.Analysis.Normed.Lp.C0Ideal`, the quotient
`lp A ∞ ⧸ lp.c0Ideal A` is then a unital C⋆-algebra by `TwoSidedIdeal.Quotient.cstarAlgebra`.

For a family of possibly nonunital C⋆-algebras, `lp A ∞` is the product in the category of
C⋆-algebras: the coordinate projections `lp.evalNonUnitalStarAlgHom` are star homomorphisms, and
`lp.liftNonUnitalStarAlgHom` identifies star homomorphisms into `lp A ∞` with families of star
homomorphisms into the factors. A family of star homomorphisms out of a C⋆-algebra is uniformly
bounded because each of them is contractive. The underlying construction,
`lp.piNonUnitalStarAlgHom`, takes any star algebra as source and any pointwise bounded family of
star homomorphisms into normed star rings.

The file also records the behaviour of the families `lp.single p i a` supported at one index
under multiplication and `star`, and `lp.hasSum_single_of_tendsto_cofinite`: a bounded family
vanishing at infinity is the sum of its coordinates.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open scoped ENNReal

namespace lp

section Product

section Eval

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalNormedRing (A i)] [∀ i, StarAddMonoid (A i)]
  [∀ i, NormedStarGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, IsBoundedSMul ℂ (A i)]

variable (A) in
/-- The coordinate projection of the bounded product `lp A ∞` onto its factor `A i`, as a star
homomorphism. -/
def evalNonUnitalStarAlgHom (i : ι) : lp A ∞ →⋆ₙₐ[ℂ] A i where
  toFun a := a i
  map_smul' c a := by simp [lp.coeFn_smul]
  map_zero' := by simp
  map_add' a b := by simp
  map_mul' a b := by simp [infty_coeFn_mul]
  map_star' a := lp.star_apply a i

/-- The coordinate projection evaluates a bounded family at an index. -/
@[simp]
theorem evalNonUnitalStarAlgHom_apply (i : ι) (a : lp A ∞) :
    evalNonUnitalStarAlgHom A i a = a i :=
  (rfl)

variable (A) in
/-- The coordinate projections of the bounded product are surjective. -/
theorem evalNonUnitalStarAlgHom_surjective (i : ι) :
    Function.Surjective (evalNonUnitalStarAlgHom A i) := by
  classical
  exact fun a ↦ ⟨lp.single ∞ i a, by simp⟩

/-- Two star homomorphisms into a bounded product agree when all their coordinates agree. -/
@[ext]
theorem nonUnitalStarAlgHom_ext {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B]
    [Star B] {φ ψ : B →⋆ₙₐ[ℂ] lp A ∞}
    (h : ∀ i, (evalNonUnitalStarAlgHom A i).comp φ = (evalNonUnitalStarAlgHom A i).comp ψ) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun b ↦ lp.ext <| funext fun i ↦ by
    simpa using congr($(h i) b)

variable {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B] [Star B]

/-- A family of star homomorphisms `φ i : B → A i` that is bounded at every `b` gives the star
homomorphism `b ↦ (φ i b)ᵢ` into the bounded product. `B` needs no norm. -/
noncomputable def piNonUnitalStarAlgHom (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Memℓp (fun i ↦ φ i b) ∞) : B →⋆ₙₐ[ℂ] lp A ∞ where
  toFun b := ⟨fun i ↦ φ i b, hφ b⟩
  map_smul' c b := lp.ext <| funext fun i ↦ map_smul (φ i) c b
  map_zero' := lp.ext <| funext fun i ↦ map_zero (φ i)
  map_add' b b' := lp.ext <| funext fun i ↦ map_add (φ i) b b'
  map_mul' b b' := lp.ext <| funext fun i ↦ map_mul (φ i) b b'
  map_star' b := lp.ext <| funext fun i ↦ map_star (φ i) b

/-- The `i`-th coordinate of `lp.piNonUnitalStarAlgHom φ hφ b` is `φ i b`. -/
@[simp]
theorem piNonUnitalStarAlgHom_apply_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Memℓp (fun i ↦ φ i b) ∞) (b : B) (i : ι) :
    piNonUnitalStarAlgHom φ hφ b i = φ i b :=
  (rfl)

end Eval

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]
variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- **The universal property of the bounded product**: star homomorphisms from a C⋆-algebra `B`
into `lp A ∞` are the families of star homomorphisms `B → A i`. The family `φ` is sent to
`lp.piNonUnitalStarAlgHom φ`, `b ↦ (φ i b)ᵢ`, which is bounded by `‖b‖` since star homomorphisms
between C⋆-algebras are contractive. -/
noncomputable def liftNonUnitalStarAlgHom : (∀ i, B →⋆ₙₐ[ℂ] A i) ≃ (B →⋆ₙₐ[ℂ] lp A ∞) where
  toFun φ := piNonUnitalStarAlgHom φ fun b ↦ memℓp_infty ⟨‖b‖, by
    rintro _ ⟨i, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (φ i) b⟩
  invFun ψ i := (evalNonUnitalStarAlgHom A i).comp ψ
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

/-- The `i`-th coordinate of `lp.liftNonUnitalStarAlgHom φ b` is `φ i b`. -/
@[simp]
theorem liftNonUnitalStarAlgHom_apply_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i) (b : B) (i : ι) :
    liftNonUnitalStarAlgHom φ b i = φ i b :=
  (rfl)

/-- The coordinates of `lp.liftNonUnitalStarAlgHom φ` are the members of the family `φ`. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_liftNonUnitalStarAlgHom (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (i : ι) : (evalNonUnitalStarAlgHom A i).comp (liftNonUnitalStarAlgHom φ) = φ i := by
  ext b
  simp

/-- The inverse of `lp.liftNonUnitalStarAlgHom` takes the coordinates of a star homomorphism. -/
@[simp]
theorem liftNonUnitalStarAlgHom_symm_apply (ψ : B →⋆ₙₐ[ℂ] lp A ∞) (i : ι) :
    liftNonUnitalStarAlgHom.symm ψ i = (evalNonUnitalStarAlgHom A i).comp ψ :=
  (rfl)

/-- A star homomorphism into the bounded product is the lift of its coordinates. -/
@[simp]
theorem liftNonUnitalStarAlgHom_evalNonUnitalStarAlgHom_comp (ψ : B →⋆ₙₐ[ℂ] lp A ∞) :
    liftNonUnitalStarAlgHom (fun i ↦ (evalNonUnitalStarAlgHom A i).comp ψ) = ψ :=
  liftNonUnitalStarAlgHom.apply_symm_apply ψ

variable (A) in
/-- The lift of the coordinate projections is the identity of the bounded product. -/
@[simp]
theorem liftNonUnitalStarAlgHom_evalNonUnitalStarAlgHom :
    liftNonUnitalStarAlgHom (evalNonUnitalStarAlgHom A) = NonUnitalStarAlgHom.id ℂ (lp A ∞) := by
  ext
  simp

/-- Precomposing a lift with a star homomorphism `g` lifts the precomposed family. -/
theorem liftNonUnitalStarAlgHom_comp {C : Type*} [NonUnitalCStarAlgebra C]
    (φ : ∀ i, B →⋆ₙₐ[ℂ] A i) (g : C →⋆ₙₐ[ℂ] B) :
    (liftNonUnitalStarAlgHom φ).comp g = liftNonUnitalStarAlgHom fun i ↦ (φ i).comp g := by
  ext
  simp

end Product

section Single

variable {ι : Type*} [DecidableEq ι]

/-- The family supported at `i` with value `a * b` is the product of those with values `a` and
`b`. -/
theorem single_mul_single {A : ι → Type*} [∀ i, NonUnitalNormedRing (A i)] (i : ι) (a b : A i) :
    lp.single ∞ i (a * b) = lp.single ∞ i a * lp.single ∞ i b :=
  lp.ext <| by rw [infty_coeFn_mul, lp.coeFn_single, lp.coeFn_single, lp.coeFn_single,
    Pi.single_mul]

/-- The family supported at `i` with value `star a` is the adjoint of the one with value `a`. -/
theorem single_star {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, StarAddMonoid (E i)]
    [∀ i, NormedStarGroup (E i)] (p : ℝ≥0∞) (i : ι) (a : E i) :
    lp.single p i (star a) = star (lp.single p i a) :=
  lp.ext <| funext fun j ↦ by
    rw [lp.star_apply, lp.coeFn_single, lp.coeFn_single, Pi.single_star, Pi.star_apply]

/-- A bounded family whose coordinate norms tend to `0` along the cofinite filter is the sum in
`lp E ∞` of its coordinates, each placed at its index. -/
theorem hasSum_single_of_tendsto_cofinite {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {a : lp E ∞} (ha : Filter.Tendsto (fun i ↦ ‖a i‖) Filter.cofinite (nhds 0)) :
    HasSum (fun i ↦ lp.single ∞ i (a i)) a := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hfin := ha.eventually (gt_mem_nhds (half_pos hε))
  refine ⟨(Filter.eventually_cofinite.1 hfin).toFinset, fun s hs ↦ ?_⟩
  rw [dist_eq_norm]
  refine (lp.norm_le_of_forall_le (half_pos hε).le fun j ↦ ?_).trans_lt (half_lt_self hε)
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hj
  · simpa using (half_pos hε).le
  · have hj' : ‖a j‖ < ε / 2 := by
      by_contra h
      exact hj (hs (by simpa using h))
    simpa using hj'.le

end Single

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The bounded product `lp A ∞` of nonzero unital C⋆-algebras is a unital C⋆-algebra. -/
noncomputable instance inftyCStarAlgebra : CStarAlgebra (lp A ∞) where

end lp
