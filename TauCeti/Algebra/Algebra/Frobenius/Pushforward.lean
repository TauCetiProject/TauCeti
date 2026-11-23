/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Pushforward along a map out of a Frobenius algebra

Let `A` be a finite-dimensional algebra over a field `k` with a Frobenius functional `φ`, so that
`(a, a') ↦ φ (a * a')` is a perfect pairing, and let `B` be any `k`-algebra with a linear
functional `ψ`. Every linear map `f : A →ₗ[k] B` then has a unique adjoint
`hφ.pushforward ψ f : B →ₗ[k] A` for the two trace pairings:

`φ (hφ.pushforward ψ f b * a) = ψ (b * f a)` for all `a : A` and `b : B`.

No hypothesis on `ψ` is needed for existence and uniqueness: they come from the perfectness of the
pairing on `A` alone.

This is the pushforward `π_*` in cohomology, defined by duality from the pullback `π^*`. For a
proper map `π : X → Y` of spaces whose rational cohomology carries a perfect pairing
`(α, β) ↦ ∫_Y α ⌣ β`, the pushforward is the adjoint of `f = π^*`, read with
`A = H^*(Y)`, `B = H^*(X)`, `φ = ∫_Y` and `ψ = ∫_X`. In particular the integrals may be weighted
integrals of orbifolds, for which the pushforward is the weighted adjoint of the pullback. Its
standard properties follow from the defining identity alone:

* the projection formula `π_*(b ⌣ π^* a) = π_* b ⌣ a`, for `f` an algebra homomorphism,
  using only associativity, so graded-commutative algebras such as cohomology rings are included
  (`LinearMap.IsFrobeniusFunctional.pushforward_mul_map`);
* functoriality `(π ∘ π')_* = π_* ∘ π'_*` (`LinearMap.IsFrobeniusFunctional.pushforward_comp`) and
  `id_* = id` (`LinearMap.IsFrobeniusFunctional.pushforward_id`);
* the pushforward to a point is the integral
  (`LinearMap.IsFrobeniusFunctional.pushforward_algebraLinearMap`);
* for gradings in which `φ` and `ψ` vanish off the top degrees `dA` and `dB` and `f` preserves
  degrees, the pushforward raises degree by `dA - dB`, the dimension of the target minus that of
  the source (`LinearMap.IsFrobeniusFunctional.pushforward_mem_graded`).

## Main definitions

* `LinearMap.IsFrobeniusFunctional.pushforward`: the adjoint of a linear map out of a Frobenius
  algebra for the two trace pairings.

## Main results

* `LinearMap.IsFrobeniusFunctional.apply_pushforward_mul`: the defining adjunction identity.
* `LinearMap.IsFrobeniusFunctional.eq_pushforward_iff` and
  `LinearMap.IsFrobeniusFunctional.isAdjointPair_iff_eq_pushforward`: the pushforward is the
  unique map with this property, in elementwise form and as Mathlib's `LinearMap.IsAdjointPair`.
* `LinearMap.IsFrobeniusFunctional.pushforward_mul_map`: the projection formula.
* `LinearMap.IsFrobeniusFunctional.pushforward_comp` and
  `LinearMap.IsFrobeniusFunctional.pushforward_id`: functoriality.
* `LinearMap.IsFrobeniusFunctional.pushforward_mem_graded`: the degree of the pushforward.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer (1982), Chapter I, §6, for the pushforward by integration along the
  fibre and its projection formula.
* M. Kontsevich and Yu. Manin, *Gromov–Witten classes, quantum cohomology, and enumerative
  geometry*, Comm. Math. Phys. 164 (1994), 525–562, §2, where the pushforwards along forgetful and
  clutching maps of moduli of stable curves enter the axioms of Gromov–Witten classes.
-/

public section

noncomputable section

open DirectSum

namespace LinearMap.IsFrobeniusFunctional

variable {k A B C : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Ring B] [Algebra k B] [Ring C] [Algebra k C] {φ : A →ₗ[k] k}

/-- The **pushforward** along a linear map `f : A →ₗ[k] B` out of the Frobenius algebra `(A, φ)`:
the map `B →ₗ[k] A` adjoint to `f` for the trace pairings `(a, a') ↦ φ (a * a')` on `A` and
`(b, b') ↦ ψ (b * b')` on `B`, characterized by `φ (hφ.pushforward ψ f b * a) = ψ (b * f a)`
(`LinearMap.IsFrobeniusFunctional.apply_pushforward_mul`). For `f` the pullback `π^*` in
cohomology and `φ`, `ψ` the integrals, this is the pushforward `π_*`. -/
def pushforward (hφ : φ.IsFrobeniusFunctional) (ψ : B →ₗ[k] k) (f : A →ₗ[k] B) :
    B →ₗ[k] A :=
  hφ.toDualEquiv.symm.toLinearMap ∘ₗ ((LinearMap.mul k B).compr₂ ψ).compl₂ f

variable (hφ : φ.IsFrobeniusFunctional) (ψ : B →ₗ[k] k) (f : A →ₗ[k] B)

/-- The defining identity of the pushforward: it is adjoint to `f` for the two trace pairings. -/
@[simp]
theorem apply_pushforward_mul (b : B) (a : A) :
    φ (hφ.pushforward ψ f b * a) = ψ (b * f a) := by
  rw [← hφ.toDualEquiv_apply_apply, pushforward, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  simp

/-- The pushforward of `b` is the unique element whose pairing with every `a` is `ψ (b * f a)`. -/
theorem eq_pushforward_iff {b : B} {x : A} :
    x = hφ.pushforward ψ f b ↔ ∀ a, φ (x * a) = ψ (b * f a) := by
  refine ⟨by rintro rfl; simp, fun h ↦ hφ.toDualEquiv.injective (LinearMap.ext fun a ↦ ?_)⟩
  simp [h]

/-- The pushforward and `f` form an adjoint pair for the trace pairings of `ψ` and `φ`. -/
theorem isAdjointPair_pushforward :
    IsAdjointPair ((LinearMap.mul k B).compr₂ ψ) ((LinearMap.mul k A).compr₂ φ)
      (hφ.pushforward ψ f) f :=
  fun b a ↦ by simp

/-- The pushforward is the only map adjoint to `f` for the trace pairings of `ψ` and `φ`. -/
theorem isAdjointPair_iff_eq_pushforward {g : B →ₗ[k] A} :
    IsAdjointPair ((LinearMap.mul k B).compr₂ ψ) ((LinearMap.mul k A).compr₂ φ) g f ↔
      g = hφ.pushforward ψ f := by
  refine ⟨fun h ↦ LinearMap.ext fun b ↦ (hφ.eq_pushforward_iff ψ f).2 fun a ↦ ?_, ?_⟩
  · simpa using h b a
  · rintro rfl
    exact hφ.isAdjointPair_pushforward ψ f

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem pushforward_id : hφ.pushforward φ LinearMap.id = LinearMap.id :=
  LinearMap.ext fun _ ↦ ((hφ.eq_pushforward_iff φ LinearMap.id).2 fun _ ↦ rfl).symm

/-- **Functoriality of the pushforward**: `(g ∘ f)_* = f_* ∘ g_*`. -/
theorem pushforward_comp [FiniteDimensional k B] {ψ : B →ₗ[k] k}
    (hψ : ψ.IsFrobeniusFunctional) (χ : C →ₗ[k] k) (f : A →ₗ[k] B) (g : B →ₗ[k] C) :
    hφ.pushforward χ (g ∘ₗ f) = hφ.pushforward ψ f ∘ₗ hψ.pushforward χ g :=
  LinearMap.ext fun c ↦ ((hφ.eq_pushforward_iff χ (g ∘ₗ f)).2 fun a ↦ by simp).symm

/-- **The projection formula**: for an algebra homomorphism `f`, the pushforward is a map of right
`A`-modules, `f_* (b * f a) = f_* b * a`. Only associativity enters, so the algebras need not be
commutative. -/
theorem pushforward_mul_map (f : A →ₐ[k] B) (b : B) (a : A) :
    hφ.pushforward ψ f.toLinearMap (b * f a) = hφ.pushforward ψ f.toLinearMap b * a :=
  ((hφ.eq_pushforward_iff ψ f.toLinearMap).2 fun c ↦ by simp [mul_assoc]).symm

/-- The pushforward of a pulled-back element is the pushforward of `1` times that element,
`f_* (f a) = f_* 1 * a`. -/
theorem pushforward_map (f : A →ₐ[k] B) (a : A) :
    hφ.pushforward ψ f.toLinearMap (f a) = hφ.pushforward ψ f.toLinearMap 1 * a := by
  simpa using hφ.pushforward_mul_map ψ f 1 a

/-- **The pushforward to a point is the integral**: on the base field with the identity as
Frobenius functional, the pushforward along the structure map `k → B` is `ψ` itself. -/
@[simp]
theorem pushforward_algebraLinearMap (h : (LinearMap.id : k →ₗ[k] k).IsFrobeniusFunctional) :
    h.pushforward ψ (Algebra.linearMap k B) = ψ :=
  LinearMap.ext fun b ↦ ((h.eq_pushforward_iff ψ _).2 fun a ↦ by
    simp [← Algebra.commutes, ← Algebra.smul_def, mul_comm]).symm

section Grading

variable {ι : Type*} [AddCommGroup ι] [DecidableEq ι] (𝒜 : ι → Submodule k A) [GradedAlgebra 𝒜]
  (ℬ : ι → Submodule k B) [SetLike.GradedMul ℬ] {dA dB : ι}

/-- **The degree of the pushforward.** If `φ` vanishes off the top degree `dA` of `A`, `ψ`
vanishes off the top degree `dB` of `B`, and `f` preserves degrees, then the pushforward raises
degrees by `dA - dB`. For cohomology this is the shift by the dimension of the target minus the
dimension of the source. -/
theorem pushforward_mem_graded (hφ0 : ∀ i ≠ dA, ∀ a ∈ 𝒜 i, φ a = 0)
    (hψ0 : ∀ i ≠ dB, ∀ b ∈ ℬ i, ψ b = 0) (hf : ∀ i, ∀ a ∈ 𝒜 i, f a ∈ ℬ i) {j : ι} {b : B}
    (hb : b ∈ ℬ j) : hφ.pushforward ψ f b ∈ 𝒜 (j + (dA - dB)) := by
  classical
  set x := hφ.pushforward ψ f b
  -- Every component of `x` off the expected degree pairs to zero with each homogeneous element,
  -- either for degree reasons in `A` or, through the adjunction, for degree reasons in `B`.
  have hcomp : ∀ i ≠ j + (dA - dB), (decompose 𝒜 x i : A) = 0 := by
    intro i hi
    refine hφ.eq_zero_of_forall_left fun c ↦ ?_
    conv_lhs => rw [← sum_support_decompose 𝒜 c]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    by_cases hil : i + l = dA
    · rw [TauCeti.GradedAlgebra.apply_coe_decompose_mul_of_forall_ne 𝒜 hφ0 x
        (SetLike.coe_mem _) hil, apply_pushforward_mul]
      refine hψ0 (j + l) (fun h ↦ hi ?_) _
        (SetLike.GradedMul.mul_mem hb (hf l _ (SetLike.coe_mem _)))
      rw [← hil, ← h]
      abel
    · exact hφ0 _ hil _ (SetLike.GradedMul.mul_mem (SetLike.coe_mem _) (SetLike.coe_mem _))
  rw [← sum_support_decompose 𝒜 x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases hi : i = j + (dA - dB)
  · subst hi
    exact SetLike.coe_mem _
  · rw [hcomp i hi]
    exact zero_mem _

end Grading

end LinearMap.IsFrobeniusFunctional
