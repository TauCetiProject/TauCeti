/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.RingTheory.Length
import Mathlib.LinearAlgebra.Quotient.Pi
import TauCeti.LinearAlgebra.Dimension.Localization

/-!
# The cokernel length of an injective endomorphism

For an injective endomorphism `φ` of an `A`-module `M`, the length of its cokernel `M ⧸ φ(M)` is
the invariant `e_A(φ, M)` of Fulton, *Intersection Theory*, Appendix A.2, in the case where the
kernel vanishes. This file records the two properties of it on which the comparison of orders of
vanishing with norms rests:

* `TauCeti.length_quotient_range_comp`: it is additive under composition,
  `e(φ ∘ ψ) = e(φ) + e(ψ)`;
* `TauCeti.length_quotient_range_restrict`: it does not change when `M` is replaced by a submodule
  `N` with `φ(N) ⊆ N` and `M ⧸ N` of finite length.

Both are read off the length of a quotient of `M` along two filtrations. An injective `φ` maps `M`
isomorphically onto `φ(M)`, carrying any submodule `N` to `φ(N)`, so that
`φ(M) ⧸ φ(N) ≃ M ⧸ N` (`TauCeti.length_quotient_comap_subtype_range_map`).

For a non-zero-divisor `a` and an ideal `I` with `A ⧸ I` of finite length, the second property
gives `length (I ⧸ aI) = ord_A a` (`TauCeti.length_quotient_lsmul_ideal_eq_ord`). For the scalar
endomorphisms of a finitely generated torsion-free module `M` over a Noetherian domain of dimension
at most one, `length (M ⧸ aM) = rank M * ord_A a`
(`TauCeti.length_quotient_lsmul_eq_finrank_mul_ord`). The proof replaces `M` by a free submodule
of full rank with torsion quotient (`TauCeti.exists_linearIndependent_smul_mem_span`, a
repackaging of Mathlib's `exists_linearIndepOn_smul_mem_span`), on which the cokernel is
`(A ⧸ aA)^rank`.
-/

public section

namespace TauCeti

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- **Additivity of cokernel length.** For an injective endomorphism `φ` and any endomorphism `ψ`,
`length (M ⧸ φψ(M)) = length (M ⧸ φ(M)) + length (M ⧸ ψ(M))`. -/
theorem length_quotient_range_comp {φ : M →ₗ[A] M} (hφ : Function.Injective φ) (ψ : M →ₗ[A] M) :
    Module.length A (M ⧸ LinearMap.range (φ ∘ₗ ψ)) =
      Module.length A (M ⧸ LinearMap.range φ) + Module.length A (M ⧸ LinearMap.range ψ) := by
  rw [LinearMap.range_comp, length_quotient_eq_length_quotient_comap_subtype_add
    (LinearMap.map_le_range (f := φ)), length_quotient_comap_subtype_range_map hφ, add_comm]

/-- **Cokernel length is insensitive to finite-length enlargement.** Let `φ` be an injective
endomorphism of `M` and `N` a submodule with `φ(N) ⊆ N` and `M ⧸ N` of finite length. Then the
cokernels of `φ` on `N` and on `M` have the same length. -/
theorem length_quotient_range_restrict {φ : M →ₗ[A] M} (hφ : Function.Injective φ)
    {N : Submodule A M} (h : ∀ x ∈ N, φ x ∈ N) (hN : IsFiniteLength A (M ⧸ N)) :
    Module.length A (↥N ⧸ LinearMap.range (φ.restrict h)) =
      Module.length A (M ⧸ LinearMap.range φ) := by
  -- `M ⧸ φ(N)` is filtered both by `N ⧸ φ(N)` and `M ⧸ N`, and by `φ(M) ⧸ φ(N) ≃ M ⧸ N` and
  -- `M ⧸ φ(M)`; the common finite term `length (M ⧸ N)` cancels.
  have hle : N.map φ ≤ N := Submodule.map_le_iff_le_comap.2 h
  have hr : LinearMap.range (φ.restrict h) = (N.map φ).comap N.subtype := by
    rw [LinearMap.range_eq_map, LinearMap.map_restrict, Submodule.map_subtype_top]
  have h₁ := length_quotient_eq_length_quotient_comap_subtype_add hle
  rw [length_quotient_eq_length_quotient_comap_subtype_add (LinearMap.map_le_range (f := φ)),
    length_quotient_comap_subtype_range_map hφ, ← hr] at h₁
  have hfin : Module.length A (M ⧸ N) ≠ ⊤ := Module.length_ne_top_iff.2 hN
  exact (WithTop.add_right_cancel hfin ((add_comm _ _).trans h₁)).symm

section Scalar

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Multiplication by `a` on `Aⁿ` has cokernel `(A ⧸ aA)ⁿ`, of length `n * ord_A a`. -/
theorem length_quotient_lsmul_pi (ι : Type*) [Fintype ι] (a : A) :
    Module.length A ((ι → A) ⧸ LinearMap.range (LinearMap.lsmul A (ι → A) a)) =
      Fintype.card ι * Ring.ord A a := by
  have hpi : LinearMap.range (LinearMap.lsmul A (ι → A) a) =
      Submodule.pi Set.univ fun _ ↦ Ideal.span {a} := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_pi, Set.mem_univ,
      forall_const, Ideal.mem_span_singleton', funext_iff, Pi.smul_apply, smul_eq_mul, mul_comm a]
    exact ⟨fun ⟨y, hy⟩ i ↦ ⟨y i, hy i⟩, fun h ↦ by choose y hy using h; exact ⟨y, hy⟩⟩
  classical
  rw [hpi, (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Ring.ord]

/-- **The length of `I ⧸ aI` for an ideal `I`.** For an ideal `I` with `A ⧸ I` of finite length
and a non-zero-divisor `a`, `length (I ⧸ aI)` is the order of vanishing `Ring.ord A a`, which is
by definition `length (A ⧸ aA)`: the cokernel of multiplication by `a` does not change when `A` is
replaced by `I` (`TauCeti.length_quotient_range_restrict`). -/
theorem length_quotient_lsmul_ideal_eq_ord (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) (a : A)
    (ha : a ∈ nonZeroDivisors A) :
    Module.length A (↥I ⧸ LinearMap.range (LinearMap.lsmul A ↥I a)) = Ring.ord A a := by
  have hinj : Function.Injective (LinearMap.lsmul A A a) := fun x y h ↦
    (isRegular_iff_mem_nonZeroDivisors.mpr ha).left (by simpa using h)
  have hI' : ∀ x ∈ I, LinearMap.lsmul A A a x ∈ I := fun x hx ↦ I.smul_mem a hx
  have hres : (LinearMap.lsmul A A a).restrict hI' = LinearMap.lsmul A I a := by
    ext; simp
  have hspan : LinearMap.range (LinearMap.lsmul A A a) = Ideal.span {a} := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm a]
  rw [← hres, length_quotient_range_restrict hinj hI' hI, hspan, Ring.ord]

variable [IsDomain A] [Module.IsTorsionFree A M]

/-- **Cokernel length of a scalar.** Over a Noetherian domain `A` of dimension at most one,
multiplication by a nonzero `a` on a finitely generated torsion-free module `M` has cokernel of
length `rank_A M * ord_A a`. -/
theorem length_quotient_lsmul_eq_finrank_mul_ord [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite A M] {a : A} (ha : a ≠ 0) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a)) =
      Module.finrank A M * Ring.ord A a := by
  -- A free submodule `F ≃ A^rank` with `M ⧸ F` torsion, hence of finite length, has the same
  -- cokernel length under multiplication by `a` as `M`.
  obtain ⟨n, v, c, hv, hc, hcM, hrank⟩ := exists_linearIndependent_smul_mem_span (A := A) (M := M)
  set F := Submodule.span A (Set.range v)
  have hfin : IsFiniteLength A (M ⧸ F) := by
    refine isFiniteLength_of_nonZeroDivisor_mem_annihilator (x := c) ?_
      (mem_nonZeroDivisors_of_ne_zero hc)
    rw [Module.mem_annihilator]
    rintro ⟨m⟩
    exact (Submodule.Quotient.mk_eq_zero F).2 (hcM m)
  have hinj : Function.Injective (LinearMap.lsmul A M a) := smul_right_injective M ha
  have hF : ∀ x ∈ F, LinearMap.lsmul A M a x ∈ F := fun x hx ↦ F.smul_mem a hx
  have hres : (LinearMap.lsmul A M a).restrict hF = LinearMap.lsmul A F a := by
    ext; simp
  rw [← length_quotient_range_restrict hinj hF hfin, hres,
    length_quotient_lsmul_congr (Module.Basis.span hv).equivFun,
    length_quotient_lsmul_pi (Fin n) a, hrank, Fintype.card_fin]

end Scalar

end TauCeti
