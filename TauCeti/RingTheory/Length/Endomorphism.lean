/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.RingTheory.Length
import Mathlib.RingTheory.KrullDimension.PID
import TauCeti.LinearAlgebra.Dimension.Localization
import TauCeti.LinearAlgebra.Matrix.Diagonal.Length

/-!
# Cokernel lengths of endomorphisms

For an injective endomorphism `φ` of an `A`-module `M`, the length of its cokernel `M ⧸ φ(M)` is
the invariant `e_A(φ, M)` of Fulton, *Intersection Theory*, Appendix A.2, in the case where the
kernel vanishes. This file records the two properties of it on which the comparison of orders of
vanishing with norms rests, subadditivity bounds for endomorphisms that need not be injective, and
bounds on the colength of submodules containing `aM`. The two properties are:

* `TauCeti.length_quotient_range_comp`: it is additive under composition,
  `e(φ ∘ ψ) = e(φ) + e(ψ)`;
* `TauCeti.length_quotient_range_restrict`: it does not change when `M` is replaced by a submodule
  `N` with `φ(N) ⊆ N` and `M ⧸ N` of finite length.

These two properties are read off the length of a quotient of `M` along two filtrations. An
injective `φ` maps `M` isomorphically onto `φ(M)`, carrying any submodule `N` to `φ(N)`, so that
`φ(M) ⧸ φ(N) ≃ M ⧸ N` (`TauCeti.length_quotient_comap_subtype_range_map`).

For endomorphisms that need not be injective, the cokernel length is subadditive:
`length (M ⧸ φψ(M)) ≤ length (M ⧸ φ(M)) + length (M ⧸ ψ(M))`
(`TauCeti.length_quotient_range_comp_le`), hence at most the sum over the factors of a product
(`TauCeti.length_quotient_range_list_prod_le`) and `m` times that of `φ` for `φ ^ m`
(`TauCeti.length_quotient_range_pow_le`). The same holds inside a submodule `N`, with the colength
of `N ⊓ φ(N)` in `N` in place of the cokernel and no hypothesis `φ(N) ⊆ N`
(`TauCeti.length_quotient_comap_subtype_map_comp_le`,
`TauCeti.length_quotient_comap_subtype_map_list_prod_le`,
`TauCeti.length_quotient_comap_subtype_map_pow_le`). The cokernel forms are the case `N = ⊤` of
the submodule forms.

For a non-zero-divisor `a` and an ideal `I` with `A ⧸ I` of finite length,
`TauCeti.length_quotient_range_restrict` gives `length (I ⧸ aI) = ord_A a`
(`TauCeti.length_quotient_lsmul_ideal_eq_ord`). For the scalar endomorphisms of a finitely
generated torsion-free module `M` over a Noetherian domain of dimension at most one,
`length (M ⧸ aM) = rank M * ord_A a`
(`TauCeti.length_quotient_lsmul_eq_finrank_mul_ord`). The proof replaces `M` by a free submodule
of full rank with torsion quotient (`TauCeti.exists_linearIndependent_smul_mem_span`, a
repackaging of Mathlib's `exists_linearIndepOn_smul_mem_span`), on which the cokernel is
`(A ⧸ aA)^rank`.
Consequently `length (M ⧸ T) ≤ rank M * ord_A a` for a submodule `T ⊇ aM`
(`TauCeti.length_quotient_le_finrank_mul_ord`), which over a principal ideal domain with an
irreducible `ϖ` reads `length (M ⧸ T) ≤ e * rank M` for `T ⊇ ϖ ^ e M`
(`TauCeti.length_quotient_le_mul_finrank`).

For a module with a finite basis, the cokernel of an endomorphism is the cokernel of its matrix
(`Module.Basis.length_quotient_range_eq_length_quotient_range_toMatrix`).
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

/-- **Subadditivity of colength in a submodule.** For a submodule `N` of `M` and endomorphisms
`φ, ψ` of `M`, the colength of `N ⊓ φψ(N)` in `N` is at most the sum of those of `N ⊓ φ(N)` and
`N ⊓ ψ(N)`: in `ℕ∞`,
`length (N ⧸ (N ⊓ φψ(N))) ≤ length (N ⧸ (N ⊓ φ(N))) + length (N ⧸ (N ⊓ ψ(N)))`.
No inclusion `φ(N) ⊆ N` or `ψ(N) ⊆ N` is assumed; when they hold, these are the cokernels of the
restrictions of `φ ∘ₗ ψ`, `φ` and `ψ` to `N`. -/
theorem length_quotient_comap_subtype_map_comp_le (N : Submodule A M) (φ ψ : M →ₗ[A] M) :
    Module.length A (↥N ⧸ (N.map (φ ∘ₗ ψ)).comap N.subtype) ≤
      Module.length A (↥N ⧸ (N.map φ).comap N.subtype) +
        Module.length A (↥N ⧸ (N.map ψ).comap N.subtype) := by
  -- `W` is the part of `N` that `φ` maps into `N`; `φ(W) = N ⊓ φ(N)`.
  set W := N ⊓ N.comap φ
  have hW : ∀ x ∈ W, φ x ∈ N := fun _ hx ↦ hx.2
  have hr : LinearMap.range (φ.restrict hW) = (N.map φ).comap N.subtype := by
    ext ⟨y, hy⟩
    simp only [LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_map, Subtype.ext_iff, LinearMap.coe_restrict_apply]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, x.property.1, hx⟩,
      fun ⟨x, hx, hxy⟩ ↦ ⟨⟨x, hx, by rwa [← hxy] at hy⟩, hxy⟩⟩
  set Y := (N.map (φ ∘ₗ ψ)).comap N.subtype
  set f := Y.mkQ ∘ₗ φ.restrict hW
  -- `N ⧸ (N ⊓ φψ(N))` is filtered by the range of `f`, the image of `φ(W)`, and by
  -- `N ⧸ (N ⊓ φ(N))`.
  rw [length_quotient_eq_length_map_add_length_quotient_sup (LinearMap.range (φ.restrict hW)) Y,
    ← LinearMap.range_comp, add_comm]
  refine add_le_add ((length_quotient_anti le_sup_right).trans_eq (by rw [hr])) ?_
  -- An element of `W ⊓ ψ(N)` is killed by `f`.
  have hK : (N.map ψ).comap W.subtype ≤ LinearMap.ker f := by
    rintro x ⟨y, hy, hyx⟩
    simp only [f, Y, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.coe_restrict_apply]
    exact ⟨y, hy, by rw [LinearMap.comp_apply, hyx, Submodule.subtype_apply]⟩
  exact (length_range_le_length_quotient f hK).trans
    (length_quotient_comap_subtype_mono inf_le_left _)

/-- **Colength of a product in a submodule.** For a submodule `N` of `M` and a list `l` of
endomorphisms of `M`, the colength of `N ⊓ (l.prod)(N)` in `N` is at most the sum over `φ ∈ l` of
the colengths of `N ⊓ φ(N)`, in `ℕ∞`. -/
theorem length_quotient_comap_subtype_map_list_prod_le (N : Submodule A M)
    (l : List (Module.End A M)) :
    Module.length A (↥N ⧸ (N.map l.prod).comap N.subtype) ≤
      (l.map fun φ ↦ Module.length A (↥N ⧸ (N.map φ).comap N.subtype)).sum := by
  induction l with
  | nil =>
    rw [List.prod_nil, Module.End.one_eq_id, Submodule.map_id, Submodule.comap_subtype_self]
    simp [Module.length_eq_zero]
  | cons φ l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons, Module.End.mul_eq_comp]
    exact (length_quotient_comap_subtype_map_comp_le N φ l.prod).trans (add_le_add_right ih _)

/-- **Colength of a power in a submodule.** For a submodule `N` of `M`, an endomorphism `φ` of `M`
and `m : ℕ`, `length (N ⧸ (N ⊓ φ ^ m (N))) ≤ m * length (N ⧸ (N ⊓ φ(N)))` in `ℕ∞`. -/
theorem length_quotient_comap_subtype_map_pow_le (N : Submodule A M) (φ : Module.End A M)
    (m : ℕ) :
    Module.length A (↥N ⧸ (N.map (φ ^ m)).comap N.subtype) ≤
      m * Module.length A (↥N ⧸ (N.map φ).comap N.subtype) := by
  rw [← List.prod_replicate]
  simpa [List.map_replicate, List.sum_replicate, nsmul_eq_mul] using
    length_quotient_comap_subtype_map_list_prod_le N (List.replicate m φ)

/-- **Subadditivity of cokernel length.** For endomorphisms `φ, ψ` of `M`,
`length (M ⧸ φψ(M)) ≤ length (M ⧸ φ(M)) + length (M ⧸ ψ(M))` in `ℕ∞`. For injective `φ` this is
the equality `TauCeti.length_quotient_range_comp`. This is the case `N = ⊤` of
`TauCeti.length_quotient_comap_subtype_map_comp_le`. -/
theorem length_quotient_range_comp_le (φ ψ : M →ₗ[A] M) :
    Module.length A (M ⧸ LinearMap.range (φ ∘ₗ ψ)) ≤
      Module.length A (M ⧸ LinearMap.range φ) + Module.length A (M ⧸ LinearMap.range ψ) := by
  have h := length_quotient_comap_subtype_map_comp_le ⊤ φ ψ
  rwa [length_quotient_comap_subtype_top, length_quotient_comap_subtype_top,
    length_quotient_comap_subtype_top, Submodule.map_top, Submodule.map_top,
    Submodule.map_top] at h

/-- **Cokernel length of a product.** For a list `l` of endomorphisms of `M`, the cokernel of
their product has length at most the sum of the lengths of their cokernels, in `ℕ∞`. -/
theorem length_quotient_range_list_prod_le (l : List (Module.End A M)) :
    Module.length A (M ⧸ LinearMap.range l.prod) ≤
      (l.map fun φ ↦ Module.length A (M ⧸ LinearMap.range φ)).sum := by
  have h := length_quotient_comap_subtype_map_list_prod_le ⊤ l
  simp only [length_quotient_comap_subtype_top] at h
  rw [Submodule.map_top] at h
  convert h using 3
  funext φ
  rw [Submodule.map_top]

/-- **Cokernel length of a power.** For an endomorphism `φ` of `M` and `m : ℕ`,
`length (M ⧸ φ ^ m (M)) ≤ m * length (M ⧸ φ(M))` in `ℕ∞`. -/
theorem length_quotient_range_pow_le (φ : Module.End A M) (m : ℕ) :
    Module.length A (M ⧸ LinearMap.range (φ ^ m)) ≤
      m * Module.length A (M ⧸ LinearMap.range φ) := by
  have h := length_quotient_comap_subtype_map_pow_le ⊤ φ m
  rwa [length_quotient_comap_subtype_top, length_quotient_comap_subtype_top, Submodule.map_top,
    Submodule.map_top] at h

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

/-- The cokernel of an endomorphism of a module with a finite basis is the cokernel of its
matrix. -/
theorem _root_.Module.Basis.length_quotient_range_eq_length_quotient_range_toMatrix
    {R ι F : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup F] [Module R F]
    (b : Module.Basis ι R F) (ψ : F →ₗ[R] F) :
    Module.length R (F ⧸ LinearMap.range ψ) =
      Module.length R ((ι → R) ⧸ LinearMap.range (LinearMap.toMatrix b b ψ).mulVecLin) := by
  refine (Submodule.Quotient.equiv _ _ b.equivFun ?_).length_eq
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨b.equivFun y, by
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨ψ (b.equivFun.symm y), ⟨_, rfl⟩, ?_⟩
    conv_rhs => rw [← b.equivFun.apply_symm_apply y]
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

section Scalar

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Multiplication by `a` on `Aⁿ` has cokernel `(A ⧸ aA)ⁿ`, of length `n * ord_A a`: it is the
diagonal matrix with constant entry `a` (`Matrix.length_quotient_range_diagonal_mulVecLin`). -/
theorem length_quotient_lsmul_pi (ι : Type*) [Fintype ι] (a : A) :
    Module.length A ((ι → A) ⧸ LinearMap.range (LinearMap.lsmul A (ι → A) a)) =
      Fintype.card ι * Ring.ord A a := by
  classical
  have hdiag : LinearMap.lsmul A (ι → A) a = (Matrix.diagonal fun _ ↦ a).mulVecLin := by
    ext; simp [Matrix.mulVec_diagonal]
  rw [hdiag, Matrix.length_quotient_range_diagonal_mulVecLin, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

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

/-- **Colength of a submodule containing `aM`.** Over a Noetherian domain `A` of dimension at most
one, let `M` be a finitely generated torsion-free module, `a ≠ 0` and `T` a submodule with
`a • x ∈ T` for every `x : M`. Then `length (M ⧸ T) ≤ rank_A M * ord_A a` in `ℕ∞`: `M ⧸ T` is a
quotient of `M ⧸ aM` (`TauCeti.length_quotient_lsmul_eq_finrank_mul_ord`). -/
theorem length_quotient_le_finrank_mul_ord [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite A M] {a : A} (ha : a ≠ 0) {T : Submodule A M} (hT : ∀ x : M, a • x ∈ T) :
    Module.length A (M ⧸ T) ≤ Module.finrank A M * Ring.ord A a := by
  rw [← length_quotient_lsmul_eq_finrank_mul_ord ha]
  refine length_quotient_anti ?_
  rintro _ ⟨x, rfl⟩
  exact hT x

/-- **The sandwich bound.** Over a principal ideal domain `A` with an irreducible element `ϖ`, let
`M` be a finitely generated torsion-free module and `T` a submodule with `ϖ ^ e • x ∈ T` for every
`x : M`. Then `length (M ⧸ T) ≤ e * rank_A M` in `ℕ∞`: this is
`TauCeti.length_quotient_le_finrank_mul_ord` with `ord_A (ϖ ^ e) = e`. -/
theorem length_quotient_le_mul_finrank [IsPrincipalIdealRing A] [Module.Finite A M] {ϖ : A}
    (hϖ : Irreducible ϖ) {e : ℕ} {T : Submodule A M} (hT : ∀ x : M, ϖ ^ e • x ∈ T) :
    Module.length A (M ⧸ T) ≤ e * Module.finrank A M := by
  have hord : Ring.ord A (ϖ ^ e) = e := by
    rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ,
      nsmul_eq_mul, mul_one]
  exact (length_quotient_le_finrank_mul_ord (pow_ne_zero e hϖ.ne_zero) hT).trans_eq
    (by rw [hord, mul_comm])

end Scalar

end TauCeti
