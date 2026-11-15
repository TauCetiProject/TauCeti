/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup.Basic
public import TauCeti.RepresentationTheory.InvariantForm.SumOfConjugates

/-!
# Positive metrics on negative Clifford modules

A module over a negative-definite Clifford algebra need not initially have skew-adjoint
Clifford multiplication. Given a finite orthogonal basis of vectors squaring to `-1`, summing
any positive-definite symmetric form over the finite group of signed monomials produces such
a metric. Neither irreducibility nor faithfulness of the module is required.

`AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι` proves existence of a
positive-definite symmetric form making every Clifford vector skew-adjoint, given a starting
positive-definite quadratic form. It works over a partially ordered commutative ring with
order-compatible addition and invertible `2`. Its proof uses
`CliffordAlgebra.finite_monomialGroup` and `Representation.sumOfConjugatesForm` to sum the
associated symmetric bilinear form over the signed monomial group.

`AlgHom.bilinForm_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply` says that applying
the Clifford action of a vector `v` to both arguments scales any bilinear form by `-Q v`,
provided that vector acts skew-adjointly. It works over any commutative ring. Over the reals,
these are the metric ingredients for constructing orthonormal tangent fields on unit spheres
from Clifford modules.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra
open LinearMap (BilinForm)

namespace AlgHom

variable {K M W : Type*}

section Scaling

variable [CommRing K] [AddCommGroup M] [Module K M]
  [AddCommGroup W] [Module K W] {Q : QuadraticForm K M}

/-- For a vector `v` whose Clifford action is skew-adjoint with respect to `B`, applying
`ρ (ι Q v)` to both arguments scales `B` by `-Q v`.
No symmetry or positivity assumption on the form is needed. -/
theorem bilinForm_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W) (B : BilinForm K W)
    (v : M) (hρ : B.IsSkewAdjoint (ρ (ι Q v))) (x y : W) :
    B (ρ (ι Q v) x) (ρ (ι Q v) y) = -Q v * B x y := by
  have hsq : ρ (ι Q v) (ρ (ι Q v) y) = Q v • y := by
    rw [← mul_apply_eq_comp, comp_ι_sq_scalar, Module.algebraMap_end_apply]
  simpa only [Pi.neg_apply, hsq, map_neg, map_smul, smul_eq_mul, neg_mul] using
    hρ x (ρ (ι Q v) y)

end Scaling

section OrderedRing

variable [CommRing K] [PartialOrder K] [IsOrderedAddMonoid K] [Invertible (2 : K)]
  [AddCommGroup M] [Module K M] [AddCommGroup W] [Module K W] {Q : QuadraticForm K M}

/-- A Clifford module equipped with a positive-definite quadratic form, whose quadratic space
has a finite orthogonal basis squaring to `-1`, admits a positive-definite symmetric form
making every Clifford vector skew-adjoint. -/
theorem exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W)
    {I : Type*} [_root_.Finite I] (b : Module.Basis I K M)
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1)
    {Q₀ : QuadraticForm K W} (hpos : Q₀.PosDef) :
    ∃ B : BilinForm K W, B.toQuadraticMap.PosDef ∧ B.IsSymm ∧
      ∀ v, B.IsSkewAdjoint (ρ (ι Q v)) := by
  classical
  let B₀ : BilinForm K W := QuadraticMap.associated Q₀
  have hpos₀ : B₀.toQuadraticMap.PosDef := by
    simpa only [B₀, QuadraticMap.toQuadraticMap_associated] using hpos
  have hsymm : B₀.IsSymm := BilinForm.isSymm_iff.mpr (Q₀.associated_isSymm K)
  have hortho : (QuadraticMap.associated Q).IsOrthoᵢ b :=
    fun i j hij ↦ QuadraticMap.associated_isOrtho.mpr (hb i j hij)
  have : _root_.Finite (monomialGroup Q b) :=
    finite_monomialGroup hortho fun i ↦ Or.inr (hQ i)
  let : Fintype (monomialGroup Q b) := Fintype.ofFinite _
  let σ : Representation K (monomialGroup Q b) W :=
    ρ.toMonoidHom.comp ((Units.coeHom (CliffordAlgebra Q)).comp
      (monomialGroup Q b).subtype)
  let B := Representation.sumOfConjugatesForm σ B₀
  have hinv := Representation.isInvariantForm_sumOfConjugatesForm σ B₀
  refine ⟨B, Representation.posDef_toQuadraticMap_sumOfConjugatesForm hpos₀,
    Representation.isSymm_sumOfConjugatesForm hsymm, ?_⟩
  -- Skew-adjoint endomorphisms form a submodule, so it suffices to check the chosen basis.
  have hspan : ⊤ ≤ B.skewAdjointSubmodule.comap (ρ.toLinearMap.comp (ι Q)) := by
    rw [← b.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.mem_skewAdjointSubmodule]
    obtain ⟨g, hg⟩ := exists_monomialGroup_val_eq_ι b (i := i)
      (by rw [hQ]; exact isUnit_neg_one)
    have hact : σ g = ρ (ι Q (b i)) := by simp [σ, hg]
    have hsq (y : W) : ρ (ι Q (b i)) (ρ (ι Q (b i)) y) = -y := by
      rw [← mul_apply_eq_comp, comp_ι_sq_scalar, hQ, map_neg, map_one,
        LinearMap.neg_apply, one_apply_eq_self]
    intro x y
    have h := hinv.apply g x (-(ρ (ι Q (b i)) y))
    simpa only [B, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hact, map_neg, hsq,
      neg_neg, Pi.neg_apply] using h
  intro v
  simpa only [Submodule.mem_comap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.mem_skewAdjointSubmodule] using hspan (Submodule.mem_top : v ∈ ⊤)

end OrderedRing

end AlgHom
