/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Prod
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Products of inhomogeneous terms

Let `ν` be an inhomogeneous term for an almost complex structure `j` on `P` and a domain-dependent
structure `J` over `P × M`, and `μ` one for `j` and `K` over `P × N`. Their product `ν.prod μ` is
the inhomogeneous term for `j` and the product family `J.prod K` over `P × (M × N)` whose value at
`(p, (x, y))` is the pair `(ν(p, x), μ(p, y)) : T_p P → T_x M × T_y N`. It is antilinear because
`J.prod K` acts componentwise. For the same reason the inhomogeneous Cauchy–Riemann equation
`du + J(z, u) ∘ du ∘ j = 2ν(z, u)` for a map `(u, w)` into `M × N` splits into the equations for
`(J, ν)` and `(K, μ)`.

The product of the underlying Hom sections is jointly `Cⁿ` without loss of derivatives, and the
product of terms is additive and real-homogeneous in the pair of factors.

## Main declarations

* `TauCeti.DomainDependentHomSection.prod`: the product of two domain-dependent Hom sections.
* `TauCeti.InhomogeneousTerm.prod`: the product of two inhomogeneous terms.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (inhomogeneous Cauchy--Riemann equations).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F H' N EP HP P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  {n : ℕ∞}

namespace DomainDependentHomSection

/-- The field `(p, (x, y)) ↦ (A(p, x), B(p, y))` underlying the product of two Hom sections. -/
private def prodField (A : DomainDependentHomSection I M IP P n)
    (B : DomainDependentHomSection I' N IP P n) (q : P × (M × N)) :
    TangentSpace IP q.1 →L[ℝ] TangentSpace (I.prod I') q.2 :=
  -- The product tangent fibre is the product of the tangent fibres of the factors.
  (A.tangentHom (q.1, q.2.1)).prod (B.tangentHom (q.1, q.2.2))

/-- The product field of two jointly `Cⁿ` Hom sections is a jointly `Cⁿ` Hom section. -/
private theorem contMDiff_prodField (A : DomainDependentHomSection I M IP P n)
    (B : DomainDependentHomSection I' N IP P n) :
    ContMDiff (IP.prod (I.prod I')) ((IP.prod (I.prod I')).prod 𝓘(ℝ, EP →L[ℝ] E × F)) n
      (fun q : P × (M × N) ↦ TotalSpace.mk' (EP →L[ℝ] E × F)
        (E := fun q : P × (M × N) ↦ horizontalTangentBundle (I.prod I') (M × N) IP P q →L[ℝ]
          verticalTangentBundle (I.prod I') (M × N) IP P q) q (prodField A B q)) := by
  refine (TauCeti.contMDiff_hom_bundle_iff
    (E₁ := horizontalTangentBundle (I.prod I') (M × N) IP P)
    (E₂ := verticalTangentBundle (I.prod I') (M × N) IP P) (prodField A B)).2 ?_
  -- The horizontal lift, read in the domain tangent bundle.
  have hlift : ContMDiff ((IP.prod (I.prod I')).prod 𝓘(ℝ, EP)) IP.tangent n
      (fun p : TotalSpace EP (horizontalTangentBundle (I.prod I') (M × N) IP P) ↦
        (⟨p.proj.1, p.snd⟩ : TangentBundle IP P)) :=
    Bundle.Pullback.contMDiff_lift
      (ContMDiffMap.fst : C^∞⟮IP.prod (I.prod I'), P × (M × N); IP, P⟯) contMDiff_fst
  have hbase : ContMDiff ((IP.prod (I.prod I')).prod 𝓘(ℝ, EP)) (IP.prod (I.prod I')) n
      (fun p : TotalSpace EP (horizontalTangentBundle (I.prod I') (M × N) IP P) ↦ p.proj) :=
    contMDiff_proj _
  -- Apply the two sections at `(p, x)` and `(p, y)` to the horizontal vector at `(p, (x, y))`.
  have hV₁ := A.contMDiff_apply
    ((contMDiff_fst.comp hbase).prodMk (contMDiff_fst.comp (contMDiff_snd.comp hbase))) hlift
  have hV₂ := B.contMDiff_apply
    ((contMDiff_fst.comp hbase).prodMk (contMDiff_snd.comp (contMDiff_snd.comp hbase))) hlift
  exact (Bundle.Pullback.contMDiff_iff
    (ContMDiffMap.snd : C^∞⟮IP.prod (I.prod I'), P × (M × N); I.prod I', M × N⟯)
      contMDiff_snd).2 ⟨hbase, contMDiff_equivTangentBundleProd_symm.comp (hV₁.prodMk hV₂)⟩

/-- The product of two domain-dependent Hom sections over a common domain `P`: at `(p, (x, y))`
it is the pair `(A(p, x), B(p, y)) : T_p P → T_x M × T_y N`. -/
def prod (A : DomainDependentHomSection I M IP P n) (B : DomainDependentHomSection I' N IP P n) :
    DomainDependentHomSection (I.prod I') (M × N) IP P n :=
  ⟨prodField A B, contMDiff_prodField A B⟩

/-- The product of two Hom sections is the pair of their values. -/
@[simp]
theorem tangentHom_prod (A : DomainDependentHomSection I M IP P n)
    (B : DomainDependentHomSection I' N IP P n) (q : P × (M × N)) :
    (A.prod B).tangentHom q = (A.tangentHom (q.1, q.2.1)).prod (B.tangentHom (q.1, q.2.2)) := by
  ext v
  rw [tangentHom_apply]
  rfl

/-- The product of the zero sections is zero. -/
@[simp]
theorem zero_prod_zero :
    (0 : DomainDependentHomSection I M IP P n).prod (0 : DomainDependentHomSection I' N IP P n) =
      0 :=
  ext_tangentHom fun q ↦ by
    simp only [tangentHom_prod, tangentHom_zero]
    -- `ContinuousLinearMap.prod` is the linear equivalence `ContinuousLinearMap.prodₗ`.
    exact (ContinuousLinearMap.prodₗ ℝ).map_zero

/-- The product of sections is additive in the pair of factors. -/
@[simp]
theorem add_prod_add (A A' : DomainDependentHomSection I M IP P n)
    (B B' : DomainDependentHomSection I' N IP P n) :
    (A + A').prod (B + B') = A.prod B + A'.prod B' :=
  ext_tangentHom fun q ↦ by
    simp only [tangentHom_prod, tangentHom_add]
    -- `ContinuousLinearMap.prod` is the linear equivalence `ContinuousLinearMap.prodₗ`.
    exact (ContinuousLinearMap.prodₗ ℝ).map_add (A.tangentHom _, B.tangentHom _)
      (A'.tangentHom _, B'.tangentHom _)

/-- The product of sections is real-homogeneous in the pair of factors. -/
@[simp]
theorem smul_prod_smul (c : ℝ) (A : DomainDependentHomSection I M IP P n)
    (B : DomainDependentHomSection I' N IP P n) :
    (c • A).prod (c • B) = c • A.prod B :=
  ext_tangentHom fun q ↦ by
    simp only [tangentHom_prod, tangentHom_smul]
    -- `ContinuousLinearMap.prod` is the linear equivalence `ContinuousLinearMap.prodₗ`.
    exact (ContinuousLinearMap.prodₗ ℝ).map_smul c (A.tangentHom _, B.tangentHom _)

/-- Negating both factors negates the product of sections. -/
@[simp]
theorem neg_prod_neg (A : DomainDependentHomSection I M IP P n)
    (B : DomainDependentHomSection I' N IP P n) :
    (-A).prod (-B) = -A.prod B :=
  ext_tangentHom fun q ↦ by
    simp only [tangentHom_prod, tangentHom_neg]
    -- `ContinuousLinearMap.prod` is the linear equivalence `ContinuousLinearMap.prodₗ`.
    exact (ContinuousLinearMap.prodₗ ℝ).map_neg (A.tangentHom _, B.tangentHom _)

/-- The product of sections commutes with subtraction in the pair of factors. -/
@[simp]
theorem sub_prod_sub (A A' : DomainDependentHomSection I M IP P n)
    (B B' : DomainDependentHomSection I' N IP P n) :
    (A - A').prod (B - B') = A.prod B - A'.prod B' :=
  ext_tangentHom fun q ↦ by
    simp only [tangentHom_prod, tangentHom_sub]
    -- `ContinuousLinearMap.prod` is the linear equivalence `ContinuousLinearMap.prodₗ`.
    exact (ContinuousLinearMap.prodₗ ℝ).map_sub (A.tangentHom _, B.tangentHom _)
      (A'.tangentHom _, B'.tangentHom _)

/-- Forgetting regularity commutes with the product of sections. -/
@[simp]
theorem prod_ofLE (A : DomainDependentHomSection I M IP P n)
    (B : DomainDependentHomSection I' N IP P n) {m : ℕ∞} (hmn : m ≤ n) :
    (A.prod B).ofLE hmn = (A.ofLE hmn).prod (B.ofLE hmn) :=
  ext_tangentHom fun q ↦ by
    rw [tangentHom_ofLE, tangentHom_prod, tangentHom_prod, tangentHom_ofLE, tangentHom_ofLE]

end DomainDependentHomSection

namespace InhomogeneousTerm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}
  {K : ContMDiffAlmostComplexStructureFamily I' N IP P n}

/-- The product of inhomogeneous terms over a common domain `P`: at `(p, (x, y))` it is the pair
`(ν(p, x), μ(p, y))`, an inhomogeneous term for `j` and the product family `J.prod K`. -/
def prod (ν : InhomogeneousTerm j J) (μ : InhomogeneousTerm j K) :
    InhomogeneousTerm j (J.prod K) :=
  ⟨ν.val.prod μ.val, (mem_inhomogeneousTerms_iff_tangentHom _ _ _).2 fun q v ↦ by
    rw [DomainDependentHomSection.tangentHom_prod,
      ContMDiffAlmostComplexStructureFamily.prod_tangentEndomorphism]
    exact Prod.ext (ν.tangentHom_apply_j (q.1, q.2.1) v) (μ.tangentHom_apply_j (q.1, q.2.2) v)⟩

/-- The underlying section of a product of terms is the product of the sections. -/
@[simp]
theorem prod_val (ν : InhomogeneousTerm j J) (μ : InhomogeneousTerm j K) :
    (ν.prod μ).val = ν.val.prod μ.val := (rfl)

/-- The product of two terms, evaluated on a domain tangent vector, is the pair of values. -/
theorem prod_val_tangentHom_apply (ν : InhomogeneousTerm j J) (μ : InhomogeneousTerm j K)
    (q : P × (M × N)) (v : TangentSpace IP q.1) :
    (ν.prod μ).val.tangentHom q v =
      (ν.val.tangentHom (q.1, q.2.1) v, μ.val.tangentHom (q.1, q.2.2) v) := by
  rw [prod_val, DomainDependentHomSection.tangentHom_prod]
  rfl

/-- The product of the zero terms is zero. -/
@[simp]
theorem zero_prod_zero : (0 : InhomogeneousTerm j J).prod (0 : InhomogeneousTerm j K) = 0 :=
  Subtype.ext DomainDependentHomSection.zero_prod_zero

/-- The product of terms is additive in the pair of factors. -/
@[simp]
theorem add_prod_add (ν ν' : InhomogeneousTerm j J) (μ μ' : InhomogeneousTerm j K) :
    (ν + ν').prod (μ + μ') = ν.prod μ + ν'.prod μ' :=
  Subtype.ext (DomainDependentHomSection.add_prod_add _ _ _ _)

/-- The product of terms is real-homogeneous in the pair of factors. -/
@[simp]
theorem smul_prod_smul (c : ℝ) (ν : InhomogeneousTerm j J) (μ : InhomogeneousTerm j K) :
    (c • ν).prod (c • μ) = c • ν.prod μ :=
  Subtype.ext (DomainDependentHomSection.smul_prod_smul _ _ _)

/-- Negating both factors negates the product of terms. -/
@[simp]
theorem neg_prod_neg (ν : InhomogeneousTerm j J) (μ : InhomogeneousTerm j K) :
    (-ν).prod (-μ) = -ν.prod μ :=
  Subtype.ext (DomainDependentHomSection.neg_prod_neg _ _)

/-- The product of terms commutes with subtraction in the pair of factors. -/
@[simp]
theorem sub_prod_sub (ν ν' : InhomogeneousTerm j J) (μ μ' : InhomogeneousTerm j K) :
    (ν - ν').prod (μ - μ') = ν.prod μ - ν'.prod μ' :=
  Subtype.ext (DomainDependentHomSection.sub_prod_sub _ _ _ _)

/-- Forgetting regularity commutes with the product of terms, up to the identification of the
regularity-downgraded product family with the product of the downgraded families. -/
theorem prod_ofLE (ν : InhomogeneousTerm j J) (μ : InhomogeneousTerm j K) {m : ℕ∞}
    (hmn : m ≤ n) :
    (ν.prod μ).ofLE hmn = ((ν.ofLE hmn).prod (μ.ofLE hmn)).ofEq rfl
      (ContMDiffAlmostComplexStructureFamily.prod_ofLE J K hmn).symm :=
  ext_tangentHom fun q v ↦ by
    rw [ofLE_val_tangentHom, ofEq_val, prod_val_tangentHom_apply, prod_val_tangentHom_apply,
      ofLE_val_tangentHom, ofLE_val_tangentHom]

end InhomogeneousTerm

end TauCeti
