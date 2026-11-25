/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Products of domain-dependent almost complex structures

Let `J` and `K` be jointly `Cⁿ` domain-dependent almost complex structures over `P × M` and
`P × N`, with the same domain `P`. Their product `J.prod K` is the domain-dependent structure over
`P × (M × N)` acting at `(p, (x, y))` by `J(p, x) × K(p, y)` on `T_x M × T_y N`, under the
canonical product tangent identification. No derivative is lost: the product is jointly `Cⁿ` for
every `n`, including `n = 0` and `n = ∞`.

Freezing a domain point turns the product into the product of the frozen target structures
(`ContMDiffAlmostComplexStructureFamily.freeze_prod`), and the product of domain-independent
families is the domain-independent family of the product structure
(`ContMDiffAlmostComplexStructureFamily.const_prod`). The product commutes with forgetting
regularity, with negation and with reparametrizing the domain.

## Main declarations

* `ContMDiffAlmostComplexStructureFamily.prod`: the product of two domain-dependent structures.
* `ContMDiffAlmostComplexStructureFamily.prod_apply`: it acts componentwise.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (finite-regularity domain-dependent almost complex structures).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace ContMDiffAlmostComplexStructureFamily

variable {E H M F H' N EP HP P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n m : ℕ∞}

/-- The block field `(p, (x, y)) ↦ J(p, x) × K(p, y)` underlying the product of two families. -/
private def prodField (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (K : ContMDiffAlmostComplexStructureFamily I' N IP P n) (q : P × (M × N)) :
    TangentSpace (I.prod I') q.2 →L[ℝ] TangentSpace (I.prod I') q.2 :=
  -- The product tangent fibre is the product of the tangent fibres of the factors.
  (J.tangentEndomorphism (q.1, q.2.1)).prodMap (K.tangentEndomorphism (q.1, q.2.2))

/-- The block field of two jointly `Cⁿ` families is a jointly `Cⁿ` vertical field. -/
private theorem contMDiff_prodField (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (K : ContMDiffAlmostComplexStructureFamily I' N IP P n) :
    ContMDiff (IP.prod (I.prod I')) ((I.prod I').prod 𝓘(ℝ, (E × F) →L[ℝ] E × F)) n
      (fun q : P × (M × N) ↦ TotalSpace.mk' ((E × F) →L[ℝ] E × F)
        (E := fun x : M × N ↦ TangentSpace (I.prod I') x →L[ℝ] TangentSpace (I.prod I') x) q.2
        (prodField J K q)) := by
  -- On total spaces, the block field acts separately on the two tangent components.
  refine (TauCeti.contMDiff_hom_bundle_prod_iff _).2 ?_
  have hsplit := contMDiff_equivTangentBundleProd.comp
    (contMDiff_snd : ContMDiff (IP.prod (I.prod I').tangent) (I.prod I').tangent n
      (Prod.snd : P × TangentBundle (I.prod I') (M × N) → _))
  have hbase : ContMDiff (IP.prod (I.prod I').tangent) (I.prod I') n
      (fun p : P × TangentBundle (I.prod I') (M × N) ↦ p.2.proj) :=
    (contMDiff_proj (TangentSpace (I.prod I'))).comp contMDiff_snd
  have hJ := (J.contMDiff_tangentEndomorphism.comp
    (contMDiff_fst.prodMk (contMDiff_fst.comp hbase))).clm_bundle_apply hsplit.fst
  have hK := (K.contMDiff_tangentEndomorphism.comp
    (contMDiff_fst.prodMk (contMDiff_snd.comp hbase))).clm_bundle_apply hsplit.snd
  exact contMDiff_equivTangentBundleProd_symm.comp (hJ.prodMk hK)

/-- The product of domain-dependent structures over a common domain `P`: at `(p, (x, y))` it
acts by `J(p, x) × K(p, y)` on `T_x M × T_y N`. -/
def prod (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (K : ContMDiffAlmostComplexStructureFamily I' N IP P n) :
    ContMDiffAlmostComplexStructureFamily (I.prod I') (M × N) IP P n :=
  ofContMDiff (prodField J K) (contMDiff_prodField J K) fun q v ↦
    Prod.ext (J.tangentEndomorphism_apply_apply (q.1, q.2.1) v.1)
      (K.tangentEndomorphism_apply_apply (q.1, q.2.2) v.2)

variable (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
  (K : ContMDiffAlmostComplexStructureFamily I' N IP P n)

/-- The product acts by the block map of the two factors. -/
theorem prod_toEndomorphism_apply (q : P × (M × N)) :
    (J.prod K).toEndomorphism q =
      (J.tangentEndomorphism (q.1, q.2.1)).prodMap (K.tangentEndomorphism (q.1, q.2.2)) := by
  unfold prod
  exact ofContMDiff_toEndomorphism_apply _ _ _ q

/-- The product acts separately on the two components of a product tangent vector. -/
theorem prod_apply (q : P × (M × N)) (v : TangentSpace (I.prod I') q.2) :
    J.prod K q v = (Manifold.tangentSpaceProdEquiv q.2).symm
      (J.tangentEndomorphism (q.1, q.2.1) (Manifold.tangentSpaceProdEquiv q.2 v).1,
        K.tangentEndomorphism (q.1, q.2.2) (Manifold.tangentSpaceProdEquiv q.2 v).2) := by
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  exact DFunLike.congr_fun (prod_toEndomorphism_apply J K q) v

/-- The product, read on the original tangent spaces, is the block map of the two factors. -/
theorem prod_tangentEndomorphism (q : P × (M × N)) :
    (J.prod K).tangentEndomorphism q =
      (J.tangentEndomorphism (q.1, q.2.1)).prodMap (K.tangentEndomorphism (q.1, q.2.2)) := by
  ext v
  rw [tangentEndomorphism_apply]
  exact DFunLike.congr_fun (prod_toEndomorphism_apply J K q) v

/-- Freezing a domain point in a product gives the product of the frozen target structures. -/
@[simp]
theorem freeze_prod (p : P) : (J.prod K).freeze p = (J.freeze p).prod (K.freeze p) := by
  ext x v
  rw [freeze_apply, ContMDiffAlmostComplexStructure.prod_apply, freeze_apply, freeze_apply,
    prod_tangentEndomorphism]
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  rfl

/-- The product of domain-independent families is the domain-independent product family. -/
@[simp]
theorem const_prod (J : ContMDiffAlmostComplexStructure I n M)
    (K : ContMDiffAlmostComplexStructure I' n N) :
    (const (IP := IP) (P := P) J).prod (const K) = const (J.prod K) :=
  ext_of_freeze fun p ↦ by rw [freeze_prod, freeze_const, freeze_const, freeze_const]

/-- Forgetting regularity commutes with the product. -/
@[simp]
theorem prod_ofLE (hmn : m ≤ n) : (J.prod K).ofLE hmn = (J.ofLE hmn).prod (K.ofLE hmn) :=
  ext_of_freeze fun p ↦ by
    rw [freeze_ofLE, freeze_prod, freeze_prod, freeze_ofLE, freeze_ofLE,
      ContMDiffAlmostComplexStructure.prod_ofLE]

/-- Negating both factors negates the product. -/
@[simp]
theorem prod_neg : (-J).prod (-K) = -(J.prod K) :=
  ext_of_freeze fun p ↦ by
    rw [freeze_neg, freeze_prod, freeze_prod, freeze_neg, freeze_neg,
      ContMDiffAlmostComplexStructure.prod_neg]

/-- Reparametrizing the common domain commutes with the product. -/
@[simp]
theorem prod_comp {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q]
    [ChartedSpace HQ Q] (g : C^n⟮IQ, Q; IP, P⟯) :
    (J.prod K).comp g = (J.comp g).prod (K.comp g) :=
  ext_of_freeze fun q ↦ by rw [freeze_comp, freeze_prod, freeze_prod, freeze_comp, freeze_comp]

end ContMDiffAlmostComplexStructureFamily

end TauCeti
