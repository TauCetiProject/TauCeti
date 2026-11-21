/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
public import TauCeti.Geometry.Symplectic.Prod.Skew
public import TauCeti.Geometry.Symplectic.Floer.Graph.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# The native skew graph construction for finite-regularity forcing data

Let `j` be a `Cⁿ` almost complex structure on a domain manifold `P`, `J` a jointly `Cⁿ`
domain-dependent almost complex structure on the target `M`, and `A` a native `Cⁿ` Hom section
from the domain tangent bundle to the target tangent bundle over `P × M`. Gromov's graph
structure on `P × M` is the skew product of `j` and `J` along `A`: at `q = (p, x)` it sends
`(ξ, v)` to `(j ξ, J (v - A ξ) + A (j ξ))`. It is a `Cⁿ` almost complex structure on the product
manifold, a `Cⁿ` section of the endomorphism bundle of the whole tangent bundle of `P × M`
(`TauCeti.DomainDependentHomSection.graphStructure`). At each point it is the existing pointwise
skew product, transported through the canonical product tangent equivalence
(`TauCeti.DomainDependentHomSection.almostComplexStructureAt_graphStructure`). For `A = 0` it is
the block structure `(ξ, v) ↦ (j ξ, J v)` of `TauCeti.ContMDiffAlmostComplexStructure.prodFamily`
(`TauCeti.DomainDependentHomSection.graphStructure_zero`).

For an antilinear forcing term `ν` the pointwise structure is `ν.graphStructureAt`, whose vertical
component is `J v - 2 J ν ζ`, and the bundled `Cⁿ` structure is `ν.graphStructure`. A weak
manifold graph equation requires its separate Sobolev derivative and chart assembly. Standard
complex model coordinates agree with the existing arbitrary-one-form `Floer.graphStructure` by its
general skew-product comparison.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  graph construction.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.DomainDependentHomSection

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {n : ℕ∞}
  (A : DomainDependentHomSection I M IP P n) (j : ContMDiffAlmostComplexStructure IP n P)
  (J : ContMDiffAlmostComplexStructureFamily I M IP P n)

/-- The skew product `(ξ, v) ↦ (j ξ, J (v - A ξ) + A (j ξ))` on the product of the tangent
spaces at `q`. -/
private def graphLinear (q : P × M) :
    TangentSpace IP q.1 × TangentSpace I q.2 →L[ℝ] TangentSpace IP q.1 × TangentSpace I q.2 :=
  let fst := ContinuousLinearMap.fst ℝ (TangentSpace IP q.1) (TangentSpace I q.2)
  let snd := ContinuousLinearMap.snd ℝ (TangentSpace IP q.1) (TangentSpace I q.2)
  ((j.toEndomorphism q.1).comp fst).prod
    ((J.tangentEndomorphism q).comp (snd - (A.tangentHom q).comp fst) +
      (A.tangentHom q).comp ((j.toEndomorphism q.1).comp fst))

private theorem graphLinear_apply (q : P × M) (v : TangentSpace IP q.1 × TangentSpace I q.2) :
    graphLinear A j J q v =
      (j q.1 v.1,
        J.tangentEndomorphism q (v.2 - A.tangentHom q v.1) + A.tangentHom q (j q.1 v.1)) :=
  rfl

private theorem graphLinear_graphLinear (q : P × M)
    (v : TangentSpace IP q.1 × TangentSpace I q.2) :
    graphLinear A j J q (graphLinear A j J q v) = -v := by
  simp only [graphLinear_apply, add_sub_cancel_right, J.tangentEndomorphism_apply_apply,
    j.apply_apply, map_neg, map_sub]
  ext <;> simp

/-- The skew product as an endomorphism of the tangent space of `P × M` at `q`. -/
private def graphEndomorphism (q : P × M) :
    TangentSpace (IP.prod I) q →L[ℝ] TangentSpace (IP.prod I) q :=
  (Manifold.tangentSpaceProdEquiv q).symm.toContinuousLinearMap.comp
    ((graphLinear A j J q).comp (Manifold.tangentSpaceProdEquiv q).toContinuousLinearMap)

private theorem graphEndomorphism_apply (q : P × M) (v : TangentSpace (IP.prod I) q) :
    graphEndomorphism A j J q v = (Manifold.tangentSpaceProdEquiv q).symm
      (graphLinear A j J q (Manifold.tangentSpaceProdEquiv q v)) :=
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EP]

/-- The skew product is a `Cⁿ` section of the endomorphism bundle of `T(P × M)`. -/
private theorem contMDiff_graphEndomorphism :
    ContMDiff (IP.prod I) ((IP.prod I).prod 𝓘(ℝ, (EP × E) →L[ℝ] EP × E)) n
      (fun q ↦ TotalSpace.mk' ((EP × E) →L[ℝ] EP × E)
        (E := fun q : P × M ↦ TangentSpace (IP.prod I) q →L[ℝ] TangentSpace (IP.prod I) q) q
        (graphEndomorphism A j J q)) := by
  refine (TauCeti.contMDiff_hom_bundle_iff _).2 ?_
  -- On total spaces, split a tangent vector of `P × M` into its components `(ξ, v)`.
  have hsplit := contMDiff_equivTangentBundleProd (I := IP) (M := P) (I' := I) (M' := M) (n := n)
  have hproj : ContMDiff (IP.prod I).tangent (IP.prod I) n
      (fun r : TangentBundle (IP.prod I) (P × M) ↦ r.proj) := contMDiff_proj _
  have hv : ContMDiff (IP.prod I).tangent I.tangent n
      (fun r : TangentBundle (IP.prod I) (P × M) ↦ TotalSpace.mk' E r.proj.2 r.snd.2) :=
    (contMDiff_snd.comp hsplit).congr fun _ ↦ rfl
  -- The horizontal component `j ξ` and the vertical component `J (v - A ξ) + A (j ξ)`.
  have hhor := j.contMDiff_apply le_rfl (contMDiff_fst.comp hproj) hsplit.fst
  have hver := ((J.contMDiff_tangentEndomorphism.comp hproj).clm_bundle_apply
    (hv.sub_sectionAlong (A.contMDiff_apply hproj hsplit.fst))).add_sectionAlong
      (A.contMDiff_apply hproj hhor)
  refine (contMDiff_equivTangentBundleProd_symm.comp (hhor.prodMk hver)).congr fun r ↦ ?_
  rw [graphEndomorphism_apply, graphLinear_apply]
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply,
    Function.comp_apply]
  -- `(equivTangentBundleProd IP P I M).symm` reassembles a pair of tangent vectors over `q.1` and
  -- `q.2` into the tangent vector over `q` with these components, by its definition.
  rfl

/-- **Gromov's graph structure** on `P × M`: the skew product of a `Cⁿ` structure `j` on `P` and a
jointly `Cⁿ` domain-dependent structure `J` on `M` along a native `Cⁿ` Hom section `A`, sending
`(ξ, v)` to `(j ξ, J (v - A ξ) + A (j ξ))`. It is a `Cⁿ` almost complex structure on the product
manifold `P × M`. -/
def graphStructure : ContMDiffAlmostComplexStructure (IP.prod I) n (P × M) where
  toEndomorphism := ⟨graphEndomorphism A j J, contMDiff_graphEndomorphism A j J⟩
  square_neg q := ContinuousLinearMap.ext fun v ↦ by
    rw [ContMDiffSection.coeFn_mk, ContinuousLinearMap.comp_apply, graphEndomorphism_apply,
      graphEndomorphism_apply, ContinuousLinearEquiv.apply_symm_apply, graphLinear_graphLinear,
      map_neg, ContinuousLinearEquiv.symm_apply_apply, neg_apply, ContinuousLinearMap.id_apply]

/-- Gromov's graph structure sends `(ξ, v)` to `(j ξ, J (v - A ξ) + A (j ξ))`, under the canonical
identification of the tangent space of `P × M` with the product of the tangent spaces. -/
@[simp]
theorem graphStructure_apply (q : P × M) (v : TangentSpace (IP.prod I) q) :
    A.graphStructure j J q v = (Manifold.tangentSpaceProdEquiv q).symm
      (j q.1 (Manifold.tangentSpaceProdEquiv q v).1,
        J.tangentEndomorphism q ((Manifold.tangentSpaceProdEquiv q v).2 -
            A.tangentHom q (Manifold.tangentSpaceProdEquiv q v).1) +
          A.tangentHom q (j q.1 (Manifold.tangentSpaceProdEquiv q v).1)) :=
  graphEndomorphism_apply A j J q v

/-- At each point, Gromov's graph structure is the pointwise skew product of `j` and `J` along
`A`, transported through the canonical product tangent equivalence. -/
theorem almostComplexStructureAt_graphStructure (q : P × M) :
    (A.graphStructure j J).almostComplexStructureAt q =
      ((j.almostComplexStructureAt q.1).skewProd
        ((J.freeze q.1).almostComplexStructureAt q.2) (A.tangentHom q).toLinearMap).transport
          (Manifold.tangentSpaceProdEquiv q).symm.toLinearEquiv := by
  ext v
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, graphStructure_apply,
    AlmostComplexStructure.transport_apply, AlmostComplexStructure.skewProd_apply]
  simp only [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
    ContinuousLinearMap.coe_coe, J.freeze_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- For `A = 0`, Gromov's graph structure is the block structure `(ξ, v) ↦ (j ξ, J v)` of
`TauCeti.ContMDiffAlmostComplexStructure.prodFamily`. -/
theorem graphStructure_zero :
    (0 : DomainDependentHomSection I M IP P n).graphStructure j J =
      j.prodFamily (fun q ↦ (J.freeze q.1).almostComplexStructureAt q.2)
        J.contMDiff_freeze_almostComplexStructureAt := by
  refine ContMDiffAlmostComplexStructure.ext fun q v ↦ ?_
  rw [graphStructure_apply, ContMDiffAlmostComplexStructure.prodFamily_apply, tangentHom_zero,
    zero_apply, zero_apply, sub_zero, add_zero]
  simp only [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, J.freeze_apply]

end TauCeti.DomainDependentHomSection

namespace TauCeti.InhomogeneousTerm

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {n : ℕ∞}
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}

/-- The existing skew graph structure in the actual product tangent fibre. -/
def graphStructureAt (ν : InhomogeneousTerm j J) (q : P × M) :
    AlmostComplexStructure (TangentSpace (IP.prod I) q) :=
  ((j.almostComplexStructureAt q.1).skewProd
    ((J.freeze q.1).almostComplexStructureAt q.2) (ν.val.tangentHom q).toLinearMap).transport
      (Manifold.tangentSpaceProdEquiv q).symm.toLinearEquiv

/-- The normalized forcing convention gives the minus sign and the factor two in the native
skew graph construction. -/
@[simp]
theorem graphStructureAt_apply (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace (IP.prod I) q) :
    ν.graphStructureAt q v = (Manifold.tangentSpaceProdEquiv q).symm
      (j q.1 (Manifold.tangentSpaceProdEquiv q v).1,
        J.tangentEndomorphism q (Manifold.tangentSpaceProdEquiv q v).2 -
          (2 : ℝ) • J.tangentEndomorphism q
            (ν.val.tangentHom q (Manifold.tangentSpaceProdEquiv q v).1)) := by
  let w := Manifold.tangentSpaceProdEquiv q v
  have hJ (a : TangentSpace I q.2) :
      (J.freeze q.1).almostComplexStructureAt q.2 a = J.tangentEndomorphism q a :=
    ((J.freeze q.1).almostComplexStructureAt_apply q.2 a).trans (J.freeze_apply q.1 q.2 a)
  have h : (j.almostComplexStructureAt q.1).skewProd
      ((J.freeze q.1).almostComplexStructureAt q.2) (ν.val.tangentHom q).toLinearMap w =
        (j q.1 w.1, J.tangentEndomorphism q w.2 -
          (2 : ℝ) • J.tangentEndomorphism q (ν.val.tangentHom q w.1)) := by
    rw [AlmostComplexStructure.skewProd_apply]
    apply Prod.ext
    · exact j.almostComplexStructureAt_apply q.1 w.1
    · simp only [ContinuousLinearMap.coe_coe]
      rw [hJ, ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
        ν.tangentHom_apply_j, map_sub]
      simp only [two_smul]
      abel
  unfold graphStructureAt
  rw [AlmostComplexStructure.transport_apply]
  exact congrArg (Manifold.tangentSpaceProdEquiv q).symm h

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EP] in
/-- Gromov's graph structure of a forcing term, as a `Cⁿ` almost complex structure on `P × M`.
At each point it is `ν.graphStructureAt`
(`TauCeti.InhomogeneousTerm.almostComplexStructureAt_graphStructure`). -/
def graphStructure (ν : InhomogeneousTerm j J) :
    ContMDiffAlmostComplexStructure (IP.prod I) n (P × M) :=
  ν.val.graphStructure j J

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EP] in
@[simp]
theorem almostComplexStructureAt_graphStructure (ν : InhomogeneousTerm j J) (q : P × M) :
    ν.graphStructure.almostComplexStructureAt q = ν.graphStructureAt q :=
  ν.val.almostComplexStructureAt_graphStructure j J q

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EP] in
/-- Gromov's `Cⁿ` graph structure of a forcing term acts on each tangent vector as the pointwise
structure `ν.graphStructureAt`, whose formula is
`TauCeti.InhomogeneousTerm.graphStructureAt_apply`. -/
@[simp]
theorem graphStructure_apply (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace (IP.prod I) q) :
    ν.graphStructure q v = ν.graphStructureAt q v := by
  rw [← ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_graphStructure]

section Model

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {jC : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) n ℂ}
  {JC : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℂ) ℂ n}

/-- In standard complex source coordinates, the native tangent skew graph structure agrees
with the existing Euclidean `Floer.graphStructure` through the canonical product
identifications. -/
theorem toLp_graphStructureAt_eq_graphStructure (ν : InhomogeneousTerm jC JC)
    (q : ℂ × V) (hj : ∀ w : ℂ, jC q.1 w = Complex.I * w)
    (v : TangentSpace (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V)) q) :
    WithLp.toLp 2 (show ℂ × V from ν.graphStructureAt q v) =
      Floer.graphStructure (fun q ↦ (show V →L[ℝ] V from JC.toEndomorphism q))
        (fun q ↦ (show ℂ →L[ℝ] V from ν.val.tangentHom q)) (WithLp.toLp 2 q)
          (WithLp.toLp 2 (show ℂ × V from v)) := by
  let K : AlmostComplexStructure V :=
    { toLinearMap := (show V →L[ℝ] V from JC.toEndomorphism q).toLinearMap
      square_neg := by ext w; exact JC.apply_apply q w }
  rw [graphStructureAt_apply, Floer.graphStructure_toLp_eq_skewProd _ _ q
    (show ℂ × V from v) K (fun _ ↦ rfl), AlmostComplexStructure.skewProd_apply]
  simp only [AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · simp only [Manifold.tangentSpaceProdEquiv_apply,
      Manifold.tangentSpaceProdEquiv_symm_apply]
    exact hj v.1
  · let A : V →L[ℝ] V := JC.toEndomorphism q
    let N : ℂ →L[ℝ] V := ν.val.tangentHom q
    have hJ := JC.tangentEndomorphism_apply q
    have hn : N (Complex.I * v.1) = -A (N v.1) := by
      have hh := ν.tangentHom_apply_j q v.1
      erw [hJ] at hh
      exact (congrArg N (hj v.1).symm).trans hh
    simp only [Manifold.tangentSpaceProdEquiv_apply,
      Manifold.tangentSpaceProdEquiv_symm_apply, hJ]
    -- Canonical model tangents and the ambient normed spaces have the same vectors; after
    -- the public tangent getter the remaining distinction is their inherited module instances.
    change A v.2 - (2 : ℝ) • A (N v.1) = A (v.2 - N v.1) + N (Complex.I * v.1)
    rw [hn, map_sub]
    simp only [two_smul]
    abel

end Model

end TauCeti.InhomogeneousTerm
