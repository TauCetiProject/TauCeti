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
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# The native skew graph construction for finite-regularity forcing data

Let `j` be a `Cⁿ` almost complex structure on a domain manifold `P`, `J` a jointly `Cⁿ`
domain-dependent almost complex structure on the target `M`, and `A` a native `Cⁿ` Hom section
from the domain tangent bundle to the target tangent bundle over `P × M`. Gromov's graph
structure on `P × M` is the skew product of `j` and `J` along `A`: at `q = (p, x)` it sends
`(ξ, v)` to `(j ξ, J (v - A ξ) + A (j ξ))`. For finite-dimensional models it is a `Cⁿ` almost
complex structure on the product manifold, a `Cⁿ` section of the endomorphism bundle of the whole
tangent bundle of `P × M` (`TauCeti.DomainDependentHomSection.graphStructure`). At each point it is
the existing pointwise skew product, transported through the canonical product tangent
equivalence (`TauCeti.DomainDependentHomSection.almostComplexStructureAt_graphStructure`). For
`A = 0` it is the block structure `(ξ, v) ↦ (j ξ, J v)` of
`TauCeti.ContMDiffAlmostComplexStructure.prodFamily`
(`TauCeti.DomainDependentHomSection.graphStructure_zero`).

For an antilinear forcing term `ν` the pointwise structure is `ν.graphStructureAt`, whose vertical
component is `J v - 2 J ν ζ`; the square identity is inherited from the native skew construction.
The pointwise structures assemble into a `Cⁿ` almost complex structure on `P × M`
(`TauCeti.InhomogeneousTerm.graphStructure`), of the same regularity `n` as the domain structure
`j`, the domain-dependent target structure `J` and the forcing term `ν`, without any
finite-dimensionality assumption. In the tangent trivialization of `P × M` at a point, which is
the product of the trivializations of the factors, the structure is the block matrix with diagonal
blocks `j` and `J` and lower block `-2 J ν`, each read in the trivializations of the factors. For
finite-dimensional models it is the general graph structure along `ν`
(`TauCeti.InhomogeneousTerm.val_graphStructure`). This is the regularity under which compactness
for unperturbed pseudoholomorphic curves in `P × M` applies to graphs of solutions of the
inhomogeneous equation.

At a point, the homogeneous equation for the graph structure on the pairs `(a, c)` and `(j a, d)`
is the inhomogeneous equation `c + J d = 2 ν a`
(`TauCeti.InhomogeneousTerm.add_graphStructure_eq_zero_iff`). The weak manifold graph equation
built on it is `TauCeti.isWeakPseudoholomorphicOn_graph_iff`, in
`TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Graph`. Standard complex model coordinates
agree with the existing arbitrary-one-form
`Floer.graphStructure` by its general skew-product comparison.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 8.1 (the graph construction).
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

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
    (contMDiff_snd.comp hsplit).congr fun r ↦ by
      rw [Function.comp_apply, equivTangentBundleProd_apply]
  -- The horizontal component `j ξ` and the vertical component `J (v - A ξ) + A (j ξ)`.
  have hhor := j.contMDiff_apply le_rfl (contMDiff_fst.comp hproj) hsplit.fst
  have hver := ((J.contMDiff_tangentEndomorphism.comp hproj).clm_bundle_apply
    (hv.sub_sectionAlong (A.contMDiff_apply hproj hsplit.fst))).add_sectionAlong
      (A.contMDiff_apply hproj hhor)
  refine (contMDiff_equivTangentBundleProd_symm.comp (hhor.prodMk hver)).congr fun r ↦ ?_
  rw [graphEndomorphism_apply, graphLinear_apply]
  simp only [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_symm_apply,
    Function.comp_apply]
  rw [Equiv.eq_symm_apply, equivTangentBundleProd_apply]

/-- **Gromov's graph structure** on `P × M`: the skew product of a `Cⁿ` structure `j` on `P` and a
jointly `Cⁿ` domain-dependent structure `J` on `M` along a native `Cⁿ` Hom section `A`, sending
`(ξ, v)` to `(j ξ, J (v - A ξ) + A (j ξ))`. It is a `Cⁿ` almost complex structure on the product
manifold `P × M`. -/
def graphStructure : ContMDiffAlmostComplexStructure (IP.prod I) n (P × M) where
  toEndomorphism := ⟨graphEndomorphism A j J, contMDiff_graphEndomorphism A j J⟩
  square_neg q := ContinuousLinearMap.ext fun v ↦ by
    -- Keep the product identifications so that they cancel against their inverses.
    simp [graphEndomorphism_apply, graphLinear_graphLinear,
      -Manifold.tangentSpaceProdEquiv_apply, -Manifold.tangentSpaceProdEquiv_symm_apply]

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

/-! ### Regularity of the graph structure -/

section Regularity

open ContinuousLinearMap (fst snd inl inr inCoordinates inCoordinates_pullback)

/-- The graph structure at `q` as a continuous endomorphism of the tangent space of `P × M`. In
the product decomposition of the tangent space it is `(ζ, v) ↦ (j ζ, J v - 2 J ν ζ)`. -/
private def graphEndomorphismAt (ν : InhomogeneousTerm j J) (q : P × M) :
    TangentSpace (IP.prod I) q →L[ℝ] TangentSpace (IP.prod I) q :=
  ((Manifold.tangentSpaceProdEquiv (I := IP) (J := I) q).symm :
      TangentSpace IP q.1 × TangentSpace I q.2 →L[ℝ] TangentSpace (IP.prod I) q).comp
    (((inl ℝ (TangentSpace IP q.1) (TangentSpace I q.2)).comp
        ((j.toEndomorphism q.1).comp (fst ℝ (TangentSpace IP q.1) (TangentSpace I q.2))) +
      (inr ℝ (TangentSpace IP q.1) (TangentSpace I q.2)).comp
        ((J.tangentEndomorphism q).comp (snd ℝ (TangentSpace IP q.1) (TangentSpace I q.2))) -
      (2 : ℝ) • (inr ℝ (TangentSpace IP q.1) (TangentSpace I q.2)).comp
        ((J.tangentEndomorphism q).comp ((ν.val.tangentHom q).comp
          (fst ℝ (TangentSpace IP q.1) (TangentSpace I q.2))))).comp
      (Manifold.tangentSpaceProdEquiv (I := IP) (J := I) q :
        TangentSpace (IP.prod I) q →L[ℝ] TangentSpace IP q.1 × TangentSpace I q.2))

/-- The continuous endomorphism `graphEndomorphismAt` acts as the graph structure. -/
private theorem graphEndomorphismAt_apply (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace (IP.prod I) q) : ν.graphEndomorphismAt q v = ν.graphStructureAt q v := by
  rw [graphStructureAt_apply]
  apply congrArg (Manifold.tangentSpaceProdEquiv (I := IP) (J := I) q).symm
  -- In the product decomposition both sides are the same pair of vectors. The left side is a
  -- sum of maps through `inl` and `inr`; `change` evaluates it in each factor, where it is
  -- definitionally the pair with zero components added.
  ext
  · change j.toEndomorphism q.1 (Manifold.tangentSpaceProdEquiv q v).1 + 0 - (2 : ℝ) • 0 = _
    rw [add_zero, smul_zero, sub_zero]
  · change 0 + J.tangentEndomorphism q (Manifold.tangentSpaceProdEquiv q v).2 -
        (2 : ℝ) • J.tangentEndomorphism q
          (ν.val.tangentHom q (Manifold.tangentSpaceProdEquiv q v).1) = _
    rw [zero_add]

/-- In the product decomposition of the tangent space, the graph structure sends `(ζ, v)` to
`(j ζ, J v - 2 J ν ζ)`. -/
private theorem tangentSpaceProdEquiv_graphEndomorphismAt (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace (IP.prod I) q) :
    Manifold.tangentSpaceProdEquiv (I := IP) (J := I) q (ν.graphEndomorphismAt q v) =
      (j q.1 (Manifold.tangentSpaceProdEquiv q v).1,
        J.tangentEndomorphism q (Manifold.tangentSpaceProdEquiv q v).2 -
          (2 : ℝ) • J.tangentEndomorphism q
            (ν.val.tangentHom q (Manifold.tangentSpaceProdEquiv q v).1)) := by
  rw [graphEndomorphismAt_apply, graphStructureAt_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Over the domain of the chart at `q₀`, the graph structure read in the tangent trivialization
of `P × M` at `q₀` is the block matrix `(ζ, v) ↦ (a ζ, b v - 2 b (c ζ))`, where `a`, `b` and `c`
are `j`, `J` and `ν` read in the trivializations of the factors at `q₀.1` and `q₀.2`. -/
private theorem inCoordinates_graphEndomorphismAt (ν : InhomogeneousTerm j J) {q₀ q : P × M}
    (hq : q ∈ (chartAt (ModelProd HP H) q₀).source) (w : EP × E) :
    inCoordinates (EP × E) (TangentSpace (IP.prod I)) (EP × E) (TangentSpace (IP.prod I))
        q₀ q q₀ q (ν.graphEndomorphismAt q) w =
      (inCoordinates EP (TangentSpace IP) EP (TangentSpace IP) q₀.1 q.1 q₀.1 q.1
          (j.toEndomorphism q.1) w.1,
        inCoordinates E (TangentSpace I) E (TangentSpace I) q₀.2 q.2 q₀.2 q.2
            (J.toEndomorphism q) w.2 -
          (2 : ℝ) • inCoordinates E (TangentSpace I) E (TangentSpace I) q₀.2 q.2 q₀.2 q.2
            (J.toEndomorphism q) (inCoordinates EP (TangentSpace IP) E (TangentSpace I)
              q₀.1 q.1 q₀.2 q.2 (ν.val q) w.1)) := by
  set τ := trivializationAt (EP × E) (TangentSpace (IP.prod I)) q₀
  set τP := trivializationAt EP (TangentSpace IP) q₀.1
  set τM := trivializationAt E (TangentSpace I) q₀.2
  have hq' : q.1 ∈ τP.baseSet ∧ q.2 ∈ τM.baseSet := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod,
      τP, τM, TangentBundle.trivializationAt_baseSet] using hq
  have hτ : q ∈ τ.baseSet := by simpa [τ] using hq
  -- Both sides are images under `τ.continuousLinearMapAt`, which `τ.symmL` inverts on the base
  -- set; the product decomposition of `τ.symmL` then compares them factor by factor.
  simp only [inCoordinates, ContinuousLinearMap.comp_apply]
  rw [← τ.continuousLinearMapAt_symmL (R := ℝ) hτ (_, _)]
  congr 1
  apply (Manifold.tangentSpaceProdEquiv (I := IP) (J := I) q).injective
  rw [tangentSpaceProdEquiv_graphEndomorphismAt,
    Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq,
    Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hq]
  ext
  · exact (τP.symmL_continuousLinearMapAt (R := ℝ) hq'.1 _).symm
  · -- `tangentEndomorphism` and `tangentHom` read the pullback fibres as the target tangent
    -- spaces; after unfolding them, `change` states the goal in those spaces, where the
    -- trivializations are linear.
    erw [ContMDiffAlmostComplexStructureFamily.tangentEndomorphism_apply,
      ContMDiffAlmostComplexStructureFamily.tangentEndomorphism_apply,
      DomainDependentHomSection.tangentHom_apply]
    change J.toEndomorphism q (τM.symmL ℝ q.2 w.2) -
        (2 : ℝ) • J.toEndomorphism q (ν.val q (τP.symmL ℝ q.1 w.1)) =
      τM.symmL ℝ q.2 (τM.continuousLinearMapAt ℝ q.2 (J.toEndomorphism q (τM.symmL ℝ q.2 w.2)) -
        (2 : ℝ) • τM.continuousLinearMapAt ℝ q.2 (J.toEndomorphism q (τM.symmL ℝ q.2
          (τM.continuousLinearMapAt ℝ q.2 (ν.val q (τP.symmL ℝ q.1 w.1))))))
    rw [map_sub, map_smul]
    have hν := τM.symmL_continuousLinearMapAt (R := ℝ) hq'.2 (ν.val q (τP.symmL ℝ q.1 w.1))
    exact (congrArg₂ (· - (2 : ℝ) • ·)
      (τM.symmL_continuousLinearMapAt (R := ℝ) hq'.2 _)
      ((τM.symmL_continuousLinearMapAt (R := ℝ) hq'.2 _).trans
        (congrArg (J.toEndomorphism q) hν))).symm

/-- The field of endomorphisms `graphEndomorphismAt` of the tangent bundle of `P × M` has the
regularity `n` of the data `j`, `J` and `ν`. In the trivialization at a point it is the block
matrix of `j`, `J` and `-2 J ν` read in the trivializations of the factors. -/
private theorem contMDiff_graphEndomorphismAt (ν : InhomogeneousTerm j J) :
    ContMDiff (IP.prod I) ((IP.prod I).prod 𝓘(ℝ, EP × E →L[ℝ] EP × E)) n
      (fun q : P × M ↦ TotalSpace.mk' (EP × E →L[ℝ] EP × E)
        (E := fun q : P × M ↦ TangentSpace (IP.prod I) q →L[ℝ] TangentSpace (IP.prod I) q) q
          (ν.graphEndomorphismAt q)) := by
  intro q₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- The three blocks, read in the trivializations of the factors.
  set a : P × M → EP →L[ℝ] EP := fun q ↦ inCoordinates EP (TangentSpace IP) EP
    (TangentSpace IP) q₀.1 q.1 q₀.1 q.1 (j.toEndomorphism q.1)
  set b : P × M → E →L[ℝ] E := fun q ↦ inCoordinates E (TangentSpace I) E (TangentSpace I)
    q₀.2 q.2 q₀.2 q.2 (J.toEndomorphism q)
  set c : P × M → EP →L[ℝ] E := fun q ↦ inCoordinates EP (TangentSpace IP) E (TangentSpace I)
    q₀.1 q.1 q₀.2 q.2 (ν.val q)
  have ha : ContMDiffAt (IP.prod I) 𝓘(ℝ, EP →L[ℝ] EP) n a q₀ :=
    ((contMDiffAt_hom_bundle _).1 (j.toEndomorphism.contMDiff q₀.1)).2.comp q₀ contMDiffAt_fst
  have hb : ContMDiffAt (IP.prod I) 𝓘(ℝ, E →L[ℝ] E) n b q₀ := by
    refine ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff q₀)).2.congr_of_eventuallyEq
      (.of_forall fun q ↦ (inCoordinates_pullback
        (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯)
        (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) q₀ q q₀ q (J.toEndomorphism q)).symm)
  have hc : ContMDiffAt (IP.prod I) 𝓘(ℝ, EP →L[ℝ] E) n c q₀ := by
    refine ((contMDiffAt_hom_bundle _).1 (ν.val.contMDiff q₀)).2.congr_of_eventuallyEq
      (.of_forall fun q ↦ (inCoordinates_pullback
        (ContMDiffMap.fst : C^∞⟮IP.prod I, P × M; IP, P⟯)
        (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) q₀ q q₀ q (ν.val q)).symm)
  -- The block matrix `(ζ, v) ↦ (a ζ, b v - 2 b (c ζ))` is `Cⁿ` in the blocks.
  have hL : ContMDiffAt (IP.prod I) 𝓘(ℝ, EP × E →L[ℝ] EP × E) n (fun q ↦
      (inl ℝ EP E).comp ((a q).comp (fst ℝ EP E)) + (inr ℝ EP E).comp ((b q).comp (snd ℝ EP E)) -
        ((2 : ℝ) • inr ℝ EP E).comp ((b q).comp ((c q).comp (fst ℝ EP E)))) q₀ :=
    ((contMDiffAt_const.clm_comp (ha.clm_comp contMDiffAt_const)).add
      (contMDiffAt_const.clm_comp (hb.clm_comp contMDiffAt_const))).sub
      (contMDiffAt_const.clm_comp (hb.clm_comp (hc.clm_comp contMDiffAt_const)))
  refine hL.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (ModelProd HP H) q₀).open_source.mem_nhds (mem_chart_source _ q₀)]
    with q hq
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [inCoordinates_graphEndomorphismAt ν hq]
  ext <;> simp [a, b, c]

/-- **The graph structure is `Cⁿ`.** Gromov's graph structure of an inhomogeneous term `ν`, as a
`Cⁿ` almost complex structure on `P × M`: at `q` it is `graphStructureAt q`, which sends `(ζ, v)`
to `(j ζ, J v - 2 J ν ζ)`. Its regularity `n` is that of the data `j`, `J` and `ν`: in the
tangent trivialization of `P × M` at a point it is the block matrix of `j`, `J` and `-2 J ν`, read
in the trivializations of the factors. -/
def graphStructure (ν : InhomogeneousTerm j J) :
    ContMDiffAlmostComplexStructure (IP.prod I) n (P × M) where
  toEndomorphism := ⟨ν.graphEndomorphismAt, ν.contMDiff_graphEndomorphismAt⟩
  square_neg q := by
    ext v
    -- The section evaluates to `graphEndomorphismAt` by construction.
    change ν.graphEndomorphismAt q (ν.graphEndomorphismAt q v) = -v
    rw [graphEndomorphismAt_apply, graphEndomorphismAt_apply,
      AlmostComplexStructure.apply_apply]

@[simp]
theorem graphStructure_apply (ν : InhomogeneousTerm j J) (q : P × M)
    (v : TangentSpace (IP.prod I) q) : ν.graphStructure q v = ν.graphStructureAt q v :=
  ν.graphEndomorphismAt_apply q v

/-- The fibres of the bundled graph structure are the pointwise graph structures. -/
@[simp]
theorem almostComplexStructureAt_graphStructure (ν : InhomogeneousTerm j J) (q : P × M) :
    ν.graphStructure.almostComplexStructureAt q = ν.graphStructureAt q := by
  ext v
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, graphStructure_apply]

/-- **The graph equation at a point.** At `q = (x, y)`, a pair `(a, c)` and the image under the
graph structure of `(j a, d)` add up to zero exactly when `c + J d = 2 ν a`. Read on the derivative
`(id, du)` of a graph, with `a = ∂ₛ`, `c = du ∂ₛ` and `d = du ∂ₜ`, the left side is the homogeneous
equation for the graph structure and the right side the inhomogeneous equation
`du + J du j = 2 ν` evaluated on `∂ₛ`. The first components cancel since `j² = -1`, and the
forcing term enters with the factor `2` since `ν` is antilinear. -/
theorem add_graphStructure_eq_zero_iff (ν : InhomogeneousTerm j J) (q : P × M)
    (a : TangentSpace IP q.1) (c d : TangentSpace I q.2) :
    (Manifold.tangentSpaceProdEquiv q).symm (a, c) +
        ν.graphStructure q ((Manifold.tangentSpaceProdEquiv q).symm (j q.1 a, d)) = 0 ↔
      c + J.tangentEndomorphism q d = (2 : ℝ) • ν.val.tangentHom q a := by
  rw [graphStructure_apply, graphStructureAt_apply, ContinuousLinearEquiv.apply_symm_apply,
    ← map_add, map_eq_zero_iff _ (Manifold.tangentSpaceProdEquiv q).symm.injective]
  -- The first components cancel since `j² = -1`; in the second, `J (ν (j a)) = ν a`.
  simp [ν.tangentHom_apply_j, j.apply_apply, add_sub_assoc', sub_eq_zero]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EP] in
/-- For finite-dimensional models, the `Cⁿ` graph structure of a forcing term is the general
graph structure `TauCeti.DomainDependentHomSection.graphStructure` along `ν`. -/
theorem val_graphStructure (ν : InhomogeneousTerm j J) :
    ν.val.graphStructure j J = ν.graphStructure :=
  ContMDiffAlmostComplexStructure.ext fun q v ↦ by
    rw [← ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
      DomainDependentHomSection.almostComplexStructureAt_graphStructure,
      ← ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply,
      almostComplexStructureAt_graphStructure]
    rfl

end Regularity

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
