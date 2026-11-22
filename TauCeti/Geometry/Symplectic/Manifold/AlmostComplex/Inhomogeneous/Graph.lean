/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
public import TauCeti.Geometry.Symplectic.Prod.Skew
public import TauCeti.Geometry.Symplectic.Floer.Graph.Basic

/-!
# The native skew graph construction for finite-regularity forcing data

The pointwise graph structure is the existing skew product, transported through the canonical
product tangent equivalence. For an antilinear forcing term its vertical component is
`J v - 2 J ν ζ`. The square identity is inherited from the native skew construction.
Standard complex model coordinates agree with the existing arbitrary-one-form
`Floer.graphStructure` by its general skew-product comparison.

The pointwise structures assemble into a `Cⁿ` almost complex structure on `P × M`
(`TauCeti.InhomogeneousTerm.graphStructure`), of the same regularity `n` as the domain structure
`j`, the domain-dependent target structure `J` and the forcing term `ν`. In the tangent
trivialization of `P × M` at a point, which is the product of the trivializations of the factors,
the structure is the block matrix with diagonal blocks `j` and `J` and lower block `-2 J ν`, each
read in the trivializations of the factors. This is the regularity under which compactness for
unperturbed pseudoholomorphic curves in `P × M` applies to graphs of solutions of the
inhomogeneous equation. A weak manifold graph equation requires its separate Sobolev derivative
and chart assembly.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 8.1 (the graph construction).
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

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

open ContinuousLinearMap (fst snd inl inr inCoordinates inCoordinates_pullback_of_mem)

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
  -- Near `q₀` both factors of `q` lie in the base sets of the trivializations at `q₀`.
  have hP : ∀ᶠ q : P × M in 𝓝 q₀, q.1 ∈ (trivializationAt EP (TangentSpace IP) q₀.1).baseSet :=
    continuousAt_fst.preimage_mem_nhds ((trivializationAt EP (TangentSpace IP) q₀.1).open_baseSet
      |>.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.1))
  have hM : ∀ᶠ q : P × M in 𝓝 q₀, q.2 ∈ (trivializationAt E (TangentSpace I) q₀.2).baseSet :=
    continuousAt_snd.preimage_mem_nhds ((trivializationAt E (TangentSpace I) q₀.2).open_baseSet
      |>.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2))
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
    refine ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff q₀)).2.congr_of_eventuallyEq ?_
    filter_upwards [hM] with q hq
    exact (inCoordinates_pullback_of_mem
      (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯)
      (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) q₀ q (J.toEndomorphism q) hq hq).symm
  have hc : ContMDiffAt (IP.prod I) 𝓘(ℝ, EP →L[ℝ] E) n c q₀ := by
    refine ((contMDiffAt_hom_bundle _).1 (ν.val.contMDiff q₀)).2.congr_of_eventuallyEq ?_
    filter_upwards [hP, hM] with q hqP hqM
    exact (inCoordinates_pullback_of_mem
      (ContMDiffMap.fst : C^∞⟮IP.prod I, P × M; IP, P⟯)
      (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) q₀ q (ν.val q) hqP hqM).symm
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
