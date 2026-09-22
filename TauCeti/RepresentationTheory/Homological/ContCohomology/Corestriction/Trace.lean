/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro

/-!
# The trace of a coinduced module

Let `U` be a finite-index subgroup of a topological group `G` and let `M` be a `G`-module.
Restricting the action to `U` and coinducing it back gives the module `Coind_U^G M` of locally
constant `U`-equivariant maps `G → M` (`TauCeti.coind`), and there is a canonical map back to
the coefficients,

```text
tr_U^G : Coind_U^G M → M,    tr_U^G f = ∑ x : G ⧸ U, x • f x⁻¹,
```

the **trace** of the coinduced module (Brown, *Cohomology of Groups*, III §9, where the
transfer is constructed from it). The summand `x • f x⁻¹` depends
only on the coset `x U`, because replacing `x` by `x u` replaces `f x⁻¹` by `u⁻¹ • f x⁻¹`; the
factor `x •` is what makes that cancellation happen, and a formula without it is correct only
for a trivial action. The sum is finite because the index is, so the trace is defined on the
nose rather than as a limit.

The trace is additive, `G`-equivariant for the right-translation action, natural in `M`, and
continuous on the discrete carrier `TauCeti.DiscreteCoind`; that is, it is a map of discrete
`G`-modules. Composed with the isomorphism of Shapiro's lemma it is what turns cohomology of `U`
into cohomology of `G`, and in degree zero that composite is exactly the corestriction norm
`m ↦ ∑ x, t x • m` of `TauCeti.ContCohomology.explicitCor0`: a `G`-invariant element of
`Coind_U^G M` is the constant function at its value at `1`
(`TauCeti.ContCohomology.apply_eq_apply_one_of_mem_H0`), so the trace of it is the norm of that
value. That identification is `TauCeti.ContCohomology.explicitCoeff0_trace`.

## Main declarations

* `TauCeti.coindTraceTerm`: the summand of the trace, as a function on `G ⧸ U`.
* `TauCeti.coindTrace`: the trace `Coind_U^G M →+ M`.
* `TauCeti.coindTrace_smul`: the trace is `G`-equivariant.
* `TauCeti.coindTrace_coindMap`: the trace is natural in the coefficient module.
* `TauCeti.DiscreteCoind.trace`: the additive trace on the discrete carrier.
* `TauCeti.coindTraceTopRep`: the trace as a morphism of smooth discrete topological
  representations.
* `TauCeti.ContCohomology.explicitCoeff0_trace` and
  `TauCeti.ContCohomology.explicitCor0_eq_explicitCoeff0_trace`: in degree zero the trace
  induces the corestriction norm, and corestriction is Shapiro's isomorphism followed by it.

## Implementation notes

Mathlib's `Rep.coindResAdjunction`, the adjunction `Coind_S^G ⊣ Res` available for a finite-index
subgroup because `Ind_S^G ≅ Coind_S^G` there, has this map as its counit, in the purely algebraic
category `Rep k G`. It is not used here. Its coinduced object is the `k`-linear module of *all*
equivariant functions `G → A`, whereas the coefficients of continuous cohomology are the locally
constant ones of `TauCeti.coind`, and the two agree only for an *open* subgroup of a compact group
(`TauCeti.topologicalCoindIsoAlgebraic`), while the trace itself needs no more than finite index
and no module structure on the coefficients. Mathlib also states its counit only as a composite of
`Rep.indCoindIso` with the induced counit, with no formula on elements, and the formula is what the
comparison with `TauCeti.ContCohomology.explicitCor0` is proved from.

## References

* K. S. Brown, *Cohomology of Groups*, III §9, which constructs the transfer from the trace of
  a coinduced module.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (1.5.7), for the
  corestriction this trace is the coefficient map of and its normalisation `cor ∘ res = (G : U)`.
-/

public section

namespace TauCeti

section Term

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]

variable (U) in
/-- The summand `x • f x⁻¹` of the trace of a coinduced element, as a function of the coset
`x U` rather than of `x`. It is well defined because `f` is `U`-equivariant: replacing a
representative `x` by `x * u` multiplies the value of `f` by `u⁻¹` and the outer action by `u`.
-/
def coindTraceTerm (f : coind G U M) (x : G ⧸ U) : M :=
  x.liftOn (fun g => g • (f : G → M) g⁻¹) fun a b hab => by
    obtain ⟨u, rfl⟩ : ∃ u : U, b = a * (u : G) :=
      ⟨⟨a⁻¹ * b, QuotientGroup.leftRel_apply.1 hab⟩, by simp⟩
    have h : (f : G → M) ((a * (u : G))⁻¹) = ((u : G))⁻¹ • (f : G → M) a⁻¹ := by
      rw [mul_inv_rev]
      exact coind_apply_mul f u⁻¹ a⁻¹
    rw [h, smul_smul, mul_inv_cancel_right]

@[simp]
theorem coindTraceTerm_mk (f : coind G U M) (g : G) :
    coindTraceTerm U f (g : G ⧸ U) = g • (f : G → M) g⁻¹ := (rfl)

/-- The summand of the trace, computed at the canonical representative of a coset. -/
theorem coindTraceTerm_out (f : coind G U M) (x : G ⧸ U) :
    coindTraceTerm U f x = x.out • (f : G → M) x.out⁻¹ := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [coindTraceTerm_mk]

@[simp]
theorem coindTraceTerm_zero (x : G ⧸ U) : coindTraceTerm U (0 : coind G U M) x = 0 := by
  rw [coindTraceTerm_out]
  simp

@[simp]
theorem coindTraceTerm_add (f f' : coind G U M) (x : G ⧸ U) :
    coindTraceTerm U (f + f') x = coindTraceTerm U f x + coindTraceTerm U f' x := by
  rw [coindTraceTerm_out, coindTraceTerm_out, coindTraceTerm_out]
  simp [smul_add]

/-- The effect of right translation on a summand of the trace: translating the coinduced element
by `g` translates the coset index by `g⁻¹` and multiplies the summand by `g`. -/
theorem coindTraceTerm_smul [ContinuousMul G] (g : G) (f : coind G U M) (x : G ⧸ U) :
    coindTraceTerm U (g • f) x = g • coindTraceTerm U f (g⁻¹ • x) := by
  have hx : g⁻¹ • x = ((g⁻¹ * x.out : G) : G ⧸ U) := by
    rw [← MulAction.Quotient.coe_smul_out U g⁻¹ x, smul_eq_mul]
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [hx, coindTraceTerm_mk, coindTraceTerm_mk, coind_smul_apply, smul_smul,
    mul_inv_cancel_left, mul_inv_rev, inv_inv]

end Term

section Trace

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G} [U.FiniteIndex]
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (G U) in
/-- **The trace of the coinduced module**, `f ↦ ∑ x : G ⧸ U, x • f x⁻¹`. This is the coefficient
map that turns Shapiro's isomorphism `Hⁿ(G, Coind_U^G M) ≅ Hⁿ(U, M)` into the corestriction
`Hⁿ(U, M) → Hⁿ(G, M)`. -/
noncomputable def coindTrace : coind G U M →+ M where
  toFun f := ∑ x : G ⧸ U, coindTraceTerm U f x
  map_zero' := by simp
  map_add' f f' := by simp [Finset.sum_add_distrib]

@[simp]
theorem coindTrace_apply (f : coind G U M) :
    coindTrace G U f = ∑ x : G ⧸ U, coindTraceTerm U f x := (rfl)

/-- The trace computed along an arbitrary transversal `t : G ⧸ U → G`. Unlike the corestriction
of a cocycle in higher degrees, the value is unchanged on the nose, not merely up to a
coboundary. -/
theorem coindTrace_eq_sum_transversal (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (f : coind G U M) :
    coindTrace G U f = ∑ x : G ⧸ U, t x • (f : G → M) (t x)⁻¹ :=
  Finset.sum_congr rfl fun x _ => by rw [← coindTraceTerm_mk f (t x), ht x]

/-- The trace is `G`-equivariant for the right-translation action on the coinduced module. -/
theorem coindTrace_smul [ContinuousMul G] (g : G) (f : coind G U M) :
    coindTrace G U (g • f) = g • coindTrace G U f := by
  rw [coindTrace_apply, coindTrace_apply, Finset.smul_sum]
  calc
    ∑ x : G ⧸ U, coindTraceTerm U (g • f) x
        = ∑ x : G ⧸ U, g • coindTraceTerm U f (g⁻¹ • x) :=
      Finset.sum_congr rfl fun x _ => coindTraceTerm_smul g f x
    _ = ∑ x : G ⧸ U, g • coindTraceTerm U f x :=
      Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun _ => rfl

/-- The trace is natural in the coefficient module: a `G`-equivariant map of coefficients
commutes with it. -/
theorem coindTrace_coindMap {N : Type*} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (f : coind G U M) :
    coindTrace G U (coindMap G U φ (fun u m => hφ (u : G) m) f) = φ (coindTrace G U f) := by
  rw [coindTrace_apply, coindTrace_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coindTraceTerm_out, coindTraceTerm_out, coindMap_apply, hφ]

/-- The trace of the whole group is evaluation at `1`: the only coset is `U` itself. -/
theorem coindTrace_top (f : coind G ⊤ M) :
    coindTrace G ⊤ f = coindEval G ⊤ f := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  rw [coindTrace_apply,
    Fintype.sum_subsingleton (coindTraceTerm (⊤ : Subgroup G) f) ((1 : G) : G ⧸ (⊤ : Subgroup G)),
    coindTraceTerm_mk]
  simp

end Trace

namespace DiscreteCoind

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  [U.FiniteIndex] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (G U M) in
/-- **The additive trace on the discrete carrier** of the coinduced module. -/
noncomputable def trace : DiscreteCoind G U M →+[G] M where
  toFun f := coindTrace G U (toCoind G U M f)
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  map_smul' g f := coindTrace_smul g (toCoind G U M f)

@[simp]
theorem trace_apply (f : DiscreteCoind G U M) :
    trace G U M f = ∑ x : G ⧸ U, x.out • f x.out⁻¹ :=
  Finset.sum_congr rfl fun x _ => coindTraceTerm_out (toCoind G U M f) x

/-- The trace is continuous, the source being discrete. -/
theorem continuous_trace [TopologicalSpace M] : Continuous (trace G U M) :=
  continuous_of_discreteTopology

section Scalar

variable {R : Type*} [Semiring R] [Module R M] [SMulCommClass G R M]

variable (R G U M) in
/-- The trace on the discrete carrier as an `R`-linear map. -/
noncomputable def traceLinear : DiscreteCoind G U M →ₗ[R] M where
  toAddHom := (trace G U M).toAddHom
  map_smul' r f := by
    change trace G U M (r • f) = r • trace G U M f
    rw [trace_apply, trace_apply, Finset.smul_sum]
    simp only [coe_smul_scalar]
    exact Finset.sum_congr rfl fun x _ => smul_comm x.out r (f x.out⁻¹)

private theorem traceLinear_apply_impl (f : DiscreteCoind G U M) :
    traceLinear (R := R) G U M f = trace G U M f := rfl

@[simp]
theorem traceLinear_apply (f : DiscreteCoind G U M) :
    traceLinear (R := R) G U M f = trace G U M f := traceLinear_apply_impl f

end Scalar

end DiscreteCoind

section BundledTrace

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

/-- **The trace as a morphism of smooth discrete `G`-representations.** For an open subgroup
`U`, this is the coefficient morphism whose image under continuous cohomology is the second map
in the Shapiro-then-trace construction of all-degree corestriction. -/
noncomputable def coindTraceTopRep (hU : IsOpen (U : Set G))
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) :
    (coindTopRep R G U
      (⟨TopRep.res (U.subtype : U →* G) A.obj,
        A.property.res continuous_subtype_val⟩ : SmoothDiscreteTopRep R U)).obj ⟶ A.obj := by
  letI : DiscreteTopology A.obj.V := A.property.discreteTopology
  letI : ContinuousSMul G A.obj.V := A.property.continuousSMul
  letI : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  letI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let X := coindTopRep R G U
    (⟨TopRep.res (U.subtype : U →* G) A.obj,
      A.property.res continuous_subtype_val⟩ : SmoothDiscreteTopRep R U)
  letI : DiscreteTopology X.obj.V := X.property.discreteTopology
  exact CategoryTheory.ConcreteCategory.ofHom
    { toContinuousLinearMap :=
        { toFun := DiscreteCoind.trace G U A.obj.V
          map_add' := map_add (DiscreteCoind.trace G U A.obj.V)
          map_smul' := by
            intro r f
            exact map_smul (DiscreteCoind.traceLinear (R := R) G U A.obj.V) r f
          cont := continuous_of_discreteTopology }
      isIntertwining' g := by
        ext f
        exact map_smul (DiscreteCoind.trace G U A.obj.V) g f }

private theorem coindTraceTopRep_apply_impl [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) (f : DiscreteCoind G U A.obj.V) :
    coindTraceTopRep R G U hU A f = DiscreteCoind.trace G U A.obj.V f := by
  change DiscreteCoind.trace G U A.obj.V f = _
  rfl

@[simp]
theorem coindTraceTopRep_apply [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) (f : DiscreteCoind G U A.obj.V) :
    coindTraceTopRep R G U hU A f = DiscreteCoind.trace G U A.obj.V f := by
  exact coindTraceTopRep_apply_impl R G U hU A f

end BundledTrace

namespace ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  [U.FiniteIndex] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **In degree zero the trace is the corestriction norm.** A `G`-invariant element of
`Coind_U^G M` is constant, so the trace sends it to the norm `∑ x, x • m` of the `U`-invariant
value `m` that Shapiro's isomorphism `TauCeti.ContCohomology.explicitShapiro0` reads off it. This
is the degree-zero instance of the statement that Shapiro's isomorphism followed by the trace is
corestriction. -/
theorem explicitCoeff0_trace :
    explicitCoeff0 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M) =
      (explicitCor0 G M U).comp (explicitShapiro0 G U M).toAddMonoidHom := by
  refine AddMonoidHom.ext fun f => Subtype.ext ?_
  rw [coe_explicitCoeff0, AddMonoidHom.comp_apply, coe_explicitCor0, DiscreteCoind.trace_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [AddEquiv.coe_toAddMonoidHom, explicitShapiro0_apply, apply_eq_apply_one_of_mem_H0 f]

/-- **Degree-zero corestriction is Shapiro's isomorphism followed by the trace.** This is
`TauCeti.ContCohomology.explicitCoeff0_trace` read through the inverse of Shapiro's isomorphism,
and it is the shape in which corestriction is defined in every degree: the transversal norm of
`TauCeti.ContCohomology.explicitCor0` is the degree-zero value of that construction. -/
theorem explicitCor0_eq_explicitCoeff0_trace :
    explicitCor0 G M U =
      (explicitCoeff0 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)).comp
        (explicitShapiro0 G U M).symm.toAddMonoidHom := by
  refine AddMonoidHom.ext fun a => ?_
  have h := DFunLike.congr_fun explicitCoeff0_trace ((explicitShapiro0 G U M).symm a)
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at h
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]

end ContCohomology

end TauCeti
