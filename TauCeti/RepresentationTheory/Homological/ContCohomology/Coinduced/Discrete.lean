/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import all TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced

/-!
# The coinduced module as a discrete `G`-module

For a topological group `G`, a subgroup `U` and a `U`-module `A`, the coinduced module
`Coind_U^G A` of `TauCeti.coind` is an additive subgroup of `G → A`. This file carries it as a
*discrete* `G`-module, `TauCeti.DiscreteCoind G U A`: the same additive group with the discrete
topology imposed. It is the coefficient object of the explicit low-degree continuous cohomology,
and the one Shapiro's lemma is stated against.

## Main definitions

* `TauCeti.DiscreteCoind`: `Coind_U^G A` with the discrete topology, identified with
  `TauCeti.coind` by `TauCeti.DiscreteCoind.toCoind`; `TauCeti.DiscreteCoind.mk` builds an element
  from a locally constant `U`-equivariant function;
* `TauCeti.DiscreteCoind.eval` and `TauCeti.DiscreteCoind.evalLinear`: evaluation at `1`, the
  counit of coinduction;
* `TauCeti.DiscreteCoind.map`: the linear map induced by a `U`-equivariant linear map of
  coefficients;
* `TauCeti.DiscreteCoind.trace` and `TauCeti.DiscreteCoind.traceLinear`: for finite-index `U`, the
  trace `TauCeti.coindTrace` on the discrete carrier, as a `G`-equivariant additive map and as a
  linear map.

## Main results

* `TauCeti.DiscreteCoind.instContinuousSMul`: for compact `G` the right-translation action on the
  discrete carrier is continuous, so `Coind_U^G A` is a discrete `G`-module;
* `TauCeti.DiscreteCoind.instContinuousSMulScalar`: for compact `G` and discrete coefficients,
  scalar multiplication is continuous;
* `TauCeti.DiscreteCoind.trace_apply`, `TauCeti.DiscreteCoind.trace_eq_sum_transversal` and
  `TauCeti.DiscreteCoind.trace_map`: the trace formula, along any transversal, and its naturality
  in the coefficients.
-/

public section

namespace TauCeti

section DiscreteCarrier

variable (G : Type*) [Group G] [TopologicalSpace G] (U : Subgroup G)
  (A : Type*) [AddCommGroup A] [DistribMulAction U A]

/-- `Coind_U^G A` **as a discrete `G`-module**: the additive group `TauCeti.coind` carrying the
discrete topology.

The topology is imposed, not inherited. Viewed as an `AddSubgroup` of `G → A` the coinduced module
inherits the pointwise topology, in which a basic neighbourhood constrains only finitely many
values and therefore does not isolate a locally constant function; that is the same trap
`TauCeti.ContCohomology.DiscreteH1` records for the low-degree cohomology quotients. The
coefficients of continuous cohomology are *discrete* modules, and
`TauCeti.isOpen_stabilizer_coind` is exactly the statement that the right-translation action is
continuous for the discrete topology once `G` is compact
(`TauCeti.DiscreteCoind.instContinuousSMul`). `TauCeti.DiscreteCoind.toCoind` keeps the
computations on representatives available.

The body is `@[expose]`d because every carrier instance below transports one from
`TauCeti.coind` along it, and an exposed instance may only be built from exposed definitions. -/
@[expose] def DiscreteCoind : Type _ := coind G U A

namespace DiscreteCoind

instance : AddCommGroup (DiscreteCoind G U A) := inferInstanceAs (AddCommGroup (coind G U A))

instance : TopologicalSpace (DiscreteCoind G U A) := ⊥

instance : DiscreteTopology (DiscreteCoind G U A) := ⟨rfl⟩

/-- The additive equivalence between the discrete carrier and the coinduced subgroup: the identity
on elements, so that a computation performed on the underlying function transfers unchanged. The
body is `@[expose]`d because the coercion to a function below is defined through it. -/
@[expose] def toCoind : DiscreteCoind G U A ≃+ coind G U A := AddEquiv.refl _

variable {G U A}

instance instFunLike : FunLike (DiscreteCoind G U A) G A where
  coe f := ((toCoind G U A f : coind G U A) : G → A)
  coe_injective _ _ h := (toCoind G U A).injective (Subtype.ext h)

@[ext]
theorem ext {f f' : DiscreteCoind G U A} (h : ∀ g : G, f g = f' g) : f = f' :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toCoind (f : DiscreteCoind G U A) :
    ((toCoind G U A f : coind G U A) : G → A) = ⇑f := rfl

@[simp]
theorem coe_toCoind_symm (f : coind G U A) :
    ⇑((toCoind G U A).symm f) = (f : G → A) := rfl

/-- The underlying function of an element of `Coind_U^G A` lies in `TauCeti.coind`. -/
theorem coe_mem (f : DiscreteCoind G U A) : ⇑f ∈ coind G U A := (toCoind G U A f).2

/-- An element of `Coind_U^G A` is locally constant. -/
theorem isLocallyConstant (f : DiscreteCoind G U A) : IsLocallyConstant ⇑f :=
  isLocallyConstant_of_mem_coind (coe_mem f)

/-- The defining equivariance `f (u * g) = u • f g`. -/
@[simp]
theorem apply_mul (f : DiscreteCoind G U A) (u : U) (g : G) : f ((u : G) * g) = u • f g :=
  apply_mul_of_mem_coind (coe_mem f) u g

/-- Equivariance at an element of `U`, in simp-normal form. -/
@[simp]
theorem apply_coe (f : DiscreteCoind G U A) (u : U) : f (u : G) = u • f 1 := by
  simpa using apply_mul f u 1

variable (G U A) in
/-- An element of `Coind_U^G A` from a locally constant `U`-equivariant function. The body is
`@[expose]`d so that `TauCeti.DiscreteCoind.coe_mk` recovers the function it was built from. -/
@[expose] def mk (f : G → A) (hlc : IsLocallyConstant f)
    (heq : ∀ (u : U) (g : G), f ((u : G) * g) = u • f g) : DiscreteCoind G U A :=
  (toCoind G U A).symm ⟨f, mem_coind_iff.2 ⟨hlc, heq⟩⟩

@[simp]
theorem coe_mk (f : G → A) (hlc : IsLocallyConstant f)
    (heq : ∀ (u : U) (g : G), f ((u : G) * g) = u • f g) : ⇑(mk G U A f hlc heq) = f := rfl

@[simp]
theorem mk_apply (f : G → A) (hlc : IsLocallyConstant f)
    (heq : ∀ (u : U) (g : G), f ((u : G) * g) = u • f g) (g : G) :
    mk G U A f hlc heq g = f g := rfl

@[simp]
theorem coe_zero : ⇑(0 : DiscreteCoind G U A) = 0 := rfl

@[simp]
theorem coe_add (f f' : DiscreteCoind G U A) : ⇑(f + f') = ⇑f + ⇑f' := rfl

@[simp]
theorem coe_neg (f : DiscreteCoind G U A) : ⇑(-f) = -⇑f := rfl

@[simp]
theorem coe_sub (f f' : DiscreteCoind G U A) : ⇑(f - f') = ⇑f - ⇑f' := rfl

section Scalar

variable {R : Type*} [Semiring R] [Module R A] [SMulCommClass U R A]

instance instSMulScalar : SMul R (DiscreteCoind G U A) :=
  inferInstanceAs (SMul R (coind G U A))

@[simp]
theorem coe_smul_scalar (r : R) (f : DiscreteCoind G U A) (g : G) :
    (r • f) g = r • f g := rfl

instance instModuleScalar : Module R (DiscreteCoind G U A) :=
  Function.Injective.module R (toCoind G U A).toAddMonoidHom
    (toCoind G U A).injective fun _ _ => rfl

end Scalar

variable (G U A) in
/-- **Evaluation at `1`** on the discrete carrier, the counit of coinduction. -/
def eval : DiscreteCoind G U A →+ A := (coindEval G U).comp (toCoind G U A).toAddMonoidHom

@[simp]
theorem eval_apply (f : DiscreteCoind G U A) : eval G U A f = f 1 := (rfl)

/-- Evaluation at `1` is continuous, the source being discrete. -/
theorem continuous_eval [TopologicalSpace A] : Continuous (eval G U A) :=
  continuous_of_discreteTopology

variable (G U A) in
/-- Evaluation at a point is continuous, the source being discrete. -/
theorem continuous_apply [TopologicalSpace A] (x : G) :
    Continuous fun f : DiscreteCoind G U A => f x := continuous_of_discreteTopology

section Action

variable [ContinuousMul G]

instance instDistribMulAction : DistribMulAction G (DiscreteCoind G U A) :=
  inferInstanceAs (DistribMulAction G (coind G U A))

@[simp]
theorem coe_smul (g : G) (f : DiscreteCoind G U A) (x : G) : (g • f) x = f (x * g) := (rfl)

/-- The counit is `U`-equivariant for the restriction of the right-translation action. This is the
compatible-pair hypothesis Shapiro's lemma is an instance of. -/
theorem eval_smul (u : U) (f : DiscreteCoind G U A) :
    eval G U A ((u : G) • f) = u • eval G U A f := by simp

/-- The `G`-stabilizer of an element of `Coind_U^G A` is its right-translation stabilizer. -/
theorem stabilizer_eq (f : DiscreteCoind G U A) :
    MulAction.stabilizer G f = rightTranslationStabilizer ⇑f := by
  ext g
  simp [MulAction.mem_stabilizer_iff, DFunLike.ext_iff]

end Action

section ScalarAction

variable {R : Type*} [Semiring R] [Module R A] [SMulCommClass U R A]

variable [ContinuousMul G] in
instance instSMulCommClass : SMulCommClass G R (DiscreteCoind G U A) :=
  ⟨fun g r f => ext fun x => by simp⟩

variable [TopologicalSpace R] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul R A] [CompactSpace G]

/-- The scalar orbit map `r ↦ r • f` of a discrete coinduced element is continuous when the group
`G` is compact and the coefficient module is discrete. Together these orbit maps give the
`ContinuousSMul R (DiscreteCoind G U A)` instance below. -/
theorem continuous_smul_const (f : DiscreteCoind G U A) : Continuous fun r : R => r • f := by
  rw [continuous_discrete_rng]
  intro y
  by_cases h : (fun r : R => r • f) ⁻¹' {y} = ∅
  · rw [h]
    exact isOpen_empty
  · obtain ⟨r₀, hr₀⟩ := Set.nonempty_iff_ne_empty.mpr h
    have hy : r₀ • f = y := hr₀
    rw [← hy]
    have hrange : (Set.range f).Finite := f.isLocallyConstant.range_finite
    have hopen : IsOpen (⋂ a ∈ Set.range f, (fun r : R => r • a) ⁻¹' {r₀ • a}) :=
      hrange.isOpen_biInter fun a _ =>
        (isOpen_discrete {r₀ • a}).preimage
          (continuous_smul.comp (continuous_id.prodMk continuous_const))
    convert hopen using 1
    ext r
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · intro hr a ha
      obtain ⟨g, rfl⟩ := ha
      exact congrArg (· g) hr
    · intro hr
      exact ext fun g => hr (f g) ⟨g, rfl⟩

instance instContinuousSMulScalar : ContinuousSMul R (DiscreteCoind G U A) :=
  ⟨continuous_prod_of_discrete_right.2 continuous_smul_const⟩

end ScalarAction

section Map

variable {R : Type*} [Semiring R] {B C : Type*}
  [Module R A] [SMulCommClass U R A]
  [AddCommGroup B] [Module R B] [DistribMulAction U B] [SMulCommClass U R B]
  [AddCommGroup C] [Module R C] [DistribMulAction U C] [SMulCommClass U R C]

/-- Coinduction of a `U`-equivariant linear map, acting pointwise on locally constant functions. -/
def map (f : A →ₗ[R] B) (hf : ∀ (u : U) (a : A), f (u • a) = u • f a) :
    DiscreteCoind G U A →ₗ[R] DiscreteCoind G U B where
  toAddHom := ((toCoind G U B).symm.toAddMonoidHom.comp
    ((coindMap G U f.toAddMonoidHom hf).comp (toCoind G U A).toAddMonoidHom)).toAddHom
  map_smul' _ _ := ext fun _ => map_smul f _ _

private theorem map_apply_impl (f : A →ₗ[R] B) (hf) (a : DiscreteCoind G U A) (g : G) :
    map f hf a g = f (a g) := rfl

@[simp]
theorem map_apply (f : A →ₗ[R] B) (hf) (a : DiscreteCoind G U A) (g : G) :
    map f hf a g = f (a g) := map_apply_impl f hf a g

/-- Coinduction of a coefficient map commutes with the right-translation action. -/
theorem map_smul [ContinuousMul G] (f : A →ₗ[R] B) (hf)
    (g : G) (a : DiscreteCoind G U A) : map f hf (g • a) = g • map f hf a := by
  ext x
  simp only [map_apply, coe_smul]

@[simp]
theorem map_id :
    map (G := G) (U := U) (LinearMap.id (R := R) (M := A)) (fun _ _ => rfl) =
      LinearMap.id := by
  ext a g
  rfl

-- Hypotheses on the left-hand side: see the comment on `TauCeti.coindMap_comp_coindMap`.
/-- Composing the maps of coinduced functions induced by two equivariant linear maps gives the map
induced by their composite. -/
@[simp]
theorem map_comp_map (f : A →ₗ[R] B) (hf) (f' : B →ₗ[R] C) (hf') :
    (map (G := G) (U := U) f' hf').comp (map (G := G) (U := U) f hf) =
      map (G := G) (U := U) (f'.comp f)
        (fun u a => by rw [LinearMap.comp_apply, hf, hf']; rfl) := by
  ext a g
  rfl

variable (R G U A) in
/-- Evaluation at `1` as a linear map, the counit of linear coinduction. -/
def evalLinear : DiscreteCoind G U A →ₗ[R] A where
  toAddHom := (eval G U A).toAddHom
  map_smul' _ _ := rfl

private theorem evalLinear_apply_impl (f : DiscreteCoind G U A) :
    evalLinear (R := R) G U A f = f 1 := rfl

@[simp]
theorem evalLinear_apply (f : DiscreteCoind G U A) : evalLinear (R := R) G U A f = f 1 :=
  evalLinear_apply_impl f

end Map

section Trace

variable [ContinuousMul G] [U.FiniteIndex]
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (G U M) in
/-- The `G`-equivariant additive trace `DiscreteCoind G U M →+[G] M`. -/
noncomputable def trace : DiscreteCoind G U M →+[G] M where
  toFun f := coindTrace G U (toCoind G U M f)
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  map_smul' g f := coindTrace_smul g (toCoind G U M f)

/-- The discrete-carrier trace is the unbundled trace after forgetting the discrete topology. -/
theorem coindTrace_toCoind (f : DiscreteCoind G U M) :
    coindTrace G U (toCoind G U M f) = trace G U M f := (rfl)

@[simp]
theorem trace_apply (f : DiscreteCoind G U M) :
    trace G U M f = ∑ x : G ⧸ U, x.out • f x.out⁻¹ :=
  (coindTrace_apply (toCoind G U M f)).trans
    (Finset.sum_congr rfl fun x _ => coindTraceTerm_out (toCoind G U M f) x)

/-- The discrete-carrier trace computed along an arbitrary transversal. -/
theorem trace_eq_sum_transversal (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (f : DiscreteCoind G U M) : trace G U M f = ∑ x : G ⧸ U, t x • f (t x)⁻¹ := by
  rw [← coindTrace_toCoind]
  simpa only [coe_toCoind] using
    coindTrace_eq_sum_transversal t ht (toCoind G U M f)

/-- The discrete-carrier trace is natural in `G`-equivariant linear coefficient maps. -/
theorem trace_map {R N : Type*} [Semiring R] [AddCommGroup N] [DistribMulAction G N]
    [Module R M] [SMulCommClass G R M] [Module R N] [SMulCommClass G R N]
    (φ : M →ₗ[R] N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    (f : DiscreteCoind G U M) :
    trace G U N (map φ (fun u m => hφ (u : G) m) f) = φ (trace G U M f) := by
  exact coindTrace_coindMap (G := G) (U := U) φ.toAddMonoidHom hφ (toCoind G U M f)

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
    -- Expose the additive trace under the linear-map coercion before using its sum formula.
    change trace G U M (r • f) = r • trace G U M f
    rw [trace_apply, trace_apply, Finset.smul_sum]
    simp only [coe_smul_scalar]
    exact Finset.sum_congr rfl fun x _ => smul_comm x.out r (f x.out⁻¹)

@[simp]
theorem traceLinear_apply (f : DiscreteCoind G U M) :
    traceLinear (R := R) G U M f = trace G U M f := by
  -- Expose the additive trace under the linear-map coercion.
  change trace G U M f = trace G U M f
  rfl

end Scalar

end Trace

/-- **`Coind_U^G A` is a discrete `G`-module over a compact group**: the right-translation action
on the discrete carrier is continuous, because a locally constant function on a compact group is
uniformly locally constant. -/
instance instContinuousSMul [IsTopologicalGroup G] [CompactSpace G] :
    ContinuousSMul G (DiscreteCoind G U A) :=
  continuousSMul_iff_stabilizer_isOpen.2 fun f => by
    rw [stabilizer_eq]
    exact isOpen_rightTranslationStabilizer (isLocallyConstant f)

end DiscreteCoind

end DiscreteCarrier

end TauCeti
