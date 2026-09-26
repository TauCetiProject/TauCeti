/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Module.Pi
public import TauCeti.Topology.Algebra.Group.LocallyConstant
public import TauCeti.Topology.Algebra.Group.Profinite.Section

import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# The coinduced module of a subgroup

For a topological group `G`, a subgroup `U` and a `U`-module `A`, the **coinduced module**
```
Coind_U^G A = {f : G → A | f locally constant, f (u * g) = u • f g for all u ∈ U, g ∈ G}
```
carries the right-translation action `(g • f) x = f (x * g)` of `G`. It is Milne's `M_*`
(*Arithmetic Duality Theorems*, Remark 0.11) and Ribes-Zalesskii's `Coind_U^G`
(*Profinite Groups*, Thm. 6.10.5), and it is the coefficient module Shapiro's lemma is stated
against.

This file builds `TauCeti.coind`, as an additive subgroup of `G → A`, and the properties Shapiro's
lemma and the dimension-shifting argument consume. The coinduced module is carried as a
*discrete* `G`-module by `TauCeti.DiscreteCoind` in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete`. It is packaged as a
functor between categories of smooth discrete representations, and compared with Mathlib's
`Representation.coind`, in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor`.

## Main definitions

* `TauCeti.coind`: the coinduced module `Coind_U^G A`, a `G`-module under right translation
  (`TauCeti.instDistribMulActionCoind`);
* `TauCeti.coindEval`: evaluation at `1`, the counit of coinduction;
* `TauCeti.coindMap`: the functoriality of coinduction in `A` along `U`-equivariant additive maps;
* `TauCeti.coindTrace`: for finite-index `U`, the trace `f ↦ ∑ x : G ⧸ U, x • f x⁻¹`.

## Main results

* `TauCeti.isOpen_stabilizer_coind`: the right-translation stabilizers are open for compact `G`,
  which is exactly what makes the coinduced module a *discrete* `G`-module in the sense of a
  continuous action on a discrete module;
* `TauCeti.coindMap_injective`, `TauCeti.coindMap_surjective` and
  `TauCeti.coindMap_range_eq_ker`: coinduction is **exact** in `A`, sending a short exact sequence
  of discrete `U`-modules to a short exact sequence;
* `TauCeti.coindTrace_smul` and `TauCeti.coindTrace_coindMap`: the trace is `G`-equivariant and
  natural in the coefficients;
* `TauCeti.mem_coind_bot_iff`: membership in `Coind_1^G A` is local constancy, so it is the group
  of all locally constant maps `G → A`, the acyclic module of the dimension-shifting argument;
* `TauCeti.coindEvalTopEquiv`: `Coind_G^G A` is `A`.

Surjectivity is where the topology does real work. Lifting a locally constant `U`-equivariant map
`G → B` through a surjection `A ↠ B` means choosing preimages coherently along the right cosets
`U \ G`, and the choice has to stay locally constant. The continuous section of `G → G ⧸ U`
(`TauCeti.exists_continuous_section`, Ribes-Zalesskii Prop. 2.2.2) supplies it: inverting turns a
continuous section of the *left* coset space into a continuous choice `s'` of representatives of
the *right* cosets, and `g ↦ g * (s' g)⁻¹` is then a continuous `U`-valued cocycle by which the
lift is transported. Discreteness of `A` and continuity of the `U`-action are what make the
transported lift locally constant again.

## Implementation notes

Mathlib's `ContRepresentation.coindV` is an analogous construction in the bundled continuous-
representation language: in this file's notation, a `Submodule R C(G, V)` attached to a
`ContRepresentation R U V` and the inclusion `U → G`. It is not used here because the
`ContRepresentation` carrier imposes no continuity of the action in the group variable, which is
needed by `TauCeti.coindMap_surjective`; `TauCeti.coindEvalTopEquiv` similarly requires continuity
of each orbit map. The discrete coefficient modules here are also given by the unbundled classes
`[DistribMulAction U A]`, `[DiscreteTopology A]`, `[ContinuousSMul U A]`, and local constancy is a
predicate on plain functions rather than a bundled `C(G, A)`.

For finite-index subgroups, Mathlib's algebraic `Rep.coindResAdjunction` has the trace as its
counit. Its coinduced object consists of all equivariant functions in `Rep k G`, whereas this file
uses locally constant functions and only identifies the two for an open subgroup of a compact
group (`TauCeti.topologicalCoindIsoAlgebraic`). Mathlib's element formula is recorded in
`Subgroup.coindResAdjunction_counit_app_hom_apply`, and
`TauCeti.groupCohomology.corestriction` builds the corresponding algebraic all-degree
corestriction. Those use the right-coset convention `∑ g, g⁻¹ • f g`; the continuous trace here
uses the equivalent left-coset convention `∑ x, x • f x⁻¹`. They cannot be reused directly
because their coefficients live in the purely algebraic category `Rep k G`, while continuous
cohomology uses this file's locally constant coinduction on discrete modules.

The trace construction follows Brown, *Cohomology of Groups*, III §9.
-/

-- Blueprint: Layer 7 (coinduced modules and Shapiro's lemma) of the human-authored roadmap
-- `TauCetiRoadmap/ProfiniteCohomology/README.md`.

public section

namespace TauCeti

section Defs

variable (G : Type*) [Group G] [TopologicalSpace G] (U : Subgroup G)
  (A : Type*) [AddCommGroup A] [DistribMulAction U A]

/-- The **coinduced module** `Coind_U^G A` of a subgroup `U ≤ G` and a `U`-module `A`: the locally
constant maps `f : G → A` with `f (u * g) = u • f g` for every `u : U` and `g : G`. The
`G`-action is right translation, `(g • f) x = f (x * g)`. -/
def coind : AddSubgroup (G → A) where
  carrier := {f | IsLocallyConstant f ∧ ∀ (u : U) (g : G), f ((u : G) * g) = u • f g}
  add_mem' {a b} ha hb :=
    ⟨(ha.1.prodMk hb.1).comp fun p => p.1 + p.2, fun u g => by
      simp [ha.2 u g, hb.2 u g, smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun u g => by simp⟩
  neg_mem' {a} ha := ⟨ha.1.comp fun x => -x, fun u g => by simp [ha.2 u g, smul_neg]⟩

variable {G U A}

theorem mem_coind_iff {f : G → A} :
    f ∈ coind G U A ↔
      IsLocallyConstant f ∧ ∀ (u : U) (g : G), f ((u : G) * g) = u • f g := Iff.rfl

/-- A member of the coinduced module is locally constant. -/
theorem isLocallyConstant_of_mem_coind {f : G → A} (hf : f ∈ coind G U A) :
    IsLocallyConstant f := hf.1

/-- A member of the coinduced module is `U`-equivariant. -/
theorem apply_mul_of_mem_coind {f : G → A} (hf : f ∈ coind G U A) (u : U) (g : G) :
    f ((u : G) * g) = u • f g := hf.2 u g

/-- The equivariance of a bundled element of the coinduced module, in the form `simp` can use
without a separate membership hypothesis. -/
@[simp]
theorem coind_apply_mul (f : coind G U A) (u : U) (g : G) :
    (f : G → A) ((u : G) * g) = u • (f : G → A) g := apply_mul_of_mem_coind f.2 u g

/-- Equivariance at an element of `U`, in simp-normal form. -/
@[simp]
theorem coind_apply_coe (f : coind G U A) (u : U) :
    (f : G → A) (u : G) = u • (f : G → A) 1 := by
  simpa using coind_apply_mul f u 1

end Defs

section Scalar

variable {R G A : Type*} [Semiring R] [Group G] [TopologicalSpace G] {U : Subgroup G}
  [AddCommGroup A] [Module R A] [DistribMulAction U A] [SMulCommClass U R A]

instance instSMulCoindScalar : SMul R (coind G U A) where
  smul r f :=
    ⟨fun g => r • f.1 g,
      mem_coind_iff.2 ⟨(isLocallyConstant_of_mem_coind f.2).comp (fun a => r • a), fun u g => by
        rw [apply_mul_of_mem_coind f.2 u g]
        exact (smul_comm u r _).symm⟩⟩

@[simp]
theorem coind_scalar_smul_apply (r : R) (f : coind G U A) (g : G) :
    ((r • f : coind G U A) : G → A) g = r • f.1 g := rfl

instance instModuleCoindScalar : Module R (coind G U A) :=
  Function.Injective.module R (AddSubgroup.subtype _) Subtype.val_injective fun _ _ => rfl

end Scalar

section Action

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  {A : Type*} [AddCommGroup A] [DistribMulAction U A]

theorem rightTranslation_mem_coind {f : G → A} (hf : f ∈ coind G U A) (g : G) :
    (fun x : G => f (x * g)) ∈ coind G U A :=
  ⟨(isLocallyConstant_of_mem_coind hf).comp_continuous (continuous_mul_const g),
    fun u x => by simpa [mul_assoc] using apply_mul_of_mem_coind hf u (x * g)⟩

instance instSMulCoind : SMul G (coind G U A) where
  smul g f := ⟨fun x => (f : G → A) (x * g), rightTranslation_mem_coind f.2 g⟩

@[simp]
theorem coind_smul_apply (g : G) (f : coind G U A) (x : G) :
    ((g • f : coind G U A) : G → A) x = (f : G → A) (x * g) := rfl

instance instDistribMulActionCoind : DistribMulAction G (coind G U A) where
  one_smul f := by ext x; simp
  mul_smul g g' f := by ext x; simp [mul_assoc]
  smul_zero g := by ext x; simp
  smul_add g f f' := by ext x; simp

/-- The `G`-stabilizer of a coinduced element is its right-translation stabilizer. -/
theorem stabilizer_coind_eq (f : coind G U A) :
    MulAction.stabilizer G f = rightTranslationStabilizer (f : G → A) := by
  ext g
  rw [mem_rightTranslationStabilizer]
  exact ⟨fun h x => congrFun (Subtype.ext_iff.mp h) x,
    fun h => Subtype.ext (funext fun x => h x)⟩

end Action

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [CompactSpace G]
  {U : Subgroup G} {A : Type*} [AddCommGroup A] [DistribMulAction U A]

/-- **The coinduced module of a compact group is a discrete `G`-module**: every stabilizer of the
right-translation action is open. This is uniform local constancy
(`TauCeti.isOpen_rightTranslationStabilizer`), and it is the reason the coinduced module can be
used as coefficients for continuous cohomology. -/
theorem isOpen_stabilizer_coind (f : coind G U A) :
    IsOpen (MulAction.stabilizer G f : Set G) := by
  rw [stabilizer_coind_eq]
  exact isOpen_rightTranslationStabilizer (isLocallyConstant_of_mem_coind f.2)

end Smooth

section Functoriality

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A B C : Type*} [AddCommGroup A] [DistribMulAction U A] [AddCommGroup B]
  [DistribMulAction U B] [AddCommGroup C] [DistribMulAction U C]

variable (G U) in
/-- **Evaluation at `1`**, the counit of coinduction: `Coind_U^G A →+ A`. It is `U`-equivariant
(`TauCeti.coindEval_smul`) and natural in `A` (`TauCeti.coindEval_coindMap`). -/
def coindEval : coind G U A →+ A where
  toFun f := (f : G → A) 1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coindEval_apply (f : coind G U A) : coindEval G U f = (f : G → A) 1 := (rfl)

/-- The counit is `U`-equivariant for the restriction of the right-translation action. -/
theorem coindEval_smul [ContinuousMul G] (u : U) (f : coind G U A) :
    coindEval G U ((u : G) • f) = u • coindEval G U f := by simp

variable (G U) in
/-- **Coinduction is functorial in the coefficients**: a `U`-equivariant additive map `φ : A →+ B`
induces `Coind_U^G A →+ Coind_U^G B` by postcomposition. -/
def coindMap (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) :
    coind G U A →+ coind G U B where
  toFun f := ⟨fun g => φ ((f : G → A) g),
    ⟨(isLocallyConstant_of_mem_coind f.2).comp φ, fun u g => by simp [hφ]⟩⟩
  map_zero' := by ext g; simp
  map_add' _ _ := by ext g; simp

@[simp]
theorem coindMap_apply (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (f : coind G U A) (g : G) :
    ((coindMap G U φ hφ f : coind G U B) : G → B) g = φ ((f : G → A) g) := (rfl)

/-- Coinduction of the identity is the identity. -/
@[simp]
theorem coindMap_id : coindMap G U (AddMonoidHom.id A) (fun _ _ => rfl) = AddMonoidHom.id _ := by
  ext f g; simp

-- The composition `simp` lemmas take both equivariance hypotheses on the left-hand side and derive
-- the equivariance of the composite on the right: a hypothesis occurring on the left only inside a
-- proof is not assigned by unification, and `simp` cannot prove an equivariance for symbolic maps.
/-- The composite of two coinductions is the coinduction of the composite. -/
@[simp]
theorem coindMap_comp_coindMap (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (ψ : B →+ C) (hψ : ∀ (u : U) (b : B), ψ (u • b) = u • ψ b) :
    (coindMap G U ψ hψ).comp (coindMap G U φ hφ) =
      coindMap G U (ψ.comp φ) (fun u a => by rw [AddMonoidHom.comp_apply, hφ, hψ]; rfl) := by
  ext f g; simp

/-- The counit is natural in the coefficients. -/
theorem coindEval_coindMap (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (f : coind G U A) : coindEval G U (coindMap G U φ hφ f) = φ (coindEval G U f) := (rfl)

/-- `coindMap` is `G`-equivariant. -/
@[simp]
theorem coindMap_smul [ContinuousMul G] (φ : A →+ B)
    (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) (g : G) (f : coind G U A) :
    coindMap G U φ hφ (g • f) = g • coindMap G U φ hφ f := by
  ext x; simp

end Functoriality

section Trace

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]

variable (U) in
/-- The summand `x • f x⁻¹` of the trace of a coinduced element, as a function of the coset
`x U` rather than of `x`. It is well defined because `f` is `U`-equivariant: replacing a
representative `x` by `x * u` multiplies the value of `f` by `u⁻¹` and the outer action by `u`. -/
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

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (G U) in
/-- **The trace of the coinduced module**, `f ↦ ∑ x : G ⧸ U, x • f x⁻¹`. This is the coefficient
map used after Shapiro's isomorphism in the coinduction construction of corestriction. -/
noncomputable def coindTrace : coind G U M →+ M where
  toFun f := ∑ x : G ⧸ U, coindTraceTerm U f x
  map_zero' := by simp
  map_add' f f' := by simp [Finset.sum_add_distrib]

theorem coindTrace_apply (f : coind G U M) :
    coindTrace G U f = ∑ x : G ⧸ U, coindTraceTerm U f x := (rfl)

/-- The trace computed along an arbitrary transversal `t : G ⧸ U → G`. -/
theorem coindTrace_eq_sum_transversal (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (f : coind G U M) :
    coindTrace G U f = ∑ x : G ⧸ U, t x • (f : G → M) (t x)⁻¹ := by
  rw [coindTrace_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [← coindTraceTerm_mk f (t x), ht x]

/-- The trace is `G`-equivariant for the right-translation action on the coinduced module. -/
theorem coindTrace_smul [ContinuousMul G] (g : G) (f : coind G U M) :
    coindTrace G U (g • f) = g • coindTrace G U f := by
  rw [coindTrace_apply, coindTrace_apply, Finset.smul_sum]
  calc
    ∑ x : G ⧸ U, coindTraceTerm U (g • f) x
        = ∑ x : G ⧸ U, g • coindTraceTerm U f (g⁻¹ • x) :=
      Finset.sum_congr rfl fun x _ => coindTraceTerm_smul g f x
    _ = ∑ x : G ⧸ U, g • coindTraceTerm U f x :=
      Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun x =>
        congrArg (fun y => g • coindTraceTerm U f y) (MulAction.toPerm_apply g⁻¹ x).symm

/-- The trace is natural in the coefficient module: a `G`-equivariant map of coefficients
commutes with it. -/
theorem coindTrace_coindMap {N : Type*} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (f : coind G U M) :
    coindTrace G U (coindMap G U φ (fun u m => hφ (u : G) m) f) = φ (coindTrace G U f) := by
  rw [coindTrace_apply, coindTrace_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coindTraceTerm_out, coindTraceTerm_out, coindMap_apply, hφ]

/-- The trace of the whole group is evaluation at `1`: the only coset is `U` itself. -/
@[simp]
theorem coindTrace_top_eq_coindEval (f : coind G ⊤ M) :
    coindTrace G ⊤ f = coindEval G ⊤ f := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  rw [coindTrace_apply,
    Fintype.sum_subsingleton (coindTraceTerm (⊤ : Subgroup G) f) ((1 : G) : G ⧸ (⊤ : Subgroup G)),
    coindTraceTerm_mk]
  simp

end Trace

section Exactness

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A B C : Type*} [AddCommGroup A] [DistribMulAction U A] [AddCommGroup B]
  [DistribMulAction U B] [AddCommGroup C] [DistribMulAction U C]

/-- **Coinduction preserves injectivity.** No topological hypothesis is needed: the induced map is
postcomposition. -/
theorem coindMap_injective (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (hinj : Function.Injective φ) : Function.Injective (coindMap G U φ hφ) := fun _ _ h =>
  Subtype.ext (funext fun g => hinj (congrFun (Subtype.ext_iff.mp h) g))

/-- **Coinduction is exact in the middle.** If `A →+ B →+ C` is exact at `B` with `φ` injective,
then the coinduced sequence is exact at `Coind_U^G B`. Choosing the preimage is unambiguous, so no
section of the group is needed here; that is only the case in
`TauCeti.coindMap_surjective`. -/
theorem coindMap_range_eq_ker (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (ψ : B →+ C) (hψ : ∀ (u : U) (b : B), ψ (u • b) = u • ψ b) (hinj : Function.Injective φ)
    (hexact : AddMonoidHom.range φ = AddMonoidHom.ker ψ) :
    AddMonoidHom.range (coindMap G U φ hφ) = AddMonoidHom.ker (coindMap G U ψ hψ) := by
  have : Nonempty A := ⟨0⟩
  have hli : ∀ a : A, Function.invFun φ (φ a) = a := Function.leftInverse_invFun hinj
  ext F
  simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨f, rfl⟩
    refine Subtype.ext (funext fun g => ?_)
    have h : φ ((f : G → A) g) ∈ AddMonoidHom.ker ψ := hexact ▸ ⟨_, rfl⟩
    simpa using h
  · intro hF
    have hmem : ∀ g : G, (F : G → B) g ∈ AddMonoidHom.range φ := fun g => by
      rw [hexact]
      exact congrFun (Subtype.ext_iff.mp hF) g
    have hinvFun : ∀ g : G, φ (Function.invFun φ ((F : G → B) g)) = (F : G → B) g := fun g =>
      Function.invFun_eq (hmem g)
    refine ⟨⟨fun g => Function.invFun φ ((F : G → B) g),
      (isLocallyConstant_of_mem_coind F.2).comp (Function.invFun φ), fun u g => ?_⟩, ?_⟩
    · obtain ⟨a, ha⟩ := hmem g
      have h1 : (F : G → B) ((u : G) * g) = φ (u • a) := by
        rw [apply_mul_of_mem_coind F.2 u g, ← ha, hφ]
      simp only [h1, ← ha, hli]
    · exact Subtype.ext (funext hinvFun)

end Exactness

section Surjectivity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {U : Subgroup G}
  {A B : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A] [AddCommGroup B] [DistribMulAction U B]

/-- **Coinduction preserves surjectivity**, and this is where the topology does the work: a
locally constant `U`-equivariant map `G → B` is lifted through `φ` by choosing preimages along a
*continuous* factorization of `G` over the right cosets of `U`
(`TauCeti.exists_continuous_rightCosetFactorization`, from the continuous coset section). The
factor `w g •` is forced — without it the lift is not `U`-equivariant — and it is exactly what
discreteness of `A` and continuity of the `U`-action make locally constant again.

Together with `TauCeti.coindMap_injective` and `TauCeti.coindMap_range_eq_ker` this says that
coinduction along a closed subgroup of a profinite group sends a short exact sequence of discrete
`U`-modules to a short exact sequence of discrete `G`-modules. -/
theorem coindMap_surjective (hU : IsClosed (U : Set G)) (φ : A →+ B)
    (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) (hsurj : Function.Surjective φ) :
    Function.Surjective (coindMap G U φ hφ) := by
  obtain ⟨w, r, hw_cont, hr_cont, hwr, hw_mul, hr_mul, -⟩ :=
    exists_continuous_rightCosetFactorization U hU
  intro F
  have hF : IsLocallyConstant fun g : G => (F : G → B) (r g) :=
    (isLocallyConstant_of_mem_coind F.2).comp_continuous hr_cont
  refine ⟨⟨fun g => w g • Function.surjInv hsurj ((F : G → B) (r g)), ?_, fun u g => ?_⟩, ?_⟩
  · exact (IsLocallyConstant.iff_continuous _).2 (continuous_smul.comp
      (hw_cont.prodMk (hF.comp (Function.surjInv hsurj)).continuous))
  · simp only [hw_mul u g, hr_mul u g, mul_smul]
  · refine Subtype.ext (funext fun g => ?_)
    rw [coindMap_apply, hφ, Function.surjInv_eq hsurj,
      ← apply_mul_of_mem_coind F.2 (w g) (r g), hwr g]

end Surjectivity

section Degenerate

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **`Coind_1^G A` is the group of all locally constant maps `G → A`**: for the trivial subgroup
the equivariance condition is vacuous. This is the module the dimension-shifting argument
embeds a discrete module into. -/
@[simp]
theorem mem_coind_bot_iff {A : Type*} [AddCommGroup A] [DistribMulAction (⊥ : Subgroup G) A]
    {f : G → A} : f ∈ coind G ⊥ A ↔ IsLocallyConstant f :=
  ⟨fun hf => hf.1, fun hf => ⟨hf, fun u g => by
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp u.2)
    rw [hu, OneMemClass.coe_one, one_mul, one_smul]⟩⟩

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (⊤ : Subgroup G) A]

/-- For `U = ⊤` the orbit map `g ↦ g • a` is a member of the coinduced module: it is locally
constant because that orbit map is continuous and `A` is discrete. -/
theorem smul_mem_coind_top {a : A}
    (hcont : Continuous fun g : G => (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a) :
    (fun g : G => (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a) ∈ coind G ⊤ A := by
  refine ⟨(IsLocallyConstant.iff_continuous _).2 hcont, fun u g => ?_⟩
  have h : (⟨(u : G) * g, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) =
      u * ⟨g, Subgroup.mem_top g⟩ := Subtype.ext rfl
  simp only [h, mul_smul]

variable (G A) in
/-- **`Coind_G^G A` is `A`**: evaluation at `1` is an isomorphism, with inverse `a ↦ (g ↦ g • a)`.
The inverse uses continuity of each orbit map; without it `g ↦ g • a` need not be locally
constant. -/
def coindEvalTopEquiv
    (hcont : ∀ a : A, Continuous fun g : G =>
      (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a) : coind G ⊤ A ≃+ A where
  toFun f := (f : G → A) 1
  invFun a := ⟨_, smul_mem_coind_top (hcont a)⟩
  left_inv f := Subtype.ext (funext fun g => by
    simpa using (apply_mul_of_mem_coind f.2 ⟨g, Subgroup.mem_top g⟩ 1).symm)
  right_inv a := by
    have h : (⟨(1 : G), Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) = 1 := Subtype.ext rfl
    simp [h]
  map_add' _ _ := (rfl)

@[simp]
theorem coindEvalTopEquiv_apply
    (hcont : ∀ a : A, Continuous fun g : G =>
      (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a) (f : coind G ⊤ A) :
    coindEvalTopEquiv G A hcont f = (f : G → A) 1 := (rfl)

@[simp]
theorem coindEvalTopEquiv_symm_apply
    (hcont : ∀ a : A, Continuous fun g : G =>
      (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a) (a : A) (g : G) :
    (((coindEvalTopEquiv G A hcont).symm a : coind G ⊤ A) : G → A) g =
      (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a := (rfl)

end Degenerate

end TauCeti
