/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete
public import TauCeti.Topology.Algebra.Group.LocallyConstant
public import TauCeti.Topology.Algebra.Group.Profinite.Section

/-!
# The coinduced discrete module of a subgroup

For a topological group `G`, a subgroup `U` and a `U`-module `A`, the **coinduced module**
```
Coind_U^G A = {f : G → A | f locally constant, f (u * g) = u • f g for all u ∈ U, g ∈ G}
```
carries the right-translation action `(g • f) x = f (x * g)` of `G`. It is Milne's `M_*`
(*Arithmetic Duality Theorems*, Remark 0.11) and Ribes-Zalesskii's `Coind_U^G`
(*Profinite Groups*, Thm. 6.10.5), and it is the coefficient module Shapiro's lemma is stated
against.

This file builds `TauCeti.coind` and the properties Shapiro's lemma and the dimension-shifting
argument consume:

* it is a `G`-module (`TauCeti.instDistribMulActionCoind`) whose right-translation stabilizers are
  open for compact `G` (`TauCeti.isOpen_stabilizer_coind`), which is exactly what makes it a
  *discrete* `G`-module in the sense of a continuous action on a discrete module;
* it is functorial in `A` along `U`-equivariant additive maps (`TauCeti.coindMap`), the counit
  being evaluation at `1` (`TauCeti.coindEval`);
* it is **exact** in `A`: `TauCeti.coindMap_injective`, `TauCeti.coindMap_surjective` and
  `TauCeti.coindMap_range_eq_ker` send a short exact sequence of discrete `U`-modules to a short
  exact sequence;
* it is carried as a *discrete* `G`-module by `TauCeti.DiscreteCoind`, the same additive group
  with the discrete topology imposed, which is the coefficient object the explicit low-degree
  cohomology of Layer 2 takes;
* scalar multiplication is continuous on that discrete carrier for compact `G`, and coefficient
  maps induce linear maps (`TauCeti.DiscreteCoind.map`);
* it is packaged as the functor `TauCeti.coindFunctor` between categories of smooth discrete
  representations;
* the two degenerate subgroups are computed: `TauCeti.mem_coind_bot_iff` characterizes membership
  in `Coind_1^G A` as local constancy, so it is the group of all locally constant maps `G → A`,
  the acyclic module of the dimension-shifting argument, and
  `TauCeti.coindEvalTopEquiv` says `Coind_G^G A` is `A`.

Surjectivity is where the topology does real work. Lifting a locally constant `U`-equivariant map
`G → B` through a surjection `A ↠ B` means choosing preimages coherently along the right cosets
`U \ G`, and the choice has to stay locally constant. Layer 0's continuous section of `G → G ⧸ U`
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
of each orbit map. It is also not used because the roadmap fixes the unbundled classes
`[DistribMulAction U A]`, `[DiscreteTopology A]`, `[ContinuousSMul U A]` for this layer, with local
constancy as a predicate on plain functions rather than a bundled `C(G, A)`. The final construction
uses the smooth-discrete dictionary to transport this unbundled module to the categorical language.

This is the "coinduced module" milestone of Layer 7 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`.
-/

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

/-- Coinduction of a composite is the composite of the coinductions. -/
@[simp]
theorem coindMap_comp (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (ψ : B →+ C) (hψ : ∀ (u : U) (b : B), ψ (u • b) = u • ψ b) :
    coindMap G U (ψ.comp φ) (fun u a => by rw [AddMonoidHom.comp_apply, hφ, hψ]; rfl) =
      (coindMap G U ψ hψ).comp (coindMap G U φ hφ) := by
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
(`TauCeti.exists_continuous_rightCosetFactorization`, from Layer 0's continuous section). The
factor `w g •` is forced — without it the lift is not `U`-equivariant — and it is exactly what
discreteness of `A` and continuity of the `U`-action make locally constant again.

Together with `TauCeti.coindMap_injective` and `TauCeti.coindMap_range_eq_ker` this says that
coinduction along a closed subgroup of a profinite group sends a short exact sequence of discrete
`U`-modules to a short exact sequence of discrete `G`-modules. -/
theorem coindMap_surjective (hU : IsClosed (U : Set G)) (φ : A →+ B)
    (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) (hsurj : Function.Surjective φ) :
    Function.Surjective (coindMap G U φ hφ) := by
  obtain ⟨w, r, hw_cont, hr_cont, hwr, hw_mul, hr_mul⟩ :=
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

/-- The scalar orbit map of every discrete coinduced element is continuous when the source group
is compact and the coefficient module is discrete. -/
theorem continuous_const_smul (f : DiscreteCoind G U A) : Continuous fun r : R => r • f := by
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
  ⟨continuous_prod_of_discrete_right.2 continuous_const_smul⟩

end ScalarAction

section Map

variable {R : Type*} [Semiring R] {B C : Type*}
  [Module R A] [SMulCommClass U R A]
  [AddCommGroup B] [Module R B] [DistribMulAction U B] [SMulCommClass U R B]
  [AddCommGroup C] [Module R C] [DistribMulAction U C] [SMulCommClass U R C]

/-- Coinduction of a `U`-equivariant linear map, acting pointwise on locally constant functions. -/
@[expose] def map (f : A →ₗ[R] B) (hf : ∀ (u : U) (a : A), f (u • a) = u • f a) :
    DiscreteCoind G U A →ₗ[R] DiscreteCoind G U B where
  toFun a := mk G U B (fun g => f (a g)) (a.isLocallyConstant.comp f)
    (fun u g => by rw [a.apply_mul, hf])
  map_add' _ _ := ext fun _ => map_add f _ _
  map_smul' _ _ := ext fun _ => map_smul f _ _

@[simp]
theorem map_apply (f : A →ₗ[R] B) (hf) (a : DiscreteCoind G U A) (g : G) :
    map f hf a g = f (a g) := rfl

@[simp]
theorem map_id :
    map (G := G) (U := U) (LinearMap.id (R := R) (M := A)) (fun _ _ => rfl) =
      LinearMap.id := by
  ext a g
  rfl

@[simp]
theorem map_comp (f : A →ₗ[R] B) (hf) (f' : B →ₗ[R] C) (hf') :
    map (G := G) (U := U) (f'.comp f)
        (fun u a => by rw [LinearMap.comp_apply, hf, hf']; rfl) =
      (map (G := G) (U := U) f' hf').comp (map (G := G) (U := U) f hf) := by
  ext a g
  rfl

variable (R G U A) in
/-- Evaluation at `1` as a linear map, the counit of linear coinduction. -/
@[expose] def evalLinear : DiscreteCoind G U A →ₗ[R] A where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalLinear_apply (f : DiscreteCoind G U A) : evalLinear (R := R) G U A f = f 1 := rfl

@[simp]
theorem evalLinear_map (f : A →ₗ[R] B) (hf) (a : DiscreteCoind G U A) :
    evalLinear (R := R) G U B (map f hf a) = f (evalLinear (R := R) G U A a) := rfl

end Map

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

section Bundled

open CategoryTheory

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance instDiscreteTopologyOfSmoothDiscreteCoind
    {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Monoid G] [TopologicalSpace G]
    (A : SmoothDiscreteTopRep.{u, v, w} R G) : DiscreteTopology A.obj.V :=
  A.property.discreteTopology

local instance instContinuousSMulOfSmoothDiscreteCoind
    {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (A : SmoothDiscreteTopRep.{u, v, w} R G) :
    ContinuousSMul G A.obj.V := A.property.continuousSMul

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

/-- The locally constant coinduced module, bundled as a discrete representation of `G`. -/
noncomputable abbrev coindDiscreteRep (A : DiscreteRep.{u, v, w} R U) :
    DiscreteRep.{u, v, max v w} R G where
  V := DiscreteCoind G U A.V
  smulCommClass := DiscreteCoind.instSMulCommClass
  continuousSMulRing := DiscreteCoind.instContinuousSMulScalar

/-- Coinduction from discrete `U`-representations to discrete `G`-representations. -/
@[expose] noncomputable def coindDiscreteFunctor :
    DiscreteRep.{u, v, w} R U ⥤ DiscreteRep.{u, v, max v w} R G where
  obj := coindDiscreteRep R G U
  map {A B} f :=
    (DiscreteCoind.map f.toLinearMap
      (DiscreteRep.equivariant f)).intertwiningMap_of_isIntertwiningMap _ _ fun g a => by
        apply DiscreteCoind.ext
        intro x
        rfl
  map_id A := Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    DiscreteCoind.ext fun g => by rfl)
  map_comp f f' := Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    DiscreteCoind.ext fun g => by rfl)

/-- The object part of discrete coinduction is the locally constant coinduced representation. -/
@[simp]
theorem coindDiscreteFunctor_obj (A : DiscreteRep.{u, v, w} R U) :
    (coindDiscreteFunctor R G U).obj A = coindDiscreteRep R G U A := rfl

@[simp]
theorem coindDiscreteFunctor_map_apply {A B : DiscreteRep.{u, v, w} R U}
    (f : A ⟶ B) (a : DiscreteCoind G U A.V) (g : G) :
    ((show Representation.IntertwiningMap
        (coindDiscreteRep R G U A).ρ (coindDiscreteRep R G U B).ρ
      from (coindDiscreteFunctor R G U).map f) a) g = f.toLinearMap (a g) := by
  change DiscreteCoind.map f.toLinearMap (DiscreteRep.equivariant f) a g = _
  exact DiscreteCoind.map_apply f.toLinearMap _ a g

/-- The locally constant coinduced module, bundled as a smooth discrete representation of `G`. -/
noncomputable abbrev coindTopRep (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    SmoothDiscreteTopRep.{u, v, max v w} R G :=
  (toSmoothDiscrete R G).obj (coindDiscreteRep R G U ((ofSmoothDiscrete R U).obj A))

/-- Coinduction from smooth discrete `U`-representations to smooth discrete
`G`-representations. -/
@[expose] noncomputable def coindFunctor :
    SmoothDiscreteTopRep.{u, v, w} R U ⥤ SmoothDiscreteTopRep.{u, v, max v w} R G :=
  ofSmoothDiscrete R U ⋙ coindDiscreteFunctor R G U ⋙ toSmoothDiscrete R G

@[simp]
theorem coindFunctor_obj (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    (coindFunctor R G U).obj A = coindTopRep R G U A := by
  change (toSmoothDiscrete R G).obj
    ((coindDiscreteFunctor R G U).obj ((ofSmoothDiscrete R U).obj A)) = _
  rw [coindDiscreteFunctor_obj]

@[simp]
theorem coindFunctor_map_apply {A B : SmoothDiscreteTopRep.{u, v, w} R U}
    (f : A ⟶ B) (a : DiscreteCoind G U A.obj.V) (g : G) :
    (show DiscreteCoind G U B.obj.V from (coindFunctor R G U).map f a) g =
      f.hom.hom (a g) := by
  change (show DiscreteCoind G U B.obj.V from
    ((toSmoothDiscrete R G).map
      ((coindDiscreteFunctor R G U).map ((ofSmoothDiscrete R U).map f))).hom.hom a) g = _
  have htop := toSmoothDiscrete_map_hom_apply (R := R) (G := G)
    ((coindDiscreteFunctor R G U).map ((ofSmoothDiscrete R U).map f)) a
  have htop' := congrArg (fun b => (show DiscreteCoind G U B.obj.V from b) g) htop
  have h := coindDiscreteFunctor_map_apply R G U ((ofSmoothDiscrete R U).map f) a g
  have h' := h.trans
    (ofSmoothDiscrete_map_toLinearMap_apply (R := R) (G := U) f (a g))
  exact htop'.trans h'

end Bundled

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
