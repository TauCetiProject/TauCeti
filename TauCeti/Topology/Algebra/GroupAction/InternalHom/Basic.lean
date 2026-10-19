/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Hom
public import TauCeti.Algebra.Group.Hom.Instances
public import TauCeti.Algebra.Module.ZMod.Extend
public import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Conjugation actions on internal homs of discrete modules

Let a group `G` act on two additive monoids `M` and `N`. The additive homomorphisms
`M →+ N` carry the *conjugation* action

`homAction g φ : m ↦ g • φ (g⁻¹ • m)`,

which is the action for which evaluation `(φ, m) ↦ φ m` is equivariant, in the form
`homAction g φ (g • m) = g • φ m`. This file constructs that action and proves that it is again a
continuous action on a discrete module when `M` is finite discrete and `N` is discrete: the set of
group elements fixing a given `φ` is open, and over a compact `G` it contains an open normal
subgroup. The internal hom is contravariantly functorial in its source, by precomposition with an
equivariant homomorphism, and covariantly functorial in its target, by postcomposition; `Hom(-, N)`
is exact on the modules killed by a prime `p`, for every `N`: this is the algebra behind the dual
of a short exact sequence of finite `𝔽_p[G]`-modules.

## Main definitions

* `TauCeti.homAction`: the conjugation action of `G` on `M →+ N`, with the action laws
  `homAction_one` and `homAction_mul` and the additivity laws `homAction_zero`, `homAction_add`,
  `homAction_neg` and `homAction_sub`.
* `TauCeti.InternalHom`: the carrier `M →+ N` equipped with that action, as a `DistribMulAction`
  instance. Its `TauCeti.InternalHom.of` and `TauCeti.InternalHom.toAddMonoidHom` translate to and
  from `M →+ N`.
* `TauCeti.InternalHom.evalPairing`: the evaluation pairing, the additive homomorphism
  `InternalHom G M N →+ (M →+ N)` whose value at `φ` and `m` is the evaluation `φ m`; its
  equivariance is `TauCeti.InternalHom.evalPairing_equivariant`, and that of the opposite pairing
  `(m, φ) ↦ φ m` is `TauCeti.InternalHom.evalPairing_flip_equivariant`.
* `TauCeti.InternalHom.precomp`: precomposition with an equivariant homomorphism `f : M →+[G] M'`,
  the equivariant homomorphism `InternalHom G M' N →+[G] InternalHom G M N`, with
  `TauCeti.InternalHom.evalPairing_precomp` as its defining equation and the functor laws
  `precomp_id` and `precomp_comp`.
* `TauCeti.InternalHom.postcomp`: postcomposition with an equivariant homomorphism `f : N →+[G] N'`,
  the equivariant homomorphism `InternalHom G M N →+[G] InternalHom G M N'`, with
  `TauCeti.InternalHom.evalPairing_postcomp` as its defining equation and the functor laws
  `postcomp_id` and `postcomp_comp`.
* `TauCeti.InternalHom.restrict`: restriction of the acting group to a subgroup `U ≤ G`, the
  `U`-equivariant bijection `InternalHom G M N →+[U] InternalHom U M N` that leaves the underlying
  homomorphism unchanged.
* `TauCeti.InternalHom.zmodEquiv`: for a `ZMod n`-module `A`, evaluation at `1` identifies
  `InternalHom G (ZMod n) A` with `A` additively; `TauCeti.InternalHom.toAddMonoidHom_apply_eq_smul`
  recovers a homomorphism from its value at `1`. For a trivial action of `G` on `ZMod n`,
  evaluation at `1` is equivariant (`TauCeti.InternalHom.zmodEquiv_smul`); for trivial actions on
  both `M` and `N` the conjugation action on `InternalHom G M N` is trivial
  (`TauCeti.InternalHom.smul_eq_self_of_smul_eq_self`).

## Main results

* `TauCeti.homAction_apply_smul`: evaluation is equivariant; on the carrier this is
  `TauCeti.InternalHom.evalPairing_equivariant`.
* `TauCeti.homAction_eq_self_iff`: `g` fixes `φ` exactly when `φ` commutes with the action of `g`
  (`TauCeti.InternalHom.smul_eq_self_iff` on the carrier); so `φ` is fixed by all of `G` exactly
  when it is `G`-equivariant (`TauCeti.forall_homAction_eq_self_iff`, and
  `TauCeti.InternalHom.mem_fixedPoints_iff` on the carrier).
* `TauCeti.isOpen_setOfPred_homAction_eq_self`: for finite `M` and discrete `N` the set of group
  elements fixing a continuous `φ` is open. This is what the `ContinuousSMul G` instance on
  `TauCeti.InternalHom` rests on; with the discrete topology that carrier has by definition, it is
  what makes it again a discrete `G`-module for finite discrete `M` and discrete `N`.
* `TauCeti.exists_openNormalSubgroup_homAction_eq_self`: over a compact topological group that
  set contains an open normal subgroup.
* `TauCeti.InternalHom.precomp_injective`, `TauCeti.InternalHom.exact_precomp`,
  `TauCeti.InternalHom.precomp_surjective` and `TauCeti.InternalHom.precomp_surjective_of_baer`:
  `Hom(-, N)` takes a surjection to an injection, an exact pair with surjective second map to an
  exact pair, and an injection to a surjection when the target of the injection is killed by a
  prime `p`, or is killed by `n` with `N` satisfying Baer's criterion over `ℤ/nℤ`; both are cases of
  `TauCeti.InternalHom.precomp_surjective_of_forall_exists_comp_eq`, precomposition is surjective
  as soon as every additive homomorphism extends. The internal hom of finite modules is finite, and
  it is killed by any natural number killing the codomain (`TauCeti.InternalHom.nsmul_eq_zero`) or
  the domain (`TauCeti.InternalHom.nsmul_eq_zero_of_domain`).
* `TauCeti.InternalHom.postcomp_injective`, `TauCeti.InternalHom.postcomp_bijective` and
  `TauCeti.InternalHom.postcomp_bijective_of_forall_nsmul_eq_zero`: `Hom(M, -)` takes an injection
  to an injection and an isomorphism to an isomorphism, and, when `M` is killed by `n`, it takes an
  injection whose range is the `n`-torsion of its target to an isomorphism.

## Implementation notes

Mathlib already puts the codomain-pointwise action `(g • φ) m = g • φ m` on `M →+ N`, as the
instance in `Mathlib/Algebra/GroupWithZero/Action/Hom.lean`, and that action is not the conjugation
one, so the conjugation action cannot be registered on `M →+ N` itself: instance search would be
incoherent, and continuous cohomology of `M →+ N` would silently pick up the pointwise action.
The conjugation action is therefore introduced twice over. It is first the plain function
`homAction` of `g`, whose action and additivity laws are the lemmas listed above; this is the
form used by the lemmas about evaluation. It is
assembled from Mathlib's `DistribSMul.toAddMonoidHom`, which bundles each `g • ·` as an additive
homomorphism, so that its additivity comes from `AddMonoidHom.comp`. It is then registered as a
genuine `DistribMulAction` on the wrapper `InternalHom G M N`, which is the object downstream
cohomology is meant to be applied to. The two actions on `M →+ N` agree at any `g` acting trivially
on the source (`homAction_eq_smul_of_smul_eq_self`).

The group `G` is a phantom parameter of `InternalHom G M N`: the type of its single field does not
mention `G`, so it is formed for bare additive monoids, and `Group G` and the two
`DistribMulAction`s are hypotheses of the action instances only, as `AddCommMonoid N` is a
hypothesis of the additive ones. The additive structure is transported from `M →+ N` along the
`of`/`toAddMonoidHom` equivalence, as an `AddCommMonoid` in general and as an `AddCommGroup` when
`N` is one. That equivalence is written inline in the two instances rather than given a name, so
that the only bundled form of the carrier map in the public surface is `evalPairing`; the
transported structure is meant to be used only through the interface lemmas below
(`toAddMonoidHom_zero`, `toAddMonoidHom_add`, `toAddMonoidHom_nsmul`, `of_zero`, `of_add`,
`of_nsmul` and their group-level counterparts), which hold by `rfl` on the transported instance.

Two theorems are instead written `(rfl)` rather than `rfl`: `homAction_apply` and
`evalPairing_apply`. The module system rejects a bare `rfl` for an *exported* theorem whose proof
unfolds a definition that is not `@[expose]`d, and those two unfold `homAction` and `evalPairing`,
which nothing here needs to be exposed. The parenthesized form elaborates the same proof as an
ordinary term, without that check.

Continuity in the group variable (`continuous_homAction_apply`) needs only that `φ` itself be
continuous, the two actions occurring in `g • φ (g⁻¹ • m)` being continuous by hypothesis, and
`isOpen_setOfPred_homAction_eq_self` inherits that hypothesis; the discrete source of the intended
setting enters only where it is discharged, in the `ContinuousSMul` instance, by
`continuous_of_discreteTopology`.

`Representation.linHom` is the same conjugation construction for `k`-linear maps `V →ₗ[k] W` of
bundled representations. It is not used as the definition here for two reasons. Its carrier is
`V →ₗ[k] W`, a type distinct from the `M →+ N` used for additive cochains, so
routing through it would still need a bespoke definition round-tripping along
`AddMonoidHom.toIntLinearMap` and `LinearMap.toAddMonoidHom`; and taking `k = ℤ` forces
`Module ℤ M` and `Module ℤ N`, hence `AddCommGroup` on both sides, whereas everything below needs
only `AddMonoid M` and `AddMonoid N`. In the generality where `Representation.linHom` is available
the two constructions do agree, transported along `AddMonoidHom.toIntLinearMap`; that comparison is
not recorded here, because it would pull `Mathlib.RepresentationTheory.Basic` — and with it the
tensor, matrix and dual stack — into a file the whole continuous-cohomology development imports.

Mathlib puts no topology on `M →+ N`. Discreteness of the internal hom enters here through the
discreteness of the ambient function space `M → N`, which is what
`isOpen_setOfPred_homAction_eq_self` rests on. `InternalHom G M N` carries the discrete topology by
definition, with no hypothesis on `M` or `N`: that is the intended topology in the discrete setting
this file is written for, namely finite discrete `M` and discrete `N`, which is also the setting in
which the action is proved continuous below. Those hypotheses are sufficient for that continuity,
not necessary — if `G` acts trivially on both `M` and `N` then it acts trivially on `M →+ N`, so
the action is continuous for an infinite `M` too — and it is sufficiency that is established here.
(A trivial action on `M` alone does not suffice: the stabilizer of `φ` is then the intersection of
the stabilizers of the values `φ m`, which for infinitely many `m` need not be open.) For infinite
`M` the internal hom in the category of discrete `G`-modules is the sub-object of homomorphisms
with open stabilizer, which is not `InternalHom G M N`; nothing here claims otherwise.
-/

public section

namespace TauCeti

section Action

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N : Type*} [AddMonoid N] [DistribMulAction G N]

/-- The conjugation action of `G` on the internal hom `M →+ N`, sending `φ` to
`m ↦ g • φ (g⁻¹ • m)`. This is the action making evaluation equivariant; see
`homAction_apply_smul`. -/
def homAction (g : G) (φ : M →+ N) : M →+ N :=
  (DistribSMul.toAddMonoidHom N g).comp (φ.comp (DistribSMul.toAddMonoidHom M g⁻¹))

@[simp]
theorem homAction_apply (g : G) (φ : M →+ N) (m : M) : homAction g φ m = g • φ (g⁻¹ • m) := (rfl)

@[simp]
theorem homAction_one (φ : M →+ N) : homAction (1 : G) φ = φ := by
  ext m
  simp

@[simp]
theorem homAction_mul (g h : G) (φ : M →+ N) :
    homAction (g * h) φ = homAction g (homAction h φ) := by
  ext m
  simp [mul_smul, mul_inv_rev]

@[simp]
theorem homAction_zero (g : G) : homAction g (0 : M →+ N) = 0 := by
  ext m
  simp

section AddCommMonoid

variable {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- The conjugation action is additive in the homomorphism. Of the four laws only `homAction_zero`
holds for a bare additive-monoid codomain; this one and `homAction_neg` and `homAction_sub` all
name the pointwise structure on `M →+ N`, hence need a commutative codomain. -/
@[simp]
theorem homAction_add (g : G) (φ ψ : M →+ N) :
    homAction g (φ + ψ) = homAction g φ + homAction g ψ := by
  ext m
  simp

end AddCommMonoid

section AddCommGroup

variable {N : Type*} [AddCommGroup N] [DistribMulAction G N]

/-- The conjugation action commutes with negation for an additive commutative codomain group. -/
@[simp]
theorem homAction_neg (g : G) (φ : M →+ N) : homAction g (-φ) = -homAction g φ := by
  ext m
  simp

/-- The conjugation action commutes with subtraction for an additive commutative codomain group. -/
@[simp]
theorem homAction_sub (g : G) (φ ψ : M →+ N) :
    homAction g (φ - ψ) = homAction g φ - homAction g ψ := by
  ext m
  simp [smul_sub]

end AddCommGroup

/-- Evaluation `(φ, m) ↦ φ m` is equivariant for the conjugation action on `M →+ N`. This is the
equivariance that makes the duality cup pairings well typed, and it is what fixes the direction of
the conjugation action. -/
theorem homAction_apply_smul (g : G) (φ : M →+ N) (m : M) : homAction g φ (g • m) = g • φ m := by
  simp

/-- A group element fixes `φ` for the conjugation action exactly when `φ` commutes with its
action. It is deliberately not `@[simp]`: `homAction g φ = φ` is the shape in which the openness
and compact-group statements below are phrased, and rewriting it away would take them out of
simp-normal form. -/
theorem homAction_eq_self_iff {g : G} {φ : M →+ N} :
    homAction g φ = φ ↔ ∀ m : M, φ (g • m) = g • φ m := by
  constructor
  · intro h m
    have hm := homAction_apply_smul g φ m
    rwa [h] at hm
  · intro h
    ext m
    rw [homAction_apply, ← h, smul_inv_smul]

/-- The fixed points of the conjugation action are exactly the `G`-equivariant homomorphisms. -/
theorem forall_homAction_eq_self_iff {φ : M →+ N} :
    (∀ g : G, homAction g φ = φ) ↔ ∀ (g : G) (m : M), φ (g • m) = g • φ m :=
  forall_congr' fun _ => homAction_eq_self_iff

@[simp]
theorem homAction_id (g : G) : homAction g (AddMonoidHom.id N) = AddMonoidHom.id N :=
  homAction_eq_self_iff.mpr fun _ => rfl

/-- The conjugation action is functorial for composition of homomorphisms. -/
theorem homAction_comp {P : Type*} [AddMonoid P] [DistribMulAction G P] (g : G) (φ : M →+ N)
    (ψ : N →+ P) : homAction g (ψ.comp φ) = (homAction g ψ).comp (homAction g φ) := by
  ext m
  simp

/-- At a group element acting trivially on the source, the conjugation action on `M →+ N` is
Mathlib's codomain-pointwise action. -/
theorem homAction_eq_smul_of_smul_eq_self {g : G} (h : ∀ m : M, g • m = m) (φ : M →+ N) :
    homAction g φ = g • φ := by
  ext m
  simp [inv_smul_eq_iff.mpr (h m).symm]

end Action

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
  {M : Type*} [AddMonoid M] [TopologicalSpace M] [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type*} [AddMonoid N] [TopologicalSpace N] [DistribMulAction G N] [ContinuousSMul G N]

/-- Each value of the conjugation action is continuous in the group variable, as soon as `φ`
itself is continuous. -/
theorem continuous_homAction_apply {φ : M →+ N} (hφ : Continuous φ) (m : M) :
    Continuous fun g : G => homAction g φ m := by
  simp only [homAction_apply]
  exact continuous_id.smul (hφ.comp (continuous_inv.smul continuous_const))

/-- The conjugation action is continuous into the ambient function space `M → N`, as soon as `φ`
itself is continuous. -/
theorem continuous_homAction_coe {φ : M →+ N} (hφ : Continuous φ) :
    Continuous fun g : G => ((homAction g φ : M →+ N) : M → N) :=
  continuous_pi fun m => continuous_homAction_apply hφ m

/-- For a finite `M` and a discrete `N` the set of group elements fixing a continuous `φ` is open.
Discreteness enters through the ambient function space `M → N`; as for the two continuity lemmas
above, the source only has to be discrete where `Continuous φ` is discharged. This is what the
`ContinuousSMul G (InternalHom G M N)` instance below rests on, through
`continuousSMul_iff_stabilizer_isOpen`. -/
theorem isOpen_setOfPred_homAction_eq_self [Finite M] [DiscreteTopology N] {φ : M →+ N}
    (hφ : Continuous φ) : IsOpen {g : G | homAction g φ = φ} := by
  have hset : {g : G | homAction g φ = φ}
      = (fun g : G => ((homAction g φ : M →+ N) : M → N)) ⁻¹' {(φ : M → N)} := by
    ext g
    simp [DFunLike.coe_fn_eq]
  rw [hset]
  exact (continuous_homAction_coe hφ).isOpen_preimage _ (isOpen_discrete _)

end Topology

/-- The internal hom of two `G`-modules: the additive homomorphisms `M →+ N` carrying the
conjugation action `g • φ = homAction g φ`. It is a one-field wrapper around `M →+ N` rather than
`M →+ N` itself because Mathlib registers the codomain-pointwise action on the latter; this is the
type on which continuous cohomology of the internal hom is to be taken. The group `G` is a phantom
parameter, recording which action is meant. The type carries the discrete topology unconditionally,
and is the internal hom of *discrete* `G`-modules in the setting this file establishes: `M` finite
discrete and `N` discrete, which is sufficient for the action to be continuous. -/
@[ext]
structure InternalHom (G : Type*) (M : Type*) [AddMonoid M] (N : Type*) [AddMonoid N] where
  /-- Regard an additive homomorphism as an element of the internal hom. -/
  of (G) ::
  /-- Regard an element of the internal hom as an additive homomorphism, forgetting the action. -/
  toAddMonoidHom : M →+ N

namespace InternalHom

variable {G : Type*} {M : Type*} [AddMonoid M] {N : Type*} [AddMonoid N]

@[simp]
theorem of_toAddMonoidHom (φ : InternalHom G M N) : of G φ.toAddMonoidHom = φ := rfl

/-- The internal hom always carries the discrete topology, by definition; see the implementation
notes for when that is the intended topology. -/
instance : TopologicalSpace (InternalHom G M N) := ⊥

instance : DiscreteTopology (InternalHom G M N) := ⟨rfl⟩

/-- The internal hom of two finite modules is finite: an additive homomorphism is determined by its
underlying function. -/
instance [Finite M] [Finite N] : Finite (InternalHom G M N) :=
  Finite.of_injective (fun φ : InternalHom G M N => (φ.toAddMonoidHom : M → N))
    fun _ _ h => InternalHom.ext (DFunLike.coe_injective h)

/-- The internal hom out of a subsingleton module is a subsingleton: a homomorphism out of the zero
module is zero. -/
instance [Subsingleton M] : Subsingleton (InternalHom G M N) :=
  ⟨fun φ ψ => InternalHom.ext (AddMonoidHom.ext fun m => by
    rw [Subsingleton.elim m 0, map_zero, map_zero])⟩

section Additive

variable (G) {N : Type*} [AddCommMonoid N]

instance : AddCommMonoid (InternalHom G M N) :=
  fast_instance% (⟨toAddMonoidHom, of G, fun _ => rfl, fun _ => rfl⟩ :
    InternalHom G M N ≃ (M →+ N)).addCommMonoid

/-- The evaluation pairing out of the internal hom: the additive homomorphism that
forgets the action, so that `evalPairing G φ m` is the evaluation `φ m`. Its equivariance is
`evalPairing_equivariant`. -/
def evalPairing : InternalHom G M N →+ (M →+ N) where
  toFun := toAddMonoidHom
  map_zero' := rfl
  map_add' _ _ := rfl

variable {G}

@[simp]
theorem evalPairing_apply (φ : InternalHom G M N) : evalPairing G φ = φ.toAddMonoidHom := (rfl)

@[simp]
theorem toAddMonoidHom_zero : (0 : InternalHom G M N).toAddMonoidHom = 0 := rfl

@[simp]
theorem toAddMonoidHom_add (φ ψ : InternalHom G M N) :
    (φ + ψ).toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom := rfl

@[simp]
theorem of_zero : of G (0 : M →+ N) = 0 := rfl

@[simp]
theorem of_add (φ ψ : M →+ N) : of G (φ + ψ) = of G φ + of G ψ := rfl

@[simp]
theorem toAddMonoidHom_nsmul (n : ℕ) (φ : InternalHom G M N) :
    (n • φ).toAddMonoidHom = n • φ.toAddMonoidHom := rfl

@[simp]
theorem of_nsmul (n : ℕ) (φ : M →+ N) : of G (n • φ) = n • of G φ := rfl

/-- A natural number killing the codomain kills the internal hom. -/
theorem nsmul_eq_zero {n : ℕ} (hN : ∀ x : N, n • x = 0) (φ : InternalHom G M N) : n • φ = 0 := by
  ext m
  simp [hN]

/-- A natural number killing the domain kills the internal hom. -/
theorem nsmul_eq_zero_of_domain {n : ℕ} (hM : ∀ x : M, n • x = 0) (φ : InternalHom G M N) :
    n • φ = 0 := by
  ext m
  simp [← map_nsmul, hM]

end Additive

section AddCommGroup

variable {N : Type*} [AddCommGroup N]

/-- For a codomain that is an additive commutative group, so is the internal hom; together with the
discrete topology below this supplies coefficients for continuous cohomology. -/
instance : AddCommGroup (InternalHom G M N) :=
  fast_instance% (⟨toAddMonoidHom, of G, fun _ => rfl, fun _ => rfl⟩ :
    InternalHom G M N ≃ (M →+ N)).addCommGroup

@[simp]
theorem toAddMonoidHom_neg (φ : InternalHom G M N) :
    (-φ).toAddMonoidHom = -φ.toAddMonoidHom := rfl

@[simp]
theorem toAddMonoidHom_sub (φ ψ : InternalHom G M N) :
    (φ - ψ).toAddMonoidHom = φ.toAddMonoidHom - ψ.toAddMonoidHom := rfl

@[simp]
theorem of_neg (φ : M →+ N) : of G (-φ) = -of G φ := rfl

@[simp]
theorem of_sub (φ ψ : M →+ N) : of G (φ - ψ) = of G φ - of G ψ := rfl

@[simp]
theorem toAddMonoidHom_zsmul (z : ℤ) (φ : InternalHom G M N) :
    (z • φ).toAddMonoidHom = z • φ.toAddMonoidHom := rfl

@[simp]
theorem of_zsmul (z : ℤ) (φ : M →+ N) : of G (z • φ) = z • of G φ := rfl

end AddCommGroup

section Action

variable [Group G] [DistribMulAction G M] [DistribMulAction G N]

/-- The conjugation action of `G` on the internal hom. -/
instance : SMul G (InternalHom G M N) where
  smul g φ := of G (homAction g φ.toAddMonoidHom)

@[simp]
theorem toAddMonoidHom_smul (g : G) (φ : InternalHom G M N) :
    (g • φ).toAddMonoidHom = homAction g φ.toAddMonoidHom := rfl

@[simp]
theorem smul_of (g : G) (φ : M →+ N) : g • of G φ = of G (homAction g φ) := rfl

instance : MulAction G (InternalHom G M N) where
  one_smul φ := by ext m; simp
  mul_smul g h φ := by ext m; simp [homAction_mul]

/-- A single group element fixes an element of the internal hom exactly when the underlying
homomorphism commutes with its action; this is `homAction_eq_self_iff` on the carrier, and the form
in which a stabilizer membership or an `exists_openNormalSubgroup_smul_eq_self` hypothesis is
consumed. Like `homAction_eq_self_iff` it is deliberately not `@[simp]`, since `g • φ = φ` is the
shape in which those statements are phrased. -/
theorem smul_eq_self_iff {g : G} {φ : InternalHom G M N} :
    g • φ = φ ↔ ∀ m : M, φ.toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m := by
  rw [InternalHom.ext_iff, toAddMonoidHom_smul, homAction_eq_self_iff]

/-- For trivial actions on `M` and `N`, the conjugation action on `InternalHom G M N` is
trivial. -/
theorem smul_eq_self_of_smul_eq_self (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (x : N), g • x = x) (g : G) (φ : InternalHom G M N) : g • φ = φ :=
  smul_eq_self_iff.2 fun m => by rw [hM, hN]

/-- The fixed points of the internal hom are the `G`-equivariant homomorphisms. This is the
degree-zero invariants of the conjugation action, phrased through Mathlib's
`MulAction.fixedPoints`, which is the invariants object the surrounding development uses. It is
deliberately not `@[simp]`: Mathlib's `MulAction.mem_fixedPoints` already rewrites the left-hand
side, so a `simp` attribute here would be shadowed and the `simpNF` linter rejects it. -/
theorem mem_fixedPoints_iff {φ : InternalHom G M N} :
    φ ∈ MulAction.fixedPoints G (InternalHom G M N) ↔
      ∀ (g : G) (m : M), φ.toAddMonoidHom (g • m) = g • φ.toAddMonoidHom m := by
  simp only [MulAction.mem_fixedPoints]
  exact forall_congr' fun _ => smul_eq_self_iff

/-- For a finite discrete `M` and a discrete `N` over a topological group, the conjugation action
on the internal hom is continuous: this is the statement that `InternalHom G M N` is again a
discrete `G`-module. -/
instance [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] [Finite M] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul G N] : ContinuousSMul G (InternalHom G M N) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun φ => ?_
  have hset : (MulAction.stabilizer G φ : Set G)
      = {g : G | homAction g φ.toAddMonoidHom = φ.toAddMonoidHom} := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_ofPred_eq,
      smul_eq_self_iff, homAction_eq_self_iff]
  rw [hset]
  exact isOpen_setOfPred_homAction_eq_self continuous_of_discreteTopology

section Distrib

variable {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

instance : DistribMulAction G (InternalHom G M N) :=
  { (inferInstance : MulAction G (InternalHom G M N)) with
    smul_zero := fun _ => by ext m; simp
    smul_add := fun _ _ _ => by ext m; simp }

/-- The evaluation pairing is `G`-equivariant: this is the carrier form of
`homAction_apply_smul`. -/
theorem evalPairing_equivariant (g : G) (φ : InternalHom G M N) (m : M) :
    evalPairing G (g • φ) (g • m) = g • evalPairing G φ m := by
  simp only [evalPairing_apply, toAddMonoidHom_smul]
  exact homAction_apply_smul g _ m

/-- The opposite evaluation pairing `(m, φ) ↦ φ m` is `G`-equivariant: `evalPairing_equivariant`
with its two arguments swapped, in the form a cup product along the opposite pairing takes. -/
theorem evalPairing_flip_equivariant (g : G) (m : M) (φ : InternalHom G M N) :
    (evalPairing G).flip (g • m) (g • φ) = g • (evalPairing G).flip m φ :=
  evalPairing_equivariant g φ m

end Distrib

end Action

end InternalHom

namespace InternalHom

/-! ### Contravariant functoriality in the source -/

section Precomp

variable (G : Type*) [Group G] {M M' : Type*} [AddMonoid M] [AddMonoid M'] [DistribMulAction G M]
  [DistribMulAction G M'] {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- Precomposition with an equivariant homomorphism `f : M →+[G] M'`, as an equivariant homomorphism
`InternalHom G M' N →+[G] InternalHom G M N`: the internal hom is contravariantly functorial in its
source. Its values are characterized by `evalPairing_precomp`. -/
def precomp (f : M →+[G] M') : InternalHom G M' N →+[G] InternalHom G M N where
  toFun φ := of G (φ.toAddMonoidHom.comp (f : M →+ M'))
  map_smul' g φ := by
    ext m
    simp [homAction_apply, map_smul]
  map_zero' := rfl
  map_add' _ _ := rfl

variable {G}

@[simp]
theorem toAddMonoidHom_precomp (f : M →+[G] M') (φ : InternalHom G M' N) :
    (precomp G f φ).toAddMonoidHom = φ.toAddMonoidHom.comp (f : M →+ M') := (rfl)

/-- Precomposition is compatible with evaluation: `(φ ∘ f) m = φ (f m)`. Not a `simp` lemma, since
`evalPairing_apply` already rewrites its left-hand side to `toAddMonoidHom_precomp`. -/
theorem evalPairing_precomp (f : M →+[G] M') (φ : InternalHom G M' N) (m : M) :
    evalPairing G (precomp G f φ) m = evalPairing G φ (f m) := (rfl)

@[simp]
theorem precomp_id : precomp G (DistribMulActionHom.id G : M →+[G] M) (N := N) =
    DistribMulActionHom.id G :=
  DistribMulActionHom.ext fun _ => InternalHom.ext (AddMonoidHom.ext fun _ => rfl)

theorem precomp_comp {M'' : Type*} [AddMonoid M''] [DistribMulAction G M''] (g : M' →+[G] M'')
    (f : M →+[G] M') : precomp G (g.comp f) (N := N) = (precomp G f).comp (precomp G g) :=
  DistribMulActionHom.ext fun _ => InternalHom.ext (AddMonoidHom.ext fun _ => rfl)

/-- Precomposition with a surjection is injective: `Hom(-, N)` takes surjections to injections. -/
theorem precomp_injective {f : M →+[G] M'} (hf : Function.Surjective f) :
    Function.Injective (precomp G f (N := N)) := by
  intro φ ψ h
  ext m'
  obtain ⟨m, rfl⟩ := hf m'
  exact congrArg (fun χ : InternalHom G M N => evalPairing G χ m) h

/-- Precomposition with `f` is surjective on internal homs as soon as every additive homomorphism
`M →+ N` is the restriction along `f` of an additive homomorphism `M' →+ N`: the extension, with
the conjugation action, is a preimage in the internal hom. -/
theorem precomp_surjective_of_forall_exists_comp_eq {f : M →+[G] M'}
    (h : ∀ φ : M →+ N, ∃ ψ : M' →+ N, ψ.comp f = φ) :
    Function.Surjective (precomp G f (N := N)) := fun φ =>
  let ⟨ψ, hψ⟩ := h φ.toAddMonoidHom
  ⟨of G ψ, InternalHom.ext hψ⟩

/-- Precomposition with a bijection is bijective: `Hom(-, N)` takes isomorphisms to isomorphisms.
The inverse is precomposition with the inverse bijection. -/
theorem precomp_bijective {f : M →+[G] M'} (hf : Function.Bijective f) :
    Function.Bijective (precomp G f (N := N)) :=
  ⟨precomp_injective hf.2, precomp_surjective_of_forall_exists_comp_eq
    (AddMonoidHom.compHom'_bijective (f := (f : M →+ M')) hf).2⟩

end Precomp

/-! ### Covariant functoriality in the target -/

section Postcomp

variable (G : Type*) [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N'] [DistribMulAction G N]
  [DistribMulAction G N']

/-- Postcomposition with an equivariant homomorphism `f : N →+[G] N'`, as an equivariant
homomorphism `InternalHom G M N →+[G] InternalHom G M N'`: the internal hom is covariantly
functorial in its target. Its values are characterized by `evalPairing_postcomp`. -/
def postcomp (f : N →+[G] N') : InternalHom G M N →+[G] InternalHom G M N' where
  toFun φ := of G ((f : N →+ N').comp φ.toAddMonoidHom)
  map_smul' g φ := by
    ext m
    simp [homAction_apply, map_smul]
  map_zero' := by
    ext m
    simp
  map_add' _ _ := by
    ext m
    simp

variable {G}

@[simp]
theorem toAddMonoidHom_postcomp (f : N →+[G] N') (φ : InternalHom G M N) :
    (postcomp G f φ).toAddMonoidHom = (f : N →+ N').comp φ.toAddMonoidHom := (rfl)

/-- Postcomposition is compatible with evaluation: `(f ∘ φ) m = f (φ m)`. Not a `simp` lemma, since
`evalPairing_apply` already rewrites its left-hand side to `toAddMonoidHom_postcomp`. -/
theorem evalPairing_postcomp (f : N →+[G] N') (φ : InternalHom G M N) (m : M) :
    evalPairing G (postcomp G f φ) m = f (evalPairing G φ m) := (rfl)

@[simp]
theorem postcomp_id : postcomp G (DistribMulActionHom.id G : N →+[G] N) (M := M) =
    DistribMulActionHom.id G :=
  DistribMulActionHom.ext fun _ => InternalHom.ext (AddMonoidHom.ext fun _ => rfl)

theorem postcomp_comp {N'' : Type*} [AddCommMonoid N''] [DistribMulAction G N''] (g : N' →+[G] N'')
    (f : N →+[G] N') : postcomp G (g.comp f) (M := M) = (postcomp G g).comp (postcomp G f) :=
  DistribMulActionHom.ext fun _ => InternalHom.ext (AddMonoidHom.ext fun _ => rfl)

/-- Postcomposition with an injection is injective: `Hom(M, -)` takes injections to injections. -/
theorem postcomp_injective {f : N →+[G] N'} (hf : Function.Injective f) :
    Function.Injective (postcomp G f (M := M)) := fun _ _ h =>
  InternalHom.ext (AddMonoidHom.ext fun m => hf (congrArg (fun χ : InternalHom G M N' =>
    evalPairing G χ m) h))

/-- **Postcomposition with an injection onto the `n`-torsion is bijective** on the internal homs out
of a module killed by `n`: if `f : N →+[G] N'` is injective and every element of `N'` killed by `n`
lies in its range, then `Hom(M, f)` is bijective for every `M` killed by `n`, because every
homomorphism out of `M` takes values in the `n`-torsion. -/
theorem postcomp_bijective_of_forall_nsmul_eq_zero {f : N →+[G] N'} (hf : Function.Injective f)
    {n : ℕ} (hM : ∀ x : M, n • x = 0) (hN' : ∀ y : N', n • y = 0 → ∃ x, f x = y) :
    Function.Bijective (postcomp G f (M := M)) := by
  have h := AddMonoidHom.compHom_bijective_of_forall_nsmul_eq_zero (M := M) (f := (f : N →+ N'))
    hf hM hN'
  refine ⟨fun φ ψ hφψ => InternalHom.ext (h.1 ?_), fun ψ => ?_⟩
  · simpa only [AddMonoidHom.compHom_apply_apply, toAddMonoidHom_postcomp] using
      congrArg toAddMonoidHom hφψ
  · obtain ⟨φ, hφ⟩ := h.2 ψ.toAddMonoidHom
    exact ⟨of G φ, InternalHom.ext (by
      simpa only [AddMonoidHom.compHom_apply_apply, toAddMonoidHom_postcomp] using hφ)⟩

/-- Postcomposition with a bijection is bijective: `Hom(M, -)` takes isomorphisms to isomorphisms.
This is the case `n = 0` of `postcomp_bijective_of_forall_nsmul_eq_zero`. -/
theorem postcomp_bijective {f : N →+[G] N'} (hf : Function.Bijective f) :
    Function.Bijective (postcomp G f (M := M)) :=
  postcomp_bijective_of_forall_nsmul_eq_zero hf.1 (n := 0) (fun x => zero_nsmul x)
    fun y _ => hf.2 y

end Postcomp

/-! ### Restricting the acting group -/

section Restrict

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
  {N : Type*} [AddCommMonoid N] [DistribMulAction G N]

/-- Restricting the acting group to a subgroup `U ≤ G`: the internal hom of `M` and `N` as
`G`-modules, regarded as a `U`-module through the restricted action, is the internal hom of `M` and
`N` as `U`-modules. The underlying homomorphism does not move (`toAddMonoidHom_restrict`), the
evaluation pairing is unchanged (`evalPairing_restrict`) and the map is a bijection
(`restrict_bijective`). It is recorded as a `U`-equivariant homomorphism because that is the form in
which the coefficient maps of continuous cohomology consume it. -/
def restrict (U : Subgroup G) : InternalHom G M N →+[U] InternalHom U M N where
  toFun φ := of U φ.toAddMonoidHom
  map_smul' _ _ := InternalHom.ext (AddMonoidHom.ext fun _ => rfl)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem toAddMonoidHom_restrict (U : Subgroup G) (φ : InternalHom G M N) :
    (restrict U φ).toAddMonoidHom = φ.toAddMonoidHom := (rfl)

/-- Restricting the acting group does not change the evaluation pairing. -/
theorem evalPairing_restrict (U : Subgroup G) (φ : InternalHom G M N) (m : M) :
    evalPairing U (restrict U φ) m = evalPairing G φ m := (rfl)

theorem restrict_bijective (U : Subgroup G) :
    Function.Bijective (restrict U : InternalHom G M N → InternalHom U M N) :=
  ⟨fun _ _ h => InternalHom.ext (by simpa using congrArg toAddMonoidHom h),
    fun ψ => ⟨of G ψ.toAddMonoidHom, (rfl)⟩⟩

end Restrict

section Exact

variable {G : Type*} [Group G] {M M' M'' : Type*} [AddMonoid M] [AddGroup M']
  [AddGroup M''] [DistribMulAction G M] [DistribMulAction G M'] [DistribMulAction G M'']
  {N : Type*} [AddCommGroup N] [DistribMulAction G N]

/-- Precomposition along an exact pair `f : M →+[G] M'`, `g : M' →+[G] M''` with `g` surjective is
exact: a homomorphism on `M'` killing the image of `f` factors through `g`. The groups
`M'` and `M''` need not be commutative. -/
theorem exact_precomp (f : M →+[G] M') (g : M' →+[G] M'') (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Function.Exact (precomp G g (N := N)) (precomp G f) := by
  intro ψ
  constructor
  · intro hψ
    have hker : (g : M' →+ M'').ker ≤ ψ.toAddMonoidHom.ker := by
      intro x hx
      rw [AddMonoidHom.mem_ker] at hx ⊢
      obtain ⟨m, rfl⟩ := (hfg x).mp hx
      exact congrArg (fun χ : InternalHom G M N => evalPairing G χ m) hψ
    refine ⟨of G ((g : M' →+ M'').liftOfSurjective hg ⟨ψ.toAddMonoidHom, hker⟩), ?_⟩
    ext x
    exact (g : M' →+ M'').liftOfRightInverse_comp_apply (Function.surjInv hg)
      (Function.rightInverse_surjInv hg) ⟨ψ.toAddMonoidHom, hker⟩ x
  · rintro ⟨χ, rfl⟩
    ext m
    simp [hfg.apply_apply_eq_zero]

end Exact

section Surjective

variable {G : Type*} [Group G] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
  [DistribMulAction G M] [DistribMulAction G M'] {N : Type*} [AddCommMonoid N]
  [DistribMulAction G N]

/-- Precomposition with an injection into a module killed by a prime `p` is surjective, for any
`N`: `Hom(-, N)` is exact on the modules killed by `p`. This is
`AddMonoidHom.exists_comp_eq_of_injective` on the internal hom. -/
theorem precomp_surjective {p : ℕ} [Fact p.Prime] (hM' : ∀ x : M', p • x = 0)
    {f : M →+[G] M'} (hf : Function.Injective f) :
    Function.Surjective (precomp G f (N := N)) :=
  precomp_surjective_of_forall_exists_comp_eq fun φ =>
    AddMonoidHom.exists_comp_eq_of_injective hM' (f := (f : M →+ M')) hf φ

end Surjective

section SurjectiveOfBaer

variable {G : Type*} [Group G] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
  [DistribMulAction G M] [DistribMulAction G M'] {N : Type*} [AddCommGroup N]
  [DistribMulAction G N]

/-- Precomposition with an injection into a module killed by `n` is surjective when the target `N`
satisfies Baer's criterion over `ℤ/nℤ`: for such `N`, `Hom(-, N)` is exact on the modules killed by
`n`. This holds for `N = ℤ/nℤ` with any action when `n ≠ 0`, by `Module.Baer.zmod_self`, and is
`AddMonoidHom.exists_comp_eq_of_injective_of_baer` on the internal hom. -/
theorem precomp_surjective_of_baer {n : ℕ} [Module (ZMod n) N] (hN : Module.Baer (ZMod n) N)
    (hM' : ∀ x : M', n • x = 0) {f : M →+[G] M'} (hf : Function.Injective f) :
    Function.Surjective (precomp G f (N := N)) :=
  precomp_surjective_of_forall_exists_comp_eq fun φ =>
    AddMonoidHom.exists_comp_eq_of_injective_of_baer hN hM' (f := (f : M →+ M')) hf φ

end SurjectiveOfBaer

end InternalHom

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {M : Type*} [AddMonoid M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Finite M]
  {N : Type*} [AddMonoid N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [ContinuousSMul G N]

/-- Over a compact topological group, a homomorphism from a finite discrete module to a discrete
module is fixed by an open normal subgroup. This is the form used by the finite-quotient system for
continuous cohomology. It is `exists_openNormalSubgroup_smul_eq_self` for the discrete `G`-module
`InternalHom G M N`, read back on `M →+ N`. -/
theorem exists_openNormalSubgroup_homAction_eq_self (φ : M →+ N) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, homAction u φ = φ := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) (InternalHom.of G φ)
  exact ⟨U, fun u hu => homAction_eq_self_iff.mpr (InternalHom.smul_eq_self_iff.mp (hU u hu))⟩

end Compact

namespace InternalHom

/-! ### Homomorphisms out of `ZMod n`

An additive homomorphism out of `ZMod n` is determined by its value at `1`, so the internal hom
`InternalHom G (ZMod n) A` is additively `A` itself whenever `A` is a `ZMod n`-module. The action of
`G` plays no part in this identification. -/

section ZMod

variable (G : Type*) {n : ℕ} {A : Type*} [AddCommGroup A] [Module (ZMod n) A]

/-- A homomorphism out of `ZMod n` into a `ZMod n`-module is scalar multiplication by its value at
`1`: it is `ZMod n`-linear, and `x = x • 1`. -/
theorem toAddMonoidHom_apply_eq_smul (φ : InternalHom G (ZMod n) A) (x : ZMod n) :
    φ.toAddMonoidHom x = x • φ.toAddMonoidHom 1 := by
  rw [← ZMod.map_smul φ.toAddMonoidHom x 1, smul_eq_mul, mul_one]

/-- **Homomorphisms out of `ZMod n` are elements.** For a `ZMod n`-module `A`, evaluation at `1`
identifies the internal hom `InternalHom G (ZMod n) A` with `A`, additively; the inverse sends
`a` to `x ↦ x • a`. -/
def zmodEquiv : InternalHom G (ZMod n) A ≃+ A where
  toFun φ := φ.toAddMonoidHom 1
  invFun a := of G
    { toFun x := x • a
      map_zero' := zero_smul (ZMod n) a
      map_add' x y := add_smul x y a }
  left_inv φ :=
    InternalHom.ext (AddMonoidHom.ext fun x => (toAddMonoidHom_apply_eq_smul G φ x).symm)
  right_inv a := one_smul (ZMod n) a
  map_add' _ _ := rfl

@[simp]
theorem zmodEquiv_apply (φ : InternalHom G (ZMod n) A) :
    zmodEquiv G φ = φ.toAddMonoidHom 1 :=
  (rfl)

@[simp]
theorem zmodEquiv_symm_apply (a : A) (x : ZMod n) :
    ((zmodEquiv G).symm a).toAddMonoidHom x = x • a :=
  (rfl)

section TrivialAction

variable {G} [Group G] [DistribMulAction G (ZMod n)] [DistribMulAction G A]
  (htriv : ∀ (g : G) (m : ZMod n), g • m = m)

include htriv

/-- For a trivial action on the source `ZMod n`, evaluation at `1` is `G`-equivariant for the
conjugation action on `InternalHom G (ZMod n) A` and any action on `A`: `(g • φ) 1 = g • φ 1`,
since `g⁻¹ • 1 = 1`. -/
theorem zmodEquiv_smul (g : G) (φ : InternalHom G (ZMod n) A) :
    zmodEquiv G (g • φ) = g • zmodEquiv G φ := by
  rw [zmodEquiv_apply, zmodEquiv_apply, toAddMonoidHom_smul, homAction_apply, htriv]

end TrivialAction

end ZMod

end InternalHom

end TauCeti
