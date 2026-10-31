/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod

import TauCeti.Data.Rat.NumDenDvd
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow

/-!
# The prime-to-`p` Tate module of the roots of unity

For a commutative monoid `E` and a natural number `p`, the **prime-to-`p` Tate module**

`PrimeToPTateModule p E = lim_{m ≠ 0, (m, p) = 1} μ_m(E)`

is the inverse limit of the groups `μ_m(E) = rootsOfUnity m E` over the nonzero `m` prime to `p`,
ordered by divisibility, along the power maps `μ_m(E) → μ_n(E)`, `ζ ↦ ζ ^ (m / n)` for `n ∣ m`.
Concretely, a point is a family `(ζ_m)_m` of roots of unity with `ζ_m ^ (m / n) = ζ_n` whenever
`n ∣ m`. It carries the inverse-limit topology, induced from the product of the discrete groups
`μ_m(E)`, and is a topological group; for a domain `E` the levels are finite, so it is compact.

When `E` is a separably closed field of exponential characteristic `p`, this is the group written
`ℤ̂^{(p')}(1)`: as a profinite group it is `∏_{ℓ ≠ p} ℤ_ℓ`, while the twist `(1)` records the action
of automorphisms of `E` on it. For a local field `K` with residue characteristic `p`, the inertia
group of `K` maps to it through the tame character.

For `p = 1` and a domain containing a compatible family `ζ` of primitive roots of unity of every
order, the profinite power map `a ↦ ζ ^ a` identifies the Tate module with the profinite integers
`ℤ̂`.

## Main definitions

* `TauCeti.primeToPTateModuleSubgroup p E`: the subgroup of compatible families in the product
  `∏_m μ_m(E)`.
* `TauCeti.PrimeToPTateModule p E`: the prime-to-`p` Tate module, a commutative topological group.
* `TauCeti.PrimeToPTateModule.proj m`: the projection to the level `μ_m(E)`.
* `TauCeti.PrimeToPTateModule.mk`: the point with prescribed compatible components.
* `TauCeti.PrimeToPTateModule.lift`: the homomorphism into the Tate module determined by a
  compatible family of homomorphisms into the levels.
* `TauCeti.PrimeToPTateModule.map`: the homomorphism of Tate modules induced by a monoid
  homomorphism `E →* F`.
* The instance `MulDistribMulAction M (PrimeToPTateModule p E)` for a monoid `M` acting on `E` by
  multiplicative maps, componentwise; for the Galois group of `E` it is the twist `(1)`.
* `TauCeti.PrimeToPTateModule.ratChar E`: for `p = 1`, where the levels are all the `μ_n(E)`, the
  character `ℚ → Eˣ`, `k / n ↦ ζ_n ^ k`, attached to a point `(ζ_n)_n`. Twisting rational
  exponents by it gives the Galois action on Puiseux series.
* `TauCeti.PrimeToPTateModule.continuousMulEquivZHat ζ hζ`: for `p = 1` and a domain `R`, the
  isomorphism of topological groups `lim_n μ_n(R) ≃ₜ* ℤ̂` attached to a point `ζ = (ζ_n)_n` whose
  components are all primitive, inverse to `zHat.lift ζ`.

## Main results

* `TauCeti.PrimeToPTateModule.proj_pow_div`: the components of a point are compatible.
* `TauCeti.PrimeToPTateModule.ext`: a point is determined by its components.
* `TauCeti.PrimeToPTateModule.lift_unique`: `lift` is the unique homomorphism with the prescribed
  components.
* `TauCeti.PrimeToPTateModule.continuous_iff`: a map into the Tate module is continuous exactly
  when each of its components is locally constant.
* `TauCeti.PrimeToPTateModule.surjective_of_forall_surjective_proj`: a continuous map from a
  compact space is surjective when each of its components is.
* `TauCeti.PrimeToPTateModule.exists_forall_isPrimitiveRoot_proj`: such a map, surjective at each
  level, takes a value whose components are all primitive roots of unity.
* `TauCeti.PrimeToPTateModule.topologicalClosure_zpowers_eq_top`: over a domain, a point whose
  components are all primitive roots of unity topologically generates the Tate module.
* `TauCeti.PrimeToPTateModule.exists_forall_isPrimitiveRoot`: a domain with primitive roots of
  unity of every order prime to `p` has a compatible system of them, that is, a point of the Tate
  module whose components are all primitive.
* `TauCeti.PrimeToPTateModule.proj_surjective`: over such a domain, every root of unity of order
  prime to `p` is the component of a point of the Tate module.
* `TauCeti.PrimeToPTateModule.proj_map`, `TauCeti.PrimeToPTateModule.coe_proj_smul`: `map` and
  the action are computed componentwise.
* `TauCeti.PrimeToPTateModule.ratChar_ofAdd_eq_zpow`: the character of `(ζ_n)_n` sends `q` to
  `ζ_n ^ k` whenever `q = k / n`; it is trivial on `ℤ` and determines the point
  (`TauCeti.PrimeToPTateModule.ratChar_injective`).
* `TauCeti.PrimeToPTateModule.ratChar_ofAdd_eq_one_iff`: if every `ζ_n` is primitive, the
  character vanishes exactly on `ℤ`.
* `TauCeti.PrimeToPTateModule.coe_proj_zHatLift`: the level-`n` component of `zHat.lift ζ a` is
  `ζ_n` raised to the residue of `a` modulo `n`.
* `TauCeti.PrimeToPTateModule.hasEnoughRootsOfUnity_of_isPrimitiveRoot_proj`: a point whose
  components are all primitive supplies all `n`-th roots of unity, for every `n ≠ 0`.
* `TauCeti.PrimeToPTateModule.zHatLift_injective`, `TauCeti.PrimeToPTateModule.zHatLift_surjective`:
  if every component of `ζ` is primitive, `zHat.lift ζ : ℤ̂ → lim_n μ_n(R)` is bijective.
* The instances `IsTopologicalGroup`, `T2Space`, `TotallyDisconnectedSpace`,
  `ContinuousConstSMul`, and, for a domain, `CompactSpace`.
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) (E : Type*) [CommMonoid E]

/-- The subgroup of the product `∏_m μ_m(E)`, over the nonzero `m` prime to `p`, consisting of the
families `(ζ_m)_m` compatible along the power maps: `ζ_m ^ (m / n) = ζ_n` whenever `n ∣ m`. Its
carrier is the prime-to-`p` Tate module `PrimeToPTateModule p E`. -/
def primeToPTateModuleSubgroup :
    Subgroup (∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m E) where
  carrier := {x | ∀ m n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, (n : ℕ) ∣ m →
    (x m : Eˣ) ^ ((m : ℕ) / n) = x n}
  one_mem' _ _ _ := by simp
  mul_mem' {x y} hx hy m n h := by simp [mul_pow, hx m n h, hy m n h]
  inv_mem' {x} hx m n h := by simp [inv_pow, hx m n h]

variable {p E} in
/-- A family of roots of unity lies in the Tate-module subgroup exactly when it is compatible along
the power maps. -/
theorem mem_primeToPTateModuleSubgroup_iff
    {x : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m E} :
    x ∈ primeToPTateModuleSubgroup p E ↔
      ∀ m n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, (n : ℕ) ∣ m → (x m : Eˣ) ^ ((m : ℕ) / n) = x n :=
  Iff.rfl

/-- The **prime-to-`p` Tate module** `lim_{m ≠ 0, (m, p) = 1} μ_m(E)` of the roots of unity of
`E`: the compatible families of roots of unity of order prime to `p`, along the power maps
`ζ ↦ ζ ^ (m / n)`. For a separably closed field of exponential characteristic `p` it is the group
`ℤ̂^{(p')}(1)`. It carries the inverse-limit topology. -/
def PrimeToPTateModule : Type _ :=
  primeToPTateModuleSubgroup p E

namespace PrimeToPTateModule

instance : CommGroup (PrimeToPTateModule p E) :=
  inferInstanceAs (CommGroup (primeToPTateModuleSubgroup p E))

variable {p E}

/-- The projection of the prime-to-`p` Tate module to its level `μ_m(E)`. -/
def proj (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : PrimeToPTateModule p E →* rootsOfUnity m E :=
  (Pi.evalMonoidHom (fun m : {m : ℕ // m ≠ 0 ∧ m.Coprime p} ↦ rootsOfUnity m E) m).comp
    (primeToPTateModuleSubgroup p E).subtype

/-- The components of a point of the Tate module are compatible along the power maps. -/
theorem proj_pow_div (x : PrimeToPTateModule p E) {m n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}}
    (h : (n : ℕ) ∣ m) : (proj m x : Eˣ) ^ ((m : ℕ) / n) = proj n x :=
  -- `PrimeToPTateModule p E` is by definition the subgroup of compatible families, so the
  -- compatibility of `x` is its membership proof there. This is the only place the synonym is
  -- unfolded for membership; later results go through this lemma and `ext` instead.
  mem_primeToPTateModuleSubgroup_iff.1 (show ↥(primeToPTateModuleSubgroup p E) from x).2 m n h

/-- A point of the Tate module is determined by its components. -/
@[ext]
theorem ext {x y : PrimeToPTateModule p E} (h : ∀ m, proj m x = proj m y) : x = y :=
  Subtype.ext (funext h)

/-- The point of the Tate module with prescribed compatible components. -/
def mk (x : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m E)
    (hx : x ∈ primeToPTateModuleSubgroup p E) : PrimeToPTateModule p E :=
  (⟨x, hx⟩ : primeToPTateModuleSubgroup p E)

/-- The components of `mk x hx` are the prescribed ones. -/
@[simp]
theorem proj_mk (x : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m E)
    (hx : x ∈ primeToPTateModuleSubgroup p E) (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    proj m (mk x hx) = x m :=
  (rfl)

/-- The family of components identifies the Tate module with the subgroup of compatible families
of the product. -/
theorem range_proj :
    Set.range (fun x : PrimeToPTateModule p E ↦ fun m ↦ proj m x) =
      (primeToPTateModuleSubgroup p E : Set (∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
        rootsOfUnity m E)) := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨mk y hy, rfl⟩⟩
  rintro ⟨x, rfl⟩
  exact fun m n h ↦ proj_pow_div x h

section Lift

variable {G : Type*} [MulOneClass G]
  (f : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, G →* rootsOfUnity m E)
  (hf : ∀ (m n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) (g : G), (n : ℕ) ∣ m →
    (f m g : Eˣ) ^ ((m : ℕ) / n) = f n g)

/-- The homomorphism into the prime-to-`p` Tate module determined by a family of homomorphisms
into the levels `μ_m(E)` that is compatible along the power maps. -/
def lift : G →* PrimeToPTateModule p E :=
  (MonoidHom.pi f).codRestrict (primeToPTateModuleSubgroup p E) fun g m n h ↦ hf m n g h

/-- The components of `lift f hf` are the prescribed homomorphisms. -/
@[simp]
theorem proj_lift (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) (g : G) : proj m (lift f hf g) = f m g :=
  (rfl)

/-- **Uniqueness of the lift.** A homomorphism into the Tate module whose components are the
prescribed homomorphisms `f m` is `lift f hf`. -/
theorem lift_unique (F : G →* PrimeToPTateModule p E) (hF : ∀ m, (proj m).comp F = f m) :
    F = lift f hf :=
  MonoidHom.ext fun g ↦ ext fun m ↦ by rw [proj_lift, ← hF m, MonoidHom.comp_apply]

end Lift

/-! ### The inverse-limit topology -/

/-- The inverse-limit topology on the prime-to-`p` Tate module, induced from the product of the
discrete groups `μ_m(E)`. -/
instance : TopologicalSpace (PrimeToPTateModule p E) :=
  .induced (fun x m ↦ proj m x) (@Pi.topologicalSpace _ _ fun _ ↦ ⊥)

/-- The inverse-limit topology is induced from the product of the discrete levels. This is the
defining equation of the topology, stated with the discrete topology on each level supplied
locally rather than as a global instance on `rootsOfUnity m E`. -/
private theorem isInducing_proj
    [t : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, TopologicalSpace (rootsOfUnity m E)]
    [∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, DiscreteTopology (rootsOfUnity m E)] :
    Topology.IsInducing (fun x : PrimeToPTateModule p E ↦ fun m ↦ proj m x) := by
  refine ⟨?_⟩
  -- The topology on `PrimeToPTateModule p E` is by definition induced from the product of the
  -- levels with the *bottom* topology, whereas the goal is stated for the arbitrary discrete
  -- instances `t`. Since `t` is a variable rather than a definition, no unfolding identifies it
  -- with `⊥`; once `DiscreteTopology.eq_bot` rewrites `t` to `fun _ ↦ ⊥`, both sides are the
  -- defining topology and agree by `rfl`.
  rw [show t = fun _ ↦ ⊥ from funext fun m ↦ DiscreteTopology.eq_bot]
  rfl

/-- A map into the prime-to-`p` Tate module is continuous exactly when each of its components is
locally constant. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → PrimeToPTateModule p E} :
    Continuous f ↔ ∀ m, IsLocallyConstant fun x ↦ proj m (f x) := by
  let (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : TopologicalSpace (rootsOfUnity m E) := ⊥
  have (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : DiscreteTopology (rootsOfUnity m E) := ⟨rfl⟩
  simp_rw [isInducing_proj.continuous_iff, continuous_pi_iff, IsLocallyConstant.iff_continuous,
    Function.comp_def]

/-- Each projection of the prime-to-`p` Tate module is locally constant. -/
theorem isLocallyConstant_proj (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    IsLocallyConstant (proj m : PrimeToPTateModule p E → rootsOfUnity m E) :=
  continuous_iff.1 continuous_id m

instance : IsTopologicalGroup (PrimeToPTateModule p E) :=
  letI (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : TopologicalSpace (rootsOfUnity m E) := ⊥
  haveI (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : DiscreteTopology (rootsOfUnity m E) := ⟨rfl⟩
  isInducing_proj.isTopologicalGroup (MonoidHom.pi proj)

/-- The family of components embeds the Tate module into the product of the discrete levels. -/
private theorem isEmbedding_proj
    [∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, TopologicalSpace (rootsOfUnity m E)]
    [∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, DiscreteTopology (rootsOfUnity m E)] :
    Topology.IsEmbedding (fun x : PrimeToPTateModule p E ↦ fun m ↦ proj m x) :=
  ⟨isInducing_proj, fun _ _ h ↦ ext (congrFun h)⟩

instance : T2Space (PrimeToPTateModule p E) :=
  letI (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : TopologicalSpace (rootsOfUnity m E) := ⊥
  haveI (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : DiscreteTopology (rootsOfUnity m E) := ⟨rfl⟩
  isEmbedding_proj.t2Space

instance : TotallyDisconnectedSpace (PrimeToPTateModule p E) :=
  letI (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : TopologicalSpace (rootsOfUnity m E) := ⊥
  haveI (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : DiscreteTopology (rootsOfUnity m E) := ⟨rfl⟩
  isEmbedding_proj.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- For a domain, the levels `μ_m(E)` are finite, so the prime-to-`p` Tate module is compact: it
is a closed subgroup of the product of the finite discrete levels. -/
instance {R : Type*} [CommRing R] [IsDomain R] : CompactSpace (PrimeToPTateModule p R) := by
  let (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : TopologicalSpace (rootsOfUnity m R) := ⊥
  have (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : DiscreteTopology (rootsOfUnity m R) := ⟨rfl⟩
  have (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : NeZero (m : ℕ) := ⟨m.2.1⟩
  refine Topology.IsClosedEmbedding.compactSpace
    (f := fun x : PrimeToPTateModule p R ↦ fun m ↦ proj m x) ⟨isEmbedding_proj, ?_⟩
  rw [range_proj]
  -- The compatible families are cut out by equations between coordinates of a product of
  -- discrete spaces, each of which is closed.
  simp only [primeToPTateModuleSubgroup, Subgroup.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, Set.ofPred_forall]
  refine isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦ ?_
  let : TopologicalSpace Rˣ := ⊥
  have : DiscreteTopology Rˣ := ⟨rfl⟩
  have hm : Continuous fun ζ : rootsOfUnity m R ↦ (ζ : Rˣ) ^ ((m : ℕ) / n) :=
    continuous_of_discreteTopology
  have hn : Continuous fun ζ : rootsOfUnity n R ↦ (ζ : Rˣ) := continuous_of_discreteTopology
  exact isClosed_eq (hm.comp (continuous_apply m)) (hn.comp (continuous_apply n))

/-- **Surjectivity from the finite levels.** A continuous map from a compact space into the
prime-to-`p` Tate module is surjective as soon as each of its components is surjective: the fibres
over the components of a point form a directed family of nonempty closed sets, whose intersection
is the fibre over the point. -/
theorem surjective_of_forall_surjective_proj {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → PrimeToPTateModule p E} (hf : Continuous f)
    (h : ∀ m, Function.Surjective fun x ↦ proj m (f x)) : Function.Surjective f := by
  intro y
  set t : {m : ℕ // m ≠ 0 ∧ m.Coprime p} → Set X := fun m ↦ {x | proj m (f x) = proj m y}
  -- The level-`n` component determines the level-`m` component for `m ∣ n`.
  have hsub {m n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}} (hmn : (m : ℕ) ∣ n) : t n ⊆ t m :=
    fun x (hx : proj n (f x) = proj n y) ↦ Subtype.ext <| by
      rw [← proj_pow_div (f x) hmn, ← proj_pow_div y hmn, hx]
  have : Nonempty {m : ℕ // m ≠ 0 ∧ m.Coprime p} := ⟨⟨1, one_ne_zero, Nat.coprime_one_left p⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun m n ↦ ⟨⟨m * n, mul_ne_zero m.2.1 n.2.1, Nat.Coprime.mul_left m.2.2 n.2.2⟩,
      hsub (dvd_mul_right _ _), hsub (dvd_mul_left _ _)⟩)
    (fun m ↦ h m (proj m y)) (fun m ↦ ((continuous_iff.1 hf m).isClosed_fiber _).isCompact)
    fun m ↦ (continuous_iff.1 hf m).isClosed_fiber _
  exact ⟨x, ext fun m ↦ Set.mem_iInter.1 hx m⟩

/-! ### Topological generators -/

/-- **A point with primitive components.** If `E` has a primitive `m`-th root of unity for every
nonzero `m` prime to `p`, and a continuous map `f` from a compact space into the Tate module is
surjective at each level, then some value `f x` has a primitive `m`-th root of unity as its
level-`m` component for every `m`. -/
theorem exists_forall_isPrimitiveRoot_proj {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → PrimeToPTateModule p E} (hf : Continuous f)
    (h : ∀ m, Function.Surjective fun x ↦ proj m (f x))
    (hE : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, ∃ ζ : E, IsPrimitiveRoot ζ m) :
    ∃ x, ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsPrimitiveRoot (proj m (f x) : Eˣ) m := by
  -- The points whose level-`m` component is primitive form a directed family of nonempty closed
  -- sets, since a power `ζ ^ (n / m)` of a primitive `n`-th root `ζ` is a primitive `m`-th root.
  set t : {m : ℕ // m ≠ 0 ∧ m.Coprime p} → Set X :=
    fun m ↦ (fun x ↦ proj m (f x)) ⁻¹' {ζ | IsPrimitiveRoot (ζ : Eˣ) m}
  have hsub {m n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}} (hmn : (m : ℕ) ∣ n) : t n ⊆ t m := by
    intro x (hx : IsPrimitiveRoot (proj n (f x) : Eˣ) n)
    have h' := hx.pow_of_dvd (Nat.div_ne_zero_iff_of_dvd hmn |>.2 ⟨n.2.1, m.2.1⟩)
      (Nat.div_dvd_of_dvd hmn)
    rwa [proj_pow_div (f x) hmn, Nat.div_div_self hmn n.2.1] at h'
  have hne (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : (t m).Nonempty := by
    have : NeZero (m : ℕ) := ⟨m.2.1⟩
    obtain ⟨ζ, hζ⟩ := hE m
    obtain ⟨x, hx⟩ := h m hζ.toRootsOfUnity
    refine ⟨x, ?_⟩
    simp only [t, Set.mem_preimage, Set.mem_ofPred, hx]
    rwa [← IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.val_toRootsOfUnity_coe]
  have hclosed (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : IsClosed (t m) :=
    isOpen_compl_iff.1 (continuous_iff.1 hf m {ζ | IsPrimitiveRoot (ζ : Eˣ) m}ᶜ)
  have : Nonempty {m : ℕ // m ≠ 0 ∧ m.Coprime p} := ⟨⟨1, one_ne_zero, Nat.coprime_one_left p⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun m n ↦ ⟨⟨m * n, mul_ne_zero m.2.1 n.2.1, Nat.Coprime.mul_left m.2.2 n.2.2⟩,
      hsub (dvd_mul_right _ _), hsub (dvd_mul_left _ _)⟩)
    hne (fun m ↦ (hclosed m).isCompact) hclosed
  exact ⟨x, Set.mem_iInter.1 hx⟩

/-- **A topological generator.** Over a domain, a point of the Tate module whose level-`m`
component is a primitive `m`-th root of unity for every `m` generates a dense subgroup. -/
theorem topologicalClosure_zpowers_eq_top {R : Type*} [CommRing R] [IsDomain R]
    {ζ : PrimeToPTateModule p R}
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsPrimitiveRoot (proj m ζ : Rˣ) m) :
    (Subgroup.zpowers ζ).topologicalClosure = ⊤ := by
  -- The closure of the subgroup generated by `ζ` is compact and surjects onto every level
  -- `μ_m(R)`, which the primitive root `proj m ζ` generates.
  set C := (Subgroup.zpowers ζ).topologicalClosure
  have : CompactSpace C :=
    isCompact_iff_compactSpace.1 (Subgroup.zpowers ζ).isClosed_topologicalClosure.isCompact
  have hsurj : Function.Surjective ((↑) : C → PrimeToPTateModule p R) := by
    refine surjective_of_forall_surjective_proj continuous_subtype_val fun m y ↦ ?_
    have : NeZero (m : ℕ) := ⟨m.2.1⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (proj m ζ : Rˣ) ^ k = y := by
      rw [← Subgroup.mem_zpowers_iff, (hζ m).zpowers_eq]
      exact y.2
    exact ⟨⟨ζ ^ k, (Subgroup.zpowers ζ).le_topologicalClosure
      (Subgroup.zpow_mem_zpowers ζ k)⟩,
      Subtype.ext (by simp [hk])⟩
  exact eq_top_iff.2 fun x _ ↦ by
    obtain ⟨c, rfl⟩ := hsurj x
    exact c.2

/-! ### Compatible systems of primitive roots of unity -/

section Primitive

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Compatible primitive roots of unity exist.** If a domain `R` has a primitive `m`-th root of
unity for every nonzero `m` prime to `p`, then the prime-to-`p` Tate module of `R` has a point
whose level-`m` component is a primitive `m`-th root of unity for every `m`. Equivalently, there
are primitive `m`-th roots of unity `ζ_m ∈ R` with `ζ_m ^ (m / n) = ζ_n` whenever `n ∣ m`. -/
theorem exists_forall_isPrimitiveRoot
    (hR : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, ∃ ζ : R, IsPrimitiveRoot ζ m) :
    ∃ ζ : PrimeToPTateModule p R, ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      IsPrimitiveRoot (proj m ζ : Rˣ) m := by
  let (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : TopologicalSpace (rootsOfUnity m R) := ⊥
  have (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : DiscreteTopology (rootsOfUnity m R) := ⟨rfl⟩
  have (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : NeZero (m : ℕ) := ⟨m.2.1⟩
  -- In the compact product of the finite discrete levels, the families whose level-`N` component
  -- is primitive and determines the components at all divisors of `N` form a directed family of
  -- nonempty closed sets. A point in their intersection is a compatible primitive family.
  set t : {m : ℕ // m ≠ 0 ∧ m.Coprime p} →
      Set (∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m R) := fun N ↦
    {x | IsPrimitiveRoot (x N : Rˣ) N ∧
      ∀ n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, (n : ℕ) ∣ N → (x N : Rˣ) ^ ((N : ℕ) / n) = x n}
  have hsub {M N : {m : ℕ // m ≠ 0 ∧ m.Coprime p}} (hMN : (M : ℕ) ∣ N) : t N ⊆ t M := by
    rintro x ⟨hx, hc⟩
    refine ⟨?_, fun n hn ↦ ?_⟩
    · have h' := hx.pow_of_dvd (Nat.div_ne_zero_iff_of_dvd hMN |>.2 ⟨N.2.1, M.2.1⟩)
        (Nat.div_dvd_of_dvd hMN)
      rwa [hc M hMN, Nat.div_div_self hMN N.2.1] at h'
    · rw [← hc M hMN, ← hc n (hn.trans hMN), ← pow_mul, Nat.div_mul_div hMN hn]
  have hne (N : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : (t N).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hR N
    -- The family `n ↦ ζ ^ (N / gcd(N, n))`: an `n`-th root of unity for every `n`, which is
    -- `ζ ^ (N / n)` when `n ∣ N`.
    have hmem (n : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
        hζ.toRootsOfUnity.1 ^ ((N : ℕ) / Nat.gcd N n) ∈ rootsOfUnity n R := by
      rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _),
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), pow_mul,
        (mem_rootsOfUnity _ _).1 hζ.toRootsOfUnity.2, one_pow]
    refine ⟨fun n ↦ ⟨_, hmem n⟩, ?_, fun n hn ↦ ?_⟩
    · simp only [Nat.gcd_self, Nat.div_self (Nat.pos_of_ne_zero N.2.1), pow_one]
      rwa [← IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.val_toRootsOfUnity_coe]
    · simp [Nat.gcd_self, Nat.div_self (Nat.pos_of_ne_zero N.2.1), Nat.gcd_eq_right hn]
  have hclosed (N : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) : IsClosed (t N) := by
    have hN : Continuous fun x : (∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m R) ↦
        x N := continuous_apply N
    simp only [t, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ (isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦ ?_)
    · exact (isClosed_discrete {ζ : rootsOfUnity N R | IsPrimitiveRoot (ζ : Rˣ) N}).preimage hN
    · have hNn : Continuous fun x : (∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, rootsOfUnity m R) ↦
          (x N, x n) := hN.prodMk (continuous_apply n)
      exact (isClosed_discrete {y : rootsOfUnity N R × rootsOfUnity n R |
        (y.1 : Rˣ) ^ ((N : ℕ) / n) = y.2}).preimage hNn
  have : Nonempty {m : ℕ // m ≠ 0 ∧ m.Coprime p} := ⟨⟨1, one_ne_zero, Nat.coprime_one_left p⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun m n ↦ ⟨⟨m * n, mul_ne_zero m.2.1 n.2.1, Nat.Coprime.mul_left m.2.2 n.2.2⟩,
      hsub (dvd_mul_right _ _), hsub (dvd_mul_left _ _)⟩)
    hne (fun N ↦ (hclosed N).isCompact) hclosed
  rw [Set.mem_iInter] at hx
  exact ⟨mk x (mem_primeToPTateModuleSubgroup_iff.2 fun m n h ↦ (hx m).2 n h),
    fun m ↦ (hx m).1⟩

/-- **Every root of unity extends to a compatible family.** If a domain `R` has a primitive `m`-th
root of unity for every nonzero `m` prime to `p`, then each projection of the prime-to-`p` Tate
module of `R` onto its level `μ_m(R)` is surjective. -/
theorem proj_surjective
    (hR : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, ∃ ζ : R, IsPrimitiveRoot ζ m)
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    Function.Surjective (proj m : PrimeToPTateModule p R → rootsOfUnity m R) := by
  have : NeZero (m : ℕ) := ⟨m.2.1⟩
  obtain ⟨ζ, hζ⟩ := exists_forall_isPrimitiveRoot hR
  intro y
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (proj m ζ : Rˣ) ^ k = y := by
    rw [← Subgroup.mem_zpowers_iff, (hζ m).zpowers_eq]
    exact y.2
  exact ⟨ζ ^ k, Subtype.ext (by simp [hk])⟩

end Primitive

/-! ### Functoriality and the action of automorphisms -/

section Map

variable {F : Type*} [CommMonoid F]

/-- The homomorphism of prime-to-`p` Tate modules induced by a monoid homomorphism `f : E →* F`,
applying `f` to each component `μ_m(E) → μ_m(F)`. -/
def map (f : E →* F) : PrimeToPTateModule p E →* PrimeToPTateModule p F :=
  lift (fun m ↦ (restrictRootsOfUnity f m).comp (proj m)) fun m n x h ↦ by
    ext
    simp only [MonoidHom.comp_apply, Units.val_pow_eq_pow_val, restrictRootsOfUnity_coe_apply]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, proj_pow_div x h]

/-- The components of `map f x` are the images under `f` of the components of `x`. -/
@[simp]
theorem proj_map (f : E →* F) (x : PrimeToPTateModule p E)
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    proj m (map f x) = restrictRootsOfUnity f m (proj m x) :=
  (rfl)

/-- Mapping the identity homomorphism gives the identity on the prime-to-`p` Tate module. -/
@[simp]
theorem map_id : map (MonoidHom.id E) = MonoidHom.id (PrimeToPTateModule p E) := by
  ext x m
  simp

/-- Mapping a composite of monoid homomorphisms is the composite of the induced maps on the
prime-to-`p` Tate modules. -/
@[simp]
theorem map_comp {G : Type*} [CommMonoid G] (g : F →* G) (f : E →* F) :
    map (p := p) (g.comp f) = (map (p := p) g).comp (map (p := p) f) := by
  ext x m
  simp

/-- The homomorphism of Tate modules induced by a monoid homomorphism is continuous. -/
theorem continuous_map (f : E →* F) : Continuous (map f : PrimeToPTateModule p E → _) :=
  continuous_iff.2 fun m ↦ by
    simpa only [proj_map, Function.comp_def] using
      (isLocallyConstant_proj m).comp (restrictRootsOfUnity f m)

end Map

section Action

variable {M : Type*} [Monoid M] [MulDistribMulAction M E]

/-- A monoid acting on `E` by multiplicative maps acts on the prime-to-`p` Tate module
componentwise. For the absolute Galois group of a field acting on a separable closure `E`, this is
the action recorded by the Tate twist `(1)` in `ℤ̂^{(p')}(1)`. -/
instance : SMul M (PrimeToPTateModule p E) :=
  ⟨fun g ↦ map (MulDistribMulAction.toMonoidHom E g)⟩

/-- The action of `g` on the prime-to-`p` Tate module is the map induced by the action of `g`
on `E`. -/
theorem smul_def (g : M) (x : PrimeToPTateModule p E) :
    g • x = map (MulDistribMulAction.toMonoidHom E g) x :=
  rfl

/-- The components of `g • x` are obtained by letting `g` act on the components of `x`. -/
@[simp]
theorem coe_proj_smul (g : M) (x : PrimeToPTateModule p E)
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    ((proj m (g • x) : Eˣ) : E) = g • ((proj m x : Eˣ) : E) := by
  rw [smul_def, proj_map, restrictRootsOfUnity_coe_apply, MulDistribMulAction.toMonoidHom_apply]

instance : MulDistribMulAction M (PrimeToPTateModule p E) where
  one_smul x := ext fun m ↦ Subtype.ext <| Units.ext <| by simp
  mul_smul g h x := ext fun m ↦ Subtype.ext <| Units.ext <| by simp [mul_smul]
  smul_mul g x y := ext fun m ↦ Subtype.ext <| Units.ext <| by simp [smul_mul']
  smul_one g := ext fun m ↦ Subtype.ext <| Units.ext <| by simp

instance : ContinuousConstSMul M (PrimeToPTateModule p E) :=
  ⟨fun g ↦ continuous_map (MulDistribMulAction.toMonoidHom E g)⟩

end Action

/-! ### The character of rational exponents -/

section RatChar

/-- The value `ζ_{q.den} ^ q.num` of the character `TauCeti.PrimeToPTateModule.ratChar`, before
bundling. -/
private def ratCharFun (x : PrimeToPTateModule 1 E) (q : ℚ) : Eˣ :=
  (proj ⟨q.den, q.den_nz, Nat.coprime_one_right _⟩ x : Eˣ) ^ q.num

/-- `ζ_{q.den} ^ q.num = ζ_n ^ k` whenever `q = k / n`, by compatibility of the components. -/
private theorem ratCharFun_eq_zpow (x : PrimeToPTateModule 1 E)
    (n : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) {q : ℚ} {k : ℤ} (h : (k : ℚ) = q * (n : ℕ)) :
    ratCharFun x q = (proj n x : Eˣ) ^ k := by
  have hdvd : q.den ∣ (n : ℕ) := Int.natCast_dvd_natCast.mp
    (Rat.den_dvd_of_intCast_eq_mul_intCast q (by rw [h, Int.cast_natCast]))
  obtain ⟨c, hc⟩ := hdvd
  have hk : k = c * q.num := by
    have : (k : ℚ) = c * q.num := by
      rw [h, hc, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num, mul_comm]
    exact_mod_cast this
  have hpow := proj_pow_div x (m := n) (n := ⟨q.den, q.den_nz, Nat.coprime_one_right _⟩) ⟨c, hc⟩
  have hdiv : (n : ℕ) / q.den = c := by rw [hc, Nat.mul_div_cancel_left _ q.den_pos]
  rw [hdiv] at hpow
  rw [ratCharFun, hk, zpow_mul, zpow_natCast, hpow]

variable (E) in
/-- The **character of rational exponents** attached to a point `ζ = (ζ_n)_n` of the Tate module
`lim_n μ_n(E)`: the homomorphism `ℚ → Eˣ` sending `k / n` to `ζ_n ^ k`. It is well defined by
compatibility of the components and trivial on `ℤ`
(`TauCeti.PrimeToPTateModule.ratChar_ofAdd_intCast`), and it determines `ζ`
(`TauCeti.PrimeToPTateModule.ratChar_injective`). -/
def ratChar : PrimeToPTateModule 1 E →* (Multiplicative ℚ →* Eˣ) where
  toFun x :=
    { toFun q := ratCharFun x q.toAdd
      map_one' := by simp [ratCharFun]
      map_mul' q r := by
        -- Compute all three values at the common level `q.den * r.den`.
        set a := q.toAdd
        set b := r.toAdd
        let N : {m : ℕ // m ≠ 0 ∧ m.Coprime 1} :=
          ⟨a.den * b.den, mul_ne_zero a.den_nz b.den_nz, Nat.coprime_one_right _⟩
        have ha : ((a.num * b.den : ℤ) : ℚ) = a * (N : ℕ) := by
          push_cast [N]
          rw [← mul_assoc, Rat.mul_den_eq_num]
        have hb : ((b.num * a.den : ℤ) : ℚ) = b * (N : ℕ) := by
          push_cast [N]
          rw [mul_left_comm, Rat.mul_den_eq_num, mul_comm]
        rw [toAdd_mul, ratCharFun_eq_zpow x N ha, ratCharFun_eq_zpow x N hb,
          ratCharFun_eq_zpow x N (k := a.num * b.den + b.num * a.den)
            (by rw [Int.cast_add, ha, hb, add_mul]), zpow_add] }
  map_one' := by
    ext q
    simp [ratCharFun]
  map_mul' x y := by
    ext q
    simp [ratCharFun, mul_zpow]

/-- The character attached to `ζ` sends `q` to `ζ_{q.den} ^ q.num`. -/
theorem ratChar_ofAdd (x : PrimeToPTateModule 1 E) (q : ℚ) :
    ratChar E x (.ofAdd q) = (proj ⟨q.den, q.den_nz, Nat.coprime_one_right _⟩ x : Eˣ) ^ q.num :=
  (rfl)

/-- The character attached to `ζ` sends `q` to `ζ_n ^ k` whenever `q = k / n`. -/
theorem ratChar_ofAdd_eq_zpow (x : PrimeToPTateModule 1 E) (n : {m : ℕ // m ≠ 0 ∧ m.Coprime 1})
    {q : ℚ} {k : ℤ} (h : (k : ℚ) = q * (n : ℕ)) :
    ratChar E x (.ofAdd q) = (proj n x : Eˣ) ^ k :=
  ratCharFun_eq_zpow x n h

/-- The character attached to `ζ` sends `k / n` to `ζ_n ^ k`. -/
@[simp]
theorem ratChar_ofAdd_intCast_div (x : PrimeToPTateModule 1 E)
    (n : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) (k : ℤ) :
    ratChar E x (.ofAdd ((k : ℚ) / (n : ℕ))) = (proj n x : Eˣ) ^ k :=
  ratChar_ofAdd_eq_zpow x n (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.2.1)).symm

/-- The character attached to `ζ` is trivial on the integers. -/
@[simp]
theorem ratChar_ofAdd_intCast (x : PrimeToPTateModule 1 E) (k : ℤ) :
    ratChar E x (.ofAdd (k : ℚ)) = 1 := by
  have h1 : (proj ⟨1, one_ne_zero, Nat.coprime_one_right _⟩ x : Eˣ) = 1 := by
    simpa using (proj ⟨1, one_ne_zero, Nat.coprime_one_right _⟩ x).2
  rw [ratChar_ofAdd_eq_zpow x ⟨1, one_ne_zero, Nat.coprime_one_right _⟩ (k := k)
    (by rw [Nat.cast_one, mul_one]), h1, one_zpow]

/-- A point of the Tate module is determined by its character of rational exponents: the
character sends `1 / n` to the component `ζ_n`. -/
theorem ratChar_injective : Function.Injective (ratChar E) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ext fun n ↦ Subtype.ext ?_
  have h := ratChar_ofAdd_intCast_div x n 1
  rw [hx, MonoidHom.one_apply, zpow_one] at h
  rw [← h, map_one, OneMemClass.coe_one]

/-- If every component `ζ_n` of `ζ` is a primitive `n`-th root of unity, then the character
attached to `ζ` vanishes exactly on the integers. -/
theorem ratChar_ofAdd_eq_one_iff {x : PrimeToPTateModule 1 E}
    (hx : ∀ n : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj n x : Eˣ) n) {q : ℚ} :
    ratChar E x (.ofAdd q) = 1 ↔ q.den = 1 := by
  rw [ratChar_ofAdd, (hx _).zpow_eq_one_iff_dvd]
  refine ⟨fun h ↦ Nat.Coprime.eq_one_of_dvd q.reduced.symm (Int.natCast_dvd.mp h), fun h ↦ ?_⟩
  simp [h]

end RatChar

/-! ### The profinite integers -/

section ZHat

universe u

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The level components of a profinite power.** The level-`n` component of the image of `a ∈ ℤ̂`
under `zHat.lift ζ` is the natural power of `ζ_n` by the residue of `a` modulo `n`. -/
theorem coe_proj_zHatLift (ζ : PrimeToPTateModule 1 R) (n : ℕ+) (a : zHat.{u}) :
    (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (zHat.lift ζ a) : Rˣ) =
      (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Rˣ) ^
        (zHat.toZMod n (Additive.ofMul a)).val := by
  let : TopologicalSpace (rootsOfUnity n R) := ⊥
  have : DiscreteTopology (rootsOfUnity n R) := ⟨rfl⟩
  -- The projection to the finite discrete level `μ_n(R)` is a continuous homomorphism, so it
  -- carries the lift of `ζ` to the lift of `ζ_n`, which is a power of `ζ_n` as `ζ_n ^ n = 1`.
  let q : PrimeToPTateModule 1 R →ₜ* rootsOfUnity n R :=
    ⟨proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩,
      (isLocallyConstant_proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩).continuous⟩
  have hq : (q ζ) ^ (n : ℕ) = 1 := Subtype.ext <| by
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity _ _).1 (q ζ).2
  have h := zpowHat_eq_pow_val_toZMod hq (Additive.ofMul a)
  rw [zpowHat_def, toMul_ofMul, ← zHat.map_lift] at h
  exact congrArg ((↑) : rootsOfUnity n R → Rˣ) h |>.trans (by simp [q])

variable {ζ : PrimeToPTateModule 1 R}
  (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj m ζ : Rˣ) m)
include hζ

/-- A point of the Tate module whose components are all primitive supplies a primitive `n`-th root
of unity in `R`, hence all `n`-th roots of unity, for every `n ≠ 0`. -/
theorem hasEnoughRootsOfUnity_of_isPrimitiveRoot_proj (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity R n :=
  ⟨⟨_, IsPrimitiveRoot.coe_units_iff.2 (hζ ⟨n, NeZero.ne n, Nat.coprime_one_right _⟩)⟩,
    rootsOfUnity.isCyclic R n⟩

/-- If every component of `ζ` is primitive, then `zHat.lift ζ` is injective: the level-`n`
component of `zHat.lift ζ a` is `ζ_n` raised to the residue of `a` modulo `n`, which determines
that residue, and a profinite integer is determined by its residues. -/
theorem zHatLift_injective : Function.Injective (zHat.lift.{u} ζ) := fun a b h ↦ by
  refine Additive.ofMul.injective (zHat.ext_of_toZMod fun n ↦ ZMod.val_injective _ ?_)
  have h' : (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Rˣ) ^
        (zHat.toZMod n (Additive.ofMul a)).val =
      (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Rˣ) ^
        (zHat.toZMod n (Additive.ofMul b)).val := by
    rw [← coe_proj_zHatLift, ← coe_proj_zHatLift, h]
  exact (hζ ⟨n, n.ne_zero, Nat.coprime_one_right _⟩).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'

/-- If every component of `ζ` is primitive, then `zHat.lift ζ` is surjective, since `ζ` is a
topological generator of the Tate module. -/
theorem zHatLift_surjective : Function.Surjective (zHat.lift.{u} ζ) :=
  zHat.lift_surjective ζ (topologicalClosure_zpowers_eq_top hζ)

variable (ζ) in
/-- **The Tate module of a domain with compatible primitive roots of unity is `ℤ̂`.** If `ζ` is a
point of `lim_n μ_n(R)` whose level-`n` component is a primitive `n`-th root of unity for every
`n`, then `zHat.lift ζ` is an isomorphism of topological groups `ℤ̂ ≃ₜ* lim_n μ_n(R)`; this is its
inverse, sending `ζ` to the canonical generator `zHat.gen`. -/
noncomputable def continuousMulEquivZHat : PrimeToPTateModule 1 R ≃ₜ* zHat.{u} :=
  -- The construction follows `TauCeti.maximalUnramifiedGaloisGroupEquivZHat`: a bijective
  -- `zHat.lift`, whose inverse is continuous because `ℤ̂` is compact and the target is Hausdorff.
  let e : zHat.{u} ≃* PrimeToPTateModule 1 R :=
    MulEquiv.ofBijective (zHat.lift ζ).toMonoidHom
      ⟨zHatLift_injective hζ, zHatLift_surjective hζ⟩
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := (zHat.lift ζ).continuous
      continuous_invFun := (zHat.lift ζ).continuous.continuous_symm_of_equiv_compact_to_t2
        (f := e.toEquiv) }

/-- The inverse of `continuousMulEquivZHat ζ hζ` is `zHat.lift ζ`. -/
@[simp]
theorem continuousMulEquivZHat_symm_apply (a : zHat.{u}) :
    (continuousMulEquivZHat ζ hζ).symm a = zHat.lift ζ a :=
  (rfl)

/-- The isomorphism `continuousMulEquivZHat ζ hζ` sends `ζ` to the canonical generator of `ℤ̂`. -/
@[simp]
theorem continuousMulEquivZHat_self : continuousMulEquivZHat.{u} ζ hζ ζ = zHat.gen :=
  (continuousMulEquivZHat ζ hζ).symm.injective <| by
    rw [ContinuousMulEquiv.symm_apply_apply, continuousMulEquivZHat_symm_apply, zHat.lift_gen]

/-- **The coordinates of the isomorphism with `ℤ̂`.** The residue modulo `n` of the image of `x`
under `continuousMulEquivZHat ζ hζ` is the exponent by which `ζ_n` gives the level-`n` component
of `x`. -/
theorem coe_proj_pow_toZMod_continuousMulEquivZHat (x : PrimeToPTateModule 1 R) (n : ℕ+) :
    (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Rˣ) ^
        (zHat.toZMod n (Additive.ofMul (continuousMulEquivZHat.{u} ζ hζ x))).val =
      proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ x := by
  rw [← coe_proj_zHatLift, ← continuousMulEquivZHat_symm_apply hζ,
    ContinuousMulEquiv.symm_apply_apply]

end ZHat

end PrimeToPTateModule

end TauCeti

end
