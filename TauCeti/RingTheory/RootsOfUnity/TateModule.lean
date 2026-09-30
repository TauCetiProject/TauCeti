/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.LocallyConstant.Basic

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

## Main definitions

* `TauCeti.primeToPTateModuleSubgroup p E`: the subgroup of compatible families in the product
  `∏_m μ_m(E)`.
* `TauCeti.PrimeToPTateModule p E`: the prime-to-`p` Tate module, a commutative topological group.
* `TauCeti.PrimeToPTateModule.proj m`: the projection to the level `μ_m(E)`.
* `TauCeti.PrimeToPTateModule.mk`: the point with prescribed compatible components.
* `TauCeti.PrimeToPTateModule.lift`: the homomorphism into the Tate module determined by a
  compatible family of homomorphisms into the levels.

## Main results

* `TauCeti.PrimeToPTateModule.proj_pow_div`: the components of a point are compatible.
* `TauCeti.PrimeToPTateModule.ext`: a point is determined by its components.
* `TauCeti.PrimeToPTateModule.continuous_iff`: a map into the Tate module is continuous exactly
  when each of its components is locally constant.
* The instances `IsTopologicalGroup`, `T2Space`, `TotallyDisconnectedSpace`, and, for a domain,
  `CompactSpace`.
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
  (show ↥(primeToPTateModuleSubgroup p E) from x).2 m n h

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

variable {G : Type*} [Group G] (f : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, G →* rootsOfUnity m E)
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

end PrimeToPTateModule

end TauCeti

end
