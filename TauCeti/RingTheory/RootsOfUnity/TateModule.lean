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
* `TauCeti.PrimeToPTateModule.map`: the homomorphism of Tate modules induced by a monoid
  homomorphism `E →* F`.
* The instance `MulDistribMulAction M (PrimeToPTateModule p E)` for a monoid `M` acting on `E` by
  multiplicative maps, componentwise; for the Galois group of `E` it is the twist `(1)`.

## Main results

* `TauCeti.PrimeToPTateModule.proj_pow_div`: the components of a point are compatible.
* `TauCeti.PrimeToPTateModule.ext`: a point is determined by its components.
* `TauCeti.PrimeToPTateModule.lift_unique`: `lift` is the unique homomorphism with the prescribed
  components.
* `TauCeti.PrimeToPTateModule.continuous_iff`: a map into the Tate module is continuous exactly
  when each of its components is locally constant.
* `TauCeti.PrimeToPTateModule.surjective_of_forall_surjective_proj`: a continuous map from a
  compact space is surjective when each of its components is.
* `TauCeti.PrimeToPTateModule.proj_map`, `TauCeti.PrimeToPTateModule.coe_proj_smul`: `map` and
  the action are computed componentwise.
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

end PrimeToPTateModule

end TauCeti

end
