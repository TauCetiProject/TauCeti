/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.CrossedModule.H0

/-!
# Degree-one continuous cohomology of a crossed module

Let a topological group `G` act on a crossed module `∂ : T → H` of discrete groups, compatibly with
its structure (`TauCeti.CrossedModule.IsEquivariant`). A **`1`-cocycle** is a pair `(p, u)` of
continuous maps `p : G → H` and `u : G × G → T` such that

`∂ (u g k) = p g * g • p k * (p (g * k))⁻¹` and
`p g • (g • u k l) * u g (k * l) = u g k * u (g * k) l`,

where `h • t` is the action of `H` on `T`. Thinking of the crossed module as a group-like category,
whose objects are the elements of `H` and whose arrows `h ⟶ ∂ t * h` are the elements `t : T`,
the map `p` is a cocycle of `G` with values in `H` up to the arrows `u g k`, and the second
identity is their coherence. The trivial `1`-cocycle is `(1, 1)`.

Two operations move a `1`-cocycle within its class:

* the **twist** by `a : H`, `(p, u) ↦ (g ↦ a⁻¹ * p g * g • a, a⁻¹ • u)`, extending the twist of
  nonabelian `1`-cocycles (`TauCeti.NonabelianH1.Cocycle.twist`);
* the **gauge** by a continuous map `v : G → T`,
  `(p, u) ↦ (g ↦ ∂ (v g) * p g, (g, k) ↦ v g * p g • (g • v k) * u g k * (v (g * k))⁻¹)`.

Two `1`-cocycles are **cohomologous** when one is obtained from the other by a twist followed by a
gauge. This is an equivalence relation, and the quotient is the pointed set `H¹(G, T → H)`.
Viewing the crossed module as a two-term complex with `T` in degree `-1`, this is its first
cohomology.

A `1`-cocycle `f` of `G` with values in `H` gives the `1`-cocycle `(f, 1)`, and so a map
`H¹(G, H) → H¹(G, T → H)` of pointed sets. Its kernel is the image of `H¹(G, T) → H¹(G, H)`,
which is the exactness of the end

`H¹(G, T) → H¹(G, H) → H¹(G, T → H)`

of the long exact sequence of a crossed module; exactness at `H¹(G, T)` is
`TauCeti.CrossedModule.H0.mem_range_toH1_iff`. For a crossed module `1 → H` with trivial source,
the map is a bijection `H¹(G, H) ≃ H¹(G, 1 → H)`. When the boundary is bijective, as for the
identity crossed module `H → H`, the pointed set `H¹(G, T → H)` is a single point.

## Main definitions

* `TauCeti.CrossedModule.OneCocycle G M`: the `1`-cocycles of `G` with values in the crossed module
  `M`.
* `TauCeti.CrossedModule.OneCocycle.twist`: the twist of a `1`-cocycle by an element of `H`.
* `TauCeti.CrossedModule.OneCocycle.gauge`: the gauge of a `1`-cocycle by a continuous map
  `G → T`.
* `TauCeti.CrossedModule.OneCocycle.ofCocycle`: the `1`-cocycle `(f, 1)` of a cocycle `f` of `H`.
* `TauCeti.CrossedModule.H1 G M`: the pointed set `H¹(G, T → H)`, with
  `TauCeti.CrossedModule.H1.mk` the class of a `1`-cocycle.
* `TauCeti.CrossedModule.H1.ofH1`: the map `H¹(G, H) → H¹(G, T → H)` of pointed sets.
* `TauCeti.CrossedModule.H1.ofH1Equiv`: `H¹(G, H) ≃ H¹(G, 1 → H)` for trivial `T`.

## Main results

* `TauCeti.CrossedModule.H1.mk_eq_mk_iff`: two `1`-cocycles have the same class exactly when the
  second is a twist followed by a gauge of the first.
* `TauCeti.CrossedModule.H1.ofH1_eq_one_iff`: exactness at `H¹(G, H)`.
* `TauCeti.CrossedModule.H1.subsingleton_of_bijective`: `H¹(G, T → H)` is a point when the
  boundary is bijective.

## Implementation notes

Galois cohomology with coefficients in a crossed module uses discrete groups, such as the points
over an algebraic closure of a crossed module of algebraic groups. We take `T` and `H` discrete:
then continuity of cochains is local constancy, and it is preserved by the action of `H` on `T`.
The twist by `a` acts on `u` through `a⁻¹`, as the twist of nonabelian cocycles does, so that
twists compose as `(z.twist a).twist b = z.twist (a * b)`.

## References

* M. Borovoi, *Abelian Galois cohomology of reductive groups*, Mem. Amer. Math. Soc. 626 (1998),
  §3.
* J.-P. Labesse, *Cohomologie, stabilisation et changement de base*, Astérisque 257 (1999),
  §1.1–1.2 (Définition 1.1.1, Lemme 1.2.1).
* M. Kisin, *Mod p points on Shimura varieties of abelian type*, J. Amer. Math. Soc. 30 (2017),
  §3.2.7.
-/

public section

open Topology

namespace TauCeti

open NonabelianH1

namespace CrossedModule

variable {G T H : Type*} [Group G] [Group T] [Group H] [MulDistribMulAction G T]
  [MulDistribMulAction G H]

/-- The twisted action of `a⁻¹ * h * g • a` on `g • a⁻¹ • t` is the action of `a⁻¹` on
`h • (g • t)`. -/
private theorem act_twist_smul_act {M : CrossedModule T H} [M.IsEquivariant G] (a h : H) (g : G)
    (t : T) :
    M.act (a⁻¹ * h * g • a) (g • M.act a⁻¹ t) = M.act a⁻¹ (M.act h (g • t)) := by
  rw [IsEquivariant.smul_act, ← MulAut.mul_apply, ← map_mul, smul_inv', mul_inv_cancel_right,
    map_mul, MulAut.mul_apply]

variable [TopologicalSpace G] [TopologicalSpace T]

section ActContinuousMap

variable [DiscreteTopology T] (M : CrossedModule T H) {X : Type*} [TopologicalSpace X]

/-- The pointwise action `x ↦ h • v x` of `h : H` on a continuous map `v : X → T` with values in
the discrete source of the crossed module `M`. -/
def actContinuousMap (h : H) (v : C(X, T)) : C(X, T) :=
  ⟨fun x ↦ M.act h (v x), continuous_of_discreteTopology.comp v.continuous⟩

@[simp]
theorem actContinuousMap_apply (h : H) (v : C(X, T)) (x : X) :
    M.actContinuousMap h v x = M.act h (v x) :=
  (rfl)

end ActContinuousMap

variable [TopologicalSpace H]

variable (G) in
/-- A **`1`-cocycle** of `G` with values in the crossed module `M : T → H`: continuous maps
`p : G → H` and `u : G × G → T`, written as a function of two variables, with
`∂ (u g k) = p g * g • p k * (p (g * k))⁻¹` and
`p g • (g • u k l) * u g (k * l) = u g k * u (g * k) l`. -/
@[ext]
structure OneCocycle (M : CrossedModule T H) where
  /-- The map `G → H` of a `1`-cocycle. -/
  cochain : G → H
  /-- The map `G × G → T`, measuring the failure of `cochain` to be a cocycle. -/
  defect : G → G → T
  /-- The map `G → H` of a `1`-cocycle is continuous. -/
  continuous_cochain : Continuous cochain
  /-- The map `G × G → T` of a `1`-cocycle is continuous. -/
  continuous_defect : Continuous fun x : G × G ↦ defect x.1 x.2
  /-- The boundary of the defect is the failure of the cocycle identity for `cochain`. -/
  boundary_defect (g k : G) :
    M.boundary (defect g k) = cochain g * g • cochain k * (cochain (g * k))⁻¹
  /-- The coherence of the defect. -/
  defect_mul (g k l : G) :
    M.act (cochain g) (g • defect k l) * defect g (k * l) = defect g k * defect (g * k) l

namespace OneCocycle

variable {M : CrossedModule T H}

/-- The cocycle identity for the map `G → H` of a `1`-cocycle holds up to the boundary of its
defect. -/
theorem boundary_defect_mul (z : OneCocycle G M) (g k : G) :
    M.boundary (z.defect g k) * z.cochain (g * k) = z.cochain g * g • z.cochain k := by
  rw [z.boundary_defect, inv_mul_cancel_right]

/-- The trivial `1`-cocycle `(1, 1)`. -/
instance : One (OneCocycle G M) where
  one := ⟨fun _ ↦ 1, fun _ _ ↦ 1, continuous_const, continuous_const, fun _ _ ↦ by simp,
    fun _ _ _ ↦ by simp⟩

@[simp]
theorem one_cochain (g : G) : (1 : OneCocycle G M).cochain g = 1 :=
  (rfl)

@[simp]
theorem one_defect (g k : G) : (1 : OneCocycle G M).defect g k = 1 :=
  (rfl)

/-- The `1`-cocycle `(f, 1)` of a cocycle `f` of `G` with values in `H`. -/
def ofCocycle (f : Cocycle G H) : OneCocycle G M where
  cochain := f
  defect _ _ := 1
  continuous_cochain := f.continuous
  continuous_defect := continuous_const
  boundary_defect g k := by simp [f.apply_mul]
  defect_mul _ _ _ := by simp

@[simp]
theorem ofCocycle_cochain (f : Cocycle G H) (g : G) :
    (ofCocycle f : OneCocycle G M).cochain g = f g :=
  (rfl)

@[simp]
theorem ofCocycle_defect (f : Cocycle G H) (g k : G) :
    (ofCocycle f : OneCocycle G M).defect g k = 1 :=
  (rfl)

@[simp]
theorem ofCocycle_one : (ofCocycle 1 : OneCocycle G M) = 1 :=
  (rfl)

theorem ofCocycle_injective : Function.Injective (ofCocycle : Cocycle G H → OneCocycle G M) :=
  fun _ _ h ↦ Cocycle.ext fun g ↦ congrFun (congrArg OneCocycle.cochain h) g

section Discrete

variable [DiscreteTopology T] [DiscreteTopology H]

/-- A map built from the action of `H` on `T` out of continuous maps is continuous. -/
private theorem continuous_act {X : Type*} [TopologicalSpace X] {f : X → H} {t : X → T}
    (hf : Continuous f) (ht : Continuous t) : Continuous fun x ↦ M.act (f x) (t x) :=
  (continuous_of_discreteTopology (f := fun q : H × T ↦ M.act q.1 q.2)).comp (hf.prodMk ht)

variable [M.IsEquivariant G]

section Twist

variable [ContinuousSMul G H]

/-- The **twist** `(g ↦ a⁻¹ * p g * g • a, a⁻¹ • u)` of a `1`-cocycle `(p, u)` by `a : H`. -/
def twist (z : OneCocycle G M) (a : H) : OneCocycle G M where
  cochain g := a⁻¹ * z.cochain g * g • a
  defect g k := M.act a⁻¹ (z.defect g k)
  continuous_cochain := (continuous_const.mul z.continuous_cochain).mul
    (continuous_id.smul continuous_const)
  continuous_defect := continuous_of_discreteTopology.comp z.continuous_defect
  boundary_defect g k := by
    simp only [boundary_act, z.boundary_defect, smul_mul', smul_inv', smul_smul, inv_inv]
    group
  defect_mul g k l := by
    rw [act_twist_smul_act, ← map_mul, ← map_mul, z.defect_mul]

@[simp]
theorem twist_cochain (z : OneCocycle G M) (a : H) (g : G) :
    (z.twist a).cochain g = a⁻¹ * z.cochain g * g • a :=
  (rfl)

@[simp]
theorem twist_defect (z : OneCocycle G M) (a : H) (g k : G) :
    (z.twist a).defect g k = M.act a⁻¹ (z.defect g k) :=
  (rfl)

@[simp]
theorem twist_one (z : OneCocycle G M) : z.twist 1 = z :=
  OneCocycle.ext (funext fun g ↦ by simp) (funext₂ fun g k ↦ by simp)

theorem twist_twist (z : OneCocycle G M) (a b : H) : (z.twist a).twist b = z.twist (a * b) :=
  OneCocycle.ext (funext fun g ↦ by simp [smul_mul', mul_assoc])
    (funext₂ fun g k ↦ by simp [MulAut.mul_apply])

/-- Twisting commutes with passing from a cocycle of `H` to a `1`-cocycle of the crossed
module. -/
@[simp]
theorem ofCocycle_twist (f : Cocycle G H) (a : H) :
    (ofCocycle (f.twist a) : OneCocycle G M) = (ofCocycle f).twist a :=
  OneCocycle.ext (funext fun g ↦ by simp) (funext₂ fun g k ↦ by simp)

end Twist

section Gauge

variable [ContinuousSMul G T] [ContinuousMul G]

/-- The **gauge** `(g ↦ ∂ (v g) * p g, (g, k) ↦ v g * p g • (g • v k) * u g k * (v (g * k))⁻¹)`
of a `1`-cocycle `(p, u)` by a continuous map `v : G → T`. -/
def gauge (z : OneCocycle G M) (v : C(G, T)) : OneCocycle G M where
  cochain g := M.boundary (v g) * z.cochain g
  defect g k := v g * M.act (z.cochain g) (g • v k) * z.defect g k * (v (g * k))⁻¹
  continuous_cochain :=
    (continuous_of_discreteTopology.comp v.continuous).mul z.continuous_cochain
  continuous_defect :=
    (((v.continuous.comp continuous_fst).mul
      (continuous_act (z.continuous_cochain.comp continuous_fst)
        (continuous_fst.smul (v.continuous.comp continuous_snd)))).mul z.continuous_defect).mul
      (v.continuous.comp continuous_mul).inv
  boundary_defect g k := by
    simp only [map_mul, map_inv, boundary_act, z.boundary_defect, smul_mul',
      IsEquivariant.boundary_smul]
    group
  defect_mul g k l := by
    -- The action of `p g * g • p k` is the action of `p (g * k)` conjugated by `u g k`.
    have hc (t : T) : M.act (z.cochain g) (M.act (g • z.cochain k) t) =
        z.defect g k * M.act (z.cochain (g * k)) t * (z.defect g k)⁻¹ := by
      rw [← MulAut.mul_apply, ← map_mul, ← z.boundary_defect_mul, act_boundary_mul]
    have hu : z.defect g (k * l) =
        (M.act (z.cochain g) (g • z.defect k l))⁻¹ * (z.defect g k * z.defect (g * k) l) :=
      eq_inv_mul_of_mul_eq (z.defect_mul g k l)
    simp only [act_boundary_mul]
    simp only [smul_mul', smul_inv', map_mul, map_inv, IsEquivariant.smul_act, smul_smul, hc, hu]
    group

@[simp]
theorem gauge_cochain (z : OneCocycle G M) (v : C(G, T)) (g : G) :
    (z.gauge v).cochain g = M.boundary (v g) * z.cochain g :=
  (rfl)

@[simp]
theorem gauge_defect (z : OneCocycle G M) (v : C(G, T)) (g k : G) :
    (z.gauge v).defect g k = v g * M.act (z.cochain g) (g • v k) * z.defect g k * (v (g * k))⁻¹ :=
  (rfl)

@[simp]
theorem gauge_one (z : OneCocycle G M) : z.gauge 1 = z :=
  OneCocycle.ext (funext fun g ↦ by simp) (funext₂ fun g k ↦ by simp)

theorem gauge_gauge (z : OneCocycle G M) (v w : C(G, T)) :
    (z.gauge w).gauge v = z.gauge (v * w) :=
  OneCocycle.ext (funext fun g ↦ by simp [mul_assoc]) (funext₂ fun g k ↦ by
    simp only [gauge_defect, gauge_cochain, act_boundary_mul]
    simp only [ContinuousMap.mul_apply, smul_mul', map_mul, mul_inv_rev]
    group)

end Gauge

variable [ContinuousSMul G H] [ContinuousSMul G T] [ContinuousMul G]

/-- A twist after a gauge is a gauge after the twist, by the transported map. -/
theorem twist_gauge (z : OneCocycle G M) (v : C(G, T)) (a : H) :
    (z.gauge v).twist a = (z.twist a).gauge (M.actContinuousMap a⁻¹ v) :=
  OneCocycle.ext (funext fun g ↦ by simp only [twist_cochain, gauge_cochain,
    actContinuousMap_apply, boundary_act, inv_inv]; group) (funext₂ fun g k ↦ by
    simp only [twist_defect, gauge_defect, twist_cochain, actContinuousMap_apply,
      act_twist_smul_act]
    simp only [map_mul, map_inv])

/-- The **cohomology relation** on `1`-cocycles: `z ≈ z'` when `z'` is a twist of `z` followed by
a gauge. -/
instance setoid : Setoid (OneCocycle G M) where
  r z z' := ∃ (a : H) (v : C(G, T)), z' = (z.twist a).gauge v
  iseqv := by
    refine ⟨fun z ↦ ⟨1, 1, by simp⟩, ?_, ?_⟩
    · rintro z _ ⟨a, v, rfl⟩
      refine ⟨a⁻¹, (M.actContinuousMap a v)⁻¹, ?_⟩
      rw [twist_gauge, twist_twist, mul_inv_cancel, twist_one, gauge_gauge, inv_inv,
        inv_mul_cancel, gauge_one]
    · rintro z _ _ ⟨a, v, rfl⟩ ⟨b, w, rfl⟩
      exact ⟨a * b, w * M.actContinuousMap b⁻¹ v, by
        rw [twist_gauge, twist_twist, gauge_gauge]⟩

theorem equiv_iff {z z' : OneCocycle G M} :
    z ≈ z' ↔ ∃ (a : H) (v : C(G, T)), z' = (z.twist a).gauge v :=
  Iff.rfl

end Discrete

end OneCocycle

section H1

variable [DiscreteTopology T] [DiscreteTopology H] [ContinuousSMul G T] [ContinuousSMul G H]
  [ContinuousMul G]

variable (G) in
/-- The **degree-one cohomology** `H¹(G, T → H)` of the crossed module `M : T → H`: the
`1`-cocycles up to twists and gauges. It is a pointed set, with base point the class of the
trivial `1`-cocycle. -/
def H1 (M : CrossedModule T H) [M.IsEquivariant G] : Type _ :=
  Quotient (OneCocycle.setoid (G := G) (M := M))

namespace H1

variable {M : CrossedModule T H} [M.IsEquivariant G]

/-- The class of a `1`-cocycle in `H¹(G, T → H)`. -/
def mk (z : OneCocycle G M) : H1 G M :=
  Quotient.mk _ z

theorem mk_surjective : Function.Surjective (mk : OneCocycle G M → H1 G M) :=
  Quotient.mk_surjective

@[elab_as_elim]
theorem induction_on {motive : H1 G M → Prop} (x : H1 G M) (mk : ∀ z, motive (mk z)) :
    motive x :=
  Quotient.inductionOn x mk

/-- Two `1`-cocycles have the same class exactly when the second is a twist followed by a gauge of
the first. -/
theorem mk_eq_mk_iff {z z' : OneCocycle G M} :
    mk z = mk z' ↔ ∃ (a : H) (v : C(G, T)), z' = (z.twist a).gauge v :=
  Quotient.eq

/-- Define a function on `H¹(G, T → H)` by a function on `1`-cocycles that is constant on
cohomology classes. -/
def lift {B : Sort*} (f : OneCocycle G M → B) (hf : ∀ z z', z ≈ z' → f z = f z') : H1 G M → B :=
  Quotient.lift f hf

@[simp]
theorem lift_mk {B : Sort*} (f : OneCocycle G M → B) (hf : ∀ z z', z ≈ z' → f z = f z')
    (z : OneCocycle G M) : lift f hf (mk z) = f z :=
  (rfl)

/-- The base point of `H¹(G, T → H)`, the class of the trivial `1`-cocycle. -/
instance : One (H1 G M) :=
  ⟨mk 1⟩

instance : Inhabited (H1 G M) :=
  ⟨1⟩

theorem one_def : (1 : H1 G M) = mk 1 :=
  (rfl)

@[simp]
theorem mk_one : mk (1 : OneCocycle G M) = 1 :=
  (rfl)

/-- A twisted `1`-cocycle has the same class. -/
@[simp]
theorem mk_twist (z : OneCocycle G M) (a : H) : mk (z.twist a) = mk z :=
  (mk_eq_mk_iff.mpr ⟨a, 1, by rw [OneCocycle.gauge_one]⟩).symm

/-- A gauged `1`-cocycle has the same class. -/
@[simp]
theorem mk_gauge (z : OneCocycle G M) (v : C(G, T)) : mk (z.gauge v) = mk z :=
  (mk_eq_mk_iff.mpr ⟨1, v, by rw [OneCocycle.twist_one]⟩).symm

/-- The map `H¹(G, H) → H¹(G, T → H)` of pointed sets, `[f] ↦ [(f, 1)]`. -/
def ofH1 : NonabelianH1 G H → H1 G M :=
  NonabelianH1.lift (fun f ↦ mk (OneCocycle.ofCocycle f)) fun f f' h ↦ by
    obtain ⟨a, rfl⟩ := Cocycle.equiv_iff_exists_twist_eq.mp h
    rw [OneCocycle.ofCocycle_twist, mk_twist]

@[simp]
theorem ofH1_mk (f : Cocycle G H) :
    ofH1 (NonabelianH1.mk f) = mk (OneCocycle.ofCocycle f : OneCocycle G M) :=
  NonabelianH1.lift_mk _ _ f

@[simp]
theorem ofH1_one : ofH1 (1 : NonabelianH1 G H) = (1 : H1 G M) := by
  rw [NonabelianH1.one_def, ofH1_mk, OneCocycle.ofCocycle_one, mk_one]

omit [ContinuousSMul G H] in
/-- A cocycle of `H` whose `1`-cocycle is gauged to the trivial one by `v` is the boundary of the
cocycle `g ↦ (v g)⁻¹` of `T`. -/
private theorem exists_map_eq_of_gauge_eq_one {f : Cocycle G H} {v : C(G, T)}
    (h : (OneCocycle.ofCocycle f : OneCocycle G M).gauge v = 1) :
    ∃ w : Cocycle G T, Cocycle.map (ContinuousMonoidHom.id G) M.continuousBoundary
      M.continuousBoundary_smul w = f := by
  have hp (g : G) : f g = M.boundary (v g)⁻¹ := by
    have := congrFun (congrArg OneCocycle.cochain h) g
    rw [OneCocycle.gauge_cochain, OneCocycle.ofCocycle_cochain, OneCocycle.one_cochain] at this
    rw [map_inv, eq_inv_of_mul_eq_one_right this]
  have hv (g k : G) : v (g * k) = g • v k * v g := by
    have := congrFun₂ (congrArg OneCocycle.defect h) g k
    rw [OneCocycle.gauge_defect, OneCocycle.ofCocycle_cochain, OneCocycle.ofCocycle_defect,
      OneCocycle.one_defect, hp, act_boundary, mul_one, mul_inv_eq_one] at this
    rw [← this]
    group
  refine ⟨⟨fun g ↦ (v g)⁻¹, continuous_of_discreteTopology.comp v.continuous,
    fun g k ↦ by rw [hv, mul_inv_rev, smul_inv']⟩, Cocycle.ext fun g ↦ ?_⟩
  simp [hp]

/-- **Exactness at `H¹(G, H)`**: a class of `H¹(G, H)` maps to the base point of `H¹(G, T → H)`
exactly when it comes from `H¹(G, T)`. -/
theorem ofH1_eq_one_iff {c : NonabelianH1 G H} :
    ofH1 c = (1 : H1 G M) ↔
      c ∈ Set.range (NonabelianH1.map (ContinuousMonoidHom.id G) M.continuousBoundary
        M.continuousBoundary_smul) := by
  induction c using NonabelianH1.induction_on with | mk f =>
  rw [ofH1_mk, one_def]
  constructor
  · intro h
    obtain ⟨a, v, h⟩ := mk_eq_mk_iff.mp h
    rw [← OneCocycle.ofCocycle_twist] at h
    obtain ⟨w, hw⟩ := exists_map_eq_of_gauge_eq_one h.symm
    exact ⟨NonabelianH1.mk w, by rw [NonabelianH1.map_mk, hw, NonabelianH1.mk_twist]⟩
  · rintro ⟨c, hc⟩
    induction c using NonabelianH1.induction_on with | mk w =>
    rw [NonabelianH1.map_mk] at hc
    obtain ⟨a, ha⟩ := NonabelianH1.mk_eq_mk_iff.mp hc
    have hf : f = (Cocycle.map (ContinuousMonoidHom.id G) M.continuousBoundary
        M.continuousBoundary_smul w).twist a :=
      Cocycle.ext fun g ↦ by rw [Cocycle.twist_apply]; exact ha g
    -- The `1`-cocycle `(∂ ∘ w, 1)` is the gauge of the trivial one by `w`.
    have hw : (OneCocycle.ofCocycle (Cocycle.map (ContinuousMonoidHom.id G) M.continuousBoundary
        M.continuousBoundary_smul w) : OneCocycle G M) = (1 : OneCocycle G M).gauge
          ⟨w, w.continuous⟩ :=
      OneCocycle.ext (funext fun g ↦ by simp) (funext₂ fun g k ↦ by simp [w.apply_mul])
    rw [hf, OneCocycle.ofCocycle_twist, mk_twist, hw, mk_gauge]

/-- When the boundary is bijective, for instance for the identity crossed module `H → H`, the
pointed set `H¹(G, T → H)` is a single point. -/
theorem subsingleton_of_bijective (hM : Function.Bijective M.boundary) : Subsingleton (H1 G M) := by
  let e := Equiv.ofBijective _ hM
  suffices h : ∀ x : H1 G M, x = 1 from ⟨fun x y ↦ (h x).trans (h y).symm⟩
  intro x
  induction x using induction_on with | mk z =>
  -- Gauging by `g ↦ ∂⁻¹ (p g)⁻¹` makes the map `G → H` trivial, and then the defect is trivial.
  let v : C(G, T) := ⟨fun g ↦ e.symm (z.cochain g)⁻¹,
    (continuous_of_discreteTopology (f := fun h : H ↦ e.symm h⁻¹)).comp z.continuous_cochain⟩
  have hp (g : G) : (z.gauge v).cochain g = 1 := by
    rw [OneCocycle.gauge_cochain]
    exact mul_eq_one_iff_eq_inv.mpr (e.apply_symm_apply _)
  rw [← mk_gauge z v, ← mk_one]
  refine congrArg mk (OneCocycle.ext (funext hp) (funext₂ fun g k ↦ hM.injective ?_))
  rw [(z.gauge v).boundary_defect, hp, hp, hp]
  simp

section Subsingleton

/-- For a crossed module `1 → H` with trivial source, `H¹(G, 1 → H)` is `H¹(G, H)`. -/
noncomputable def ofH1Equiv [Subsingleton T] : NonabelianH1 G H ≃ H1 G M :=
  Equiv.ofBijective ofH1 <| by
    refine ⟨fun c c' hcc' ↦ ?_, fun x ↦ ?_⟩
    · induction c using NonabelianH1.induction_on with | mk f =>
      induction c' using NonabelianH1.induction_on with | mk f' =>
      rw [ofH1_mk, ofH1_mk] at hcc'
      obtain ⟨a, v, h⟩ := mk_eq_mk_iff.mp hcc'
      rw [Subsingleton.elim v 1, OneCocycle.gauge_one, ← OneCocycle.ofCocycle_twist] at h
      rw [OneCocycle.ofCocycle_injective h, NonabelianH1.mk_twist]
    · induction x using induction_on with | mk z =>
      have hz (g k : G) : z.defect g k = 1 := Subsingleton.elim _ _
      refine ⟨NonabelianH1.mk ⟨z.cochain, z.continuous_cochain, fun g k ↦ ?_⟩,
        (ofH1_mk _).trans (congrArg mk (OneCocycle.ext rfl (funext₂ fun g k ↦ (hz g k).symm)))⟩
      have := z.boundary_defect_mul g k
      rwa [hz, _root_.map_one, one_mul] at this

@[simp]
theorem ofH1Equiv_apply [Subsingleton T] (c : NonabelianH1 G H) :
    (ofH1Equiv c : H1 G M) = ofH1 c :=
  (rfl)

end Subsingleton

end H1

end H1

end CrossedModule

end TauCeti
