/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.MinimalAxioms
public import TauCeti.Algebra.Group.CrossedModule.Equivariant
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.ExactSequence

/-!
# Degree-zero continuous cohomology of a crossed module

Let a topological group `G` act on a crossed module `∂ : T → H` of groups, compatibly with its
structure (`TauCeti.CrossedModule.IsEquivariant`), with `T` discrete. A **`0`-cocycle** is a pair
`(h, u)` of an element `h : H` and a continuous `1`-cocycle `u : G → T` with

`∂ (u g) = h⁻¹ * g • h`.

The `0`-cocycles form a group under `(h, u) * (h', u') = (h * h', g ↦ h'⁻¹ • u g * u' g)`, and the
map `t ↦ (∂ t, g ↦ t⁻¹ * g • t)` is a homomorphism from `T` onto a normal subgroup, the
`0`-coboundaries. The quotient is the group `H⁰(G, T → H)`. Viewing the crossed module as a
two-term complex with `T` in degree `-1`, this is the degree-zero cohomology of the complex: it is
`Hᴳ` when `T` is trivial, `Qᴳ` when `1 → T → H → Q → 1` is a short exact sequence of topological
`G`-groups (`TauCeti.NonabelianH1.IsGroupExtension`, with `H` a topological group on which `G`
acts continuously, so that fixed points of `Q` lift to continuous cocycles), and `H¹(G, T)` when
`H` is trivial (so it is not the invariants of the cokernel in general).

With the map `Hᴳ → H⁰(G, T → H)`, `h ↦ (h, 1)`, and the map `H⁰(G, T → H) → H¹(G, T)`,
`(h, u) ↦ [u]`, the sequence

`Tᴳ → Hᴳ → H⁰(G, T → H) → H¹(G, T) → H¹(G, H)`

is exact, and the fibres of `H⁰(G, T → H) → H¹(G, T)` are the orbits of `Hᴳ` acting by left
multiplication.

## Main definitions

* `TauCeti.CrossedModule.ZeroCocycle G M`: the group of `0`-cocycles of `G` with values in the
  crossed module `M`.
* `TauCeti.CrossedModule.ZeroCocycle.coboundary`: the homomorphism `T →* ZeroCocycle G M` whose
  range is the normal subgroup of `0`-coboundaries.
* `TauCeti.CrossedModule.H0 G M`: the group `H⁰(G, T → H)`, with `TauCeti.CrossedModule.H0.mk`
  the class of a `0`-cocycle.
* `TauCeti.CrossedModule.H0.lift` and `TauCeti.CrossedModule.H0.liftHom`: functions and
  homomorphisms out of `H⁰(G, T → H)`, descended from `0`-cocycles along the coboundaries.
* `TauCeti.CrossedModule.H0.ofFixedPoints`: the homomorphism `Hᴳ →* H⁰(G, T → H)`.
* `TauCeti.CrossedModule.H0.toH1`: the map `H⁰(G, T → H) → H¹(G, T)` of pointed sets.
* `TauCeti.CrossedModule.H0.fixedPointsMulEquiv`: `H⁰(G, T → H) ≃* Hᴳ` for trivial `T`.
* `TauCeti.CrossedModule.H0.toH1Equiv`: `H⁰(G, T → H) ≃ H¹(G, T)` for trivial `H`.
* `TauCeti.CrossedModule.H0.mulEquivOfIsGroupExtension`: `H⁰(G, T → H) ≃* Qᴳ` when
  `1 → T → H → Q → 1` is a short exact sequence of `G`-groups.

## Main results

* `TauCeti.CrossedModule.H0.mk_eq_mk_iff`: two `0`-cocycles have the same class exactly when they
  differ by the boundary and the twist of one `t : T`.
* `TauCeti.CrossedModule.H0.ofFixedPoints_eq_one_iff`: exactness at `Hᴳ`.
* `TauCeti.CrossedModule.H0.toH1_eq_toH1_iff`: the fibres of `H⁰(G, T → H) → H¹(G, T)` are the
  `Hᴳ`-orbits; in particular `TauCeti.CrossedModule.H0.toH1_eq_one_iff` gives exactness at
  `H⁰(G, T → H)`.
* `TauCeti.CrossedModule.H0.mem_range_toH1_iff`: exactness at `H¹(G, T)`.

## Implementation notes

Galois cohomology with coefficients in a crossed module uses discrete groups, such as the points
over an algebraic closure of a crossed module of algebraic groups. We take `T` discrete, so that
continuity of `0`-cocycles is local constancy and is preserved by the action of `H`. The group `H`
needs no topology for the definition of `H⁰(G, T → H)`.

## References

* J.-P. Labesse, *Cohomologie, stabilisation et changement de base*, Astérisque 257 (1999),
  §1.1–1.2 (Définition 1.1.1, Lemme 1.2.1).
* M. Borovoi, *Abelian Galois cohomology of reductive groups*, Mem. Amer. Math. Soc. 626 (1998),
  §3.
* M. Kisin, *Mod p points on Shimura varieties of abelian type*, J. Amer. Math. Soc. 30 (2017),
  §3.2.7.
-/

public section

open Topology

namespace TauCeti

open NonabelianH1

namespace CrossedModule

variable {G T H : Type*} [Group G] [TopologicalSpace G] [Group T] [TopologicalSpace T] [Group H]
  [MulDistribMulAction G T] [MulDistribMulAction G H]

variable (G) in
/-- A **`0`-cocycle** of `G` with values in the crossed module `M : T → H`: an element `h : H` and
a continuous `1`-cocycle `u : G → T` with `∂ (u g) = h⁻¹ * g • h`. -/
@[ext]
structure ZeroCocycle (M : CrossedModule T H) where
  /-- The element of `H` of a `0`-cocycle. -/
  elem : H
  /-- The `1`-cocycle of `T` of a `0`-cocycle. -/
  cocycle : Cocycle G T
  /-- The boundary of the `1`-cocycle is the coboundary of the element. -/
  boundary_cocycle (g : G) : M.boundary (cocycle g) = elem⁻¹ * g • elem

namespace ZeroCocycle

variable {M : CrossedModule T H}

/-- The action of `g` on the element of a `0`-cocycle `(h, u)` is `h * ∂ (u g)`. -/
theorem smul_elem (z : ZeroCocycle G M) (g : G) :
    g • z.elem = z.elem * M.boundary (z.cocycle g) := by
  rw [z.boundary_cocycle, mul_inv_cancel_left]

/-- The identity `0`-cocycle `(1, 1)`. -/
instance : One (ZeroCocycle G M) where
  one := ⟨1, 1, fun g ↦ by simp⟩

@[simp]
theorem one_elem : (1 : ZeroCocycle G M).elem = 1 :=
  (rfl)

@[simp]
theorem one_cocycle : (1 : ZeroCocycle G M).cocycle = 1 :=
  (rfl)

section Group

variable [M.IsEquivariant G]

/-- The cocycle identity of the cocycle `g ↦ h'⁻¹ • u g * u' g` of the product of two
`0`-cocycles `(h, u)` and `(h', u')`. -/
private theorem mulCocycle_apply_mul (z z' : ZeroCocycle G M) (g k : G) :
    M.act z'.elem⁻¹ (z.cocycle (g * k)) * z'.cocycle (g * k) =
      M.act z'.elem⁻¹ (z.cocycle g) * z'.cocycle g *
        g • (M.act z'.elem⁻¹ (z.cocycle k) * z'.cocycle k) := by
  have h : g • z'.elem⁻¹ = M.boundary (z'.cocycle g)⁻¹ * z'.elem⁻¹ := by
    rw [smul_inv', smul_elem, map_inv, mul_inv_rev]
  rw [Cocycle.apply_mul, Cocycle.apply_mul, map_mul, smul_mul', IsEquivariant.smul_act, h,
    act_boundary_mul]
  group

/-- The cocycle identity of the cocycle `g ↦ h • (u g)⁻¹` of the inverse of a `0`-cocycle
`(h, u)`. -/
private theorem invCocycle_apply_mul (z : ZeroCocycle G M) (g k : G) :
    M.act z.elem (z.cocycle (g * k))⁻¹ =
      M.act z.elem (z.cocycle g)⁻¹ * g • M.act z.elem (z.cocycle k)⁻¹ := by
  rw [IsEquivariant.smul_act, smul_elem, act_mul_boundary, ← map_mul, Cocycle.apply_mul,
    smul_inv']
  group

variable [DiscreteTopology T]

/-- The product `(h, u) * (h', u') = (h * h', g ↦ h'⁻¹ • u g * u' g)` of `0`-cocycles. -/
instance : Mul (ZeroCocycle G M) where
  mul z z' :=
    { elem := z.elem * z'.elem
      cocycle :=
        { toFun g := M.act z'.elem⁻¹ (z.cocycle g) * z'.cocycle g
          continuous_toFun := continuous_of_discreteTopology.comp z.cocycle.continuous |>.mul
            z'.cocycle.continuous
          map_mul' := by exact mulCocycle_apply_mul z z' }
      boundary_cocycle g := by
        simp only [Cocycle.coe_mk, map_mul, boundary_act, boundary_cocycle, smul_mul']
        group }

@[simp]
theorem mul_elem (z z' : ZeroCocycle G M) : (z * z').elem = z.elem * z'.elem :=
  (rfl)

@[simp]
theorem mul_cocycle_apply (z z' : ZeroCocycle G M) (g : G) :
    (z * z').cocycle g = M.act z'.elem⁻¹ (z.cocycle g) * z'.cocycle g :=
  (rfl)

/-- The inverse `(h, u)⁻¹ = (h⁻¹, g ↦ h • (u g)⁻¹)` of a `0`-cocycle. -/
instance : Inv (ZeroCocycle G M) where
  inv z :=
    { elem := z.elem⁻¹
      cocycle :=
        { toFun g := M.act z.elem (z.cocycle g)⁻¹
          continuous_toFun :=
            (continuous_of_discreteTopology (f := fun t ↦ M.act z.elem t⁻¹)).comp
              z.cocycle.continuous
          map_mul' := by exact invCocycle_apply_mul z }
      boundary_cocycle g := by
        simp only [Cocycle.coe_mk, boundary_act, map_inv, boundary_cocycle, smul_inv']
        group }

@[simp]
theorem inv_elem (z : ZeroCocycle G M) : z⁻¹.elem = z.elem⁻¹ :=
  (rfl)

@[simp]
theorem inv_cocycle_apply (z : ZeroCocycle G M) (g : G) :
    z⁻¹.cocycle g = M.act z.elem (z.cocycle g)⁻¹ :=
  (rfl)

/-- The `0`-cocycles of a crossed module form a group. -/
instance : Group (ZeroCocycle G M) :=
  Group.ofLeftAxioms
    (fun _ _ _ ↦ ZeroCocycle.ext (mul_assoc _ _ _) <| Cocycle.ext fun _ ↦ by
      simp [MulAut.mul_apply, mul_assoc])
    (fun _ ↦ ZeroCocycle.ext (one_mul _) <| Cocycle.ext fun _ ↦ by simp)
    (fun _ ↦ ZeroCocycle.ext (inv_mul_cancel _) <| Cocycle.ext fun _ ↦ by
      simp [MulAut.inv_apply])

variable (G M) in
/-- The `0`-cocycle `(h, 1)` of an element `h` of `H` fixed by `G`, as a homomorphism
`Hᴳ →* ZeroCocycle G M`. -/
def ofFixedPoints : FixedPoints.subgroup G H →* ZeroCocycle G M where
  toFun h := ⟨h, 1, fun g ↦ by simp [(FixedPoints.mem_subgroup G H h).mp h.prop g]⟩
  map_one' := rfl
  map_mul' _ _ := ZeroCocycle.ext rfl <| Cocycle.ext fun _ ↦ by simp

@[simp]
theorem ofFixedPoints_elem (h : FixedPoints.subgroup G H) : (ofFixedPoints G M h).elem = h :=
  (rfl)

@[simp]
theorem ofFixedPoints_cocycle (h : FixedPoints.subgroup G H) :
    (ofFixedPoints G M h).cocycle = 1 :=
  (rfl)

/-- Left multiplication by the `0`-cocycle of a fixed point does not change the `1`-cocycle. -/
@[simp]
theorem ofFixedPoints_mul_cocycle (h : FixedPoints.subgroup G H) (z : ZeroCocycle G M) :
    (ofFixedPoints G M h * z).cocycle = z.cocycle :=
  Cocycle.ext fun g ↦ by simp

section Coboundary

variable [ContinuousSMul G T]

variable (G M) in
/-- The **`0`-coboundary** map `T →* ZeroCocycle G M`, `t ↦ (∂ t, g ↦ t⁻¹ * g • t)`. Its range is
a normal subgroup, the `0`-coboundaries. -/
def coboundary : T →* ZeroCocycle G M where
  toFun t := ⟨M.boundary t, (1 : Cocycle G T).twist t, fun g ↦ by simp⟩
  map_one' := ZeroCocycle.ext (map_one _) (Cocycle.ext fun g ↦ by simp)
  map_mul' s t := ZeroCocycle.ext (map_mul _ _ _) <| Cocycle.ext fun g ↦ by
    simp [← map_inv, act_boundary, smul_mul', mul_assoc]

@[simp]
theorem coboundary_elem (t : T) : (coboundary G M t).elem = M.boundary t :=
  (rfl)

@[simp]
theorem coboundary_cocycle (t : T) : (coboundary G M t).cocycle = (1 : Cocycle G T).twist t :=
  (rfl)

/-- Multiplying a `0`-cocycle `(h, u)` on the right by the coboundary of `t` gives
`(h * ∂ t, u.twist t)`. -/
@[simp]
theorem mul_coboundary_cocycle (z : ZeroCocycle G M) (t : T) :
    (z * coboundary G M t).cocycle = z.cocycle.twist t :=
  Cocycle.ext fun g ↦ by simp [← map_inv, act_boundary, mul_assoc]

/-- Coboundaries are normalized by `0`-cocycles: `z * δ t = δ (h • t) * z` for `z = (h, u)`. -/
theorem mul_coboundary (z : ZeroCocycle G M) (t : T) :
    z * coboundary G M t = coboundary G M (M.act z.elem t) * z := by
  have hinv (y : T) : M.act z.elem⁻¹ (M.act z.elem y) = y := by
    rw [map_inv, MulAut.inv_apply_self]
  have hsmul (g : G) :
      M.act z.elem⁻¹ (g • M.act z.elem t) = z.cocycle g * g • t * (z.cocycle g)⁻¹ := by
    rw [IsEquivariant.smul_act, smul_elem, act_mul_boundary, hinv]
  refine ZeroCocycle.ext (by simp) (Cocycle.ext fun g ↦ ?_)
  rw [mul_coboundary_cocycle, mul_cocycle_apply, coboundary_cocycle, Cocycle.twist_apply,
    Cocycle.twist_apply, Cocycle.one_apply, mul_one, map_mul, hsmul, map_inv, hinv]
  group

instance normal_range_coboundary : (coboundary G M).range.Normal where
  conj_mem := by
    rintro _ ⟨t, rfl⟩ z
    exact ⟨M.act z.elem t, by rw [mul_coboundary, mul_inv_cancel_right]⟩

end Coboundary

end Group

end ZeroCocycle

section ContinuousBoundary

variable [DiscreteTopology T] [TopologicalSpace H] (M : CrossedModule T H)

/-- The boundary of a crossed module with discrete source, as a continuous homomorphism. -/
def continuousBoundary : T →ₜ* H :=
  { M.boundary with continuous_toFun := continuous_of_discreteTopology }

@[simp]
theorem continuousBoundary_apply (t : T) : M.continuousBoundary t = M.boundary t :=
  (rfl)

/-- The equivariance of the boundary, stated as the compatibility of the pair
`(ContinuousMonoidHom.id G, M.continuousBoundary)` taken by `TauCeti.NonabelianH1.map`. -/
theorem continuousBoundary_smul [M.IsEquivariant G] (g : G) (t : T) :
    M.continuousBoundary (ContinuousMonoidHom.id G g • t) = g • M.continuousBoundary t :=
  IsEquivariant.boundary_smul g t

end ContinuousBoundary

section H0

variable [DiscreteTopology T] [ContinuousSMul G T]

variable (G) in
/-- The **degree-zero cohomology** `H⁰(G, T → H)` of the crossed module `M : T → H`: the group of
`0`-cocycles modulo the normal subgroup of `0`-coboundaries. -/
def H0 (M : CrossedModule T H) [M.IsEquivariant G] : Type _ :=
  ZeroCocycle G M ⧸ (ZeroCocycle.coboundary G M).range

namespace H0

variable {M : CrossedModule T H}

section Equivariant

variable [M.IsEquivariant G]

instance : Group (H0 G M) :=
  inferInstanceAs (Group (ZeroCocycle G M ⧸ (ZeroCocycle.coboundary G M).range))

/-- The class of a `0`-cocycle in `H⁰(G, T → H)`. -/
def mk : ZeroCocycle G M →* H0 G M :=
  QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk : ZeroCocycle G M →* H0 G M) :=
  QuotientGroup.mk'_surjective _

@[elab_as_elim]
theorem induction_on {motive : H0 G M → Prop} (x : H0 G M) (mk : ∀ z, motive (mk z)) :
    motive x :=
  QuotientGroup.induction_on x mk

/-- Define a function on `H⁰(G, T → H)` by a function on `0`-cocycles that is invariant under
right multiplication by coboundaries. -/
def lift {B : Sort*} (f : ZeroCocycle G M → B)
    (hf : ∀ z t, f (z * ZeroCocycle.coboundary G M t) = f z) : H0 G M → B :=
  Quotient.lift f fun z _ h ↦ by
    obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := (QuotientGroup.mk'_eq_mk' _).mp (Quotient.sound h)
    exact (hf z t).symm

@[simp]
theorem lift_mk {B : Sort*} (f : ZeroCocycle G M → B)
    (hf : ∀ z t, f (z * ZeroCocycle.coboundary G M t) = f z) (z : ZeroCocycle G M) :
    lift f hf (mk z) = f z :=
  (rfl)

/-- A function on `H⁰(G, T → H)` is determined by its values on classes of `0`-cocycles. -/
theorem lift_unique {B : Sort*} (f : ZeroCocycle G M → B)
    (hf : ∀ z t, f (z * ZeroCocycle.coboundary G M t) = f z) (F : H0 G M → B)
    (hF : ∀ z, F (mk z) = f z) : F = lift f hf :=
  funext fun x ↦ by induction x using induction_on with | mk z => exact hF z

/-- The homomorphism `H⁰(G, T → H) →* K` induced by a homomorphism on `0`-cocycles that kills the
coboundaries. -/
def liftHom {K : Type*} [Monoid K] (φ : ZeroCocycle G M →* K)
    (hφ : ∀ t, φ (ZeroCocycle.coboundary G M t) = 1) : H0 G M →* K :=
  QuotientGroup.lift _ φ (by rintro _ ⟨t, rfl⟩; exact hφ t)

@[simp]
theorem liftHom_mk {K : Type*} [Monoid K] (φ : ZeroCocycle G M →* K)
    (hφ : ∀ t, φ (ZeroCocycle.coboundary G M t) = 1) (z : ZeroCocycle G M) :
    liftHom φ hφ (mk z) = φ z :=
  (rfl)

/-- Two homomorphisms out of `H⁰(G, T → H)` agreeing on classes of `0`-cocycles are equal. -/
@[ext]
theorem hom_ext {K : Type*} [Monoid K] ⦃φ ψ : H0 G M →* K⦄ (h : φ.comp mk = ψ.comp mk) :
    φ = ψ :=
  QuotientGroup.monoidHom_ext _ h

/-- Two `0`-cocycles have the same class exactly when they differ by one `t : T`: the second is
`(h * ∂ t, u.twist t)` for the first `(h, u)`. -/
theorem mk_eq_mk_iff {z z' : ZeroCocycle G M} :
    mk z = mk z' ↔ ∃ t : T, z'.elem = z.elem * M.boundary t ∧ z'.cocycle = z.cocycle.twist t := by
  refine (QuotientGroup.mk'_eq_mk' _).trans ⟨?_, ?_⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl, ZeroCocycle.mul_coboundary_cocycle z t⟩
  · rintro ⟨t, he, hc⟩
    refine ⟨_, ⟨t, rfl⟩, ZeroCocycle.ext (by simp [he]) ?_⟩
    rw [ZeroCocycle.mul_coboundary_cocycle, hc]

/-- The class of a `0`-cocycle is trivial exactly when it is the coboundary
`(∂ t, g ↦ t⁻¹ * g • t)` of one `t : T`. -/
theorem mk_eq_one_iff {z : ZeroCocycle G M} :
    mk z = 1 ↔ ∃ t : T, z.elem = M.boundary t ∧ z.cocycle = (1 : Cocycle G T).twist t := by
  rw [← _root_.map_one mk, eq_comm, mk_eq_mk_iff]
  simp only [ZeroCocycle.one_elem, one_mul, ZeroCocycle.one_cocycle]

variable (G M) in
/-- The homomorphism `Hᴳ →* H⁰(G, T → H)`, `h ↦ [(h, 1)]`. -/
def ofFixedPoints : FixedPoints.subgroup G H →* H0 G M :=
  mk.comp (ZeroCocycle.ofFixedPoints G M)

theorem ofFixedPoints_apply (h : FixedPoints.subgroup G H) :
    ofFixedPoints G M h = mk (ZeroCocycle.ofFixedPoints G M h) :=
  (rfl)

/-- **Exactness at `Hᴳ`**: a fixed point of `H` has trivial class in `H⁰(G, T → H)` exactly when
it is the boundary of a fixed point of `T`. -/
theorem ofFixedPoints_eq_one_iff {h : FixedPoints.subgroup G H} :
    ofFixedPoints G M h = 1 ↔ ∃ t ∈ FixedPoints.subgroup G T, M.boundary t = h := by
  rw [ofFixedPoints_apply, mk_eq_one_iff, ZeroCocycle.ofFixedPoints_elem,
    ZeroCocycle.ofFixedPoints_cocycle]
  constructor
  · rintro ⟨t, ht, hc⟩
    refine ⟨t, (FixedPoints.mem_subgroup G T t).mpr fun g ↦ ?_, ht.symm⟩
    have hg := DFunLike.congr_fun hc g
    rw [Cocycle.twist_apply, Cocycle.one_apply, mul_one, eq_comm, inv_mul_eq_one] at hg
    exact hg.symm
  · rintro ⟨t, ht, hth⟩
    exact ⟨t, hth.symm, Cocycle.ext fun g ↦ by simp [(FixedPoints.mem_subgroup G T t).mp ht g]⟩

/-- The map `H⁰(G, T → H) → H¹(G, T)` of pointed sets, `[(h, u)] ↦ [u]`. -/
def toH1 : H0 G M → NonabelianH1 G T :=
  lift (fun z ↦ NonabelianH1.mk z.cocycle) fun z t ↦ by
    rw [ZeroCocycle.mul_coboundary_cocycle, NonabelianH1.mk_twist]

@[simp]
theorem toH1_mk (z : ZeroCocycle G M) : toH1 (mk z) = NonabelianH1.mk z.cocycle :=
  (rfl)

@[simp]
theorem toH1_one : toH1 (1 : H0 G M) = 1 := by
  rw [← _root_.map_one mk, toH1_mk, ZeroCocycle.one_cocycle, NonabelianH1.mk_one]

/-- Left multiplication by the class of a fixed point of `H` does not change the image in
`H¹(G, T)`. -/
@[simp]
theorem toH1_ofFixedPoints_mul (h : FixedPoints.subgroup G H) (x : H0 G M) :
    toH1 (ofFixedPoints G M h * x) = toH1 x := by
  induction x using induction_on with | mk z =>
  rw [ofFixedPoints_apply, ← map_mul, toH1_mk, toH1_mk, ZeroCocycle.ofFixedPoints_mul_cocycle]

/-- The fibres of `H⁰(G, T → H) → H¹(G, T)` are the orbits of `Hᴳ` acting by left
multiplication. -/
theorem toH1_eq_toH1_iff {x y : H0 G M} :
    toH1 x = toH1 y ↔ ∃ h : FixedPoints.subgroup G H, ofFixedPoints G M h * x = y := by
  refine ⟨fun hxy ↦ ?_, fun ⟨h, hy⟩ ↦ hy ▸ (toH1_ofFixedPoints_mul h x).symm⟩
  induction x using induction_on with | mk z =>
  induction y using induction_on with | mk z' =>
  obtain ⟨a, ha⟩ := NonabelianH1.mk_eq_mk_iff.mp hxy
  -- The element `k = h' * (∂ a)⁻¹ * h⁻¹` is fixed by `G`, and `(k, 1) * (h, u) ~ (h', u')`.
  have hk (g : G) : g • (z'.elem * (M.boundary a)⁻¹ * z.elem⁻¹) =
      z'.elem * (M.boundary a)⁻¹ * z.elem⁻¹ := by
    simp only [smul_mul', smul_inv', ZeroCocycle.smul_elem, ← IsEquivariant.boundary_smul, ha g,
      map_mul, map_inv]
    group
  refine ⟨⟨_, (FixedPoints.mem_subgroup _ _ _).mpr hk⟩, ?_⟩
  rw [ofFixedPoints_apply, ← map_mul, mk_eq_mk_iff]
  refine ⟨a, by simp, ?_⟩
  rw [ZeroCocycle.ofFixedPoints_mul_cocycle]
  exact Cocycle.ext fun g ↦ by rw [ha g, Cocycle.twist_apply]

/-- **Exactness at `H⁰(G, T → H)`**: a class maps to the base point of `H¹(G, T)` exactly when it
comes from `Hᴳ`. -/
theorem toH1_eq_one_iff {x : H0 G M} : toH1 x = 1 ↔ x ∈ (ofFixedPoints G M).range := by
  rw [← toH1_one (G := G) (M := M), eq_comm, toH1_eq_toH1_iff]
  simp [MonoidHom.mem_range]

/-- **Exactness at `H¹(G, T)`**: a class of `H¹(G, T)` comes from `H⁰(G, T → H)` exactly when its
image in `H¹(G, H)` is the base point. -/
theorem mem_range_toH1_iff [TopologicalSpace H] {c : NonabelianH1 G T} :
    c ∈ Set.range (toH1 (G := G) (M := M)) ↔
      NonabelianH1.map (ContinuousMonoidHom.id G) M.continuousBoundary
        M.continuousBoundary_smul c = 1 := by
  induction c using NonabelianH1.induction_on with | mk u =>
  rw [NonabelianH1.map_mk, NonabelianH1.mk_eq_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    induction x using induction_on with | mk z =>
    obtain ⟨a, ha⟩ := NonabelianH1.mk_eq_mk_iff.mp hx
    have hu : u = (z * ZeroCocycle.coboundary G M a).cocycle := by
      rw [ZeroCocycle.mul_coboundary_cocycle]
      exact Cocycle.ext fun g ↦ by rw [ha g, Cocycle.twist_apply]
    exact ⟨_, fun g ↦ by rw [Cocycle.map_apply, hu]; exact (z * _).boundary_cocycle g⟩
  · rintro ⟨h, hh⟩
    exact ⟨mk ⟨h, u, fun g ↦ by simpa using hh g⟩, rfl⟩

end Equivariant

section Subsingleton

/-- For a crossed module `1 → H` with trivial source, `H⁰(G, 1 → H)` is the group `Hᴳ`. -/
noncomputable def fixedPointsMulEquiv [Subsingleton T] : FixedPoints.subgroup G H ≃* H0 G M :=
  MulEquiv.ofBijective (ofFixedPoints G M) <| by
    refine ⟨(injective_iff_map_eq_one _).mpr fun h hh ↦ ?_, fun x ↦ ?_⟩
    · obtain ⟨t, -, ht⟩ := ofFixedPoints_eq_one_iff.mp hh
      rw [Subsingleton.elim t 1, _root_.map_one] at ht
      exact Subtype.ext ht.symm
    · induction x using induction_on with | mk z =>
      have hz (g : G) : z.cocycle g = 1 := Subsingleton.elim _ _
      refine ⟨⟨z.elem, (FixedPoints.mem_subgroup _ _ _).mpr fun g ↦ ?_⟩, ?_⟩
      · rw [ZeroCocycle.smul_elem, hz, _root_.map_one, mul_one]
      · exact congrArg mk (ZeroCocycle.ext rfl (Cocycle.ext fun g ↦ (hz g).symm))

@[simp]
theorem fixedPointsMulEquiv_apply [Subsingleton T] (h : FixedPoints.subgroup G H) :
    fixedPointsMulEquiv h = ofFixedPoints G M h :=
  (rfl)

/-- For a crossed module `T → 1` with trivial target, `H⁰(G, T → 1)` is `H¹(G, T)`. In particular
the degree-zero cohomology of a crossed module is not in general the group of invariants of the
cokernel of its boundary. -/
noncomputable def toH1Equiv [Subsingleton H] : H0 G M ≃ NonabelianH1 G T :=
  Equiv.ofBijective toH1 <| by
    refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨h, rfl⟩ := toH1_eq_toH1_iff.mp hxy
      rw [Subsingleton.elim h 1, _root_.map_one, one_mul]
    · induction c using NonabelianH1.induction_on with | mk u =>
      exact ⟨mk ⟨1, u, fun _ ↦ Subsingleton.elim _ _⟩, rfl⟩

@[simp]
theorem toH1Equiv_apply [Subsingleton H] (x : H0 G M) : toH1Equiv x = toH1 x :=
  (rfl)

end Subsingleton

section Extension

variable [M.IsEquivariant G] {Q : Type*} [Group Q] [MulDistribMulAction G Q]

/-- The homomorphism `H⁰(G, T → H) →* Qᴳ`, `[(h, u)] ↦ p h`, for a `G`-equivariant homomorphism
`p : H →* Q` that kills the boundary. -/
def toFixedPoints (p : H →* Q) (hp : ∀ (g : G) (h : H), p (g • h) = g • p h)
    (hpb : ∀ t, p (M.boundary t) = 1) : H0 G M →* FixedPoints.subgroup G Q :=
  liftHom
    { toFun z := ⟨p z.elem, (FixedPoints.mem_subgroup _ _ _).mpr fun g ↦ by
        rw [← hp, z.smul_elem, map_mul, hpb, mul_one]⟩
      map_one' := Subtype.ext (_root_.map_one p)
      map_mul' _ _ := Subtype.ext (map_mul p _ _) }
    fun t ↦ Subtype.ext (hpb t)

@[simp]
theorem coe_toFixedPoints_mk (p : H →* Q) (hp : ∀ (g : G) (h : H), p (g • h) = g • p h)
    (hpb : ∀ t, p (M.boundary t) = 1) (z : ZeroCocycle G M) :
    (toFixedPoints p hp hpb (mk z) : Q) = p z.elem :=
  (rfl)

variable [TopologicalSpace H] [ContinuousMul H] [ContinuousSMul G H] [TopologicalSpace Q]
  {p : H →ₜ* Q}

/-- When `1 → T → H → Q → 1` is a short exact sequence of `G`-groups, the map
`H⁰(G, T → H) → Qᴳ` is bijective. -/
theorem toFixedPoints_bijective (hE : IsGroupExtension G M.continuousBoundary p) :
    Function.Bijective (toFixedPoints (G := G) (M := M) p.toMonoidHom hE.map_smul_right
      fun t ↦ by simpa using hE.mulExact.apply_apply_eq_one t) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun x hx ↦ ?_, fun ⟨q, hq⟩ ↦ ?_⟩
  · induction x using induction_on with | mk z =>
    obtain ⟨t, ht⟩ := (hE.mulExact z.elem).mp (congrArg Subtype.val hx)
    rw [continuousBoundary_apply] at ht
    refine mk_eq_one_iff.mpr ⟨t, ht.symm, Cocycle.ext fun g ↦ hE.isEmbedding.injective ?_⟩
    simp [z.boundary_cocycle, ← ht]
  · obtain ⟨h, rfl⟩ := hE.surjective q
    -- The values `h⁻¹ * g • h` lie in the kernel of `p`, so they lift to a cocycle of `T`.
    have hmem (g : G) : (1 : Cocycle G H).twist h g ∈ Set.range M.continuousBoundary :=
      (hE.mulExact _).mp <| by simp [hE.map_smul_right, (FixedPoints.mem_subgroup _ _ _).mp hq g]
    refine ⟨mk ⟨h, ((1 : Cocycle G H).twist h).liftOfMemRange M.continuousBoundary
      hE.isEmbedding hE.compatible_left hmem, fun g ↦ ?_⟩, rfl⟩
    simpa only [continuousBoundary_apply, Cocycle.twist_apply, Cocycle.one_apply, mul_one] using
      Cocycle.apply_liftOfMemRange _ hE.isEmbedding hE.compatible_left _ hmem g

/-- When `1 → T → H → Q → 1` is a short exact sequence of `G`-groups, `H⁰(G, T → H)` is the group
`Qᴳ` of invariants of the cokernel. -/
noncomputable def mulEquivOfIsGroupExtension (hE : IsGroupExtension G M.continuousBoundary p) :
    H0 G M ≃* FixedPoints.subgroup G Q :=
  MulEquiv.ofBijective _ (toFixedPoints_bijective hE)

@[simp]
theorem coe_mulEquivOfIsGroupExtension_mk (hE : IsGroupExtension G M.continuousBoundary p)
    (z : ZeroCocycle G M) : (mulEquivOfIsGroupExtension hE (mk z) : Q) = p z.elem :=
  (rfl)

end Extension

end H0

end H0

end CrossedModule

end TauCeti
