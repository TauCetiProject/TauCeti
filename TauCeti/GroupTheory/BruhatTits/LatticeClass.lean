/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.Algebra.Module.Submodule.Pointwise

/-!
# Homothety classes of lattices and their adjacency graph

Let `K` be a field which is an algebra over a commutative ring `O`, and let `V` be a `K`-vector
space. A *full lattice* in `V` is an `O`-submodule which is a lattice spanning `V` over `K`
(`Submodule.IsFullLattice`). A nonzero scalar `a ∈ Kˣ` moves full lattices to full lattices, and
two full lattices are *homothetic* when one is a scalar multiple of the other. The homothety
classes of full lattices form the type `TauCeti.LatticeClass O K V`, the orbit space of `Kˣ`
acting on the full lattices `TauCeti.fullLattices O K V`.

A `K`-linear automorphism `g` of `V` moves full lattices to full lattices and commutes with
homotheties, so the group `V ≃ₗ[K] V` acts on lattice classes by `g [L] = [g L]`. A scalar
automorphism fixes every class, so this action factors through the projective linear group.

Now let `O` be a discrete valuation ring with fraction field `K` and maximal ideal `𝔪`. Two classes
are *adjacent* when they have representatives `L` and `M` with `𝔪 L ⊊ M ⊊ L`; for a uniformizer
`ϖ` the pair `M`, `ϖ L` then exhibits the reverse adjacency. No class is adjacent to itself,
since every nonzero scalar of `K` is a unit of `O` times a power of `ϖ`. Adjacency is therefore a
simple graph `TauCeti.LatticeClass.graph O K V` on the lattice classes, and linear automorphisms of
`V` act on it by graph automorphisms (`TauCeti.LatticeClass.toGraphIso`). The neighbours of the
class of `L` correspond to the submodules strictly between `𝔪 L` and `L`, each neighbour having
exactly one representative between them (`TauCeti.LatticeClass.neighborEquiv`).

For `V = K²` this is the graph on which Serre builds the tree of `SL₂(K)`; Serre proves that it is
a tree, regular of degree `q + 1` when the residue field has `q` elements (*Trees*, Chapter II,
§1.1). For a general finite-dimensional `V` it is the one-skeleton of the Bruhat–Tits building of
`PGL(V)`.

## Main definitions

* `TauCeti.fullLattices O K V`: the full `O`-lattices in `V`, a `Kˣ`-stable set of submodules.
* `TauCeti.LatticeClass O K V`: the homothety classes of full lattices.
* `TauCeti.LatticeClass.mk`: the class of a full lattice.
* `TauCeti.LatticeClass.graph O K V`: the adjacency graph of lattice classes over a discrete
  valuation ring.
* `TauCeti.LatticeClass.toGraphIso`: the action of `V ≃ₗ[K] V` by graph automorphisms.
* `TauCeti.LatticeClass.neighborEquiv`: the neighbours of the class of `L` are the submodules
  strictly between `𝔪 L` and `L`.

## Main results

* `TauCeti.LatticeClass.mk_eq_mk_iff`: two full lattices have the same class exactly when they
  are homothetic.
* `TauCeti.LatticeClass.smul_mk`: a linear automorphism acts on classes through representatives.
* `TauCeti.LatticeClass.smulOfUnit_smul`: scalar automorphisms act trivially.
* `TauCeti.LatticeClass.graph_adj_mk_iff`: adjacency of two classes, read on a fixed
  representative of the first one.
* `TauCeti.LatticeClass.graph_adj_smul_iff`: linear automorphisms preserve adjacency.

## References

* J.-P. Serre, *Trees*, Springer (1980), Chapter II, §1.1.
* P. Garrett, *Buildings and Classical Groups*, Chapman & Hall (1997), §19.1.
-/

public section

open scoped Pointwise
open IsLocalRing (maximalIdeal)

namespace TauCeti

variable (O K V : Type*) [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module O V]
  [Module K V] [IsScalarTower O K V]

section FullLattices

/-- The **full `O`-lattices** in a `K`-vector space `V`: the `O`-submodules that are lattices
spanning `V` over `K`. They form a set of submodules stable under the nonzero scalars of `K`. -/
def fullLattices : SubMulAction Kˣ (Submodule O V) where
  carrier := {M | M.IsFullLattice K}
  smul_mem' a M hM := by
    have : M.IsFullLattice K := hM
    exact Submodule.IsFullLattice.smul K M a

variable {O K V}

@[simp]
theorem mem_fullLattices {M : Submodule O V} : M ∈ fullLattices O K V ↔ M.IsFullLattice K :=
  Iff.rfl

/-- A member of `fullLattices O K V` is a full lattice. -/
instance (L : fullLattices O K V) : (L : Submodule O V).IsFullLattice K :=
  L.property

/-- Linear automorphisms of `V` move full lattices to full lattices. -/
instance : MulAction (V ≃ₗ[K] V) (fullLattices O K V) where
  smul g L := ⟨g • (L : Submodule O V), mem_fullLattices.2 inferInstance⟩
  one_smul L := Subtype.ext (one_smul _ (L : Submodule O V))
  mul_smul g h L := Subtype.ext (mul_smul g h (L : Submodule O V))

@[simp]
theorem fullLattices.val_linearEquiv_smul (g : V ≃ₗ[K] V) (L : fullLattices O K V) :
    ((g • L : fullLattices O K V) : Submodule O V) = g • (L : Submodule O V) :=
  (rfl)

instance : SMulCommClass Kˣ (V ≃ₗ[K] V) (fullLattices O K V) :=
  ⟨fun a g L => Subtype.ext (smul_comm a g (L : Submodule O V))⟩

instance : SMulCommClass (V ≃ₗ[K] V) Kˣ (fullLattices O K V) :=
  SMulCommClass.symm _ _ _

end FullLattices

/-- The **homothety classes** of full `O`-lattices in `V`: full lattices up to multiplication by
nonzero scalars of `K`. -/
abbrev LatticeClass : Type _ :=
  MulAction.orbitRel.Quotient Kˣ (fullLattices O K V)

namespace LatticeClass

variable {O K V}

/-- The homothety class of a full lattice. -/
def mk (L : fullLattices O K V) : LatticeClass O K V :=
  Quotient.mk (MulAction.orbitRel Kˣ (fullLattices O K V)) L

theorem mk_surjective : Function.Surjective (mk : fullLattices O K V → LatticeClass O K V) :=
  Quotient.mk_surjective

@[elab_as_elim]
theorem ind {p : LatticeClass O K V → Prop} (h : ∀ L, p (mk L)) (x : LatticeClass O K V) : p x :=
  Quotient.ind h x

/-- Two full lattices have the same class exactly when they are homothetic. -/
theorem mk_eq_mk_iff {L M : fullLattices O K V} : mk L = mk M ↔ ∃ a : Kˣ, a • M = L :=
  Quotient.eq.trans MulAction.mem_orbit_iff

/-- Homothetic full lattices have the same class. -/
@[simp]
theorem mk_smul (a : Kˣ) (L : fullLattices O K V) : mk (a • L) = mk L :=
  mk_eq_mk_iff.2 ⟨a, rfl⟩

/-- Linear automorphisms of `V` act on lattice classes through representatives. -/
instance : SMul (V ≃ₗ[K] V) (LatticeClass O K V) where
  smul g := Quotient.map (g • ·) fun L M h => by
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.1 h
    exact MulAction.mem_orbit_iff.2 ⟨a, smul_comm a g M⟩

@[simp]
theorem smul_mk (g : V ≃ₗ[K] V) (L : fullLattices O K V) : g • mk L = mk (g • L) :=
  (rfl)

instance : MulAction (V ≃ₗ[K] V) (LatticeClass O K V) where
  one_smul x := ind (fun L => by rw [smul_mk, one_smul]) x
  mul_smul g h x := ind (fun L => by rw [smul_mk, smul_mk, smul_mk, mul_smul]) x

/-- A scalar automorphism fixes every lattice class: the action of `V ≃ₗ[K] V` factors through the
projective linear group. -/
@[simp]
theorem smulOfUnit_smul (a : Kˣ) (x : LatticeClass O K V) :
    (LinearEquiv.smulOfUnit a : V ≃ₗ[K] V) • x = x := by
  induction x using ind with | h L => ?_
  rw [smul_mk, ← mk_smul a L]
  -- `LinearEquiv.smulOfUnit a` is defined as the action of `a` on `V`, so both translates of `L`
  -- are its image under that action.
  exact congrArg mk (Subtype.ext (Submodule.ext fun _ => Iff.rfl))

section Graph

variable [IsFractionRing O K] [IsDomain O] [IsDiscreteValuationRing O]

/-- No homothety places a submodule strictly between its product with the maximal ideal and
itself. -/
private theorem not_maximalIdeal_smul_lt_and_lt (a : Kˣ) (N : Submodule O V) :
    ¬(maximalIdeal O • N < a • N ∧ a • N < N) := fun ⟨h₁, h₂⟩ =>
  h₂.ne (Submodule.smul_eq_self_of_maximalIdeal_smul_lt Submodule.smul_le_right le_rfl h₁ h₂)

variable (O K V) in
/-- The **adjacency graph of lattice classes** over a discrete valuation ring `O` with fraction
field `K`: two classes are adjacent when they have representatives `L` and `M` with
`𝔪 L ⊊ M ⊊ L`, where `𝔪` is the maximal ideal of `O`. For `V = K²` this is the graph of the
Bruhat–Tits tree of `SL₂(K)`, which is a tree by Serre, *Trees*, Chapter II, §1.1, Theorem 1. -/
def graph : SimpleGraph (LatticeClass O K V) where
  Adj x y := ∃ L M : fullLattices O K V, mk L = x ∧ mk M = y ∧
    maximalIdeal O • (L : Submodule O V) < M ∧ (M : Submodule O V) < L
  symm := ⟨fun _ _ ⟨L, M, hL, hM, h₁, h₂⟩ => by
    obtain ⟨-, π, -, -, h𝔪⟩ := Submodule.exists_units_maximalIdeal_smul_eq O K V
    -- The representatives `M` and `ϖ L` of the two classes are in the opposite position.
    refine ⟨M, π • L, hM, (mk_smul _ _).trans hL, ?_, ?_⟩
    · rw [h𝔪, SubMulAction.val_smul]
      exact Submodule.pointwise_smul_lt_pointwise_smul_iff.2 h₂
    · rwa [SubMulAction.val_smul, ← h𝔪]⟩
  loopless := ⟨fun _ ⟨L, M, hL, hM, h₁, h₂⟩ => by
    obtain ⟨a, rfl⟩ := mk_eq_mk_iff.1 (hM.trans hL.symm)
    rw [SubMulAction.val_smul] at h₁ h₂
    exact not_maximalIdeal_smul_lt_and_lt a (L : Submodule O V) ⟨h₁, h₂⟩⟩

theorem graph_adj_iff {x y : LatticeClass O K V} :
    (graph O K V).Adj x y ↔ ∃ L M : fullLattices O K V, mk L = x ∧ mk M = y ∧
      maximalIdeal O • (L : Submodule O V) < M ∧ (M : Submodule O V) < L :=
  Iff.rfl

/-- Full lattices `L` and `M` with `𝔪 L ⊊ M ⊊ L` have adjacent classes. -/
theorem graph_adj_mk_of_lt {L M : fullLattices O K V}
    (h₁ : maximalIdeal O • (L : Submodule O V) < M) (h₂ : (M : Submodule O V) < L) :
    (graph O K V).Adj (mk L) (mk M) :=
  ⟨L, M, rfl, rfl, h₁, h₂⟩

/-- **Adjacency on a fixed representative.** The classes of `L` and `M` are adjacent exactly when
some multiple `a M` lies strictly between `𝔪 L` and `L`. -/
theorem graph_adj_mk_iff {L M : fullLattices O K V} :
    (graph O K V).Adj (mk L) (mk M) ↔ ∃ a : Kˣ, maximalIdeal O • (L : Submodule O V) <
      a • (M : Submodule O V) ∧ a • (M : Submodule O V) < L := by
  refine ⟨?_, fun ⟨a, h₁, h₂⟩ => (mk_smul a M).symm ▸ graph_adj_mk_of_lt
    (by rwa [SubMulAction.val_smul]) (by rwa [SubMulAction.val_smul])⟩
  rintro ⟨L', M', hL, hM, h₁, h₂⟩
  obtain ⟨b, rfl⟩ := mk_eq_mk_iff.1 hL
  obtain ⟨c, rfl⟩ := mk_eq_mk_iff.1 hM
  rw [SubMulAction.val_smul, SubMulAction.val_smul] at h₁ h₂
  -- Translate the chain `𝔪 (b L) = b (𝔪 L) ⊊ c M ⊊ b L` by `b⁻¹`.
  refine ⟨b⁻¹ * c, ?_, ?_⟩
  · rw [mul_smul, ← inv_smul_smul b (maximalIdeal O • (L : Submodule O V))]
    exact Submodule.pointwise_smul_lt_pointwise_smul_iff.2
      ((Submodule.ideal_smul_pointwise_smul _ _ _).symm.trans_lt h₁)
  · rw [mul_smul, ← inv_smul_smul b (L : Submodule O V)]
    exact Submodule.pointwise_smul_lt_pointwise_smul_iff.2 h₂

/-- The submodules strictly between `𝔪 L` and `L`, as full lattices: by
`Submodule.IsFullLattice.of_maximalIdeal_smul_le` they are full lattices. -/
private def betweenToFullLattices (L : fullLattices O K V)
    (M : {M : Submodule O V // maximalIdeal O • (L : Submodule O V) < M ∧ M < L}) :
    fullLattices O K V :=
  ⟨M, mem_fullLattices.2
    (Submodule.IsFullLattice.of_maximalIdeal_smul_le K M.property.1.le M.property.2.le)⟩

/-- The class of a submodule strictly between `𝔪 L` and `L`, as a neighbour of the class of
`L`. -/
private def toNeighbor (L : fullLattices O K V)
    (M : {M : Submodule O V // maximalIdeal O • (L : Submodule O V) < M ∧ M < L}) :
    (graph O K V).neighborSet (mk L) :=
  ⟨mk (betweenToFullLattices L M), graph_adj_mk_of_lt M.property.1 M.property.2⟩

private theorem toNeighbor_bijective (L : fullLattices O K V) :
    Function.Bijective (toNeighbor L) := by
  refine ⟨fun M₁ M₂ h => ?_, fun ⟨y, hy⟩ => ?_⟩
  · -- Two such submodules with the same class are homothetic, and the homothety fixes them.
    obtain ⟨a, ha⟩ := mk_eq_mk_iff.1 (congrArg Subtype.val h)
    have ha' : a • (M₂ : Submodule O V) = M₁ := congrArg Subtype.val ha
    refine Subtype.ext (ha'.symm.trans (Submodule.smul_eq_self_of_maximalIdeal_smul_lt
      M₂.property.1.le M₂.property.2.le ?_ ?_))
    · rw [ha']
      exact M₁.property.1
    · rw [ha']
      exact M₁.property.2
  · -- A neighbour has a representative strictly between `𝔪 L` and `L`.
    induction y using ind with | h M => ?_
    obtain ⟨a, h₁, h₂⟩ := graph_adj_mk_iff.1 hy
    exact ⟨⟨a • (M : Submodule O V), h₁, h₂⟩, Subtype.ext ((congrArg mk
      (Subtype.ext (SubMulAction.val_smul a M).symm)).trans (mk_smul a M))⟩

/-- **The neighbours of a lattice class.** The classes adjacent to the class of a full lattice `L`
correspond to the submodules strictly between `𝔪 L` and `L`: each neighbour has exactly one
representative between them. For `V = K²` these are the lines of `L / 𝔪 L`. -/
noncomputable def neighborEquiv (L : fullLattices O K V) :
    (graph O K V).neighborSet (mk L) ≃
      {M : Submodule O V // maximalIdeal O • (L : Submodule O V) < M ∧ M < L} :=
  (Equiv.ofBijective _ (toNeighbor_bijective L)).symm

/-- The inverse of `neighborEquiv L` sends a submodule strictly between `𝔪 L` and `L` to its
class. -/
@[simp]
theorem coe_neighborEquiv_symm_apply (L : fullLattices O K V)
    (M : {M : Submodule O V // maximalIdeal O • (L : Submodule O V) < M ∧ M < L}) :
    ((neighborEquiv L).symm M : LatticeClass O K V) =
      mk ⟨M, mem_fullLattices.2
        (Submodule.IsFullLattice.of_maximalIdeal_smul_le K M.property.1.le M.property.2.le)⟩ :=
  (rfl)

/-- Linear automorphisms of `V` preserve adjacency of lattice classes. -/
@[simp]
theorem graph_adj_smul_iff (g : V ≃ₗ[K] V) {x y : LatticeClass O K V} :
    (graph O K V).Adj (g • x) (g • y) ↔ (graph O K V).Adj x y := by
  -- It suffices to show that `g` preserves adjacency, since `g⁻¹` then does too.
  suffices h : ∀ (g : V ≃ₗ[K] V) {x y : LatticeClass O K V},
      (graph O K V).Adj x y → (graph O K V).Adj (g • x) (g • y) from
    ⟨fun hg => by simpa using h g⁻¹ hg, h g⟩
  rintro g _ _ ⟨L, M, rfl, rfl, h₁, h₂⟩
  refine graph_adj_mk_of_lt ?_ ?_
  · simpa only [fullLattices.val_linearEquiv_smul, Submodule.ideal_smul_pointwise_smul,
      Submodule.pointwise_smul_lt_pointwise_smul_iff] using h₁
  · simpa only [fullLattices.val_linearEquiv_smul,
      Submodule.pointwise_smul_lt_pointwise_smul_iff] using h₂

variable (O K V) in
/-- The action of the linear automorphisms of `V` on the adjacency graph of lattice classes, by
graph automorphisms. -/
def toGraphIso : (V ≃ₗ[K] V) →* (graph O K V ≃g graph O K V) where
  toFun g :=
    { toEquiv := MulAction.toPerm g
      map_rel_iff' := graph_adj_smul_iff g }
  map_one' := RelIso.ext fun x => one_smul (V ≃ₗ[K] V) x
  map_mul' g h := RelIso.ext fun x => mul_smul g h x

@[simp]
theorem toGraphIso_apply (g : V ≃ₗ[K] V) (x : LatticeClass O K V) :
    toGraphIso O K V g x = g • x :=
  (rfl)

end Graph

end LatticeClass

end TauCeti
