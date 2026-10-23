/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.LowDimTopology.Heegaard.Domain
import Mathlib.Tactic.Abel

/-!
# The class `ε(x, y)` of a pair of generators

Let `(Σ, α, β, z)` be a pointed Heegaard diagram of a closed `3`-manifold `Y`, with generators
`x`, `y`. Ozsváth and Szabó attach to them a class `ε(x, y) ∈ H₁(Y; ℤ)`: join the points of `x`
to those of `y` by paths in the `α`-curves, join the points of `y` back to those of `x` by paths
in the `β`-curves, and take the class of the resulting loop in
`H₁(Σ) / ⟨[α₁], …, [β₁], …⟩ ≅ H₁(Y)`. Changing the paths changes the loop by whole curves, so
the class is well defined. It vanishes exactly when some domain connects `x` to `y`, and
`s_z(x) - s_z(y)` is the Poincaré dual of `ε(x, y)` (Ozsváth–Szabó, Lemma 2.19). So `ε` sorts
the generators into the spin^c summands of the Heegaard Floer chain complex, and the differential
only counts disks between generators in the same summand.

This file develops `ε` for the incidence data `TauCeti.HeegaardRegionSystem`. A `1`-chain on
`α ∪ β` is a pair of integer functions on intersection points: a coefficient on the `α`-arc and
one on the `β`-arc starting at each point. The class `ε(x, y)` lives in
`TauCeti.HeegaardRegionSystem.CurveHomology`, the group of `1`-cycles of `α ∪ β` modulo
boundaries of domains and the cycles supported on whole curves. For the incidence data of an
actual diagram in which every attaching curve meets the other family, so that the arcs cover
`α ∪ β`, the boundaries of domains are exactly the cycles of `α ∪ β` that bound in `Σ`,
so this group is the image of `H₁(α ∪ β)` in `H₁(Σ) / ⟨[αᵢ], [βⱼ]⟩ ≅ H₁(Y)` and embeds in
`H₁(Y)`; that identification is geometric and is not formalized here. The embedding need not be
onto: for the genus-one diagram of `S¹ × S²` in
`TauCeti.LowDimTopology.Heegaard.CircleTimesSphere`, the core of the annulus is not homologous
to a cycle in `α ∪ β`, and the group is trivial although `H₁(S¹ × S²) = ℤ`. Since `ε(x, y)` is
the class of a cycle in `α ∪ β`, nothing is lost for it.

## Main definitions

* `TauCeti.HeegaardRegionSystem.arcBoundary`: the boundary of a `1`-chain on `α ∪ β`.
* `TauCeti.HeegaardRegionSystem.domainBoundary`: the boundary of a domain, as a `1`-chain.
* `TauCeti.HeegaardRegionSystem.arcCycles`: the `1`-cycles of `α ∪ β`.
* `TauCeti.HeegaardRegionSystem.curveCycles`: the `1`-chains that are combinations of whole
  `α`- and `β`-curves.
* `TauCeti.HeegaardRegionSystem.arcRelations`: boundaries of domains plus whole curves.
* `TauCeti.HeegaardRegionSystem.CurveHomology`: the `1`-cycles modulo `arcRelations`, with
  its class map `CurveHomology.mk` and universal property `CurveHomology.lift`.
* `TauCeti.HeegaardRegionSystem.IsConnectingChain`: a `1`-chain made of paths from `x` to `y`
  along `α` and from `y` to `x` along `β`.
* `TauCeti.HeegaardRegionSystem.epsilon`: the class `ε(x, y)`.

## Main results

* `TauCeti.HeegaardRegionSystem.exists_isConnectingChain`: any two generators are joined by a
  connecting chain.
* `TauCeti.HeegaardRegionSystem.IsConnectingChain.epsilon_eq`: `ε(x, y)` is the class of every
  connecting chain.
* `TauCeti.HeegaardRegionSystem.epsilon_add_epsilon`: `ε(x, y) + ε(y, w) = ε(x, w)`.
* `TauCeti.HeegaardRegionSystem.epsilon_eq_zero_iff`: `ε(x, y) = 0` exactly when some domain
  connects `x` to `y`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4: Definition 2.11 of `ε(x, y)`,
  Proposition 2.15 (`π₂(x, y)` is nonempty exactly when `ε(x, y) = 0`) and Lemma 2.19.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

section Chains

/-- The boundary of a `1`-chain on `α ∪ β`, given as its `α`-part and its `β`-part. -/
def arcBoundary : (Point → ℤ) × (Point → ℤ) →+ (Point → ℤ) :=
  H.alphaArcBoundary.coprod H.betaArcBoundary

@[simp]
theorem arcBoundary_apply (c : (Point → ℤ) × (Point → ℤ)) :
    H.arcBoundary c = H.alphaArcBoundary c.1 + H.betaArcBoundary c.2 :=
  (rfl)

/-- The boundary of a domain as a `1`-chain on `α ∪ β`: its `α`-part `∂D ∩ α` and its `β`-part
`∂D ∩ β`. -/
def domainBoundary : (Region → ℤ) →+ (Point → ℤ) × (Point → ℤ) :=
  H.alphaBoundary.prod H.betaBoundary

@[simp]
theorem domainBoundary_apply (D : Region → ℤ) :
    H.domainBoundary D = (H.alphaBoundary D, H.betaBoundary D) :=
  (rfl)

/-- The boundary of a domain is a cycle. -/
theorem arcBoundary_domainBoundary (D : Region → ℤ) : H.arcBoundary (H.domainBoundary D) = 0 :=
  by simpa using H.boundary_boundary_eq_zero D

/-- The `1`-cycles of `α ∪ β`. -/
def arcCycles : AddSubgroup ((Point → ℤ) × (Point → ℤ)) :=
  H.arcBoundary.ker

variable {H} in
@[simp]
theorem mem_arcCycles_iff {c : (Point → ℤ) × (Point → ℤ)} :
    c ∈ H.arcCycles ↔ H.alphaArcBoundary c.1 + H.betaArcBoundary c.2 = 0 := by
  simp [arcCycles]

/-- The `1`-chains that are combinations `∑ aᵢ αᵢ + ∑ bⱼ βⱼ` of whole curves, that is, whose
`α`- and `β`-parts are both cycles. -/
def curveCycles : AddSubgroup ((Point → ℤ) × (Point → ℤ)) :=
  H.alphaArcBoundary.ker.prod H.betaArcBoundary.ker

variable {H} in
/-- A `1`-chain is a combination of whole curves exactly when its `α`- and `β`-parts are
cycles. -/
@[simp]
theorem mem_curveCycles_iff {c : (Point → ℤ) × (Point → ℤ)} :
    c ∈ H.curveCycles ↔ H.alphaArcBoundary c.1 = 0 ∧ H.betaArcBoundary c.2 = 0 :=
  Iff.rfl

variable {H} in
/-- A `1`-chain is a combination of whole curves exactly when its `α`-part is constant along
each `α`-curve and its `β`-part is constant along each `β`-curve. -/
theorem mem_curveCycles_iff_exists {c : (Point → ℤ) × (Point → ℤ)} :
    c ∈ H.curveCycles ↔ (∃ a : Fin n → ℤ, ∀ p, c.1 p = a (H.alpha p)) ∧
      ∃ b : Fin n → ℤ, ∀ p, c.2 p = b (H.beta p) := by
  rw [mem_curveCycles_iff, alphaArcBoundary_eq_zero_iff, betaArcBoundary_eq_zero_iff]

/-- The relations defining `CurveHomology`: boundaries of domains plus combinations of whole
curves. -/
def arcRelations : AddSubgroup ((Point → ℤ) × (Point → ℤ)) :=
  H.domainBoundary.range ⊔ H.curveCycles

variable {H} in
/-- A `1`-chain is a relation exactly when it differs from the boundary of some domain by a
combination of whole curves. -/
theorem mem_arcRelations_iff {c : (Point → ℤ) × (Point → ℤ)} :
    c ∈ H.arcRelations ↔ ∃ D, c - H.domainBoundary D ∈ H.curveCycles := by
  simp only [arcRelations, AddSubgroup.mem_sup, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨D, rfl⟩, e, he, rfl⟩
    exact ⟨D, by simpa using he⟩
  · rintro ⟨D, hD⟩
    exact ⟨_, ⟨D, rfl⟩, _, hD, add_sub_cancel _ _⟩

/-- The boundary of a domain is a relation. -/
theorem domainBoundary_mem_arcRelations (D : Region → ℤ) :
    H.domainBoundary D ∈ H.arcRelations :=
  AddSubgroup.mem_sup_left ⟨D, rfl⟩

/-- Combinations of whole curves are relations. -/
theorem curveCycles_le_arcRelations : H.curveCycles ≤ H.arcRelations :=
  le_sup_right

/-- Every relation is a cycle. -/
theorem arcRelations_le_arcCycles : H.arcRelations ≤ H.arcCycles := by
  refine sup_le ?_ fun c hc => ?_
  · rintro _ ⟨D, rfl⟩
    exact H.arcBoundary_domainBoundary D
  · rw [mem_curveCycles_iff] at hc
    simp [hc.1, hc.2]

end Chains

section CurveHomology

/-- The `1`-cycles of `α ∪ β` modulo boundaries of domains and combinations of whole curves.
For the incidence data of a pointed Heegaard diagram of `Y` whose arcs cover `α ∪ β`, this is
the image of `H₁(α ∪ β)` in `H₁(Σ) / ⟨[αᵢ], [βⱼ]⟩ ≅ H₁(Y; ℤ)`, the group in which the classes
`ε(x, y)` live. -/
def CurveHomology : Type u :=
  H.arcCycles ⧸ H.arcRelations.addSubgroupOf H.arcCycles

instance : AddCommGroup H.CurveHomology :=
  inferInstanceAs (AddCommGroup (H.arcCycles ⧸ H.arcRelations.addSubgroupOf H.arcCycles))

/-- The class of a `1`-cycle of `α ∪ β` in `CurveHomology`. -/
def CurveHomology.mk : H.arcCycles →+ H.CurveHomology :=
  QuotientAddGroup.mk' _

/-- Every element of `CurveHomology` is the class of a cycle. -/
theorem CurveHomology.mk_surjective : Function.Surjective (CurveHomology.mk H) :=
  QuotientAddGroup.mk'_surjective _

/-- A cycle has class zero exactly when it is a relation. -/
@[simp]
theorem CurveHomology.mk_eq_zero_iff {c : H.arcCycles} :
    CurveHomology.mk H c = 0 ↔ (c : (Point → ℤ) × (Point → ℤ)) ∈ H.arcRelations :=
  (QuotientAddGroup.eq_zero_iff c).trans AddSubgroup.mem_addSubgroupOf

/-- Two cycles have the same class exactly when they differ by a relation. -/
@[simp]
theorem CurveHomology.mk_eq_mk_iff {c d : H.arcCycles} :
    CurveHomology.mk H c = CurveHomology.mk H d ↔
      (c - d : (Point → ℤ) × (Point → ℤ)) ∈ H.arcRelations := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, AddSubgroup.coe_sub]

/-- Two additive homomorphisms out of `CurveHomology` agree once they agree on classes of
cycles. -/
@[ext]
theorem CurveHomology.hom_ext {A : Type*} [AddMonoid A] {f g : H.CurveHomology →+ A}
    (h : f.comp (CurveHomology.mk H) = g.comp (CurveHomology.mk H)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ h

/-- An additive homomorphism on `1`-cycles that vanishes on the relations descends to
`CurveHomology`. -/
def CurveHomology.lift {A : Type*} [AddMonoid A] (f : H.arcCycles →+ A)
    (hf : ∀ c : H.arcCycles, (c : (Point → ℤ) × (Point → ℤ)) ∈ H.arcRelations → f c = 0) :
    H.CurveHomology →+ A :=
  QuotientAddGroup.lift _ f fun c hc => hf c (AddSubgroup.mem_addSubgroupOf.mp hc)

@[simp]
theorem CurveHomology.lift_mk {A : Type*} [AddMonoid A] (f : H.arcCycles →+ A)
    (hf : ∀ c : H.arcCycles, (c : (Point → ℤ) × (Point → ℤ)) ∈ H.arcRelations → f c = 0)
    (c : H.arcCycles) : CurveHomology.lift H f hf (CurveHomology.mk H c) = f c :=
  (rfl)

end CurveHomology

section ConnectingChain

variable {H}

/-- `c` connects the generator `x` to the generator `y`: its `α`-part is a `1`-chain on the
`α`-arcs with boundary `y - x` and its `β`-part a `1`-chain on the `β`-arcs with boundary
`x - y`. Concretely, `c` runs from the points of `x` to those of `y` along the `α`-curves and
back along the `β`-curves. -/
def IsConnectingChain (x y : H.Generator) (c : (Point → ℤ) × (Point → ℤ)) : Prop :=
  H.alphaArcBoundary c.1 = H.generatorChain y - H.generatorChain x ∧
    H.betaArcBoundary c.2 = H.generatorChain x - H.generatorChain y

/-- Unfolding `IsConnectingChain` into its two boundary conditions. -/
@[simp]
theorem isConnectingChain_iff {x y : H.Generator} {c : (Point → ℤ) × (Point → ℤ)} :
    H.IsConnectingChain x y c ↔
      H.alphaArcBoundary c.1 = H.generatorChain y - H.generatorChain x ∧
        H.betaArcBoundary c.2 = H.generatorChain x - H.generatorChain y :=
  Iff.rfl

/-- The boundary of a domain connects `x` to `y` exactly when the domain does. -/
theorem isConnectingChain_domainBoundary_iff {x y : H.Generator} {D : Region → ℤ} :
    H.IsConnectingChain x y (H.domainBoundary D) ↔ H.IsDomainBetween x y D := by
  rw [isConnectingChain_iff, isDomainBetween_iff, domainBoundary_apply]

alias ⟨_, IsDomainBetween.isConnectingChain⟩ := isConnectingChain_domainBoundary_iff

/-- The chains connecting a generator to itself are the combinations of whole curves. -/
theorem isConnectingChain_self_iff {x : H.Generator} {c : (Point → ℤ) × (Point → ℤ)} :
    H.IsConnectingChain x x c ↔ c ∈ H.curveCycles := by
  simp [mem_curveCycles_iff]

namespace IsConnectingChain

variable {x y w : H.Generator} {c d : (Point → ℤ) × (Point → ℤ)}

/-- A connecting chain is a cycle. -/
theorem mem_arcCycles (hc : H.IsConnectingChain x y c) : c ∈ H.arcCycles := by
  simp [hc.1, hc.2]

/-- Concatenating a chain from `x` to `y` with one from `y` to `w` gives a chain from `x` to
`w`. -/
theorem add (hc : H.IsConnectingChain x y c) (hd : H.IsConnectingChain y w d) :
    H.IsConnectingChain x w (c + d) := by
  refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, map_add, hc.1, hc.2, hd.1, hd.2] <;>
    abel

/-- Reversing a chain from `x` to `y` gives a chain from `y` to `x`. -/
theorem neg (hc : H.IsConnectingChain x y c) : H.IsConnectingChain y x (-c) := by
  refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_neg, Prod.snd_neg, map_neg, hc.1, hc.2, neg_sub]

/-- Two chains connecting `x` to `y` differ by a combination of whole curves. -/
theorem sub_mem_curveCycles (hc : H.IsConnectingChain x y c) (hd : H.IsConnectingChain x y d) :
    c - d ∈ H.curveCycles := by
  rw [mem_curveCycles_iff]
  simp [hc.1, hc.2, hd.1, hd.2]

end IsConnectingChain

/-- Any two generators are connected by a chain. -/
theorem exists_isConnectingChain (x y : H.Generator) : ∃ c, H.IsConnectingChain x y c := by
  classical
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_comp_symm_sub_eq_sum (u := H.point x) (v := H.point y)
    (fun i => (H.alphaNext_isCycleOn i).2 (by simp) (by simp)) fun _ => (1 : ℤ)
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_comp_symm_sub_eq_sum
    (u := fun j => H.point y (y.1.symm j)) (v := fun j => H.point x (x.1.symm j))
    (fun j => (H.betaNext_isCycleOn j).2 (by simp) (by simp)) fun _ => (1 : ℤ)
  refine ⟨(a, b), ?_, ?_⟩
  · rw [H.generatorChain_eq_sum_single, H.generatorChain_eq_sum_single, ← ha]
    exact funext fun q => H.alphaArcBoundary_apply a q
  · rw [H.generatorChain_eq_sum_single, H.generatorChain_eq_sum_single,
      ← Equiv.sum_comp x.1.symm, ← Equiv.sum_comp y.1.symm (fun i => Pi.single (H.point y i) 1),
      ← hb]
    exact funext fun q => H.betaArcBoundary_apply b q

end ConnectingChain

section Epsilon

/-- The class `ε(x, y)` of Ozsváth and Szabó: the class in `CurveHomology` of any chain
connecting `x` to `y` (see `IsConnectingChain.epsilon_eq`). -/
noncomputable def epsilon (x y : H.Generator) : H.CurveHomology :=
  CurveHomology.mk H ⟨_, (H.exists_isConnectingChain x y).choose_spec.mem_arcCycles⟩

variable {H} {x y w : H.Generator}

/-- `ε(x, y)` is the class of every chain connecting `x` to `y`. -/
theorem IsConnectingChain.epsilon_eq {c : (Point → ℤ) × (Point → ℤ)}
    (hc : H.IsConnectingChain x y c) : H.epsilon x y = CurveHomology.mk H ⟨c, hc.mem_arcCycles⟩ :=
  (CurveHomology.mk_eq_mk_iff H).mpr <| H.curveCycles_le_arcRelations <|
    (H.exists_isConnectingChain x y).choose_spec.sub_mem_curveCycles hc

/-- `ε(x, x) = 0`. -/
@[simp]
theorem epsilon_self (x : H.Generator) : H.epsilon x x = 0 := by
  rw [(isConnectingChain_self_iff.mpr (zero_mem H.curveCycles)).epsilon_eq,
    CurveHomology.mk_eq_zero_iff]
  exact zero_mem _

/-- The classes `ε` are additive along a chain of generators: `ε(x, y) + ε(y, w) = ε(x, w)`. -/
@[simp]
theorem epsilon_add_epsilon (x y w : H.Generator) :
    H.epsilon x y + H.epsilon y w = H.epsilon x w := by
  obtain ⟨c, hc⟩ := H.exists_isConnectingChain x y
  obtain ⟨d, hd⟩ := H.exists_isConnectingChain y w
  rw [hc.epsilon_eq, hd.epsilon_eq, (hc.add hd).epsilon_eq, ← map_add]
  exact congrArg _ (Subtype.ext (by simp))

/-- Exchanging the generators negates `ε`: `-ε(x, y) = ε(y, x)`. -/
@[simp]
theorem neg_epsilon (x y : H.Generator) : -H.epsilon x y = H.epsilon y x :=
  neg_eq_of_add_eq_zero_right (by rw [epsilon_add_epsilon, epsilon_self])

/-- `ε(x, y)` vanishes exactly when some domain connects `x` to `y`. -/
@[simp]
theorem epsilon_eq_zero_iff : H.epsilon x y = 0 ↔ ∃ D, H.IsDomainBetween x y D := by
  obtain ⟨c, hc⟩ := H.exists_isConnectingChain x y
  rw [hc.epsilon_eq, CurveHomology.mk_eq_zero_iff, mem_arcRelations_iff]
  refine exists_congr fun D => ⟨fun h => ?_, fun h => hc.sub_mem_curveCycles h.isConnectingChain⟩
  rw [mem_curveCycles_iff] at h
  have h_alpha : H.alphaArcBoundary c.1 = H.alphaArcBoundary (H.domainBoundary D).1 :=
    sub_eq_zero.mp (by simpa only [Prod.fst_sub, map_sub] using h.1)
  have h_beta : H.betaArcBoundary c.2 = H.betaArcBoundary (H.domainBoundary D).2 :=
    sub_eq_zero.mp (by simpa only [Prod.snd_sub, map_sub] using h.2)
  apply isConnectingChain_domainBoundary_iff.mp
  exact ⟨h_alpha.symm.trans hc.1, h_beta.symm.trans hc.2⟩

/-- If a domain connects `x` to `y`, then `ε(x, y) = 0`. -/
theorem IsDomainBetween.epsilon_eq_zero {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    H.epsilon x y = 0 :=
  epsilon_eq_zero_iff.mpr ⟨D, hD⟩

end Epsilon

end HeegaardRegionSystem

end TauCeti
