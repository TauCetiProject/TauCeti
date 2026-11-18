/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Mazur's finiteness condition `Φ_p`

A profinite group `G` satisfies **Mazur's finiteness condition** `Φ_p` at a prime `p` if every
open subgroup `U` of `G` has only finitely many continuous homomorphisms `U → 𝔽_p`. This is the
group-theoretic hypothesis under which the framed and unframed deformation functors of a
continuous residual representation of `G` over a finite field of characteristic `p` have
Noetherian representing rings: over a finite field `k` of characteristic `p`, the tangent space
of the lifting functor of the trivial rank-one representation of `U` is
`Hom_cont(U, k) = Hom_cont(U, 𝔽_p) ⊗ k`, and the open subgroups enter through the kernel of the
residual representation.

The condition quantifies over every open subgroup, not only over `G` itself. A group can have no
nonzero continuous homomorphism to `𝔽_p` while an open subgroup has infinitely many: for odd `p`
the semidirect product of `∏_ℕ ℤ/p` by an involution acting by inversion is an example.

For a profinite group the condition is equivalent to the topological finite generation of the
maximal pro-`p` quotient of every open subgroup: characters with values in `𝔽_p` factor through
the maximal pro-`p` quotient, and by Burnside's basis theorem a pro-`p` group is topologically
finitely generated exactly when its continuous `𝔽_p`-dual is finite-dimensional.
In particular topologically finitely generated profinite groups, such as `ℤ_p` and the finite
groups, satisfy `Φ_p`, while the countable power `∏_ℕ ℤ/p` does not, already because its
coordinate characters are pairwise distinct.

## Main definitions

* `TauCeti.MazurFiniteness p G`: Mazur's finiteness condition `Φ_p`: every open subgroup of `G`
  has finitely many continuous homomorphisms to `ZMod p`.

## Main results

* `TauCeti.mazurFiniteness_iff_forall_moduleFinite`: the same condition with each continuous
  `ZMod p`-dual finite as a `ZMod p`-module; for prime `p`, finite-dimensional over `𝔽_p`.
* `TauCeti.MazurFiniteness.finite_continuousZModDual`: under `Φ_p` the group itself has finitely
  many continuous homomorphisms to `ZMod p`.
* `TauCeti.MazurFiniteness.openSubgroup`: `Φ_p` passes to open subgroups.
* `TauCeti.mazurFiniteness_iff_forall_isTopologicallyFinitelyGenerated_maximalProPQuotient`: a
  profinite group satisfies `Φ_p` exactly when the maximal pro-`p` quotient of each of its open
  subgroups is topologically finitely generated.
* `TauCeti.IsTopologicallyFinitelyGenerated.mazurFiniteness`: a topologically finitely generated
  compact group satisfies `Φ_p`.
* `TauCeti.mazurFiniteness_of_finite`, `TauCeti.mazurFiniteness_multiplicative_padicInt`: finite
  groups and the additive group of `ℤ_p` satisfy `Φ_p`.
* `TauCeti.not_mazurFiniteness_pi_zmod`: the countable power of `ℤ/p` does not satisfy `Φ_p`.

## References

* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publications 16
  (1989), Section 1.1.
* T. Gee, *Modularity lifting theorems*, Essential Number Theory 1 (2022), Section 3.1.
* M. Kisin, *Moduli of finite flat group schemes and modularity*, lecture notes, Lecture 1, (1.2)
  and Exercise 1.
-/

public section

namespace TauCeti

universe u

/-- **Mazur's finiteness condition `Φ_p`.** Every open subgroup `U` of the topological group `G`
has only finitely many continuous homomorphisms `U → ZMod p`. For a prime `p` and a profinite `G`
this is the hypothesis under which deformation functors of residual representations of `G` over
finite fields of characteristic `p` have Noetherian representing rings. -/
def MazurFiniteness (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenSubgroup G, Finite (continuousZModDual p U.toSubgroup)

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- The defining property of `TauCeti.MazurFiniteness`. -/
theorem mazurFiniteness_iff_forall_finite :
    MazurFiniteness p G ↔ ∀ U : OpenSubgroup G, Finite (continuousZModDual p U.toSubgroup) :=
  Iff.rfl

/-- Under `Φ_p` the group itself has only finitely many continuous homomorphisms to `ZMod p`. A
condition imposed only at this level would not be `Φ_p`. -/
theorem MazurFiniteness.finite_continuousZModDual (h : MazurFiniteness p G) :
    Finite (continuousZModDual p G) :=
  have := h ⊤
  let e : (⊤ : Subgroup G) ≃ₜ* G :=
    { toMulEquiv := Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  .of_injective _ e.continuousZModDualMap_bijective.1

/-- **`Φ_p` passes to open subgroups.** An open subgroup of an open subgroup `U` of `G` is an open
subgroup of `G`, through the inclusion of `U`. -/
theorem MazurFiniteness.openSubgroup (h : MazurFiniteness p G) (U : OpenSubgroup G) :
    MazurFiniteness p U.toSubgroup := by
  intro V
  let W : Subgroup G := V.toSubgroup.map U.toSubgroup.subtype
  have hW : IsOpen (W : Set G) := by
    rw [Subgroup.coe_map]
    exact U.isOpen.isOpenMap_subtype_val _ V.isOpen
  have hWU : W ≤ U.toSubgroup := Subgroup.map_subtype_le _
  have : Finite (continuousZModDual p W) := h ⟨W, hW⟩
  have hfin : Finite (continuousZModDual p (W.subgroupOf U.toSubgroup)) :=
    Finite.of_injective _
      (Subgroup.subgroupOfContinuousMulEquivOfLe hWU).symm.continuousZModDualMap_bijective.1
  rwa [← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)] at hfin

section NeZero

variable [NeZero p]

/-- **`Φ_p` in terms of dimensions.** Over the finite ring `ZMod p`, for instance the field `𝔽_p`,
finiteness of the continuous `ZMod p`-dual of each open subgroup is its finiteness as a module. -/
theorem mazurFiniteness_iff_forall_moduleFinite :
    MazurFiniteness p G ↔
      ∀ U : OpenSubgroup G, Module.Finite (ZMod p) (continuousZModDual p U.toSubgroup) :=
  forall_congr' fun _ ↦ ⟨fun _ ↦ .of_finite, fun _ ↦ Module.finite_of_finite (ZMod p)⟩

/-- **Finite groups satisfy `Φ_p`.** A continuous homomorphism is determined by its values, and
there are only finitely many functions from a finite group to `ZMod p`. No hypothesis on the
topology is needed. -/
theorem mazurFiniteness_of_finite [Finite G] : MazurFiniteness p G := fun U ↦
  Finite.of_injective (β := U.toSubgroup → Multiplicative (ZMod p)) (fun χ ↦ ⇑χ.toMul)
    fun _ _ h ↦ Additive.toMul.injective (DFunLike.coe_injective h)

end NeZero

section TopologicalGroup

variable [IsTopologicalGroup G] [CompactSpace G]

/-- **Topologically finitely generated compact groups satisfy `Φ_p`.** Every open subgroup has
finite index, hence is topologically finitely generated by the Schreier bound, and a finite
topological generating set bounds the dimension of the continuous `𝔽_p`-dual. -/
theorem IsTopologicallyFinitelyGenerated.mazurFiniteness [Fact p.Prime]
    (hG : IsTopologicallyFinitelyGenerated G) : MazurFiniteness p G :=
  mazurFiniteness_iff_forall_moduleFinite.mpr fun U ↦
    finite_continuousZModDual (hG.of_openSubgroup U)

variable [TotallyDisconnectedSpace G]

/-- **Characterisation of `Φ_p`.** A profinite group satisfies Mazur's condition `Φ_p` exactly when
the maximal pro-`p` quotient of every open subgroup is topologically finitely generated: continuous
`𝔽_p`-valued characters of an open subgroup are those of its maximal pro-`p` quotient, whose
continuous `𝔽_p`-dual is finite-dimensional exactly under topological finite generation, by
Burnside's basis theorem. -/
theorem mazurFiniteness_iff_forall_isTopologicallyFinitelyGenerated_maximalProPQuotient
    [Fact p.Prime] :
    MazurFiniteness p G ↔
      ∀ U : OpenSubgroup G,
        IsTopologicallyFinitelyGenerated (maximalProPQuotient p U.toSubgroup) := by
  refine forall_congr' fun U ↦ ?_
  have hbij := maximalProPQuotient.continuousZModDualMap_bijective (p := p) (G := U.toSubgroup)
  rw [← isProP_maximalProPQuotient.finite_continuousZModDual_iff]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : Finite (continuousZModDual p (maximalProPQuotient p U.toSubgroup)) :=
      .of_injective _ hbij.1
    exact .of_finite
  · have := Module.finite_of_finite (ZMod p)
      (M := continuousZModDual p (maximalProPQuotient p U.toSubgroup))
    exact .of_surjective _ hbij.2

end TopologicalGroup

/-- **`ℤ_p` satisfies `Φ_p`.** The additive group of the `p`-adic integers is topologically
generated by `1`. -/
theorem mazurFiniteness_multiplicative_padicInt (p : ℕ) [Fact p.Prime] :
    MazurFiniteness p (Multiplicative ℤ_[p]) :=
  (isTopologicallyFinitelyGenerated_multiplicative_padicInt p).mazurFiniteness

/-- **The countable power of `ℤ/p` does not satisfy `Φ_p`.** Already the group itself has
infinitely many continuous homomorphisms to `ZMod p`: the coordinate projections are pairwise
distinct. -/
theorem not_mazurFiniteness_pi_zmod (p : ℕ) [Fact (1 < p)] :
    ¬ MazurFiniteness p (ℕ → Multiplicative (ZMod p)) := by
  intro h
  have := h.finite_continuousZModDual
  let coord (i : ℕ) : continuousZModDual p (ℕ → Multiplicative (ZMod p)) :=
    Additive.ofMul ⟨Pi.evalMonoidHom _ i, continuous_apply i⟩
  have hcoord (i : ℕ) (x : ℕ → Multiplicative (ZMod p)) : Additive.toMul (coord i) x = x i := rfl
  have hinj : Function.Injective coord := fun i j hij ↦ by
    by_contra hne
    have := DFunLike.congr_fun (congrArg Additive.toMul hij) (Pi.mulSingle i (.ofAdd 1))
    rw [hcoord, hcoord, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hne)] at this
    exact one_ne_zero (ofAdd_eq_one.mp this)
  have := Finite.of_injective coord hinj
  exact not_finite ℕ

end TauCeti
