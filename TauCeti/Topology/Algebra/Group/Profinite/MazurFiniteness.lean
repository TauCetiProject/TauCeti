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
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RingTheory.Finiteness.Cardinality
import TauCeti.Topology.Algebra.Group.OpenSubgroup.BoundedIndex
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Mazur's finiteness condition `Φ_p`

A profinite group `G` satisfies **Mazur's finiteness condition** `Φ_p` at a prime `p` if every
open subgroup `U` of `G` has only finitely many continuous homomorphisms `U → 𝔽_p`. This is the
group-theoretic finiteness hypothesis on deformations of a continuous residual representation `ρbar`
of `G` over a finite field `k` of characteristic `p`: under it the framed deformation (lifting)
functor is representable by a Noetherian ring, and the unframed deformation functor has a
Noetherian hull, which represents it when `End_k(ρbar) = k`. Over `k`, the tangent space of the
lifting functor of the trivial rank-one representation of `U` is
`Hom_cont(U, k) = Hom_cont(U, 𝔽_p) ⊗ k`, and the open subgroups enter through the kernel of the
residual representation.

The condition quantifies over every open subgroup, not only over `G` itself. A group can have no
nonzero continuous homomorphism to `𝔽_p` while an open subgroup has infinitely many: for odd `p`
the semidirect product of `∏_ℕ ℤ/p` by an involution acting by inversion, with the product
topology, is an example
(`TauCeti.subsingleton_continuousZModDual_and_not_mazurFiniteness_semidirectProduct_pi_zmod_inv`).

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
* `TauCeti.MazurFiniteness.of_surjective`, `ContinuousMulEquiv.mazurFiniteness_iff`: `Φ_p` passes to
  continuous surjective images, so it is invariant under topological group isomorphisms.
* `TauCeti.mazurFiniteness_iff_forall_isTopologicallyFinitelyGenerated_maximalProPQuotient`: a
  profinite group satisfies `Φ_p` exactly when the maximal pro-`p` quotient of each of its open
  subgroups is topologically finitely generated.
* `TauCeti.IsTopologicallyFinitelyGenerated.mazurFiniteness`: a topologically finitely generated
  compact group satisfies `Φ_p`.
* `TauCeti.mazurFiniteness_of_finite_setOf_isOpen_index_le`: a compact group with finitely many
  open subgroups of each bounded index satisfies `Φ_p`.
* `TauCeti.mazurFiniteness_of_finite`, `TauCeti.mazurFiniteness_multiplicative_padicInt`: finite
  groups and the additive group of `ℤ_p` satisfy `Φ_p`.
* `TauCeti.not_mazurFiniteness_pi_zmod`: the countable power of `ℤ/p` does not satisfy `Φ_p`.
* `TauCeti.subsingleton_continuousZModDual_semidirectProduct_zpowers_inv`,
  `TauCeti.not_mazurFiniteness_semidirectProduct_pi_zmod`: for odd `p` the semidirect product of
  `∏_ℕ ℤ/p` by inversion has no nonzero continuous `ZMod p`-character, yet does not satisfy `Φ_p`
  for any topology on it in which `∏_ℕ ℤ/p` is open and the projection to it is continuous.
* `TauCeti.subsingleton_continuousZModDual_and_not_mazurFiniteness_semidirectProduct_pi_zmod_inv`:
  for odd `p`, that semidirect product with the product topology, discrete on the acting group, has
  no nonzero continuous `ZMod p`-character and does not satisfy `Φ_p`.

## References

* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publications 16
  (1989), Section 1.1.
* T. Gee, *Modularity lifting theorems*, Essential Number Theory 1 (2022), Section 3.1.
* M. Kisin, *Lectures on deformations of Galois representations*, Lecture 1, (1.2) and Exercise 1,
  https://people.math.harvard.edu/~kisin/notes/notes.pdf.
-/

public section

namespace TauCeti

universe u

/-- **Mazur's finiteness condition `Φ_p`.** Every open subgroup `U` of the topological group `G`
has only finitely many continuous homomorphisms `U → ZMod p`. For a prime `p` and a profinite `G`
this is the finiteness input under which framed deformation (lifting) functors of residual
representations of `G` over finite fields of characteristic `p` are representable by Noetherian
rings; unframed ones have Noetherian hulls, representable when `End_k(ρbar) = k`. -/
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
  .of_injective _ (ContinuousMonoidHom.continuousZModDualMap_injective_of_surjective
    (f := ⟨(⊤ : Subgroup G).subtype, continuous_subtypeVal⟩) fun g ↦ ⟨⟨g, trivial⟩, rfl⟩)

/-- **`Φ_p` passes to open subgroups.** An open subgroup of an open subgroup `U` of `G` is an open
subgroup of `G`, through the inclusion of `U`. -/
theorem MazurFiniteness.openSubgroup (h : MazurFiniteness p G) (U : OpenSubgroup G) :
    MazurFiniteness p U.toSubgroup := by
  intro V
  let W : Subgroup G := V.toSubgroup.map U.toSubgroup.subtype
  have hW : IsOpen (W : Set G) := by
    rw [Subgroup.coe_map]
    exact U.isOpen.isOpenMap_subtypeVal _ V.isOpen
  have hWU : W ≤ U.toSubgroup := Subgroup.map_subtype_le _
  have : Finite (continuousZModDual p W) := h ⟨W, hW⟩
  have hfin : Finite (continuousZModDual p (W.subgroupOf U.toSubgroup)) :=
    Finite.of_injective _
      (Subgroup.subgroupOfContinuousMulEquivOfLe hWU).symm.continuousZModDualMap_bijective.1
  rwa [← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)] at hfin

/-- **`Φ_p` passes to continuous surjective images.** An open subgroup `V` of `H` pulls back along
`f` to an open subgroup of `G` which `f` maps onto `V`, and characters of `V` pull back injectively
along this surjection. -/
theorem MazurFiniteness.of_surjective {H : Type*} [Group H] [TopologicalSpace H]
    (h : MazurFiniteness p G) (f : G →ₜ* H) (hf : Function.Surjective f) :
    MazurFiniteness p H := fun V ↦
  have : Finite (continuousZModDual p (V.toSubgroup.comap f.toMonoidHom)) :=
    h (V.comap f.toMonoidHom f.continuous)
  .of_injective _ (ContinuousMonoidHom.continuousZModDualMap_injective_of_surjective
    (f := ⟨f.toMonoidHom.subgroupComap V.toSubgroup, f.continuous.comp continuous_subtypeVal
      |>.subtype_mk _⟩) (f.toMonoidHom.subgroupComap_surjective V.toSubgroup hf))

/-- **`Φ_p` is invariant under topological group isomorphisms.** -/
theorem _root_.ContinuousMulEquiv.mazurFiniteness_iff {H : Type*} [Group H] [TopologicalSpace H]
    (e : G ≃ₜ* H) : MazurFiniteness p G ↔ MazurFiniteness p H :=
  ⟨fun h ↦ h.of_surjective e e.surjective, fun h ↦ h.of_surjective e.symm e.symm.surjective⟩

section NeZero

variable [NeZero p]

/-- **`Φ_p` in terms of dimensions.** Over the finite ring `ZMod p`, for instance the field `𝔽_p`,
finiteness of the continuous `ZMod p`-dual of each open subgroup is its finiteness as a module. -/
theorem mazurFiniteness_iff_forall_moduleFinite :
    MazurFiniteness p G ↔
      ∀ U : OpenSubgroup G, Module.Finite (ZMod p) (continuousZModDual p U.toSubgroup) :=
  forall_congr' fun _ ↦ Module.finite_iff_finite.symm

/-- **Finite groups satisfy `Φ_p`.** A continuous homomorphism is determined by its values, and
there are only finitely many functions from a finite group to `ZMod p`. No hypothesis on the
topology is needed. -/
theorem mazurFiniteness_of_finite [Finite G] : MazurFiniteness p G := fun U ↦
  Finite.of_injective (β := U.toSubgroup → Multiplicative (ZMod p)) (fun χ ↦ ⇑χ.toMul)
    fun _ _ h ↦ Additive.toMul.injective (DFunLike.coe_injective h)

/-- A compact group with separately continuous multiplication and finitely many open subgroups
of each bounded finite index satisfies `Φ_p`. The bounded-index finiteness passes to each open
subgroup by `finite_setOf_isOpen_index_le_of_isOpen`. -/
theorem mazurFiniteness_of_finite_setOf_isOpen_index_le [SeparatelyContinuousMul G] [CompactSpace G]
    (h : ∀ n, {H : Subgroup G | IsOpen (H : Set G) ∧ H.FiniteIndex ∧ H.index ≤ n}.Finite) :
    MazurFiniteness p G :=
  mazurFiniteness_iff_forall_finite.mpr fun U ↦
    finite_continuousMonoidHom_of_finite_setOf_isOpen_index_le
      (finite_setOf_isOpen_index_le_of_isOpen U.isOpen _ (h _))

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
  rw [← isProP_maximalProPQuotient.finite_continuousZModDual_iff, Module.finite_iff_finite]
  exact ⟨fun _ ↦ .of_injective _ hbij.1, fun _ ↦ .of_surjective _ hbij.2⟩

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
    Additive.ofMul (ContinuousMonoidHom.proj i)
  have hinj : Function.Injective coord := fun i j hij ↦ by
    by_contra hne
    have := DFunLike.congr_fun (congrArg Additive.toMul hij) (Pi.mulSingle i (.ofAdd 1))
    simp only [coord, toMul_ofMul, ContinuousMonoidHom.proj_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (Ne.symm hne)] at this
    exact one_ne_zero (ofAdd_eq_one.mp this)
  have := Finite.of_injective coord hinj
  exact not_finite ℕ

section SemidirectProduct

/-- **A semidirect product by inversion has no nonzero `ℤ/p`-characters for odd `p`.** Let `N` be
a commutative group and let the subgroup generated by inversion act on it. A homomorphism to
`ZMod p` takes the same value at `n` and at its conjugate `n⁻¹`, and the same value at `σ` and at
`σ⁻¹ = σ`, so twice each value vanishes, and `2` is a unit in `ZMod p`. This holds for every
topology on the semidirect product. -/
theorem subsingleton_continuousZModDual_semidirectProduct_zpowers_inv {N : Type*} [CommGroup N]
    [TopologicalSpace
      (N ⋊[(Subgroup.zpowers (MulEquiv.inv N)).subtype] Subgroup.zpowers (MulEquiv.inv N))]
    (hp : Odd p) :
    Subsingleton (continuousZModDual p
      (N ⋊[(Subgroup.zpowers (MulEquiv.inv N)).subtype] Subgroup.zpowers (MulEquiv.inv N))) := by
  have h2 : IsUnit (2 : ZMod p) := by
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 p).mpr (Nat.coprime_two_left.mpr hp)
  -- every element of the acting group is an involution
  have hσ (s : Subgroup.zpowers (MulEquiv.inv N)) : s * s = 1 := by
    obtain ⟨_, k, rfl⟩ := s
    have hinv : MulEquiv.inv N * MulEquiv.inv N = 1 := MulEquiv.ext fun _ ↦ inv_inv _
    ext1
    simp [← zpow_add, ← two_mul, zpow_mul, sq, hinv]
  -- twice every value of a character vanishes
  have hsq (χ : continuousZModDual p
      (N ⋊[(Subgroup.zpowers (MulEquiv.inv N)).subtype] Subgroup.zpowers (MulEquiv.inv N))) g :
      χ.toMul g * χ.toMul g = 1 := by
    have hl (n : N) : χ.toMul (.inl n) * χ.toMul (.inl n) = 1 := by
      have := congrArg χ.toMul
        (SemidirectProduct.inl_aut ⟨MulEquiv.inv N, Subgroup.mem_zpowers _⟩ n)
      simp only [Subgroup.coe_subtype, MulEquiv.inv_apply, map_inv, map_mul,
        mul_inv_cancel_comm] at this
      exact inv_eq_iff_mul_eq_one.mp this
    have hr (s : Subgroup.zpowers (MulEquiv.inv N)) :
        χ.toMul (.inr s) * χ.toMul (.inr s) = 1 := by
      rw [← map_mul, ← map_mul, hσ, map_one, map_one]
    rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul, mul_mul_mul_comm, hl, hr, one_mul]
  refine ⟨fun χ ψ ↦ ?_⟩
  suffices key : ∀ χ : continuousZModDual p
      (N ⋊[(Subgroup.zpowers (MulEquiv.inv N)).subtype] Subgroup.zpowers (MulEquiv.inv N)),
      χ = 0 from (key χ).trans (key ψ).symm
  refine fun χ ↦ Additive.toMul.injective (ContinuousMonoidHom.ext fun g ↦ ?_)
  have := congrArg Multiplicative.toAdd (hsq χ g)
  rw [toAdd_mul, toAdd_one, ← two_mul, h2.mul_right_eq_zero] at this
  exact Multiplicative.toAdd.injective this

/-- **`Φ_p` of a semidirect product passes to the normal factor**, when the normal factor is open
and the projection to it is continuous, as for the product topology. -/
theorem MazurFiniteness.semidirectProduct_left {N H : Type*} [Group N] [Group H]
    [TopologicalSpace N] {φ : H →* MulAut N} [TopologicalSpace (N ⋊[φ] H)]
    (h : MazurFiniteness p (N ⋊[φ] H))
    (hN : IsOpen ((SemidirectProduct.inl.range : Subgroup (N ⋊[φ] H)) : Set (N ⋊[φ] H)))
    (hl : Continuous fun g : N ⋊[φ] H ↦ g.left) : MazurFiniteness p N :=
  (h.openSubgroup ⟨_, hN⟩).of_surjective
    ⟨(MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).symm.toMonoidHom,
      (hl.comp continuous_subtypeVal).congr fun g ↦
        (congrArg SemidirectProduct.left
          (MonoidHom.apply_ofInjective_symm (SemidirectProduct.inl_injective (φ := φ)) g)).symm⟩
    (MulEquiv.surjective _)

/-- **`Φ_p` is not a condition on `G` alone.** No semidirect product of `∏_ℕ ℤ/p` satisfies `Φ_p`
for a topology in which `∏_ℕ ℤ/p` is open and the projection to it is continuous, such as the
product topology of
`TauCeti.subsingleton_continuousZModDual_and_not_mazurFiniteness_semidirectProduct_pi_zmod_inv`.
For odd `p` and the involution acting by inversion such a group has no
nonzero continuous character to `ZMod p`, by
`TauCeti.subsingleton_continuousZModDual_semidirectProduct_zpowers_inv`, so a definition quantifying
only over `G` would accept it. -/
theorem not_mazurFiniteness_semidirectProduct_pi_zmod (p : ℕ) [Fact (1 < p)] {H : Type*} [Group H]
    {φ : H →* MulAut (ℕ → Multiplicative (ZMod p))}
    [TopologicalSpace ((ℕ → Multiplicative (ZMod p)) ⋊[φ] H)]
    (hN : IsOpen ((SemidirectProduct.inl.range : Subgroup ((ℕ → Multiplicative (ZMod p)) ⋊[φ] H)) :
      Set ((ℕ → Multiplicative (ZMod p)) ⋊[φ] H)))
    (hl : Continuous fun g : (ℕ → Multiplicative (ZMod p)) ⋊[φ] H ↦ g.left) :
    ¬ MazurFiniteness p ((ℕ → Multiplicative (ZMod p)) ⋊[φ] H) := fun h ↦
  not_mazurFiniteness_pi_zmod p (h.semidirectProduct_left hN hl)

/-- **`Φ_p` is not a condition on `G` alone: the semidirect product of `∏_ℕ ℤ/p` by inversion.**
Give `∏_ℕ ℤ/p` its product topology, the group generated by inversion the discrete topology, and
the semidirect product the product topology through `SemidirectProduct.equivProd`. For odd `p` this
group has no nonzero continuous character to `ZMod p`, yet its open subgroup `∏_ℕ ℤ/p` has
infinitely many, so it does not satisfy `Φ_p`. -/
theorem subsingleton_continuousZModDual_and_not_mazurFiniteness_semidirectProduct_pi_zmod_inv
    (p : ℕ) [Fact (1 < p)] (hp : Odd p) :
    let : TopologicalSpace (Subgroup.zpowers (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))) := ⊥
    let : TopologicalSpace ((ℕ → Multiplicative (ZMod p)) ⋊[(Subgroup.zpowers
        (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))).subtype]
        Subgroup.zpowers (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))) :=
      .induced SemidirectProduct.equivProd inferInstance
    Subsingleton (continuousZModDual p ((ℕ → Multiplicative (ZMod p)) ⋊[(Subgroup.zpowers
        (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))).subtype]
        Subgroup.zpowers (MulEquiv.inv (ℕ → Multiplicative (ZMod p))))) ∧
      ¬ MazurFiniteness p ((ℕ → Multiplicative (ZMod p)) ⋊[(Subgroup.zpowers
        (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))).subtype]
        Subgroup.zpowers (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))) := by
  intro _ _
  have : DiscreteTopology (Subgroup.zpowers (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))) := ⟨rfl⟩
  have he : Continuous (SemidirectProduct.equivProd (φ := (Subgroup.zpowers
      (MulEquiv.inv (ℕ → Multiplicative (ZMod p)))).subtype)) := continuous_induced_dom
  refine ⟨subsingleton_continuousZModDual_semidirectProduct_zpowers_inv hp,
    not_mazurFiniteness_semidirectProduct_pi_zmod p ?_ (continuous_fst.comp he)⟩
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage (continuous_snd.comp he)

end SemidirectProduct

end TauCeti
