/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Finiteness
import Mathlib.FieldTheory.Galois.Profinite
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import TauCeti.Topology.Algebra.Group.OpenSubgroup.BoundedIndex
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Finiteness of `H¹(G_{K,S}, M)`

Let `K` be a number field, `Ω` a normal extension of `K`, such as a separable closure, and `S` a
finite set of finite places of `K`. This file proves that the first continuous cohomology group
`H¹(G_{K,S}, M)` of the Galois group `G_{K,S} = Gal(K_S / K)` of the maximal extension unramified
outside `S` is finite for every finite discrete `G_{K,S}`-module `M`, of any order
(`TauCeti.RestrictedRamification.finite_H1_galoisGroupS`).

The arithmetic input is Hermite's theorem: an open subgroup of `G_{K,S}` of index at most `n` is
the fixing subgroup of a subextension of `K_S` of degree at most `n`, which is unramified outside
`S`, so there are only finitely many such subgroups
(`TauCeti.RestrictedRamification.finite_setOf_isOpen_index_le`). The same holds for an open
subgroup `V` of `G_{K,S}`, so `V` has only finitely many continuous homomorphisms to a finite
group. The kernel `V` of the action on `M` is open and normal, and
`TauCeti.ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal_of_prime` reduces
the finiteness of `H¹(G_{K,S}, M)` to that of `H¹(V, A) = Hom_cont(V, A)` for the trivial
`V`-modules `A` of prime order.

## Main results

* `TauCeti.RestrictedRamification.finite_setOf_isOpen_index_le`: `G_{K,S}` has only finitely
  many open subgroups of index at most `n`.
* `TauCeti.RestrictedRamification.finite_continuousMonoidHom`: an open subgroup of `G_{K,S}` has
  only finitely many continuous homomorphisms to a finite group.
* `TauCeti.RestrictedRamification.finite_H1_galoisGroupS`: `H¹(G_{K,S}, M)` is finite for every
  finite discrete `G_{K,S}`-module `M`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4, Lemma 4.9.
-/

public section

open IntermediateField IsDedekindDomain Module

open scoped NumberField

namespace TauCeti.RestrictedRamification

universe u

variable {K : Type*} {Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

/-- **Open subgroups of bounded index of `G_{K,S}`.** For `Ω / K` normal and `S` finite, the
group `G_{K,S}` has only finitely many open subgroups of index at most `n`. -/
theorem finite_setOf_isOpen_index_le [Normal K Ω] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) (n : ℕ) :
    {W : Subgroup (galoisGroupS K Ω S) | IsOpen (W : Set (galoisGroupS K Ω S)) ∧
      W.index ≤ n}.Finite := by
  -- such a subgroup is the fixing subgroup of a subextension of `K_S` of degree at most `n`, and
  -- by Hermite's theorem there are only finitely many of these
  -- `W ↦ fixedField W`, read in `Ω`, is injective on closed subgroups
  let φ : Subgroup (galoisGroupS K Ω S) → IntermediateField K Ω := fun W ↦ lift (fixedField W)
  refine Set.Finite.of_finite_image (f := φ)
    ((finite_unramifiedOutside_of_finrank_le (Ω := Ω) S hS n).subset ?_) fun W hW W' hW' h ↦ ?_
  · rintro _ ⟨W, hW, rfl⟩
    have hc := TauCeti.fixingSubgroup_fixedField (Subgroup.isClosed_of_isOpen W hW.1)
    have hfin : FiniteDimensional K (fixedField W) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by
        rw [hc]
        exact hW.1)
    have hrank : finrank K (φ W) = finrank K (fixedField W) :=
      (liftAlgEquiv (fixedField W)).toLinearEquiv.finrank_eq.symm
    have : FiniteDimensional K (φ W) :=
      (liftAlgEquiv (fixedField W)).toLinearEquiv.finiteDimensional
    refine ⟨this, ?_, le_maxUnramifiedOutside_iff.1 (lift_le _)⟩
    rw [hrank, finrank_eq_fixingSubgroup_index, hc]
    exact hW.2
  · rw [← TauCeti.fixingSubgroup_fixedField (Subgroup.isClosed_of_isOpen W hW.1),
      ← TauCeti.fixingSubgroup_fixedField (Subgroup.isClosed_of_isOpen W' hW'.1),
      lift_injective _ h]

/-- **Finitely many continuous homomorphisms to a finite group.** For `Ω / K` normal and `S`
finite, an open subgroup `V` of `G_{K,S}` has only finitely many continuous homomorphisms to a
finite discrete group `Q`, by Hermite's theorem. -/
theorem finite_continuousMonoidHom [Normal K Ω] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) {V : Subgroup (galoisGroupS K Ω S)} (hV : IsOpen (V : Set (galoisGroupS K Ω S)))
    (Q : Type*) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q] :
    Finite (V →ₜ* Q) :=
  have : V.FiniteIndex := OpenSubgroup.finiteIndex_toSubgroup ⟨V, hV⟩
  finite_continuousMonoidHom_of_finite_setOf_isOpen_index_le
    (finite_setOf_isOpen_index_le_of_isOpen hV _
      ((finite_setOf_isOpen_index_le S hS _).subset fun _ hW ↦ ⟨hW.1, hW.2.2⟩))

/-- **Finiteness of `H¹(G_{K,S}, M)`.** For `Ω` a normal extension of the number field `K`, such as
a separable closure, `S` a finite set of finite places of `K` and `M` a finite discrete
`G_{K,S}`-module, of any order, the continuous cohomology group `H¹(G_{K,S}, M)` is finite. -/
theorem finite_H1_galoisGroupS [Normal K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (M : Type u) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (galoisGroupS K Ω S) M] [ContinuousSMul (galoisGroupS K Ω S) M] :
    Finite (continuousCohomology 1 (ofDiscreteModule ℤ (galoisGroupS K Ω S) M)) := by
  -- the kernel `V` of the action is an open normal subgroup
  let V : Subgroup (galoisGroupS K Ω S) := (MulAction.toPermHom _ M).ker
  have hVmem (g : galoisGroupS K Ω S) : g ∈ V ↔ ∀ m : M, g • m = m := by
    simp [V, MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  have hV : IsOpen (V : Set (galoisGroupS K Ω S)) := isOpen_ker_toPermHom (galoisGroupS K Ω S) M
  have : V.FiniteIndex := OpenSubgroup.finiteIndex_toSubgroup ⟨V, hV⟩
  refine ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal_of_prime hV 1
    (N := Nat.card M) ?_ M (fun a ↦ card_nsmul_eq_zero') fun v hv a ↦ (hVmem v).1 hv a
  intro j hj₀ hj A _ _ _ _ _ _ _ _ htriv
  obtain rfl : j = 1 := by omega
  -- `H¹(V, A) = Hom_cont(V, A)` is finite, by Hermite's theorem
  have := finite_continuousMonoidHom S hS hV (Multiplicative A)
  exact Finite.of_equiv _ ((ContCohomology.H1EquivOfSmulEqSelf htriv).symm.trans
    (ContCohomology.explicitH1AddEquivContinuousCohomology V A)).toEquiv

end TauCeti.RestrictedRamification
