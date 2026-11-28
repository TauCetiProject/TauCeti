/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.Algebra.MonoidAlgebra.GroupCompletion
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.MonoidAlgebra.Localization
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Krull dimension of affine semigroup and Laurent group algebras

Over a field `k`, the Laurent group algebra `k[L]` of a finitely generated free abelian group `L`
has Krull dimension `Module.finrank ℤ L` (`AddMonoidAlgebra.ringKrullDim_of_free`). More generally,
if `f : M →+ H` embeds a finitely generated `UniqueSums` monoid `M` into a finitely generated free
abelian group `H` such that `H` shifts into `f '' M`, then `ringKrullDim k[M] = Module.finrank ℤ H`
(`AddMonoidAlgebra.ringKrullDim_of_exists_add_eq`). In particular, for any finitely generated
submonoid `S` of a torsion-free abelian group `G`,
`ringKrullDim k[S] = Module.finrank ℤ (AddSubgroup.closure S)`
(`AddSubmonoid.FG.ringKrullDim_addMonoidAlgebra`).

## Main declarations

* `AddMonoidAlgebra.ringKrullDim_of_free`: Krull dimension of `k[L]` for finite-rank free `L`.
* `AddMonoidAlgebra.ringKrullDim_of_exists_add_eq`: Krull dimension of `k[M]` from a localization
  into a finite-rank free group `k[H]`.
* `AddSubmonoid.FG.ringKrullDim_addMonoidAlgebra`: Krull dimension of `k[S]` for finitely
  generated `S` in a torsion-free abelian group.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapters 2 and 4.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Chapter 7.
-/

public section

namespace AddMonoidAlgebra

/-- Over a field `k`, the Laurent group algebra `k[L]` of a finitely generated free abelian group
`L` has Krull dimension `Module.finrank ℤ L`. -/
theorem ringKrullDim_of_free (k L : Type*) [Field k] [AddCommGroup L] [Module.Finite ℤ L]
    [Module.Free ℤ L] :
    ringKrullDim (AddMonoidAlgebra k L) = Module.finrank ℤ L := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let castHom : (ι →₀ ℕ) →+ (ι →₀ ℤ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  have hcast_inj : Function.Injective castHom :=
    Finsupp.mapRange_injective (Nat.castAddMonoidHom ℤ) (map_zero _) Nat.cast_injective
  have hshift (g : ι →₀ ℤ) : ∃ a c : ι →₀ ℕ, g + castHom c = castHom a := by
    refine ⟨g.mapRange (fun z ↦ z.toNat) rfl, g.mapRange (fun z ↦ (-z).toNat) rfl, ?_⟩
    ext i
    simp only [Finsupp.add_apply, castHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_apply, Nat.coe_castAddMonoidHom]
    lia
  have : AddMonoid.FG (ι →₀ ℕ) := AddMonoid.fg_iff.2
    ⟨Set.range fun i : ι ↦ Finsupp.single i 1, eq_top_iff.2 fun f _ ↦ by
      refine f.induction_linear (zero_mem _) (fun _ _ ↦ add_mem) fun i n ↦ ?_
      have hn : Finsupp.single i n = n • Finsupp.single i 1 := by ext j; simp [Finsupp.single_apply]
      exact hn ▸ nsmul_mem (AddSubmonoid.subset_closure (Set.mem_range_self i)) n,
      Set.finite_range _⟩
  obtain ⟨u, hu⟩ := exists_isLocalization_away_of_exists_add_eq hcast_inj hshift k
  let := (mapDomainRingHom k castHom).toAlgebra
  have hdim : ringKrullDim (AddMonoidAlgebra k (ι →₀ ℤ)) = Nat.card ι := by
    rw [TauCeti.ringKrullDim_localization_away (A := MvPolynomial ι k) k
      (single_ne_zero.2 (one_ne_zero : (1 : k) ≠ 0) : (single u (1 : k) : MvPolynomial ι k) ≠ 0)
      (AddMonoidAlgebra k (ι →₀ ℤ)),
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add]
  rw [ringKrullDim_eq_of_ringEquiv (domCongr k k b.repr.toAddEquiv).toRingEquiv, hdim,
    Module.finrank_eq_nat_card_basis b]

/-- Over a field `k`, if `f : M →+ H` is an injective additive homomorphism from a finitely
generated commutative monoid `M` with `UniqueSums M` into a finitely generated free abelian group
`H` such that every element of `H` shifts into `f '' M`, then `k[M]` has Krull dimension
`Module.finrank ℤ H`. -/
theorem ringKrullDim_of_exists_add_eq {M H : Type*} [AddCommMonoid M] [AddMonoid.FG M]
    [UniqueSums M] [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
    {f : M →+ H} (hf : Function.Injective f) (hshift : ∀ g : H, ∃ a b : M, g + f b = f a)
    (k : Type*) [Field k] : ringKrullDim (AddMonoidAlgebra k M) = Module.finrank ℤ H := by
  have : Algebra.FiniteType k (AddMonoidAlgebra k M) := AddMonoidAlgebra.finiteType_of_fg k M
  obtain ⟨u, _⟩ := exists_isLocalization_away_of_exists_add_eq hf hshift k
  let := (mapDomainRingHom k f).toAlgebra
  rw [← TauCeti.ringKrullDim_localization_away k
    (single_ne_zero.2 (one_ne_zero : (1 : k) ≠ 0) : single u (1 : k) ≠ 0)
    (AddMonoidAlgebra k H), ringKrullDim_of_free k H]

end AddMonoidAlgebra

namespace AddSubmonoid

open AddMonoidAlgebra

/-- Over a field `k`, the semigroup algebra `k[S]` of a finitely generated submonoid `S` of a
torsion-free abelian group `G` has Krull dimension `Module.finrank ℤ (AddSubgroup.closure S)`. -/
theorem FG.ringKrullDim_addMonoidAlgebra {G : Type*} [AddCommGroup G] [HasUniqueDiv G]
    {S : AddSubmonoid G} (hS : S.FG) (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k S) = Module.finrank ℤ (AddSubgroup.closure (S : Set G)) := by
  let L := AddSubgroup.closure (S : Set G)
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : UniqueSums S := .of_injective_addHom S.subtype.toAddHom S.subtype_injective inferInstance
  have : Module.Finite ℤ L := Module.Finite.iff_addGroup_fg.2
    ((AddGroup.fg_iff_addSubgroup_fg L).2 hS.addSubgroupClosure)
  exact AddMonoidAlgebra.ringKrullDim_of_exists_add_eq S.toGroupClosure_injective
    S.exists_add_toGroupClosure_eq k

end AddSubmonoid
