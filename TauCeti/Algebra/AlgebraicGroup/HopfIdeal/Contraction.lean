/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Noetherian

/-!
# Contraction of Hopf ideals along a base change

Let `H` be a commutative Hopf algebra over `k`, the coordinate ring of an affine group `G`, and
let `k → K` be a ring map. A closed subgroup of `G` is cut out by a Hopf ideal `I` of `H`, and
its base change `G_K` is cut out by the Hopf ideal `I_K` of `K ⊗[k] H`
(`TauCeti.CommHopfAlgCat.baseChangeHopfIdeal`). This file constructs the right adjoint of
`I ↦ I_K`: for a Hopf ideal `J` of `K ⊗[k] H`, the **contraction**
`TauCeti.CommHopfAlgCat.contractHopfIdeal J` is the largest Hopf ideal of `H` whose base change
is contained in `J`. Contravariantly, it cuts out the smallest closed subgroup of `G`, defined
over `k`, whose base change to `K` contains the closed subgroup of `G_K` cut out by `J`.

The contraction is defined as a supremum of Hopf ideals, so no ring-theoretic contraction of `J`
has to be shown to be a Hopf ideal. Taking `J` to be the common kernel of a family of morphisms
out of `K ⊗[k] H` gives the smallest closed `k`-subgroup through whose base change every member
of the family factors. For the real extension of an algebraic group over `ℚ` and a homomorphism
from the Deligne torus this is the Mumford–Tate group.

## Main declarations

* `TauCeti.CommHopfAlgCat.contractHopfIdeal`: the largest Hopf ideal whose base change lies in a
  given Hopf ideal of the base change.
* `TauCeti.CommHopfAlgCat.gc_baseChangeHopfIdeal_contractHopfIdeal`: base change and contraction
  form a Galois connection, so `I ≤ contractHopfIdeal J ↔ I_K ≤ J`
  (`TauCeti.CommHopfAlgCat.le_contractHopfIdeal_iff`).
* `TauCeti.CommHopfAlgCat.contractHopfIdeal_baseChangeHopfIdeal`: along a faithfully flat base
  change, the contraction of `I_K` is `I`.
* `TauCeti.CommHopfAlgCat.contractHopfIdeal_eq_augmentation_iff`: the contraction cuts out the
  trivial subgroup exactly when `J` contains the augmentation ideal.
* `TauCeti.CommHopfAlgCat.contractHopfIdeal_toIdeal_le_ker`: a morphism defined over `k` whose
  base change kills `J` kills the contraction of `J`, when `k → K` is injective and the target
  is flat over `k`.
* `TauCeti.CommHopfAlgCat.comapOfSurjective_contractHopfIdeal`: contraction commutes with
  pulling back along an isomorphism of Hopf algebras.
* `TauCeti.CommHopfAlgCat.exists_finset_sup_eq_contractHopfIdeal`: for noetherian `H`, the
  contraction is the supremum of finitely many Hopf ideals whose base changes lie in `J`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 1, for closed subgroups and their base
  change.
* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31, and P. Deligne,
  *Hodge cycles on abelian varieties*, §3, for the Mumford–Tate group as the smallest
  `ℚ`-subgroup whose real extension contains the image of the Deligne torus.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

open _root_.CommHopfAlgCat

universe u v w y

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]
variable {H L : _root_.CommHopfAlgCat.{v} k}

/-- **The contraction of a Hopf ideal along `k → K`**: the largest Hopf ideal of `H` whose base
change to `K` is contained in the Hopf ideal `J` of `K ⊗[k] H`.

Contravariantly, it cuts out the smallest closed subgroup defined over `k` whose base change
contains the closed subgroup cut out by `J`. It is right adjoint to base change
(`TauCeti.CommHopfAlgCat.gc_baseChangeHopfIdeal_contractHopfIdeal`). -/
noncomputable def contractHopfIdeal (J : HopfIdeal K (baseChange (K := K) H)) : HopfIdeal k H :=
  sSup {I | baseChangeHopfIdeal (K := K) I ≤ J}

/-- The base change of the contraction of `J` is contained in `J`. -/
theorem baseChangeHopfIdeal_contractHopfIdeal_le (J : HopfIdeal K (baseChange (K := K) H)) :
    baseChangeHopfIdeal (K := K) (contractHopfIdeal J) ≤ J := by
  rw [← HopfIdeal.toIdeal_le_toIdeal, baseChangeHopfIdeal_toIdeal, contractHopfIdeal,
    HopfIdeal.sSup_toIdeal, Ideal.map_iSup]
  refine iSup_le fun I ↦ ?_
  rw [← baseChangeHopfIdeal_toIdeal]
  exact HopfIdeal.toIdeal_le_toIdeal.mpr I.property

/-- **Base change and contraction of Hopf ideals form a Galois connection**: a Hopf ideal lies
below the contraction of `J` exactly when its base change lies below `J`. -/
theorem gc_baseChangeHopfIdeal_contractHopfIdeal :
    GaloisConnection (baseChangeHopfIdeal (K := K) : HopfIdeal k H → _) contractHopfIdeal :=
  fun _ J ↦ ⟨fun h ↦ le_sSup h,
    fun h ↦ (baseChangeHopfIdeal_mono h).trans (baseChangeHopfIdeal_contractHopfIdeal_le J)⟩

/-- A Hopf ideal lies below the contraction of `J` exactly when its base change lies below `J`. -/
theorem le_contractHopfIdeal_iff {I : HopfIdeal k H} {J : HopfIdeal K (baseChange (K := K) H)} :
    I ≤ contractHopfIdeal J ↔ baseChangeHopfIdeal (K := K) I ≤ J :=
  (gc_baseChangeHopfIdeal_contractHopfIdeal I J).symm

/-- Contraction of Hopf ideals is monotone. -/
theorem contractHopfIdeal_mono :
    Monotone (contractHopfIdeal : HopfIdeal K (baseChange (K := K) H) → HopfIdeal k H) :=
  gc_baseChangeHopfIdeal_contractHopfIdeal.monotone_u

/-- A Hopf ideal lies below the contraction of its own base change. -/
theorem le_contractHopfIdeal_baseChangeHopfIdeal (I : HopfIdeal k H) :
    I ≤ contractHopfIdeal (baseChangeHopfIdeal (K := K) I) :=
  le_contractHopfIdeal_iff.mpr le_rfl

/-- Along a faithfully flat base change, for instance a field extension, contracting the base
change of a Hopf ideal recovers it: a closed subgroup defined over `k` is the smallest closed
`k`-subgroup whose base change contains its own base change. -/
@[simp]
theorem contractHopfIdeal_baseChangeHopfIdeal [Module.FaithfullyFlat k K] (I : HopfIdeal k H) :
    contractHopfIdeal (baseChangeHopfIdeal (K := K) I) = I :=
  le_antisymm
    ((baseChangeHopfIdeal_le_iff_of_faithfullyFlat _ _).mp
      (baseChangeHopfIdeal_contractHopfIdeal_le _))
    (le_contractHopfIdeal_baseChangeHopfIdeal I)

/-- Along a faithfully flat base change, the contraction of the zero Hopf ideal is zero: the
smallest closed `k`-subgroup whose base change is the whole group is the whole group. -/
@[simp]
theorem contractHopfIdeal_bot [Module.FaithfullyFlat k K] :
    contractHopfIdeal (⊥ : HopfIdeal K (baseChange (K := K) H)) = ⊥ := by
  rw [← baseChangeHopfIdeal_bot (K := K) (H := H), contractHopfIdeal_baseChangeHopfIdeal]

/-- **The contraction cuts out the trivial subgroup exactly when `J` does**: the contraction of
`J` is the augmentation ideal of `H` if and only if `J` contains the augmentation ideal of
`K ⊗[k] H`. -/
theorem contractHopfIdeal_eq_augmentation_iff (J : HopfIdeal K (baseChange (K := K) H)) :
    contractHopfIdeal J = HopfIdeal.augmentation k H ↔
      HopfIdeal.augmentation K (baseChange (K := K) H) ≤ J := by
  rw [← baseChangeHopfIdeal_augmentation, ← le_contractHopfIdeal_iff]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm (HopfIdeal.le_augmentation _ _ _) h⟩

/-- A Hopf ideal lies below the contraction of the common kernel of a family of morphisms out of
`K ⊗[k] H` exactly when every member of the family kills its base change. Contravariantly, the
contraction of the common kernel is the smallest closed `k`-subgroup through whose base change
every member of the family factors. -/
theorem le_contractHopfIdeal_commonKernelHopfIdeal_iff {ι : Type y}
    {N : ι → _root_.CommHopfAlgCat.{max w v} K} (f : ∀ i, baseChange (K := K) H ⟶ N i)
    (I : HopfIdeal k H) :
    I ≤ contractHopfIdeal (commonKernelHopfIdeal f) ↔
      ∀ i, (baseChangeHopfIdeal (K := K) I).toIdeal ≤ RingHom.ker (f i).hom.toAlgHom.toRingHom := by
  rw [le_contractHopfIdeal_iff, le_commonKernelHopfIdeal_iff]

/-- **Morphisms defined over `k`.** Suppose `k → K` is injective and `N` is flat over `k`. If the
base change of a morphism `f : H ⟶ N` kills `J`, then `f` kills the contraction of `J`.
Contravariantly, a homomorphism into `G` defined over `k` whose base change lands in the closed
subgroup cut out by `J` lands in the smallest closed `k`-subgroup containing it. -/
theorem contractHopfIdeal_toIdeal_le_ker (halg : Function.Injective (algebraMap k K))
    {N : _root_.CommHopfAlgCat.{v} k} [Module.Flat k N]
    (J : HopfIdeal K (baseChange (K := K) H)) (f : H ⟶ N)
    (hJ : J.toIdeal ≤ RingHom.ker (baseChangeMap (K := K) f).hom.toAlgHom.toRingHom) :
    (contractHopfIdeal J).toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom :=
  (baseChangeHopfIdeal_toIdeal_le_ker_baseChangeMap_iff halg _ f).mp
    ((HopfIdeal.toIdeal_le_toIdeal.mpr (baseChangeHopfIdeal_contractHopfIdeal_le J)).trans hJ)

/-- Pulling the contraction back along an isomorphism `e : H ≅ L` is contained in the contraction
of the pullback along the base change of `e`. -/
private theorem comapOfSurjective_contractHopfIdeal_le (J : HopfIdeal K (baseChange (K := K) L))
    (e : H ≅ L) :
    (contractHopfIdeal J).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 ≤
      contractHopfIdeal (J.comapOfSurjective (baseChangeMap (K := K) e.hom).hom
        (ConcreteCategory.bijective_of_isIso ((baseChangeFunctor (K := K)).mapIso e).hom).2) := by
  rw [le_contractHopfIdeal_iff, baseChangeHopfIdeal_comapOfIso]
  exact HopfIdeal.comapOfSurjective_mono _ _ (baseChangeHopfIdeal_contractHopfIdeal_le J)

/-- **Contraction is invariant under isomorphisms**: pulling the contraction of `J` back along an
isomorphism `e : H ≅ L` gives the contraction of the pullback of `J` along the base change of
`e`. Contravariantly, an isomorphism of affine groups over `k` carries the smallest closed
`k`-subgroup containing a closed `K`-subgroup to the smallest one containing its image. -/
theorem comapOfSurjective_contractHopfIdeal (J : HopfIdeal K (baseChange (K := K) L))
    (e : H ≅ L) :
    (contractHopfIdeal J).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      contractHopfIdeal (J.comapOfSurjective (baseChangeMap (K := K) e.hom).hom
        (ConcreteCategory.bijective_of_isIso ((baseChangeFunctor (K := K)).mapIso e).hom).2) := by
  let eK := (baseChangeFunctor (K := K)).mapIso e
  let J' := J.comapOfSurjective eK.hom.hom (ConcreteCategory.bijective_of_isIso eK.hom).2
  refine le_antisymm (comapOfSurjective_contractHopfIdeal_le J e) ?_
  -- Apply the inclusion to `e.symm`; pulling `J'` back along the base change of `e.symm` gives
  -- `J` again, and pulling back along `e.symm` and then `e` is the identity.
  have h : (contractHopfIdeal J').comapOfSurjective e.inv.hom
      (ConcreteCategory.bijective_of_isIso e.inv).2 ≤ contractHopfIdeal J :=
    (comapOfSurjective_contractHopfIdeal_le J' e.symm).trans_eq
      (congrArg contractHopfIdeal (comapOfSurjective_inv_hom eK.symm J))
  calc _ = ((contractHopfIdeal J').comapOfSurjective e.inv.hom
          (ConcreteCategory.bijective_of_isIso e.inv).2).comapOfSurjective e.hom.hom
            (ConcreteCategory.bijective_of_isIso e.hom).2 :=
        (comapOfSurjective_inv_hom e _).symm
    _ ≤ _ := HopfIdeal.comapOfSurjective_mono _ _ h

/-- **Finiteness of the contraction.** When `H` is noetherian, the contraction of `J` is the
supremum of finitely many Hopf ideals whose base changes lie in `J`. Contravariantly, the
smallest closed `k`-subgroup whose base change contains a given closed `K`-subgroup is the
intersection of finitely many closed `k`-subgroups with that property. -/
theorem exists_finset_sup_eq_contractHopfIdeal [IsNoetherianRing H]
    (J : HopfIdeal K (baseChange (K := K) H)) :
    ∃ t : Finset (HopfIdeal k H),
      (∀ I ∈ t, baseChangeHopfIdeal (K := K) I ≤ J) ∧ t.sup id = contractHopfIdeal J := by
  obtain ⟨t, ht, hsup⟩ :=
    HopfIdeal.exists_finset_sup_eq_sSup {I | baseChangeHopfIdeal (K := K) I ≤ J}
  exact ⟨t, fun I hI ↦ ht hI, hsup⟩

end TauCeti.CommHopfAlgCat
