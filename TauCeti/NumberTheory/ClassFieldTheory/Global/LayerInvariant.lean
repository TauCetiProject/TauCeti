/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Inflation
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation

/-!
# The local invariants of an idele layer and their sum

Let `K` be a number field and `L/F` a finite Galois layer inside `Kˢ`, cut out by open subgroups
`V ◁ U` of `G_K`. This file attaches to every class `x ∈ H²(Gal(L/F), I_L)` of the idele formation
`ideleFormation K` a local invariant at every place of `K`, and their sum. The class is carried to
the continuous cohomology of `G_K` by inflation to `U = G_F` and corestriction to `G_K`,

```text
ideleLayerCorInfl K L : H²(Gal(L/F), I_L) → H²(G_F, I_{Kˢ}) → H²(G_K, I_{Kˢ}),
```

and there it is localized at the places of `K` (`ideleBrLocalization`,
`ideleInfiniteBrLocalization`) and evaluated by the local invariants `invMap` and
`infiniteInvMap`:

* `ideleLocalInvAt K L v x ∈ ℚ/ℤ` at a finite place `v`, nonzero only at the finitely many places
  of `ideleSupport K L x`;
* `ideleInfiniteInvAt K L w x ∈ ℚ/ℤ` at an infinite place `w`;
* `ideleSumLocalInv K L x`, the sum of all of them: the sum of the local invariants
  `sumLocalInv K` of the family `ideleLocalization K (ideleLayerCorInfl K L x)` of local Brauer
  classes, computed over any finite set of finite places containing `ideleSupport K L x`
  (`ideleSumLocalInv_eq_sum`).

Inflation to a refinement `L'/F` of the layer does not change the class over `G_K`
(`ideleLayerCorInfl_cohomologyInfl`), so all of these are inflation-invariant
(`ideleSumLocalInv_infl`). Corestriction is what makes the invariants of a layer over `F` those
of places of `K`: classically, the invariant at `v` of a corestricted class is the sum of the
invariants at the places of `F` above `v`, so `ideleSumLocalInv K L` is the sum of the local
invariants over all places of `F`.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleLayerCorInfl K L`: the class over `G_K` of an idele-layer class.
* `TauCeti.ClassFieldTheory.ideleLocalInvAt K L v`,
  `TauCeti.ClassFieldTheory.ideleInfiniteInvAt K L w`: the local invariants of an idele-layer class
  at a finite place `v` and an infinite place `w`.
* `TauCeti.ClassFieldTheory.ideleSupport K L x`: the finite set of finite places where the local
  invariant of `x` is nonzero.
* `TauCeti.ClassFieldTheory.ideleSumLocalInv K L`: the sum of the local invariants.

## Main results

* `TauCeti.ClassFieldTheory.ideleLayerCorInfl_cohomologyInfl`: inflation to a refinement does not
  change the class over `G_K`.
* `TauCeti.ClassFieldTheory.ideleSumLocalInv_eq_sum`: the sum of the local invariants is a finite
  sum over any set of finite places containing the support, plus the archimedean invariants.
* `TauCeti.ClassFieldTheory.ideleSumLocalInv_infl`: the sum of the local invariants is
  inflation-invariant.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 and Chapter VIII, §4.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter VII (Tate, *Global
  Class Field Theory*), §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology

variable (K : Type) [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))

/-! ### The class over the absolute Galois group -/

/-- **The class over `G_K` of an idele-layer class**: for a layer `V ◁ U` of the idele formation,
inflation `H²(U ⧸ V, I_{Kˢ}^V) → H²(U, I_{Kˢ})` followed by corestriction from the open subgroup
`U` to `G_K`. -/
def ideleLayerCorInfl : L.H (ideleFormation K) 2 →+ H2 (AbsoluteGaloisGroup K) (IdeleCoeff K) :=
  (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) L.ground.toSubgroup L.ground.isOpen).comp
    (L.explicitInfl2 (ideleCoeffEquivIdeleFormation K) (ideleCoeffEquivIdeleFormation_smul K))

/-- The class over `G_K` of an idele-layer class is the corestriction of its inflation. -/
theorem ideleLayerCorInfl_apply (x : L.H (ideleFormation K) 2) :
    ideleLayerCorInfl K L x =
      explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) L.ground.toSubgroup L.ground.isOpen
        (L.explicitInfl2 (ideleCoeffEquivIdeleFormation K) (ideleCoeffEquivIdeleFormation_smul K)
          x) :=
  (rfl)

/-- **Inflation to a refinement does not change the class over `G_K`.** Both layers have the same
ground subgroup `U`, and corestriction from `U` does not see the identification of the two copies
of `U`. -/
@[simp]
theorem ideleLayerCorInfl_cohomologyInfl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (x : old.H (ideleFormation K) 2) :
    ideleLayerCorInfl K new (T.cohomologyInfl (ideleFormation K) 2 x) =
      ideleLayerCorInfl K old x := by
  rw [ideleLayerCorInfl_apply, ideleLayerCorInfl_apply, NormalLayer.explicitInfl2_cohomologyInfl]
  -- Reading a class of `U` on the same subgroup `U` is conjugation by `1`.
  exact explicitCor2_explicitMap2_of_conj old.ground.toSubgroup new.ground.toSubgroup
    (IdeleCoeff K) 1 _ (fun v ↦ by simp) (AddMonoidHom.id _) (fun m ↦ (one_smul _ m).symm)
    -- `(1 : MulAut G).toMonoidHom` is `MonoidHom.id G` by definition, so `Subgroup.map_id` applies.
    (by rw [map_one]; exact T.same_ground_toSubgroup.symm.trans (Subgroup.map_id _).symm)
    old.ground.isOpen new.ground.isOpen _

/-! ### The local invariants -/

/-- **The local invariant at a finite place** `v` of an idele-layer class: the invariant of the
nonarchimedean local field `K_v` of the localization at `v` of its class over `G_K`. -/
def ideleLocalInvAt (v : HeightOneSpectrum (𝓞 K)) :
    L.H (ideleFormation K) 2 →+ AddCircle (1 : ℚ) :=
  (invMap (v.adicCompletion K)).toAddMonoidHom.comp
    ((ideleBrLocalization v).comp (ideleLayerCorInfl K L))

/-- The local invariant at a finite place is the invariant of the localization of the class over
`G_K`. -/
theorem ideleLocalInvAt_apply (v : HeightOneSpectrum (𝓞 K)) (x : L.H (ideleFormation K) 2) :
    ideleLocalInvAt K L v x =
      invMap (v.adicCompletion K) (ideleBrLocalization v (ideleLayerCorInfl K L x)) :=
  (rfl)

/-- The local invariant at a finite place vanishes exactly when the localization does. -/
@[simp]
theorem ideleLocalInvAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (x : L.H (ideleFormation K) 2) :
    ideleLocalInvAt K L v x = 0 ↔ ideleBrLocalization v (ideleLayerCorInfl K L x) = 0 := by
  rw [ideleLocalInvAt_apply, map_eq_zero_iff _ (invMap _).injective]

/-- **The local invariant at an infinite place** `w` of an idele-layer class: the archimedean
invariant of the localization at `w` of its class over `G_K`. -/
def ideleInfiniteInvAt (w : InfinitePlace K) : L.H (ideleFormation K) 2 →+ AddCircle (1 : ℚ) :=
  (infiniteInvMap w).comp ((ideleInfiniteBrLocalization w).comp (ideleLayerCorInfl K L))

/-- The local invariant at an infinite place is the archimedean invariant of the localization of
the class over `G_K`. -/
theorem ideleInfiniteInvAt_apply (w : InfinitePlace K) (x : L.H (ideleFormation K) 2) :
    ideleInfiniteInvAt K L w x =
      infiniteInvMap w (ideleInfiniteBrLocalization w (ideleLayerCorInfl K L x)) :=
  (rfl)

/-- The local invariant at an infinite place vanishes exactly when the localization does. -/
@[simp]
theorem ideleInfiniteInvAt_eq_zero_iff (w : InfinitePlace K) (x : L.H (ideleFormation K) 2) :
    ideleInfiniteInvAt K L w x = 0 ↔
      ideleInfiniteBrLocalization w (ideleLayerCorInfl K L x) = 0 := by
  rw [ideleInfiniteInvAt_apply, infiniteInvMap_eq_zero_iff]

/-- **Inflation preserves the local invariants at the finite places.** -/
@[simp]
theorem ideleLocalInvAt_infl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (v : HeightOneSpectrum (𝓞 K)) (x : old.H (ideleFormation K) 2) :
    ideleLocalInvAt K new v (T.cohomologyInfl (ideleFormation K) 2 x) =
      ideleLocalInvAt K old v x := by
  rw [ideleLocalInvAt_apply, ideleLayerCorInfl_cohomologyInfl, ideleLocalInvAt_apply]

/-- **Inflation preserves the local invariants at the infinite places.** -/
@[simp]
theorem ideleInfiniteInvAt_infl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (w : InfinitePlace K) (x : old.H (ideleFormation K) 2) :
    ideleInfiniteInvAt K new w (T.cohomologyInfl (ideleFormation K) 2 x) =
      ideleInfiniteInvAt K old w x := by
  rw [ideleInfiniteInvAt_apply, ideleLayerCorInfl_cohomologyInfl, ideleInfiniteInvAt_apply]

/-! ### Finite support -/

/-- **An idele-layer class is unramified almost everywhere**: its local invariant vanishes at all
but finitely many finite places. -/
theorem hasFiniteSupport_ideleLocalInvAt (x : L.H (ideleFormation K) 2) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦ ideleLocalInvAt K L v x).HasFiniteSupport :=
  (finite_setOfPred_ideleBrLocalization_ne_zero (ideleLayerCorInfl K L x)).subset fun _ hv ↦
    mt (ideleLocalInvAt_eq_zero_iff K L _ x).2 hv

/-- **The ramification set of an idele-layer class**: the finite set of the finite places where its
local invariant is nonzero: the support of the finite-place part of the localization
`ideleLocalization K` of its class over `G_K`. -/
def ideleSupport (x : L.H (ideleFormation K) 2) : Finset (HeightOneSpectrum (𝓞 K)) :=
  open scoped Classical in (ideleLocalization K (ideleLayerCorInfl K L x)).1.support

/-- A finite place lies in the ramification set of `x` exactly when the local invariant of `x`
there is nonzero. -/
@[simp]
theorem mem_ideleSupport {x : L.H (ideleFormation K) 2} {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ ideleSupport K L x ↔ ideleLocalInvAt K L v x ≠ 0 := by
  classical
  rw [ideleSupport, DFinsupp.mem_support_iff, ideleLocalization_fst_apply, ne_eq, ne_eq,
    ideleLocalInvAt_eq_zero_iff]

/-- Outside its ramification set, the local invariant of an idele-layer class vanishes. -/
theorem ideleLocalInvAt_eq_zero_of_notMem_ideleSupport {x : L.H (ideleFormation K) 2}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ideleSupport K L x) : ideleLocalInvAt K L v x = 0 :=
  not_not.1 fun h ↦ hv ((mem_ideleSupport K L).2 h)

/-- **Inflation preserves the ramification set.** -/
@[simp]
theorem ideleSupport_infl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (x : old.H (ideleFormation K) 2) :
    ideleSupport K new (T.cohomologyInfl (ideleFormation K) 2 x) = ideleSupport K old x :=
  Finset.ext fun v ↦ by simp

/-! ### The sum of the local invariants -/

/-- **The sum of the local invariants of an idele-layer class**: the sum `sumLocalInv K` of the
local invariants of the family `ideleLocalization K` of local Brauer classes of its class over
`G_K`. It is the sum of the invariants `ideleLocalInvAt` at the finitely many finite places of
`ideleSupport` and of the invariants `ideleInfiniteInvAt` at the infinite places
(`ideleSumLocalInv_eq_sum`). -/
def ideleSumLocalInv : L.H (ideleFormation K) 2 →+ AddCircle (1 : ℚ) :=
  (sumLocalInv K).comp ((ideleLocalization K).comp (ideleLayerCorInfl K L))

/-- The sum of the local invariants is `sumLocalInv K` of the localizations of the class over
`G_K`. -/
theorem ideleSumLocalInv_apply (x : L.H (ideleFormation K) 2) :
    ideleSumLocalInv K L x = sumLocalInv K (ideleLocalization K (ideleLayerCorInfl K L x)) :=
  (rfl)

/-- **The sum of the local invariants of an idele-layer class** may be computed over any finite
set of finite places containing its ramification set, together with all the infinite places. -/
theorem ideleSumLocalInv_eq_sum (x : L.H (ideleFormation K) 2)
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : ideleSupport K L x ⊆ S) :
    ideleSumLocalInv K L x =
      ∑ v ∈ S, ideleLocalInvAt K L v x + ∑ w, ideleInfiniteInvAt K L w x := by
  rw [ideleSumLocalInv_apply, sumLocalInv_eq_sum K _ fun v hv ↦ by
    rw [ideleLocalization_fst_apply, ← ideleLocalInvAt_eq_zero_iff]
    exact ideleLocalInvAt_eq_zero_of_notMem_ideleSupport K L fun h ↦ hv (hS h)]
  simp only [ideleLocalization_fst_apply, ideleLocalization_snd_apply, ideleLocalInvAt_apply,
    ideleInfiniteInvAt_apply]

/-- **The sum of the local invariants is inflation-invariant**: inflating an idele-layer class to
a refinement of its layer does not change the sum of its local invariants. -/
@[simp]
theorem ideleSumLocalInv_infl {old new : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRefinement old new) (x : old.H (ideleFormation K) 2) :
    ideleSumLocalInv K new (T.cohomologyInfl (ideleFormation K) 2 x) =
      ideleSumLocalInv K old x := by
  rw [ideleSumLocalInv_apply, ideleLayerCorInfl_cohomologyInfl, ideleSumLocalInv_apply]

end TauCeti.ClassFieldTheory
