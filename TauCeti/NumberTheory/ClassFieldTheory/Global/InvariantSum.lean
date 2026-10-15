/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalInvariant
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import TauCeti.Data.DFinsupp.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Unramified
import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.RingTheory.DedekindDomain.PrimesAbove
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# The localization map and the sum of the local invariants

Let `K` be a number field. A cohomological Brauer class `x ∈ Br K` has a local invariant
`TauCeti.ClassFieldTheory.finiteInvAt K v x` at every finite place `v` and
`TauCeti.ClassFieldTheory.infiniteInvAt K w x` at every infinite place `w`. This file proves that
only finitely many of the finite invariants are nonzero, names the finite set where they are,
`brauerSupport K x`, and defines the two maps of the global Brauer sequence

```text
0 → Br K → ⨁_v Br K_v → ℚ/ℤ → 0:
```

the localization map `brLocalization K : Br K → ⨁_v Br K_v`, and the sum of the local invariants
`sumLocalInv K : ⨁_v Br K_v → ℚ/ℤ`. The direct sum is modelled as the product of the finitely
supported families `Π₀ v, Br K_v` over the finite places with the families `Π w, Br K_w` over the
finitely many infinite places. The composite `sumLocalInv K ∘ brLocalization K` is the sum of the
local invariants of a global class (`sumLocalInv_brLocalization`).

Finiteness is the classical argument. The class `x` is inflated from `H²(Gal(E/K), Eˣ)` for a
finite Galois subextension `E` of `Kˢ` (`TauCeti.ClassFieldTheory.exists_relBrInfl_eq`), so it is
represented by a cocycle `c` with finitely many values in `Eˣ`. Outside a finite set of places of
`E`, the place `w` is unramified over `K`, since it does not divide the different ideal, and all
values of `c` are `w`-adic units. For a finite place `v` of `K` below such a place `w`, the
localization of `x` at `v` is inflated from `H²(Gal(E_w/K_v), E_wˣ)`
(`TauCeti.ClassFieldTheory.brBaseChange_relBrInfl`), where the extension `E_w/K_v` is unramified
and `c` takes unit values, so the localization vanishes
(`TauCeti.ClassFieldTheory.brBaseChange_relBrInfl_eq_zero`).

## Main definitions

* `TauCeti.ClassFieldTheory.brauerSupport K x`: the finite set of the finite places where `x` has
  nonzero local invariant.
* `TauCeti.ClassFieldTheory.brLocalization K`: the localization map `Br K →+ ⨁_v Br K_v`.
* `TauCeti.ClassFieldTheory.sumLocalInv K`: the sum of the local invariants at all places,
  `⨁_v Br K_v →+ ℚ/ℤ`.

## Main results

* `TauCeti.ClassFieldTheory.hasFiniteSupport_finiteInvAt`: a global Brauer class has nonzero
  local invariant at only finitely many finite places.
* `TauCeti.ClassFieldTheory.sumLocalInv_eq_sum`: the sum of the local invariants of a family may
  be computed over any finite set of finite places outside which the family vanishes.
* `TauCeti.ClassFieldTheory.sumLocalInv_single`: the sum for a family supported at one finite
  place is its invariant there.
* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization`: the sum of the local invariants of a
  global class may be computed over any finite set of finite places containing
  `brauerSupport K x`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (8.1.17).
* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter VII (Tate, *Global
  Class Field Theory*), §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField groupCohomology
open scoped AdicCompletionExtension

variable (K : Type) [Field K] [NumberField K]

/-! ### Finiteness of the ramification set -/

/-- **A global Brauer class is unramified almost everywhere**: its local invariant vanishes at
all but finitely many finite places. -/
theorem hasFiniteSupport_finiteInvAt (x : Br K) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦ finiteInvAt K v x).HasFiniteSupport := by
  obtain ⟨E, _, _, y, rfl⟩ := exists_relBrInfl_eq x
  have : NumberField E := .of_module_finite K E
  induction y using groupCohomology.H2_induction_on with
  | h c =>
  -- The finitely many places of `E` that ramify over `K` or where a value of `c` is not a unit.
  let val : Gal(E/K) × Gal(E/K) → Eˣ := fun p ↦ (Rep.toAdditive (c p)).toMul
  let bad : Set (HeightOneSpectrum (𝓞 E)) :=
    {w | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 E)} ∪
      ⋃ p, {w | w.valuation E ((val p : Eˣ) : E) ≠ 1}
  have hbad : bad.Finite :=
    (Ideal.finite_factors differentIdeal_ne_bot).union (Set.finite_iUnion fun _ ↦
      HeightOneSpectrum.finite_setOfPred_valuation_ne_one (Units.ne_zero _))
  -- The invariant vanishes at every place `v` below none of them.
  refine (hbad.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv ↦ ?_
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
  rw [Function.mem_support] at hv
  by_contra hvS
  refine hv ?_
  have hw : w ∉ bad := fun h ↦ hvS ⟨w, h, rfl⟩
  simp only [bad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    not_not] at hw
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.1 hw.1
  have : IsGalois K E := {}
  have : IsUnramified ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion E) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt _ w
  rw [finiteInvAt_eq_zero_iff]
  exact brBaseChange_relBrInfl_eq_zero _ (w.adicCompletion E) K E E.val c fun g h ↦
    (HeightOneSpectrum.unitsMap_algebraMap_mem_unitFiltration_zero_iff w _).2 (hw.2 (g, h))

/-- **The ramification set of a global Brauer class**: the finite set of the finite places where
its local invariant is nonzero. -/
def brauerSupport (x : Br K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  Set.Finite.toFinset (s := Function.support fun v ↦ finiteInvAt K v x)
    (hasFiniteSupport_finiteInvAt K x)

/-- A finite place lies in the ramification set of `x` exactly when the local invariant of `x`
there is nonzero. -/
@[simp]
theorem mem_brauerSupport {x : Br K} {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ brauerSupport K x ↔ finiteInvAt K v x ≠ 0 :=
  (Set.Finite.mem_toFinset _).trans Function.mem_support

/-- Outside its ramification set, the local invariant of a global Brauer class vanishes. -/
theorem finiteInvAt_eq_zero_of_notMem_brauerSupport {x : Br K} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ brauerSupport K x) : finiteInvAt K v x = 0 :=
  not_not.1 fun h ↦ hv ((mem_brauerSupport K).2 h)

/-! ### The localization map and the sum of the local invariants -/

/-- **The localization map of the global Brauer sequence** `Br K → ⨁_v Br K_v`: base change of a
global Brauer class to every completion, as a finitely supported family at the finite places
together with a family at the (finitely many) infinite places. The family at the finite places is
supported on the ramification set `brauerSupport K x`. -/
def brLocalization : Br K →+ (Π₀ v : HeightOneSpectrum (𝓞 K), Br (v.adicCompletion K)) ×
    ((w : InfinitePlace K) → Br w.Completion) where
  toFun x :=
    (dfinsuppOfFiniteSupport (fun v ↦ brBaseChange K (v.adicCompletion K) x)
      ((hasFiniteSupport_finiteInvAt K x).subset fun v hv ↦
        mt (finiteInvAt_eq_zero_iff K v x).1 hv),
      fun w ↦ brBaseChange K w.Completion x)
  map_zero' := Prod.ext (DFinsupp.ext fun _ ↦ by simp) (funext fun _ ↦ map_zero (brBaseChange K _))
  map_add' x y := Prod.ext (DFinsupp.ext fun _ ↦ by simp)
    (funext fun _ ↦ map_add (brBaseChange K _) x y)

/-- The component of the localization map at a finite place `v` is base change to `K_v`. -/
@[simp]
theorem brLocalization_fst_apply (x : Br K) (v : HeightOneSpectrum (𝓞 K)) :
    (brLocalization K x).1 v = brBaseChange K (v.adicCompletion K) x :=
  dfinsuppOfFiniteSupport_apply _ _ v

/-- The component of the localization map at an infinite place `w` is base change to `K_w`. -/
@[simp]
theorem brLocalization_snd_apply (x : Br K) (w : InfinitePlace K) :
    (brLocalization K x).2 w = brBaseChange K w.Completion x :=
  (rfl)

/-- **The sum of the local invariants**, the map `⨁_v Br K_v → ℚ/ℤ` of the global Brauer
sequence: the sum of the invariants `inv_{K_v}` of a finitely supported family of local Brauer
classes at the finite places, plus the archimedean invariants of a family at the infinite places
(`sumLocalInv_eq_sum`). -/
def sumLocalInv : (Π₀ v : HeightOneSpectrum (𝓞 K), Br (v.adicCompletion K)) ×
    ((w : InfinitePlace K) → Br w.Completion) →+ AddCircle (1 : ℚ) :=
  open Classical in
  AddMonoidHom.coprod
    (DFinsupp.sumAddHom fun v ↦ (invMap (v.adicCompletion K)).toAddMonoidHom)
    (∑ w, (infiniteInvMap w).comp (Pi.evalAddMonoidHom _ w))

/-- The sum of the local invariants of a family of local Brauer classes may be computed over any
finite set of finite places outside which the family vanishes. -/
theorem sumLocalInv_eq_sum (y : (Π₀ v : HeightOneSpectrum (𝓞 K), Br (v.adicCompletion K)) ×
    ((w : InfinitePlace K) → Br w.Completion)) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v ∉ S, y.1 v = 0) :
    sumLocalInv K y =
      ∑ v ∈ S, invMap (v.adicCompletion K) (y.1 v) + ∑ w, infiniteInvMap w (y.2 w) := by
  classical
  rw [sumLocalInv, AddMonoidHom.coprod_apply, DFinsupp.sumAddHom_apply,
    DFinsupp.sum_of_support_subset (s := S)
      (fun v hv ↦ not_not.1 fun h ↦ DFinsupp.mem_support_iff.1 hv (hS v h)) fun _ _ ↦ map_zero _,
    AddMonoidHom.finsetSum_apply]
  simp

/-- The sum of the local invariants of a family supported at one finite place is its local
invariant there. -/
@[simp]
theorem sumLocalInv_single [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (v : HeightOneSpectrum (𝓞 K)) (x : Br (v.adicCompletion K)) :
    sumLocalInv K (DFinsupp.single v x, 0) = invMap (v.adicCompletion K) x := by
  classical
  rw [sumLocalInv_eq_sum K _ (S := {v})]
  · simp
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    exact DFinsupp.single_eq_of_ne hw

/-- **The sum of the local invariants of a global Brauer class**, the composite of the localization
map with the sum of the local invariants, may be computed over any finite set of finite places
containing the ramification set. -/
theorem sumLocalInv_brLocalization (x : Br K) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : brauerSupport K x ⊆ S) :
    sumLocalInv K (brLocalization K x) =
      ∑ v ∈ S, finiteInvAt K v x + ∑ w, infiniteInvAt K w x := by
  rw [sumLocalInv_eq_sum K _ fun v hv ↦ (brLocalization_fst_apply K x v).trans
    ((finiteInvAt_eq_zero_iff K v x).1
      (finiteInvAt_eq_zero_of_notMem_brauerSupport K fun h ↦ hv (hS h)))]
  simp only [brLocalization_fst_apply, brLocalization_snd_apply, finiteInvAt_apply,
    infiniteInvAt_apply]

end TauCeti.ClassFieldTheory
