/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalInvariant
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Unramified
import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The sum of the local invariants of a global Brauer class

Let `K` be a number field. A cohomological Brauer class `x ∈ Br K` has a local invariant
`TauCeti.ClassFieldTheory.finiteInvAt K v x` at every finite place `v` and
`TauCeti.ClassFieldTheory.infiniteInvAt K w x` at every infinite place `w`. This file proves that
only finitely many of the finite invariants are nonzero, names the finite set where they are,
`brauerSupport K x`, and defines the middle map of the global Brauer sequence

```text
0 → Br K → ⨁_v Br K_v → ℚ/ℤ → 0,
```

the sum of the local invariants `sumLocalInv K : Br K →+ ℚ/ℤ`.

Finiteness is the classical argument. The class `x` is inflated from `H²(Gal(E/K), Eˣ)` for a
finite Galois subextension `E` of `Kˢ` (`TauCeti.ClassFieldTheory.exists_relBrInfl_eq`), so it is
represented by a cocycle `c` with finitely many values in `Eˣ`. Outside a finite set of places of
`E`, the place `w` is unramified over `K`, since it does not divide the different ideal, and all
values of `c` are `w`-adic units. For a finite place `v` of `K` below such a place `w`, the
localization of `x` at `v` is inflated from `H²(Gal(E_w/K_v), E_wˣ)`
(`TauCeti.ClassFieldTheory.brBaseChange_relBrInfl`), where the extension `E_w/K_v` is unramified
and `c` takes unit values, so the localization vanishes
(`TauCeti.ClassFieldTheory.H2π_eq_zero_of_forall_mem_unitFiltration_zero`).

## Main definitions

* `TauCeti.ClassFieldTheory.brauerSupport K x`: the finite set of the finite places where `x` has
  nonzero local invariant.
* `TauCeti.ClassFieldTheory.sumLocalInv K`: the sum of the local invariants at all places,
  `Br K →+ ℚ/ℤ`.

## Main results

* `TauCeti.ClassFieldTheory.hasFiniteSupport_finiteInvAt`: a global Brauer class has nonzero
  local invariant at only finitely many finite places.
* `TauCeti.ClassFieldTheory.sumLocalInv_eq_sum`: the sum of the local invariants may be computed
  over any finite set of finite places containing `brauerSupport K x`.

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

variable (K : Type) [Field K]

/-- A class inflated from a finite Galois extension `E/K` vanishes after base change to a
nonarchimedean local field `F/K` when `E` maps into a finite unramified Galois extension `M/F` in
which the inflated cocycle takes unit values. -/
private theorem brBaseChange_relBrInfl_eq_zero (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [Normal K E]
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra K F]
    (M : Type) [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M]
    [IsUnramified F M] [Algebra K M] [IsScalarTower K F M] [Algebra E M] [IsScalarTower K E M]
    (c : cocycles₂ (Rep.ofMulDistribMulAction Gal(E/K) Eˣ))
    (hc : ∀ g h, Units.map (algebraMap E M : E →* M) (Rep.toAdditive (c (g, h))).toMul ∈
      unitFiltration M 0) :
    brBaseChange K F (relBrInfl K E E.val (H2π _ c)) = 0 := by
  rw [brBaseChange_relBrInfl K F E M E.val IsSepClosed.lift, H2π_comp_map_apply,
    H2π_eq_zero_of_forall_mem_unitFiltration_zero F M _ fun g h ↦ ?_, map_zero]
  -- The values of the base-changed cocycle are the images of those of `c`.
  have hval : Additive.toMul (Rep.toAdditive ((mapCocycles₂ ((AlgEquiv.restrictNormalHom E).comp
      (AlgEquiv.restrictScalarsHom K)) (unitsBaseChangeHom K E F M) c) (g, h))) =
      Units.map (algebraMap E M : E →* M) (Additive.toMul (Rep.toAdditive
        (c ((AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K) g,
          (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K) h)))) :=
    congrArg (fun x ↦ Additive.toMul (Rep.toAdditive x)) (unitsBaseChangeHom_apply K E F M _)
  rw [hval]
  exact hc _ _

variable [NumberField K]

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
      ⋃ p, (HeightOneSpectrum.Support (𝓞 E) ((val p : Eˣ) : E) ∪
        HeightOneSpectrum.Support (𝓞 E) (((val p)⁻¹ : Eˣ) : E))
  have hbad : bad.Finite := by
    refine (Ideal.finite_factors ?_).union (Set.finite_iUnion fun p ↦ ?_)
    · exact differentIdeal_ne_bot
    · exact (HeightOneSpectrum.Support.finite (𝓞 E) _).union
        (HeightOneSpectrum.Support.finite (𝓞 E) _)
  -- The invariant vanishes at every place `v` below none of them.
  refine (hbad.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv ↦ ?_
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
  rw [Function.mem_support] at hv
  by_contra hvS
  refine hv ?_
  have hw : w ∉ bad := fun h ↦ hvS ⟨w, h, rfl⟩
  simp only [bad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hw
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.1 hw.1
  have : IsGalois K E := {}
  have : IsUnramified ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion E) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt _ w
  rw [finiteInvAt_eq_zero_iff]
  refine brBaseChange_relBrInfl_eq_zero K E _ (w.adicCompletion E) c fun g h ↦ ?_
  refine (HeightOneSpectrum.unitsMap_algebraMap_mem_unitFiltration_zero_iff w _).2 ?_
  obtain ⟨h₁, h₂⟩ := hw.2 (g, h)
  simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt, Units.val_inv_eq_inv_val,
    map_inv₀] at h₁ h₂
  exact le_antisymm h₁ ((inv_le_one₀ (zero_lt_iff.2 (by simp))).1 h₂)

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

/-! ### The sum of the local invariants -/

/-- The sum of the finite local invariants of `x` over its ramification set is their sum over any
finite set of finite places containing it. -/
private theorem sum_brauerSupport_eq (x : Br K) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : brauerSupport K x ⊆ S) :
    ∑ v ∈ brauerSupport K x, finiteInvAt K v x = ∑ v ∈ S, finiteInvAt K v x :=
  Finset.sum_subset hS fun _ _ hv ↦ finiteInvAt_eq_zero_of_notMem_brauerSupport K hv

/-- **The sum of the local invariants**, the middle map `Br K → ℚ/ℤ` of the global Brauer
sequence: the sum of the finite local invariants over the ramification set, plus the archimedean
invariants at all infinite places (`sumLocalInv_apply`). -/
def sumLocalInv : Br K →+ AddCircle (1 : ℚ) where
  toFun x := ∑ v ∈ brauerSupport K x, finiteInvAt K v x + ∑ w, infiniteInvAt K w x
  map_zero' := by simp
  map_add' x y := by
    classical
    -- Compute all three sums over the union of the three ramification sets.
    let S := brauerSupport K x ∪ brauerSupport K y ∪ brauerSupport K (x + y)
    have hx : brauerSupport K x ⊆ S :=
      Finset.subset_union_left.trans Finset.subset_union_left
    have hy : brauerSupport K y ⊆ S :=
      Finset.subset_union_right.trans Finset.subset_union_left
    have hxy : brauerSupport K (x + y) ⊆ S := Finset.subset_union_right
    rw [sum_brauerSupport_eq K x hx, sum_brauerSupport_eq K y hy,
      sum_brauerSupport_eq K (x + y) hxy]
    simp only [map_add, Finset.sum_add_distrib]
    abel

/-- The sum of the local invariants of `x` is the sum of its finite local invariants over its
ramification set, plus its archimedean invariants. -/
theorem sumLocalInv_apply (x : Br K) :
    sumLocalInv K x =
      ∑ v ∈ brauerSupport K x, finiteInvAt K v x + ∑ w, infiniteInvAt K w x :=
  (rfl)

/-- The sum of the local invariants may be computed over any finite set of finite places
containing the ramification set. -/
theorem sumLocalInv_eq_sum (x : Br K) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : brauerSupport K x ⊆ S) :
    sumLocalInv K x = ∑ v ∈ S, finiteInvAt K v x + ∑ w, infiniteInvAt K w x := by
  rw [sumLocalInv_apply, sum_brauerSupport_eq K x hS]

end TauCeti.ClassFieldTheory
