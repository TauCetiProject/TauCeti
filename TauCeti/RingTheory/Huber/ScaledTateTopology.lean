/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RingTheory.Huber.RestrictedPowerSeries

/-!
# The scaled topology on the Tate algebra

For a nonarchimedean ring `A` and a scaling parameter `f : A`, this file puts on the restricted
power series `A⟨X⟩` the topology in which a series is small when its *scaled* coefficients
`fⁿ aₙ` are uniformly small. It is the topology induced along the substitution `X ↦ f X`.

## Main definitions

* `TauCeti.Huber.scaleHom`: the substitution `X ↦ f X` on `MvPowerSeries (Fin 1) A`, as a ring
  homomorphism.
* `TauCeti.Huber.scaleIncl`: its restriction to `A⟨X⟩`, valued in `MvPowerSeries (Fin 1) A`.
* `TauCeti.Huber.scaledTateTopology`: the topology induced along `scaleIncl f`.

## Main results

* `TauCeti.Huber.scaledTateTopology_isTopologicalRing`: it is a ring topology.
* `TauCeti.Huber.scaledTateTopology_nonarchimedean`: it is nonarchimedean, so it has a basis of
  open additive subgroups at zero.
* `TauCeti.Huber.continuous_algebraMap_scaledTateTopology`: the constant-series embedding
  `A → A⟨X⟩` is continuous for it.

## This is not Wedhorn's `A⟨X⟩_T`

Wedhorn's weighted restricted series (*Adic Spaces*, Remark and Definition 5.48, equation
(5.6.1)) is a different object in two ways. Its carrier is a subring of `A[[X]]` cut out by

```text
A⟨X⟩_T := { ∑ aν Xν ; aν ∈ Tν · U for every open subgroup U of A and almost all ν },
```

with fundamental neighbourhoods `U⟨X⟩ := { ∑ aν Xν ∈ A⟨X⟩_T ; aν ∈ Tν · U for all ν }`. So the
weight multiplies the neighbourhood `U`, not the coefficient, and the carrier varies with `T`
— `A⟨X⟩` is by definition the case `T = {1}` (Wedhorn, Example 5.54).

What is built here instead keeps the `T = {1}` carrier `A⟨X⟩` and transports its topology along
`X ↦ f X`, giving the conditions `fⁿ aₙ ∈ U`. The two agree only under extra invertibility
assumptions on `f`, which are not made here and for which no equivalence is proved. Anything
claiming to formalise (5.6.1) must build the weighted carrier directly.

## Provenance

This is a port of the first part of AINTLIB's `TateAlgebraWedhorn.lean`, at commit `d9f2fbbb`,
covering its `scaleHom` through `tateTopologyT_continuous_algebraMap`. The changes are: the
declarations move into the `TauCeti.Huber` namespace and are renamed after their conclusions;
`A⟨X⟩` is spelled `restrictedMvPowerSeriesSubring 1 A` rather than through a `TateAlgebra`
abbreviation; the module opts into the Lean module system; and the identification of this
construction with Wedhorn's Definition 5.48, which the source asserts, is retracted for the
reason given above.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48 and Example 5.54, for
  the weighted ring this construction is *not*.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), commit `d9f2fbbb`,
  `projects/AdicSpaces/Adic spaces/TateAlgebraWedhorn.lean`.
-/

open MvPowerSeries

namespace TauCeti.Huber

public section

section Scaling

variable {A : Type*} [CommRing A]

/-! ### The scaling homomorphism -/

/-- The substitution `X ↦ f X` on `MvPowerSeries (Fin 1) A`: it multiplies the coefficient at
the multi-index `s` by `f ^ s 0`. -/
noncomputable def scaleHom (f : A) :
    MvPowerSeries (Fin 1) A →+* MvPowerSeries (Fin 1) A where
  toFun g s := f ^ (s 0) * g s
  map_zero' := funext fun _ ↦ mul_zero _
  map_one' := funext fun s ↦ by
    change f ^ (s 0) * (1 : MvPowerSeries (Fin 1) A) s = (1 : MvPowerSeries (Fin 1) A) s
    rw [show (1 : MvPowerSeries (Fin 1) A) s = MvPowerSeries.coeff s 1 from rfl,
      MvPowerSeries.coeff_one]
    split
    · rename_i h; subst h; simp
    · ring
  map_add' _ _ := funext fun _ ↦ mul_add _ _ _
  map_mul' g h := funext fun s ↦ by
    classical
    let φ : MvPowerSeries (Fin 1) A := fun s ↦ f ^ (s 0) * g s
    let ψ : MvPowerSeries (Fin 1) A := fun s ↦ f ^ (s 0) * h s
    change f ^ (s 0) * MvPowerSeries.coeff s (g * h) = MvPowerSeries.coeff s (φ * ψ)
    rw [MvPowerSeries.coeff_mul (φ := g) (ψ := h),
      MvPowerSeries.coeff_mul (φ := φ) (ψ := ψ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    change f ^ (s 0) * (g p.1 * h p.2) = (f ^ (p.1 0) * g p.1) * (f ^ (p.2 0) * h p.2)
    have hs : p.1 0 + p.2 0 = s 0 := by
      rw [← Finsupp.add_apply, Finset.mem_antidiagonal.mp hp]
    calc f ^ (s 0) * (g p.1 * h p.2)
        = f ^ (p.1 0 + p.2 0) * (g p.1 * h p.2) := by rw [hs]
      _ = _ := by rw [pow_add]; ring

@[simp]
theorem scaleHom_apply (f : A) (g : MvPowerSeries (Fin 1) A) (s : Fin 1 →₀ ℕ) :
    scaleHom f g s = f ^ (s 0) * g s := (rfl)

end Scaling

section Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The scaling homomorphism restricted to the restricted power series `A⟨X⟩`. The weighted
topology is the one this map induces. -/
noncomputable def scaleIncl (f : A) :
    restrictedMvPowerSeriesSubring 1 A →+* MvPowerSeries (Fin 1) A :=
  (scaleHom f).comp (restrictedMvPowerSeriesSubring 1 A).subtype

theorem scaleIncl_apply (f : A) (g : restrictedMvPowerSeriesSubring 1 A) (s : Fin 1 →₀ ℕ) :
    scaleIncl f g s = f ^ (s 0) * (g : MvPowerSeries (Fin 1) A) s := (rfl)

/-! ### The weighted topology -/

/-- The topology on `A⟨X⟩` in which a series is close to zero when all of its scaled
coefficients `fⁿ aₙ` are. See the module docstring: this is *not* Wedhorn's `A⟨X⟩_T`. -/
@[reducible]
noncomputable def scaledTateTopology (f : A) :
    TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) :=
  TopologicalSpace.induced (scaleIncl f) (WithPiTopology.instTopologicalSpace A)

private theorem scaleIncl_comp_neg (f : A) :
    scaleIncl f ∘ (- · : restrictedMvPowerSeriesSubring 1 A → _) = (- ·) ∘ scaleIncl f := by
  ext x s
  change f ^ (s 0) * ((-x : restrictedMvPowerSeriesSubring 1 A) :
    MvPowerSeries (Fin 1) A) s = -(f ^ (s 0) * (x : MvPowerSeries (Fin 1) A) s)
  rw [NegMemClass.coe_neg, show (-(x : MvPowerSeries (Fin 1) A)) s =
    -((x : MvPowerSeries (Fin 1) A) s) from rfl, mul_neg]

/-- The weighted topology is a ring topology: it is induced along a ring homomorphism from the
product topology, which is one. -/
theorem scaledTateTopology_isTopologicalRing (f : A) :
    @IsTopologicalRing _ (scaledTateTopology f) _ := by
  let _ : TopologicalSpace (MvPowerSeries (Fin 1) A) := WithPiTopology.instTopologicalSpace A
  have : IsTopologicalRing (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instIsTopologicalRing (Fin 1) A
  let _ : TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) := scaledTateTopology f
  have hind : Topology.IsInducing (scaleIncl f) := ⟨rfl⟩
  have : ContinuousMul (restrictedMvPowerSeriesSubring 1 A) := continuousMul_induced (scaleIncl f)
  have : ContinuousAdd (restrictedMvPowerSeriesSubring 1 A) := continuousAdd_induced (scaleIncl f)
  have : ContinuousNeg (restrictedMvPowerSeriesSubring 1 A) := by
    constructor
    rw [hind.continuous_iff]
    change Continuous (scaleIncl f ∘ (- ·))
    rw [scaleIncl_comp_neg]
    exact continuous_neg.comp continuous_induced_dom
  exact { continuous_add := continuous_add
          continuous_mul := continuous_mul
          continuous_neg := continuous_neg }

/-- The weighted topology is nonarchimedean: every neighbourhood of zero contains an open
additive subgroup, obtained by pulling back a finite product of such subgroups of `A`. -/
theorem scaledTateTopology_nonarchimedean (f : A) :
    @NonarchimedeanRing _ _ (scaledTateTopology f) := by
  let _ : TopologicalSpace (MvPowerSeries (Fin 1) A) := WithPiTopology.instTopologicalSpace A
  have : IsTopologicalRing (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instIsTopologicalRing (Fin 1) A
  let _ : TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) := scaledTateTopology f
  have := scaledTateTopology_isTopologicalRing f
  constructor
  intro U hU
  rw [@nhds_induced _ _ (WithPiTopology.instTopologicalSpace A) (scaleIncl f) 0,
    Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  rw [map_zero] at hW
  change W ∈ @nhds _ (@Pi.topologicalSpace (Fin 1 →₀ ℕ) (fun _ ↦ A) fun _ ↦ ‹_›) 0 at hW
  rw [nhds_pi] at hW
  simp only [show ∀ i : Fin 1 →₀ ℕ, (0 : (Fin 1 →₀ ℕ) → A) i = (0 : A) from fun _ ↦ rfl] at hW
  obtain ⟨I, hI, t, ht, hIt⟩ := Filter.mem_pi.mp hW
  have hVi : ∀ i : Fin 1 →₀ ℕ, ∃ V : OpenAddSubgroup A, (V : Set A) ⊆ t i := fun i ↦
    NonarchimedeanRing.is_nonarchimedean (t i) (ht i)
  choose V hV using hVi
  set S : Set (MvPowerSeries (Fin 1) A) := {φ | ∀ i ∈ I, φ i ∈ V i} with hS
  have hSopen : IsOpen S := isOpen_set_pi hI fun i _ ↦ (V i).isOpen
  refine ⟨⟨{ carrier := scaleIncl f ⁻¹' S
             add_mem' := fun {a b} ha hb i hi ↦ by
               change scaleIncl f (a + b) i ∈ _
               rw [map_add]
               exact (V i).toAddSubgroup.add_mem (ha i hi) (hb i hi)
             zero_mem' := fun i _ ↦ by
               change scaleIncl f 0 i ∈ _
               rw [map_zero]
               exact (V i).toAddSubgroup.zero_mem
             neg_mem' := fun {a} ha i hi ↦ by
               change scaleIncl f (-a) i ∈ _
               rw [map_neg]
               exact (V i).toAddSubgroup.neg_mem (ha i hi) },
      hSopen.preimage continuous_induced_dom⟩,
    fun g hg ↦ hWU (hIt fun i hi ↦ hV i (hg i hi))⟩

/-- The constant-series embedding `A → A⟨X⟩` is continuous for the weighted topology. -/
theorem continuous_algebraMap_scaledTateTopology (f : A) :
    @Continuous _ _ _ (scaledTateTopology f)
      (algebraMap A (restrictedMvPowerSeriesSubring 1 A)) := by
  let _ : TopologicalSpace (restrictedMvPowerSeriesSubring 1 A) := scaledTateTopology f
  let _ : TopologicalSpace (MvPowerSeries (Fin 1) A) := WithPiTopology.instTopologicalSpace A
  refine continuous_induced_rng.mpr ?_
  change Continuous (scaleIncl f ∘ algebraMap A (restrictedMvPowerSeriesSubring 1 A))
  refine continuous_pi fun s ↦ ?_
  change Continuous fun a ↦
    f ^ (s 0) * ((algebraMap A (restrictedMvPowerSeriesSubring 1 A) a :
      MvPowerSeries (Fin 1) A)) s
  by_cases hs : s = 0
  · subst hs
    simp only [Finsupp.zero_apply, pow_zero, one_mul]
    change Continuous fun a ↦ (algebraMap A (MvPowerSeries (Fin 1) A) a) 0
    exact (WithPiTopology.continuous_coeff A 0).comp WithPiTopology.continuous_C
  · have hzero : (fun a : A ↦ f ^ (s 0) *
        ((algebraMap A (restrictedMvPowerSeriesSubring 1 A) a :
          MvPowerSeries (Fin 1) A)) s) = fun _ ↦ 0 := by
      ext a
      classical
      change f ^ (s 0) * (algebraMap A (MvPowerSeries (Fin 1) A) a) s = 0
      rw [show (algebraMap A (MvPowerSeries (Fin 1) A) a) s =
        MvPowerSeries.coeff s (MvPowerSeries.C (σ := Fin 1) a) from rfl,
        MvPowerSeries.coeff_C, if_neg hs, mul_zero]
    rw [hzero]
    exact continuous_const

end Topology

end

end TauCeti.Huber
