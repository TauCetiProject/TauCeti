/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.LowDimTopology.Heegaard.AddBasepoint
public import TauCeti.LowDimTopology.Heegaard.LensSpace.Diagram
public import TauCeti.LowDimTopology.Heegaard.Stabilization

/-!
# The summands of the Heegaard Floer complexes indexed by `ε`-classes

Let `(Σ, α, β, z)` be a pointed Heegaard diagram of a closed `3`-manifold `Y`. Ozsváth and Szabó
attach to two generators `x`, `y` a class `ε(x, y) ∈ H₁(Y; ℤ)`
(`TauCeti.HeegaardRegionSystem.epsilon`), and show that the spin^c structures of the generators
differ by its Poincaré dual, `s_z(y) - s_z(x) = PD(ε(x, y))`. A domain, and so a holomorphic disk,
can only connect generators with `ε(x, y) = 0`. Consequently each Heegaard Floer chain complex is
the direct sum of the subcomplexes spanned by the generators of one spin^c structure, and its
homology splits accordingly.

This file develops that splitting for the incidence data `TauCeti.HeegaardRegionSystem`. The
relation `ε(x, y) = 0` is an equivalence relation on generators (`epsilonSetoid`), since `ε` is
additive along chains of generators, and its classes are the **`ε`-classes**
`TauCeti.HeegaardRegionSystem.EpsilonClass`. Two generators lie in the same `ε`-class exactly
when some domain connects them
(`TauCeti.HeegaardRegionSystem.epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween`). On an
actual diagram the `ε`-classes are the spin^c structures that are represented by generators. A
spin^c structure need not be represented by any generator of a given diagram, so the `ε`-classes
of a diagram are in general fewer than the spin^c structures of `Y`; they are not a definition of
the spin^c structures.

The difference `ε(x, y)` only depends on the `ε`-classes of `x` and `y`, and descends to a
difference `TauCeti.HeegaardRegionSystem.EpsilonClass.epsilon c d` of classes, valued in the group
`TauCeti.HeegaardRegionSystem.CurveHomology`. It vanishes exactly when `c = d`, and it is additive,
`c.epsilon d + d.epsilon e = c.epsilon e`. So after choosing one class `c₀`, the map
`d ↦ c₀.epsilon d` embeds the `ε`-classes into `CurveHomology`, the combinatorial shadow of the
affine action of `H₁(Y; ℤ) ≅ H²(Y; ℤ)` on the spin^c structures.

For a ring `R`, the chains supported on the generators of one class `c` form the submodule
`TauCeti.HeegaardRegionSystem.epsilonSummand R c` of the free module on generators, and the free
module is the internal direct sum of these summands
(`TauCeti.HeegaardRegionSystem.isInternal_epsilonSummand`). The hat, minus and infinity
differentials count domains, so their coefficients vanish between generators of different classes
(`TauCeti.HeegaardRegionSystem.epsilonClass_eq_of_hatCoefficient_ne_zero`,
`TauCeti.HeegaardRegionSystem.epsilonClass_eq_of_minusCoefficient_ne_zero`). Hence each of them
maps every summand to itself and commutes with the projection of a chain onto a summand
(`TauCeti.HeegaardRegionSystem.hatDifferential_filter`,
`TauCeti.HeegaardRegionSystem.minusDifferential_filter`,
`TauCeti.HeegaardRegionSystem.infinityDifferential_filter`): the complexes `CF̂`, `CF⁻` and
`CF^∞` are the direct sums of their summands over the `ε`-classes.

The `ε`-classes are compatible with the moves on diagrams. Stabilization does not change which
generators are joined by domains, so it identifies the `ε`-classes of the two diagrams
(`TauCeti.HeegaardRegionSystem.stabilizeEpsilonClassEquiv`), and its identification of the hat
chain groups carries each summand onto the corresponding summand
(`TauCeti.HeegaardRegionSystem.map_stabilizeChainEquiv_epsilonSummand`). Adding a basepoint
doubles the generators, `(x, 0)` and `(x, 1)` for each generator `x`, and these two lie in the
same `ε`-class (`TauCeti.HeegaardRegionSystem.epsilonClass_addBasepointGenerator_eq_iff`), so it
too identifies the `ε`-classes (`TauCeti.HeegaardRegionSystem.addBasepointEpsilonClassEquiv`).

For the genus-one diagram of the lens space `L(p, q)` the `p` generators lie in pairwise
different `ε`-classes, so there are exactly `p` of them
(`TauCeti.HeegaardRegionSystem.card_epsilonClass_lensSpace`), one for each spin^c structure of
`L(p, q)`, and each class contains exactly one generator.

## Main definitions

* `TauCeti.HeegaardRegionSystem.EpsilonClass`: the classes of generators under `ε(x, y) = 0`.
* `TauCeti.HeegaardRegionSystem.epsilonClass`: the class of a generator.
* `TauCeti.HeegaardRegionSystem.EpsilonClass.epsilon`: the difference `ε` of two classes.
* `TauCeti.HeegaardRegionSystem.epsilonSummand`: the chains supported on one class.
* `TauCeti.HeegaardRegionSystem.stabilizeEpsilonClassEquiv`,
  `TauCeti.HeegaardRegionSystem.addBasepointEpsilonClassEquiv`: the identifications of classes
  under stabilization and under adding a basepoint.

## Main results

* `TauCeti.HeegaardRegionSystem.epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween`: two
  generators lie in the same class exactly when a domain connects them.
* `TauCeti.HeegaardRegionSystem.EpsilonClass.epsilon_eq_zero_iff`,
  `TauCeti.HeegaardRegionSystem.EpsilonClass.epsilon_right_injective`: the difference of classes
  vanishes only on equal classes, and the classes embed into `CurveHomology`.
* `TauCeti.HeegaardRegionSystem.isInternal_epsilonSummand`: the chain group is the internal direct
  sum of the summands.
* `TauCeti.HeegaardRegionSystem.hatDifferential_mem_epsilonSummand`,
  `TauCeti.HeegaardRegionSystem.minusDifferential_mem_epsilonSummand`,
  `TauCeti.HeegaardRegionSystem.infinityDifferential_mem_epsilonSummand`: the differentials
  preserve the summands.
* `TauCeti.HeegaardRegionSystem.hatDifferential_filter`,
  `TauCeti.HeegaardRegionSystem.minusDifferential_filter`,
  `TauCeti.HeegaardRegionSystem.infinityDifferential_filter`: the differentials commute with the
  projections onto the summands.
* `TauCeti.HeegaardRegionSystem.card_epsilonClass_lensSpace`: the diagram of `L(p, q)` has `p`
  classes.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4 (Definition 2.11 of `ε(x, y)`,
  Proposition 2.15 and Lemma 2.19) and §4 (the splitting of the chain complexes along spin^c
  structures).
-/

public section

open Polynomial LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

section EpsilonClass

/-- The relation `ε(x, y) = 0` on the generators of a Heegaard diagram. It is an equivalence
relation since `ε(x, x) = 0`, `ε(y, x) = -ε(x, y)` and `ε(x, y) + ε(y, w) = ε(x, w)`. -/
def epsilonSetoid : Setoid H.Generator where
  r x y := H.epsilon x y = 0
  iseqv :=
    { refl := H.epsilon_self
      symm := fun {x y} h => by rw [← neg_epsilon, h, neg_zero]
      trans := fun {x y w} h₁ h₂ => by rw [← H.epsilon_add_epsilon x y w, h₁, h₂, add_zero] }

/-- The **`ε`-classes** of generators: the classes of the relation `ε(x, y) = 0`. On an actual
diagram these are the spin^c structures represented by generators. -/
def EpsilonClass : Type u :=
  Quotient H.epsilonSetoid

/-- The `ε`-class of a generator. -/
def epsilonClass (x : H.Generator) : H.EpsilonClass :=
  Quotient.mk H.epsilonSetoid x

variable {H} in
/-- The relation of `epsilonSetoid` is `ε(x, y) = 0`. -/
theorem epsilonSetoid_apply {x y : H.Generator} : H.epsilonSetoid x y ↔ H.epsilon x y = 0 :=
  Iff.rfl

instance : Finite H.EpsilonClass :=
  inferInstanceAs (Finite (Quotient H.epsilonSetoid))

variable {H} {x y : H.Generator}

/-- Two generators lie in the same `ε`-class exactly when `ε(x, y) = 0`. -/
theorem epsilonClass_eq_epsilonClass_iff :
    H.epsilonClass x = H.epsilonClass y ↔ H.epsilon x y = 0 :=
  Quotient.eq

/-- Two generators lie in the same `ε`-class exactly when some domain connects them. -/
theorem epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween :
    H.epsilonClass x = H.epsilonClass y ↔ ∃ D, H.IsDomainBetween x y D := by
  rw [epsilonClass_eq_epsilonClass_iff, epsilon_eq_zero_iff]

/-- Generators joined by a domain lie in the same `ε`-class. -/
theorem IsDomainBetween.epsilonClass_eq {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    H.epsilonClass x = H.epsilonClass y :=
  epsilonClass_eq_epsilonClass_iff.mpr hD.epsilon_eq_zero

variable (H) in
/-- Every `ε`-class is the class of a generator. -/
theorem epsilonClass_surjective : Function.Surjective H.epsilonClass :=
  Quotient.mk_surjective

/-- Induction on `ε`-classes: a property of all classes of generators holds for all classes. -/
@[elab_as_elim]
theorem EpsilonClass.ind {motive : H.EpsilonClass → Prop} (h : ∀ x, motive (H.epsilonClass x))
    (c : H.EpsilonClass) : motive c :=
  Quotient.ind h c

variable (H) in
/-- The difference `ε(c, d) ∈ CurveHomology` of two `ε`-classes: the class `ε(x, y)` of any
generators `x` of `c` and `y` of `d`. -/
noncomputable def EpsilonClass.epsilon (c d : H.EpsilonClass) : H.CurveHomology :=
  Quotient.lift₂ H.epsilon (fun x₁ y₁ x₂ y₂ (hx : H.epsilon x₁ x₂ = 0)
      (hy : H.epsilon y₁ y₂ = 0) => by
    rw [← H.epsilon_add_epsilon x₂ x₁ y₂, ← H.epsilon_add_epsilon x₁ y₁ y₂, ← neg_epsilon x₁ x₂,
      hx, hy, neg_zero, zero_add, add_zero]) c d

namespace EpsilonClass

variable {c d e : H.EpsilonClass}

/-- The difference of the classes of `x` and `y` is `ε(x, y)`. -/
@[simp]
theorem epsilon_epsilonClass (x y : H.Generator) :
    EpsilonClass.epsilon H (H.epsilonClass x) (H.epsilonClass y) = H.epsilon x y :=
  (rfl)

/-- The difference of a class with itself vanishes. -/
@[simp]
theorem epsilon_self (c : H.EpsilonClass) : EpsilonClass.epsilon H c c = 0 := by
  induction c using EpsilonClass.ind with
  | h x => simp

/-- Differences of classes add: `ε(c, d) + ε(d, e) = ε(c, e)`. -/
@[simp]
theorem epsilon_add_epsilon (c d e : H.EpsilonClass) :
    EpsilonClass.epsilon H c d + EpsilonClass.epsilon H d e = EpsilonClass.epsilon H c e := by
  induction c using EpsilonClass.ind with
  | h x =>
    induction d using EpsilonClass.ind with
    | h y =>
      induction e using EpsilonClass.ind with
      | h w => simp

/-- Exchanging the classes negates their difference. -/
@[simp]
theorem neg_epsilon (c d : H.EpsilonClass) :
    -EpsilonClass.epsilon H c d = EpsilonClass.epsilon H d c :=
  neg_eq_of_add_eq_zero_right (by rw [epsilon_add_epsilon, epsilon_self])

/-- The difference of two classes vanishes exactly when they are equal. -/
@[simp]
theorem epsilon_eq_zero_iff : EpsilonClass.epsilon H c d = 0 ↔ c = d := by
  induction c using EpsilonClass.ind with
  | h x =>
    induction d using EpsilonClass.ind with
    | h y => rw [epsilon_epsilonClass, epsilonClass_eq_epsilonClass_iff]

/-- Two classes have the same difference from a third one only if they are equal: after choosing
a class `c`, the map `d ↦ ε(c, d)` embeds the `ε`-classes into `CurveHomology`. -/
theorem epsilon_right_injective (c : H.EpsilonClass) :
    Function.Injective (EpsilonClass.epsilon H c) := fun d e h => by
  rw [← epsilon_eq_zero_iff, ← epsilon_add_epsilon d c e, ← neg_epsilon c d, h, neg_add_cancel]

/-- The difference to a fixed class determines the class. -/
theorem epsilon_left_injective (d : H.EpsilonClass) :
    Function.Injective (EpsilonClass.epsilon H · d) := fun c e h => by
  simp only at h
  rw [← neg_epsilon, ← neg_epsilon d e, neg_inj] at h
  exact epsilon_right_injective d h

end EpsilonClass

end EpsilonClass

section Summand

variable (R : Type*) [Semiring R]

/-- The summand of the chain group on generators spanned by the generators of the `ε`-class `c`:
the chains supported on `c`. -/
def epsilonSummand (c : H.EpsilonClass) : Submodule R (H.Generator →₀ R) :=
  Finsupp.supported R R {x | H.epsilonClass x = c}

variable {H R}

/-- A chain lies in the summand of `c` exactly when it vanishes on the generators outside `c`. -/
theorem mem_epsilonSummand_iff {c : H.EpsilonClass} {v : H.Generator →₀ R} :
    v ∈ H.epsilonSummand R c ↔ ∀ x, H.epsilonClass x ≠ c → v x = 0 :=
  Finsupp.mem_supported' R v

/-- A generator lies in the summand of its class. -/
theorem single_mem_epsilonSummand (x : H.Generator) (a : R) :
    Finsupp.single x a ∈ H.epsilonSummand R (H.epsilonClass x) :=
  Finsupp.single_mem_supported R a rfl

variable (H R)

/-- The summands of distinct `ε`-classes are independent. -/
theorem iSupIndep_epsilonSummand : iSupIndep (H.epsilonSummand R) := fun c =>
  (Finsupp.disjoint_supported_supported (s := {x | H.epsilonClass x = c})
    (t := {x | H.epsilonClass x ≠ c}) (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ h₁)).mono_right
    (iSup₂_le fun d hd =>
      Finsupp.supported_mono fun _ hx => (hx : H.epsilonClass _ = d).trans_ne hd)

/-- The summands span the chain group. -/
theorem iSup_epsilonSummand : ⨆ c, H.epsilonSummand R c = ⊤ := by
  simp_rw [epsilonSummand]
  rw [← Finsupp.supported_iUnion,
    Set.iUnion_eq_univ_iff.mpr fun x => ⟨H.epsilonClass x, rfl⟩, Finsupp.supported_univ]

/-- **The splitting of the chain group along `ε`-classes.** The free module on generators is the
internal direct sum of the summands spanned by the `ε`-classes. -/
theorem isInternal_epsilonSummand (R : Type*) [Ring R] [DecidableEq H.EpsilonClass] :
    DirectSum.IsInternal (H.epsilonSummand R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (H.iSupIndep_epsilonSummand R)
    (H.iSup_epsilonSummand R)

variable {H R}

/-- A map of free modules on generators whose matrix coefficients `k x y` vanish between
generators of different `ε`-classes commutes with restriction to the generators of a class. -/
private theorem filter_of_apply_eq_sum [DecidableEq H.EpsilonClass]
    {f : (H.Generator →₀ R) → H.Generator →₀ R} {k : H.Generator → H.Generator → R}
    (hf : ∀ v y, f v y = v.sum fun x a => a * k x y)
    (hk : ∀ x y, k x y ≠ 0 → H.epsilonClass x = H.epsilonClass y) (c : H.EpsilonClass)
    (v : H.Generator →₀ R) :
    f (v.filter fun x => H.epsilonClass x = c) = (f v).filter fun y => H.epsilonClass y = c := by
  have hk' (x y : H.Generator) (hxy : H.epsilonClass x ≠ H.epsilonClass y) : k x y = 0 :=
    not_imp_comm.mp (hk x y) hxy
  ext y
  rw [Finsupp.filter_apply, hf, hf, Finsupp.sum_fintype _ _ fun _ => zero_mul _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  split_ifs with hy
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finsupp.filter_apply]
    split_ifs with hx
    · rfl
    · rw [zero_mul, hk' x y (fun h => hx (h.trans hy)), mul_zero]
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [Finsupp.filter_apply]
    split_ifs with hx
    · rw [hk' x y (fun h => hy (h.symm.trans hx)), mul_zero]
    · rw [zero_mul]

/-- A map as in `filter_of_apply_eq_sum` maps the summand of each class to itself. -/
private theorem mem_epsilonSummand_of_apply_eq_sum
    {f : (H.Generator →₀ R) → H.Generator →₀ R} {k : H.Generator → H.Generator → R}
    (hf : ∀ v y, f v y = v.sum fun x a => a * k x y)
    (hk : ∀ x y, k x y ≠ 0 → H.epsilonClass x = H.epsilonClass y) {c : H.EpsilonClass}
    {v : H.Generator →₀ R} (hv : v ∈ H.epsilonSummand R c) : f v ∈ H.epsilonSummand R c := by
  classical
  have hfv : v.filter (fun x => H.epsilonClass x = c) = v :=
    (Finsupp.filter_eq_self_iff _ _).mpr fun x hx =>
      not_imp_comm.mp (mem_epsilonSummand_iff.mp hv x) hx
  rw [← hfv, filter_of_apply_eq_sum hf hk]
  exact mem_epsilonSummand_iff.mpr fun _ hx => Finsupp.filter_apply_neg _ _ hx

end Summand

section Differentials

variable {H} [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}
  {x y : H.Generator}

/-- The hat differential only counts domains, so its coefficients vanish between generators of
different `ε`-classes. -/
theorem epsilonClass_eq_of_hatCoefficient_ne_zero (h : H.hatCoefficient χ x y ≠ 0) :
    H.epsilonClass x = H.epsilonClass y := by
  obtain ⟨D, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero h
  exact (mem_hatDomains_iff.mp hD).1.epsilonClass_eq

/-- The hat differential maps the summand of each `ε`-class to itself. -/
theorem hatDifferential_mem_epsilonSummand {c : H.EpsilonClass} {v : H.Generator →₀ ZMod 2}
    (hv : v ∈ H.epsilonSummand (ZMod 2) c) :
    H.hatDifferential χ v ∈ H.epsilonSummand (ZMod 2) c :=
  hatDifferential_mem_supported
    (fun _ hx _ h => (epsilonClass_eq_of_hatCoefficient_ne_zero h).symm.trans hx) hv

/-- **The splitting of `CF̂` along `ε`-classes.** The hat differential commutes with the
projection of a chain onto the summand of each `ε`-class. -/
theorem hatDifferential_filter [DecidableEq H.EpsilonClass] (c : H.EpsilonClass)
    (v : H.Generator →₀ ZMod 2) :
    H.hatDifferential χ (v.filter fun x => H.epsilonClass x = c) =
      (H.hatDifferential χ v).filter fun y => H.epsilonClass y = c :=
  filter_of_apply_eq_sum hatDifferential_apply
    (fun _ _ => epsilonClass_eq_of_hatCoefficient_ne_zero) c v

variable [Fintype Basepoint]

/-- The minus differential only counts domains, so its coefficients vanish between generators of
different `ε`-classes. -/
theorem epsilonClass_eq_of_minusCoefficient_ne_zero (h : H.minusCoefficient χ x y ≠ 0) :
    H.epsilonClass x = H.epsilonClass y := by
  by_contra hne
  exact h (minusCoefficient_eq_zero_of_minusDomains_eq_empty
    (Set.eq_empty_of_forall_notMem fun _ hD => hne (mem_minusDomains_iff.mp hD).1.epsilonClass_eq))

/-- The minus differential maps the summand of each `ε`-class to itself. -/
theorem minusDifferential_mem_epsilonSummand {c : H.EpsilonClass}
    {v : H.Generator →₀ (ZMod 2)[X]} (hv : v ∈ H.epsilonSummand (ZMod 2)[X] c) :
    H.minusDifferential χ v ∈ H.epsilonSummand (ZMod 2)[X] c :=
  mem_epsilonSummand_of_apply_eq_sum minusDifferential_apply
    (fun _ _ => epsilonClass_eq_of_minusCoefficient_ne_zero) hv

/-- **The splitting of `CF⁻` along `ε`-classes.** The minus differential commutes with the
projection of a chain onto the summand of each `ε`-class. -/
theorem minusDifferential_filter [DecidableEq H.EpsilonClass] (c : H.EpsilonClass)
    (v : H.Generator →₀ (ZMod 2)[X]) :
    H.minusDifferential χ (v.filter fun x => H.epsilonClass x = c) =
      (H.minusDifferential χ v).filter fun y => H.epsilonClass y = c :=
  filter_of_apply_eq_sum minusDifferential_apply
    (fun _ _ => epsilonClass_eq_of_minusCoefficient_ne_zero) c v

/-- The coefficients of the infinity differential, the minus coefficients read as Laurent
polynomials, vanish between generators of different `ε`-classes. -/
private theorem epsilonClass_eq_of_toLaurent_minusCoefficient_ne_zero
    (h : toLaurent (H.minusCoefficient χ x y) ≠ 0) : H.epsilonClass x = H.epsilonClass y :=
  epsilonClass_eq_of_minusCoefficient_ne_zero fun h' => h (by rw [h', map_zero])

/-- The infinity differential maps the summand of each `ε`-class to itself. -/
theorem infinityDifferential_mem_epsilonSummand {c : H.EpsilonClass}
    {v : H.Generator →₀ (ZMod 2)[T;T⁻¹]} (hv : v ∈ H.epsilonSummand (ZMod 2)[T;T⁻¹] c) :
    H.infinityDifferential χ v ∈ H.epsilonSummand (ZMod 2)[T;T⁻¹] c :=
  mem_epsilonSummand_of_apply_eq_sum infinityDifferential_apply
    (fun _ _ => epsilonClass_eq_of_toLaurent_minusCoefficient_ne_zero) hv

/-- **The splitting of `CF^∞` along `ε`-classes.** The infinity differential commutes with the
projection of a chain onto the summand of each `ε`-class. -/
theorem infinityDifferential_filter [DecidableEq H.EpsilonClass] (c : H.EpsilonClass)
    (v : H.Generator →₀ (ZMod 2)[T;T⁻¹]) :
    H.infinityDifferential χ (v.filter fun x => H.epsilonClass x = c) =
      (H.infinityDifferential χ v).filter fun y => H.epsilonClass y = c :=
  filter_of_apply_eq_sum infinityDifferential_apply
    (fun _ _ => epsilonClass_eq_of_toLaurent_minusCoefficient_ne_zero) c v

end Differentials

section Stabilization

variable (r₀ : Region)

/-- Stabilization does not change the `ε`-classes: `x ∪ {x₀}` and `y ∪ {x₀}` lie in the same
class of the stabilized diagram exactly when `x` and `y` lie in the same class. -/
@[simp]
theorem epsilonClass_stabilizeGenerator_eq_iff {x y : H.Generator} :
    (H.stabilize r₀).epsilonClass (H.stabilizeGenerator r₀ x) =
        (H.stabilize r₀).epsilonClass (H.stabilizeGenerator r₀ y) ↔
      H.epsilonClass x = H.epsilonClass y := by
  simp only [epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween, isDomainBetween_stabilize_iff]

/-- The identification of the `ε`-classes of a diagram with those of its stabilization, sending
the class of `x` to the class of `x ∪ {x₀}`. -/
noncomputable def stabilizeEpsilonClassEquiv : H.EpsilonClass ≃ (H.stabilize r₀).EpsilonClass :=
  Quotient.congr (H.stabilizeGeneratorEquiv r₀) fun x y => by
    rw [stabilizeGeneratorEquiv_apply, stabilizeGeneratorEquiv_apply, epsilonSetoid_apply,
      epsilonSetoid_apply, ← epsilonClass_eq_epsilonClass_iff, ← epsilonClass_eq_epsilonClass_iff,
      epsilonClass_stabilizeGenerator_eq_iff]

/-- The identification sends the class of `x` to the class of `x ∪ {x₀}`. -/
@[simp]
theorem stabilizeEpsilonClassEquiv_epsilonClass (x : H.Generator) :
    H.stabilizeEpsilonClassEquiv r₀ (H.epsilonClass x) =
      (H.stabilize r₀).epsilonClass (H.stabilizeGenerator r₀ x) :=
  (Quotient.congr_mk _ _ x).trans (congrArg _ (H.stabilizeGeneratorEquiv_apply r₀ x))

/-- The identification of the hat chain groups by stabilization carries the summand of each
`ε`-class onto the summand of the corresponding class of the stabilized diagram. -/
theorem map_stabilizeChainEquiv_epsilonSummand (c : H.EpsilonClass) :
    (H.epsilonSummand (ZMod 2) c).map (H.stabilizeChainEquiv r₀).toLinearMap =
      (H.stabilize r₀).epsilonSummand (ZMod 2) (H.stabilizeEpsilonClassEquiv r₀ c) := by
  induction c using EpsilonClass.ind with
  | h z =>
    simp only [epsilonSummand, Finsupp.supported_eq_span_single, Submodule.map_span,
      ← Set.image_comp]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply, LinearEquiv.coe_coe,
      stabilizeChainEquiv_single, stabilizeEpsilonClassEquiv_epsilonClass]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, (H.epsilonClass_stabilizeGenerator_eq_iff r₀).mpr hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g
      rw [stabilizeGeneratorEquiv_apply] at hg ⊢
      exact ⟨x, (H.epsilonClass_stabilizeGenerator_eq_iff r₀).mp hg, rfl⟩

end Stabilization

section AddBasepoint

variable (r₀ : Region)

/-- Adding a basepoint does not change the `ε`-classes: the generators `(x, i)` and `(y, j)` of
the diagram with an added basepoint lie in the same class exactly when `x` and `y` lie in the same
class, whatever the new points `i` and `j`. -/
@[simp]
theorem epsilonClass_addBasepointGenerator_eq_iff {x y : H.Generator} {i j : Fin 2} :
    (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x i) =
        (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ y j) ↔
      H.epsilonClass x = H.epsilonClass y := by
  simp only [epsilonClass_eq_epsilonClass_iff_exists_isDomainBetween,
    isDomainBetween_addBasepoint_iff]
  refine ⟨fun ⟨D, hD, _⟩ => ⟨_, hD⟩, fun ⟨D, hD⟩ => ⟨Sum.elim D ![D r₀ + (j - i), 0, 0], ?_⟩⟩
  simpa using hD

/-- The identification of the `ε`-classes of a diagram with those of the diagram with an added
basepoint, sending the class of `x` to the common class of `(x, 0)` and `(x, 1)`. -/
noncomputable def addBasepointEpsilonClassEquiv :
    H.EpsilonClass ≃ (H.addBasepoint r₀).EpsilonClass :=
  Equiv.ofBijective
    (Quotient.lift (fun x => (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x 0))
      fun _ _ h => (H.epsilonClass_addBasepointGenerator_eq_iff r₀).mpr (Quotient.sound h))
    ⟨fun c d => by
      induction c using EpsilonClass.ind with
      | h x =>
        induction d using EpsilonClass.ind with
        | h y => exact (H.epsilonClass_addBasepointGenerator_eq_iff r₀).mp,
    fun c => by
      induction c using EpsilonClass.ind with
      | h g =>
        obtain ⟨⟨x, k⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
        rw [addBasepointGeneratorEquiv_apply]
        exact ⟨H.epsilonClass x, (H.epsilonClass_addBasepointGenerator_eq_iff r₀).mpr rfl⟩⟩

/-- The identification sends the class of `x` to the class of `(x, k)`, for either new point
`k`. -/
theorem addBasepointEpsilonClassEquiv_epsilonClass (x : H.Generator) (k : Fin 2) :
    H.addBasepointEpsilonClassEquiv r₀ (H.epsilonClass x) =
      (H.addBasepoint r₀).epsilonClass (H.addBasepointGenerator r₀ x k) :=
  (H.epsilonClass_addBasepointGenerator_eq_iff r₀).mpr rfl

end AddBasepoint

section LensSpace

variable {p : ℕ} [NeZero p] {q : (ZMod p)ˣ} {r : ZMod p}

/-- In the genus-one diagram of `L(p, q)` distinct generators lie in distinct `ε`-classes. -/
theorem epsilonClass_lensSpace_injective : Function.Injective (lensSpace p q r).epsilonClass :=
  fun _ _ h => epsilon_lensSpace_eq_zero_iff.mp (epsilonClass_eq_epsilonClass_iff.mp h)

/-- The genus-one diagram of `L(p, q)` has exactly `p` `ε`-classes, one for each of its
generators. -/
theorem card_epsilonClass_lensSpace : Nat.card (lensSpace p q r).EpsilonClass = p := by
  rw [← Nat.card_congr (Equiv.ofBijective _
      ⟨epsilonClass_lensSpace_injective, epsilonClass_surjective _⟩),
    ← Nat.card_congr (Equiv.ofBijective _ lensSpaceGenerator_bijective), Nat.card_zmod]

end LensSpace

end HeegaardRegionSystem

end TauCeti
