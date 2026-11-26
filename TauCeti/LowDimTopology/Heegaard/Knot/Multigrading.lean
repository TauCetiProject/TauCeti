/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AlexanderGrading
public import TauCeti.LowDimTopology.Heegaard.AlphaComponent
public import TauCeti.LowDimTopology.Heegaard.Knot.Full

/-!
# The relative Alexander multigrading of a multi-pointed link diagram

A link `L = L₁ ∪ ⋯ ∪ L_ℓ` in a closed three-manifold is presented by a multi-pointed Heegaard
diagram `(Σ, α, β, w, z)`, in which every basepoint is a `w` or a `z` of one of the components
`L_q`. The generators of the link Floer complex carry one Alexander grading for each component.
For generators `x`, `y` joined by a Whitney disk `φ`, the `q`-th grading changes by the
multiplicities of `φ` at the basepoints of `L_q`:

`A_q(x) - A_q(y) = ∑_{z ∈ L_q} n_z(φ) - ∑_{w ∈ L_q} n_w(φ)`.

For a knot, with a single `w` and a single `z`, this is the relative Alexander grading
`n_z(φ) - n_w(φ)` of `TauCeti.LowDimTopology.Heegaard.AlexanderGrading`.

This file defines the multigrading for the abstract region incidence data
`TauCeti.HeegaardRegionSystem`. The components are indexed by a type `K`, and
`ws q, zs q : Finset Basepoint` are the `w`'s and the `z`'s of the component `q`. The multiplicity
vector `q ↦ ∑_{z ∈ zs q} n_z(D) - ∑_{w ∈ ws q} n_w(D)` of a domain `D` is additive in `D`
(`TauCeti.HeegaardRegionSystem.componentAlexanderMultiplicity`). As for a knot, the relative
multigrading `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading ws zs x y : K → ℤ` is
computed from a chosen domain from `x` to `y`. Two such domains differ by a domain from `x` to
itself, whose multiplicity vector lies in the subgroup
`TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues ws zs` of `K → ℤ`, and the class of
the multigrading modulo this subgroup does not depend on the choice.

In a link diagram in the sense of Ozsváth and Szabó, each component of `Σ - α` contains exactly
one `w` and one `z`, both on the same component of the link, so the domain of that component of
`Σ - α` has vanishing multiplicity vector. Every domain from a generator to itself is a combination
of these components plus a domain with multiplicity zero at the `w`'s, so the subgroup vanishes,
and the multigrading is a vector of integers, as soon as the multiplicity vector vanishes on the
latter domains
(`TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues_eq_bot_of_forall_eq_zero`). With
two or more `w`'s these need not be zero: if `A` and `B` are the components of `Σ - α` and of
`Σ - β` through the same `w`, then `A - B` is one of them. For a link in `S³` they are combinations
of components of `Σ - α` and of `Σ - β`, each with vanishing multiplicity vector, but the
components of `Σ - β` are not formalized here, so the results below that need the subgroup to
vanish take this as a hypothesis.

The multigrading has the properties that the link Floer complex uses.

* It is additive and antisymmetric, and a nonnegative domain from `x` to `y` avoiding the `w`'s
  of `L_q` has `A_q(x, y) ≥ 0`: the `q`-th grading filters the complex of the diagram pointed at
  those `w`'s.
* A term `∏_b X_b ^ m b · y` of the full multi-pointed differential of `x`
  (`TauCeti.LowDimTopology.Heegaard.Knot.Full`) has
  `A_q(x, y) = ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w`
  (`relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero`), so grading the
  variable `X_z` of a `z` on `L_q` by `+1` in the `q`-th grading and that of a `w` on `L_q` by
  `-1`, the full differential preserves every Alexander grading. In particular the hat
  differential, which counts domains avoiding all the basepoints, preserves each `A_q`.
* When every basepoint other than the `w`'s is a `z` of exactly one component, the sum of the
  component gradings relative to a fixed generator is an Alexander function for the `w`'s
  (`TauCeti.HeegaardRegionSystem.isAlexanderFunction_sum_relativeComponentAlexanderGrading`), so
  the single Alexander filtration of the hat complex is that of the total grading `∑_q A_q`.
* For one component with one `w` and one `z` it is the relative Alexander grading of a knot
  (`TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading_singleton`).

As for the knot grading, the comparison of domains with Whitney disks and of the multigrading with
relative spin^c structures is geometric and is not formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.componentAlexanderMultiplicity`: the vector of the differences
  `∑_{z ∈ zs q} n_z(D) - ∑_{w ∈ ws q} n_w(D)`, an additive map of domains.
* `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues`: its values on the domains whose
  boundary is a combination of whole curves.
* `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading`: the relative Alexander
  multigrading `A(x, y) : K → ℤ`, computed from a chosen domain from `x` to `y`, or `0` when there
  is none.

## Main results

* `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues_eq_bot_of_forall_eq_zero`:
  the subgroup vanishes for a link diagram when the multiplicity vector vanishes on the domains
  with multiplicity zero at the `w`'s whose boundary is a combination of whole curves.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeComponentAlexanderGrading_eq` and
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeComponentAlexanderGrading_eq`: the
  multigrading is the multiplicity vector of every domain from `x` to `y`, modulo the subgroup, or
  exactly when it vanishes.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeComponentAlexanderGrading_add`,
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeComponentAlexanderGrading_swap` and
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeComponentAlexanderGrading_nonneg`:
  additivity, antisymmetry and the filtration by each component grading.
* In the namespace `TauCeti.HeegaardRegionSystem`,
  `relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero` and
  `relativeComponentAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero`: the gradings of the terms
  of the full and the hat differentials.
* `TauCeti.HeegaardRegionSystem.isAlexanderFunction_sum_relativeComponentAlexanderGrading`: the
  total grading is an Alexander function.
* `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading_singleton` and
  `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues_singleton_eq_bot_iff`: the
  comparison with the relative Alexander grading of a knot.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks, link invariants and the multi-variable Alexander
  polynomial*, Algebr. Geom. Topol. **8** (2008),
  [arXiv:math/0512286](https://arxiv.org/abs/math/0512286), §3: multi-pointed diagrams of links
  and the Alexander multigrading.
* C. Manolescu, P. Ozsváth, Z. Szabó and D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. **11** (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), §2: the
  multigrading computed from several basepoints on each component.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint} {K : Type*}

section Multiplicity

variable (H) in
/-- The **Alexander multiplicity vector** of a domain `D` for a link diagram whose component `q`
carries the basepoints `ws q` (the `w`'s) and `zs q` (the `z`'s): its component at `q` is
`∑_{z ∈ zs q} n_z(D) - ∑_{w ∈ ws q} n_w(D)`. It is additive in `D`. -/
def componentAlexanderMultiplicity (ws zs : K → Finset Basepoint) : (Region → ℤ) →+ (K → ℤ) where
  toFun D q := ∑ b ∈ zs q, D (H.basepoint b) - ∑ b ∈ ws q, D (H.basepoint b)
  map_zero' := by
    ext q
    simp
  map_add' D E := by
    ext q
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring

variable {ws zs : K → Finset Basepoint}

@[simp]
theorem componentAlexanderMultiplicity_apply (D : Region → ℤ) (q : K) :
    H.componentAlexanderMultiplicity ws zs D q =
      ∑ b ∈ zs q, D (H.basepoint b) - ∑ b ∈ ws q, D (H.basepoint b) :=
  (rfl)

/-- The whole surface has multiplicity one at every basepoint, so its Alexander multiplicity at
`q` is the number of `z`'s minus the number of `w`'s of the component `q`. -/
theorem componentAlexanderMultiplicity_one (q : K) :
    H.componentAlexanderMultiplicity ws zs 1 q = (zs q).card - (ws q).card := by
  simp

end Multiplicity

section PeriodicValues

variable (H) in
/-- The values of the Alexander multiplicity vector on the domains whose boundary is a combination
of whole curves, that is, on the domains from any generator to itself; a subgroup of `K → ℤ`. The
relative Alexander multigrading is well defined modulo this subgroup
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeComponentAlexanderGrading_eq`). -/
def periodicComponentAlexanderValues (ws zs : K → Finset Basepoint) : AddSubgroup (K → ℤ) :=
  ((H.alphaArcBoundary.comp H.alphaBoundary).ker ⊓
    (H.betaArcBoundary.comp H.betaBoundary).ker).map (H.componentAlexanderMultiplicity ws zs)

variable {ws zs : K → Finset Basepoint} {x y : H.Generator} {v : K → ℤ}

/-- A vector lies in `periodicComponentAlexanderValues ws zs` when it is the Alexander
multiplicity vector of a domain whose `α`- and `β`-parts are cycles. -/
@[simp]
theorem mem_periodicComponentAlexanderValues_iff :
    v ∈ H.periodicComponentAlexanderValues ws zs ↔ ∃ E : Region → ℤ,
      H.alphaArcBoundary (H.alphaBoundary E) = 0 ∧ H.betaArcBoundary (H.betaBoundary E) = 0 ∧
        H.componentAlexanderMultiplicity ws zs E = v := by
  simp [periodicComponentAlexanderValues, and_assoc]

/-- A vector lies in `periodicComponentAlexanderValues ws zs` when it is the Alexander
multiplicity vector of a domain from a given generator `x` to itself. -/
theorem mem_periodicComponentAlexanderValues_iff_exists_isDomainBetween (x : H.Generator) :
    v ∈ H.periodicComponentAlexanderValues ws zs ↔
      ∃ E, H.IsDomainBetween x x E ∧ H.componentAlexanderMultiplicity ws zs E = v := by
  simp only [mem_periodicComponentAlexanderValues_iff,
    isDomainBetween_self_iff_arcBoundary_eq_zero, and_assoc]

/-- The Alexander multiplicity vector of a domain from a generator to itself is a periodic
value. -/
theorem IsDomainBetween.componentAlexanderMultiplicity_mem_periodicComponentAlexanderValues
    {E : Region → ℤ} (hE : H.IsDomainBetween x x E) :
    H.componentAlexanderMultiplicity ws zs E ∈ H.periodicComponentAlexanderValues ws zs :=
  (mem_periodicComponentAlexanderValues_iff_exists_isDomainBetween x).mpr ⟨E, hE, rfl⟩

/-- The periodic values vanish exactly when every domain whose boundary is a combination of whole
curves has vanishing Alexander multiplicity vector. -/
theorem periodicComponentAlexanderValues_eq_bot_iff :
    H.periodicComponentAlexanderValues ws zs = ⊥ ↔ ∀ E : Region → ℤ,
      H.alphaArcBoundary (H.alphaBoundary E) = 0 → H.betaArcBoundary (H.betaBoundary E) = 0 →
        H.componentAlexanderMultiplicity ws zs E = 0 := by
  rw [AddSubgroup.eq_bot_iff_forall]
  refine ⟨fun h E hα hβ => h _ (mem_periodicComponentAlexanderValues_iff.mpr ⟨E, hα, hβ, rfl⟩),
    fun h v hv => ?_⟩
  obtain ⟨E, hα, hβ, rfl⟩ := mem_periodicComponentAlexanderValues_iff.mp hv
  exact h E hα hβ

/-- **A criterion for an integral Alexander multigrading.** Let `ι` pick out the `w`'s of a link
diagram, lying in distinct components of `Σ - α`, and suppose that the domain of each of these
components has vanishing Alexander multiplicity vector, as when it contains exactly one `w` and
one `z`, both on the same component of the link. If every domain with multiplicity zero at the
`w`'s whose boundary is a combination of whole curves has vanishing Alexander multiplicity vector,
then the periodic values vanish: a domain whose boundary is a combination of whole curves is such
a domain plus a combination of these components of `Σ - α`. With two or more `w`'s, the domains
with multiplicity zero at the `w`'s include the differences `A - B` of the components of `Σ - α`
and `Σ - β` through the same `w`, so `hP` does not ask them to be zero. -/
theorem periodicComponentAlexanderValues_eq_bot_of_forall_eq_zero {W : Type*} [Finite W]
    {ι : W → Basepoint}
    (hι : ∀ i j, H.SameAlphaComponent (H.basepoint (ι i)) (H.basepoint (ι j)) → i = j)
    (hP : ∀ P : Region → ℤ, H.alphaArcBoundary (H.alphaBoundary P) = 0 →
      H.betaArcBoundary (H.betaBoundary P) = 0 → (∀ i, P (H.basepoint (ι i)) = 0) →
        H.componentAlexanderMultiplicity ws zs P = 0)
    (hA : ∀ i, H.componentAlexanderMultiplicity ws zs
      (H.alphaComponentDomain (H.basepoint (ι i))) = 0) :
    H.periodicComponentAlexanderValues ws zs = ⊥ := by
  have := Fintype.ofFinite W
  refine periodicComponentAlexanderValues_eq_bot_iff.mpr fun E hα hβ => ?_
  -- `E` minus its components of `Σ - α` through the `w`'s vanishes at the `w`'s
  have hE : H.componentAlexanderMultiplicity ws zs E = H.componentAlexanderMultiplicity ws zs
      (∑ i, E (H.basepoint (ι i)) • H.alphaComponentDomain (H.basepoint (ι i))) := by
    rw [← sub_eq_zero, ← map_sub]
    refine hP _ (by simp only [map_sub, map_sum, map_zsmul, hα, smul_zero, Finset.sum_const_zero,
        alphaArcBoundary_alphaBoundary_alphaComponentDomain, sub_zero])
      (by simp only [map_sub, map_sum, map_zsmul, hβ, betaBoundary_alphaComponentDomain,
        smul_zero, Finset.sum_const_zero, sub_zero]) fun j => ?_
    rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single j (fun i _ hij => ?_) (by simp),
      Pi.smul_apply, alphaComponentDomain_self, smul_eq_mul, mul_one, sub_self]
    rw [Pi.smul_apply, alphaComponentDomain_of_not_sameAlphaComponent fun h =>
      hij (hι j i h).symm, smul_zero]
  rw [hE, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_zsmul, hA i, smul_zero]

end PeriodicValues

section RelativeGrading

open scoped Classical in
variable (H) in
/-- The **relative Alexander multigrading** `A(x, y) : K → ℤ` of two generators of a link diagram
whose component `q` carries the basepoints `ws q` and `zs q`: the Alexander multiplicity vector
`q ↦ ∑_{z ∈ zs q} n_z(D) - ∑_{w ∈ ws q} n_w(D)` of a chosen domain `D` from `x` to `y`, or `0`
when no domain joins them. Its class modulo `periodicComponentAlexanderValues ws zs` does not
depend on the choice of `D`
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeComponentAlexanderGrading_eq`), and
when that subgroup vanishes neither does the value itself
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeComponentAlexanderGrading_eq`). -/
noncomputable def relativeComponentAlexanderGrading (ws zs : K → Finset Basepoint)
    (x y : H.Generator) : K → ℤ :=
  if h : ∃ D, H.IsDomainBetween x y D then H.componentAlexanderMultiplicity ws zs h.choose else 0

variable {ws zs : K → Finset Basepoint} {x y v : H.Generator} {D E : Region → ℤ}

/-- When no domain joins `x` to `y`, the relative Alexander multigrading is `0`. -/
theorem relativeComponentAlexanderGrading_of_forall_not_isDomainBetween
    (h : ∀ D, ¬H.IsDomainBetween x y D) : H.relativeComponentAlexanderGrading ws zs x y = 0 := by
  rw [relativeComponentAlexanderGrading, dite_eq_right (not_exists.mpr h)]

/-- The Alexander multiplicity vectors of two domains from `x` to `y` differ by a periodic
value: their difference is a domain from `x` to itself. -/
theorem IsDomainBetween.sub_mem_periodicComponentAlexanderValues
    (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween x y E) :
    H.componentAlexanderMultiplicity ws zs D - H.componentAlexanderMultiplicity ws zs E ∈
      H.periodicComponentAlexanderValues ws zs := by
  rw [← map_sub, sub_eq_add_neg]
  exact (hD.add hE.neg).componentAlexanderMultiplicity_mem_periodicComponentAlexanderValues

/-- Modulo the periodic values, the relative Alexander multigrading is the Alexander multiplicity
vector of every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.coe_relativeComponentAlexanderGrading_eq (hD : H.IsDomainBetween x y D) :
    (H.relativeComponentAlexanderGrading ws zs x y :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) =
      (H.componentAlexanderMultiplicity ws zs D :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) := by
  have h : ∃ D, H.IsDomainBetween x y D := ⟨D, hD⟩
  rw [QuotientAddGroup.eq_iff_sub_mem, relativeComponentAlexanderGrading, dite_eq_left h]
  exact h.choose_spec.sub_mem_periodicComponentAlexanderValues hD

/-- When the periodic values vanish, the relative Alexander multigrading is the Alexander
multiplicity vector of every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.relativeComponentAlexanderGrading_eq
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) (hD : H.IsDomainBetween x y D) :
    H.relativeComponentAlexanderGrading ws zs x y = H.componentAlexanderMultiplicity ws zs D := by
  have h := QuotientAddGroup.eq_iff_sub_mem.mp
    (hD.coe_relativeComponentAlexanderGrading_eq (ws := ws) (zs := zs))
  rwa [hA, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- A generator has relative Alexander multigrading zero with itself, modulo the periodic
values. -/
@[simp]
theorem coe_relativeComponentAlexanderGrading_self :
    (H.relativeComponentAlexanderGrading ws zs x x :
      (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) = 0 := by
  simp [(isDomainBetween_zero x).coe_relativeComponentAlexanderGrading_eq]

/-- A generator has relative Alexander multigrading zero with itself, when the periodic values
vanish. -/
@[simp]
theorem relativeComponentAlexanderGrading_self
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) :
    H.relativeComponentAlexanderGrading ws zs x x = 0 := by
  simp [(isDomainBetween_zero x).relativeComponentAlexanderGrading_eq hA]

/-- The relative Alexander multigrading is additive modulo the periodic values:
`A(x, y) + A(y, v) = A(x, v)` for generators joined by domains. -/
theorem IsDomainBetween.coe_relativeComponentAlexanderGrading_add (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y v E) :
    ((H.relativeComponentAlexanderGrading ws zs x y +
          H.relativeComponentAlexanderGrading ws zs y v : K → ℤ) :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) =
      H.relativeComponentAlexanderGrading ws zs x v := by
  rw [QuotientAddGroup.mk_add, hD.coe_relativeComponentAlexanderGrading_eq,
    hE.coe_relativeComponentAlexanderGrading_eq,
    (hD.add hE).coe_relativeComponentAlexanderGrading_eq, map_add, QuotientAddGroup.mk_add]

/-- The relative Alexander multigrading is additive, `A(x, y) + A(y, v) = A(x, v)` for generators
joined by domains, when the periodic values vanish. -/
theorem IsDomainBetween.relativeComponentAlexanderGrading_add
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y v E) :
    H.relativeComponentAlexanderGrading ws zs x y + H.relativeComponentAlexanderGrading ws zs y v =
      H.relativeComponentAlexanderGrading ws zs x v := by
  rw [hD.relativeComponentAlexanderGrading_eq hA, hE.relativeComponentAlexanderGrading_eq hA,
    (hD.add hE).relativeComponentAlexanderGrading_eq hA, map_add]

/-- The relative Alexander multigrading is antisymmetric modulo the periodic values:
`A(y, x) = -A(x, y)` for generators joined by a domain. -/
theorem IsDomainBetween.coe_relativeComponentAlexanderGrading_swap
    (hD : H.IsDomainBetween x y D) :
    (H.relativeComponentAlexanderGrading ws zs y x :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) =
      -(H.relativeComponentAlexanderGrading ws zs x y :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) := by
  rw [hD.neg.coe_relativeComponentAlexanderGrading_eq, hD.coe_relativeComponentAlexanderGrading_eq,
    map_neg, QuotientAddGroup.mk_neg]

/-- The relative Alexander multigrading is antisymmetric, `A(y, x) = -A(x, y)` for generators
joined by a domain, when the periodic values vanish. -/
theorem IsDomainBetween.relativeComponentAlexanderGrading_swap
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) (hD : H.IsDomainBetween x y D) :
    H.relativeComponentAlexanderGrading ws zs y x =
      -H.relativeComponentAlexanderGrading ws zs x y := by
  rw [hD.neg.relativeComponentAlexanderGrading_eq hA, hD.relativeComponentAlexanderGrading_eq hA,
    map_neg]

/-- **The filtration by a component grading.** A nonnegative domain from `x` to `y` with
multiplicity zero at the `w`'s of the component `q` has `A_q(x, y) = ∑_{z ∈ zs q} n_z(D) ≥ 0`.
So the hat differential of the diagram pointed at those `w`'s does not raise the `q`-th Alexander
grading. -/
theorem IsDomainBetween.relativeComponentAlexanderGrading_nonneg
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D) {q : K} (hw : ∀ b ∈ ws q, D (H.basepoint b) = 0) :
    0 ≤ H.relativeComponentAlexanderGrading ws zs x y q := by
  rw [hD.relativeComponentAlexanderGrading_eq hA, componentAlexanderMultiplicity_apply,
    Finset.sum_eq_zero hw, sub_zero]
  exact Finset.sum_nonneg fun b _ => hD0 _

section Differentials

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- A domain counted by the hat differential has multiplicity zero at every basepoint, so it joins
generators of the same Alexander multigrading, when the periodic values vanish. -/
theorem relativeComponentAlexanderGrading_eq_zero_of_mem_hatDomains
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) (hD : D ∈ H.hatDomains χ x y) :
    H.relativeComponentAlexanderGrading ws zs x y = 0 := by
  obtain ⟨hD, hb, -⟩ := mem_hatDomains_iff.mp hD
  ext q
  simp [hD.relativeComponentAlexanderGrading_eq hA, hb]

/-- **The hat differential preserves the Alexander multigrading.** When the periodic values
vanish, a nonzero coefficient of the hat differential of a link diagram, which counts the domains
avoiding all the basepoints, joins generators of the same Alexander multigrading. -/
theorem relativeComponentAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) (h : H.hatCoefficient χ x y ≠ 0) :
    H.relativeComponentAlexanderGrading ws zs x y = 0 :=
  have ⟨_, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero h
  relativeComponentAlexanderGrading_eq_zero_of_mem_hatDomains hA hD

variable [Fintype Basepoint]

/-- **The full differential preserves the Alexander multigrading**, modulo the periodic values. A
term `∏_b X_b ^ m b` of the full coefficient from `x` to `y` has relative Alexander multigrading
`A_q(x, y) = ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w`. -/
theorem coe_relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero
    {m : Basepoint →₀ ℕ} (h : (H.fullCoefficient χ x y).coeff m ≠ 0) :
    (H.relativeComponentAlexanderGrading ws zs x y :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) =
      ((fun q => ∑ b ∈ zs q, (m b : ℤ) - ∑ b ∈ ws q, (m b : ℤ) : K → ℤ) :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) := by
  obtain ⟨D, hD, hm⟩ := exists_mem_minusDomains_of_coeff_fullCoefficient_ne_zero h
  rw [(mem_minusDomains_iff.mp hD).1.coe_relativeComponentAlexanderGrading_eq]
  congr 1
  ext q
  simp [hm]

/-- **The full differential preserves the Alexander multigrading.** When the periodic values
vanish, a term `∏_b X_b ^ m b` of the full coefficient from `x` to `y` has
relative Alexander multigrading `A_q(x, y) = ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w`. Grading
`∏_b X_b ^ m b · y` by `A_q(y) + ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w` in the `q`-th grading, the
full differential preserves every Alexander grading. -/
theorem relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) {m : Basepoint →₀ ℕ}
    (h : (H.fullCoefficient χ x y).coeff m ≠ 0) (q : K) :
    H.relativeComponentAlexanderGrading ws zs x y q =
      ∑ b ∈ zs q, (m b : ℤ) - ∑ b ∈ ws q, (m b : ℤ) := by
  obtain ⟨D, hD, hm⟩ := exists_mem_minusDomains_of_coeff_fullCoefficient_ne_zero h
  simp [(mem_minusDomains_iff.mp hD).1.relativeComponentAlexanderGrading_eq hA, hm]

end Differentials

/-- **The total Alexander grading.** Let `ι` pick out the `w`'s, and suppose that every `w` of a
component is one of them and every other basepoint is a `z` of exactly one component. When the
periodic values vanish, the sum `∑_q A_q(x, x₀)` of the component gradings relative to a generator
`x₀` joined to every generator by a domain is an Alexander function for the `w`'s: a domain `D`
from `x` to `y` avoiding the `w`'s changes it by its total multiplicity at the `z`'s. -/
theorem isAlexanderFunction_sum_relativeComponentAlexanderGrading [Fintype Basepoint] [Fintype K]
    {W : Type*} {ι : W → Basepoint} (hws : ∀ q, ∀ b ∈ ws q, b ∈ Set.range ι)
    (hzs : ∀ b ∉ Set.range ι, ∃! q, b ∈ zs q)
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) {x₀ : H.Generator}
    (hx₀ : ∀ x, ∃ E, H.IsDomainBetween x x₀ E) :
    H.IsAlexanderFunction ι (fun x => ∑ q, H.relativeComponentAlexanderGrading ws zs x x₀ q) := by
  classical
  rw [isAlexanderFunction_iff]
  intro x y D hD hw
  obtain ⟨E, hE⟩ := hx₀ y
  have hD0 : ∀ b ∈ Set.range ι, D (H.basepoint b) = 0 := by
    rintro _ ⟨i, rfl⟩
    exact hw i
  rw [← hD.relativeComponentAlexanderGrading_add hA hE]
  simp only [Pi.add_apply, Finset.sum_add_distrib, add_sub_cancel_right,
    hD.relativeComponentAlexanderGrading_eq hA, componentAlexanderMultiplicity_apply,
    Finset.sum_eq_zero fun b hb => hD0 b (hws _ b hb), sub_zero]
  -- count each basepoint once for every component carrying it as a `z`
  have hsum (q : K) : ∑ b ∈ zs q, D (H.basepoint b) =
      ∑ b, if b ∈ zs q then D (H.basepoint b) else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [hsum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ Set.range ι
  · simp [hD0 b hb]
  · obtain ⟨q, hq, huniq⟩ := hzs b hb
    rw [Finset.sum_eq_single q (fun q' _ hq' => ite_eq_right fun h => hq' (huniq q' h)) (by simp),
      ite_eq_left hq]

/-- For a single component with the basepoints `w` and `z`, the periodic values vanish exactly
when the periodic Alexander values of the knot do. -/
theorem periodicComponentAlexanderValues_singleton_eq_bot_iff (w z : Basepoint) :
    H.periodicComponentAlexanderValues (fun _ : Unit => {w}) (fun _ => {z}) = ⊥ ↔
      H.periodicAlexanderValues w z = ⊥ := by
  rw [periodicComponentAlexanderValues_eq_bot_iff, periodicAlexanderValues_eq_bot_iff]
  refine forall₃_congr fun E _ _ => ?_
  simp [funext_iff, sub_eq_zero]


/-- For a single component with the basepoints `w` and `z`, the relative Alexander multigrading is
the relative Alexander grading `n_z(D) - n_w(D)` of a knot, when the periodic Alexander values
vanish. -/
theorem relativeComponentAlexanderGrading_singleton {w z : Basepoint}
    (hA : H.periodicAlexanderValues w z = ⊥) (x y : H.Generator) :
    H.relativeComponentAlexanderGrading (fun _ : Unit => {w}) (fun _ => {z}) x y () =
      H.relativeAlexanderGrading w z x y := by
  by_cases h : ∃ D, H.IsDomainBetween x y D
  · obtain ⟨D, hD⟩ := h
    rw [hD.relativeComponentAlexanderGrading_eq
      ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA),
      hD.relativeAlexanderGrading_eq hA]
    simp
  · rw [relativeComponentAlexanderGrading_of_forall_not_isDomainBetween (not_exists.mp h),
      relativeAlexanderGrading_of_forall_not_isDomainBetween (not_exists.mp h), Pi.zero_apply]

end RelativeGrading

end HeegaardRegionSystem

end TauCeti
