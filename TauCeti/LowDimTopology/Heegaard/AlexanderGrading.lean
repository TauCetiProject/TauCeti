/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.HatDifferential

/-!
# The relative Alexander grading of a doubly pointed Heegaard diagram

A knot `K` in a closed three-manifold `Y` is presented by a *doubly pointed* Heegaard diagram
`(Σ, α, β, w, z)`: the knot is an arc from `w` to `z` in the complement of the `α`-curves followed
by an arc from `z` back to `w` in the complement of the `β`-curves, both pushed into the two
handlebodies. The generators of the knot Floer complex are those of the diagram, and they carry
an *Alexander grading*. For generators `x`, `y` joined by a Whitney disk `φ`, Ozsváth and Szabó
show that the relative spin^c structures of `x` and `y` differ by `(n_z(φ) - n_w(φ)) PD[μ]`, where
`μ` is the meridian of the knot, so that

`A(x) - A(y) = n_z(φ) - n_w(φ)`.

The hat knot Floer differential counts disks with `n_w = n_z = 0`, so it preserves `A`; the hat
differential of the singly pointed diagram `(Σ, α, β, w)` of `Y` counts disks with `n_w = 0`,
and lowers `A` by `n_z ≥ 0`, so `A` is a filtration of `CF̂(Y)`.

This file defines this grading for the abstract region incidence data
`TauCeti.HeegaardRegionSystem`, in which two basepoints `w` and `z` are singled out among the
basepoints. As for the relative Maslov grading
(`TauCeti.LowDimTopology.Heegaard.RelativeGrading`), the value
`TauCeti.HeegaardRegionSystem.relativeAlexanderGrading w z x y` is computed from a chosen domain
`D` from `x` to `y` as `n_z(D) - n_w(D)`. Two domains from `x` to `y` differ by a domain from `x`
to itself, a domain whose boundary is a combination of whole curves. Its value `n_z - n_w` lies in
the subgroup `TauCeti.HeegaardRegionSystem.periodicAlexanderValues w z` of `ℤ`, and the class of
`n_z(D) - n_w(D)` modulo this subgroup does not depend on `D`. The whole surface has `n_z = n_w`,
so if the singly pointed diagram `(Σ, α, β, w)` has no nonzero periodic domain, as for a knot in
`S³`, the subgroup vanishes and the grading is an integer
(`TauCeti.HeegaardRegionSystem.periodicAlexanderValues_eq_bot_of_forall_eq_zero`). On a
geometric diagram its elements are, up to sign, the intersection numbers of the knot with the
closed surfaces obtained by capping off the periodic domains of `(Σ, α, β, w)`; that
identification, and the comparison of domains with Whitney disks and relative spin^c structures,
are geometric and are not formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.periodicAlexanderValues`: the values of `n_z - n_w` on the
  domains whose boundary is a combination of whole curves, a subgroup of `ℤ`.
* `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading`: the relative Alexander grading
  `A(x, y)`, computed from a chosen domain from `x` to `y`, or `0` when there is none.

## Main results

* `TauCeti.HeegaardRegionSystem.periodicAlexanderValues_eq_bot_of_forall_eq_zero`: the subgroup
  vanishes when the only domain avoiding `w` whose boundary is a combination of whole curves is
  zero.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeAlexanderGrading_eq`: modulo
  `periodicAlexanderValues w z`, the relative Alexander grading is `n_z(D) - n_w(D)` for every
  domain `D` from `x` to `y`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeAlexanderGrading_eq`: when the subgroup
  vanishes, it is `n_z(D) - n_w(D)` for every domain `D` from `x` to `y`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeAlexanderGrading_add` and
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeAlexanderGrading_swap`: additivity and
  antisymmetry, with their versions modulo the subgroup.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeAlexanderGrading_nonneg`: a nonnegative
  domain from `x` to `y` avoiding `w` has `A(x, y) ≥ 0`, so the Alexander grading filters the hat
  complex of the diagram pointed at `w`.
* `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero`: the
  hat differential of the doubly pointed diagram preserves the Alexander grading.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §2: doubly pointed diagrams, the
  relative spin^c difference `(n_z(φ) - n_w(φ)) PD[μ]` (Lemma 2.5) and the Alexander filtration.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section PeriodicAlexanderValues

variable (H) in
/-- The values of `n_z - n_w` on the domains whose boundary is a combination of whole curves,
that is, on the domains from any generator to itself; a subgroup of `ℤ`. The relative Alexander
grading is well defined modulo this subgroup
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeAlexanderGrading_eq`). -/
def periodicAlexanderValues (w z : Basepoint) : AddSubgroup ℤ where
  carrier := {k | ∃ E : Region → ℤ, H.alphaArcBoundary (H.alphaBoundary E) = 0 ∧
    H.betaArcBoundary (H.betaBoundary E) = 0 ∧ E (H.basepoint z) - E (H.basepoint w) = k}
  add_mem' := by
    rintro _ _ ⟨E, hEα, hEβ, rfl⟩ ⟨E', hE'α, hE'β, rfl⟩
    exact ⟨E + E', by simp [hEα, hE'α], by simp [hEβ, hE'β], by simp only [Pi.add_apply]; ring⟩
  zero_mem' := ⟨0, by simp, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨E, hEα, hEβ, rfl⟩
    exact ⟨-E, by simp [hEα], by simp [hEβ], by simp only [Pi.neg_apply]; ring⟩

variable {w z : Basepoint} {x y : H.Generator} {k : ℤ}

/-- An integer lies in `periodicAlexanderValues w z` when it is `n_z(E) - n_w(E)` for a domain
`E` whose `α`- and `β`-parts are cycles. -/
@[simp]
theorem mem_periodicAlexanderValues_iff :
    k ∈ H.periodicAlexanderValues w z ↔ ∃ E : Region → ℤ,
      H.alphaArcBoundary (H.alphaBoundary E) = 0 ∧ H.betaArcBoundary (H.betaBoundary E) = 0 ∧
        E (H.basepoint z) - E (H.basepoint w) = k :=
  Iff.rfl

/-- An integer lies in `periodicAlexanderValues w z` when it is `n_z(E) - n_w(E)` for a domain
`E` from a given generator `x` to itself. -/
theorem mem_periodicAlexanderValues_iff_exists_isDomainBetween (x : H.Generator) :
    k ∈ H.periodicAlexanderValues w z ↔
      ∃ E, H.IsDomainBetween x x E ∧ E (H.basepoint z) - E (H.basepoint w) = k := by
  simp only [mem_periodicAlexanderValues_iff, isDomainBetween_self_iff_arcBoundary_eq_zero,
    and_assoc]

/-- The value `n_z(E) - n_w(E)` of a domain from a generator to itself is a periodic Alexander
value. -/
theorem IsDomainBetween.sub_mem_periodicAlexanderValues {E : Region → ℤ}
    (hE : H.IsDomainBetween x x E) :
    E (H.basepoint z) - E (H.basepoint w) ∈ H.periodicAlexanderValues w z :=
  (mem_periodicAlexanderValues_iff_exists_isDomainBetween x).mpr ⟨E, hE, rfl⟩

/-- The periodic Alexander values vanish exactly when every domain whose boundary is a
combination of whole curves has the same multiplicity at `w` and at `z`. -/
theorem periodicAlexanderValues_eq_bot_iff :
    H.periodicAlexanderValues w z = ⊥ ↔ ∀ E : Region → ℤ,
      H.alphaArcBoundary (H.alphaBoundary E) = 0 → H.betaArcBoundary (H.betaBoundary E) = 0 →
        E (H.basepoint z) = E (H.basepoint w) := by
  rw [AddSubgroup.eq_bot_iff_forall]
  constructor
  · intro h E hα hβ
    exact sub_eq_zero.mp (h _ ⟨E, hα, hβ, rfl⟩)
  · rintro h _ ⟨E, hα, hβ, rfl⟩
    rw [h E hα hβ, sub_self]

/-- **A criterion for an integer Alexander grading.** If the only domain with multiplicity zero
at `w` whose boundary is a combination of whole curves is zero, that is, if the singly pointed
diagram `(Σ, α, β, w)` has no nonzero periodic domain, then the periodic Alexander values vanish:
a domain whose boundary is a combination of whole curves is a multiple of the whole surface, which
has the same multiplicity at `w` and at `z`. -/
theorem periodicAlexanderValues_eq_bot_of_forall_eq_zero
    (h : ∀ E : Region → ℤ, H.alphaArcBoundary (H.alphaBoundary E) = 0 →
      H.betaArcBoundary (H.betaBoundary E) = 0 → E (H.basepoint w) = 0 → E = 0) :
    H.periodicAlexanderValues w z = ⊥ := by
  refine periodicAlexanderValues_eq_bot_iff.mpr fun E hα hβ => ?_
  have hE := h (E - E (H.basepoint w) • 1)
    (by simp only [map_sub, map_zsmul, alphaBoundary_one, smul_zero, sub_zero, hα])
    (by simp only [map_sub, map_zsmul, betaBoundary_one, smul_zero, sub_zero, hβ]) (by simp)
  have hz := congrFun hE (H.basepoint z)
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
    Pi.zero_apply, sub_eq_zero] at hz
  exact hz

end PeriodicAlexanderValues

section RelativeAlexanderGrading

open scoped Classical in
variable (H) in
/-- The relative Alexander grading `A(x, y) = n_z(D) - n_w(D)` of two generators of a diagram
with basepoints `w` and `z`, for a chosen domain `D` from `x` to `y`, or `0` when no domain joins
them. Its class modulo `periodicAlexanderValues w z` does not depend on the choice of `D`
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeAlexanderGrading_eq`), and when that
subgroup vanishes neither does the value itself
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeAlexanderGrading_eq`). -/
noncomputable def relativeAlexanderGrading (w z : Basepoint) (x y : H.Generator) : ℤ :=
  if h : ∃ D, H.IsDomainBetween x y D then
    h.choose (H.basepoint z) - h.choose (H.basepoint w)
  else 0

variable {w z : Basepoint} {x y v : H.Generator} {D D' E : Region → ℤ}

/-- When no domain joins `x` to `y`, the relative Alexander grading is `0`. -/
theorem relativeAlexanderGrading_of_forall_not_isDomainBetween
    (h : ∀ D, ¬H.IsDomainBetween x y D) : H.relativeAlexanderGrading w z x y = 0 := by
  rw [relativeAlexanderGrading, dite_eq_right (not_exists.mpr h)]

/-- The values `n_z(D) - n_w(D)` of two domains `D`, `D'` from `x` to `y` differ by a periodic
Alexander value: `D - D'` is a domain from `x` to itself. -/
theorem IsDomainBetween.sub_sub_sub_mem_periodicAlexanderValues (hD : H.IsDomainBetween x y D)
    (hD' : H.IsDomainBetween x y D') :
    D (H.basepoint z) - D (H.basepoint w) - (D' (H.basepoint z) - D' (H.basepoint w)) ∈
      H.periodicAlexanderValues w z := by
  convert (hD.add hD'.neg).sub_mem_periodicAlexanderValues (w := w) (z := z) using 1
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- Modulo the periodic Alexander values, the relative Alexander grading is `n_z(D) - n_w(D)` for
every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.coe_relativeAlexanderGrading_eq (hD : H.IsDomainBetween x y D) :
    (H.relativeAlexanderGrading w z x y : ℤ ⧸ H.periodicAlexanderValues w z) =
      ((D (H.basepoint z) - D (H.basepoint w) : ℤ) : ℤ ⧸ H.periodicAlexanderValues w z) := by
  have h : ∃ D, H.IsDomainBetween x y D := ⟨D, hD⟩
  rw [QuotientAddGroup.eq_iff_sub_mem, relativeAlexanderGrading, dite_eq_left h]
  exact h.choose_spec.sub_sub_sub_mem_periodicAlexanderValues hD

/-- When the periodic Alexander values vanish, the relative Alexander grading is
`n_z(D) - n_w(D)` for every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.relativeAlexanderGrading_eq (hA : H.periodicAlexanderValues w z = ⊥)
    (hD : H.IsDomainBetween x y D) :
    H.relativeAlexanderGrading w z x y = D (H.basepoint z) - D (H.basepoint w) := by
  have h := QuotientAddGroup.eq_iff_sub_mem.mp (hD.coe_relativeAlexanderGrading_eq (w := w)
    (z := z))
  rwa [hA, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- A generator has relative Alexander grading zero with itself, modulo the periodic Alexander
values. -/
@[simp]
theorem coe_relativeAlexanderGrading_self :
    (H.relativeAlexanderGrading w z x x : ℤ ⧸ H.periodicAlexanderValues w z) = 0 := by
  simp [(isDomainBetween_zero x).coe_relativeAlexanderGrading_eq]

/-- A generator has relative Alexander grading zero with itself, when the periodic Alexander
values vanish. -/
@[simp]
theorem relativeAlexanderGrading_self (hA : H.periodicAlexanderValues w z = ⊥) :
    H.relativeAlexanderGrading w z x x = 0 := by
  simp [(isDomainBetween_zero x).relativeAlexanderGrading_eq hA]

/-- The relative Alexander grading is additive modulo the periodic Alexander values:
`A(x, y) + A(y, v) = A(x, v)` for generators joined by domains. -/
theorem IsDomainBetween.coe_relativeAlexanderGrading_add (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y v E) :
    ((H.relativeAlexanderGrading w z x y + H.relativeAlexanderGrading w z y v : ℤ) :
        ℤ ⧸ H.periodicAlexanderValues w z) = H.relativeAlexanderGrading w z x v := by
  rw [QuotientAddGroup.mk_add, hD.coe_relativeAlexanderGrading_eq,
    hE.coe_relativeAlexanderGrading_eq, (hD.add hE).coe_relativeAlexanderGrading_eq,
    ← QuotientAddGroup.mk_add]
  congr 1
  simp only [Pi.add_apply]
  ring

/-- The relative Alexander grading is additive, `A(x, y) + A(y, v) = A(x, v)` for generators
joined by domains, when the periodic Alexander values vanish. -/
theorem IsDomainBetween.relativeAlexanderGrading_add (hA : H.periodicAlexanderValues w z = ⊥)
    (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween y v E) :
    H.relativeAlexanderGrading w z x y + H.relativeAlexanderGrading w z y v =
      H.relativeAlexanderGrading w z x v := by
  rw [hD.relativeAlexanderGrading_eq hA, hE.relativeAlexanderGrading_eq hA,
    (hD.add hE).relativeAlexanderGrading_eq hA]
  simp only [Pi.add_apply]
  ring

/-- The relative Alexander grading is antisymmetric modulo the periodic Alexander values:
`A(y, x) = -A(x, y)` for generators joined by a domain. -/
theorem IsDomainBetween.coe_relativeAlexanderGrading_swap (hD : H.IsDomainBetween x y D) :
    (H.relativeAlexanderGrading w z y x : ℤ ⧸ H.periodicAlexanderValues w z) =
      -(H.relativeAlexanderGrading w z x y : ℤ ⧸ H.periodicAlexanderValues w z) := by
  rw [hD.neg.coe_relativeAlexanderGrading_eq, hD.coe_relativeAlexanderGrading_eq,
    ← QuotientAddGroup.mk_neg]
  congr 1
  simp only [Pi.neg_apply]
  ring

/-- The relative Alexander grading is antisymmetric, `A(y, x) = -A(x, y)` for generators joined
by a domain, when the periodic Alexander values vanish. -/
theorem IsDomainBetween.relativeAlexanderGrading_swap (hA : H.periodicAlexanderValues w z = ⊥)
    (hD : H.IsDomainBetween x y D) :
    H.relativeAlexanderGrading w z y x = -H.relativeAlexanderGrading w z x y := by
  rw [hD.neg.relativeAlexanderGrading_eq hA, hD.relativeAlexanderGrading_eq hA]
  simp only [Pi.neg_apply]
  ring

/-- **The Alexander filtration.** A nonnegative domain from `x` to `y` with multiplicity zero at
`w` has `A(x, y) = n_z(D) ≥ 0`. So the hat differential of the singly pointed diagram
`(Σ, α, β, w)`, whose disks have nonnegative domains avoiding `w`, does not raise the Alexander
grading. -/
theorem IsDomainBetween.relativeAlexanderGrading_nonneg (hA : H.periodicAlexanderValues w z = ⊥)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hw : D (H.basepoint w) = 0) :
    0 ≤ H.relativeAlexanderGrading w z x y := by
  rw [hD.relativeAlexanderGrading_eq hA, hw, sub_zero]
  exact hD0 _

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- A domain counted by the hat differential has multiplicity zero at both `w` and `z`, so it
joins generators of the same Alexander grading, when the periodic Alexander values vanish. -/
theorem relativeAlexanderGrading_eq_zero_of_mem_hatDomains
    (hA : H.periodicAlexanderValues w z = ⊥) (hD : D ∈ H.hatDomains χ x y) :
    H.relativeAlexanderGrading w z x y = 0 := by
  obtain ⟨hD, hz, -⟩ := mem_hatDomains_iff.mp hD
  rw [hD.relativeAlexanderGrading_eq hA, hz, hz, sub_self]

/-- **The hat differential preserves the Alexander grading.** When the periodic Alexander values
vanish, a nonzero coefficient of the hat differential of a diagram with basepoints `w` and `z`
joins generators of the same Alexander grading. For a doubly pointed diagram of a knot, this is
the hat knot Floer differential. -/
theorem relativeAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero
    (hA : H.periodicAlexanderValues w z = ⊥) (h : H.hatCoefficient χ x y ≠ 0) :
    H.relativeAlexanderGrading w z x y = 0 :=
  have ⟨_, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero h
  relativeAlexanderGrading_eq_zero_of_mem_hatDomains hA hD

end RelativeAlexanderGrading

end HeegaardRegionSystem

end TauCeti
