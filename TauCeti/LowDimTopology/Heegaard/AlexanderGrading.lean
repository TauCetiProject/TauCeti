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

The grading is constructed for links. A link `L = L₁ ∪ ⋯ ∪ L_ℓ` is presented by a multi-pointed
diagram in which every basepoint is a `w` or a `z` of one of the components `L_q`, and the
generators carry one Alexander grading for each component, with
`A_q(x) - A_q(y) = ∑_{z ∈ L_q} n_z(φ) - ∑_{w ∈ L_q} n_w(φ)`. Here the components are indexed by a
type `K`, and `ws q, zs q : Finset Basepoint` are the `w`'s and the `z`'s of the component `q`.
The multiplicity vector `q ↦ ∑_{z ∈ zs q} n_z(D) - ∑_{w ∈ ws q} n_w(D)` of a domain `D` is additive
in `D` (`TauCeti.HeegaardRegionSystem.componentAlexanderMultiplicity`), and the relative
multigrading `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading ws zs x y : K → ℤ` is
computed from a chosen domain from `x` to `y`. It is well defined modulo the subgroup
`TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues ws zs` of `K → ℤ`. The grading of
a knot is the case of a single component, indexed by `Unit`, with one `w` and one `z`:
`relativeAlexanderGrading w z` is the value of the multigrading at that component, and
`periodicAlexanderValues w z` is the image of its periodic values. The integrality of the
multigrading of a link diagram and its behaviour under the full multi-pointed differential are in
`TauCeti.LowDimTopology.Heegaard.Knot.Multigrading`.

The filtration is made explicit for any number of basepoints. The diagram `H` carries all the
basepoints, the `w`'s and the `z`'s, and `H.withBasepoints (H.basepoint ∘ ι)` keeps only the `w`'s,
picked out by `ι`. An Alexander function `A` on the generators
(`TauCeti.HeegaardRegionSystem.IsAlexanderFunction`) satisfies `A(x) - A(y) = ∑_b n_b(D)` for the
domains `D` from `x` to `y` avoiding the `w`'s, so that `A(x) - A(y)` is the total multiplicity
of `D` at the `z`'s. For a doubly pointed diagram whose periodic Alexander values vanish, the
relative Alexander gradings to a generator joined to every generator by a domain are such a
function (`TauCeti.HeegaardRegionSystem.isAlexanderFunction_relativeAlexanderGrading`), the case
of a single component of the corresponding result for a link diagram in which every basepoint
other than the `w`'s is a `z` of exactly one component: there the sum `∑_q A_q` of the
component gradings to such a generator is an Alexander function
(`TauCeti.HeegaardRegionSystem.isAlexanderFunction_sum_relativeComponentAlexanderGrading`).
For the multipointed diagram of a grid, with the `O`-markings as `w`'s and the `X`-markings as
`z`'s, the requirement is the relation `A(x) - A(y) = n_X(D) - n_O(D)` of Manolescu, Ozsváth and
Sarkar on these domains; that diagram is not constructed here. The hat differential of the diagram
pointed at the `w`'s then maps the chains supported in Alexander gradings at most `k` to chains
supported there, and the map it induces on the quotient by the chains in gradings below `k` is the
hat differential of `H`, which counts only the domains with `n_z = 0`. This distinguishes the
filtered differential, which counts the domains avoiding the `w`'s with any multiplicity at the
`z`'s, from its associated graded differential.

## Main definitions

* `TauCeti.HeegaardRegionSystem.componentAlexanderMultiplicity`: the vector of the differences
  `∑_{z ∈ zs q} n_z(D) - ∑_{w ∈ ws q} n_w(D)`, an additive map of domains.
* `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues`: its values on the domains whose
  boundary is a combination of whole curves.
* `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading`: the relative Alexander
  multigrading `A(x, y) : K → ℤ`, computed from a chosen domain from `x` to `y`, or `0` when there
  is none.
* `TauCeti.HeegaardRegionSystem.IsAlexanderFunction`: `A(x) - A(y)` is the total multiplicity at
  the basepoints of every domain from `x` to `y` avoiding the basepoints picked out by `ι`.
* `TauCeti.HeegaardRegionSystem.periodicAlexanderValues`: the values of `n_z - n_w` on the
  domains whose boundary is a combination of whole curves, a subgroup of `ℤ`.
* `TauCeti.HeegaardRegionSystem.relativeAlexanderGrading`: the relative Alexander grading
  `A(x, y)`, computed from a chosen domain from `x` to `y`, or `0` when there is none.

## Main results

* In the namespace `TauCeti.HeegaardRegionSystem.IsDomainBetween`,
  `coe_relativeComponentAlexanderGrading_eq` and `relativeComponentAlexanderGrading_eq`: the
  multigrading is the multiplicity vector of every domain from `x` to `y`, modulo the periodic
  values, or exactly when they vanish; `relativeComponentAlexanderGrading_add`,
  `relativeComponentAlexanderGrading_swap` and `relativeComponentAlexanderGrading_nonneg`:
  additivity, antisymmetry and the filtration by each component grading.
* In the namespace `TauCeti.HeegaardRegionSystem`,
  `relativeComponentAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero`: the hat differential
  preserves the multigrading.
* In the namespace `TauCeti.HeegaardRegionSystem`, `periodicAlexanderValues_eq_map` and
  `relativeAlexanderGrading_eq_relativeComponentAlexanderGrading`: the knot grading and its
  periodic values are the one-component case of the multigrading.
* `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues_singleton_eq_bot_iff`: the
  periodic values of a knot vanish exactly when those of its multigrading do.
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
* `TauCeti.HeegaardRegionSystem.isAlexanderFunction_sum_relativeComponentAlexanderGrading`: when
  every basepoint other than the `w`'s is a `z` of exactly one component and the periodic values
  vanish, the total grading `∑_q A_q` relative to a fixed generator is an Alexander function for
  the `w`'s.
* `TauCeti.HeegaardRegionSystem.isAlexanderFunction_relativeAlexanderGrading`: in a doubly
  pointed diagram whose periodic Alexander values vanish, the relative Alexander gradings to a
  generator joined to every generator by a domain form an Alexander function.
* In the namespace `TauCeti.HeegaardRegionSystem.IsAlexanderFunction`, for an Alexander
  function `A`:
  * `le_of_hatCoefficient_withBasepoints_ne_zero` and `eq_of_hatCoefficient_ne_zero`: the hat
    differential of the diagram pointed at the `w`'s does not raise `A`, and that of `H`
    preserves it;
  * `hatCoefficient_withBasepoints_of_le`: the two differentials have the same coefficient from
    `x` to `y` unless `A(y) < A(x)`;
  * `hatDifferential_withBasepoints_mem_supported_setOf_le`: the Alexander filtration of the hat
    complex of the diagram pointed at the `w`'s;
  * `hatDifferential_mem_supported_setOf_eq`: the hat differential of `H` preserves each
    Alexander grading;
  * `hatDifferential_withBasepoints_sub_hatDifferential_mem_supported`: the associated graded
    differential of the Alexander filtration is the hat differential of `H`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §2: doubly pointed diagrams, the
  relative spin^c difference `(n_z(φ) - n_w(φ)) PD[μ]` (Lemma 2.5) and the Alexander filtration.
* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), §2,
  for multipointed diagrams, in which the Alexander grading is computed from all the `z`
  basepoints.
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

end PeriodicValues

section PeriodicAlexanderValues

variable (H) in
/-- The values of `n_z - n_w` on the domains whose boundary is a combination of whole curves,
that is, on the domains from any generator to itself; a subgroup of `ℤ`. It is the image of the
periodic values of the Alexander multigrading of the single component with basepoints `w` and `z`.
The relative Alexander grading is well defined modulo this subgroup
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeAlexanderGrading_eq`). -/
def periodicAlexanderValues (w z : Basepoint) : AddSubgroup ℤ :=
  (H.periodicComponentAlexanderValues (fun _ : Unit => {w}) (fun _ => {z})).map
    (Pi.evalAddMonoidHom (fun _ : Unit => ℤ) ())

variable {w z : Basepoint} {x y : H.Generator} {k : ℤ}

/-- The periodic Alexander values are the image, under evaluation at the single component, of the
periodic values of the Alexander multigrading of the component with basepoints `w` and `z`. -/
theorem periodicAlexanderValues_eq_map :
    H.periodicAlexanderValues w z =
      (H.periodicComponentAlexanderValues (fun _ : Unit => {w}) (fun _ => {z})).map
        (Pi.evalAddMonoidHom (fun _ : Unit => ℤ) ()) :=
  (rfl)

/-- The value of a periodic value of the one-component multigrading with basepoints `w` and `z` is
a periodic Alexander value. -/
theorem apply_mem_periodicAlexanderValues {v : Unit → ℤ}
    (hv : v ∈ H.periodicComponentAlexanderValues (fun _ : Unit => {w}) (fun _ => {z})) :
    v () ∈ H.periodicAlexanderValues w z :=
  AddSubgroup.mem_map_of_mem (Pi.evalAddMonoidHom (fun _ : Unit => ℤ) ()) hv

/-- An integer lies in `periodicAlexanderValues w z` when it is `n_z(E) - n_w(E)` for a domain
`E` whose `α`- and `β`-parts are cycles. -/
@[simp]
theorem mem_periodicAlexanderValues_iff :
    k ∈ H.periodicAlexanderValues w z ↔ ∃ E : Region → ℤ,
      H.alphaArcBoundary (H.alphaBoundary E) = 0 ∧ H.betaArcBoundary (H.betaBoundary E) = 0 ∧
        E (H.basepoint z) - E (H.basepoint w) = k := by
  simp [periodicAlexanderValues, and_assoc]

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

/-- For a single component with the basepoints `w` and `z`, the periodic values of the Alexander
multigrading vanish exactly when the periodic Alexander values of the knot do. -/
theorem periodicComponentAlexanderValues_singleton_eq_bot_iff (w z : Basepoint) :
    H.periodicComponentAlexanderValues (fun _ : Unit => {w}) (fun _ => {z}) = ⊥ ↔
      H.periodicAlexanderValues w z = ⊥ :=
  (AddSubgroup.map_eq_bot_iff_of_injective _ fun _ _ h => funext fun () => h).symm

/-- The periodic Alexander values vanish exactly when every domain whose boundary is a
combination of whole curves has the same multiplicity at `w` and at `z`. -/
theorem periodicAlexanderValues_eq_bot_iff :
    H.periodicAlexanderValues w z = ⊥ ↔ ∀ E : Region → ℤ,
      H.alphaArcBoundary (H.alphaBoundary E) = 0 → H.betaArcBoundary (H.betaBoundary E) = 0 →
        E (H.basepoint z) = E (H.basepoint w) := by
  rw [← periodicComponentAlexanderValues_singleton_eq_bot_iff,
    periodicComponentAlexanderValues_eq_bot_iff]
  simp [funext_iff, sub_eq_zero]

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

end RelativeGrading

section RelativeAlexanderGrading

variable (H) in
/-- The relative Alexander grading `A(x, y) = n_z(D) - n_w(D)` of two generators of a diagram
with basepoints `w` and `z`, for a chosen domain `D` from `x` to `y`, or `0` when no domain joins
them. By definition it is the relative Alexander multigrading of the single component with
basepoints `w` and `z`. Its class modulo `periodicAlexanderValues w z` does not depend on the
choice of `D` (`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeAlexanderGrading_eq`),
and when that subgroup vanishes neither does the value itself
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeAlexanderGrading_eq`). -/
noncomputable def relativeAlexanderGrading (w z : Basepoint) (x y : H.Generator) : ℤ :=
  H.relativeComponentAlexanderGrading (fun _ : Unit => {w}) (fun _ => {z}) x y ()

variable {w z : Basepoint} {x y v : H.Generator} {D D' E : Region → ℤ}

/-- The relative Alexander grading is the value of the relative Alexander multigrading of the
single component with basepoints `w` and `z`. -/
theorem relativeAlexanderGrading_eq_relativeComponentAlexanderGrading :
    H.relativeAlexanderGrading w z x y =
      H.relativeComponentAlexanderGrading (fun _ : Unit => {w}) (fun _ => {z}) x y () :=
  (rfl)

/-- When no domain joins `x` to `y`, the relative Alexander grading is `0`. -/
theorem relativeAlexanderGrading_of_forall_not_isDomainBetween
    (h : ∀ D, ¬H.IsDomainBetween x y D) : H.relativeAlexanderGrading w z x y = 0 :=
  congrFun (relativeComponentAlexanderGrading_of_forall_not_isDomainBetween h) ()

/-- The values `n_z(D) - n_w(D)` of two domains `D`, `D'` from `x` to `y` differ by a periodic
Alexander value: `D - D'` is a domain from `x` to itself. -/
theorem IsDomainBetween.sub_sub_sub_mem_periodicAlexanderValues (hD : H.IsDomainBetween x y D)
    (hD' : H.IsDomainBetween x y D') :
    D (H.basepoint z) - D (H.basepoint w) - (D' (H.basepoint z) - D' (H.basepoint w)) ∈
      H.periodicAlexanderValues w z := by
  simpa only [Pi.sub_apply, componentAlexanderMultiplicity_apply, Finset.sum_singleton] using
    apply_mem_periodicAlexanderValues (hD.sub_mem_periodicComponentAlexanderValues hD')

/-- Modulo the periodic Alexander values, the relative Alexander grading is `n_z(D) - n_w(D)` for
every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.coe_relativeAlexanderGrading_eq (hD : H.IsDomainBetween x y D) :
    (H.relativeAlexanderGrading w z x y : ℤ ⧸ H.periodicAlexanderValues w z) =
      ((D (H.basepoint z) - D (H.basepoint w) : ℤ) : ℤ ⧸ H.periodicAlexanderValues w z) := by
  rw [QuotientAddGroup.eq_iff_sub_mem,
    relativeAlexanderGrading_eq_relativeComponentAlexanderGrading]
  simpa only [Pi.sub_apply, componentAlexanderMultiplicity_apply, Finset.sum_singleton] using
    apply_mem_periodicAlexanderValues
      (QuotientAddGroup.eq_iff_sub_mem.mp hD.coe_relativeComponentAlexanderGrading_eq)

/-- When the periodic Alexander values vanish, the relative Alexander grading is
`n_z(D) - n_w(D)` for every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.relativeAlexanderGrading_eq (hA : H.periodicAlexanderValues w z = ⊥)
    (hD : H.IsDomainBetween x y D) :
    H.relativeAlexanderGrading w z x y = D (H.basepoint z) - D (H.basepoint w) := by
  simpa only [relativeAlexanderGrading_eq_relativeComponentAlexanderGrading,
    componentAlexanderMultiplicity_apply, Finset.sum_singleton] using
    congrFun (hD.relativeComponentAlexanderGrading_eq
      ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA)) ()

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
    H.relativeAlexanderGrading w z x x = 0 :=
  congrFun (relativeComponentAlexanderGrading_self
    ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA)) ()

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
      H.relativeAlexanderGrading w z x v :=
  congrFun (hD.relativeComponentAlexanderGrading_add
    ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA) hE) ()

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
    H.relativeAlexanderGrading w z y x = -H.relativeAlexanderGrading w z x y :=
  congrFun (hD.relativeComponentAlexanderGrading_swap
    ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA)) ()

/-- **The Alexander filtration.** A nonnegative domain from `x` to `y` with multiplicity zero at
`w` has `A(x, y) = n_z(D) ≥ 0`. So the hat differential of the singly pointed diagram
`(Σ, α, β, w)`, whose disks have nonnegative domains avoiding `w`, does not raise the Alexander
grading. -/
theorem IsDomainBetween.relativeAlexanderGrading_nonneg (hA : H.periodicAlexanderValues w z = ⊥)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hw : D (H.basepoint w) = 0) :
    0 ≤ H.relativeAlexanderGrading w z x y :=
  hD.relativeComponentAlexanderGrading_nonneg
    ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA) hD0
    (by simpa using hw)

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- A domain counted by the hat differential has multiplicity zero at both `w` and `z`, so it
joins generators of the same Alexander grading, when the periodic Alexander values vanish. -/
theorem relativeAlexanderGrading_eq_zero_of_mem_hatDomains
    (hA : H.periodicAlexanderValues w z = ⊥) (hD : D ∈ H.hatDomains χ x y) :
    H.relativeAlexanderGrading w z x y = 0 :=
  congrFun (relativeComponentAlexanderGrading_eq_zero_of_mem_hatDomains
    ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA) hD) ()

/-- **The hat differential preserves the Alexander grading.** When the periodic Alexander values
vanish, a nonzero coefficient of the hat differential of a diagram with basepoints `w` and `z`
joins generators of the same Alexander grading. Here the hat differential is the count of
domains avoiding the basepoints of `TauCeti.LowDimTopology.Heegaard.HatDifferential`. Only when
the incidence data are realized by a genuine nice doubly pointed diagram of a knot whose regions
have Euler characteristics `χ` is this count the hat knot Floer differential; that realization is
not formalized here. -/
theorem relativeAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero
    (hA : H.periodicAlexanderValues w z = ⊥) (h : H.hatCoefficient χ x y ≠ 0) :
    H.relativeAlexanderGrading w z x y = 0 :=
  congrFun (relativeComponentAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero
    ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA) h) ()

end RelativeAlexanderGrading

section AlexanderFiltration

/-! ### The Alexander filtration of the hat complex

Here `H` carries all the basepoints of a knot or link diagram, the `w`'s and the `z`'s, and
`ι : W → Basepoint` picks out the `w`'s. The diagram `H.withBasepoints (H.basepoint ∘ ι)` keeps
only the `w`'s; its hat differential counts the domains with `n_w = 0`. An Alexander function
`A` on the generators (`TauCeti.HeegaardRegionSystem.IsAlexanderFunction`) satisfies
`A(x) - A(y) = ∑_b n_b(D)` for every domain `D` from `x` to `y` avoiding the `w`'s, the sum
running over all basepoints, so that it is the total multiplicity of `D` at the `z`'s. For a
doubly pointed diagram this is `A(x) - A(y) = n_z(D) - n_w(D)` on such domains, and for a grid
diagram, with the `O`-markings as `w`'s and the `X`-markings as `z`'s, it is
`A(x) - A(y) = n_X(D) - n_O(D)` on them. -/

variable {W : Type*} {ι : W → Basepoint} {A : H.Generator → ℤ} {χ : Region → ℤ}
  {x y : H.Generator} {D : Region → ℤ}

variable (H) in
/-- `A` is an Alexander function for the basepoints picked out by `ι`, the `w`'s: every domain
`D` from `x` to `y` avoiding the `w`'s has `A(x) - A(y) = ∑_b n_b(D)`, its total multiplicity at
the other basepoints, the `z`'s. -/
def IsAlexanderFunction [Fintype Basepoint] (ι : W → Basepoint) (A : H.Generator → ℤ) : Prop :=
  ∀ x y D, H.IsDomainBetween x y D → (∀ i, D (H.basepoint (ι i)) = 0) →
    A x - A y = ∑ b, D (H.basepoint b)

/-- Unfold the definition of an Alexander function. -/
theorem isAlexanderFunction_iff [Fintype Basepoint] :
    H.IsAlexanderFunction ι A ↔ ∀ x y D, H.IsDomainBetween x y D →
      (∀ i, D (H.basepoint (ι i)) = 0) → A x - A y = ∑ b, D (H.basepoint b) :=
  Iff.rfl

/-- With every basepoint picked out, an Alexander function is a function constant along the
domains avoiding all the basepoints. -/
theorem isAlexanderFunction_id_iff [Fintype Basepoint] :
    H.IsAlexanderFunction id A ↔
      ∀ x y D, H.IsDomainBetween x y D → (∀ b, D (H.basepoint b) = 0) → A x = A y := by
  refine forall₃_congr fun x y D => imp_congr_right fun _ => imp_congr_right fun hz => ?_
  simp only [id_eq] at hz
  simp only [hz, Finset.sum_const_zero, sub_eq_zero]

/-- **The total Alexander grading.** Let `ι` pick out the `w`'s, and suppose that every `w` of a
component is one of them and every other basepoint is a `z` of exactly one component. When the
periodic values vanish, the sum `∑_q A_q(x, x₀)` of the component gradings relative to a generator
`x₀` joined to every generator by a domain is an Alexander function for the `w`'s: a domain `D`
from `x` to `y` avoiding the `w`'s changes it by its total multiplicity at the `z`'s. -/
theorem isAlexanderFunction_sum_relativeComponentAlexanderGrading [Fintype Basepoint] [Fintype K]
    {ws zs : K → Finset Basepoint} (hws : ∀ q, ∀ b ∈ ws q, b ∈ Set.range ι)
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

/-- In a diagram whose basepoints are `w` and `z`, with vanishing periodic Alexander values, the
Alexander gradings `A(x) = A(x, x₀)` relative to a generator `x₀` joined to every generator by a
domain form an Alexander function for `w`: `A(x) - A(y) = n_w(D) + n_z(D)` for every domain `D`
from `x` to `y` avoiding `w`. -/
theorem isAlexanderFunction_relativeAlexanderGrading [Fintype Basepoint] {w z : Basepoint}
    (hB : ∀ b, b = w ∨ b = z) (hA : H.periodicAlexanderValues w z = ⊥) {x₀ : H.Generator}
    (hx₀ : ∀ x, ∃ E, H.IsDomainBetween x x₀ E) :
    H.IsAlexanderFunction (fun _ : Unit => w) (H.relativeAlexanderGrading w z · x₀) := by
  simpa [relativeAlexanderGrading_eq_relativeComponentAlexanderGrading] using
    isAlexanderFunction_sum_relativeComponentAlexanderGrading (ι := fun _ : Unit => w)
      (ws := fun _ : Unit => {w}) (zs := fun _ => {z}) (by simp)
      (fun b hb => ⟨(), by simpa using (hB b).resolve_left (by simpa using hb), fun _ _ => rfl⟩)
      ((periodicComponentAlexanderValues_singleton_eq_bot_iff w z).mpr hA) hx₀

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

namespace IsAlexanderFunction

variable [Fintype Basepoint]

/-- A domain counted by the hat differential of the diagram pointed at the `w`'s lowers the
Alexander grading by its total multiplicity at the `z`'s, which is nonnegative. -/
theorem le_of_mem_hatDomains_withBasepoints (hA : H.IsAlexanderFunction ι A)
    (hD : D ∈ (H.withBasepoints (H.basepoint ∘ ι)).hatDomains χ x y) : A y ≤ A x := by
  obtain ⟨hD, hw, hD0, -⟩ := mem_hatDomains_iff.mp hD
  have h := hA x y D ((isDomainBetween_withBasepoints _).mp hD) hw
  have h0 : 0 ≤ ∑ b, D (H.basepoint b) := Finset.sum_nonneg fun b _ => hD0 (H.basepoint b)
  omega

/-- **The hat differential of the diagram pointed at the `w`'s is filtered by the Alexander
grading**: a nonzero coefficient from `x` to `y` forces `A(y) ≤ A(x)`. -/
theorem le_of_hatCoefficient_withBasepoints_ne_zero (hA : H.IsAlexanderFunction ι A)
    (h : (H.withBasepoints (H.basepoint ∘ ι)).hatCoefficient χ x y ≠ 0) : A y ≤ A x :=
  have ⟨_, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero h
  hA.le_of_mem_hatDomains_withBasepoints hD

/-- A domain counted by the hat differential of `H` avoids every basepoint, so it joins
generators of the same Alexander grading. -/
theorem eq_of_mem_hatDomains (hA : H.IsAlexanderFunction ι A) (hD : D ∈ H.hatDomains χ x y) :
    A x = A y := by
  obtain ⟨hD, hz, -⟩ := mem_hatDomains_iff.mp hD
  have h := hA x y D hD fun _ => hz _
  simp only [hz, Finset.sum_const_zero] at h
  omega

/-- **The hat differential of `H` preserves the Alexander grading**: a nonzero coefficient from
`x` to `y` forces `A(x) = A(y)`. -/
theorem eq_of_hatCoefficient_ne_zero (hA : H.IsAlexanderFunction ι A)
    (h : H.hatCoefficient χ x y ≠ 0) : A x = A y :=
  have ⟨_, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero h
  hA.eq_of_mem_hatDomains hD

/-- Between generators of the same Alexander grading, the domains counted by the hat differential
of the diagram pointed at the `w`'s are those counted by the hat differential of `H`: a
nonnegative domain with total multiplicity zero at the `z`'s vanishes at each of them. -/
theorem hatDomains_withBasepoints_of_eq (hA : H.IsAlexanderFunction ι A) (hxy : A x = A y) :
    (H.withBasepoints (H.basepoint ∘ ι)).hatDomains χ x y = H.hatDomains χ x y := by
  refine Set.Subset.antisymm (fun D hD => ?_) (hatDomains_subset_hatDomains_withBasepoints ι χ x y)
  obtain ⟨hD, hw, hD0, hμ⟩ := mem_hatDomains_iff.mp hD
  rw [isDomainBetween_withBasepoints] at hD
  rw [maslovIndex_withBasepoints] at hμ
  have h := hA x y D hD hw
  rw [hxy, sub_self, eq_comm,
    Finset.sum_eq_zero_iff_of_nonneg fun b _ => hD0 (H.basepoint b)] at h
  exact mem_hatDomains_iff.mpr ⟨hD, fun b => h b (Finset.mem_univ b), hD0, hμ⟩

/-- Unless the Alexander grading drops from `x` to `y`, the hat differential of the diagram
pointed at the `w`'s has the same coefficient from `x` to `y` as that of `H`. -/
theorem hatCoefficient_withBasepoints_of_le (hA : H.IsAlexanderFunction ι A) (hxy : A x ≤ A y) :
    (H.withBasepoints (H.basepoint ∘ ι)).hatCoefficient χ x y = H.hatCoefficient χ x y := by
  rcases hxy.lt_or_eq with hxy | hxy
  · rw [hatCoefficient_eq_zero_of_hatDomains_eq_empty
        (Set.eq_empty_of_forall_notMem fun _ hD =>
          hxy.not_ge (hA.le_of_mem_hatDomains_withBasepoints hD)),
      hatCoefficient_eq_zero_of_hatDomains_eq_empty
        (Set.eq_empty_of_forall_notMem fun _ hD => hxy.ne (hA.eq_of_mem_hatDomains hD))]
  · rw [hatCoefficient_def, hatCoefficient_def, hA.hatDomains_withBasepoints_of_eq hxy]

/-- **The Alexander filtration.** The hat differential of the diagram pointed at the `w`'s maps
the chains supported in Alexander gradings at most `k` to chains supported there. -/
theorem hatDifferential_withBasepoints_mem_supported_setOf_le (hA : H.IsAlexanderFunction ι A)
    {k : ℤ} {c : H.Generator →₀ ZMod 2}
    (hc : c ∈ Finsupp.supported (ZMod 2) (ZMod 2) {x | A x ≤ k}) :
    (H.withBasepoints (H.basepoint ∘ ι)).hatDifferential χ c ∈
      Finsupp.supported (ZMod 2) (ZMod 2) {x | A x ≤ k} :=
  hatDifferential_mem_supported
    (fun _ hx _ h => (hA.le_of_hatCoefficient_withBasepoints_ne_zero h).trans hx) hc

/-- The hat differential of `H` maps the chains supported in Alexander grading `k` to chains
supported there. -/
theorem hatDifferential_mem_supported_setOf_eq (hA : H.IsAlexanderFunction ι A) {k : ℤ}
    {c : H.Generator →₀ ZMod 2} (hc : c ∈ Finsupp.supported (ZMod 2) (ZMod 2) {x | A x = k}) :
    H.hatDifferential χ c ∈ Finsupp.supported (ZMod 2) (ZMod 2) {x | A x = k} :=
  hatDifferential_mem_supported (fun _ hx _ h => (hA.eq_of_hatCoefficient_ne_zero h).symm.trans hx)
    hc

/-- **The associated graded of the Alexander filtration.** On a chain `c` supported in Alexander
gradings at most `k`, the hat differentials of the diagram pointed at the `w`'s and of `H` agree
up to chains supported in Alexander gradings below `k`. So the map induced on the quotient of the
`k`-th filtration level by the `(k - 1)`-st is the hat differential of `H`, which keeps the domains
with `n_z = 0` and discards those that lower the Alexander grading. -/
theorem hatDifferential_withBasepoints_sub_hatDifferential_mem_supported
    (hA : H.IsAlexanderFunction ι A) {k : ℤ} {c : H.Generator →₀ ZMod 2}
    (hc : c ∈ Finsupp.supported (ZMod 2) (ZMod 2) {x | A x ≤ k}) :
    (H.withBasepoints (H.basepoint ∘ ι)).hatDifferential χ c - H.hatDifferential χ c ∈
      Finsupp.supported (ZMod 2) (ZMod 2) {x | A x < k} := by
  rw [Finsupp.mem_supported']
  intro y hy
  rw [Set.mem_ofPred_eq, not_lt] at hy
  rw [Finsupp.sub_apply, hatDifferential_apply, hatDifferential_apply, sub_eq_zero]
  refine Finsupp.sum_congr fun x hx => ?_
  have hxk : A x ≤ k := (Finsupp.mem_supported _ _).mp hc hx
  rw [hA.hatCoefficient_withBasepoints_of_le (hxk.trans hy)]

end IsAlexanderFunction

end AlexanderFiltration

end HeegaardRegionSystem

end TauCeti
