/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.LowDimTopology.Heegaard.ConnectedSum.Basic
public import TauCeti.LowDimTopology.Heegaard.Nice
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Ring.Regular
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.Homology.SquareZero.Quotient
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MonoidAlgebra.Exactness

/-!
# The twisted hat complex of a connected sum with `S¹ × S²`

The connected sum `Y # (S¹ × S²)` has the Heegaard diagram
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphere r₀`, obtained from a pointed diagram of `Y` by
drawing a small `α`-circle and a small `β`-circle in a region `R₀`, meeting in two points `p` and
`q`, and joining the lens between them to `R₀` by a tube. Its generators are the pairs `(x, p)`
and `(x, q)` of a generator `x` of the original diagram and a new point, and its new regions are
the two bigons `B₁` and `B₂` from `p` to `q`. This file computes the twisted hat complex of the
connected sum, with coefficients in the group ring of its periodic domains, from that of the
original diagram.

The periodic domains of the connected sum are those of the original diagram together with the
multiples of the sphere class `B₁ - B₂`: a periodic domain `P` of the connected sum corresponds to
its restriction `Q` to the old regions and the integer `P(B₁) - P(R₀)`, and conversely `(Q, a)`
goes to the extension of `Q` with multiplicities `Q(R₀) + a` on `B₁` and `Q(R₀) - a` on `B₂`
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSpherePeriodicDomainsEquiv`). So the group ring of
the periodic domains of the connected sum is the group ring `R` of those of the original diagram
with a Laurent variable `t = t^{B₁ - B₂}` adjoined, and `R` maps into it by extending periodic
domains (`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRingHom`).

Reference domains `D_x` for the original diagram give reference domains for the connected sum
(`TauCeti.HeegaardRegionSystem.ReferenceDomains.sumCircleTimesSphere`): the reference generator
of `(x, k)` is `(x₀, p)` for the reference generator `x₀` of `x`, with reference domain `D_x`
extended by `D_x(R₀)` on `B₁` and by `D_x(R₀) + k` on `B₂`. The label of a domain of the
connected sum is then the label of its restriction to the old regions, extended over the bigons
(`TauCeti.HeegaardRegionSystem.ReferenceDomains.label_sumCircleTimesSphere`).

With these choices, when `R₀` contains a basepoint, the twisted hat coefficients of the connected
sum are:

* from `(x, k)` to `(y, k)`, the twisted coefficient of the original diagram from `x` to `y`,
  mapped into the larger group ring
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_self`): the counted
  domains are those of the original diagram, extended by zero on the bigons;
* from `(x, q)` to `(y, p)`, zero
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_one_zero`);
* from `(x, p)` to `(x, q)`, in a weakly admissible nice diagram, `1 + t`
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_zero_one_self`):
  the counted domains are the two bigons, with labels `B₁ - B₂` and `0`;
* from `(x, p)` to `(y, q)` with `x ≠ y`, in a nice diagram, zero
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_zero_one_of_ne`).

In general the domains counted from `(x, p)` to `(y, q)` are the pairs of a nonnegative domain of
Maslov index zero from `x` to `y` avoiding the basepoints and one of the two bigons
(`TauCeti.HeegaardRegionSystem.hatDomains_sumCircleTimesSphere_zero_one`); in a weakly
admissible nice diagram the only such domain is the zero domain from `x` to itself
(`TauCeti.HeegaardRegionSystem.IsNice.eq_zero_of_maslovIndex_nonpos`).

Hence the twisted hat differential of the connected sum is `∂ ⊗ 1 + 1 ⊗ κ`, where `∂` is the
twisted hat differential of the original diagram with its coefficients extended to the larger
group ring, and `κ` is the Koszul differential `p ↦ (1 + t) q`, `q ↦ 0`, of the new factor
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_sumCircleTimesSphere_single`). Under the
augmentation `t ↦ 1` the coefficient `1 + t` becomes `0`, so `κ` vanishes. For weakly admissible
nice diagrams this recovers the untwisted statement
`TauCeti.HeegaardRegionSystem.hatDifferential_sumCircleTimesSphere_comp_addBasepointChainEquiv`,
which itself holds without these hypotheses.
**Homology.** The Koszul factor does not change the twisted homology. The ring map
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedRetraction` `ε`, induced by
`(Q, a) ↦ Q`, sets `t` to `1` and is a left inverse of the map of group rings, and its kernel is
generated by `1 + t` (`TauCeti.HeegaardRegionSystem.ker_sumCircleTimesSphereTwistedRetraction`).
The twisted complex of the connected sum is the mapping cone of multiplication by `1 + t` on the
extended twisted complex of the original diagram. Since `1 + t` is a nonzerodivisor, the cone
computes the homology of the quotient by `1 + t`, which `ε` identifies with the original complex
(`LinearMap.bijective_homologyMap_comp_snd`). Concretely, when the twisted hat differential of the
original diagram squares to zero, so does that of the connected sum
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero`), and
the projection `c ↦ (y ↦ ε (c (y, q)))`
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedProjection`) is a chain map inducing a
bijection on twisted homology
(`TauCeti.HeegaardRegionSystem.homologyMap_sumCircleTimesSphereTwistedProjection_bijective`). So
the twisted homology of the connected sum is that of the original diagram, with the larger group
ring acting through `ε` (`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedHomologyEquiv`,
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedHomologyEquiv_smul`); in particular `1 + t`
annihilates it. The vanishing of the square of the original twisted differential is a hypothesis,
as it is not proved for the incidence data in general. The augmentation of the whole group ring is
not flat, so homology does not commute with it: this comparison is not a statement about the
untwisted hat homology.

On a geometric diagram the periodic domains of the connected sum are the second homology of
`Y # (S¹ × S²)` and the counted domains are the holomorphic disks; neither identification is
formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRingHom`: the map of group rings induced by
  `TauCeti.HeegaardRegionSystem.sumCircleTimesSpherePeriodicDomainsEquiv`.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.sumCircleTimesSphere`: the reference domains of
  the connected sum induced by reference domains of the original diagram.
* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedRetraction`: the ring map setting `t`
  to `1`.
* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedProjection`: the chain map
  `c ↦ (y ↦ ε (c (y, q)))` from the twisted complex of the connected sum to that of the original
  diagram.
* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedHomologyEquiv`: the induced
  identification of twisted homologies.

## Main results

* `TauCeti.HeegaardRegionSystem.ReferenceDomains.label_sumCircleTimesSphere`: the labels of
  domains of the connected sum.
* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_self`,
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_zero_one_self`,
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_zero_one_of_ne` and
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_one_zero`: the twisted
  hat coefficients of the connected sum.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_sumCircleTimesSphere_single`: its twisted
  hat differential is the twisted hat differential of the original diagram tensored with the
  Koszul complex of `1 + t`.
* `TauCeti.HeegaardRegionSystem.ker_sumCircleTimesSphereTwistedRetraction`: the kernel of `ε` is
  generated by `1 + t`.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero`: the
  twisted differential of the connected sum squares to zero if that of the original diagram does.
* `TauCeti.HeegaardRegionSystem.homologyMap_sumCircleTimesSphereTwistedProjection_bijective`: the
  projection induces a bijection on twisted homology.
* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedHomologyEquiv_smul` and
  `TauCeti.HeegaardRegionSystem.sumCircleTimesSphere_one_add_single_smul_eq_zero`: the coefficients
  act on the twisted homology of the connected sum through `ε`, so `1 + t` acts by zero.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §8 (Floer homology with twisted
  coefficients, and the twisted Floer homology of `S¹ × S²`).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830),
  §10 (twisted coefficients for nice diagrams with several basepoints, and the auxiliary connected
  sums with `S¹ × S²`).
-/

public section

open Function MonoidAlgebra

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

section PeriodicDomain

variable (r₀ : Region)

/-- The map from the group ring of the periodic domains of the original diagram to the group ring
of the periodic domains of the connected sum with `S¹ × S²` in `r₀`, sending `t^Q` to `t^{Q'}` for
the extension `Q'` of `Q` with multiplicity `Q(r₀)` on both bigons. -/
noncomputable def sumCircleTimesSphereRingHom :
    MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) →+*
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains) :=
  mapDomainRingHom (ZMod 2) (AddMonoidHom.toMultiplicative
    ((H.sumCircleTimesSpherePeriodicDomainsEquiv r₀).toAddMonoidHom.comp
      (AddMonoidHom.inl _ _)))

/-- The map of group rings sends the monomial `t^Q` to the monomial of the extension of `Q`. -/
@[simp]
theorem sumCircleTimesSphereRingHom_single (Q : H.periodicDomains) (a : ZMod 2) :
    H.sumCircleTimesSphereRingHom r₀ (single (Multiplicative.ofAdd Q) a) =
      single (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (Q, 0))) a := by
  simp [sumCircleTimesSphereRingHom]

end PeriodicDomain

section ReferenceDomains

variable {H}

/-- The reference domains of the connected sum with `S¹ × S²` in a region `r₀` induced by
reference domains `D_x` of the original diagram: the reference generator of `(x, k)` is `(x₀, p)`
for the reference generator `x₀` of `x`, and its reference domain is `D_x` extended by `D_x(r₀)`
on the bigon `B₁` and by `D_x(r₀) + k` on the bigon `B₂`. -/
noncomputable def ReferenceDomains.sumCircleTimesSphere (r : H.ReferenceDomains) (r₀ : Region) :
    (H.sumCircleTimesSphere r₀).ReferenceDomains where
  base g := H.addBasepointGenerator r₀ (r.base ((H.addBasepointGeneratorEquiv r₀).symm g).1) 0
  domain g := Sum.elim (r.domain ((H.addBasepointGeneratorEquiv r₀).symm g).1)
    ![r.domain ((H.addBasepointGeneratorEquiv r₀).symm g).1 r₀,
      r.domain ((H.addBasepointGeneratorEquiv r₀).symm g).1 r₀ +
        (((H.addBasepointGeneratorEquiv r₀).symm g).2 : ℤ)]
  isDomainBetween_domain g := by
    obtain ⟨⟨x, i⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
    simp only [addBasepointGeneratorEquiv_apply, addBasepointGeneratorEquiv_symm_apply]
    rw [isDomainBetween_sumCircleTimesSphere_iff]
    refine ⟨r.isDomainBetween_domain x, ?_⟩
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Nat.cast_zero, sub_zero]
    ring
  domain_basepoint g z := by
    simpa using r.domain_basepoint _ z
  base_eq_base {g h D} hD hz := by
    obtain ⟨⟨x, i⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
    obtain ⟨⟨y, j⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective h
    simp only [addBasepointGeneratorEquiv_apply, addBasepointGeneratorEquiv_symm_apply] at hD ⊢
    rw [isDomainBetween_sumCircleTimesSphere_iff] at hD
    rw [r.base_eq_base hD.1 fun z => hz z]

variable (r : H.ReferenceDomains) (r₀ : Region)

/-- The reference generator of `(x, k)` is `(x₀, p)` for the reference generator `x₀` of `x`. -/
@[simp]
theorem ReferenceDomains.sumCircleTimesSphere_base (x : H.Generator) (k : Fin 2) :
    (r.sumCircleTimesSphere r₀).base (H.addBasepointGenerator r₀ x k) =
      H.addBasepointGenerator r₀ (r.base x) 0 := by
  simp [sumCircleTimesSphere]

/-- The reference domain of `(x, k)` is the reference domain `D_x` of `x`, extended by `D_x(r₀)`
on `B₁` and by `D_x(r₀) + k` on `B₂`. -/
@[simp]
theorem ReferenceDomains.sumCircleTimesSphere_domain (x : H.Generator) (k : Fin 2) :
    (r.sumCircleTimesSphere r₀).domain (H.addBasepointGenerator r₀ x k) =
      Sum.elim (r.domain x) ![r.domain x r₀, r.domain x r₀ + k] := by
  simp [sumCircleTimesSphere]

/-- **Labels in the connected sum.** The label of a domain `D` of the connected sum from `(x, i)`
to `(y, j)` is the label `L` of its restriction to the old regions, extended by
`L(r₀) + D(B₁) - D(r₀)` on `B₁` and by `L(r₀) + D(B₂) - D(r₀) + i - j` on `B₂`. -/
theorem ReferenceDomains.label_sumCircleTimesSphere (x y : H.Generator) (i j : Fin 2)
    (D : Region ⊕ Fin 2 → ℤ) :
    (r.sumCircleTimesSphere r₀).label (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) D =
      Sum.elim (r.label x y (D ∘ Sum.inl))
        ![r.label x y (D ∘ Sum.inl) r₀ + D (Sum.inr 0) - D (Sum.inl r₀),
          r.label x y (D ∘ Sum.inl) r₀ + D (Sum.inr 1) - D (Sum.inl r₀) + i - j] := by
  ext (s | k)
  · simp [label_def]
  · fin_cases k
    · simp [label_def]
      ring
    · simp [label_def]
      ring

end ReferenceDomains

section Coefficient

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {r₀ : Region} {χ : Region → ℤ}
  (r : H.ReferenceDomains)

/-- **Twisted coefficients between generators with the same new point.** For the reference domains
induced by `r`, the twisted coefficient of the connected sum with `S¹ × S²` in a region containing
a basepoint, from `(x, k)` to `(y, k)`, is the twisted coefficient of the original diagram from
`x` to `y`, mapped into the group ring of the periodic domains of the connected sum. -/
theorem twistedHatCoefficient_sumCircleTimesSphere_self (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) (i : Fin 2) :
    (H.sumCircleTimesSphere r₀).twistedHatCoefficient (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y i) =
      H.sumCircleTimesSphereRingHom r₀ (H.twistedHatCoefficient r χ x y) := by
  have hinj : Injective fun E : Region → ℤ => (Sum.elim E 0 : Region ⊕ Fin 2 → ℤ) :=
    fun D E h => funext fun s => congrFun h (Sum.inl s)
  have hS := H.hatDomains_sumCircleTimesSphere_self (χ := χ) r₀ hr₀ x y i
  rcases (H.hatDomains χ x y).finite_or_infinite with hfin | hinf
  · have := hfin.to_subtype
    -- Extending by zero identifies the counted domains, and the labels correspond.
    let e : H.hatDomains χ x y ≃ (H.sumCircleTimesSphere r₀).hatDomains
        (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y i) :=
      (Equiv.Set.image _ _ hinj).trans (Set.equivOfEq hS.symm)
    rw [twistedHatCoefficient_def, ← finsum_comp_equiv e, twistedHatCoefficient_def,
      map_finsum _ (Set.toFinite _)]
    refine finsum_congr fun E => ?_
    have hl := r.label_sumCircleTimesSphere r₀ x y i i (Sum.elim (E : Region → ℤ) 0)
    rw [sumCircleTimesSphereRingHom_single]
    congr 2
    refine Subtype.ext ?_
    simp only [e, Equiv.trans_apply, Equiv.Set.image_apply, Set.equivOfEq_apply]
    rw [hl]
    -- A counted domain vanishes on `r₀`, which contains a basepoint.
    obtain ⟨z₀, rfl⟩ := hr₀
    have hz := (mem_hatDomains_iff.mp E.property).2.1 z₀
    ext (s | k)
    · simp
    · fin_cases k <;> simp [hz]
  · rw [twistedHatCoefficient_of_infinite hinf, map_zero, twistedHatCoefficient_of_infinite]
    rw [hS]
    exact hinf.image hinj.injOn

variable {H} in
/-- In a weakly admissible nice diagram the only nonnegative domain of Maslov index zero from a
generator to itself avoiding the basepoints is the zero domain. -/
private theorem setOf_maslovIndex_eq_zero_self (hN : H.IsNice χ) (hW : H.WeaklyAdmissible)
    (x : H.Generator) :
    {E | H.IsDomainBetween x x E ∧ (∀ z, E (H.basepoint z) = 0) ∧ 0 ≤ E ∧
      H.maslovIndex χ x x E = 0} = {0} := by
  ext E
  refine ⟨fun ⟨hD, hz, hD0, hμ⟩ => hN.eq_zero_of_maslovIndex_nonpos hW hD hD0 hz hμ.le, ?_⟩
  rintro rfl
  exact ⟨isDomainBetween_zero x, fun _ => rfl, le_rfl, map_zero _⟩

variable {H} in
/-- In a nice diagram there is no nonnegative domain of Maslov index zero between distinct
generators avoiding the basepoints. -/
private theorem setOf_maslovIndex_eq_zero_of_ne (hN : H.IsNice χ) {x y : H.Generator}
    (hxy : x ≠ y) :
    {E | H.IsDomainBetween x y E ∧ (∀ z, E (H.basepoint z) = 0) ∧ 0 ≤ E ∧
      H.maslovIndex χ x y E = 0} = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hD, hz, hD0, hμ⟩ =>
    hxy (hN.eq_of_maslovIndex_nonpos hD hD0 hz hμ.le)

/-- **The Koszul coefficient `1 + t`.** In a weakly admissible nice diagram, for the reference
domains induced by `r`, the twisted coefficient of the connected sum with `S¹ × S²` in a region
containing a basepoint, from `(x, p)` to `(x, q)`, is `1 + t`, where `t = t^{B₁ - B₂}` is the
monomial of the sphere class: the counted domains are the two bigons `B₁` and `B₂`, whose labels
are `B₁ - B₂` and `0`. -/
theorem twistedHatCoefficient_sumCircleTimesSphere_zero_one_self (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hN : H.IsNice χ)
    (hW : H.WeaklyAdmissible) (x : H.Generator) :
    (H.sumCircleTimesSphere r₀).twistedHatCoefficient (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
        (H.addBasepointGenerator r₀ x 1) =
      1 + single
        (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1 := by
  -- The counted domains are the two bigons.
  let f : Fin 2 → Region ⊕ Fin 2 → ℤ := fun k => Sum.elim 0 (Pi.single k 1)
  have hf : Injective f := fun k m h => by
    simpa [f, Pi.single_apply, eq_comm] using congrFun h (Sum.inr k)
  have hS : Set.range f = (H.sumCircleTimesSphere r₀).hatDomains
      (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
      (H.addBasepointGenerator r₀ x 1) := by
    rw [H.hatDomains_sumCircleTimesSphere_zero_one r₀ hr₀, setOf_maslovIndex_eq_zero_self hN hW,
      Set.singleton_prod, Set.image_image, Set.image_univ]
  let e : Fin 2 ≃ (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
      (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1) :=
    (Equiv.ofInjective f hf).trans (Set.equivOfEq hS)
  have hl (k : Fin 2) := r.label_sumCircleTimesSphere r₀ x x 0 1 (f k)
  rw [twistedHatCoefficient_def, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype,
    Fin.sum_univ_two, add_comm (1 : MonoidAlgebra (ZMod 2) _), one_def, ← ofAdd_zero]
  -- The label of `B₁` is `B₁ - B₂` and the label of `B₂` is `0`.
  congr 1 <;> congr 2 <;> refine Subtype.ext ?_ <;>
    simp only [e, Equiv.trans_apply, Equiv.ofInjective_apply, Set.equivOfEq_apply, hl] <;>
    simp [f, funext_iff, Sum.forall, Fin.forall_fin_two]

/-- In a nice diagram, for the reference domains induced by `r`, the twisted coefficient of the
connected sum with `S¹ × S²` in a region containing a basepoint, from `(x, p)` to `(y, q)` with
`x ≠ y`, vanishes. -/
theorem twistedHatCoefficient_sumCircleTimesSphere_zero_one_of_ne (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hN : H.IsNice χ)
    {x y : H.Generator} (hxy : x ≠ y) :
    (H.sumCircleTimesSphere r₀).twistedHatCoefficient (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
        (H.addBasepointGenerator r₀ y 1) = 0 :=
  twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty <| by
    rw [H.hatDomains_sumCircleTimesSphere_zero_one r₀ hr₀, setOf_maslovIndex_eq_zero_of_ne hN hxy,
      Set.empty_prod, Set.image_empty]

/-- For the reference domains induced by `r`, the twisted coefficient of the connected sum with
`S¹ × S²` in a region containing a basepoint, from `(x, q)` to `(y, p)`, vanishes. -/
theorem twistedHatCoefficient_sumCircleTimesSphere_one_zero (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) :
    (H.sumCircleTimesSphere r₀).twistedHatCoefficient (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x 1)
        (H.addBasepointGenerator r₀ y 0) = 0 :=
  twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty
    (H.hatDomains_sumCircleTimesSphere_one_zero r₀ hr₀ x y)

/-- **The twisted hat differential of a connected sum with `S¹ × S²`.** In a weakly admissible
nice diagram, for the reference domains induced by `r`, the twisted hat differential of the
connected sum with `S¹ × S²` in a region containing a basepoint is `∂ ⊗ 1 + 1 ⊗ κ`: it sends
`a (x, k)` to `a ∂x` placed at the new point `k`, where `∂` is the twisted hat differential of the
original diagram with its coefficients mapped into the larger group ring, plus, for `k = p`, the
Koszul term `(1 + t) a (x, q)`, where `t = t^{B₁ - B₂}` is the monomial of the sphere class. -/
theorem twistedHatDifferential_sumCircleTimesSphere_single (hr₀ : r₀ ∈ Set.range H.basepoint)
    (hN : H.IsNice χ)
    (hW : H.WeaklyAdmissible) (x : H.Generator) (i : Fin 2)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) :
    (H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) (Finsupp.single (H.addBasepointGenerator r₀ x i) a) =
      a • Finsupp.mapDomain (fun y => H.addBasepointGenerator r₀ y i)
          (Finsupp.mapRange (H.sumCircleTimesSphereRingHom r₀) (map_zero _)
            (H.twistedHatDifferential r χ (Finsupp.single x 1))) +
        if i = 0 then
          Finsupp.single (H.addBasepointGenerator r₀ x 1)
            ((1 + single (Multiplicative.ofAdd
              (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1) * a)
        else 0 := by
  have hinj (k : Fin 2) : Injective fun y : H.Generator => H.addBasepointGenerator r₀ y k :=
    fun y z h => (H.addBasepointGenerator_inj r₀).mp h |>.1
  have hout (k m : Fin 2) (hkm : k ≠ m)
      (c : H.Generator →₀ MonoidAlgebra (ZMod 2)
        (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) (y : H.Generator) :
      Finsupp.mapDomain (fun y => H.addBasepointGenerator r₀ y k) c
        (H.addBasepointGenerator r₀ y m) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ fun ⟨z, hz⟩ =>
      hkm ((H.addBasepointGenerator_inj r₀).mp hz).2
  refine Finsupp.ext fun g => ?_
  obtain ⟨⟨y, j⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
  simp only [addBasepointGeneratorEquiv_apply, twistedHatDifferential_single_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · -- From `(x, p)` to `(y, p)`: the coefficient of the original diagram.
    simp [Finsupp.mapDomain_apply_of_injective (hinj 0),
      H.twistedHatCoefficient_sumCircleTimesSphere_self r hr₀]
  · -- From `(x, p)` to `(y, q)`: the Koszul coefficient `1 + t`.
    by_cases hxy : x = y
    · subst hxy
      simp [hout 0 1 (by decide),
        H.twistedHatCoefficient_sumCircleTimesSphere_zero_one_self r hr₀ hN hW, mul_comm]
    · simp [hout 0 1 (by decide),
        H.twistedHatCoefficient_sumCircleTimesSphere_zero_one_of_ne r hr₀ hN hxy, hxy]
  · -- From `(x, q)` to `(y, p)`: nothing.
    simp [hout 1 0 (by decide), H.twistedHatCoefficient_sumCircleTimesSphere_one_zero r hr₀]
  · -- From `(x, q)` to `(y, q)`: the coefficient of the original diagram.
    simp [Finsupp.mapDomain_apply_of_injective (hinj 1),
      H.twistedHatCoefficient_sumCircleTimesSphere_self r hr₀]

end Coefficient

section Retraction

variable (r₀ : Region)

/-- The ring map from the group ring of the periodic domains of the connected sum with `S¹ × S²` in
`r₀` back to that of the original diagram, induced by the projection `(Q, a) ↦ Q` of
`TauCeti.HeegaardRegionSystem.sumCircleTimesSpherePeriodicDomainsEquiv`. It sends the monomial `t`
of the sphere class `B₁ - B₂` to `1`, and it is a left inverse of
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRingHom`. -/
noncomputable def sumCircleTimesSphereTwistedRetraction :
    MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains) →+*
      MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) :=
  mapDomainRingHom (ZMod 2) (AddMonoidHom.toMultiplicative
    ((AddMonoidHom.fst _ _).comp
      (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀).symm.toAddMonoidHom))

/-- The retraction sends the monomial `t^P` to the monomial of the restriction of `P` to the old
regions. -/
@[simp]
theorem sumCircleTimesSphereTwistedRetraction_single
    (P : (H.sumCircleTimesSphere r₀).periodicDomains) (a : ZMod 2) :
    H.sumCircleTimesSphereTwistedRetraction r₀ (single (Multiplicative.ofAdd P) a) =
      single (Multiplicative.ofAdd ((H.sumCircleTimesSpherePeriodicDomainsEquiv r₀).symm P).1)
        a := by
  simp [sumCircleTimesSphereTwistedRetraction]

/-- The retraction is a left inverse of the map of group rings
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRingHom`. -/
@[simp]
theorem sumCircleTimesSphereTwistedRetraction_sumCircleTimesSphereRingHom
    (a : MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    H.sumCircleTimesSphereTwistedRetraction r₀ (H.sumCircleTimesSphereRingHom r₀ a) = a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g c =>
    obtain ⟨Q, rfl⟩ := Multiplicative.ofAdd.surjective g
    simp

/-- The retraction kills the Koszul coefficient `1 + t`: it sends `t` to `1`, and `1 + 1 = 0`. -/
@[simp]
theorem sumCircleTimesSphereTwistedRetraction_one_add_single :
    H.sumCircleTimesSphereTwistedRetraction r₀
      (1 + single (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1) =
        0 := by
  simp [← one_def, ZModModule.add_self]

/-- **The kernel of the retraction is generated by `1 + t`.** Setting `t = 1` identifies the group
ring of the periodic domains of the connected sum with `S¹ × S²`, modulo `1 + t`, with the group
ring of the periodic domains of the original diagram. -/
theorem ker_sumCircleTimesSphereTwistedRetraction :
    RingHom.ker (H.sumCircleTimesSphereTwistedRetraction r₀) =
      Ideal.span {1 + single (Multiplicative.ofAdd
        (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1} := by
  refine le_antisymm ?_ ?_
  · -- The kernel is generated by the differences `t^k - 1` for `k` in the kernel `ℤ (0, 1)` of
    -- `(Q, a) ↦ Q`, and `t^{(0, a)} - 1` lies in the ideal generated by `t - 1 = 1 + t`.
    rw [sumCircleTimesSphereTwistedRetraction, TauCeti.MonoidAlgebra.ker_mapDomainRingHom_eq_span,
      Ideal.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective k
    obtain ⟨⟨Q, m⟩, rfl⟩ := (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀).surjective P
    obtain rfl : Q = 0 := by simpa [AddSubgroup.mem_prod] using hk
    have hmem : Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, m)) ∈
        Subgroup.closure
          {Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))} := by
      rw [Subgroup.mem_closure_singleton]
      exact ⟨m, by rw [← ofAdd_zsmul, ← map_zsmul]; simp⟩
    have h := TauCeti.MonoidAlgebra.single_sub_one_mem_span_of_mem_closure (ZMod 2) hmem
    simpa [ZModModule.sub_eq_add, add_comm] using h
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact H.sumCircleTimesSphereTwistedRetraction_one_add_single r₀

/-- Setting `t = 1` in the coefficients of a chain of the original diagram with coefficients in
the group ring of the periodic domains of the connected sum. -/
private noncomputable def retractCoefficients :
    (H.Generator →₀
        MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) →ₛₗ[
      H.sumCircleTimesSphereTwistedRetraction r₀]
      H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) :=
  Finsupp.mapRange.linearMap (H.sumCircleTimesSphereTwistedRetraction r₀).toSemilinearMap

@[simp]
private theorem retractCoefficients_apply
    (c : H.Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
    (y : H.Generator) :
    H.retractCoefficients r₀ c y = H.sumCircleTimesSphereTwistedRetraction r₀ (c y) := by
  simp [retractCoefficients]

@[simp]
private theorem retractCoefficients_single (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) :
    H.retractCoefficients r₀ (Finsupp.single x a) =
      Finsupp.single x (H.sumCircleTimesSphereTwistedRetraction r₀ a) := by
  simp [retractCoefficients]

private theorem retractCoefficients_surjective : Surjective (H.retractCoefficients r₀) :=
  fun c => ⟨Finsupp.mapRange (H.sumCircleTimesSphereRingHom r₀) (map_zero _) c,
    Finsupp.ext fun y => by simp⟩

/-- The chains whose coefficients vanish at `t = 1` are the multiples of `1 + t`. -/
private theorem exact_lsmul_retractCoefficients :
    Function.Exact (LinearMap.lsmul _ (H.Generator →₀
        MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
      (1 + single (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1)))
        (1 : ZMod 2)))
      (H.retractCoefficients r₀) := by
  intro c
  constructor
  · intro hc
    have h (y : H.Generator) : c y ∈ Ideal.span {1 + single (Multiplicative.ofAdd
        (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) (1 : ZMod 2)} := by
      rw [← ker_sumCircleTimesSphereTwistedRetraction, RingHom.mem_ker]
      simpa using congr($hc y)
    choose v hv using fun y => Ideal.mem_span_singleton'.1 (h y)
    exact ⟨Finsupp.equivFunOnFinite.symm v, Finsupp.ext fun y => by simp [← hv y]; ring⟩
  · rintro ⟨w, rfl⟩
    exact Finsupp.ext fun y => by
      simp only [LinearMap.lsmul_apply, retractCoefficients_apply, Finsupp.smul_apply,
        smul_eq_mul, map_mul, sumCircleTimesSphereTwistedRetraction_one_add_single, zero_mul,
        Finsupp.coe_zero, Pi.zero_apply]

end Retraction

section Homology

variable [Fintype Point] (r₀ : Region)

/-- The chain map from the twisted hat complex of the connected sum with `S¹ × S²` in `r₀` to that
of the original diagram: it keeps the coefficients at the generators `(y, q)` and sets `t` to `1` in
them, `c ↦ (y ↦ ε (c (y, q)))`, where `ε` is
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedRetraction`. It is semilinear along
`ε`. -/
noncomputable def sumCircleTimesSphereTwistedProjection :
    ((H.sumCircleTimesSphere r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) →ₛₗ[
        H.sumCircleTimesSphereTwistedRetraction r₀]
      H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) where
  toFun c := Finsupp.equivFunOnFinite.symm fun y =>
    H.sumCircleTimesSphereTwistedRetraction r₀ (c (H.addBasepointGenerator r₀ y 1))
  map_add' c c' := by ext; simp
  map_smul' a c := by ext; simp

/-- The projection reads the coefficient at `(y, q)` with `t` set to `1`. -/
@[simp]
theorem sumCircleTimesSphereTwistedProjection_apply
    (c : (H.sumCircleTimesSphere r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
    (y : H.Generator) :
    H.sumCircleTimesSphereTwistedProjection r₀ c y =
      H.sumCircleTimesSphereTwistedRetraction r₀ (c (H.addBasepointGenerator r₀ y 1)) := by
  simp [sumCircleTimesSphereTwistedProjection]

/-- The splitting of the chains of the connected sum with `S¹ × S²` into their components at the
generators `(x, p)` and at the generators `(x, q)`. -/
private noncomputable def chainEquiv :
    ((H.sumCircleTimesSphere r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) ≃ₗ[
        MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)]
      (H.Generator →₀
          MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) ×
        (H.Generator →₀
          MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) where
  toFun c := (Finsupp.equivFunOnFinite.symm fun y => c (H.addBasepointGenerator r₀ y 0),
    Finsupp.equivFunOnFinite.symm fun y => c (H.addBasepointGenerator r₀ y 1))
  invFun c := Finsupp.equivFunOnFinite.symm fun g =>
    ![c.1 ((H.addBasepointGeneratorEquiv r₀).symm g).1,
      c.2 ((H.addBasepointGeneratorEquiv r₀).symm g).1] ((H.addBasepointGeneratorEquiv r₀).symm g).2
  map_add' c c' := by ext <;> simp
  map_smul' a c := by ext <;> simp
  left_inv c := by
    ext g
    obtain ⟨⟨y, k⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
    fin_cases k <;> simp
  right_inv c := by ext <;> simp

@[simp]
private theorem chainEquiv_apply_fst
    (c : (H.sumCircleTimesSphere r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
    (y : H.Generator) :
    (H.chainEquiv r₀ c).1 y = c (H.addBasepointGenerator r₀ y 0) := by
  simp [chainEquiv]

@[simp]
private theorem chainEquiv_apply_snd
    (c : (H.sumCircleTimesSphere r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
    (y : H.Generator) :
    (H.chainEquiv r₀ c).2 y = c (H.addBasepointGenerator r₀ y 1) := by
  simp [chainEquiv]

/-- The splitting of a basis chain at `(x, p)` is `(x, 0)`. -/
private theorem chainEquiv_single_zero (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) :
    H.chainEquiv r₀ (Finsupp.single (H.addBasepointGenerator r₀ x 0) a) =
      (Finsupp.single x a, 0) := by
  classical
  refine Prod.ext (Finsupp.ext fun y => ?_) (Finsupp.ext fun y => ?_)
  · rw [chainEquiv_apply_fst, Finsupp.single_apply, Finsupp.single_apply]
    simp [addBasepointGenerator_inj]
  · simp

/-- The splitting of a basis chain at `(x, q)` is `(0, x)`. -/
private theorem chainEquiv_single_one (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) :
    H.chainEquiv r₀ (Finsupp.single (H.addBasepointGenerator r₀ x 1) a) =
      (0, Finsupp.single x a) := by
  classical
  refine Prod.ext (Finsupp.ext fun y => ?_) (Finsupp.ext fun y => ?_)
  · simp
  · rw [chainEquiv_apply_snd, Finsupp.single_apply, Finsupp.single_apply]
    simp [addBasepointGenerator_inj]

variable [DecidableEq Region] [Fintype Region] {χ : Region → ℤ} (r : H.ReferenceDomains)

/-- The twisted hat differential of the original diagram, with its coefficients mapped into the
group ring of the periodic domains of the connected sum. -/
private noncomputable def extendedDifferential :
    (H.Generator →₀
        MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) →ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)]
      H.Generator →₀
        MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains) :=
  Finsupp.linearCombination _ fun x => Finsupp.mapRange (H.sumCircleTimesSphereRingHom r₀)
    (map_zero _) (H.twistedHatDifferential r χ (Finsupp.single x 1))

private theorem extendedDifferential_single (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) :
    H.extendedDifferential r₀ (χ := χ) r (Finsupp.single x a) =
      a • Finsupp.mapRange (H.sumCircleTimesSphereRingHom r₀) (map_zero _)
        (H.twistedHatDifferential r χ (Finsupp.single x 1)) := by
  simp [extendedDifferential]

/-- Extending the coefficients is a chain map. -/
private theorem extendedDifferential_mapRange
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    H.extendedDifferential r₀ (χ := χ) r
        (Finsupp.mapRange (H.sumCircleTimesSphereRingHom r₀) (map_zero _) c) =
      Finsupp.mapRange (H.sumCircleTimesSphereRingHom r₀) (map_zero _)
        (H.twistedHatDifferential r χ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' => simp only [Finsupp.mapRange_add (map_add _), map_add, hc, hc']
  | single x a =>
    ext y
    simp [extendedDifferential_single, mul_comm]

private theorem extendedDifferential_comp_self
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0) :
    H.extendedDifferential r₀ (χ := χ) r ∘ₗ H.extendedDifferential r₀ (χ := χ) r = 0 :=
  Finsupp.lhom_ext fun x a => by
    rw [LinearMap.comp_apply, extendedDifferential_single, map_smul, extendedDifferential_mapRange,
      ← LinearMap.comp_apply, hd]
    simp

variable {r₀} (hr₀ : r₀ ∈ Set.range H.basepoint) (hN : H.IsNice χ) (hW : H.WeaklyAdmissible)

include hr₀ hN hW in
/-- **The twisted hat differential of the connected sum is a mapping cone.** Under the splitting of
the chains into their components at the points `p` and `q`, the twisted hat differential of the
connected sum with `S¹ × S²` is the mapping cone of multiplication by `1 + t` on the twisted hat
complex of the original diagram with extended coefficients. -/
private theorem chainEquiv_comp_twistedHatDifferential :
    (H.chainEquiv r₀).toLinearMap ∘ₗ (H.sumCircleTimesSphere r₀).twistedHatDifferential
        (r.sumCircleTimesSphere r₀) (sumCircleTimesSphereEuler χ r₀) =
      LinearMap.mappingCone (H.extendedDifferential r₀ (χ := χ) r)
          (H.extendedDifferential r₀ (χ := χ) r)
          (LinearMap.lsmul _ _ (1 + single (Multiplicative.ofAdd
            (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1)) ∘ₗ
        (H.chainEquiv r₀).toLinearMap := by
  refine Finsupp.lhom_ext fun g a => ?_
  obtain ⟨⟨x, i⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
  have hinj (k : Fin 2) : Injective fun y : H.Generator => H.addBasepointGenerator r₀ y k :=
    fun y z h => ((H.addBasepointGenerator_inj r₀).mp h).1
  have hout (k m : Fin 2) (hkm : k ≠ m) (c : H.Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
      (y : H.Generator) :
      Finsupp.mapDomain (fun y => H.addBasepointGenerator r₀ y k) c
        (H.addBasepointGenerator r₀ y m) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ fun ⟨z, hz⟩ =>
      hkm ((H.addBasepointGenerator_inj r₀).mp hz).2
  simp only [addBasepointGeneratorEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    twistedHatDifferential_sumCircleTimesSphere_single H r hr₀ hN hW]
  fin_cases i <;> refine Prod.ext (Finsupp.ext fun y => ?_) (Finsupp.ext fun y => ?_)
  · simp [Finsupp.mapDomain_apply_of_injective (hinj 0), chainEquiv_single_zero,
      extendedDifferential_single, ZModModule.neg_eq_self]
  · -- The Koszul term `(1 + t) a` at `(x, q)`.
    classical
    by_cases hxy : x = y
    · subst hxy
      simp [hout 0 1 (by decide), chainEquiv_single_zero, add_mul]
    · simp [hout 0 1 (by decide), chainEquiv_single_zero, hxy]
  · simp [hout 1 0 (by decide), chainEquiv_single_one]
  · simp [Finsupp.mapDomain_apply_of_injective (hinj 1), chainEquiv_single_one,
      extendedDifferential_single]

private theorem lsmul_comp_extendedDifferential
    (u : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) :
    LinearMap.lsmul _ _ u ∘ₗ H.extendedDifferential r₀ (χ := χ) r =
      H.extendedDifferential r₀ (χ := χ) r ∘ₗ LinearMap.lsmul _ _ u :=
  LinearMap.ext fun c => by simp

include hr₀ hN hW in
/-- **The twisted hat differential of the connected sum with `S¹ × S²` squares to zero** if that of
the original diagram does. In a weakly admissible nice diagram and for a region `r₀` containing a
basepoint, the new differential is the mapping cone of multiplication by `1 + t` on the old one
with extended coefficients, and a mapping cone of a chain map squares to zero. -/
theorem twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0) :
    (H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) ∘ₗ
      (H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) = 0 := by
  have hc := H.chainEquiv_comp_twistedHatDifferential r hr₀ hN hW
  have h2 := LinearMap.mappingCone_comp_self _ (H.extendedDifferential_comp_self r₀ r hd)
    (H.extendedDifferential_comp_self r₀ r hd) (H.lsmul_comp_extendedDifferential r
      (1 + single (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1))
  refine LinearMap.ext fun c => (H.chainEquiv r₀).injective ?_
  have e1 := congr($hc ((H.sumCircleTimesSphere r₀).twistedHatDifferential
    (r.sumCircleTimesSphere r₀) (sumCircleTimesSphereEuler χ r₀) c))
  have e2 := congr($hc c)
  have e3 := congr($h2 (H.chainEquiv r₀ c))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at e1 e2 e3 ⊢
  rw [e1, e2, e3, map_zero]

variable (r₀) in
private theorem retractCoefficients_comp_extendedDifferential :
    H.retractCoefficients r₀ ∘ₛₗ H.extendedDifferential r₀ (χ := χ) r =
      H.twistedHatDifferential r χ ∘ₛₗ H.retractCoefficients r₀ :=
  Finsupp.lhom_ext fun x a => Finsupp.ext fun y => by
    simp [extendedDifferential_single]

omit [DecidableEq Region] [Fintype Region] in
variable (r₀) in
/-- The projection is the composite of the splitting of the chains, the projection to the
components at the points `q`, and the reduction of the coefficients at `t = 1`. -/
private theorem sumCircleTimesSphereTwistedProjection_eq :
    H.sumCircleTimesSphereTwistedProjection r₀ =
      (H.retractCoefficients r₀ ∘ₛₗ LinearMap.snd _ _ _) ∘ₛₗ (H.chainEquiv r₀).toLinearMap :=
  LinearMap.ext fun c => Finsupp.ext fun y => by simp

include hr₀ hN hW in
/-- **The projection is a chain map.** In a weakly admissible nice diagram and for a region `r₀`
containing a basepoint, the projection `c ↦ (y ↦ ε (c (y, q)))` intertwines the twisted hat
differential of the connected sum with `S¹ × S²` with that of the original diagram: the Koszul term
`(1 + t) c(y, p)` is killed by `ε`. -/
theorem sumCircleTimesSphereTwistedProjection_comp_twistedHatDifferential :
    H.sumCircleTimesSphereTwistedProjection r₀ ∘ₛₗ
        (H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
          (sumCircleTimesSphereEuler χ r₀) =
      H.twistedHatDifferential r χ ∘ₛₗ H.sumCircleTimesSphereTwistedProjection r₀ := by
  have hc := H.chainEquiv_comp_twistedHatDifferential r hr₀ hN hW
  have hπ := LinearMap.comp_snd_comp_mappingCone (d := H.extendedDifferential r₀ (χ := χ) r)
    (H.exact_lsmul_retractCoefficients (r₀ := r₀))
    (H.retractCoefficients_comp_extendedDifferential r₀ (χ := χ) r)
  refine LinearMap.ext fun c => ?_
  have e1 := congr($hc c)
  have e2 := congr($hπ (H.chainEquiv r₀ c))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at e1 e2 ⊢
  rw [sumCircleTimesSphereTwistedProjection_eq, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, e1, e2]
  simp

include hr₀ hN hW in
/-- **The connected sum with `S¹ × S²` does not change the twisted homology.** Suppose that `r₀`
contains a basepoint, that the diagram is nice and weakly admissible, and that its twisted hat
differential squares to zero. Then the projection
`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedProjection` induces a bijection from the
twisted homology of the connected sum onto that of the original diagram.

The twisted complex of the connected sum is the mapping cone of multiplication by `1 + t` on the
twisted complex of the original diagram with extended coefficients
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_sumCircleTimesSphere_single`). Since `1 + t`
is not a zero divisor, the cone computes the homology of the quotient by `1 + t`
(`LinearMap.bijective_homologyMap_comp_snd`), which is the original complex: setting `t = 1` is
the retraction, whose kernel is generated by `1 + t`
(`TauCeti.HeegaardRegionSystem.ker_sumCircleTimesSphereTwistedRetraction`). -/
theorem homologyMap_sumCircleTimesSphereTwistedProjection_bijective
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0) :
    Bijective (LinearMap.homologyMap (H.sumCircleTimesSphereTwistedProjection r₀)
      (H.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero r hr₀ hN hW hd) hd
      (H.sumCircleTimesSphereTwistedProjection_comp_twistedHatDifferential r hr₀ hN hW)) := by
  set u : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains) :=
    1 + single (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1))) 1
  have hu : IsRegular u := IsRegular.of_ne_zero' (one_add_single_ne_zero (by simp) _)
  have hD := H.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero r hr₀ hN hW hd
  have hext := H.extendedDifferential_comp_self r₀ r hd
  have hsmul := H.lsmul_comp_extendedDifferential (χ := χ) r u
  have hcone := LinearMap.mappingCone_comp_self _ hext hext hsmul
  have hc := H.chainEquiv_comp_twistedHatDifferential r hr₀ hN hW
  have hinj : Injective (LinearMap.lsmul _ (H.Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) u) :=
    fun c c' h => Finsupp.ext fun y => hu.left (by simpa using congr($h y))
  have hexact := H.exact_lsmul_retractCoefficients (r₀ := r₀)
  have hπe := H.retractCoefficients_comp_extendedDifferential r₀ (χ := χ) r
  -- The cone projection induces a bijection on homology.
  have hπ := LinearMap.bijective_homologyMap_comp_snd hext hext hd hsmul hinj
    (H.retractCoefficients_surjective r₀) hexact hπe
  -- The splitting of the chains induces a bijection on homology.
  have hΦ : Bijective (LinearMap.homologyMap (H.chainEquiv r₀).toLinearMap hD hcone hc) := by
    have h : ⇑(LinearMap.homologyMap (H.chainEquiv r₀).toLinearMap hD hcone hc) =
        (H.chainEquiv r₀).homologyEquiv hD hcone hc := funext fun z => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      simp
    rw [h]
    exact LinearEquiv.bijective _
  -- The projection is the composite of the two.
  have key : ∀ (Q : _ →ₛₗ[H.sumCircleTimesSphereTwistedRetraction r₀] _)
      (_ : Q = (H.retractCoefficients r₀ ∘ₛₗ LinearMap.snd _ _ _) ∘ₛₗ
        (H.chainEquiv r₀).toLinearMap) hQ, Bijective (LinearMap.homologyMap Q hD hd hQ) := by
    rintro _ rfl -
    rw [LinearMap.homologyMap_comp _ _ hD hcone hd hc
      (LinearMap.comp_snd_comp_mappingCone hexact hπe)]
    exact hπ.comp hΦ
  exact key _ (H.sumCircleTimesSphereTwistedProjection_eq r₀) _

/-- **The twisted homology of a connected sum with `S¹ × S²`.** In a weakly admissible nice diagram
whose twisted hat differential squares to zero, and for a region `r₀` containing a basepoint, the
twisted homology of the connected sum with `S¹ × S²` in `r₀` is that of the original diagram,
through the map induced by `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedProjection`.
The group ring of the periodic domains of the connected sum acts through the retraction `t ↦ 1`
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereTwistedHomologyEquiv_smul`). -/
noncomputable def sumCircleTimesSphereTwistedHomologyEquiv
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0) :
    ((H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀)).homology
        (H.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero r hr₀ hN hW hd) ≃+
      (H.twistedHatDifferential r χ).homology hd :=
  AddEquiv.ofBijective _
    (H.homologyMap_sumCircleTimesSphereTwistedProjection_bijective r hr₀ hN hW hd)

/-- The equivalence sends the class of a cycle `c` to the class of its projection
`y ↦ ε (c (y, q))`. -/
@[simp]
theorem sumCircleTimesSphereTwistedHomologyEquiv_mk
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0)
    (c : LinearMap.ker ((H.sumCircleTimesSphere r₀).twistedHatDifferential
      (r.sumCircleTimesSphere r₀) (sumCircleTimesSphereEuler χ r₀))) :
    H.sumCircleTimesSphereTwistedHomologyEquiv r hr₀ hN hW hd (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk ⟨H.sumCircleTimesSphereTwistedProjection r₀ c,
        LinearMap.map_mem_ker_of_comp_eq _
          (H.sumCircleTimesSphereTwistedProjection_comp_twistedHatDifferential r hr₀ hN hW)
          c.property⟩ := by
  rw [sumCircleTimesSphereTwistedHomologyEquiv, AddEquiv.ofBijective_apply]
  exact LinearMap.homologyMap_mk _ _ _ _ c

/-- **The coefficients act through the retraction.** An element `a` of the group ring of the
periodic domains of the connected sum with `S¹ × S²` acts on its twisted homology as its retraction
`ε a` acts on the twisted homology of the original diagram. -/
theorem sumCircleTimesSphereTwistedHomologyEquiv_smul
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains))
    (z : ((H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀)).homology
        (H.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero r hr₀ hN hW hd)) :
    H.sumCircleTimesSphereTwistedHomologyEquiv r hr₀ hN hW hd (a • z) =
      H.sumCircleTimesSphereTwistedRetraction r₀ a •
        H.sumCircleTimesSphereTwistedHomologyEquiv r hr₀ hN hW hd z :=
  map_smulₛₗ (LinearMap.homologyMap (H.sumCircleTimesSphereTwistedProjection r₀) _ hd
    (H.sumCircleTimesSphereTwistedProjection_comp_twistedHatDifferential r hr₀ hN hW)) a z

/-- **`1 + t` annihilates the twisted homology of a connected sum with `S¹ × S²`**: the class of
the sphere `S²` acts trivially. -/
theorem sumCircleTimesSphere_one_add_single_smul_eq_zero
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0)
    (z : ((H.sumCircleTimesSphere r₀).twistedHatDifferential (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀)).homology
        (H.twistedHatDifferential_sumCircleTimesSphere_comp_self_eq_zero r hr₀ hN hW hd)) :
    (1 + single (Multiplicative.ofAdd (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1)))
        (1 : ZMod 2) :
      MonoidAlgebra (ZMod 2) (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) • z =
        0 := by
  apply (H.sumCircleTimesSphereTwistedHomologyEquiv r hr₀ hN hW hd).injective
  rw [sumCircleTimesSphereTwistedHomologyEquiv_smul,
    sumCircleTimesSphereTwistedRetraction_one_add_single, zero_smul, map_zero]

end Homology

end HeegaardRegionSystem

end TauCeti
