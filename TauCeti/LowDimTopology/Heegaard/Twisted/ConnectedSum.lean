/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.ConnectedSum
public import TauCeti.LowDimTopology.Heegaard.Nice
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic

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
augmentation `t ↦ 1` the coefficient `1 + t` becomes `0`, so `κ` vanishes and the untwisted
statement
`TauCeti.HeegaardRegionSystem.hatDifferential_sumCircleTimesSphere_comp_addBasepointChainEquiv`
follows.
Since `1 + t` is a nonzerodivisor, informally the twisted homology of the connected sum is the
twisted homology of the original diagram, extended to the larger group ring, modulo `1 + t`. On a
geometric diagram the periodic domains of the connected sum are the second homology of
`Y # (S¹ × S²)` and the counted domains are the holomorphic disks; neither identification is
formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRingHom`: the map of group rings induced by
  `TauCeti.HeegaardRegionSystem.sumCircleTimesSpherePeriodicDomainsEquiv`.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.sumCircleTimesSphere`: the reference domains of
  the connected sum induced by reference domains of the original diagram.

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

end HeegaardRegionSystem

end TauCeti
