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
* from `(x, p)` to `(y, q)`, in a weakly admissible nice diagram, `1 + t` when `x = y` and zero
  otherwise (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_zero_one`):
  the counted domains are the two bigons, with labels `B₁ - B₂` and `0`.

In general the domains counted from `(x, p)` to `(y, q)` are the pairs of a nonnegative domain of
Maslov index zero from `x` to `y` avoiding the basepoints and one of the two bigons
(`TauCeti.HeegaardRegionSystem.hatDomains_sumCircleTimesSphere_zero_one`); in a weakly
admissible nice diagram the only such domain is the zero domain from `x` to itself
(`TauCeti.HeegaardRegionSystem.IsNice.eq_zero_of_maslovIndex_nonpos`).

Hence the twisted hat differential of the connected sum is `∂ ⊗ 1 + 1 ⊗ κ`, where `∂` is the
twisted hat differential of the original diagram with its coefficients extended to the larger
group ring, and `κ` is the Koszul differential `p ↦ (1 + t) q`, `q ↦ 0`, of the new factor
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_sumCircleTimesSphere_single`). Modulo two
the two bigons cancel and `κ` vanishes, which is the untwisted statement
`TauCeti.HeegaardRegionSystem.hatDifferential_sumCircleTimesSphere_comp_addBasepointChainEquiv`.
Since `1 + t` is a nonzerodivisor, informally the twisted homology of the connected sum is the
twisted homology of the original diagram, extended to the larger group ring, modulo `1 + t`. On a
geometric diagram the periodic domains of the connected sum are the second homology of
`Y # (S¹ × S²)` and the counted domains are the holomorphic disks; neither identification is
formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.sumCircleTimesSpherePeriodicDomainsEquiv`: the periodic domains of
  the connected sum are those of the original diagram times `ℤ`, the multiples of `B₁ - B₂`.
* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRingHom`: the induced map of group rings.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.sumCircleTimesSphere`: the reference domains of
  the connected sum induced by reference domains of the original diagram.

## Main results

* `TauCeti.HeegaardRegionSystem.ReferenceDomains.label_sumCircleTimesSphere`: the labels of
  domains of the connected sum.
* `TauCeti.HeegaardRegionSystem.hatDomains_sumCircleTimesSphere_self`,
  `TauCeti.HeegaardRegionSystem.hatDomains_sumCircleTimesSphere_zero_one` and
  `TauCeti.HeegaardRegionSystem.hatDomains_sumCircleTimesSphere_one_zero`: the domains counted by
  the hat differential of the connected sum.
* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_self`,
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_zero_one` and
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_sumCircleTimesSphere_one_zero`: its twisted
  hat coefficients.
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

/-- **The periodic domains of the connected sum with `S¹ × S²`.** The periodic domains of the
connected sum with `S¹ × S²` in `r₀` are those of the original diagram together with the multiples
of the difference `B₁ - B₂` of the two bigons. The pair `(Q, a)` goes to the extension of `Q` with
multiplicities `Q(r₀) + a` on `B₁` and `Q(r₀) - a` on `B₂`, and a periodic domain `P` goes to its
restriction to the old regions and `P(B₁) - P(r₀)`. Geometrically, `B₁ - B₂` is the class of the
sphere `S²` in `S¹ × S²`. -/
def sumCircleTimesSpherePeriodicDomainsEquiv :
    H.periodicDomains × ℤ ≃+ (H.sumCircleTimesSphere r₀).periodicDomains where
  toFun c := ⟨Sum.elim (c.1 : Region → ℤ)
      ![(c.1 : Region → ℤ) r₀ + c.2, (c.1 : Region → ℤ) r₀ - c.2],
    (H.mem_periodicDomains_sumCircleTimesSphere_iff r₀).mpr ⟨c.1.property, by simp; ring⟩⟩
  invFun P := (⟨(P : Region ⊕ Fin 2 → ℤ) ∘ Sum.inl,
    ((H.mem_periodicDomains_sumCircleTimesSphere_iff r₀).mp P.property).1⟩,
    (P : Region ⊕ Fin 2 → ℤ) (Sum.inr 0) - (P : Region ⊕ Fin 2 → ℤ) (Sum.inl r₀))
  left_inv c := by
    ext
    · rfl
    · simp
  right_inv P := by
    have hs := ((H.mem_periodicDomains_sumCircleTimesSphere_iff r₀).mp P.property).2
    ext (r | k)
    · rfl
    · fin_cases k
      · simp
      · simp
        omega
  map_add' c d := by
    ext (r | k)
    · rfl
    · fin_cases k <;> simp <;> ring

/-- The periodic domain attached to `(Q, a)` is `Q` extended by `Q(r₀) + a` on `B₁` and
`Q(r₀) - a` on `B₂`. -/
@[simp]
theorem coe_sumCircleTimesSpherePeriodicDomainsEquiv_apply (c : H.periodicDomains × ℤ) :
    (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ c : Region ⊕ Fin 2 → ℤ) =
      Sum.elim (c.1 : Region → ℤ) ![(c.1 : Region → ℤ) r₀ + c.2, (c.1 : Region → ℤ) r₀ - c.2] :=
  (rfl)

/-- The old periodic domain attached to a periodic domain of the connected sum is its restriction
to the old regions. -/
@[simp]
theorem coe_sumCircleTimesSpherePeriodicDomainsEquiv_symm_apply_fst
    (P : (H.sumCircleTimesSphere r₀).periodicDomains) :
    (((H.sumCircleTimesSpherePeriodicDomainsEquiv r₀).symm P).1 : Region → ℤ) =
      (P : Region ⊕ Fin 2 → ℤ) ∘ Sum.inl :=
  (rfl)

/-- The multiple of `B₁ - B₂` attached to a periodic domain `P` of the connected sum is
`P(B₁) - P(r₀)`. -/
@[simp]
theorem sumCircleTimesSpherePeriodicDomainsEquiv_symm_apply_snd
    (P : (H.sumCircleTimesSphere r₀).periodicDomains) :
    ((H.sumCircleTimesSpherePeriodicDomainsEquiv r₀).symm P).2 =
      (P : Region ⊕ Fin 2 → ℤ) (Sum.inr 0) - (P : Region ⊕ Fin 2 → ℤ) (Sum.inl r₀) :=
  (rfl)

/-- The periodic domain attached to `(0, 1)` is the difference `B₁ - B₂` of the two bigons. -/
theorem coe_sumCircleTimesSpherePeriodicDomainsEquiv_zero_one [DecidableEq Region] :
    (H.sumCircleTimesSpherePeriodicDomainsEquiv r₀ (0, 1) : Region ⊕ Fin 2 → ℤ) =
      Pi.single (Sum.inr 0) 1 - Pi.single (Sum.inr 1) 1 := by
  ext (r | k)
  · simp
  · fin_cases k <;> simp

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

section Hat

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {r₀ : Region} {χ : Region → ℤ}

/-- When `r₀` contains a basepoint, a domain of the connected sum is counted by its hat
differential from `(x, i)` to `(y, j)` exactly when its restriction to the old regions is a
nonnegative domain from `x` to `y` avoiding the basepoints, its multiplicities on the two bigons
are nonnegative with sum `j - i`, and the Maslov index of the restriction plus that sum is one. -/
private theorem mem_hatDomains_sumCircleTimesSphere_addBasepointGenerator_iff
    (hr₀ : r₀ ∈ Set.range H.basepoint) {x y : H.Generator} {i j : Fin 2}
    {D : Region ⊕ Fin 2 → ℤ} :
    D ∈ (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ y j) ↔
      H.IsDomainBetween x y (D ∘ Sum.inl) ∧ (∀ z, D (Sum.inl (H.basepoint z)) = 0) ∧
        0 ≤ D ∘ Sum.inl ∧ 0 ≤ D (Sum.inr 0) ∧ 0 ≤ D (Sum.inr 1) ∧
          D (Sum.inr 0) + D (Sum.inr 1) = (j : ℤ) - i ∧
            H.maslovIndex χ x y (D ∘ Sum.inl) + D (Sum.inr 0) + D (Sum.inr 1) = 1 := by
  obtain ⟨z₀, rfl⟩ := hr₀
  rw [mem_hatDomains_iff, isDomainBetween_sumCircleTimesSphere_iff,
    maslovIndex_sumCircleTimesSphere]
  simp only [Pi.le_def, Sum.forall, Pi.zero_apply, Function.comp_apply, Fin.forall_fin_two]
  constructor
  · rintro ⟨⟨hD, hs⟩, hz, ⟨hD0, h0, h1⟩, hμ⟩
    have hr : D (Sum.inl (H.basepoint z₀)) = 0 := hz z₀
    rw [hr] at hs hμ
    exact ⟨hD, hz, hD0, h0, h1, by simpa using hs, by simpa using hμ⟩
  · rintro ⟨hD, hz, hD0, h0, h1, hs, hμ⟩
    have hr : D (Sum.inl (H.basepoint z₀)) = 0 := hz z₀
    exact ⟨⟨hD, by simpa [hr] using hs⟩, hz, ⟨hD0, h0, h1⟩, by simpa [hr] using hμ⟩

/-- Between generators with the same new point, the domains counted by the hat differential of
the connected sum with `S¹ × S²` in a region containing a basepoint are those of the original
diagram, extended by zero on the two bigons. -/
theorem hatDomains_sumCircleTimesSphere_self (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) (i : Fin 2) :
    (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ y i) =
      (fun E : Region → ℤ => (Sum.elim E 0 : Region ⊕ Fin 2 → ℤ)) '' H.hatDomains χ x y := by
  ext D
  rw [H.mem_hatDomains_sumCircleTimesSphere_addBasepointGenerator_iff hr₀]
  constructor
  · rintro ⟨hD, hz, hD0, h0, h1, hs, hμ⟩
    have h0' : D (Sum.inr 0) = 0 := by omega
    have h1' : D (Sum.inr 1) = 0 := by omega
    refine ⟨D ∘ Sum.inl, mem_hatDomains_iff.mpr ⟨hD, hz, hD0, by simpa [h0', h1'] using hμ⟩, ?_⟩
    funext s
    rcases s with s | k
    · rfl
    · fin_cases k <;> simp [h0', h1']
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨hE, hz, hE0, hμ⟩ := mem_hatDomains_iff.mp hE
    exact ⟨by simpa using hE, by simpa using hz, by simpa using hE0, by simp, by simp, by simp,
      by simpa using hμ⟩

/-- From the new point `p` to the new point `q`, a domain counted by the hat differential of the
connected sum with `S¹ × S²` in a region containing a basepoint is a nonnegative domain of Maslov
index zero of the original diagram avoiding the basepoints, together with one of the two
bigons. -/
theorem hatDomains_sumCircleTimesSphere_zero_one (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) :
    (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ y 1) =
      (fun c : (Region → ℤ) × Fin 2 => Sum.elim c.1 (Pi.single c.2 1)) ''
        ({E | H.IsDomainBetween x y E ∧ (∀ z, E (H.basepoint z) = 0) ∧ 0 ≤ E ∧
          H.maslovIndex χ x y E = 0} ×ˢ Set.univ) := by
  ext D
  rw [H.mem_hatDomains_sumCircleTimesSphere_addBasepointGenerator_iff hr₀]
  constructor
  · rintro ⟨hD, hz, hD0, h0, h1, hs, hμ⟩
    simp only [Fin.isValue, Fin.val_one, Fin.val_zero, Nat.cast_one, Nat.cast_zero,
      sub_zero] at hs
    obtain ⟨k, hk0, hk1⟩ : ∃ k : Fin 2, D (Sum.inr 0) = (Pi.single k 1 : Fin 2 → ℤ) 0 ∧
        D (Sum.inr 1) = (Pi.single k 1 : Fin 2 → ℤ) 1 := by
      rcases (by omega : D (Sum.inr 0) = 1 ∧ D (Sum.inr 1) = 0 ∨
          D (Sum.inr 0) = 0 ∧ D (Sum.inr 1) = 1) with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    refine ⟨⟨D ∘ Sum.inl, k⟩, ⟨⟨hD, hz, hD0, ?_⟩, Set.mem_univ _⟩, ?_⟩
    · have : (D (Sum.inr 0) : ℚ) + D (Sum.inr 1) = 1 := by exact_mod_cast hs
      linarith
    · funext s
      rcases s with s | m
      · rfl
      · fin_cases m <;> fin_cases k <;> simp_all
  · rintro ⟨⟨E, k⟩, ⟨⟨hE, hz, hE0, hμ⟩, -⟩, rfl⟩
    fin_cases k <;>
      exact ⟨by simpa using hE, by simpa using hz, by simpa using hE0, by simp, by simp, by simp,
        by simp [hμ]⟩

/-- No domain counted by the hat differential of the connected sum with `S¹ × S²` in a region
containing a basepoint runs from the new point `q` to the new point `p`. -/
theorem hatDomains_sumCircleTimesSphere_one_zero (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) :
    (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x 1) (H.addBasepointGenerator r₀ y 0) = ∅ := by
  ext D
  simp only [H.mem_hatDomains_sumCircleTimesSphere_addBasepointGenerator_iff hr₀,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, -, h0, h1, hs, -⟩
  simp at hs
  omega

end Hat

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
  have hS := H.hatDomains_sumCircleTimesSphere_self (χ := χ) hr₀ x y i
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
    rw [H.hatDomains_sumCircleTimesSphere_zero_one hr₀, setOf_maslovIndex_eq_zero_self hN hW,
      Set.singleton_prod, Set.image_image, Set.image_univ]
  let e : Fin 2 ≃ (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
      (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1) :=
    (Equiv.ofInjective f hf).trans (Set.equivOfEq hS)
  have hl (k : Fin 2) := r.label_sumCircleTimesSphere r₀ x x 0 1 (f k)
  rw [twistedHatCoefficient_def, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype,
    Fin.sum_univ_two, add_comm (1 : MonoidAlgebra (ZMod 2) _), one_def]
  -- The label of `B₁` is `B₁ - B₂` and the label of `B₂` is `0`.
  congr 1
  · congr 2
    refine Subtype.ext ?_
    simp only [e, Equiv.trans_apply, Equiv.ofInjective_apply, Set.equivOfEq_apply, hl]
    ext (s | k)
    · simp [f]
    · fin_cases k <;> simp [f]
  · rw [← ofAdd_zero]
    congr 2
    refine Subtype.ext ?_
    simp only [e, Equiv.trans_apply, Equiv.ofInjective_apply, Set.equivOfEq_apply, hl]
    ext (s | k)
    · simp [f]
    · fin_cases k <;> simp [f]

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
    rw [H.hatDomains_sumCircleTimesSphere_zero_one hr₀, setOf_maslovIndex_eq_zero_of_ne hN hxy,
      Set.empty_prod, Set.image_empty]

/-- For the reference domains induced by `r`, the twisted coefficient of the connected sum with
`S¹ × S²` in a region containing a basepoint, from `(x, q)` to `(y, p)`, vanishes. -/
theorem twistedHatCoefficient_sumCircleTimesSphere_one_zero (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) :
    (H.sumCircleTimesSphere r₀).twistedHatCoefficient (r.sumCircleTimesSphere r₀)
        (sumCircleTimesSphereEuler χ r₀) (H.addBasepointGenerator r₀ x 1)
        (H.addBasepointGenerator r₀ y 0) = 0 :=
  twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty
    (H.hatDomains_sumCircleTimesSphere_one_zero hr₀ x y)

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
  have hgen {y z : H.Generator} {k m : Fin 2} :
      H.addBasepointGenerator r₀ y k = H.addBasepointGenerator r₀ z m ↔ y = z ∧ k = m :=
    ⟨fun h => Prod.ext_iff.mp
      (H.addBasepointGenerator_injective r₀ (a₁ := (y, k)) (a₂ := (z, m)) h),
      fun ⟨hyz, hkm⟩ => hyz ▸ hkm ▸ rfl⟩
  have hinj (k : Fin 2) : Injective fun y : H.Generator => H.addBasepointGenerator r₀ y k :=
    fun y z h => (hgen.mp h).1
  have hout (k m : Fin 2) (hkm : k ≠ m)
      (c : H.Generator →₀ MonoidAlgebra (ZMod 2)
        (Multiplicative (H.sumCircleTimesSphere r₀).periodicDomains)) (y : H.Generator) :
      Finsupp.mapDomain (fun y => H.addBasepointGenerator r₀ y k) c
        (H.addBasepointGenerator r₀ y m) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ fun ⟨z, hz⟩ => hkm (hgen.mp hz).2
  refine Finsupp.ext fun g => ?_
  obtain ⟨⟨y, j⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
  simp only [addBasepointGeneratorEquiv_apply, twistedHatDifferential_single_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · -- From `(x, p)` to `(y, p)`: the coefficient of the original diagram.
    simp [Finsupp.mapDomain_apply_of_injective (hinj 0),
      H.twistedHatCoefficient_sumCircleTimesSphere_self r hr₀, hgen]
  · -- From `(x, p)` to `(y, q)`: the Koszul coefficient `1 + t`.
    by_cases hxy : x = y
    · subst hxy
      simp [hout 0 1 (by decide),
        H.twistedHatCoefficient_sumCircleTimesSphere_zero_one_self r hr₀ hN hW, mul_comm]
    · simp [hout 0 1 (by decide),
        H.twistedHatCoefficient_sumCircleTimesSphere_zero_one_of_ne r hr₀ hN hxy, hgen, hxy]
  · -- From `(x, q)` to `(y, p)`: nothing.
    simp [hout 1 0 (by decide), H.twistedHatCoefficient_sumCircleTimesSphere_one_zero r hr₀]
  · -- From `(x, q)` to `(y, q)`: the coefficient of the original diagram.
    simp [Finsupp.mapDomain_apply_of_injective (hinj 1),
      H.twistedHatCoefficient_sumCircleTimesSphere_self r hr₀]

end Coefficient

end HeegaardRegionSystem

end TauCeti
