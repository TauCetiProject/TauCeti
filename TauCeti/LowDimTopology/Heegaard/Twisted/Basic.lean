/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.SMul
public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.Algebra.MonoidAlgebra.Augmentation.Basic
public import TauCeti.Algebra.MonoidAlgebra.Units
public import TauCeti.LowDimTopology.Heegaard.HatDifferential

/-!
# The twisted hat differential of a Heegaard diagram

The hat differential of a Heegaard diagram counts, modulo two, the domains of holomorphic disks
from one generator to another. Its *twisted* version remembers, for each counted domain, a class
in the group of periodic domains, and so has coefficients in the group ring
`R = 𝔽₂[t^P : P periodic]`. Two domains from `x` to `y` avoiding the basepoints differ by a
periodic domain, so a choice of reference domains turns domains into periodic labels: choose, in
each class of generators joined by domains avoiding the basepoints, a reference generator `x₀`,
and for every generator `x` of the class a domain `D_x` from `x₀` to `x` avoiding the basepoints.
A domain `D` from `x` to `y` then has the label

`A(D) = D_x + D - D_y`,

a domain from `x₀` to itself avoiding the basepoints, that is, a periodic domain. Labels are
additive under juxtaposition, `A(D) + A(E) = A(D + E)`, and a periodic domain from `x` to itself
is its own label. The twisted coefficient from `x` to `y` is `∑_D t^{A(D)}`, the sum over the
domains counted by the hat differential, and the twisted hat differential is the `R`-linear map
on the free `R`-module on generators with these coefficients. On a geometric diagram the
periodic domains of a diagram with `b` basepoints of `Y` are the second homology of
`Y # (b - 1) (S¹ × S²)`, and this is the hat Floer complex with twisted coefficients in its
group ring; that identification is geometric and is not formalized here.

Setting every `t^P` to `1`, the coefficient-sum augmentation `R → 𝔽₂`
(`MonoidAlgebra.augmentation`), sends each twisted coefficient to the ordinary one, the number of
counted domains modulo two. Hence the augmentation of the twisted differential is the hat
differential `TauCeti.HeegaardRegionSystem.hatDifferential`, at the level of chains. This is a
chain-level comparison only: homology does not commute with the augmentation, which is not flat.

The twisted complex depends on the reference domains only up to an explicit isomorphism. Two
choices with the same reference generators differ at each generator `x` by the periodic domain
`a(x) = D'_x - D_x`, the coefficients are related by `c'(x, y) = t^{a(x) - a(y)} c(x, y)`, and the
diagonal map `x ↦ t^{a(x)} x` is an isomorphism of `R`-modules intertwining the two twisted
differentials.

Changing the reference generators reduces to this. If `x₀` is the reference generator of `x` for
`r`, replacing each reference domain `D_x` of `r` by `D'_{x₀} + D_x`, which starts at the reference
generator of `x` for another choice `r'`, gives reference domains with the reference generators of
`r'` (`TauCeti.HeegaardRegionSystem.ReferenceDomains.rebase`). This adds the same domain at both
ends of every counted domain, whose ends lie in one class, so the labels, the twisted coefficients
and the twisted differential are unchanged. Hence for any two choices of reference data the
twisted complexes are isomorphic by a diagonal map `x ↦ t^{a(x)} x`, one squares to zero exactly
when the other does, and their homologies are isomorphic as `R`-modules.

As for the hat differential, `TauCeti.HeegaardRegionSystem.hatDomains` counts the domains of the
supplied incidence data, and that this is the count of holomorphic disks is a theorem only for
genuine nice diagrams; neither that nor the vanishing of the square of the differential is
formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.ReferenceDomains`: reference generators and reference domains.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.label`: the label `D_x + D - D_y` of a domain.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.shift`: the periodic domain `a(x) = D'_x - D_x`
  between two choices of reference domains with the same reference generators.
* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient`: the twisted coefficient `∑_D t^{A(D)}`.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential`: the twisted hat differential.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.changeEquiv`: the diagonal isomorphism
  `x ↦ t^{a(x)} x` between the twisted complexes of two choices of reference domains.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.rebase`: reference domains moved to the reference
  generators of another choice.
* `TauCeti.HeegaardRegionSystem.twistedHatHomologyEquiv`: the isomorphism between the twisted
  homologies of any two choices of reference data.

## Main results

* `TauCeti.HeegaardRegionSystem.ReferenceDomains.instNonempty`: reference domains exist.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.label_mem_periodicDomains`: labels are periodic.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.label_add`: labels are additive.
* `TauCeti.HeegaardRegionSystem.augmentation_twistedHatCoefficient` and
  `TauCeti.HeegaardRegionSystem.mapRange_augmentation_twistedHatDifferential`: the augmentation
  of the twisted differential is the hat differential.
* `TauCeti.HeegaardRegionSystem.sum_twistedHatCoefficient_mul_twistedHatCoefficient_eq_zero`: if
  the twisted hat differential squares to zero, so does the matrix of its coefficients.
* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_eq_single_mul`: the coefficients for two
  choices of reference domains differ by the monomials `t^{a(x) - a(y)}`.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.changeEquiv_twistedHatDifferential`: the diagonal
  isomorphism intertwines the two twisted differentials.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_rebase`: moving the reference generators
  does not change the twisted differential.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.changeEquiv_rebase_twistedHatDifferential`: for
  any two choices of reference data, a diagonal isomorphism intertwines the twisted differentials.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_comp_self_eq_zero_iff`: whether the twisted
  differential squares to zero does not depend on the reference data.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic triangles and invariants for smooth four-manifolds*, Adv.
  Math. **202** (2006), [arXiv:math/0110169](https://arxiv.org/abs/math/0110169), §2.1 (the
  additive assignments and the twisted Floer complexes).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §8 (Floer homology with twisted
  coefficients).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830),
  §9 (the twisted complex of a nice diagram with several basepoints, and its independence of the
  reference generators and domains in Theorem 9.4) and §10 (twisted coefficients).
-/

public section

open MonoidAlgebra

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section ReferenceDomains

variable (H) in
/-- Reference domains for twisted coefficients: every generator `x` is joined to a reference
generator `base x` by a domain `domain x` avoiding the basepoints, and generators joined by a
domain avoiding the basepoints have the same reference generator. So there is one reference
generator in each class of generators joined by such domains. -/
@[ext]
structure ReferenceDomains where
  /-- The reference generator of the class of a generator. -/
  base : H.Generator → H.Generator
  /-- The reference domain from the reference generator to a generator. -/
  domain : H.Generator → Region → ℤ
  /-- The reference domain of `x` is a domain from `base x` to `x`. -/
  isDomainBetween_domain (x : H.Generator) : H.IsDomainBetween (base x) x (domain x)
  /-- The reference domains avoid the basepoints. -/
  domain_basepoint (x : H.Generator) (z : Basepoint) : domain x (H.basepoint z) = 0
  /-- Generators joined by a domain avoiding the basepoints have the same reference generator. -/
  base_eq_base {x y : H.Generator} {D : Region → ℤ} :
    H.IsDomainBetween x y D → (∀ z, D (H.basepoint z) = 0) → base x = base y

namespace ReferenceDomains

/-- Reference domains exist: being joined by a domain avoiding the basepoints is an equivalence
relation on generators, so choose a reference generator in each class and a domain avoiding the
basepoints from it to each generator of the class. -/
instance instNonempty : Nonempty H.ReferenceDomains := by
  classical
  let s : Setoid H.Generator :=
    { r x y := ∃ D, H.IsDomainBetween x y D ∧ ∀ z, D (H.basepoint z) = 0
      iseqv :=
        { refl x := ⟨0, isDomainBetween_zero x, fun _ => rfl⟩
          symm := fun ⟨D, hD, hz⟩ => ⟨-D, hD.neg, fun z => by simp [hz z]⟩
          trans := fun ⟨D, hD, hz⟩ ⟨E, hE, hz'⟩ =>
            ⟨D + E, hD.add hE, fun z => by simp [hz z, hz' z]⟩ } }
  choose D hD hz using fun x : H.Generator => Quotient.mk_out (s := s) x
  exact ⟨{ base x := (Quotient.mk s x).out
           domain := D
           isDomainBetween_domain := hD
           domain_basepoint := hz
           base_eq_base := fun hxy hxyz => congrArg Quotient.out (Quotient.sound ⟨_, hxy, hxyz⟩) }⟩

section Label

variable (r : H.ReferenceDomains)

/-- The label `D_x + D - D_y` of a domain `D` from `x` to `y`, for the reference domains `D_x`
and `D_y`. For a domain avoiding the basepoints it is a periodic domain
(`label_mem_periodicDomains`). -/
def label (x y : H.Generator) (D : Region → ℤ) : Region → ℤ :=
  r.domain x + D - r.domain y

variable {r} {x y w : H.Generator} {D E : Region → ℤ}

theorem label_def : r.label x y D = r.domain x + D - r.domain y :=
  (rfl)

/-- The label of a domain from `x` to `y` avoiding the basepoints is a periodic domain. -/
theorem label_mem_periodicDomains (hD : H.IsDomainBetween x y D)
    (hz : ∀ z, D (H.basepoint z) = 0) : r.label x y D ∈ H.periodicDomains := by
  have h := ((r.isDomainBetween_domain x).add hD).add (r.isDomainBetween_domain y).neg
  rw [← r.base_eq_base hD hz, ← sub_eq_add_neg] at h
  exact isDomainBetween_self_iff.mp ⟨h, fun z => by simp [label_def, hz z, r.domain_basepoint]⟩

/-- Labels are additive under juxtaposition of domains. -/
theorem label_add : r.label x y D + r.label y w E = r.label x w (D + E) := by
  simp only [label_def]
  abel

/-- A domain from a generator to itself is its own label. -/
@[simp]
theorem label_self : r.label x x D = D := by
  simp [label_def]

end Label

variable {r r' : H.ReferenceDomains}

/-- Two choices of reference domains with the same reference generators differ at each generator
by a periodic domain. -/
theorem domain_sub_domain_mem_periodicDomains (h : r.base = r'.base) (x : H.Generator) :
    r'.domain x - r.domain x ∈ H.periodicDomains := by
  have hx := (r'.isDomainBetween_domain x).add (r.isDomainBetween_domain x).neg
  rw [h, ← sub_eq_add_neg] at hx
  exact isDomainBetween_self_iff.mp
    ⟨hx, fun z => by simp [r.domain_basepoint, r'.domain_basepoint]⟩

/-- The labels of a domain for two choices of reference domains differ by the changes of the
reference domains at its ends. -/
theorem label_eq_label_add_sub (x y : H.Generator) (D : Region → ℤ) :
    r'.label x y D = r.label x y D + (r'.domain x - r.domain x) - (r'.domain y - r.domain y) := by
  simp only [label_def]
  abel

/-- The periodic domain `a(x) = D'_x - D_x` by which two choices of reference domains with the
same reference generators differ at the generator `x`. -/
def shift (h : r.base = r'.base) (x : H.Generator) : H.periodicDomains :=
  ⟨r'.domain x - r.domain x, domain_sub_domain_mem_periodicDomains h x⟩

@[simp]
theorem coe_shift (h : r.base = r'.base) (x : H.Generator) :
    (shift h x : Region → ℤ) = r'.domain x - r.domain x :=
  (rfl)

/-- The shift of the reverse change of reference domains is the negative of the shift. This is not
a simp lemma: by proof irrelevance its left-hand side matches every shift, so it would loop. -/
theorem shift_symm (h : r.base = r'.base) (x : H.Generator) : shift h.symm x = -shift h x :=
  Subtype.ext (by simp)

/-- The diagonal map `x ↦ t^{a(x)} x` with `a(x) = D'_x - D_x` (`shift`), between the twisted
complexes of two choices of reference domains with the same reference generators: the change of
basis from the standard basis to its rescaling by the units `t^{a(x)}`. It is an isomorphism of
modules over the group ring, with inverse `x ↦ t^{-a(x)} x` (`changeEquiv_symm_single`), and it
intertwines the twisted hat differentials (`changeEquiv_twistedHatDifferential`). -/
noncomputable def changeEquiv (h : r.base = r'.base) :
    (H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) ≃ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)]
      H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) :=
  Finsupp.basisSingleOne.equiv (Finsupp.basisSingleOne.unitsSMul fun x =>
    unitsSingle (1, toUnits (Multiplicative.ofAdd (shift h x)))) (Equiv.refl _)

/-- The diagonal map multiplies the generator `x` by `t^{a(x)}`. -/
@[simp]
theorem changeEquiv_single (h : r.base = r'.base) (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    changeEquiv h (Finsupp.single x a) =
      Finsupp.single x (single (Multiplicative.ofAdd (shift h x)) 1 * a) := by
  have hx : changeEquiv h (Finsupp.single x 1) =
      Finsupp.single x (single (Multiplicative.ofAdd (shift h x)) 1) := by
    simpa [changeEquiv, Module.Basis.unitsSMul_apply, Units.smul_def] using Module.Basis.equiv_apply
      (Finsupp.basisSingleOne (R := MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains))) x
      (Finsupp.basisSingleOne.unitsSMul fun x =>
        unitsSingle (1, toUnits (Multiplicative.ofAdd (shift h x)))) (Equiv.refl _)
  rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, hx]
  simp [mul_comm]

/-- The inverse of the diagonal map multiplies the generator `x` by `t^{-a(x)}`. -/
@[simp]
theorem changeEquiv_symm_single (h : r.base = r'.base) (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    (changeEquiv h).symm (Finsupp.single x a) =
      Finsupp.single x (single (Multiplicative.ofAdd (-shift h x)) 1 * a) := by
  rw [LinearEquiv.symm_apply_eq, changeEquiv_single, ← mul_assoc, single_mul_single, ← ofAdd_add]
  simp [← one_def]

/-- The coefficient of `x` in the image of a chain under the diagonal map is multiplied by
`t^{a(x)}`. -/
theorem changeEquiv_apply (h : r.base = r'.base)
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains))
    (x : H.Generator) :
    changeEquiv h c x = single (Multiplicative.ofAdd (shift h x)) 1 * c x := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply, mul_add]
  | single y a =>
    rw [changeEquiv_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with hy
    · rw [hy]
    · rw [mul_zero]

/-- A reference generator has the reference generator of its class for any other choice of
reference domains. -/
@[simp]
theorem base_base (r r' : H.ReferenceDomains) (x : H.Generator) :
    r'.base (r.base x) = r'.base x :=
  r'.base_eq_base (r.isDomainBetween_domain x) (r.domain_basepoint x)

/-- The reference domains `r` moved to the reference generators of `r'`. The reference domain of
`x` is `D'_{x₀} + D_x`, where `x₀` is the reference generator of `x` for `r`: the reference domain
of `r'` from the new reference generator of `x` to `x₀`, followed by that of `r` from `x₀` to `x`.
Its twisted hat differential is that of `r`
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_rebase`), and its reference generators are
those of `r'`, so `changeEquiv` compares it with `r'`. -/
def rebase (r r' : H.ReferenceDomains) : H.ReferenceDomains where
  base := r'.base
  domain x := r'.domain (r.base x) + r.domain x
  isDomainBetween_domain x := by
    simpa using (r'.isDomainBetween_domain (r.base x)).add (r.isDomainBetween_domain x)
  domain_basepoint x z := by simp [r.domain_basepoint, r'.domain_basepoint]
  base_eq_base := r'.base_eq_base

@[simp]
theorem rebase_base (r r' : H.ReferenceDomains) : (r.rebase r').base = r'.base :=
  (rfl)

@[simp]
theorem rebase_domain (r r' : H.ReferenceDomains) (x : H.Generator) :
    (r.rebase r').domain x = r'.domain (r.base x) + r.domain x :=
  (rfl)

/-- Moving the reference generators does not change the label of a domain between generators
with the same reference generator. -/
theorem label_rebase (r r' : H.ReferenceDomains) {x y : H.Generator} (h : r.base x = r.base y)
    (D : Region → ℤ) : (r.rebase r').label x y D = r.label x y D := by
  rw [label_def, label_def, rebase_domain, rebase_domain, h]
  abel

end ReferenceDomains

end ReferenceDomains

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

section Coefficient

/-- The label of a domain counted by the hat differential is a periodic domain. -/
theorem ReferenceDomains.label_mem_periodicDomains_of_mem_hatDomains (r : H.ReferenceDomains)
    {χ : Region → ℤ} {x y : H.Generator} {D : Region → ℤ} (hD : D ∈ H.hatDomains χ x y) :
    r.label x y D ∈ H.periodicDomains :=
  ReferenceDomains.label_mem_periodicDomains (mem_hatDomains_iff.mp hD).1
    (mem_hatDomains_iff.mp hD).2.1

variable (H) in
/-- The twisted coefficient of the generator `y` in the twisted hat differential of the
generator `x`: the sum of the monomials `t^{A(D)}` over the domains `D` counted by the hat
differential (`TauCeti.HeegaardRegionSystem.hatDomains`), where `A(D)` is the periodic label of
`D` for the reference domains `r`. It is `0` when infinitely many domains are counted, matching the
convention of `TauCeti.HeegaardRegionSystem.hatCoefficient`. -/
noncomputable def twistedHatCoefficient (r : H.ReferenceDomains) (χ : Region → ℤ)
    (x y : H.Generator) : MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) :=
  ∑ᶠ D : H.hatDomains χ x y, single (Multiplicative.ofAdd
    ⟨r.label x y D, r.label_mem_periodicDomains_of_mem_hatDomains D.property⟩) 1

variable {r : H.ReferenceDomains} {χ : Region → ℤ} {x y : H.Generator}

theorem twistedHatCoefficient_def :
    H.twistedHatCoefficient r χ x y = ∑ᶠ D : H.hatDomains χ x y, single (Multiplicative.ofAdd
      ⟨r.label x y D, r.label_mem_periodicDomains_of_mem_hatDomains D.property⟩) 1 :=
  (rfl)

/-- When finitely many domains are counted, the twisted coefficient is the finite sum of the
monomials of their labels. -/
theorem twistedHatCoefficient_eq_sum [Fintype (H.hatDomains χ x y)] :
    H.twistedHatCoefficient r χ x y = ∑ D : H.hatDomains χ x y,
      single (Multiplicative.ofAdd
        ⟨r.label x y D, r.label_mem_periodicDomains_of_mem_hatDomains D.property⟩) 1 :=
  finsum_eq_sum_of_fintype _

/-- When infinitely many domains are counted, the twisted coefficient is `0`. -/
theorem twistedHatCoefficient_of_infinite (h : (H.hatDomains χ x y).Infinite) :
    H.twistedHatCoefficient r χ x y = 0 := by
  have : Infinite (H.hatDomains χ x y) := h.to_subtype
  refine finsum_of_infinite_support ?_
  simp [Function.support, Set.infinite_univ]

/-- The twisted coefficient vanishes when no domain is counted. -/
theorem twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty (h : H.hatDomains χ x y = ∅) :
    H.twistedHatCoefficient r χ x y = 0 := by
  have : IsEmpty (H.hatDomains χ x y) := by rw [h]; infer_instance
  exact finsum_of_isEmpty _

/-- When exactly two distinct domains `D₁` and `D₂` are counted, the twisted coefficient is the
sum of the two monomials of their labels. -/
theorem twistedHatCoefficient_of_hatDomains_eq_pair {D₁ D₂ : Region → ℤ}
    (h : H.hatDomains χ x y = {D₁, D₂}) (hne : D₁ ≠ D₂) :
    H.twistedHatCoefficient r χ x y =
      single (Multiplicative.ofAdd ⟨r.label x y D₁, r.label_mem_periodicDomains_of_mem_hatDomains
        (h ▸ Set.mem_insert D₁ {D₂})⟩) 1 +
      single (Multiplicative.ofAdd ⟨r.label x y D₂, r.label_mem_periodicDomains_of_mem_hatDomains
        (h ▸ Set.mem_insert_of_mem D₁ rfl)⟩) 1 := by
  classical
  have := (show (H.hatDomains χ x y).Finite from h ▸ Set.toFinite _).fintype
  have hD₁ : D₁ ∈ H.hatDomains χ x y := h ▸ Set.mem_insert D₁ {D₂}
  have hD₂ : D₂ ∈ H.hatDomains χ x y := h ▸ Set.mem_insert_of_mem D₁ rfl
  have huniv : (Finset.univ : Finset (H.hatDomains χ x y)) = {⟨D₁, hD₁⟩, ⟨D₂, hD₂⟩} := by
    ext ⟨D, hD⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
      true_iff]
    rwa [h] at hD
  rw [twistedHatCoefficient_eq_sum, huniv, Finset.sum_pair (by simpa using hne)]

/-- In a weakly admissible diagram the twisted hat differential has no diagonal terms. -/
@[simp]
theorem WeaklyAdmissible.twistedHatCoefficient_self (hW : H.WeaklyAdmissible)
    (r : H.ReferenceDomains) (χ : Region → ℤ) (x : H.Generator) :
    H.twistedHatCoefficient r χ x x = 0 :=
  twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty (hW.hatDomains_self χ x)

/-- The coefficient of the monomial `t^P` in the twisted coefficient is the number, modulo two,
of counted domains with label `P`, provided finitely many domains are counted. -/
theorem coeff_twistedHatCoefficient (hfin : (H.hatDomains χ x y).Finite)
    (P : H.periodicDomains) :
    (H.twistedHatCoefficient r χ x y).coeff (Multiplicative.ofAdd P) =
      {D | D ∈ H.hatDomains χ x y ∧ r.label x y D = P}.ncard := by
  classical
  have := hfin.fintype
  rw [twistedHatCoefficient_eq_sum, coeff_sum, Finset.sum_apply']
  simp only [coeff_single, Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [Finset.sum_boole, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_coe_set_eq]
  congr 1
  exact Nat.card_congr
    { toFun := fun D => ⟨D.val, D.val.property, congrArg Subtype.val D.property⟩
      invFun := fun D => ⟨⟨D.val, D.property.1⟩, Subtype.ext D.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **The augmentation of the twisted coefficient.** Setting every monomial `t^P` to `1` sends
the twisted coefficient to the hat coefficient, the number of counted domains modulo two. -/
@[simp]
theorem augmentation_twistedHatCoefficient :
    augmentation (ZMod 2) _ (H.twistedHatCoefficient r χ x y) = H.hatCoefficient χ x y := by
  rcases (H.hatDomains χ x y).finite_or_infinite with hfin | hinf
  · have := hfin.fintype
    rw [twistedHatCoefficient_eq_sum, map_sum, hatCoefficient_def, ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    simp
  · rw [twistedHatCoefficient_of_infinite hinf, hatCoefficient_def, hinf.ncard, map_zero,
      Nat.cast_zero]

end Coefficient

section Differential

variable (H) in
/-- The twisted hat differential of a Heegaard diagram with region Euler characteristics `χ` and
reference domains `r`: the linear endomorphism of the free module on generators over the group
ring of the periodic domains whose coefficient from `x` to `y` is the twisted coefficient
`TauCeti.HeegaardRegionSystem.twistedHatCoefficient`. -/
noncomputable def twistedHatDifferential (r : H.ReferenceDomains) (χ : Region → ℤ) :
    (H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) →ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)]
      H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) :=
  Finsupp.linearCombination _ fun x =>
    Finsupp.equivFunOnFinite.symm (H.twistedHatCoefficient r χ x)

variable {r : H.ReferenceDomains} {χ : Region → ℤ}

/-- The matrix coefficients of the twisted hat differential are the twisted coefficients. -/
@[simp]
theorem twistedHatDifferential_single_apply (x y : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    H.twistedHatDifferential r χ (Finsupp.single x a) y = a * H.twistedHatCoefficient r χ x y := by
  simp [twistedHatDifferential]

/-- The coefficient of `y` in the twisted hat differential of a chain `c`. -/
theorem twistedHatDifferential_apply
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains))
    (y : H.Generator) :
    H.twistedHatDifferential r χ c y = c.sum fun x a => a * H.twistedHatCoefficient r χ x y := by
  simp [twistedHatDifferential, Finsupp.linearCombination_apply, Finsupp.sum_apply]

/-- The coefficient of `y` in the twisted hat differential of a chain `c`, as a sum over all
generators. -/
theorem twistedHatDifferential_apply_eq_sum
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains))
    (y : H.Generator) :
    H.twistedHatDifferential r χ c y = ∑ x, c x * H.twistedHatCoefficient r χ x y := by
  rw [twistedHatDifferential_apply, Finsupp.sum_fintype _ _ (by simp)]

/-- If the twisted hat differential squares to zero, then so does the matrix of its coefficients:
`∑_y c(x, y) c(y, z) = 0` for all generators `x` and `z`. -/
theorem sum_twistedHatCoefficient_mul_twistedHatCoefficient_eq_zero
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0) (x z : H.Generator) :
    ∑ y, H.twistedHatCoefficient r χ x y * H.twistedHatCoefficient r χ y z = 0 := by
  have h := congr($hd (Finsupp.single x 1) z)
  rw [LinearMap.comp_apply, twistedHatDifferential_apply_eq_sum] at h
  simpa using h

/-- **The augmentation of the twisted hat differential is the hat differential.** Applying the
augmentation `t^P ↦ 1` to the coefficients of chains turns the twisted hat differential into the
hat differential. -/
theorem mapRange_augmentation_twistedHatDifferential
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    (H.twistedHatDifferential r χ c).mapRange (augmentation (ZMod 2) _) (map_zero _) =
      H.hatDifferential χ (c.mapRange (augmentation (ZMod 2) _) (map_zero _)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add, Finsupp.mapRange_add (map_add _), hc, hd, Finsupp.mapRange_add (map_add _),
      map_add]
  | single x a =>
    ext y
    simp

end Differential

section Change

variable {r r' : H.ReferenceDomains} {χ : Region → ℤ}

/-- **Change of reference domains.** For two choices of reference domains with the same reference
generators, differing by the periodic domains `a(x) = D'_x - D_x`, the twisted coefficients are
related by `c'(x, y) = t^{a(x) - a(y)} c(x, y)`. -/
theorem twistedHatCoefficient_eq_single_mul (h : r.base = r'.base) (x y : H.Generator) :
    H.twistedHatCoefficient r' χ x y =
      single (Multiplicative.ofAdd (ReferenceDomains.shift h x - ReferenceDomains.shift h y)) 1 *
        H.twistedHatCoefficient r χ x y := by
  rcases (H.hatDomains χ x y).finite_or_infinite with hfin | hinf
  · have := hfin.fintype
    rw [twistedHatCoefficient_eq_sum, twistedHatCoefficient_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [single_mul_single, one_mul, ← ofAdd_add]
    refine congrArg (fun P => single (Multiplicative.ofAdd P) (1 : ZMod 2)) (Subtype.ext ?_)
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, ReferenceDomains.coe_shift,
      ReferenceDomains.label_eq_label_add_sub (r := r) (r' := r')]
    abel
  · rw [twistedHatCoefficient_of_infinite hinf, twistedHatCoefficient_of_infinite hinf, mul_zero]

namespace ReferenceDomains

variable (h : r.base = r'.base)

/-- **The change of reference domains is a chain isomorphism.** The diagonal map `x ↦ t^{a(x)} x`
carries the twisted hat differential for the reference domains `r'` to the one for `r`. -/
theorem changeEquiv_twistedHatDifferential
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    changeEquiv h (H.twistedHatDifferential r' χ c) =
      H.twistedHatDifferential r χ (changeEquiv h c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single x a =>
    refine Finsupp.ext fun y => ?_
    simp only [changeEquiv_apply, changeEquiv_single, twistedHatDifferential_single_apply,
      twistedHatCoefficient_eq_single_mul h]
    simp [mul_left_comm a, ← mul_assoc, single_mul_single]

end ReferenceDomains

/-- Moving the reference generators does not change the twisted coefficients: a counted domain
joins two generators with the same reference generator, and its label is unchanged. -/
@[simp]
theorem twistedHatCoefficient_rebase (r r' : H.ReferenceDomains) (x y : H.Generator) :
    H.twistedHatCoefficient (r.rebase r') χ x y = H.twistedHatCoefficient r χ x y := by
  rw [twistedHatCoefficient_def, twistedHatCoefficient_def]
  refine finsum_congr fun D => congrArg (fun P => single (Multiplicative.ofAdd P) (1 : ZMod 2))
    (Subtype.ext ?_)
  obtain ⟨hD, hz, -⟩ := mem_hatDomains_iff.mp D.property
  exact ReferenceDomains.label_rebase r r' (r.base_eq_base hD hz) D

/-- Moving the reference generators does not change the twisted hat differential. -/
@[simp]
theorem twistedHatDifferential_rebase (r r' : H.ReferenceDomains) :
    H.twistedHatDifferential (r.rebase r') χ = H.twistedHatDifferential r χ :=
  Finsupp.lhom_ext fun x a => Finsupp.ext fun y => by simp

namespace ReferenceDomains

/-- **Change of reference generators and domains.** For any two choices `r` and `r'` of reference
data, the diagonal map `x ↦ t^{a(x)} x` with `a(x) = D_x - D_{x₀'} - D'_x`, where `x₀'` is the
reference generator of `x` for `r'`, carries the twisted hat differential for `r` to the one for
`r'`. It is `changeEquiv` between `r'` moved to the reference generators of `r` and `r`. -/
theorem changeEquiv_rebase_twistedHatDifferential (r r' : H.ReferenceDomains)
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    changeEquiv (rebase_base r' r) (H.twistedHatDifferential r χ c) =
      H.twistedHatDifferential r' χ (changeEquiv (rebase_base r' r) c) := by
  rw [changeEquiv_twistedHatDifferential, twistedHatDifferential_rebase]

end ReferenceDomains

/-- Whether the twisted hat differential squares to zero does not depend on the choice of
reference generators and reference domains. -/
theorem twistedHatDifferential_comp_self_eq_zero_iff (r r' : H.ReferenceDomains) :
    H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0 ↔
      H.twistedHatDifferential r' χ ∘ₗ H.twistedHatDifferential r' χ = 0 := by
  suffices h : ∀ r r' : H.ReferenceDomains,
      H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0 →
        H.twistedHatDifferential r' χ ∘ₗ H.twistedHatDifferential r' χ = 0 from
    ⟨h r r', h r' r⟩
  intro r r' hd
  rw [((ReferenceDomains.changeEquiv (ReferenceDomains.rebase_base r' r)).eq_conjRingEquiv_apply_iff
    (H.twistedHatDifferential r χ) (e := H.twistedHatDifferential r' χ)).mpr
      (LinearMap.ext (ReferenceDomains.changeEquiv_rebase_twistedHatDifferential r r')).symm]
  exact (ReferenceDomains.changeEquiv _).conjRingEquiv_apply_comp_self hd

end Change

section Homology

variable {χ : Region → ℤ}

/-- **The twisted homology does not depend on the reference data.** For any two choices `r` and
`r'` of reference generators and reference domains for which the twisted hat differentials square
to zero (one does exactly when the other does,
`TauCeti.HeegaardRegionSystem.twistedHatDifferential_comp_self_eq_zero_iff`), the diagonal map of
`TauCeti.HeegaardRegionSystem.ReferenceDomains.changeEquiv_rebase_twistedHatDifferential` induces
an isomorphism of their twisted homologies, as modules over the group ring of the periodic
domains. -/
noncomputable def twistedHatHomologyEquiv (r r' : H.ReferenceDomains)
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0)
    (hd' : H.twistedHatDifferential r' χ ∘ₗ H.twistedHatDifferential r' χ = 0) :
    (H.twistedHatDifferential r χ).homology hd ≃ₗ[
      MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)]
      (H.twistedHatDifferential r' χ).homology hd' :=
  (ReferenceDomains.changeEquiv (ReferenceDomains.rebase_base r' r)).homologyEquiv hd hd'
    (LinearMap.ext (ReferenceDomains.changeEquiv_rebase_twistedHatDifferential r r'))

/-- The isomorphism of twisted homologies sends the class of a cycle `z` to the class of its image
under the diagonal map. -/
@[simp]
theorem twistedHatHomologyEquiv_mk (r r' : H.ReferenceDomains)
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0)
    (hd' : H.twistedHatDifferential r' χ ∘ₗ H.twistedHatDifferential r' χ = 0)
    (z : LinearMap.ker (H.twistedHatDifferential r χ)) :
    twistedHatHomologyEquiv r r' hd hd' (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨ReferenceDomains.changeEquiv (ReferenceDomains.rebase_base r' r) z,
        LinearMap.map_mem_ker_of_comp_eq
          (ReferenceDomains.changeEquiv (ReferenceDomains.rebase_base r' r)).toLinearMap
          (LinearMap.ext (ReferenceDomains.changeEquiv_rebase_twistedHatDifferential r r'))
          z.property⟩ :=
  LinearEquiv.homologyEquiv_mk _ hd hd' _ z

end Homology

end HeegaardRegionSystem

end TauCeti
