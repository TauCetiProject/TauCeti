/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AddBasepoint
public import TauCeti.LowDimTopology.Heegaard.LensSpace.Diagram
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# The twisted hat complex after adding a basepoint: the Koszul factor `1 + t`

Adding a basepoint to a Heegaard diagram in a region `R₀` that already contains one
(`TauCeti.HeegaardRegionSystem.addBasepoint`) tensors the hat complex with the two-dimensional
space `W` on the two new points `p` and `q`, with zero differential
(`TauCeti.HeegaardRegionSystem.hatDifferential_comp_addBasepointChainEquiv`): the two crescents
`C_α` and `C_β` are the domains from `p` to `q`, and they cancel modulo two. The new diagram also
has one new periodic domain, `C_α - C_β`, the class of the sphere around the new basepoint
(`TauCeti.HeegaardRegionSystem.addBasepointPeriodicDomainsEquiv`). With twisted coefficients
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential`) the two crescents no longer cancel: their
labels differ by this class, so the twisted complex of the new diagram is the twisted complex of the
old one, with coefficients pushed into the larger group ring, tensored with the Koszul complex

`p ↦ (1 + t) q`, `q ↦ 0`

of the monomial `t = t^{C_α - C_β}`. This is the Koszul factor of the auxiliary `S¹ × S²` summand in
the twisted comparison for diagrams with several basepoints: a diagram of `Y` with `b` basepoints
has the periodic domains of `Y # (b - 1) (S¹ × S²)`, and each added basepoint contributes one Koszul
factor `1 + t_i`.

**Coefficients.** The group ring `R'` of the periodic domains of the new diagram contains the group
ring `R` of the old ones through the ring map
`TauCeti.HeegaardRegionSystem.addBasepointTwistedRingHom` induced by `Q ↦ (Q, 0)` under
`addBasepointPeriodicDomainsEquiv`. Since `R₀` contains a basepoint, every old periodic domain
vanishes on `R₀`, and `(Q, 0)` is just `Q` extended by zero over the new regions.

**Reference domains.** Reference domains `D_x` of the old diagram induce reference domains of the
new one (`TauCeti.HeegaardRegionSystem.ReferenceDomains.addBasepoint`): the reference generator of
`(x, k)` is `(x₀, p)` for the reference generator `x₀` of `x`, with reference domain `D_x` at
`(x, p)` and `D_x + C_β` at `(x, q)`. With these choices:

* between generators with the same new point, the counted domains are the old ones extended by zero,
  with the same labels, so the twisted coefficient is the image of the old one
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_self`);
* no domain is counted from `q` to `p`
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_one_zero`);
* from `(x, p)` to `(y, q)` the counted domains are a nonnegative domain `E` of Maslov index zero
  from `x` to `y` avoiding the basepoints together with one crescent. When `E = 0` is the only such
  domain, the twisted coefficient is `1 + t` for `x = y` and `0` otherwise: the crescent `C_β` has
  label `0` and the crescent `C_α` has label `C_α - C_β`
  (`HeegaardRegionSystem.WeaklyAdmissibleAt.twistedHatCoefficient_addBasepoint_zero_one_self` and
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_zero_one_of_ne`).

So, when the zero domain is the only nonnegative domain of Maslov index zero avoiding the
basepoints, the twisted hat differential of the new diagram is
`(∂' c)(y, k) = ∑ₓ c(x, k) ι(c(x, y)) + [k = q] (1 + t) c(y, p)`
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_apply`), the tensor product of
the old twisted differential with the Koszul complex of `1 + t`. Under the augmentation `t ↦ 1` the
factor `1 + t` becomes `0`, recovering `∂ ⊗ 1` on `CF̂ ⊗ W` at the level of chains. This is a
chain-level comparison only: homology does not commute with the non-flat augmentation.

**Lens spaces and the twice-pointed sphere.** The genus-one diagram of a lens space `L(p, q)`
(`TauCeti.HeegaardRegionSystem.lensSpace`) has no nonzero domain from a generator to itself avoiding
the basepoint, and no domain between distinct generators, so the hypothesis holds. Its twisted hat
differential vanishes, and after adding a basepoint in the basepoint region the twisted hat
differential sends the generator `(x, 0)` to `(1 + t) (x, 1)` and `(x, 1)` to `0`
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_apply`). Its cycles are
the chains vanishing on the generators `(x, 0)`, since `1 + t` is not a zero divisor
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_eq_zero_iff`). For
`L(1, 1) = S³` this is the twice-pointed diagram of `S³`: the raw complex has two generators and
zero differential, while the twisted one is the injective multiplication by `1 + t` on the group
ring `𝔽₂[t, t⁻¹]` of the single new periodic domain. Its cokernel `𝔽₂[t, t⁻¹] ⧸ (1 + t)` is `𝔽₂`,
as for `S¹ × S²` in `TauCeti.HeegaardRegionSystem.circleTimesSphereQuotientEquiv`; that quotient is
not computed again here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.addBasepointTwistedRingHom`: the ring map `R → R'` of group rings of
  periodic domains.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.addBasepoint`: the induced reference domains.

## Main results

* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_self`,
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_one_zero`,
  `TauCeti.HeegaardRegionSystem.WeaklyAdmissibleAt.twistedHatCoefficient_addBasepoint_zero_one_self`
  and `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_zero_one_of_ne`: the twisted
  coefficients of the diagram with an added basepoint.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_apply`: its twisted hat
  differential is the old one tensored with the Koszul complex of `1 + t`.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_apply` and
  `TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_eq_zero_iff`: the
  twisted hat complex of the diagram of a lens space with an added basepoint.

## References

* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830), §10
  (twisted coefficients for diagrams with several basepoints, and the comparison with the singly
  pointed theory).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §8 (Floer homology with twisted
  coefficients, and the twisted Floer homology of `S¹ × S²`).
-/

public section

open MonoidAlgebra Function

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint) (r₀ : Region)

section Ring

/-- The ring map from the group ring of the periodic domains of a diagram to that of the diagram
with an added basepoint in `r₀`, induced by the inclusion `Q ↦ (Q, 0)` of
`TauCeti.HeegaardRegionSystem.addBasepointPeriodicDomainsEquiv`. -/
noncomputable def addBasepointTwistedRingHom :
    MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) →+*
      MonoidAlgebra (ZMod 2) (Multiplicative (H.addBasepoint r₀).periodicDomains) :=
  mapDomainRingHom (ZMod 2) (AddMonoidHom.toMultiplicative
    ((H.addBasepointPeriodicDomainsEquiv r₀).toAddMonoidHom.comp (AddMonoidHom.inl _ _)))

/-- The ring map sends the monomial `t^Q` to the monomial `t^{(Q, 0)}`. -/
@[simp]
theorem addBasepointTwistedRingHom_single (Q : H.periodicDomains) (a : ZMod 2) :
    H.addBasepointTwistedRingHom r₀ (single (Multiplicative.ofAdd Q) a) =
      single (Multiplicative.ofAdd (H.addBasepointPeriodicDomainsEquiv r₀ (Q, 0))) a := by
  simp [addBasepointTwistedRingHom]

end Ring

namespace ReferenceDomains

variable {H r₀}

/-- The reference domains of the diagram with an added basepoint in a region `r₀` containing a
basepoint, induced by reference domains `D_x` of the original diagram: the reference generator of
`(x, k)` is `(x₀, 0)` for the reference generator `x₀` of `x`, and its reference domain is `D_x`
extended by `k` on the `β`-crescent and by zero on the other new regions. -/
noncomputable def addBasepoint (r : H.ReferenceDomains) (hr₀ : r₀ ∈ Set.range H.basepoint) :
    (H.addBasepoint r₀).ReferenceDomains where
  base g := H.addBasepointGenerator r₀ (r.base ((H.addBasepointGeneratorEquiv r₀).symm g).1) 0
  domain g := Sum.elim (r.domain ((H.addBasepointGeneratorEquiv r₀).symm g).1)
    ![0, (((H.addBasepointGeneratorEquiv r₀).symm g).2 : ℤ), 0]
  isDomainBetween_domain g := by
    obtain ⟨⟨x, k⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
    obtain ⟨z₀, rfl⟩ := hr₀
    simp only [addBasepointGeneratorEquiv_apply, addBasepointGeneratorEquiv_symm_apply]
    rw [isDomainBetween_addBasepoint_iff]
    exact ⟨r.isDomainBetween_domain x, by simp [r.domain_basepoint]⟩
  domain_basepoint g z := by
    rcases z with z | z <;> simp [r.domain_basepoint]
  base_eq_base {g g' D} hD hz := by
    obtain ⟨⟨x, i⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
    obtain ⟨⟨y, j⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g'
    simp only [addBasepointGeneratorEquiv_apply, addBasepointGeneratorEquiv_symm_apply] at hD ⊢
    rw [isDomainBetween_addBasepoint_iff] at hD
    rw [r.base_eq_base hD.1 fun z => by simpa using hz (Sum.inl z)]

variable (r : H.ReferenceDomains) (hr₀ : r₀ ∈ Set.range H.basepoint)

/-- The reference generator of `(x, k)` is `(x₀, 0)`, for the reference generator `x₀` of `x`. -/
@[simp]
theorem addBasepoint_base (x : H.Generator) (k : Fin 2) :
    (r.addBasepoint hr₀).base (H.addBasepointGenerator r₀ x k) =
      H.addBasepointGenerator r₀ (r.base x) 0 := by
  simp [addBasepoint]

/-- The reference domain of `(x, k)` is that of `x`, extended by `k` on the `β`-crescent and by
zero on the other new regions. -/
@[simp]
theorem addBasepoint_domain (x : H.Generator) (k : Fin 2) :
    (r.addBasepoint hr₀).domain (H.addBasepointGenerator r₀ x k) =
      Sum.elim (r.domain x) ![0, (k : ℤ), 0] := by
  simp [addBasepoint]

/-- The label of a domain of the diagram with an added basepoint is the label of its restriction
to the old regions, extended by the multiplicities of the new regions corrected by the reference
domains. -/
theorem addBasepoint_label (x y : H.Generator) (i j : Fin 2) (D : Region ⊕ Fin 3 → ℤ) :
    (r.addBasepoint hr₀).label (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) D =
      Sum.elim (r.label x y (D ∘ Sum.inl))
        fun m => ![0, (i : ℤ), 0] m + D (Sum.inr m) - ![0, (j : ℤ), 0] m := by
  funext s
  rcases s with s | m <;>
    simp only [label_def, addBasepoint_domain, Pi.add_apply, Pi.sub_apply, Sum.elim_inl,
      Sum.elim_inr, comp_apply]

end ReferenceDomains

section Hat

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}
  {r : H.ReferenceDomains} {r₀} (hr₀ : r₀ ∈ Set.range H.basepoint)

/-- **Twisted coefficients between generators with the same new point.** When `r₀` contains a
basepoint, the twisted coefficient of the diagram with an added basepoint from `(x, k)` to `(y, k)`
is the image of the twisted coefficient of the original diagram from `x` to `y`. -/
theorem twistedHatCoefficient_addBasepoint_self (x y : H.Generator) (k : Fin 2) :
    (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x k) (H.addBasepointGenerator r₀ y k) =
      H.addBasepointTwistedRingHom r₀ (H.twistedHatCoefficient r χ x y) := by
  classical
  have hset := H.hatDomains_addBasepoint_self (χ := χ) r₀ hr₀ x y k
  have hinj : Injective fun D : Region → ℤ => (Sum.elim D 0 : Region ⊕ Fin 3 → ℤ) :=
    fun D E h => funext fun s => congrFun h (Sum.inl s)
  rcases (H.hatDomains χ x y).finite_or_infinite with hfin | hinf
  · have := hfin.fintype
    have : Fintype ((H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x k) (H.addBasepointGenerator r₀ y k)) :=
      (show Set.Finite _ by rw [hset]; exact hfin.image _).fintype
    rw [twistedHatCoefficient_eq_sum, twistedHatCoefficient_eq_sum, map_sum]
    have hmem (E : H.hatDomains χ x y) : (Sum.elim E.val 0 : Region ⊕ Fin 3 → ℤ) ∈
        (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x k)
          (H.addBasepointGenerator r₀ y k) := by
      rw [hset]
      exact ⟨E.val, E.property, rfl⟩
    refine (Fintype.sum_bijective (fun E => ⟨Sum.elim E.val 0, hmem E⟩)
      ⟨fun E F h => Subtype.ext (hinj (congrArg Subtype.val h)), fun D => ?_⟩ _ _
      fun E => ?_).symm
    · obtain ⟨E, hE, hDE⟩ := (Set.ext_iff.mp hset D.val).mp D.property
      exact ⟨⟨E, hE⟩, Subtype.ext hDE⟩
    · rw [addBasepointTwistedRingHom_single]
      congr 2
      refine Subtype.ext ?_
      dsimp only
      rw [H.coe_addBasepointPeriodicDomainsEquiv_mk_zero r₀ hr₀,
        ReferenceDomains.addBasepoint_label]
      funext s
      rcases s with s | m
      · rfl
      · fin_cases m <;> simp
  · rw [twistedHatCoefficient_of_infinite hinf, map_zero, twistedHatCoefficient_of_infinite]
    rw [hset]
    exact hinf.image hinj.injOn

/-- **No twisted coefficient from `q` to `p`.** When `r₀` contains a basepoint, the twisted
coefficient of the diagram with an added basepoint from `(x, 1)` to `(y, 0)` vanishes. -/
theorem twistedHatCoefficient_addBasepoint_one_zero (x y : H.Generator) :
    (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x 1) (H.addBasepointGenerator r₀ y 0) = 0 :=
  twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty
    (H.hatDomains_addBasepoint_one_zero r₀ hr₀ x y)

/-- Under the hypothesis that the zero domain is the only nonnegative domain of Maslov index zero
from `x` to `y` avoiding the basepoints, the set of such domains is `{0}` when `x = y` and empty
otherwise. -/
private theorem setOf_maslovIndex_eq_zero {x y : H.Generator}
    (h₀ : ∀ E, H.IsDomainBetween x y E → (∀ z, E (H.basepoint z) = 0) → 0 ≤ E →
      H.maslovIndex χ x y E = 0 → E = 0) (E : Region → ℤ) :
    E ∈ {E | H.IsDomainBetween x y E ∧ (∀ z, E (H.basepoint z) = 0) ∧ 0 ≤ E ∧
      H.maslovIndex χ x y E = 0} ↔ x = y ∧ E = 0 := by
  constructor
  · rintro ⟨hD, hz, hE₀, hμ⟩
    obtain rfl := h₀ E hD hz hE₀ hμ
    exact ⟨isDomainBetween_zero_iff.mp hD, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨isDomainBetween_zero x, fun z => rfl, le_rfl, map_zero _⟩

variable {H} in
/-- **The Koszul coefficient `1 + t` from `p` to `q`.** Suppose that `r₀` contains a basepoint and
that the diagram is weakly admissible at `x`, so that the zero domain is the only nonnegative
periodic domain of Maslov index zero at `x`. Then the twisted coefficient of the diagram with an
added basepoint from `(x, 0)` to `(x, 1)` is `1 + t`, for the monomial `t` of the periodic domain
`C_α - C_β`: the crescent `C_α` is counted with label `C_α - C_β` and the crescent `C_β` with
label `0`. -/
theorem WeaklyAdmissibleAt.twistedHatCoefficient_addBasepoint_zero_one_self {x : H.Generator}
    (hW : H.WeaklyAdmissibleAt χ x) :
    (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1) =
      1 + single (Multiplicative.ofAdd (H.addBasepointPeriodicDomainsEquiv r₀ (0, 1))) 1 := by
  classical
  have h₀ (E : Region → ℤ) (hE : H.IsDomainBetween x x E) (hz : ∀ z, E (H.basepoint z) = 0)
      (hE₀ : 0 ≤ E) (hμ : H.maslovIndex χ x x E = 0) : E = 0 :=
    weaklyAdmissibleAt_iff.mp hW E (isDomainBetween_self_iff.mp ⟨hE, hz⟩) hμ hE₀
  have hset := H.hatDomains_addBasepoint_zero_one (χ := χ) r₀ hr₀ x x
  have hC (k : Fin 2) : (Sum.elim 0 (Pi.single k.castSucc 1) : Region ⊕ Fin 3 → ℤ) ∈
      (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
        (H.addBasepointGenerator r₀ x 1) := by
    rw [hset]
    exact ⟨((0 : Region → ℤ), k),
      ⟨(H.setOf_maslovIndex_eq_zero h₀ 0).mpr ⟨rfl, rfl⟩, Set.mem_univ _⟩, rfl⟩
  have hfin : Set.Finite ((H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀)
      (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1)) :=
    (Set.toFinite ({Pi.single (Sum.inr 0) 1, Pi.single (Sum.inr 1) 1} :
      Set (Region ⊕ Fin 3 → ℤ))).subset
      fun D hD => by
        rw [hset] at hD
        obtain ⟨⟨E, k⟩, ⟨hE, -⟩, rfl⟩ := hD
        obtain ⟨-, rfl⟩ := (H.setOf_maslovIndex_eq_zero h₀ E).mp hE
        fin_cases k <;> simp
  have := hfin.fintype
  have hne : (⟨_, hC 1⟩ : (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀)
      (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1)) ≠ ⟨_, hC 0⟩ := by
    intro h
    have := congrFun (congrArg Subtype.val h) (Sum.inr 0)
    simp at this
  have huniv : (Finset.univ : Finset ((H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀)
      (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1))) =
      {⟨_, hC 1⟩, ⟨_, hC 0⟩} := by
    ext ⟨D, hD⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
      true_iff]
    rw [hset] at hD
    obtain ⟨⟨E, k⟩, ⟨hE, -⟩, rfl⟩ := hD
    obtain ⟨-, rfl⟩ := (H.setOf_maslovIndex_eq_zero h₀ E).mp hE
    fin_cases k <;> simp
  rw [twistedHatCoefficient_eq_sum, huniv, Finset.sum_pair hne, one_def, ← ofAdd_zero]
  -- The crescent `C_β` has label `0` and the crescent `C_α` has label `C_α - C_β`.
  congr 3 <;> refine Subtype.ext ?_ <;> dsimp only <;>
    rw [ReferenceDomains.addBasepoint_label] <;> funext s <;> rcases s with s | m
  · simp
  · fin_cases m <;> simp
  · simp
  · fin_cases m <;> simp

/-- **No twisted coefficient from `p` to `q` between distinct generators.** Suppose that `r₀`
contains a basepoint and that the zero domain is the only nonnegative domain of Maslov index zero
from `x` to `y` avoiding the basepoints. If `x ≠ y`, the twisted coefficient of the diagram with an
added basepoint from `(x, 0)` to `(y, 1)` vanishes. -/
theorem twistedHatCoefficient_addBasepoint_zero_one_of_ne {x y : H.Generator}
    (h₀ : ∀ E, H.IsDomainBetween x y E → (∀ z, E (H.basepoint z) = 0) → 0 ≤ E →
      H.maslovIndex χ x y E = 0 → E = 0) (hxy : x ≠ y) :
    (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ y 1) = 0 := by
  refine twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty ?_
  rw [H.hatDomains_addBasepoint_zero_one r₀ hr₀ x y, Set.image_eq_empty, Set.prod_eq_empty_iff]
  exact Or.inl (Set.eq_empty_of_forall_notMem fun E hE =>
    hxy ((H.setOf_maslovIndex_eq_zero h₀ E).mp hE).1)

/-- **The twisted hat differential after adding a basepoint is a Koszul tensor product.** Suppose
that `r₀` contains a basepoint and that the zero domain is the only nonnegative domain of Maslov
index zero avoiding the basepoints. Then the twisted hat differential of the diagram with an added
basepoint in `r₀` sends a chain `c` to the chain whose coefficient at `(y, k)` is
`∑ₓ c(x, k) ι(c(x, y)) + [k = 1] (1 + t) c(y, 0)`, where `c(x, y)` are the twisted coefficients of
the original diagram, `ι` is `TauCeti.HeegaardRegionSystem.addBasepointTwistedRingHom` and `t` is
the monomial of the periodic domain `C_α - C_β`: the old twisted differential tensored with the
Koszul complex `p ↦ (1 + t) q`. -/
theorem twistedHatDifferential_addBasepoint_apply
    (h₀ : ∀ x y E, H.IsDomainBetween x y E → (∀ z, E (H.basepoint z) = 0) → 0 ≤ E →
      H.maslovIndex χ x y E = 0 → E = 0)
    (c : (H.addBasepoint r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.addBasepoint r₀).periodicDomains))
    (y : H.Generator) (k : Fin 2) :
    (H.addBasepoint r₀).twistedHatDifferential (r.addBasepoint hr₀) (addBasepointEuler χ r₀) c
        (H.addBasepointGenerator r₀ y k) =
      (∑ x, c (H.addBasepointGenerator r₀ x k) *
        H.addBasepointTwistedRingHom r₀ (H.twistedHatCoefficient r χ x y)) +
        if k = 1 then c (H.addBasepointGenerator r₀ y 0) *
          (1 + single (Multiplicative.ofAdd (H.addBasepointPeriodicDomainsEquiv r₀ (0, 1))) 1)
        else 0 := by
  classical
  rw [twistedHatDifferential_apply, Finsupp.sum_fintype _ _ (by simp),
    ← (H.addBasepointGeneratorEquiv r₀).sum_comp, Fintype.sum_prod_type]
  simp only [addBasepointGeneratorEquiv_apply, Fin.sum_univ_two]
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · simp [twistedHatCoefficient_addBasepoint_self H hr₀,
      twistedHatCoefficient_addBasepoint_one_zero H hr₀]
  · have hcoef (x : H.Generator) :
        (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
          (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ y 1) =
        if x = y then
          1 + single (Multiplicative.ofAdd (H.addBasepointPeriodicDomainsEquiv r₀ (0, 1))) 1
        else 0 := by
      split_ifs with hxy
      · subst hxy
        refine WeaklyAdmissibleAt.twistedHatCoefficient_addBasepoint_zero_one_self hr₀
          (weaklyAdmissibleAt_iff.mpr fun P hP hμ hP₀ => ?_)
        obtain ⟨hD, hz⟩ := isDomainBetween_self_iff.mpr hP
        exact h₀ x x P hD hz hP₀ hμ
      · exact H.twistedHatCoefficient_addBasepoint_zero_one_of_ne hr₀ (h₀ x y) hxy
    simp only [hcoef, twistedHatCoefficient_addBasepoint_self H hr₀, mul_ite, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact add_comm _ _

end Hat

section LensSpace

variable {p : ℕ} [NeZero p] {q : (ZMod p)ˣ} {s : ZMod p}
  (r : (lensSpace p q s).ReferenceDomains)

/-- **The twisted hat complex of a lens space with an added basepoint.** After adding a basepoint to
the genus-one diagram of `L(p, q)` in its basepoint region, the twisted hat differential sends a
chain `c` to the chain whose coefficient at `(y, 1)` is `(1 + t) c(y, 0)` and whose coefficient at
`(y, 0)` is zero: the direct sum over the generators of the Koszul complex of `1 + t`. For `p = 1`
this is the twice-pointed diagram of `S³`. -/
theorem twistedHatDifferential_addBasepoint_lensSpace_apply
    (c : ((lensSpace p q s).addBasepoint s).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative ((lensSpace p q s).addBasepoint s).periodicDomains))
    (y : (lensSpace p q s).Generator) (k : Fin 2) :
    ((lensSpace p q s).addBasepoint s).twistedHatDifferential
        (r.addBasepoint (Set.mem_range.mpr ⟨(), lensSpace_basepoint ()⟩))
        (addBasepointEuler 1 s) c ((lensSpace p q s).addBasepointGenerator s y k) =
      if k = 1 then c ((lensSpace p q s).addBasepointGenerator s y 0) *
        (1 + single (Multiplicative.ofAdd
          ((lensSpace p q s).addBasepointPeriodicDomainsEquiv s (0, 1))) 1)
      else 0 := by
  rw [twistedHatDifferential_addBasepoint_apply _ _
    (fun _ _ _ hE hz _ _ => eq_zero_of_isDomainBetween_lensSpace hE hz)]
  simp [twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty (hatDomains_lensSpace _ _)]

/-- **The cycles of the twisted hat complex of a lens space with an added basepoint** are the
chains vanishing on the generators `(x, 0)`: the coefficient `1 + t` is not a zero divisor. -/
theorem twistedHatDifferential_addBasepoint_lensSpace_eq_zero_iff
    (c : ((lensSpace p q s).addBasepoint s).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative ((lensSpace p q s).addBasepoint s).periodicDomains)) :
    ((lensSpace p q s).addBasepoint s).twistedHatDifferential
        (r.addBasepoint (Set.mem_range.mpr ⟨(), lensSpace_basepoint ()⟩))
        (addBasepointEuler 1 s) c = 0 ↔
      ∀ x, c ((lensSpace p q s).addBasepointGenerator s x 0) = 0 := by
  have : UniqueSums ((lensSpace p q s).addBasepoint s).periodicDomains :=
    UniqueSums.of_injective_addHom
      ((lensSpace p q s).addBasepoint s).periodicDomains.subtype.toAddHom Subtype.val_injective
      inferInstance
  have hne : (1 + single (Multiplicative.ofAdd
      ((lensSpace p q s).addBasepointPeriodicDomainsEquiv s (0, 1))) 1 :
      MonoidAlgebra (ZMod 2) (Multiplicative ((lensSpace p q s).addBasepoint s).periodicDomains))
      ≠ 0 := by
    intro h
    have := congrArg (fun f => f.coeff 1) h
    have h01 : (lensSpace p q s).addBasepointPeriodicDomainsEquiv s (0, 1) ≠ 0 := by
      simp
    simp [one_def, coeff_single, h01] at this
  constructor
  · intro h x
    have := twistedHatDifferential_addBasepoint_lensSpace_apply r c x 1
    simp only [h, Finsupp.zero_apply, ite_true] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hne
  · intro h
    ext g
    obtain ⟨⟨y, k⟩, rfl⟩ := ((lensSpace p q s).addBasepointGeneratorEquiv s).surjective g
    rw [addBasepointGeneratorEquiv_apply, twistedHatDifferential_addBasepoint_lensSpace_apply,
      h, zero_mul, ite_self, Finsupp.zero_apply]

end LensSpace

end HeegaardRegionSystem

end TauCeti
