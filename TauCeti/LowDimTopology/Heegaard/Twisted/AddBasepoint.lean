/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AddBasepoint
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic

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
  (`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_zero_one_self` and
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_zero_one_of_ne`).

So, when the zero domain is the only nonnegative domain of Maslov index zero to `y` avoiding the
basepoints, the twisted hat differential of the new diagram at `y` is
`(∂' c)(y, k) = ∑ₓ c(x, k) ι(c(x, y)) + [k = q] (1 + t) c(y, p)`
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_apply`), the tensor product of
the old twisted differential with the Koszul complex of `1 + t`. Under the augmentation `t ↦ 1` the
factor `1 + t` becomes `0`, recovering `∂ ⊗ 1` on `CF̂ ⊗ W` at the level of chains. This is a
chain-level comparison only: homology does not commute with the non-flat augmentation.

The genus-one diagram of a lens space with an added basepoint, in particular the twice-pointed
diagram of `S³`, is treated in `TauCeti.LowDimTopology.Heegaard.Twisted.LensSpace`.

## Main definitions

* `TauCeti.HeegaardRegionSystem.addBasepointTwistedRingHom`: the ring map `R → R'` of group rings of
  periodic domains.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.addBasepoint`: the induced reference domains.

## Main results

* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_self`,
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_one_zero`,
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_zero_one_self` and
  `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_addBasepoint_zero_one_of_ne`: the twisted
  coefficients of the diagram with an added basepoint.
* `HeegaardRegionSystem.WeaklyAdmissibleAt.twistedHatCoefficient_addBasepoint_zero_one_self`: the
  coefficient `1 + t` at a generator where the diagram is weakly admissible.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_apply`: its twisted hat
  differential is the old one tensored with the Koszul complex of `1 + t`.

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
      · simp
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

include hr₀ in
/-- Under the hypothesis that the zero domain is the only nonnegative periodic domain of Maslov
index zero at `x` avoiding the basepoints, the domains counted from `(x, 0)` to `(x, 1)` in the
diagram with an added basepoint are exactly the two crescents `C_β` and `C_α`. -/
private theorem hatDomains_addBasepoint_zero_one_self {x : H.Generator}
    (h₀ : ∀ E, H.IsDomainBetween x x E → (∀ z, E (H.basepoint z) = 0) → 0 ≤ E →
      H.maslovIndex χ x x E = 0 → E = 0) :
    (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
        (H.addBasepointGenerator r₀ x 1) =
      {Sum.elim (0 : Region → ℤ) (Pi.single 1 1), Sum.elim (0 : Region → ℤ) (Pi.single 0 1)} := by
  ext D
  rw [H.hatDomains_addBasepoint_zero_one r₀ hr₀ x x]
  constructor
  · rintro ⟨⟨E, k⟩, ⟨hE, -⟩, rfl⟩
    obtain ⟨-, rfl⟩ := (H.setOf_maslovIndex_eq_zero h₀ E).mp hE
    fin_cases k <;> simp
  · have h0 := (H.setOf_maslovIndex_eq_zero h₀ 0).mpr ⟨rfl, rfl⟩
    rintro (rfl | rfl)
    exacts [⟨(0, 1), ⟨h0, Set.mem_univ _⟩, rfl⟩, ⟨(0, 0), ⟨h0, Set.mem_univ _⟩, rfl⟩]

/-- **The Koszul coefficient `1 + t` from `p` to `q`.** Suppose that `r₀` contains a basepoint and
that the zero domain is the only nonnegative periodic domain of Maslov index zero at `x` avoiding
the basepoints. Then the twisted coefficient of the diagram with an added basepoint from `(x, 0)`
to `(x, 1)` is `1 + t`, for the monomial `t` of the periodic domain `C_α - C_β`: the crescent `C_α`
is counted with label `C_α - C_β` and the crescent `C_β` with label `0`. -/
theorem twistedHatCoefficient_addBasepoint_zero_one_self {x : H.Generator}
    (h₀ : ∀ E, H.IsDomainBetween x x E → (∀ z, E (H.basepoint z) = 0) → 0 ≤ E →
      H.maslovIndex χ x x E = 0 → E = 0) :
    (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1) =
      1 + single (Multiplicative.ofAdd (H.addBasepointPeriodicDomainsEquiv r₀ (0, 1))) 1 := by
  have hne : (Sum.elim 0 (Pi.single 1 1) : Region ⊕ Fin 3 → ℤ) ≠
      Sum.elim (0 : Region → ℤ) (Pi.single 0 1) :=
    fun h => by simpa using congrFun h (Sum.inr 0)
  rw [twistedHatCoefficient_of_hatDomains_eq_pair
    (H.hatDomains_addBasepoint_zero_one_self hr₀ h₀) hne, one_def, ← ofAdd_zero]
  -- The crescent `C_β` has label `0` and the crescent `C_α` has label `C_α - C_β`.
  congr 3 <;> refine Subtype.ext ?_ <;> dsimp only <;>
    rw [ReferenceDomains.addBasepoint_label] <;> funext s <;> rcases s with s | m
  · simp
  · fin_cases m <;> simp
  · simp
  · fin_cases m <;> simp

variable {H} in
/-- **The Koszul coefficient `1 + t` at a weakly admissible generator.** If `r₀` contains a
basepoint and the diagram is weakly admissible at `x`, then the twisted coefficient of the diagram
with an added basepoint from `(x, 0)` to `(x, 1)` is `1 + t`. -/
theorem WeaklyAdmissibleAt.twistedHatCoefficient_addBasepoint_zero_one_self {x : H.Generator}
    (hW : H.WeaklyAdmissibleAt χ x) :
    (H.addBasepoint r₀).twistedHatCoefficient (r.addBasepoint hr₀) (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1) =
      1 + single (Multiplicative.ofAdd (H.addBasepointPeriodicDomainsEquiv r₀ (0, 1))) 1 :=
  H.twistedHatCoefficient_addBasepoint_zero_one_self hr₀ fun E hE hz hE₀ hμ =>
    weaklyAdmissibleAt_iff.mp hW E (isDomainBetween_self_iff.mp ⟨hE, hz⟩) hμ hE₀

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
that `r₀` contains a basepoint and that, for every generator `x`, the zero domain is the only
nonnegative domain of Maslov index zero from `x` to `y` avoiding the basepoints. Then the twisted
hat differential of the diagram with an added basepoint in `r₀` sends a chain `c` to the chain
whose coefficient at `(y, k)` is
`∑ₓ c(x, k) ι(c(x, y)) + [k = 1] (1 + t) c(y, 0)`, where `c(x, y)` are the twisted coefficients of
the original diagram, `ι` is `TauCeti.HeegaardRegionSystem.addBasepointTwistedRingHom` and `t` is
the monomial of the periodic domain `C_α - C_β`: the old twisted differential tensored with the
Koszul complex `p ↦ (1 + t) q`. -/
theorem twistedHatDifferential_addBasepoint_apply (y : H.Generator)
    (h₀ : ∀ x E, H.IsDomainBetween x y E → (∀ z, E (H.basepoint z) = 0) → 0 ≤ E →
      H.maslovIndex χ x y E = 0 → E = 0)
    (c : (H.addBasepoint r₀).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative (H.addBasepoint r₀).periodicDomains))
    (k : Fin 2) :
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
        exact H.twistedHatCoefficient_addBasepoint_zero_one_self hr₀ (h₀ _)
      · exact H.twistedHatCoefficient_addBasepoint_zero_one_of_ne hr₀ (h₀ x) hxy
    simp only [hcoef, twistedHatCoefficient_addBasepoint_self H hr₀, mul_ite, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact add_comm _ _

end Hat

end HeegaardRegionSystem

end TauCeti
