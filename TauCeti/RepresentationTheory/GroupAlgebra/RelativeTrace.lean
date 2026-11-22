/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Relative traces in a group algebra

A group `G` acts on its group algebra `R[G]` by conjugation, `x ↦ g x g⁻¹`
(`TauCeti.conjRepresentation`). For a subgroup `H ≤ G` the fixed points `R[G]^H` form a
subalgebra, the centralizer of the image of `H` (`TauCeti.conjInvariants`); the centre of `R[G]` is
contained in every `R[G]^H`.

For subgroups `Q ≤ P` with `Q` of finite index in `P`, the **relative trace**
`Tr_Q^P : R[G]^Q → R[G]^P` sends `a` to `∑_{x ∈ P/Q} x a x⁻¹` (`TauCeti.relTrace`). It is the
relative norm `Representation.relNormInvariants` of the conjugation representation of `P` at `Q`,
and does not depend on the transversal (`TauCeti.relTrace_apply_eq_sum_of_bijective`). It is the
identity for `Q = P`, it multiplies `P`-fixed elements by the index `|P : Q|`, it is transitive
along `S ≤ Q ≤ P`, and it is a map of `R[G]^P`-bimodules: `Tr_Q^P(a) b = Tr_Q^P(a b)` and
`b Tr_Q^P(a) = Tr_Q^P(b a)` for `b ∈ R[G]^P`. Its image `R[G]^P_Q` is therefore an ideal of
`R[G]^P` (`TauCeti.relTraceIdeal`).

These are the relative traces of the ModularCharactersAndBlocks roadmap, §6.1, whose defect groups
are read from the ideals `R[G]^P_Q` and the Brauer homomorphism.

## Main definitions

* `TauCeti.conjRepresentation R G`: the conjugation representation of `G` on `R[G]`.
* `TauCeti.conjInvariants R H`: the subalgebra `R[G]^H` of `H`-fixed elements.
* `TauCeti.relTrace R hQP`: the relative trace `Tr_Q^P : R[G]^Q → R[G]^P`.
* `TauCeti.relTraceIdeal R hQP`: its image `R[G]^P_Q`, an ideal of `R[G]^P`.

## Main results

* `TauCeti.relTrace_apply_eq_sum_of_bijective`: `Tr_Q^P(a) = ∑ᵢ sᵢ a sᵢ⁻¹` for every transversal.
* `TauCeti.relTrace_self`, `TauCeti.relTrace_apply_of_mem`: `Tr_P^P = id`, and
  `Tr_Q^P(a) = |P : Q| a` for `a ∈ R[G]^P`.
* `TauCeti.relTrace_relTrace`: transitivity `Tr_Q^P ∘ Tr_S^Q = Tr_S^P`.
* `TauCeti.relTrace_mul`, `TauCeti.mul_relTrace`: the product formulas.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Lemma 11.3.1, pp. 194–195, and
  Proposition 12.4.1, p. 238.
-/

public section

namespace TauCeti

open MonoidAlgebra

section Semiring

variable (R G : Type*) [CommSemiring R] [Group G]

/-- The **conjugation representation** of `G` on its group algebra `R[G]`: `g` acts by the algebra
automorphism `x ↦ g x g⁻¹`, which sends `single h r` to `single (g h g⁻¹) r`. -/
noncomputable def conjRepresentation : Representation R G (MonoidAlgebra R G) :=
  (AlgEquiv.toLinearMapHom R (MonoidAlgebra R G)).comp
    ((MonoidAlgebra.domCongrAut (R := R) (A := R)).comp MulAut.conj)

variable {R G}

/-- The conjugation representation is the algebra automorphism `MonoidAlgebra.domCongr` of the
inner automorphism of `g`. -/
theorem conjRepresentation_apply (g : G) (x : MonoidAlgebra R G) :
    conjRepresentation R G g x = MonoidAlgebra.domCongr R R (MulAut.conj g) x := by
  simp [conjRepresentation]

/-- The coefficient of `g x g⁻¹` at `h` is the coefficient of `x` at `g⁻¹ h g`. -/
@[simp]
theorem coeff_conjRepresentation (g : G) (x : MonoidAlgebra R G) (h : G) :
    (conjRepresentation R G g x).coeff h = x.coeff (g⁻¹ * h * g) := by
  simp [conjRepresentation_apply]

/-- Conjugation by `g` sends `single h r` to `single (g h g⁻¹) r`. -/
@[simp]
theorem conjRepresentation_single (g h : G) (r : R) :
    conjRepresentation R G g (single h r) = single (g * h * g⁻¹) r := by
  simp [conjRepresentation_apply]

/-- Conjugation by `g` is `x ↦ g x g⁻¹` in `R[G]`. -/
theorem conjRepresentation_apply_eq_mul (g : G) (x : MonoidAlgebra R G) :
    conjRepresentation R G g x = of R G g * x * of R G g⁻¹ := by
  ext h
  simp [of_apply, coeff_single_mul_apply, coeff_mul_single_apply, mul_assoc]

/-- Conjugation by `g` is multiplicative. -/
theorem conjRepresentation_mul (g : G) (x y : MonoidAlgebra R G) :
    conjRepresentation R G g (x * y) = conjRepresentation R G g x * conjRepresentation R G g y :=
  map_mul (MonoidAlgebra.domCongr R R (MulAut.conj g)) x y

variable (R) in
/-- The subalgebra `R[G]^H` of elements of `R[G]` fixed by conjugation by `H`: the centralizer in
`R[G]` of the group elements of `H` (`TauCeti.mem_conjInvariants_iff`). -/
noncomputable def conjInvariants (H : Subgroup G) : Subalgebra R (MonoidAlgebra R G) :=
  Subalgebra.centralizer R (of R G '' H)

/-- An element lies in `R[G]^H` when it commutes with every element of `H`. -/
theorem mem_conjInvariants_iff_commute {H : Subgroup G} {x : MonoidAlgebra R G} :
    x ∈ conjInvariants R H ↔ ∀ h ∈ H, of R G h * x = x * of R G h := by
  simp [conjInvariants, Subalgebra.mem_centralizer_iff]

/-- An element lies in `R[G]^H` when conjugation by every element of `H` fixes it. -/
theorem mem_conjInvariants_iff {H : Subgroup G} {x : MonoidAlgebra R G} :
    x ∈ conjInvariants R H ↔ ∀ h ∈ H, conjRepresentation R G h x = x := by
  rw [mem_conjInvariants_iff_commute]
  refine forall₂_congr fun h _ => ?_
  rw [conjRepresentation_apply_eq_mul]
  constructor
  · intro hx
    rw [hx, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  · intro hx
    conv_rhs => rw [← hx]
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

/-- An element lies in `R[G]^H` when its coefficients are constant on `H`-conjugates. -/
theorem mem_conjInvariants_iff_coeff {H : Subgroup G} {x : MonoidAlgebra R G} :
    x ∈ conjInvariants R H ↔ ∀ h ∈ H, ∀ g : G, x.coeff (h * g * h⁻¹) = x.coeff g := by
  rw [mem_conjInvariants_iff]
  constructor
  · intro hx h hh g
    conv_lhs => rw [← hx h hh]
    simp [mul_assoc]
  · intro hx h hh
    ext g
    simpa using hx h⁻¹ (H.inv_mem hh) g

/-- Fixed points under a larger subgroup are fixed under a smaller one. -/
theorem conjInvariants_anti {H K : Subgroup G} (hHK : H ≤ K) :
    conjInvariants R K ≤ conjInvariants R H :=
  Subalgebra.centralizer_le R _ _ (Set.image_mono hHK)

/-- The centre of `R[G]` is fixed by every subgroup. -/
theorem center_le_conjInvariants (H : Subgroup G) :
    Subalgebra.center R (MonoidAlgebra R G) ≤ conjInvariants R H :=
  Subalgebra.center_le_centralizer R _

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-- The subalgebra `R[G]^H` is the module of invariants of the conjugation representation
restricted to `H`. -/
theorem conjInvariants_toSubmodule {G : Type*} [Group G] (H : Subgroup G) :
    Subalgebra.toSubmodule (conjInvariants R H) =
      Representation.invariants ((conjRepresentation R G).comp H.subtype) := by
  ext x
  rw [Subalgebra.mem_toSubmodule, mem_conjInvariants_iff, Representation.mem_invariants]
  exact ⟨fun hx h => hx h h.property, fun hx h hh => hx ⟨h, hh⟩⟩

variable (R) {G : Type*} [Group G] {S Q P : Subgroup G}

/-- The `Q`-fixed points of `R[G]`, read as the invariants of the conjugation representation of
`P` restricted to `Q`, for `Q ≤ P`. -/
private theorem conjInvariants_toSubmodule_subgroupOf (hQP : Q ≤ P) :
    Subalgebra.toSubmodule (conjInvariants R Q) =
      Representation.invariants
        (((conjRepresentation R G).comp P.subtype).comp (Q.subgroupOf P).subtype) := by
  ext x
  rw [Subalgebra.mem_toSubmodule, mem_conjInvariants_iff, Representation.mem_invariants]
  exact ⟨fun hx h => hx _ (Subgroup.mem_subgroupOf.1 h.property),
    fun hx h hh => hx ⟨⟨h, hQP hh⟩, Subgroup.mem_subgroupOf.2 hh⟩⟩

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (hQP : Q ≤ P) [(Q.subgroupOf P).FiniteIndex]

/-- The **relative trace** `Tr_Q^P : R[G]^Q → R[G]^P` for subgroups `Q ≤ P` with `Q` of finite
index in `P`: `a ↦ ∑_{x ∈ P/Q} x a x⁻¹`, summed over any transversal of `Q` in `P`
(`TauCeti.relTrace_apply_eq_sum_of_bijective`). It is the relative norm
`Representation.relNormInvariants` of the conjugation representation of `P` at `Q`. -/
noncomputable def relTrace : conjInvariants R Q →ₗ[R] conjInvariants R P :=
  (LinearEquiv.ofEq _ _ (conjInvariants_toSubmodule P).symm).toLinearMap ∘ₗ
    Representation.relNormInvariants ((conjRepresentation R G).comp P.subtype) (Q.subgroupOf P) ∘ₗ
      (LinearEquiv.ofEq _ _ (conjInvariants_toSubmodule_subgroupOf R hQP)).toLinearMap

variable {R}

/-- The relative trace sums the conjugates of `a` over the chosen representatives of `P/Q`. -/
theorem coe_relTrace (a : conjInvariants R Q) :
    (relTrace R hQP a : MonoidAlgebra R G) =
      ∑ q : P ⧸ Q.subgroupOf P, conjRepresentation R G (q.out : G) a := by
  simp [relTrace, Representation.relNorm_apply]
  rfl

/-- **The relative trace does not depend on the transversal.** For any family `s : ι → P` whose
cosets enumerate `P/Q` bijectively, `Tr_Q^P(a) = ∑ᵢ sᵢ a sᵢ⁻¹`. -/
theorem relTrace_apply_eq_sum_of_bijective {ι : Type*} [Fintype ι] (s : ι → P)
    (hs : Function.Bijective fun i => (s i : P ⧸ Q.subgroupOf P)) (a : conjInvariants R Q) :
    (relTrace R hQP a : MonoidAlgebra R G) = ∑ i, conjRepresentation R G (s i : G) a := by
  rw [coe_relTrace]
  let e := Equiv.ofBijective _ hs
  refine (Fintype.sum_equiv e _ _ fun i => ?_).symm
  have hmem : ((e i).out⁻¹ * s i : P) ∈ Q.subgroupOf P :=
    QuotientGroup.leftRel_apply.1 (Quotient.exact (by simp [e]))
  have hfix := mem_conjInvariants_iff.1 a.property _ (Subgroup.mem_subgroupOf.1 hmem)
  rw [← mul_inv_cancel_left ((e i).out : P) (s i), Subgroup.coe_mul, map_mul,
    mul_apply_eq_comp, hfix]

/-- `Tr_P^P` is the identity of `R[G]^P`. -/
theorem relTrace_self [(P.subgroupOf P).FiniteIndex] (a : conjInvariants R P) :
    relTrace R (le_refl P) a = a := by
  ext1
  rw [relTrace_apply_eq_sum_of_bijective _ (fun _ : Unit => 1), Fintype.sum_unique,
    OneMemClass.coe_one, map_one, one_apply_eq_self]
  refine ⟨fun _ _ _ => rfl, fun q => ⟨(), ?_⟩⟩
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact Quotient.sound (QuotientGroup.leftRel_apply.2 (by simp))

/-- On `P`-fixed elements, the relative trace is multiplication by the index `|P : Q|`. -/
theorem relTrace_apply_of_mem {a : conjInvariants R Q} (ha : (a : MonoidAlgebra R G) ∈
    conjInvariants R P) : (relTrace R hQP a : MonoidAlgebra R G) = (Q.subgroupOf P).index • a := by
  rw [coe_relTrace, Finset.sum_congr rfl fun q _ => mem_conjInvariants_iff.1 ha _ q.out.property,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.index]

variable (S) in
/-- The products `u v` of a representative `u` of `P/Q` and a representative `v` of `Q/S`
enumerate `P/S` bijectively. -/
private theorem bijective_mk_out_mul_out (hSQ : S ≤ Q) [(S.subgroupOf Q).FiniteIndex]
    [(S.subgroupOf P).FiniteIndex] :
    Function.Bijective fun uv : (P ⧸ Q.subgroupOf P) × (Q ⧸ S.subgroupOf Q) =>
      ((uv.1.out * ⟨uv.2.out, hQP uv.2.out.property⟩ : P) : P ⧸ S.subgroupOf P) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have h' := QuotientGroup.leftRel_apply.1 (Quotient.exact h)
    have hu : u = u' := by
      rw [← QuotientGroup.out_eq' u, ← QuotientGroup.out_eq' u']
      refine Quotient.sound (QuotientGroup.leftRel_apply.2 ?_)
      have := Subgroup.mem_subgroupOf.1 h'
      rw [Subgroup.mem_subgroupOf]
      simp only [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
      have h1 := hSQ this
      simpa [mul_assoc] using Q.mul_mem (Q.mul_mem v.out.property h1) (Q.inv_mem v'.out.property)
    subst hu
    refine Prod.ext rfl ?_
    rw [← QuotientGroup.out_eq' v, ← QuotientGroup.out_eq' v']
    refine Quotient.sound (QuotientGroup.leftRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_))
    have := Subgroup.mem_subgroupOf.1 h'
    simpa [mul_assoc] using this
  · rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, ← Subgroup.index, ← Subgroup.index, ← Subgroup.index,
      ← Subgroup.relIndex, ← Subgroup.relIndex, ← Subgroup.relIndex, mul_comm,
      Subgroup.relIndex_mul_relIndex S Q P hSQ hQP]

/-- **Transitivity of relative traces.** For `S ≤ Q ≤ P`, `Tr_Q^P ∘ Tr_S^Q = Tr_S^P`. -/
theorem relTrace_relTrace (hSQ : S ≤ Q) [(S.subgroupOf Q).FiniteIndex]
    [(S.subgroupOf P).FiniteIndex] (a : conjInvariants R S) :
    relTrace R hQP (relTrace R hSQ a) = relTrace R (hSQ.trans hQP) a := by
  ext1
  rw [relTrace_apply_eq_sum_of_bijective (hSQ.trans hQP) _ (bijective_mk_out_mul_out S hQP hSQ),
    Fintype.sum_prod_type, coe_relTrace]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coe_relTrace, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp]

/-- **Product formula.** For `a ∈ R[G]^Q` and `b ∈ R[G]^P`, `Tr_Q^P(a) b = Tr_Q^P(a b)`. -/
theorem relTrace_mul (a : conjInvariants R Q) (b : conjInvariants R P) :
    relTrace R hQP a * b =
      relTrace R hQP (a * Subalgebra.inclusion (conjInvariants_anti hQP) b) := by
  ext1
  rw [Subalgebra.coe_mul, coe_relTrace, coe_relTrace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Subalgebra.coe_mul, Subalgebra.coe_inclusion, conjRepresentation_mul,
    mem_conjInvariants_iff.1 b.property _ q.out.property]

/-- **Product formula.** For `a ∈ R[G]^Q` and `b ∈ R[G]^P`, `b Tr_Q^P(a) = Tr_Q^P(b a)`. -/
theorem mul_relTrace (a : conjInvariants R Q) (b : conjInvariants R P) :
    b * relTrace R hQP a =
      relTrace R hQP (Subalgebra.inclusion (conjInvariants_anti hQP) b * a) := by
  ext1
  rw [Subalgebra.coe_mul, coe_relTrace, coe_relTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Subalgebra.coe_mul, Subalgebra.coe_inclusion, conjRepresentation_mul,
    mem_conjInvariants_iff.1 b.property _ q.out.property]

variable (R) in
/-- The ideal `R[G]^P_Q = Tr_Q^P(R[G]^Q)` of `R[G]^P`: the image of the relative trace, an ideal
by the product formula `TauCeti.mul_relTrace`. -/
noncomputable def relTraceIdeal : Ideal (conjInvariants R P) where
  carrier := Set.range (relTrace R hQP)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨_, (mul_relTrace hQP a c).symm⟩

/-- The elements of `R[G]^P_Q` are the relative traces of elements of `R[G]^Q`. -/
theorem mem_relTraceIdeal_iff {x : conjInvariants R P} :
    x ∈ relTraceIdeal R hQP ↔ ∃ a, relTrace R hQP a = x :=
  Iff.rfl

end Ring

end TauCeti
