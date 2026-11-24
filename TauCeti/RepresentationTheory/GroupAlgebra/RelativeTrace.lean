/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import TauCeti.RepresentationTheory.RelativeNorm
import TauCeti.GroupTheory.Coset.Basic

/-!
# Relative traces in a group algebra

A group `G` acts on its group algebra `R[G]` by conjugation, `x ↦ g x g⁻¹`
(`TauCeti.conjRepresentation`). For a subgroup `H ≤ G` the fixed points `R[G]^H` form a
subalgebra, the centralizer of the image of `H` (`TauCeti.conjInvariants`). The centre of `R[G]`
is contained in every `R[G]^H`, and it is `R[G]^G`; the trivial subgroup fixes all of `R[G]`.

For subgroups `Q ≤ P` with `Q` of finite index in `P`, the **relative trace**
`Tr_Q^P : R[G]^Q → R[G]^P` sends `a` to `∑_{x ∈ P/Q} x a x⁻¹` (`TauCeti.relTrace`). It is the
relative norm `Representation.relNorm` of the conjugation representation of `P` at `Q`, and does
not depend on the transversal (`TauCeti.relTrace_apply_eq_sum_of_bijective`). It is the identity
for `Q = P`, it multiplies `P`-fixed elements by the index `|P : Q|`, it is transitive along
`S ≤ Q ≤ P`, and it is a map of `R[G]^P`-bimodules: `Tr_Q^P(a) b = Tr_Q^P(a b)` and
`b Tr_Q^P(a) = Tr_Q^P(b a)` for `b ∈ R[G]^P`. Its image `R[G]^P_Q` is therefore a two-sided ideal
of `R[G]^P` (`TauCeti.relTraceIdeal`), decreasing as `Q` shrinks and equal to `R[G]^P` for
`Q = P`.

For a `p`-subgroup `P` of a finite group in characteristic `p`, the ideals `R[G]^P_Q` for `Q < P`
lie in the kernel of the Brauer homomorphism of `P`, and the defect groups of the blocks of `R[G]`
are described through them.

## Main definitions

* `TauCeti.conjRepresentation R G`: the conjugation representation of `G` on `R[G]`.
* `TauCeti.conjInvariants R H`: the subalgebra `R[G]^H` of `H`-fixed elements.
* `TauCeti.relTrace R Q P`: the relative trace `Tr_Q^P : R[G]^Q → R[G]^P`.
* `TauCeti.relTraceIdeal R hQP`: its image `R[G]^P_Q`, a two-sided ideal of `R[G]^P`.

## Main results

* `TauCeti.conjInvariants_top`, `TauCeti.conjInvariants_bot`: `R[G]^G = Z(R[G])` and
  `R[G]^1 = R[G]`.
* `TauCeti.relTrace_apply_eq_sum_of_bijective`: `Tr_Q^P(a) = ∑ᵢ sᵢ a sᵢ⁻¹` for every transversal.
* `TauCeti.relTrace_self`, `TauCeti.relTrace_apply_of_mem`: `Tr_P^P = id`, and
  `Tr_Q^P(a) = |P : Q| a` for `a ∈ R[G]^P`.
* `TauCeti.relTrace_relTrace`: transitivity `Tr_Q^P ∘ Tr_S^Q = Tr_S^P`.
* `TauCeti.relTrace_mul`, `TauCeti.mul_relTrace`: the product formulas.
* `TauCeti.relTraceIdeal_mono`, `TauCeti.relTraceIdeal_self`: `R[G]^P_S ≤ R[G]^P_Q` for
  `S ≤ Q ≤ P`, and `R[G]^P_P = R[G]^P`.

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

/-- Conjugation by `g` fixes the identity `1` of `R[G]`. -/
@[simp]
theorem conjRepresentation_one (g : G) : conjRepresentation R G g 1 = 1 := by
  rw [conjRepresentation_apply, map_one]

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

/-- The fixed points of conjugation by all of `G` are the centre of `R[G]`. -/
theorem conjInvariants_top :
    conjInvariants R (⊤ : Subgroup G) = Subalgebra.center R (MonoidAlgebra R G) := by
  refine le_antisymm (fun x hx => Subalgebra.mem_center_iff.2 fun y => ?_)
    (center_le_conjInvariants ⊤)
  rw [mem_conjInvariants_iff_commute] at hx
  induction y using MonoidAlgebra.induction_on with
  | of g => exact hx g (Subgroup.mem_top g)
  | add y z hy hz => rw [add_mul, mul_add, hy, hz]
  | smul r y hy => rw [smul_mul_assoc, mul_smul_comm, hy]

/-- The trivial subgroup fixes all of `R[G]`. -/
@[simp]
theorem conjInvariants_bot : conjInvariants R (⊥ : Subgroup G) = ⊤ :=
  eq_top_iff.2 fun x _ => mem_conjInvariants_iff.2 fun h hh => by
    rw [Subgroup.mem_bot.1 hh, map_one, one_apply_eq_self]

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

end Ring

section RelTrace

variable (R : Type*) [CommSemiring R] {G : Type*} [Group G] {S Q P : Subgroup G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The **relative trace** `Tr_Q^P : R[G]^Q → R[G]^P` for subgroups `Q` and `P` with `Q ⊓ P` of
finite index in `P`: `a ↦ ∑_{x ∈ P/(Q ⊓ P)} x a x⁻¹`, summed over any transversal of `Q ⊓ P` in
`P` (`TauCeti.relTrace_apply_eq_sum_of_bijective`). It is the relative norm
`Representation.relNorm` of the conjugation representation of `P` at `Q.subgroupOf P`. The case of
interest is `Q ≤ P`, which the API lemmas assume where they need it. -/
noncomputable def relTrace (Q P : Subgroup G) [(Q.subgroupOf P).FiniteIndex] :
    conjInvariants R Q →ₗ[R] conjInvariants R P where
  toFun a :=
    ⟨Representation.relNorm ((conjRepresentation R G).comp P.subtype) (Q.subgroupOf P) a,
      mem_conjInvariants_iff.2 fun g hg =>
        Representation.relNorm_apply_eq_self ((conjRepresentation R G).comp P.subtype)
          (H := Q.subgroupOf P) (fun h => mem_conjInvariants_iff.1 a.property _
            (Subgroup.mem_subgroupOf.1 h.property)) ⟨g, hg⟩⟩
  map_add' a b := Subtype.ext (map_add _ (a : MonoidAlgebra R G) b)
  map_smul' c a := Subtype.ext (map_smul _ c (a : MonoidAlgebra R G))

variable {R} [(Q.subgroupOf P).FiniteIndex]

/-- The relative trace sums the conjugates of `a` over the chosen representatives of `P/Q`. -/
theorem coe_relTrace (a : conjInvariants R Q) :
    (relTrace R Q P a : MonoidAlgebra R G) =
      ∑ q : P ⧸ Q.subgroupOf P, conjRepresentation R G (q.out : G) a :=
  Representation.relNorm_apply _

/-- **The relative trace does not depend on the transversal.** For any family `s : ι → P` whose
cosets enumerate `P/Q` bijectively, `Tr_Q^P(a) = ∑ᵢ sᵢ a sᵢ⁻¹`. -/
theorem relTrace_apply_eq_sum_of_bijective {ι : Type*} [Fintype ι] (s : ι → P)
    (hs : Function.Bijective fun i => (s i : P ⧸ Q.subgroupOf P)) (a : conjInvariants R Q) :
    (relTrace R Q P a : MonoidAlgebra R G) = ∑ i, conjRepresentation R G (s i : G) a := by
  rw [coe_relTrace]
  let e := Equiv.ofBijective _ hs
  refine (Fintype.sum_equiv e _ _ fun i => ?_).symm
  have hmem : ((e i).out⁻¹ * s i : P) ∈ Q.subgroupOf P :=
    QuotientGroup.leftRel_apply.1 (Quotient.exact (by simp [e]))
  have hfix := mem_conjInvariants_iff.1 a.property _ (Subgroup.mem_subgroupOf.1 hmem)
  rw [← mul_inv_cancel_left ((e i).out : P) (s i), Subgroup.coe_mul, map_mul,
    mul_apply_eq_comp, hfix]

/-- On `P`-fixed elements, the relative trace is multiplication by the index `|P : Q|`. -/
theorem relTrace_apply_of_mem {a : conjInvariants R Q} (ha : (a : MonoidAlgebra R G) ∈
    conjInvariants R P) : (relTrace R Q P a : MonoidAlgebra R G) = (Q.subgroupOf P).index • a :=
  Representation.relNorm_apply_of_forall_apply_eq _ fun g =>
    mem_conjInvariants_iff.1 ha _ g.property

variable (hQP : Q ≤ P)

/-- On `R[G]^P`, viewed inside `R[G]^Q`, the relative trace is multiplication by `|P : Q|`. -/
theorem relTrace_inclusion (b : conjInvariants R P) :
    relTrace R Q P (Subalgebra.inclusion (conjInvariants_anti hQP) b) =
      (Q.subgroupOf P).index • b :=
  Subtype.ext (relTrace_apply_of_mem (a := Subalgebra.inclusion _ b) b.property)

/-- `Tr_P^P` is the identity of `R[G]^P`. -/
@[simp]
theorem relTrace_self [(P.subgroupOf P).FiniteIndex] (a : conjInvariants R P) :
    relTrace R P P a = a := by
  ext1
  rw [relTrace_apply_of_mem a.property, Subgroup.subgroupOf_self, Subgroup.index_top,
    one_smul]

/-- **Transitivity of relative traces.** For `S ≤ Q ≤ P`, `Tr_Q^P ∘ Tr_S^Q = Tr_S^P`. -/
theorem relTrace_relTrace (hSQ : S ≤ Q) (hQP : Q ≤ P) [(S.subgroupOf Q).FiniteIndex]
    [(S.subgroupOf P).FiniteIndex] (a : conjInvariants R S) :
    relTrace R Q P (relTrace R S Q a) = relTrace R S P a := by
  -- Cosets of `S` in `Q`, read inside `P`, enumerate `Q/S` through `Q.subgroupOf P ≃* Q`.
  have hE := Subgroup.mk_mulEquiv_out_bijective (Subgroup.subgroupOfEquivOfLe hQP)
    (H := (S.subgroupOf P).subgroupOf (Q.subgroupOf P)) (H' := S.subgroupOf Q)
    fun _ => by simp [Subgroup.mem_subgroupOf]
  have := Finite.of_injective _ hE.1
  have := Fintype.ofFinite (Q.subgroupOf P ⧸ (S.subgroupOf P).subgroupOf (Q.subgroupOf P))
  ext1
  rw [relTrace_apply_eq_sum_of_bijective _
      (Subgroup.mk_out_mul_out_bijective (Subgroup.subgroupOf_mono P hSQ)),
    Fintype.sum_prod_type, coe_relTrace]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [relTrace_apply_eq_sum_of_bijective _ hE, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp]
  simp [Subgroup.subgroupOfEquivOfLe_apply_coe]

/-- **Product formula.** For `a ∈ R[G]^Q` and `b ∈ R[G]^P`, `Tr_Q^P(a) b = Tr_Q^P(a b)`. -/
theorem relTrace_mul (a : conjInvariants R Q) (b : conjInvariants R P) :
    relTrace R Q P a * b =
      relTrace R Q P (a * Subalgebra.inclusion (conjInvariants_anti hQP) b) := by
  ext1
  rw [Subalgebra.coe_mul, coe_relTrace, coe_relTrace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Subalgebra.coe_mul, Subalgebra.coe_inclusion, conjRepresentation_mul,
    mem_conjInvariants_iff.1 b.property _ q.out.property]

/-- **Product formula.** For `a ∈ R[G]^Q` and `b ∈ R[G]^P`, `b Tr_Q^P(a) = Tr_Q^P(b a)`. -/
theorem mul_relTrace (a : conjInvariants R Q) (b : conjInvariants R P) :
    b * relTrace R Q P a =
      relTrace R Q P (Subalgebra.inclusion (conjInvariants_anti hQP) b * a) := by
  ext1
  rw [Subalgebra.coe_mul, coe_relTrace, coe_relTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Subalgebra.coe_mul, Subalgebra.coe_inclusion, conjRepresentation_mul,
    mem_conjInvariants_iff.1 b.property _ q.out.property]

variable (R) in
/-- The ideal `R[G]^P_Q = Tr_Q^P(R[G]^Q)` of `R[G]^P`: the image of the relative trace, an ideal
by the product formula `TauCeti.mul_relTrace`, and two-sided by `TauCeti.relTrace_mul`. -/
noncomputable def relTraceIdeal : Ideal (conjInvariants R P) where
  carrier := Set.range (relTrace R Q P)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨_, (mul_relTrace hQP a c).symm⟩

/-- The elements of `R[G]^P_Q` are the relative traces of elements of `R[G]^Q`. -/
theorem mem_relTraceIdeal_iff {x : conjInvariants R P} :
    x ∈ relTraceIdeal R hQP ↔ ∃ a, relTrace R Q P a = x :=
  Iff.rfl

/-- Every relative trace `Tr_Q^P(a)` lies in `R[G]^P_Q`. -/
@[simp]
theorem relTrace_mem_relTraceIdeal (a : conjInvariants R Q) :
    relTrace R Q P a ∈ relTraceIdeal R hQP :=
  ⟨a, rfl⟩

/-- `R[G]^P_Q` is a two-sided ideal of `R[G]^P`, by the product formula `TauCeti.relTrace_mul`. -/
instance instIsTwoSidedRelTraceIdeal : (relTraceIdeal R hQP).IsTwoSided where
  mul_mem_of_left b := by
    rintro ⟨a, rfl⟩
    exact ⟨_, (relTrace_mul hQP a b).symm⟩

/-- `R[G]^P_P` is all of `R[G]^P`, since `Tr_P^P` is the identity. -/
@[simp]
theorem relTraceIdeal_self [(P.subgroupOf P).FiniteIndex] :
    relTraceIdeal R (le_refl P) = ⊤ :=
  eq_top_iff.2 fun x _ => ⟨x, relTrace_self x⟩

/-- For `S ≤ Q ≤ P`, `R[G]^P_S ≤ R[G]^P_Q`, since `Tr_S^P = Tr_Q^P ∘ Tr_S^Q`. -/
theorem relTraceIdeal_mono (hSQ : S ≤ Q) [(S.subgroupOf Q).FiniteIndex]
    [(S.subgroupOf P).FiniteIndex] :
    relTraceIdeal R (hSQ.trans hQP) ≤ relTraceIdeal R hQP := by
  rintro _ ⟨a, rfl⟩
  exact ⟨relTrace R S Q a, relTrace_relTrace hSQ hQP a⟩

end RelTrace

end TauCeti
