/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.DoubleCoset.Finite
public import TauCeti.GroupTheory.Index.Basic
public import Mathlib.GroupTheory.Sylow
public import TauCeti.RepresentationTheory.RelativeNorm
public import TauCeti.Algebra.MonoidAlgebra.Augmentation.Basic
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.GroupTheory.DoubleCoset.Cover

/-!
# Relative traces in a group algebra

A group `G` acts on its group algebra `R[G]` by conjugation, `x ↦ g x g⁻¹`
(`TauCeti.conjRepresentation`). For a subgroup `H ≤ G` the fixed points `R[G]^H` form a
subalgebra, the centralizer of the image of `H` (`TauCeti.conjInvariants`). The centre of `R[G]`
is contained in every `R[G]^H`, and it is `R[G]^G`, a commutative ring; the trivial subgroup
fixes all of `R[G]`.

For subgroups `Q ≤ P` with `Q` of finite index in `P`, the **relative trace**
`Tr_Q^P : R[G]^Q → R[G]^P` sends `a` to `∑_{x ∈ P/Q} x a x⁻¹` (`TauCeti.relTrace`). It is the
relative norm `Representation.relNorm` of the conjugation representation of `P` at `Q`, and does
not depend on the transversal (`TauCeti.relTrace_apply_eq_sum_of_bijective`). It is the identity
for `Q = P`, it multiplies `P`-fixed elements, and augmentations, by the index `|P : Q|`, it is
transitive along `S ≤ Q ≤ P`, and it is a map of `R[G]^P`-bimodules:
`Tr_Q^P(a) b = Tr_Q^P(a b)` and `b Tr_Q^P(a) = Tr_Q^P(b a)` for `b ∈ R[G]^P`. Its image
`R[G]^P_Q` is therefore a two-sided ideal of `R[G]^P` (`TauCeti.relTraceIdeal`), decreasing as `Q`
shrinks and equal to `R[G]^P` for `Q = P`. On the centralizer `C_G(P)` the coefficients of
`Tr_Q^P(a)` are `|P : Q|` times those of `a`. For `g ∈ G`, the relative trace of `g` from its
stabilizer `P ⊓ C_G(g)` is the sum of the `P`-conjugates of `g`, each once.

Conjugation by `g ∈ G` is an algebra isomorphism `R[G]^H ≃ R[G]^{gHg⁻¹}`
(`TauCeti.conjInvariantsEquiv`), and it carries `Tr_Q^P` to `Tr_{gQg⁻¹}^{gPg⁻¹}`. For `T ≤ P`,
the **Mackey formula** expresses `Tr_Q^P(a)`, viewed in `R[G]^T`, as the sum over the double
cosets `TxQ` in `P` of the traces from `T ∩ xQx⁻¹` to `T` of `x a x⁻¹`.

Relative traces from subgroups of index invertible in `R` are onto: if `|P : H|` is a unit of `R`,
then `Tr_H^P(|P : H|⁻¹ b) = b` for `b ∈ R[G]^P`, so `Tr_H^P(R[G]^H) = R[G]^P`
(`TauCeti.relTraceIdeal_eq_top_of_isUnit_index`) and `Tr_H^L(R[G]^H) = Tr_P^L(R[G]^P)` for
`P ≤ L`. In characteristic `p` this applies to a Sylow `p`-subgroup `S` of `P`, so
`Tr_S^L(R[G]^S) = Tr_P^L(R[G]^P)` (`TauCeti.relTraceIdeal_eq_of_subgroupOf_eq_sylow`). For `P = G`,
every element of the centre `R[G]^G` is a trace from `S` (`TauCeti.relTraceIdeal_sylow_eq_top`).

For a `p`-subgroup `P` of a finite group in characteristic `p`, the ideals `R[G]^P_Q` for `Q < P`
lie in the kernel of the Brauer homomorphism of `P`, and the defect groups of the blocks of `R[G]`
are described through them.

## Main definitions

* `TauCeti.conjRepresentation R G`: the conjugation representation of `G` on `R[G]`.
* `TauCeti.conjInvariants R H`: the subalgebra `R[G]^H` of `H`-fixed elements.
* `TauCeti.relTrace R Q P`: the relative trace `Tr_Q^P : R[G]^Q → R[G]^P`.
* `TauCeti.relTraceIdeal R hQP`: its image `R[G]^P_Q`, a two-sided ideal of `R[G]^P`.
* `TauCeti.conjInvariantsEquiv R g H`: conjugation by `g` as `R[G]^H ≃ₐ R[G]^{gHg⁻¹}`.
* `TauCeti.conjInvariantsBotEquiv R`: `R[G] ≃ₐ R[G]^1`, each element as a `1`-fixed element.

## Main results

* `TauCeti.conjInvariants_top`, `TauCeti.conjInvariants_bot`: `R[G]^G = Z(R[G])` and
  `R[G]^1 = R[G]`.
* `TauCeti.mem_conjInvariants_closure_iff`: `R[G]^{⟨S⟩}` is the centralizer of `S`.
* `TauCeti.relTrace_apply_eq_sum_of_bijective`: `Tr_Q^P(a) = ∑ᵢ sᵢ a sᵢ⁻¹` for every transversal.
* `TauCeti.coe_relTrace_bot_top`: `Tr_1^G(a) = ∑_{g ∈ G} g a g⁻¹` for a finite group `G`.
* `TauCeti.relTrace_self`, `TauCeti.relTrace_apply_of_mem`: `Tr_P^P = id`, and
  `Tr_Q^P(a) = |P : Q| a` for `a ∈ R[G]^P`.
* `TauCeti.relTrace_relTrace`: transitivity `Tr_Q^P ∘ Tr_S^Q = Tr_S^P`.
* `TauCeti.relTrace_mul`, `TauCeti.mul_relTrace`: the product formulas.
* `TauCeti.augmentation_relTrace`: `ε(Tr_Q^P(a)) = |P : Q| ε(a)`.
* `TauCeti.coeff_relTrace_of_mem_centralizer`: `Tr_Q^P(a)` has coefficient `|P : Q| a_c` at
  `c ∈ C_G(P)`.
* `TauCeti.coeff_relTrace_single_inf_centralizer`: the relative trace of `g` from its
  stabilizer in `P` is the sum of the `P`-conjugates of `g`, each once.
* `TauCeti.relTraceIdeal_mono`, `TauCeti.relTraceIdeal_self`: `R[G]^P_S ≤ R[G]^P_Q` for
  `S ≤ Q ≤ P`, and `R[G]^P_P = R[G]^P`.
* `TauCeti.conjInvariantsEquiv_relTrace`: `g Tr_Q^P(a) g⁻¹ = Tr_{gQg⁻¹}^{gPg⁻¹}(g a g⁻¹)`.
* `TauCeti.mem_relTraceIdeal_conj`: a central element that is a trace from `P` is a trace from
  every conjugate `gPg⁻¹`.
* `TauCeti.inclusion_relTrace_eq_sum_relTrace_conj`,
  `TauCeti.inclusion_relTrace_eq_sum_doubleCoset`: the Mackey formula
  `Tr_Q^P(a) = ∑_{TxQ} Tr_{T ∩ xQx⁻¹}^T(x a x⁻¹)` in `R[G]^T` for `T ≤ P`, over any system of
  double coset representatives and over the double coset quotient.
* `TauCeti.relTrace_inclusion_smul_of_mul_index_eq_one`: `Tr_H^P(r b) = b` when
  `r |P : H| = 1` and `b ∈ R[G]^P`.
* `TauCeti.relTraceIdeal_eq_of_subgroupOf_eq_sylow`: in characteristic `p`,
  `Tr_S^L(R[G]^S) = Tr_P^L(R[G]^P)` for a Sylow `p`-subgroup `S` of `P ≤ L`.
* `TauCeti.relTraceIdeal_sylow_eq_top`: in characteristic `p`, `Tr_S^G(R[G]^S) = R[G]^G` for a
  Sylow `p`-subgroup `S`.

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

/-- The algebra automorphism `MonoidAlgebra.domCongrAut` of the inner automorphism of `g` is the
conjugation representation of `g`. -/
theorem domCongrAut_conj_apply (g : G) (x : MonoidAlgebra R G) :
    MonoidAlgebra.domCongrAut (R := R) (A := R) (MulAut.conj g) x = conjRepresentation R G g x := by
  rw [conjRepresentation_apply, MonoidAlgebra.domCongrAut_apply]

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

/-- Summing the conjugates `g x g⁻¹` over a finite group gives the sum of the conjugates
`g⁻¹ x g`, reindexed by `g ↦ g⁻¹`. -/
theorem sum_conjRepresentation_eq_sum_inv_mul_mul [Fintype G] (x : MonoidAlgebra R G) :
    ∑ g : G, conjRepresentation R G g x = ∑ g : G, of R G g⁻¹ * x * of R G g := by
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [conjRepresentation_apply_eq_mul, Equiv.inv_apply, inv_inv]

/-- Conjugation by `g` is multiplicative. -/
theorem conjRepresentation_mul (g : G) (x y : MonoidAlgebra R G) :
    conjRepresentation R G g (x * y) = conjRepresentation R G g x * conjRepresentation R G g y :=
  map_mul (MonoidAlgebra.domCongr R R (MulAut.conj g)) x y

/-- Conjugating by `h` and then by `g` is conjugating by `g * h`. This is not a simp lemma: simp
normalises `conjRepresentation R G (g * h)` the other way, with `map_mul`. -/
theorem conjRepresentation_conjRepresentation (g h : G) (x : MonoidAlgebra R G) :
    conjRepresentation R G g (conjRepresentation R G h x) = conjRepresentation R G (g * h) x := by
  rw [map_mul, mul_apply_eq_comp]

/-- Conjugation preserves the augmentation: `ε(g x g⁻¹) = ε(x)`. -/
@[simp]
theorem augmentation_conjRepresentation (g : G) (x : MonoidAlgebra R G) :
    augmentation R G (conjRepresentation R G g x) = augmentation R G x := by
  simp [conjRepresentation_apply_eq_mul, of_apply]

variable (R) in
/-- The subalgebra `R[G]^H` of elements of `R[G]` fixed by conjugation by `H`: the centralizer in
`R[G]` of the group elements of `H` (`TauCeti.mem_conjInvariants_iff`). -/
noncomputable def conjInvariants (H : Subgroup G) : Subalgebra R (MonoidAlgebra R G) :=
  Subalgebra.centralizer R (of R G '' H)

/-- An element lies in `R[G]^H` when it commutes with every element of `H`. -/
theorem mem_conjInvariants_iff_commute {H : Subgroup G} {x : MonoidAlgebra R G} :
    x ∈ conjInvariants R H ↔ ∀ h ∈ H, of R G h * x = x * of R G h := by
  simp [conjInvariants, Subalgebra.mem_centralizer_iff]

/-- An element lies in `R[G]^{⟨S⟩}` exactly when it commutes with every element of `S`. -/
theorem mem_conjInvariants_closure_iff {S : Set G} {x : MonoidAlgebra R G} :
    x ∈ conjInvariants R (Subgroup.closure S) ↔ ∀ g ∈ S, of R G g * x = x * of R G g := by
  rw [mem_conjInvariants_iff_commute]
  refine ⟨fun h g hg => h g (Subgroup.subset_closure hg), fun h g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => rw [map_one, one_mul, mul_one]
  | mul a b _ _ ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
    -- `a` is a unit of `R[G]`, so its inverse commutes with `x` as well
    have hc : Commute (((of R G).toHomUnits a : (MonoidAlgebra R G)ˣ) : MonoidAlgebra R G) x := by
      rw [MonoidHom.coe_toHomUnits]
      exact ha
    simpa only [← map_inv, MonoidHom.coe_toHomUnits] using hc.units_inv_left.eq

/-- An element lies in `R[G]^⟨g⟩` exactly when it commutes with `g`. -/
theorem mem_conjInvariants_zpowers_iff {g : G} {x : MonoidAlgebra R G} :
    x ∈ conjInvariants R (Subgroup.zpowers g) ↔ of R G g * x = x * of R G g := by
  rw [Subgroup.zpowers_eq_closure, mem_conjInvariants_closure_iff, Set.forall_mem_singleton]

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

/-- The centre `R[G]^G` is a commutative semiring. -/
noncomputable instance instCommSemiringConjInvariantsTop :
    CommSemiring (conjInvariants R (⊤ : Subgroup G)) :=
  { (inferInstance : Semiring (conjInvariants R (⊤ : Subgroup G))) with
    mul_comm x y := Subtype.ext <| by
      have hy : (y : MonoidAlgebra R G) ∈ Subalgebra.center R (MonoidAlgebra R G) := by
        rw [← conjInvariants_top]; exact y.property
      exact Subalgebra.mem_center_iff.1 hy x }

/-- The trivial subgroup fixes all of `R[G]`. -/
@[simp]
theorem conjInvariants_bot : conjInvariants R (⊥ : Subgroup G) = ⊤ :=
  eq_top_iff.2 fun x _ => mem_conjInvariants_iff.2 fun h hh => by
    rw [Subgroup.mem_bot.1 hh, map_one, one_apply_eq_self]

variable (R) in
/-- `R[G]` as the subalgebra `R[G]^1` of elements fixed by the trivial subgroup. -/
noncomputable def conjInvariantsBotEquiv :
    MonoidAlgebra R G ≃ₐ[R] conjInvariants R (⊥ : Subgroup G) :=
  Subalgebra.topEquiv.symm.trans (Subalgebra.equivOfEq _ _ conjInvariants_bot.symm)

/-- The isomorphism `R[G] ≃ R[G]^1` is the identity on underlying elements. -/
@[simp]
theorem coe_conjInvariantsBotEquiv (x : MonoidAlgebra R G) :
    (conjInvariantsBotEquiv R x : MonoidAlgebra R G) = x := by
  simp [conjInvariantsBotEquiv]

/-- The inverse of `R[G] ≃ R[G]^1` forgets that an element is `1`-fixed. -/
@[simp]
theorem conjInvariantsBotEquiv_symm_apply (y : conjInvariants R (⊥ : Subgroup G)) :
    (conjInvariantsBotEquiv R).symm y = (y : MonoidAlgebra R G) := by
  obtain ⟨x, rfl⟩ := (conjInvariantsBotEquiv R).surjective y
  simp

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

/-- The centre `R[G]^G` is a commutative ring. -/
noncomputable instance instCommRingConjInvariantsTop {G : Type*} [Group G] :
    CommRing (conjInvariants R (⊤ : Subgroup G)) :=
  { (inferInstance : CommSemiring (conjInvariants R (⊤ : Subgroup G))),
    (inferInstance : Ring (conjInvariants R (⊤ : Subgroup G))) with }

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

/-- The relative trace multiplies the augmentation by the index: `ε(Tr_Q^P(a)) = |P : Q| ε(a)`. -/
@[simp]
theorem augmentation_relTrace (a : conjInvariants R Q) :
    augmentation R G (relTrace R Q P a : MonoidAlgebra R G) =
      (Q.subgroupOf P).index • augmentation R G (a : MonoidAlgebra R G) := by
  rw [coe_relTrace, map_sum]
  simp only [augmentation_conjRepresentation, Finset.sum_const, Finset.card_univ,
    Subgroup.index, Nat.card_eq_fintype_card]

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

/-- The relative trace from the trivial subgroup to the whole of a finite group `G` is the sum of
all conjugates: `Tr_1^G(a) = ∑_{g ∈ G} g a g⁻¹`. -/
theorem coe_relTrace_bot_top [Fintype G] (a : conjInvariants R (⊥ : Subgroup G)) :
    (relTrace R ⊥ ⊤ a : MonoidAlgebra R G) = ∑ g : G, conjRepresentation R G g a := by
  refine relTrace_apply_eq_sum_of_bijective (fun g => ⟨g, Subgroup.mem_top g⟩)
    ⟨fun g h hgh => ?_, fun q => ?_⟩ a
  · have := QuotientGroup.leftRel_apply.1 (Quotient.exact hgh)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
    simpa [inv_mul_eq_one] using this
  · induction q using QuotientGroup.induction_on with
    | H x => exact ⟨x, rfl⟩

/-- On `P`-fixed elements, the relative trace is multiplication by the index `|P : Q|`. -/
theorem relTrace_apply_of_mem {a : conjInvariants R Q} (ha : (a : MonoidAlgebra R G) ∈
    conjInvariants R P) : (relTrace R Q P a : MonoidAlgebra R G) = (Q.subgroupOf P).index • a :=
  Representation.relNorm_apply_of_forall_apply_eq _ fun g =>
    mem_conjInvariants_iff.1 ha _ g.property

/-- **The trace from the trivial subgroup.** For finite `P`, `Tr_1^P(a) = ∑_{g ∈ P} g a g⁻¹`. -/
theorem relTrace_bot_apply [Fintype P] (a : conjInvariants R (⊥ : Subgroup G)) :
    (relTrace R ⊥ P a : MonoidAlgebra R G) = ∑ g : P, conjRepresentation R G (g : G) a := by
  refine relTrace_apply_eq_sum_of_bijective id ⟨fun g h hgh => ?_, QuotientGroup.mk_surjective⟩ a
  rwa [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot, inv_mul_eq_one] at hgh

/-- The coefficient of `Tr_Q^P(a)` at an element of `C_G(P)` is `|P : Q|` times that of `a`. -/
theorem coeff_relTrace_of_mem_centralizer (a : conjInvariants R Q) {c : G}
    (hc : c ∈ Subgroup.centralizer (P : Set G)) :
    (relTrace R Q P a : MonoidAlgebra R G).coeff c =
      (Q.subgroupOf P).index • (a : MonoidAlgebra R G).coeff c := by
  classical
  rw [coe_relTrace, coeff_sum]
  simp only [Finsupp.finsetSum_apply, coeff_conjRepresentation]
  have hconj (q : P) : (q : G)⁻¹ * c * q = c := by
    rw [mul_assoc, ← Subgroup.mem_centralizer_iff.1 hc q q.property, inv_mul_cancel_left]
  simp only [hconj, Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card,
    Fintype.card_eq_nat_card]

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

section Conj

open scoped Pointwise

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G]

/-- Conjugation by `g` carries `R[G]^H` into `R[G]^{gHg⁻¹}`. -/
theorem conjRepresentation_mem_conjInvariants (g : G) {H : Subgroup G} {x : MonoidAlgebra R G}
    (hx : x ∈ conjInvariants R H) :
    conjRepresentation R G g x ∈ conjInvariants R (MulAut.conj g • H) := by
  rw [mem_conjInvariants_iff] at hx ⊢
  intro h hh
  have := hx _ ((mem_conj_smul g H h).1 hh)
  rw [conjRepresentation_conjRepresentation, show h * g = g * (g⁻¹ * h * g) by group,
    ← conjRepresentation_conjRepresentation, this]

/-- Conjugation by `g` maps `R[G]^H` onto `R[G]^{gHg⁻¹}`. -/
theorem map_conjInvariants (g : G) (H : Subgroup G) :
    (conjInvariants R H).map (MonoidAlgebra.domCongrAut (R := R) (A := R) (MulAut.conj g) :
      MonoidAlgebra R G →ₐ[R] MonoidAlgebra R G) = conjInvariants R (MulAut.conj g • H) := by
  refine le_antisymm ?_ fun y hy => ⟨conjRepresentation R G g⁻¹ y, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact conjRepresentation_mem_conjInvariants g hx
  · simpa [map_inv, inv_smul_smul] using conjRepresentation_mem_conjInvariants g⁻¹ hy
  · -- the `AlgHom` coercion of an `AlgEquiv` applies as the `AlgEquiv` (`AlgEquiv.coe_toAlgHom`)
    exact (domCongrAut_conj_apply g _).trans (Representation.self_inv_apply _ g y)

variable (R) in
/-- Conjugation by `g` as an algebra isomorphism `R[G]^H ≃ R[G]^{gHg⁻¹}`, `x ↦ g x g⁻¹`. -/
noncomputable def conjInvariantsEquiv (g : G) (H : Subgroup G) :
    conjInvariants R H ≃ₐ[R] conjInvariants R (MulAut.conj g • H) :=
  ((MonoidAlgebra.domCongrAut (MulAut.conj g)).subalgebraMap _).trans
    (Subalgebra.equivOfEq _ _ (map_conjInvariants g H))

/-- The isomorphism `R[G]^H ≃ R[G]^{gHg⁻¹}` is conjugation by `g`. -/
@[simp]
theorem coe_conjInvariantsEquiv (g : G) (H : Subgroup G) (x : conjInvariants R H) :
    (conjInvariantsEquiv R g H x : MonoidAlgebra R G) = conjRepresentation R G g x := by
  rw [conjInvariantsEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    AlgEquiv.subalgebraMap_apply_coe, domCongrAut_conj_apply]

/-- The inverse of `R[G]^H ≃ R[G]^{gHg⁻¹}` is conjugation by `g⁻¹`. -/
@[simp]
theorem coe_conjInvariantsEquiv_symm (g : G) (H : Subgroup G)
    (y : conjInvariants R (MulAut.conj g • H)) :
    ((conjInvariantsEquiv R g H).symm y : MonoidAlgebra R G) = conjRepresentation R G g⁻¹ y := by
  obtain ⟨x, rfl⟩ := (conjInvariantsEquiv R g H).surjective y
  rw [AlgEquiv.symm_apply_apply, coe_conjInvariantsEquiv, Representation.inv_self_apply]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex Fintype.ofFinite

/-- **Conjugation of relative traces.** `g Tr_Q^P(a) g⁻¹ = Tr_{gQg⁻¹}^{gPg⁻¹}(g a g⁻¹)` (Webb,
Lemma 11.3.1, p. 194). -/
theorem conjInvariantsEquiv_relTrace (g : G) {Q P : Subgroup G} [(Q.subgroupOf P).FiniteIndex]
    (a : conjInvariants R Q) :
    conjInvariantsEquiv R g P (relTrace R Q P a) =
      relTrace R (MulAut.conj g • Q) (MulAut.conj g • P) (conjInvariantsEquiv R g Q a) := by
  let e : P ≃* (MulAut.conj g • P : Subgroup G) := Subgroup.equivSMul (MulAut.conj g) P
  have he : ∀ x : P, e x ∈ (MulAut.conj g • Q).subgroupOf (MulAut.conj g • P) ↔
      x ∈ Q.subgroupOf P := fun x => by
    simp [e, Subgroup.mem_subgroupOf, mul_assoc]
  ext1
  rw [coe_conjInvariantsEquiv, coe_relTrace, map_sum,
    relTrace_apply_eq_sum_of_bijective _ (Subgroup.mk_mulEquiv_out_bijective e he)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coe_conjInvariantsEquiv, conjRepresentation_conjRepresentation,
    conjRepresentation_conjRepresentation]
  congr 2
  simp [e, MulAut.smul_def, MulAut.conj_apply]

/-- The relative trace into `P` depends on `P` only through its value: for `P = P'`, `Tr_Q^P` and
`Tr_Q^{P'}` agree in `R[G]`. -/
theorem coe_relTrace_of_eq {Q P P' : Subgroup G} (h : P = P') [(Q.subgroupOf P).FiniteIndex]
    [(Q.subgroupOf P').FiniteIndex] (a : conjInvariants R Q) :
    (relTrace R Q P a : MonoidAlgebra R G) = relTrace R Q P' a := by
  subst h
  rfl

/-- **Traces from conjugate subgroups.** A central element that is a trace from `P` is a trace
from every conjugate `gPg⁻¹`, since `g Tr_P^G(a) g⁻¹ = Tr_{gPg⁻¹}^G(g a g⁻¹)`. Applied to `g⁻¹`,
this gives the converse. -/
theorem mem_relTraceIdeal_conj [Finite G] {P : Subgroup G}
    {x : conjInvariants R (⊤ : Subgroup G)} (hx : x ∈ relTraceIdeal R (le_top : P ≤ ⊤)) (g : G) :
    x ∈ relTraceIdeal R (le_top : MulAut.conj g • P ≤ ⊤) := by
  obtain ⟨a, rfl⟩ := (mem_relTraceIdeal_iff _).1 hx
  refine (mem_relTraceIdeal_iff _).2 ⟨conjInvariantsEquiv R g P a, Subtype.ext ?_⟩
  have h := congrArg Subtype.val (conjInvariantsEquiv_relTrace (R := R) g (P := ⊤) a)
  rw [coe_conjInvariantsEquiv,
    mem_conjInvariants_iff.1 (relTrace R P ⊤ a).property g (Subgroup.mem_top g)] at h
  rw [h, coe_relTrace_of_eq (Subgroup.conj_smul_eq_self_of_mem (Subgroup.mem_top g))]

/-- **The Mackey formula for relative traces.** For `T ≤ P`, any subgroup `Q` with `Q ∩ P` of
finite index in `P`, and elements `xᵢ ∈ P` representing each double coset `T x Q` in `P` exactly
once, `Tr_Q^P(a) = ∑ᵢ Tr_{T ∩ xᵢQxᵢ⁻¹}^T(xᵢ a xᵢ⁻¹)` in `R[G]^T` (Webb, Lemma 11.3.1, p. 194). Here
`Tr_{xQx⁻¹}^T` is the relative trace from `T ∩ xQx⁻¹`, applied to the `xQx⁻¹`-fixed element
`x a x⁻¹`; `T ∩ xQx⁻¹` has finite index in `T` by `Subgroup.finiteIndex_conj_smul_subgroupOf`. -/
theorem inclusion_relTrace_eq_sum_relTrace_conj {T Q P : Subgroup G}
    [(Q.subgroupOf P).FiniteIndex] (hTP : T ≤ P) {ι : Type*} [Fintype ι] (x : ι → P)
    (hx : ∀ y ∈ P, ∃! i, y ∈ DoubleCoset.doubleCoset (x i : G) T Q) (a : conjInvariants R Q) :
    Subalgebra.inclusion (conjInvariants_anti hTP) (relTrace R Q P a) =
      ∑ i, haveI := Subgroup.finiteIndex_conj_smul_subgroupOf Q hTP (x i).property
        relTrace R (MulAut.conj (x i : G) • Q) T (conjInvariantsEquiv R (x i : G) Q a) := by
  have := fun i => Subgroup.finiteIndex_conj_smul_subgroupOf Q hTP (x i).property
  ext1
  rw [Subalgebra.coe_inclusion, relTrace_apply_eq_sum_of_bijective _
    (Subgroup.bijective_sigma_quotient_mul_of_existsUnique_doubleCoset hTP x hx),
    Fintype.sum_sigma]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_relTrace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_conjInvariantsEquiv, conjRepresentation_conjRepresentation]

/-- **The Mackey formula over the double cosets.** For `T ≤ P` and any subgroup `Q` with `Q ∩ P`
of finite index in `P`, `Tr_Q^P(a) = ∑_{TxQ ⊆ P} Tr_{T ∩ xQx⁻¹}^T(x a x⁻¹)` in `R[G]^T`, summed
over the double cosets `T \ P / Q`, finite by `TauCeti.finite_doubleCosetQuotient`, with their
chosen representatives `x` (Webb, Lemma 11.3.1, p. 194). -/
theorem inclusion_relTrace_eq_sum_doubleCoset {T Q P : Subgroup G} [(Q.subgroupOf P).FiniteIndex]
    (hTP : T ≤ P) (a : conjInvariants R Q) :
    Subalgebra.inclusion (conjInvariants_anti hTP) (relTrace R Q P a) =
      ∑ q : DoubleCoset.Quotient (T.subgroupOf P : Set P) (Q.subgroupOf P),
        haveI := Subgroup.finiteIndex_conj_smul_subgroupOf Q hTP q.out.property
        relTrace R (MulAut.conj (q.out : G) • Q) T (conjInvariantsEquiv R (q.out : G) Q a) :=
  inclusion_relTrace_eq_sum_relTrace_conj (ι := DoubleCoset.Quotient (T.subgroupOf P : Set P)
    (Q.subgroupOf P)) hTP (fun q => Quotient.out q)
    (fun _ hy => Subgroup.existsUnique_mem_doubleCoset_out hTP hy) a

end Conj

section OrbitSum

variable {R G : Type*} [CommSemiring R] [Group G]

/-- `g` is fixed by conjugation by its stabilizer. -/
theorem single_mem_conjInvariants_inf_centralizer (P : Subgroup G) (g : G) (r : R) :
    single g r ∈ conjInvariants R (P ⊓ Subgroup.centralizer {g}) := by
  rw [mem_conjInvariants_iff]
  intro h hh
  rw [conjRepresentation_single, (Subgroup.mem_centralizer_singleton_iff.1 hh.2).eq,
    mul_inv_cancel_right]

open scoped Classical in
/-- **Orbit sums are relative traces.** The relative trace of `g` from its stabilizer
`P ⊓ C_G(g)` to `P` has coefficient `r` on each `P`-conjugate of `g`, and `0` elsewhere. -/
theorem coeff_relTrace_single_inf_centralizer [Finite G] (P : Subgroup G) (g : G) (r : R)
    (h : G) :
    (relTrace R (P ⊓ Subgroup.centralizer {g}) P
        ⟨single g r, single_mem_conjInvariants_inf_centralizer P g r⟩ : MonoidAlgebra R G).coeff h =
      if ∃ q ∈ P, q * g * q⁻¹ = h then r else 0 := by
  classical
  -- `P` acts on `G` by conjugation through its image `K` in `ConjAct G`.
  let K := P.map (ConjAct.toConjAct (G := G)).toMonoidHom
  let φ : P ≃* K := P.equivMapOfInjective _ ConjAct.toConjAct.injective
  have hsmul (q : P) (a : G) : φ q • a = q * a * (q : G)⁻¹ := ConjAct.toConjAct_smul _ _
  have hrel (a b : P) : QuotientGroup.leftRel ((P ⊓ Subgroup.centralizer {g}).subgroupOf P) a b ↔
      QuotientGroup.leftRel (MulAction.stabilizer K g) (φ a) (φ b) := by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv φ, ← map_mul φ,
      MulAction.mem_stabilizer_iff, hsmul]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, SetLike.coe_mem, true_and,
      Subgroup.mem_centralizer_singleton_iff, commute_iff_eq, mul_inv_eq_iff_eq_mul]
  have := Fintype.ofFinite (MulAction.orbit K g)
  let e : MulAction.orbit K g ≃ P ⧸ (P ⊓ Subgroup.centralizer {g}).subgroupOf P :=
    ((Quotient.congr φ.toEquiv hrel).trans (MulAction.orbitEquivQuotientStabilizer K g).symm).symm
  have hs (x : MulAction.orbit K g) : ((e x).out : G) * g * ((e x).out : G)⁻¹ = x := by
    have he (q : P) : (e.symm q : G) = φ q • g := by
      simp only [e, Equiv.symm_symm, Equiv.trans_apply]
      -- `Quotient.congr` sends the class of `q` to the class of `φ q` (`Quotient.congr_mk`).
      exact MulAction.orbitEquivQuotientStabilizer_symm_apply (G := K) g (φ q)
    rw [← hsmul, ← he, QuotientGroup.out_eq', e.symm_apply_apply]
  have hbij : Function.Bijective
      fun x => ((e x).out : P ⧸ (P ⊓ Subgroup.centralizer {g}).subgroupOf P) := by
    simpa only [QuotientGroup.out_eq'] using e.bijective
  have horbit : h ∈ MulAction.orbit K g ↔ ∃ q ∈ P, q * g * q⁻¹ = h := by
    rw [MulAction.mem_orbit_iff, φ.surjective.exists]
    simp only [hsmul, Subtype.exists, exists_prop]
  rw [relTrace_apply_eq_sum_of_bijective _ hbij, coeff_sum]
  simp only [Finsupp.finsetSum_apply, conjRepresentation_single, hs, coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_set_coe (f := fun x => if x = h then r else 0), Finset.sum_ite_eq']
  simp only [Set.mem_toFinset, horbit]

end OrbitSum

section Index

variable {R G : Type*} [CommSemiring R] [Group G] {H P L : Subgroup G}
  [(H.subgroupOf P).FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Traces from subgroups of invertible index.** If `r |P : H| = 1` in `R`, then
`Tr_H^P(r b) = b` for every `b ∈ R[G]^P`. -/
theorem relTrace_inclusion_smul_of_mul_index_eq_one (hHP : H ≤ P) {r : R}
    (hr : r * (H.subgroupOf P).index = 1) (b : conjInvariants R P) :
    relTrace R H P (Subalgebra.inclusion (conjInvariants_anti hHP) (r • b)) = b := by
  rw [relTrace_inclusion hHP, ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm, hr, one_smul]

/-- If `|P : H|` is a unit of `R`, every element of `R[G]^P` is a trace from `H`. -/
theorem relTraceIdeal_eq_top_of_isUnit_index (hHP : H ≤ P)
    (hu : IsUnit ((H.subgroupOf P).index : R)) : relTraceIdeal R hHP = ⊤ := by
  obtain ⟨u, hu⟩ := hu
  refine eq_top_iff.2 fun b _ => (mem_relTraceIdeal_iff hHP).2
    ⟨_, relTrace_inclusion_smul_of_mul_index_eq_one hHP (r := ((u⁻¹ : Rˣ) : R))
      (by rw [← hu, Units.inv_mul]) b⟩

/-- If `|P : H|` is a unit of `R`, then `Tr_H^L(R[G]^H) = Tr_P^L(R[G]^P)` for `H ≤ P ≤ L`. -/
theorem relTraceIdeal_eq_of_isUnit_index (hHP : H ≤ P) (hPL : P ≤ L)
    [(P.subgroupOf L).FiniteIndex] [(H.subgroupOf L).FiniteIndex]
    (hu : IsUnit ((H.subgroupOf P).index : R)) :
    relTraceIdeal R (hHP.trans hPL) = relTraceIdeal R hPL := by
  refine le_antisymm (relTraceIdeal_mono hPL hHP) ?_
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_relTraceIdeal_iff hPL).1 hx
  obtain ⟨b, rfl⟩ := (mem_relTraceIdeal_iff hHP (x := a)).1
    (by rw [relTraceIdeal_eq_top_of_isUnit_index hHP hu]; trivial)
  exact (mem_relTraceIdeal_iff _).2 ⟨b, (relTrace_relTrace hHP hPL b).symm⟩

/-- In characteristic `p`, if `H ≤ P` is a Sylow `p`-subgroup `S` of `P`, then
`Tr_H^L(R[G]^H) = Tr_P^L(R[G]^P)` for `P ≤ L`. -/
theorem relTraceIdeal_eq_of_subgroupOf_eq_sylow {p : ℕ} [Fact p.Prime] [CharP R p]
    (hHP : H ≤ P) (hPL : P ≤ L) [(P.subgroupOf L).FiniteIndex] [(H.subgroupOf L).FiniteIndex]
    (S : Sylow p P) (hS : H.subgroupOf P = S) :
    relTraceIdeal R (hHP.trans hPL) = relTraceIdeal R hPL := by
  -- `|P : H| = |P : S|` is prime to `p`, hence a unit of `R`.
  have : (S : Subgroup P).FiniteIndex := hS ▸ inferInstance
  refine relTraceIdeal_eq_of_isUnit_index hHP hPL (isUnit_natCast_of_not_dvd Fact.out ?_)
  rw [hS]
  exact S.not_dvd_index

end Index

/-- In characteristic `p`, every element of `R[G]^G` is a trace from a Sylow `p`-subgroup `S`:
`x = Tr_S^G(|G : S|⁻¹ x)`. -/
theorem relTraceIdeal_sylow_eq_top {R G : Type*} [CommSemiring R] [Group G] {p : ℕ}
    [Fact p.Prime] [CharP R p] (S : Sylow p G) [(S : Subgroup G).FiniteIndex] :
    relTraceIdeal R (le_top : (S : Subgroup G) ≤ ⊤) = ⊤ := by
  have := relTraceIdeal_eq_of_subgroupOf_eq_sylow (R := R) (le_top : (S : Subgroup G) ≤ ⊤)
    le_rfl (S.subtype le_top) (S.coe_subtype le_top).symm
  rwa [relTraceIdeal_self] at this

end TauCeti
