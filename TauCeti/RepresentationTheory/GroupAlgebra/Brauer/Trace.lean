/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Projection
public import TauCeti.GroupTheory.PGroup.FixedPointSum

/-!
# The Brauer projection of a relative trace

Let `P` be a `p`-subgroup of a finite group `G`, `R` a commutative semiring of characteristic `p`
and `P ≤ H ≤ G`. For `a ∈ R[G]^P`, the Brauer projection of the relative trace `Tr_P^H(a)` only
sees the part of the trace over the normalizer:
`Br_P(Tr_P^H(a)) = Br_P(Tr_P^{N_H(P)}(a))`, where `N_H(P) = H ∩ N_G(P)`
(`TauCeti.brauerProjection_relTrace_eq_normalizer`). For `H = G` this is the step of Brauer's first
main theorem that compares traces in `R[G]` and in `R[N_G(P)]`.

The proof is a fixed-point count. The coefficient of `Tr_P^H(a)` at `c ∈ C_G(P)` is
`∑_{hP ∈ H/P} a(h⁻¹ c h)`. Since `c` centralizes `P`, the summand is constant on the orbits of `P`
acting on `H/P` by left multiplication, so in characteristic `p` the sum is the sum over the fixed
points (`IsPGroup.sum_eq_sum_fixedPoints`). A coset `hP` is fixed by `P` exactly when
`h⁻¹ P h ⊆ P`, that is, since `P` is finite, when `h` normalizes `P`; so the fixed points are the
cosets `N_H(P)/P`, and the sum is the coefficient of `Tr_P^{N_H(P)}(a)` at `c`.

## Main results

* `TauCeti.forall_inclusion_mul_eq_iff_mem_normalizer`: the cosets in `H/P` fixed by `P` are
  those of `N_H(P)`.
* `TauCeti.brauerProjection_relTrace_eq_normalizer`: `Br_P(Tr_P^H(a)) = Br_P(Tr_P^{N_H(P)}(a))`.
* `TauCeti.brauerProjection_relTrace_top_eq_normalizer`: the case `H = G`.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Group G]

variable [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P H : Subgroup G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [Fact p.Prime] in
/-- **The cosets fixed by `P`.** For `P ≤ H` in a finite group, the coset `hP ∈ H/P` is fixed by
left multiplication by `P` exactly when `h` normalizes `P`. -/
theorem forall_inclusion_mul_eq_iff_mem_normalizer (hPH : P ≤ H) (h : H) :
    (∀ u : P, ((Subgroup.inclusion hPH u * h : H) : H ⧸ P.subgroupOf H) = h) ↔
      (h : G) ∈ Subgroup.normalizer (P : Set G) := by
  have hu (u : P) : ((Subgroup.inclusion hPH u * h : H) : H ⧸ P.subgroupOf H) = h ↔
      (h : G)⁻¹ * u * h ∈ P := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, Subgroup.coe_inv, mul_inv_rev]
    rw [show (h : G)⁻¹ * (u : G)⁻¹ * h = ((h : G)⁻¹ * u * h)⁻¹ by group, P.inv_mem_iff]
  refine ⟨fun hh => inv_inv (h : G) ▸ Subgroup.inv_mem _ (Subgroup.mem_normalizer_fintype
    fun u hu' => by simpa using (hu ⟨u, hu'⟩).1 (hh ⟨u, hu'⟩)), fun hh u => (hu u).2 ?_⟩
  exact (Subgroup.mem_normalizer_iff''.1 hh u).1 u.property

/-- The coefficient of `Tr_P^H(a)` at `c ∈ C_G(P)` is that of `Tr_P^{N_H(P)}(a)`, for a
`p`-subgroup `P ≤ H` in characteristic `p`. -/
theorem coeff_relTrace_eq_normalizer_of_mem_centralizer (hP : IsPGroup p P) (hPH : P ≤ H)
    (a : conjInvariants R P) {c : G} (hc : c ∈ Subgroup.centralizer (P : Set G)) :
    (relTrace R P H a : MonoidAlgebra R G).coeff c =
      (relTrace R P (H ⊓ Subgroup.normalizer (P : Set G)) a : MonoidAlgebra R G).coeff c := by
  classical
  set N := H ⊓ Subgroup.normalizer (P : Set G)
  -- The summand `a(k⁻¹ c k)` is well defined on cosets `kP`, for `k` in any subgroup `K`.
  have hwd (K : Subgroup G) (k₁ k₂ : K) (hk : (k₁ : G)⁻¹ * k₂ ∈ P) :
      (a : MonoidAlgebra R G).coeff ((k₁ : G)⁻¹ * c * k₁) =
        (a : MonoidAlgebra R G).coeff ((k₂ : G)⁻¹ * c * k₂) := by
    have := mem_conjInvariants_iff_coeff.1 a.property _ (P.inv_mem hk) ((k₁ : G)⁻¹ * c * k₁)
    rw [← this]
    congr 1
    group
  let F (K : Subgroup G) : K ⧸ P.subgroupOf K → R :=
    Quotient.lift (fun k : K => (a : MonoidAlgebra R G).coeff ((k : G)⁻¹ * c * k))
      fun k₁ k₂ hk => hwd K k₁ k₂ (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hk))
  have hF (K : Subgroup G) (k : K) : F K (k : K ⧸ P.subgroupOf K) =
      (a : MonoidAlgebra R G).coeff ((k : G)⁻¹ * c * k) := rfl
  have hsum (K : Subgroup G) :
      (relTrace R P K a : MonoidAlgebra R G).coeff c = ∑ q, F K q := by
    rw [coe_relTrace, coeff_sum]
    simp only [Finsupp.finsetSum_apply, coeff_conjRepresentation]
    refine Finset.sum_congr rfl fun q _ => ?_
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  rw [hsum H, hsum N]
  -- `P` acts on `H/P` by left multiplication, and the summand is invariant.
  let _ : MulAction P (H ⧸ P.subgroupOf H) := MulAction.compHom _ (Subgroup.inclusion hPH)
  have hsmul (u : P) (h : H) : u • (h : H ⧸ P.subgroupOf H) =
      ((Subgroup.inclusion hPH u * h : H) : H ⧸ P.subgroupOf H) := rfl
  have hinv (u : P) (q : H ⧸ P.subgroupOf H) : F H (u • q) = F H q := by
    induction q using QuotientGroup.induction_on with
    | H h =>
      rw [hsmul, hF, hF]
      congr 1
      have hcu : (u : G)⁻¹ * c * u = c := by
        rw [mul_assoc, ← Subgroup.mem_centralizer_iff.1 hc u u.property, inv_mul_cancel_left]
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, mul_inv_rev]
      rw [show (h : G)⁻¹ * (u : G)⁻¹ * c * ((u : G) * h) = (h : G)⁻¹ * ((u : G)⁻¹ * c * u) * h by
        group, hcu]
  rw [hP.sum_eq_sum_fixedPoints (F H) hinv]
  -- The fixed cosets are those of `N_H(P)`.
  have hfix (h : H) : (h : H ⧸ P.subgroupOf H) ∈ MulAction.fixedPoints P (H ⧸ P.subgroupOf H) ↔
      (h : G) ∈ Subgroup.normalizer (P : Set G) :=
    forall_inclusion_mul_eq_iff_mem_normalizer hPH h
  let ι : N ⧸ P.subgroupOf N → H ⧸ P.subgroupOf H :=
    Quotient.map (fun n : N => (⟨n, n.property.1⟩ : H)) fun n₁ n₂ hn => by
      have := Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hn)
      exact QuotientGroup.leftRel_apply.2 (Subgroup.mem_subgroupOf.2 this)
  have hι (n : N) : ι (n : N ⧸ P.subgroupOf N) = ((⟨n, n.property.1⟩ : H) : H ⧸ P.subgroupOf H) :=
    rfl
  symm
  refine Finset.sum_bij (fun q _ => ι q) (fun q _ => ?_) (fun q₁ _ q₂ _ h => ?_) (fun q hq => ?_)
    (fun q _ => ?_)
  · induction q using QuotientGroup.induction_on with
    | H n => exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hfix _).2 n.property.2⟩
  · induction q₁ using QuotientGroup.induction_on with
    | H n₁ =>
    induction q₂ using QuotientGroup.induction_on with
    | H n₂ =>
      rw [hι, hι, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 h)
  · induction q using QuotientGroup.induction_on with
    | H h =>
      have hN := (hfix h).1 (Finset.mem_filter.1 hq).2
      exact ⟨((⟨h, h.property, hN⟩ : N) : N ⧸ P.subgroupOf N), Finset.mem_univ _, rfl⟩
  · induction q using QuotientGroup.induction_on with
    | H n => rfl

/-- **The Brauer projection of a relative trace only sees the normalizer.** For a `p`-subgroup
`P ≤ H` of a finite group `G`, `R` of characteristic `p` and `a ∈ R[G]^P`,
`Br_P(Tr_P^H(a)) = Br_P(Tr_P^{N_H(P)}(a))` with `N_H(P) = H ∩ N_G(P)`. -/
theorem brauerProjection_relTrace_eq_normalizer (hP : IsPGroup p P) (hPH : P ≤ H)
    (a : conjInvariants R P) :
    brauerProjection P (relTrace R P H a : MonoidAlgebra R G) =
      brauerProjection P
        (relTrace R P (H ⊓ Subgroup.normalizer (P : Set G)) a : MonoidAlgebra R G) := by
  ext c
  rw [coeff_brauerProjection, coeff_brauerProjection,
    coeff_relTrace_eq_normalizer_of_mem_centralizer hP hPH a c.property]

/-- **The Brauer projection of a trace from `P` to `G`.** For a `p`-subgroup `P` of a finite group
`G`, `R` of characteristic `p` and `a ∈ R[G]^P`, `Br_P(Tr_P^G(a)) = Br_P(Tr_P^{N_G(P)}(a))`. -/
theorem brauerProjection_relTrace_top_eq_normalizer (hP : IsPGroup p P)
    (a : conjInvariants R P) :
    brauerProjection P (relTrace R P ⊤ a : MonoidAlgebra R G) =
      brauerProjection P
        (relTrace R P (Subgroup.normalizer (P : Set G)) a : MonoidAlgebra R G) := by
  rw [brauerProjection_relTrace_eq_normalizer hP le_top a, coe_relTrace_of_eq (top_inf_eq _)]

end TauCeti
