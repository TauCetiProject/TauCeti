/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Projection

/-!
# The kernel of the Brauer homomorphism

Let `P` be a `p`-subgroup of a finite group `G` and `R` a commutative semiring of characteristic
`p`. The Brauer homomorphism `Br_P : R[G]^P → R[C_G(P)]` (`TauCeti.brauerHom`) keeps the
coefficients on the centralizer `C_G(P)`. Its kernel is the sum of the relative trace ideals
`R[G]^P_Q = Tr_Q^P(R[G]^Q)` over the proper subgroups `Q < P` (`TauCeti.ker_brauerHom`; Webb,
Lemma 12.5.3).

Both inclusions are coefficient computations. The coefficient of `Tr_Q^P(a)` at `c ∈ C_G(P)` is
`|P : Q|` times that of `a`, which vanishes in characteristic `p` when `Q < P`. Conversely, an
element `x ∈ R[G]^P` has coefficients constant on the `P`-conjugacy orbits of `G`. For `g` in its
support, outside `C_G(P)` when `Br_P(x) = 0`, the orbit sum of `g` is the relative trace of `g`
from its stabilizer `Q = P ⊓ C_G(g) < P` (`TauCeti.coeff_relTrace_single_inf_centralizer`), so
`x` is `x_g` times that trace plus an element of `R[G]^P` whose support misses the orbit of `g`,
and induction on the support writes `x` as a sum of such traces. This direction uses neither the
characteristic nor that `P` is a `p`-group.

## Main results

* `TauCeti.brauerProjection_relTrace_eq_zero`: `Br_P` kills `Tr_Q^P(a)` for `Q < P`.
* `TauCeti.ker_brauerHom`: `ker Br_P = ∑_{Q < P} R[G]^P_Q`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Lemma 12.5.3, p. 245.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Group G]

/-! ### Traces from proper subgroups lie in the kernel -/

/-- **The Brauer projection kills traces from proper subgroups.** For a `p`-subgroup `P` in
characteristic `p` and `Q < P`, `Br_P(Tr_Q^P(a)) = 0`, since `|P : Q|` is a positive power of
`p`. -/
theorem brauerProjection_relTrace_eq_zero {p : ℕ} [Fact p.Prime] [CharP R p] {Q P : Subgroup G}
    [(Q.subgroupOf P).FiniteIndex] (hP : IsPGroup p P) (hQP : Q < P) (a : conjInvariants R Q) :
    brauerProjection P (relTrace R Q P a : MonoidAlgebra R G) = 0 := by
  obtain ⟨n, hn⟩ := hP.index (Q.subgroupOf P)
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hn
    exact hQP.not_ge hn
  have hp : ((Q.subgroupOf P).index : R) = 0 := by
    rw [hn, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn0]
  ext c
  rw [coeff_brauerProjection, coeff_relTrace_of_mem_centralizer a c.property, nsmul_eq_mul, hp,
    zero_mul, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

/-! ### The kernel -/

open scoped Classical in
/-- An element `x` of `R[G]^P` is the relative trace of `x_g g` from the stabilizer of `g`, plus
an element of `R[G]^P` with the coefficients of `x` on the `P`-orbit of `g` removed. -/
private theorem exists_eq_relTrace_add [Finite G] {P : Subgroup G} (x : conjInvariants R P)
    (g : G) : ∃ x' : conjInvariants R P,
      x = relTrace R (P ⊓ Subgroup.centralizer {g}) P ⟨single g ((x : MonoidAlgebra R G).coeff g),
        single_mem_conjInvariants_inf_centralizer P g _⟩ + x' ∧
      ∀ h, (x' : MonoidAlgebra R G).coeff h =
        if ∃ q ∈ P, q * g * q⁻¹ = h then 0 else (x : MonoidAlgebra R G).coeff h := by
  have hinv := mem_conjInvariants_iff_coeff.1 x.property
  set orb : G → Prop := fun h => ∃ q ∈ P, q * g * q⁻¹ = h
  have horb (q : G) (hq : q ∈ P) (h : G) : orb (q * h * q⁻¹) ↔ orb h := by
    refine ⟨fun ⟨q', hq', e⟩ => ⟨q⁻¹ * q', P.mul_mem (P.inv_mem hq) hq', ?_⟩,
      fun ⟨q', hq', e⟩ => ⟨q * q', P.mul_mem hq hq', ?_⟩⟩
    · rw [show h = q⁻¹ * (q * h * q⁻¹) * q by group, ← e]
      group
    · rw [← e]
      group
  set x' : MonoidAlgebra R G := ofCoeff ((x : MonoidAlgebra R G).coeff.filter fun h => ¬ orb h)
  have hx'coeff (h : G) : x'.coeff h = if orb h then 0 else (x : MonoidAlgebra R G).coeff h := by
    rw [coeff_ofCoeff, Finsupp.filter_apply]
    split_ifs <;> rfl
  have hx'mem : x' ∈ conjInvariants R P := by
    rw [mem_conjInvariants_iff_coeff]
    intro q hq h
    rw [hx'coeff, hx'coeff]
    simp only [horb q hq, hinv q hq]
  refine ⟨⟨x', hx'mem⟩, ?_, hx'coeff⟩
  ext1
  ext h
  rw [Subalgebra.coe_add, coeff_add, Finsupp.add_apply, coeff_relTrace_single_inf_centralizer,
    Subtype.coe_mk, hx'coeff]
  by_cases ho : ∃ q ∈ P, q * g * q⁻¹ = h
  · obtain ⟨q, hq, rfl⟩ := ho
    simp only [orb, show ∃ q' ∈ P, q' * g * q'⁻¹ = q * g * q⁻¹ from ⟨q, hq, rfl⟩, ite_true,
      add_zero, hinv q hq]
  · simp only [orb, ho, ite_false, zero_add]

/-- **Elements with vanishing Brauer projection are sums of traces from proper subgroups.** An
element of `R[G]^P` whose coefficients on `C_G(P)` vanish lies in `∑_{Q < P} R[G]^P_Q`. This
holds over any commutative semiring and for any subgroup `P` of a finite group. -/
theorem mem_iSup_relTraceIdeal_of_brauerProjection_eq_zero [Finite G] {P : Subgroup G}
    (x : conjInvariants R P) (hx : brauerProjection P (x : MonoidAlgebra R G) = 0) :
    x ∈ ⨆ (Q : Subgroup G) (hQ : Q < P), relTraceIdeal R hQ.le := by
  classical
  induction hn : (x : MonoidAlgebra R G).coeff.support.card using Nat.strong_induction_on
    generalizing x with | _ n ih =>
  have hxc (c : Subgroup.centralizer (P : Set G)) : (x : MonoidAlgebra R G).coeff c = 0 := by
    simpa using congrArg (fun y => y.coeff c) hx
  by_cases hx0 : (x : MonoidAlgebra R G) = 0
  · rw [show x = 0 from Subtype.ext hx0]
    exact zero_mem _
  obtain ⟨g, hg⟩ : (x : MonoidAlgebra R G).coeff.support.Nonempty := by
    rwa [Finsupp.support_nonempty_iff, ne_eq, coeff_eq_zero]
  -- `g` is outside `C_G(P)`, where the coefficients of `x` vanish, so its stabilizer is proper.
  have hQ : P ⊓ Subgroup.centralizer {g} < P := by
    refine lt_of_le_of_ne inf_le_left fun e => Finsupp.mem_support_iff.1 hg (hxc ⟨g, ?_⟩)
    refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
    have hq' : q ∈ P ⊓ Subgroup.centralizer {g} := by rw [e]; exact hq
    exact (Subgroup.mem_centralizer_singleton_iff.1 hq'.2).eq
  obtain ⟨x', hsplit, hx'⟩ := exists_eq_relTrace_add x g
  have hBr : brauerProjection P (x' : MonoidAlgebra R G) = 0 := by
    ext c
    simp only [coeff_brauerProjection, hx', hxc c, ite_self, coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
  have hcard : (x' : MonoidAlgebra R G).coeff.support.card < n := by
    rw [← hn]
    refine Finset.card_lt_card ⟨fun h hh => ?_, fun hsub => ?_⟩
    · rw [Finsupp.mem_support_iff, hx'] at hh
      rw [Finsupp.mem_support_iff]
      split_ifs at hh
      · exact absurd rfl hh
      · exact hh
    · have := hsub hg
      rw [Finsupp.mem_support_iff, hx'] at this
      simp only [show ∃ q ∈ P, q * g * q⁻¹ = g from ⟨1, P.one_mem, by group⟩, ite_true] at this
      exact this rfl
  rw [hsplit]
  exact add_mem (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hQ
    (relTrace_mem_relTraceIdeal hQ.le _))) (ih _ hcard x' hBr rfl)

/-- **The kernel of the Brauer homomorphism** (Webb, Lemma 12.5.3). For a `p`-subgroup `P` of a
finite group `G` in characteristic `p`, the kernel of `Br_P : R[G]^P → R[C_G(P)]` is the sum of
the relative trace ideals `R[G]^P_Q` over the proper subgroups `Q < P`. -/
theorem ker_brauerHom [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {P : Subgroup G}
    (hP : IsPGroup p P) :
    RingHom.ker (brauerHom (R := R) hP) =
      ⨆ (Q : Subgroup G) (hQ : Q < P), relTraceIdeal R hQ.le := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun Q => iSup_le fun hQ => ?_)
  · rw [RingHom.mem_ker, brauerHom_apply] at hx
    exact mem_iSup_relTraceIdeal_of_brauerProjection_eq_zero x hx
  · intro y hy
    obtain ⟨a, rfl⟩ := (mem_relTraceIdeal_iff hQ.le).1 hy
    rw [RingHom.mem_ker, brauerHom_apply]
    exact brauerProjection_relTrace_eq_zero hP hQ a

end TauCeti
