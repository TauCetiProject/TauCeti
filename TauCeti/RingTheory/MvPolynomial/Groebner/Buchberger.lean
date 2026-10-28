/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic

/-!
# Buchberger's criterion

Let `m` be a monomial order on `σ →₀ ℕ` and let `G` be a set of multivariate polynomials whose
nonzero members have unit leading coefficients, for instance any set of polynomials over a field.
Buchberger's criterion says that `G` is a Gröbner basis of the ideal it generates if and only if
`0` is a remainder of every S-polynomial `m.sPolynomial g₁ g₂` with `g₁, g₂ ∈ G` on division by `G`.
This turns the infinitely many conditions in the definition of a Gröbner basis into finitely many
checks when `G` is finite, and is the key step in the correctness of Buchberger's algorithm.

## Main results

* `MonomialOrder.IsGroebnerBasis.isRemainder_sPolynomial_zero`: the S-polynomials of a Gröbner
  basis have remainder `0`.
* `MonomialOrder.isGroebnerBasis_span_of_isRemainder_sPolynomial_zero`: **Buchberger's criterion**,
  if every S-polynomial of `G` has remainder `0` on division by `G`, then `G` is a Gröbner basis of
  `Ideal.span G`.
* `MonomialOrder.isGroebnerBasis_span_iff_isRemainder_sPolynomial_zero` and
  `MonomialOrder.isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero`: the resulting
  characterizations of Gröbner bases.

## Implementation notes

A remainder `0` of `f` on division by `G` is a *standard representation* `f = ∑ q_b * b` with
every `q_b * b` of degree at most that of `f`. The proof works with the `R`-span of the products
`X^a * b`, `b ∈ G`, whose degree `a + deg b` lies below a bound `d`. Products of degree exactly
`d` with `b ≠ 0` differ, after normalizing their leading coefficients, by monomial multiples of
S-polynomials, and these have representations of degree `< d` by hypothesis. So a representation
of degree at most `d` of a polynomial whose coefficient at `d` vanishes can be replaced by one of
degree `< d`, and well-founded induction on `d` shows that every element of `Ideal.span G` has a
standard representation. Its leading monomial is then divisible by the leading monomial of an
element of `G`.

The theorems hold over any commutative ring, assuming only that the nonzero members of `G` have
unit leading coefficients; over a field this is `MonomialOrder.isUnit_leadingCoeff`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Theorem 6
  (Buchberger's criterion) and Lemma 5 (cancellation of leading terms by S-polynomials).
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} {m : MonomialOrder σ} [CommRing R] {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

variable (m) in
/-- The `R`-span of the products `X^a * b` with `b ∈ G` whose degree `a + deg b`, read in `m.syn`,
lies in `s`. For `s = Set.Iic d` it consists of the polynomials having a representation
`∑ q_b * b` by `G` with `deg q_b + deg b ≤ d` for every `b`. -/
private noncomputable def degreeSpan (G : Set (MvPolynomial σ R)) (s : Set m.syn) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {p | ∃ b ∈ G, ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ p = monomial a 1 * b}

private theorem monomial_one_mul_mem_degreeSpan {s : Set m.syn} {b : MvPolynomial σ R}
    (hb : b ∈ G) {a : σ →₀ ℕ} (has : m.toSyn (a + m.degree b) ∈ s) :
    monomial a 1 * b ∈ degreeSpan m G s :=
  Submodule.subset_span ⟨b, hb, a, has, rfl⟩

private theorem degreeSpan_mono {s t : Set m.syn} (hst : s ⊆ t) :
    degreeSpan m G s ≤ degreeSpan m G t :=
  Submodule.span_mono fun _ ⟨b, hb, a, has, hp⟩ ↦ ⟨b, hb, a, hst has, hp⟩

private theorem mem_degreeSpan_self {b : MvPolynomial σ R} (hb : b ∈ G) :
    b ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree b))) := by
  simpa using monomial_one_mul_mem_degreeSpan (s := Set.Iic _) hb (a := 0) (by simp)

private theorem monomial_mul_mem_degreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ degreeSpan m G (Set.Iic d)) (c : σ →₀ ℕ) (r : R) :
    monomial c r * p ∈ degreeSpan m G (Set.Iic (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have hcab : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      rw [smul_eq_C_mul, ← mul_assoc, ← mul_assoc, C_mul_monomial, monomial_mul_monomial]
    rw [hcab]
    refine Submodule.smul_mem _ _ (monomial_one_mul_mem_degreeSpan hb ?_)
    rw [Set.mem_Iic, add_assoc, map_add]
    gcongr
    exact had
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

private theorem mul_mem_degreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ degreeSpan m G (Set.Iic d)) (q : MvPolynomial σ R) :
    q * p ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree q) + d)) := by
  have hq : q * p = ∑ c ∈ q.support, monomial c (q.coeff c) * p := by
    rw [← Finset.sum_mul, ← q.as_sum]
  rw [hq]
  refine Submodule.sum_mem _ fun c hc ↦ degreeSpan_mono ?_ (monomial_mul_mem_degreeSpan hp c _)
  exact Set.Iic_subset_Iic.2 (by gcongr; exact m.le_degree hc)

/-- A polynomial with remainder `0` on division by `G` has a representation by `G` of degree at
most its own degree. -/
private theorem IsRemainder.mem_degreeSpan {f : MvPolynomial σ R} (h : m.IsRemainder f G 0) :
    f ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree f))) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  generalize hV : degreeSpan m G (Set.Iic (m.toSyn (m.degree f))) = V
  rw [hfg, add_zero, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun b _ ↦ ?_
  rcases eq_or_ne (g b) 0 with hg | hg
  · simp [hg]
  rcases eq_or_ne (b : MvPolynomial σ R) 0 with hb | hb
  · simp [hb]
  rw [smul_eq_mul, ← hV]
  refine degreeSpan_mono (Set.Iic_subset_Iic.2 ?_) (mul_mem_degreeSpan (mem_degreeSpan_self b.2) _)
  rw [add_comm]
  exact (toWithBotSyn_withBotDegree_add_le_iff hb hg hf).1 (hdeg b)

/-- Every element of `Ideal.span G` has a representation by `G` of some bounded degree. -/
private theorem exists_mem_degreeSpan_of_mem_span {f : MvPolynomial σ R}
    (hf : f ∈ Ideal.span G) : ∃ d, f ∈ degreeSpan m G (Set.Iic d) := by
  induction hf using Submodule.span_induction with
  | mem b hb => exact ⟨_, mem_degreeSpan_self hb⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hx⟩ := hx
    obtain ⟨d₂, hy⟩ := hy
    exact ⟨d₁ ⊔ d₂, add_mem (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul q x _ hx =>
    obtain ⟨d, hx⟩ := hx
    exact ⟨_, mul_mem_degreeSpan hx q⟩

/-- An element of the span of the products of degree `< d` lies in the span of the products of
degree at most some `d' < d`. -/
private theorem eq_zero_or_exists_mem_degreeSpan_Iic {d : m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ degreeSpan m G (Set.Iio d)) :
    f = 0 ∨ ∃ d' < d, f ∈ degreeSpan m G (Set.Iic d') := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    exact .inr ⟨_, had, monomial_one_mul_mem_degreeSpan hb le_rfl⟩
  | zero => exact .inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | ⟨d₁, hd₁, hx⟩
    · rwa [zero_add]
    rcases hy with rfl | ⟨d₂, hd₂, hy⟩
    · rw [add_zero]
      exact .inr ⟨d₁, hd₁, hx⟩
    exact .inr ⟨d₁ ⊔ d₂, max_lt hd₁ hd₂, add_mem
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul r x _ hx =>
    rcases hx with rfl | ⟨d', hd', hx⟩
    · exact .inl (smul_zero r)
    exact .inr ⟨d', hd', Submodule.smul_mem _ r hx⟩

private theorem toSyn_degree_monomial_one_mul_le (a : σ →₀ ℕ) (b : MvPolynomial σ R) :
    m.toSyn (m.degree (monomial a 1 * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le 1)

/-- If an element of the span of the products whose degrees lie in `s` has a nonzero coefficient
at `e`, then one of these products, with `b ≠ 0`, has degree at least `e`. -/
private theorem exists_le_of_mem_degreeSpan {s : Set m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ degreeSpan m G s) {e : σ →₀ ℕ} (he : f.coeff e ≠ 0) :
    ∃ b ∈ G, b ≠ 0 ∧ ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ m.toSyn e ≤ m.toSyn (a + m.degree b) := by
  by_contra! H
  have hle : degreeSpan m G s ≤ LinearMap.ker (lcoeff R e) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, has, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simpa using m.coeff_eq_zero_of_lt
      ((toSyn_degree_monomial_one_mul_le a b).trans_lt (H b hb hb0 a has))
  exact he (by simpa using hle hf)

/-- The products of exact degree `D` with `b ≠ 0`, normalized to leading coefficient one, differ
by monomial multiples of S-polynomials: the difference between `X^a * b` and `lc b` times the
normalized product `X^(D - deg b₀) * b₀ / lc b₀` is `X^(D - L) / lc b₀ * S(b, b₀)`, where
`L = deg b ⊔ deg b₀`. -/
private theorem monomial_one_mul_sub_smul_eq {a : σ →₀ ℕ} {b b₀ : MvPolynomial σ R}
    (hb₀ : m.degree b₀ ≤ a + m.degree b) (u₀ : Rˣ) (hu₀ : (u₀ : R) = m.leadingCoeff b₀) :
    monomial a 1 * b -
        m.leadingCoeff b • (monomial (a + m.degree b - m.degree b₀) ((u₀⁻¹ : Rˣ) : R) * b₀) =
      monomial (a + m.degree b - m.degree b ⊔ m.degree b₀) ((u₀⁻¹ : Rˣ) : R) *
        m.sPolynomial b b₀ := by
  have hL : m.degree b ⊔ m.degree b₀ ≤ a + m.degree b := sup_le le_add_self hb₀
  have e₁ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b) =
      a := by
    rw [tsub_add_tsub_cancel hL le_sup_left, add_tsub_cancel_right]
  rw [sPolynomial_def, mul_sub, ← mul_assoc, ← mul_assoc, monomial_mul_monomial,
    monomial_mul_monomial, e₁, tsub_add_tsub_cancel hL le_sup_right, ← hu₀, Units.inv_mul,
    smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_comm (u₀⁻¹ : Rˣ).val]

/-- **The reduction step.** If every S-polynomial of `G` has remainder `0` on division by `G`, a
representation of degree at most `D` of a polynomial whose coefficient at `D` vanishes can be
replaced by a representation of degree `< D`. -/
private theorem mem_degreeSpan_Iio_of_coeff_eq_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) {D : σ →₀ ℕ}
    {f : MvPolynomial σ R} (hf : f ∈ degreeSpan m G (Set.Iic (m.toSyn D))) (hfD : f.coeff D = 0) :
    f ∈ degreeSpan m G (Set.Iio (m.toSyn D)) := by
  by_cases htop : ∃ b₀ ∈ G, b₀ ≠ 0 ∧ m.degree b₀ ≤ D
  swap
  · -- No product of degree exactly `D` is nonzero, so every product has degree `< D`.
    simp only [not_exists, not_and] at htop
    refine Submodule.span_le.2 ?_ hf
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    refine monomial_one_mul_mem_degreeSpan hb (lt_of_le_of_ne had fun h ↦ ?_)
    exact htop b hb hb0 (m.toSyn.injective h ▸ le_add_self)
  -- Fix a normalized product `q₀` of degree `D`. Every product `p` of degree at most `D` satisfies
  -- `p - p.coeff D • q₀ ∈ degreeSpan m G (Set.Iio D)`, and this condition is linear in `p`.
  obtain ⟨b₀, hb₀, hb₀0, hb₀D⟩ := htop
  obtain ⟨u₀, hu₀⟩ := hG b₀ hb₀ hb₀0
  set q₀ := monomial (D - m.degree b₀) (↑u₀⁻¹ : R) * b₀
  have hle : degreeSpan m G (Set.Iic (m.toSyn D)) ≤ (degreeSpan m G (Set.Iio (m.toSyn D))).comap
      (LinearMap.id - (lcoeff R D).smulRight q₀) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, lcoeff_apply]
    rcases eq_or_ne (a + m.degree b) D with rfl | hne
    · -- The difference is a monomial multiple of `S(b, b₀)`, which has a representation of
      -- degree `deg S(b, b₀) < deg b ⊔ deg b₀`.
      rw [coeff_monomial_mul, one_mul, ← leadingCoeff, monomial_one_mul_sub_smul_eq hb₀D u₀ hu₀]
      set L := m.degree b ⊔ m.degree b₀
      rcases eq_or_ne (m.sPolynomial b b₀) 0 with hS0 | hS0
      · simp [hS0]
      refine degreeSpan_mono (Set.Iic_subset_Iio.2 ?_)
        (monomial_mul_mem_degreeSpan (hS b hb b₀ hb₀).mem_degreeSpan _ _)
      calc m.toSyn (a + m.degree b - L) + m.toSyn (m.degree (m.sPolynomial b b₀))
          < m.toSyn (a + m.degree b - L) + m.toSyn L := by
            gcongr; exact m.degree_sPolynomial_lt_sup_degree hS0
        _ = m.toSyn (a + m.degree b) := by
            rw [← map_add, tsub_add_cancel_of_le (sup_le le_add_self hb₀D)]
    · -- The product has degree `< D`, so its coefficient at `D` vanishes.
      have hlt : m.toSyn (a + m.degree b) < m.toSyn D :=
        lt_of_le_of_ne had (m.toSyn.injective.ne hne)
      rw [m.coeff_eq_zero_of_lt ((toSyn_degree_monomial_one_mul_le a b).trans_lt hlt), zero_smul,
        sub_zero]
      exact monomial_one_mul_mem_degreeSpan hb hlt
  simpa [hfD] using hle hf

/-- If every S-polynomial of `G` has remainder `0` on division by `G`, then every polynomial with a
representation by `G` of degree at most `d` has a representation of degree at most its own
degree, so its leading monomial is divisible by the leading monomial of a nonzero element of
`G`. -/
private theorem exists_degree_le_degree_of_mem_degreeSpan
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) (d : m.syn)
    {f : MvPolynomial σ R} (hf : f ∈ degreeSpan m G (Set.Iic d)) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  induction d using WellFoundedLT.induction generalizing f with
  | ind d ih =>
  obtain ⟨b, hb, hb0, a, had, hfa⟩ :=
    exists_le_of_mem_degreeSpan hf (m.coeff_degree_ne_zero_iff.2 hf0)
  rcases eq_or_ne (m.toSyn (m.degree f)) d with hfd | hfd
  · -- A product of degree exactly `deg f` occurs, so `deg b ≤ deg f`.
    have : a + m.degree b = m.degree f := m.toSyn.injective (le_antisymm (hfd ▸ had) hfa)
    exact ⟨b, hb, hb0, this ▸ le_add_self⟩
  · -- Otherwise `deg f < d`, and the representation can be improved.
    have hlt : m.toSyn (m.degree f) < d := lt_of_le_of_ne (hfa.trans had) hfd
    obtain ⟨D, rfl⟩ := m.toSyn.surjective d
    have hfD := mem_degreeSpan_Iio_of_coeff_eq_zero hG hS hf (m.coeff_eq_zero_of_lt hlt)
    obtain hf' | ⟨d', hd', hf'⟩ := eq_zero_or_exists_mem_degreeSpan_Iic hfD
    · exact absurd hf' hf0
    exact ih d' hd' hf' hf0

/-- The S-polynomials of two members of a Gröbner basis whose nonzero members have unit leading
coefficients have remainder `0` on division by that basis. -/
theorem IsGroebnerBasis.isRemainder_sPolynomial_zero (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) {g₁ g₂ : MvPolynomial σ R} (hg₁ : g₁ ∈ G)
    (hg₂ : g₂ ∈ G) : m.IsRemainder (m.sPolynomial g₁ g₂) G 0 :=
  (h.isRemainder_zero_iff_mem hG).2 (sPolynomial_mem_ideal (h.subset hg₁) (h.subset hg₂))

/-- **Buchberger's criterion.** If the nonzero members of `G` have unit leading coefficients and
the S-polynomial of any two members of `G` has remainder `0` on division by `G`, then `G` is a
Gröbner basis of the ideal it generates. -/
theorem isGroebnerBasis_span_of_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) :
    m.IsGroebnerBasis G (Ideal.span G) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨Ideal.subset_span, fun f hf hf0 ↦ ?_⟩
  obtain ⟨d, hfd⟩ := exists_mem_degreeSpan_of_mem_span (m := m) hf
  exact exists_degree_le_degree_of_mem_degreeSpan hG hS d hfd hf0

/-- **Buchberger's criterion.** A set `G` whose nonzero members have unit leading coefficients is a
Gröbner basis of `I` if and only if it generates `I` and the S-polynomial of any two members of `G`
has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      Ideal.span G = I ∧ ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  refine ⟨fun h ↦ ⟨(h.ideal_eq_span hG).symm, fun _ hg₁ _ hg₂ ↦
    h.isRemainder_sPolynomial_zero hG hg₁ hg₂⟩, ?_⟩
  rintro ⟨rfl, hS⟩
  exact isGroebnerBasis_span_of_isRemainder_sPolynomial_zero hG hS

/-- **Buchberger's criterion.** A set `G` whose nonzero members have unit leading coefficients is a
Gröbner basis of the ideal it generates if and only if the S-polynomial of any two members of `G`
has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_span_iff_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
      ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  simpa using isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero (I := Ideal.span G) hG

end MonomialOrder
