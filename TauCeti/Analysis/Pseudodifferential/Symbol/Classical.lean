/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Analysis.Pseudodifferential.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Pseudodifferential.Symbol.HighFrequency

/-!
# Classical symbols

A *classical* (one-step polyhomogeneous) symbol of order `m` on `ℝⁿ` is a symbol `a ∈ S^m_{1,0}`
with an asymptotic expansion `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` into homogeneous terms: each `a_{m-j}`
is smooth away from `ξ = 0` and positively homogeneous of degree `m - j` in `ξ`, `χ` is a frequency
cutoff, and for every `N` the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N`.
The leading term `a_m` is the principal symbol. Differential operators with smooth coefficients
and their parametrices have classical symbols, and the principal symbol of a classical symbol is
what ellipticity, the symbol calculus and index theory are phrased in.

The homogeneous terms enter the expansion through their cut-off terms
`TauCeti.HomogeneousSymbol.cutoffSymbol χ a`, the symbols `χ(ξ) a(x, ξ)` of
`TauCeti/Analysis/Pseudodifferential/Symbol/Homogeneous.lean`. This file defines the carrier
`TauCeti.ClassicalSymbol n V W m` of classical symbols, with an actual remainder symbol
`TauCeti.ClassicalSymbol.remainder χ N` of order `m - N` after `N` terms
(`TauCeti.ClassicalSymbol.inclusion_remainder` states it as an identity of symbols of order `m`),
and proves:

* `TauCeti.ClassicalSymbol.exists_remainder`: the expansion holds for every frequency cutoff, not
  only for the one used to define the symbol;
* `TauCeti.ClassicalSymbol.term_eq_of_toSymbol_eq` and `TauCeti.ClassicalSymbol.ext`: the
  homogeneous terms are determined by the symbol, so a classical symbol is determined by its full
  symbol;
* the classical symbols of order `m` form a complex vector space, termwise;
* `TauCeti.ClassicalSymbol.principal`, the principal symbol, with
  `TauCeti.ClassicalSymbol.exists_sub_cutoffSymbol_principal`: the full symbol and its cut-off
  principal symbol differ by a symbol of order `m - 1`;
* `TauCeti.ClassicalSymbol.tendsto_rpow_neg_smul_coefficient_smul`: at a nonzero frequency the
  principal symbol is the high-frequency limit `σ(a)(x, ξ) = lim_{t → ∞} t ^ (-m) a(x, t ξ)`;
* `TauCeti.ClassicalSymbol.principal_eq_zero_iff` and
  `TauCeti.ClassicalSymbol.principal_surjective`: the principal symbol vanishes exactly on the
  classical symbols of order `m - 1`, and every homogeneous symbol of degree `m` is a principal
  symbol;
* `TauCeti.ClassicalSymbol.isSmoothing_toSymbol_iff`: a classical symbol is smoothing exactly when
  all of its homogeneous terms vanish; `TauCeti.ClassicalSymbol.ofIsSmoothing` makes every
  smoothing symbol classical;
* `TauCeti.ClassicalSymbol.termsLinearMap`: the homogeneous terms as a linear map, whose kernel
  consists of the smoothing classical symbols (`TauCeti.ClassicalSymbol.mem_ker_termsLinearMap`);
  `TauCeti.ClassicalSymbol.isSmoothing_toSymbol_sub_iff`: two classical symbols differ by a
  smoothing symbol exactly when their homogeneous terms agree;
* `TauCeti.ClassicalSymbol.ofHomogeneous`: the classical symbol `χ(ξ) a(x, ξ)` of a single
  homogeneous term, whose principal symbol is `a`;
* `TauCeti.ClassicalSymbol.ofEqHomogeneous`: a symbol that agrees with a homogeneous symbol `h` at
  all large frequencies is classical, with principal symbol `h` and no further terms; in
  particular so is a coefficient that is smooth everywhere and homogeneous away from `ξ = 0`, such
  as a homogeneous polynomial in `ξ` (`TauCeti.ClassicalSymbol.ofContDiffHomogeneous`);
* `TauCeti.ClassicalSymbol.inclusion`: a classical symbol of order `m - k`, `k ∈ ℕ`, is classical
  of order `m`, with `k` leading terms equal to zero;
* `TauCeti.ClassicalSymbol.tail`: the remainder `a - χ(ξ) a_m` after the principal term, a
  classical symbol of order `m - 1`;
* the exact sequence `0 → S^{m-1}_cl → S^m_cl → H^m → 0`: the principal symbol is surjective
  (`TauCeti.ClassicalSymbol.principal_surjective`), its kernel is the image of the classical
  symbols of order `m - 1` (`TauCeti.ClassicalSymbol.principal_eq_zero_iff_exists_inclusion`,
  `TauCeti.ClassicalSymbol.ker_principalLinearMap`), and
  `TauCeti.ClassicalSymbol.principalEquiv` identifies the quotient by them with the homogeneous
  symbols of degree `m`;
* `TauCeti.ClassicalSymbol.comp`: the pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of
  classical symbols of orders `m'` and `m` is classical of order `m' + m`, with the terms
  `cₖ = ∑_{i + j = k} bᵢ ∘ aⱼ` (`TauCeti.ClassicalSymbol.compTerms`), so the principal symbol is
  multiplicative (`TauCeti.ClassicalSymbol.principal_comp`). This is not the composition of the
  operators, whose lower order terms also involve derivatives of the symbols;
* `TauCeti.ClassicalSymbol.spatialDeriv` and `TauCeti.ClassicalSymbol.frequencyDeriv`: the
  derivatives `∂_{x_j} a` and `∂_{ξ_j} a` of a classical symbol of order `m` are classical, of
  orders `m` and `m - 1`, and their homogeneous terms are the derivatives of those of `a`. These
  are the factors `∂_ξ^α a` and `∂_x^α b` of the terms of the composition expansion
  `∑_α (1 / α!) ∂_ξ^α a D_x^α b`;
* `TauCeti.ClassicalSymbol.IsElliptic`: ellipticity, the invertibility of the principal symbol at
  every nonzero frequency; its pointwise inverse is the homogeneous symbol
  `TauCeti.HomogeneousSymbol.inverse` of degree `-m`. By
  `TauCeti.ClassicalSymbol.isElliptic_iff_forall_isCompact`, a classical symbol with a complete
  source space is elliptic exactly when, on every compact set of positions, its full symbol
  `a(x, ξ)` is invertible at all large frequencies with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. This bound is
  what the derivative estimates of the inverse symbol, and the parametrix built from it, start
  from. The radius beyond which `a(x, ξ)` is invertible depends on the compact set in general.
  Ellipticity does not see terms of order `m - 1`
  (`TauCeti.ClassicalSymbol.isElliptic_add_iff`), and the inverse of the principal symbol is the
  unique homogeneous symbol of degree `-m` inverting it at every nonzero frequency
  (`TauCeti.ClassicalSymbol.existsUnique_inversePrincipalSymbol`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5
  and Proposition 18.1.3.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17) and (4.1)–(4.6).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2, §2.9, Lemma 2.5.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

open HomogeneousSymbol

variable (n V W m) in
/-- A classical symbol of order `m` on `ℝⁿ`: a symbol `a` of order `m` together with homogeneous
terms `a_{m-j}` of degree `m - j` for `j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and
every `N`, the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N`. The expansion
then holds for every cutoff (`TauCeti.ClassicalSymbol.exists_remainder`), and the terms are
determined by the symbol (`TauCeti.ClassicalSymbol.ext`). -/
structure ClassicalSymbol where
  /-- The full symbol. -/
  toSymbol : Symbol n V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`;
  use `TauCeti.ClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : Symbol n V W (m - N), ∀ p,
      r.coefficient p =
        toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace ClassicalSymbol

section Remainder

variable (a : ClassicalSymbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol is a symbol of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      a.toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  obtain ⟨χ₀, h₀⟩ := a.exists_remainder'
  obtain ⟨r₀, hr₀⟩ := h₀ N
  -- The truncated expansions for `χ₀` and `χ` differ by `∑_{j<N} (χ₀ - χ)(ξ) a_{m-j}`, a sum of
  -- smoothing symbols.
  choose s hs using fun j =>
    Symbol.isSmoothing_iff.1 (isSmoothing_cutoffSymbol_sub_cutoffSymbol χ₀ χ (a.term j)) (m - N)
  refine ⟨r₀ + ∑ j ∈ Finset.range N, s j, fun p => ?_⟩
  simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_sum, Finset.sum_apply, hr₀,
    hs, Symbol.coefficient_sub, Pi.sub_apply, coefficient_cutoffSymbol, Finset.sum_sub_distrib]
  abel

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol after `N` terms, a symbol of
order `m - N`. -/
def remainder (N : ℕ) : Symbol n V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

/-- The remainder after `N` terms, included in the symbols of order `m`, is the full symbol minus
the first `N` cut-off terms. -/
theorem inclusion_remainder (N : ℕ) :
    Symbol.inclusion (by simp) (a.remainder χ N) =
      a.toSymbol - ∑ k ∈ Finset.range N, Symbol.inclusion (by simp) (cutoffSymbol χ (a.term k)) :=
  Symbol.ext <| funext fun p => by simp

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols with the same full symbol have
the same homogeneous terms. -/
theorem term_eq_of_toSymbol_eq {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol)
    (j : ℕ) : a.term j = b.term j := by
  obtain ⟨χ, -⟩ := a.exists_remainder'
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- Given the equality of the earlier terms, the difference of the remainders after `j + 1`
    -- terms is the cut-off term of `b_{m-j} - a_{m-j}`, of order `m - (j + 1) < m - j`.
    refine (sub_eq_zero.1 <| eq_zero_of_coefficient_eq_cutoffSymbol χ (m' := m - (j + 1 : ℕ))
      (by push_cast; linarith) (a.remainder χ (j + 1) - b.remainder χ (j + 1)) ?_).symm
    funext p
    have hsum : ∑ i ∈ Finset.range j, χ p.2 • (a.term i).coefficient p =
        ∑ i ∈ Finset.range j, χ p.2 • (b.term i).coefficient p :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.1 hi)]
    simp only [Symbol.coefficient_sub, Pi.sub_apply, coefficient_remainder,
      Finset.sum_range_succ, hsum, h, coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_sub,
      smul_sub]
    abel

/-- A classical symbol is determined by its full symbol. -/
@[ext]
theorem ext {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol) : a = b := by
  have ht : a.term = b.term := funext (term_eq_of_toSymbol_eq h)
  cases a
  cases b
  cases h
  cases ht
  rfl

theorem toSymbol_injective :
    Function.Injective (toSymbol : ClassicalSymbol n V W m → Symbol n V W m) :=
  fun _ _ => ext

end Uniqueness

/-! ### The vector space of classical symbols of order `m` -/

section Module

instance : Zero (ClassicalSymbol n V W m) where
  zero :=
    { toSymbol := 0
      term _ := 0
      exists_remainder' := ⟨default, fun _ => ⟨0, fun p => by simp⟩⟩ }

instance : Add (ClassicalSymbol n V W m) where
  add a b :=
    { toSymbol := a.toSymbol + b.toSymbol
      term j := a.term j + b.term j
      exists_remainder' := ⟨default, fun N => ⟨a.remainder default N + b.remainder default N,
        fun p => by
          simp only [Symbol.coefficient_add, Pi.add_apply, coefficient_remainder,
            HomogeneousSymbol.coefficient_add, smul_add, Finset.sum_add_distrib]
          abel⟩⟩ }

instance : SMul ℂ (ClassicalSymbol n V W m) where
  smul c a :=
    { toSymbol := c • a.toSymbol
      term j := c • a.term j
      exists_remainder' := ⟨default, fun N => ⟨c • a.remainder default N, fun p => by
        simp only [Symbol.coefficient_smul, Pi.smul_apply, coefficient_remainder,
          HomogeneousSymbol.coefficient_smul, smul_sub, Finset.smul_sum, smul_comm c]⟩⟩ }

instance : Neg (ClassicalSymbol n V W m) where
  neg a :=
    { toSymbol := -a.toSymbol
      term j := -a.term j
      exists_remainder' := ⟨default, fun N => ⟨-a.remainder default N, fun p => by
        simp only [Symbol.coefficient_neg, Pi.neg_apply, coefficient_remainder,
          HomogeneousSymbol.coefficient_neg, smul_neg, Finset.sum_neg_distrib]
        abel⟩⟩ }

instance : Sub (ClassicalSymbol n V W m) where
  sub a b := a + -b

instance : SMul ℕ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

variable (a b : ClassicalSymbol n V W m) (c : ℂ) (j : ℕ)

@[simp]
theorem toSymbol_zero : (0 : ClassicalSymbol n V W m).toSymbol = 0 := (rfl)

@[simp]
theorem toSymbol_add : (a + b).toSymbol = a.toSymbol + b.toSymbol := (rfl)

@[simp]
theorem toSymbol_smul : (c • a).toSymbol = c • a.toSymbol := (rfl)

@[simp]
theorem toSymbol_neg : (-a).toSymbol = -a.toSymbol := (rfl)

@[simp]
theorem toSymbol_sub : (a - b).toSymbol = a.toSymbol - b.toSymbol :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem toSymbol_nsmul (k : ℕ) : (k • a).toSymbol = k • a.toSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toSymbol

@[simp]
theorem toSymbol_zsmul (k : ℤ) : (k • a).toSymbol = k • a.toSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toSymbol

@[simp]
theorem term_zero : (0 : ClassicalSymbol n V W m).term j = 0 := (rfl)

@[simp]
theorem term_add : (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_smul : (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_neg : (-a).term j = -a.term j := (rfl)

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j :=
  (sub_eq_add_neg _ _).symm

instance : AddCommGroup (ClassicalSymbol n V W m) :=
  toSymbol_injective.addCommGroup _ toSymbol_zero toSymbol_add toSymbol_neg toSymbol_sub
    (fun a k => toSymbol_nsmul a k) (fun a k => toSymbol_zsmul a k)

instance : Module ℂ (ClassicalSymbol n V W m) :=
  toSymbol_injective.module ℂ ⟨⟨toSymbol, toSymbol_zero⟩, toSymbol_add⟩
    fun c a => toSymbol_smul a c

@[simp]
theorem toSymbol_sum {ι : Type*} (s : Finset ι) (a : ι → ClassicalSymbol n V W m) :
    (∑ i ∈ s, a i).toSymbol = ∑ i ∈ s, (a i).toSymbol :=
  map_sum (AddMonoidHom.mk' toSymbol toSymbol_add) a s

@[simp]
theorem term_sum {ι : Type*} (s : Finset ι) (a : ι → ClassicalSymbol n V W m) (j : ℕ) :
    (∑ i ∈ s, a i).term j = ∑ i ∈ s, (a i).term j :=
  map_sum (AddMonoidHom.mk' (fun a : ClassicalSymbol n V W m => a.term j) fun a b => term_add a b j)
    a s

end Module

/-! ### The principal symbol -/

section Principal

variable (a b : ClassicalSymbol n V W m)

/-- The principal symbol of a classical symbol of order `m`: its leading homogeneous term `a_m`,
of degree `m`. -/
def principal : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  (a.term 0).castDegree (by simp)

theorem principal_def : a.principal = (a.term 0).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  coefficient_castDegree _ _

/-- A classical symbol and its cut-off principal symbol differ by a symbol of order `m - 1`. -/
theorem exists_sub_cutoffSymbol_principal (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : Symbol n V W (m - 1),
      r.coefficient = (a.toSymbol - cutoffSymbol χ a.principal).coefficient :=
  ⟨Symbol.inclusion (by simp) (a.remainder χ 1), funext fun p => by simp⟩

/-- The full symbol of a classical symbol of order `m` and its principal symbol differ by
`C ⟨ξ⟩^(m - 1)` at the frequencies of norm at least `2`, uniformly for positions in a compact
set. -/
theorem exists_norm_toSymbol_sub_principal_le {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ ξ, 2 ≤ ‖ξ‖ →
      ‖a.toSymbol.coefficient (x, ξ) - a.principal.coefficient (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) := by
  obtain ⟨r, hr⟩ := a.exists_sub_cutoffSymbol_principal default
  obtain ⟨C, hC⟩ := r.exists_norm_coefficient_le K hK
  refine ⟨C, fun x hx ξ hξ ↦ ?_⟩
  have h := congrFun hr (x, ξ)
  rw [Symbol.coefficient_sub, Pi.sub_apply, coefficient_cutoffSymbol_of_two_le_norm _ _ hξ] at h
  exact h ▸ hC x hx ξ

/-- **The principal symbol is the high-frequency limit of the full symbol.** At a nonzero
frequency `ξ`, `t ^ (-m) a(y, t ζ) → σ(a)(x, ξ)` as `t → ∞` and `(y, ζ) → (x, ξ)`. -/
theorem tendsto_rpow_neg_smul_coefficient_smul {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    Tendsto (fun p : ℝ × (CoordinateSpace n × CoordinateSpace n) ↦
        p.1 ^ (-m) • a.toSymbol.coefficient (p.2.1, p.1 • p.2.2))
      (atTop ×ˢ 𝓝 (x, ξ)) (𝓝 (a.principal.coefficient (x, ξ))) := by
  have hσ : ContinuousAt a.principal.coefficient (x, ξ) :=
    a.principal.contDiffOn_coefficient.continuousOn.continuousAt
      ((isOpen_ne.preimage continuous_snd).mem_nhds hξ)
  obtain ⟨b, hb⟩ := a.exists_sub_cutoffSymbol_principal default
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hN : {p : CoordinateSpace n × CoordinateSpace n | ‖ξ‖ / 2 < ‖p.2‖} ∈ 𝓝 (x, ξ) :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds (half_lt_self hr)
  -- For `‖t ζ‖ ≥ 2` the cut-off principal symbol is `σ(a)(y, t ζ) = t ^ m σ(a)(y, ζ)`, so
  -- `t ^ (-m) a(y, t ζ) = σ(a)(y, ζ) + t ^ (-m) b(y, t ζ)` with `b` of order `m - 1`.
  have heq : ∀ᶠ p : ℝ × (CoordinateSpace n × CoordinateSpace n) in atTop ×ˢ 𝓝 (x, ξ),
      a.principal.coefficient p.2 + p.1 ^ (-m) • b.coefficient (p.2.1, p.1 • p.2.2) =
        p.1 ^ (-m) • a.toSymbol.coefficient (p.2.1, p.1 • p.2.2) := by
    filter_upwards [prod_mem_prod (eventually_ge_atTop (4 / ‖ξ‖)) hN]
    rintro ⟨t, y, ζ⟩ ⟨ht, hζ⟩
    have ht : 4 / ‖ξ‖ ≤ t := ht
    have hζ : ‖ξ‖ / 2 < ‖ζ‖ := hζ
    have ht0 : 0 < t := (by positivity : 0 < 4 / ‖ξ‖).trans_le ht
    have h2 : 2 ≤ ‖t • ζ‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      have : 4 ≤ t * ‖ξ‖ := by rwa [div_le_iff₀ hr] at ht
      nlinarith
    have h := congrFun hb (y, t • ζ)
    rw [Symbol.coefficient_sub, Pi.sub_apply, coefficient_cutoffSymbol_of_two_le_norm _ _ h2,
      a.principal.homogeneous _ _ _ ht0] at h
    simp [h, smul_sub, smul_smul, ← Real.rpow_add ht0]
  simpa using ((hσ.tendsto.comp tendsto_snd).add
    (b.tendsto_rpow_neg_smul_coefficient_smul_zero (by linarith) hξ)).congr' heq

@[simp]
theorem principal_zero : (0 : ClassicalSymbol n V W m).principal = 0 :=
  castDegree_zero _

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  castDegree_add _ _ _

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  castDegree_smul _ _ _

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  castDegree_neg _ _

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal := by
  simp [principal, castDegree_sub]

end Principal

/-! ### Smoothing symbols and single homogeneous terms -/

section Examples

/-- A smoothing symbol is a classical symbol, all of whose homogeneous terms vanish. -/
def ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) : ClassicalSymbol n V W m where
  toSymbol := a
  term _ := 0
  exists_remainder' := ⟨default, fun N => ⟨(Symbol.isSmoothing_iff.1 ha (m - N)).choose, fun p => by
    simp [(Symbol.isSmoothing_iff.1 ha (m - N)).choose_spec]⟩⟩

@[simp]
theorem toSymbol_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) :
    (ofIsSmoothing a ha).toSymbol = a :=
  (rfl)

@[simp]
theorem term_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) (j : ℕ) :
    (ofIsSmoothing a ha).term j = 0 :=
  (rfl)

/-- A classical symbol is smoothing exactly when all of its homogeneous terms vanish. -/
theorem isSmoothing_toSymbol_iff (a : ClassicalSymbol n V W m) :
    a.toSymbol.IsSmoothing ↔ ∀ j, a.term j = 0 := by
  refine ⟨fun ha j => ?_, fun ha => Symbol.isSmoothing_iff_forall_nat.2 fun N => ?_⟩
  · exact (term_eq_of_toSymbol_eq (a := a) (b := ofIsSmoothing a.toSymbol ha) rfl j).trans
      (term_ofIsSmoothing _ _ j)
  · -- With vanishing terms the remainder after `N` terms is the symbol itself, of order `m - N`.
    exact ⟨a.remainder default N, funext fun p => by simp [ha]⟩

/-- The classical symbol `χ(ξ) a(x, ξ)` of a single homogeneous term `a` of degree `m`: its
principal symbol is `a` and its other homogeneous terms vanish. -/
def ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ClassicalSymbol n V W m where
  toSymbol := cutoffSymbol χ a
  term
    | 0 => a.castDegree (by simp)
    | _ + 1 => 0
  exists_remainder' := ⟨χ, fun
    | 0 => ⟨Symbol.inclusion (by simp) (cutoffSymbol χ a), fun p => by simp⟩
    | N + 1 => ⟨0, fun p => by simp [Finset.sum_range_succ']⟩⟩

variable (χ : FrequencyCutoff (CoordinateSpace n))
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

@[simp]
theorem toSymbol_ofHomogeneous : (ofHomogeneous χ a).toSymbol = cutoffSymbol χ a :=
  (rfl)

@[simp]
theorem principal_ofHomogeneous : (ofHomogeneous χ a).principal = a :=
  castDegree_castDegree _ _ _ |>.trans (castDegree_rfl a)

@[simp]
theorem term_ofHomogeneous_succ (j : ℕ) : (ofHomogeneous χ a).term (j + 1) = 0 :=
  (rfl)

@[simp]
theorem ofHomogeneous_zero : ofHomogeneous χ (0 : HomogeneousSymbol _ _ V W m) = 0 :=
  ext (map_zero (cutoffSymbol χ))

end Examples

section EqHomogeneous

/-- A symbol `a` of order `m` that agrees with a homogeneous symbol `h` of degree `m` at all
frequencies of norm at least some `R` is a classical symbol, with principal symbol `h`
(`TauCeti.ClassicalSymbol.principal_ofEqHomogeneous`) and no further homogeneous terms. It is
the cut-off term `χ(ξ) h(x, ξ)` plus a smoothing symbol. -/
def ofEqHomogeneous (a : Symbol n V W m)
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (hah : ∃ R : ℝ, ∀ x ξ, R ≤ ‖ξ‖ → a.coefficient (x, ξ) = h.coefficient (x, ξ)) :
    ClassicalSymbol n V W m :=
  ofHomogeneous default h + ofIsSmoothing (a - cutoffSymbol default h) (by
    obtain ⟨R, hR⟩ := hah
    refine Symbol.isSmoothing_of_coefficient_eq_zero (max R 2) fun x ξ hξ ↦ ?_
    rw [Symbol.coefficient_sub, Pi.sub_apply, hR x ξ (le_of_max_le_left hξ),
      coefficient_cutoffSymbol_of_two_le_norm _ _ (le_of_max_le_right hξ), sub_self])

variable (a : Symbol n V W m) (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
  (hah : ∃ R : ℝ, ∀ x ξ, R ≤ ‖ξ‖ → a.coefficient (x, ξ) = h.coefficient (x, ξ))

@[simp]
theorem toSymbol_ofEqHomogeneous : (ofEqHomogeneous a h hah).toSymbol = a := by
  simp [ofEqHomogeneous]

@[simp]
theorem principal_ofEqHomogeneous : (ofEqHomogeneous a h hah).principal = h := by
  rw [ofEqHomogeneous, principal_add, principal_ofHomogeneous, principal_def, term_ofIsSmoothing,
    castDegree_zero, add_zero]

@[simp]
theorem term_ofEqHomogeneous_succ (j : ℕ) : (ofEqHomogeneous a h hah).term (j + 1) = 0 := by
  simp [ofEqHomogeneous, term_ofIsSmoothing]

/-- A coefficient `f` that is smooth on all of `ℝⁿ × ℝⁿ` and positively homogeneous of degree `m`
in the frequency away from `ξ = 0` is a classical symbol of order `m`, whose principal symbol is
`f` itself away from `ξ = 0` and whose other homogeneous terms vanish. -/
def ofContDiffHomogeneous (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) :
    ClassicalSymbol n V W m :=
  ofEqHomogeneous (Symbol.ofContDiffHomogeneous f hf hhom) (mk' f hf.contDiffOn hhom)
    ⟨1, fun _ _ hξ ↦ by
      rw [Symbol.coefficient_ofContDiffHomogeneous,
        coefficient_mk'_of_ne_zero _ _ _ (norm_pos_iff.1 (lt_of_lt_of_le one_pos hξ))]⟩

variable (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f)
  (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ))

@[simp]
theorem toSymbol_ofContDiffHomogeneous :
    (ofContDiffHomogeneous f hf hhom).toSymbol = Symbol.ofContDiffHomogeneous f hf hhom := by
  rw [ofContDiffHomogeneous, toSymbol_ofEqHomogeneous]

@[simp]
theorem principal_ofContDiffHomogeneous :
    (ofContDiffHomogeneous f hf hhom).principal = mk' f hf.contDiffOn hhom := by
  rw [ofContDiffHomogeneous, principal_ofEqHomogeneous]

@[simp]
theorem term_ofContDiffHomogeneous_succ (j : ℕ) :
    (ofContDiffHomogeneous f hf hhom).term (j + 1) = 0 := by
  rw [ofContDiffHomogeneous, term_ofEqHomogeneous_succ]

end EqHomogeneous

section PrincipalKernel

/-- The principal symbol of a classical symbol of order `m` vanishes exactly when its full symbol
has order `m - 1`. -/
theorem principal_eq_zero_iff {a : ClassicalSymbol n V W m} :
    a.principal = 0 ↔ ∃ r : Symbol n V W (m - 1), r.coefficient = a.toSymbol.coefficient := by
  obtain ⟨r', hr'⟩ := a.exists_sub_cutoffSymbol_principal default
  constructor
  · intro h
    refine ⟨r', ?_⟩
    rw [hr', h]
    funext p
    simp
  · rintro ⟨r, hr⟩
    refine eq_zero_of_coefficient_eq_cutoffSymbol default (m' := m - 1) (by linarith) (r - r') ?_
    rw [Symbol.coefficient_sub, hr, hr', Symbol.coefficient_sub, sub_sub_cancel]

/-- Every homogeneous symbol of degree `m` is the principal symbol of a classical symbol of
order `m`. -/
theorem principal_surjective :
    Function.Surjective (principal : ClassicalSymbol n V W m → _) :=
  fun a ↦ ⟨ofHomogeneous default a, principal_ofHomogeneous default a⟩

end PrincipalKernel

/-! ### Inclusion of orders -/

section Inclusion

variable {m' : ℝ}

/-- **Inclusion of orders.** A classical symbol of order `m' = m - k`, `k ∈ ℕ`, is a classical
symbol of order `m` whose first `k` homogeneous terms vanish, followed by the terms of the original
expansion. The steps of an expansion are integers, so orders with a non-integer difference are not
comparable in the classical calculus. -/
def inclusion (k : ℕ) (hk : m' = m - k) :
    ClassicalSymbol n V W m' →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun b :=
    { toSymbol := Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b.toSymbol
      term j := if h : k ≤ j then (b.term (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring)
        else 0
      exists_remainder' := ⟨default, fun N => by
        rcases le_or_gt k N with hN | hN
        · -- After `N = k + M` terms the remainder is the remainder of `b` after `M` terms.
          obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
          refine ⟨Symbol.inclusion (le_of_eq (by rw [hk]; push_cast; ring))
            (b.remainder default M), fun p => ?_⟩
          rw [Symbol.coefficient_inclusion, coefficient_remainder, Symbol.coefficient_inclusion,
            Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range k) fun j hj => ?_,
            zero_add]
          · congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Nat.le_add_right, ↓reduceDIte, coefficient_castDegree]
            rw [coefficient_congr_index b.term (Nat.add_sub_cancel_left k i)]
          · simp [show ¬k ≤ j by simpa using hj]
        · -- Before the `k`-th term all terms vanish, and `b` has order `m - k ≤ m - N`.
          refine ⟨Symbol.inclusion (by rw [hk]; gcongr) b.toSymbol, fun p => ?_⟩
          rw [Symbol.coefficient_inclusion, Symbol.coefficient_inclusion,
            Finset.sum_eq_zero fun j hj => ?_, sub_zero]
          simp [show ¬k ≤ j by simp at hj; omega]⟩ }
  map_add' a b := ext (map_add (Symbol.inclusion _) a.toSymbol b.toSymbol)
  map_smul' c a := ext (map_smul (Symbol.inclusion _) c a.toSymbol)

variable (k : ℕ) (hk : m' = m - k) (b : ClassicalSymbol n V W m')

@[simp]
theorem toSymbol_inclusion :
    (inclusion k hk b).toSymbol =
      Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b.toSymbol :=
  (rfl)

theorem term_inclusion (j : ℕ) :
    (inclusion k hk b).term j =
      if h : k ≤ j then (b.term (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring) else 0 :=
  (rfl)

@[simp]
theorem term_inclusion_of_lt {j : ℕ} (hj : j < k) : (inclusion k hk b).term j = 0 := by
  simp [term_inclusion, show ¬k ≤ j by omega]

@[simp]
theorem term_inclusion_add (j : ℕ) :
    (inclusion k hk b).term (k + j) = (b.term j).castDegree (by rw [hk]; push_cast; ring) := by
  ext1
  simp only [term_inclusion, Nat.le_add_right, ↓reduceDIte, coefficient_castDegree]
  rw [coefficient_congr_index b.term (Nat.add_sub_cancel_left k j)]

/-- Including a classical symbol into an equal order (a change of the order's expression) keeps
its homogeneous terms. -/
@[simp]
theorem term_inclusion_zero (hk : m' = m - (0 : ℕ)) (j : ℕ) :
    (inclusion 0 hk b).term j = (b.term j).castDegree (by rw [hk]; simp) := by
  ext1
  simp only [term_inclusion, Nat.zero_le, ↓reduceDIte, coefficient_castDegree]
  rw [coefficient_congr_index b.term (Nat.sub_zero j)]

/-- Including a classical symbol into a strictly larger order kills its principal symbol. -/
@[simp]
theorem principal_inclusion_succ (k : ℕ) (hk : m' = m - (k + 1 : ℕ)) :
    (inclusion (k + 1) hk b).principal = 0 := by
  ext1
  simp

theorem inclusion_injective :
    Function.Injective (inclusion (n := n) (V := V) (W := W) k hk) := fun _ _ h =>
  ext (Symbol.inclusion_injective _ (congrArg toSymbol h))

end Inclusion

/-! ### Removing the leading term -/

section Tail

variable (χ : FrequencyCutoff (CoordinateSpace n)) (a : ClassicalSymbol n V W m)

/-- **Removing the leading term.** The remainder `a - χ(ξ) a_m` of a classical symbol of order `m`
after its principal term, as a classical symbol of order `m - 1` with the homogeneous terms
`a_{m-1}, a_{m-2}, …`. -/
def tail : ClassicalSymbol n V W (m - 1) where
  toSymbol := Symbol.inclusion (le_of_eq (by simp)) (a.remainder χ 1)
  term j := (a.term (j + 1)).castDegree (by push_cast; ring)
  exists_remainder' := ⟨χ, fun N =>
    ⟨Symbol.inclusion (le_of_eq (by push_cast; ring)) (a.remainder χ (N + 1)), fun p => by
      rw [Symbol.coefficient_inclusion, Symbol.coefficient_inclusion, coefficient_remainder,
        coefficient_remainder, Finset.sum_range_succ', Finset.sum_range_one]
      simp only [coefficient_castDegree]
      abel⟩⟩

@[simp]
theorem coefficient_toSymbol_tail (p : CoordinateSpace n × CoordinateSpace n) :
    (a.tail χ).toSymbol.coefficient p =
      a.toSymbol.coefficient p - χ p.2 • (a.term 0).coefficient p := by
  simp [tail]

@[simp]
theorem term_tail (j : ℕ) :
    (a.tail χ).term j = (a.term (j + 1)).castDegree (by push_cast; ring) :=
  (rfl)

/-- A classical symbol is its cut-off principal term plus its tail, included back into order
`m`. -/
theorem inclusion_tail_add_ofHomogeneous :
    inclusion 1 (by simp) (a.tail χ) + ofHomogeneous χ a.principal = a :=
  ext <| Symbol.ext <| funext fun p => by simp

end Tail

/-! ### The principal symbol sequence

The principal symbol fits into the exact sequence `0 → S^{m-1}_cl → S^m_cl → H^m → 0`: it is
surjective onto the homogeneous symbols of degree `m`, and its kernel is the image of the classical
symbols of order `m - 1`. -/

section PrincipalSequence

variable (n V W m) in
/-- The principal symbol as a linear map. -/
def principalLinearMap :
    ClassicalSymbol n V W m →ₗ[ℂ] HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m
    where
  toFun := principal
  map_add' := principal_add
  map_smul' c a := principal_smul a c

@[simp]
theorem principalLinearMap_apply (a : ClassicalSymbol n V W m) :
    principalLinearMap n V W m a = a.principal :=
  (rfl)
/-- **The kernel of the principal symbol.** A classical symbol of order `m` has principal symbol
zero exactly when it is a classical symbol of order `m - 1`. -/
theorem principal_eq_zero_iff_exists_inclusion (a : ClassicalSymbol n V W m) :
    a.principal = 0 ↔ ∃ b : ClassicalSymbol n V W (m - 1), inclusion 1 (by simp) b = a := by
  refine ⟨fun h => ⟨a.tail default, ?_⟩, ?_⟩
  · -- With a vanishing leading term, `a` is the inclusion of its tail.
    simpa [h] using inclusion_tail_add_ofHomogeneous default a
  · rintro ⟨b, rfl⟩
    exact principal_inclusion_succ b 0 (by simp)

variable (n V W m) in
/-- **The kernel of the principal symbol** is the image of the classical symbols of order
`m - 1`. -/
theorem ker_principalLinearMap :
    LinearMap.ker (principalLinearMap n V W m) =
      LinearMap.range (inclusion (n := n) (V := V) (W := W) (m' := m - 1) 1 (by simp)) := by
  ext a
  simp only [LinearMap.mem_ker, principalLinearMap_apply, principal_eq_zero_iff_exists_inclusion,
    LinearMap.mem_range]

variable (n V W m) in
/-- The principal symbol identifies the quotient of the classical symbols of order `m` by the
classical symbols of order `m - 1` (`TauCeti.ClassicalSymbol.ker_principalLinearMap`) with the
homogeneous symbols of degree `m`. -/
def principalEquiv :
    (ClassicalSymbol n V W m ⧸
        LinearMap.range (inclusion (n := n) (V := V) (W := W) (m' := m - 1) 1 (by simp))) ≃ₗ[ℂ]
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  (Submodule.quotEquivOfEq _ _ (ker_principalLinearMap n V W m).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ principal_surjective)

@[simp]
theorem principalEquiv_mk (a : ClassicalSymbol n V W m) :
    principalEquiv n V W m (Submodule.Quotient.mk a) = a.principal :=
  (rfl)

end PrincipalSequence

/-! ### Pointwise composition -/

section Comp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}

/-- The homogeneous terms `cₖ = ∑_{i + j = k} qᵢ ∘ pⱼ` of the pointwise composition
`(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of two classical symbols, with the terms `qᵢ` of degree `m' - i` and
`pⱼ` of degree `m - j`. The term `cₖ` has degree `m' + m - k`. -/
def compTerms
    (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (k : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V U (m' + m - k) :=
  ∑ i ∈ Finset.range (k + 1),
    if h : i ≤ k then ((q i).comp (p (k - i))).castDegree (by rw [Nat.cast_sub h]; ring) else 0

section CompTerms

variable (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
  (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))

/-- The coefficient of `cₖ` is `∑_{i ≤ k} qᵢ ∘ pₖ₋ᵢ`. -/
theorem coefficient_compTerms (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (compTerms q p k).coefficient z =
      ∑ i ∈ Finset.range (k + 1), ((q i).coefficient z).comp ((p (k - i)).coefficient z) := by
  rw [compTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Nat.le_of_lt_succ (Finset.mem_range.1 hi)]

@[simp]
theorem coefficient_compTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (compTerms q p 0).coefficient z = ((q 0).coefficient z).comp ((p 0).coefficient z) := by
  simp [coefficient_compTerms]

/-- The recursion `cₖ₊₁ = q₀ ∘ pₖ₊₁ + ∑_{i + j = k} qᵢ₊₁ ∘ pⱼ` for the terms of a composition. -/
theorem coefficient_compTerms_succ (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (compTerms q p (k + 1)).coefficient z =
      ((q 0).coefficient z).comp ((p (k + 1)).coefficient z) +
        (compTerms (m' := m' - 1) (fun i => (q (i + 1)).castDegree (by push_cast; ring)) p
          k).coefficient z := by
  rw [coefficient_compTerms, coefficient_compTerms, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coefficient_castDegree, coefficient_congr_index p (Nat.add_sub_add_right k 1 i)]

end CompTerms

/-- The remainders of the pointwise composition of classical symbols after `N` terms have
order `m' + m - N`. -/
private theorem exists_remainder_comp (χ : FrequencyCutoff (CoordinateSpace n))
    (a : ClassicalSymbol n V W m) (N : ℕ) :
    ∀ {m' : ℝ} (b : ClassicalSymbol n W U m'), ∃ r : Symbol n V U (m' + m - N), ∀ p,
      r.coefficient p = (b.toSymbol.comp a.toSymbol).coefficient p -
        ∑ k ∈ Finset.range N, χ p.2 • (compTerms b.term a.term k).coefficient p := by
  -- Induct on the number `N` of terms, removing the leading term of `b` at each step.
  induction N with
  | zero => exact fun b => ⟨Symbol.inclusion (le_of_eq (by simp)) (b.toSymbol.comp a.toSymbol),
      fun p => by simp⟩
  | succ N ih =>
    intro m' b
    -- Split `b = χ(ξ) b₀ + b₁`, where `b₁` has order `m' - 1` and the terms `b₁, b₂, …`. Then
    -- `b ∘ a - ∑_{k ≤ N} χ cₖ = χ b₀ ∘ (a - ∑_{j ≤ N} χ aⱼ) + (b₁ ∘ a - ∑_{k < N} χ cₖ')` for
    -- `‖ξ‖ ≥ 2`, where `cₖ'` are the terms of `b₁ ∘ a`, and both summands have order
    -- `m' + m - (N + 1)`.
    obtain ⟨R, hR⟩ := ih (b.tail χ)
    have ht : (b.tail χ).term = fun i => (b.term (i + 1)).castDegree (by push_cast; ring) := rfl
    obtain ⟨r, hr⟩ := Symbol.exists_coefficient_eq_of_forall_le_norm
      ((b.toSymbol.comp a.toSymbol).contDiff_coefficient.sub
        (Symbol.contDiff_sum_coefficient (Finset.range (N + 1))
          fun k => cutoffSymbol χ (compTerms b.term a.term k)))
      (Symbol.inclusion (le_of_eq (by push_cast; ring))
          ((cutoffSymbol χ b.principal).comp (a.remainder χ (N + 1))) +
        Symbol.inclusion (le_of_eq (by push_cast; ring)) R : Symbol n V U (m' + m - (N + 1 : ℕ)))
      2 fun x ξ hξ => by
      have hχ := χ.apply_eq_one_of_two_le_norm hξ
      simp only [Finset.sum_apply, Symbol.coefficient_add, Pi.add_apply,
        Symbol.coefficient_inclusion, Symbol.coefficient_comp, hR, ht, coefficient_remainder,
        coefficient_toSymbol_tail, coefficient_cutoffSymbol, coefficient_principal, hχ,
        one_smul, Finset.sum_range_succ' _ N, coefficient_compTerms_succ,
        coefficient_compTerms_zero, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_finsetSum, Finset.sum_add_distrib]
      abel
    exact ⟨r, fun p => by simp [hr, Finset.sum_apply]⟩

/-- **Pointwise composition.** The pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of classical
symbols of orders `m'` and `m` is a classical symbol of order `m' + m`, whose terms
`cₖ = ∑_{i + j = k} bᵢ ∘ aⱼ` collect the products of the terms of total degree drop `k`. This is
not the composition of the operators: the lower order terms of the symbol of a composition of
operators also involve derivatives of the symbols. -/
def comp (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    ClassicalSymbol n V U (m' + m) where
  toSymbol := b.toSymbol.comp a.toSymbol
  term := compTerms b.term a.term
  exists_remainder' := ⟨default, fun N => exists_remainder_comp default a N b⟩

variable (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_comp : (b.comp a).toSymbol = b.toSymbol.comp a.toSymbol :=
  (rfl)

@[simp]
theorem term_comp (k : ℕ) : (b.comp a).term k = compTerms b.term a.term k :=
  (rfl)

theorem comp_add (b : ClassicalSymbol n W U m') (a₁ a₂ : ClassicalSymbol n V W m) :
    b.comp (a₁ + a₂) = b.comp a₁ + b.comp a₂ :=
  ext (Symbol.comp_add _ _ _)

theorem add_comp (b₁ b₂ : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (b₁ + b₂).comp a = b₁.comp a + b₂.comp a :=
  ext (Symbol.add_comp _ _ _)

@[simp]
theorem comp_smul (c : ℂ) : b.comp (c • a) = c • b.comp a :=
  ext (Symbol.comp_smul _ _ _)

@[simp]
theorem smul_comp (c : ℂ) : (c • b).comp a = c • b.comp a :=
  ext (Symbol.smul_comp _ _ _)

@[simp]
theorem comp_zero : b.comp (0 : ClassicalSymbol n V W m) = 0 :=
  ext (Symbol.comp_zero _)

@[simp]
theorem zero_comp : (0 : ClassicalSymbol n W U m').comp a = 0 :=
  ext (Symbol.zero_comp _)

/-- **The principal symbol is multiplicative** for the pointwise composition. -/
@[simp]
theorem principal_comp : (b.comp a).principal = b.principal.comp a.principal := by
  ext1
  funext z
  simp

@[simp]
theorem comp_neg (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    b.comp (-a) = -b.comp a :=
  ext (Symbol.comp_neg _ _)

@[simp]
theorem neg_comp (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (-b).comp a = -b.comp a :=
  ext (Symbol.neg_comp _ _)

theorem comp_sub (b : ClassicalSymbol n W U m') (a₁ a₂ : ClassicalSymbol n V W m) :
    b.comp (a₁ - a₂) = b.comp a₁ - b.comp a₂ :=
  ext (Symbol.comp_sub _ _ _)

theorem sub_comp (b₁ b₂ : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (b₁ - b₂).comp a = b₁.comp a - b₂.comp a :=
  ext (Symbol.sub_comp _ _ _)

/-- The product of two cut-off homogeneous terms is the cut-off composition of the terms, for the
product cutoff. -/
theorem ofHomogeneous_comp_ofHomogeneous (χ χ' : FrequencyCutoff (CoordinateSpace n))
    (b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U m')
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (ofHomogeneous χ b).comp (ofHomogeneous χ' a) = ofHomogeneous (χ * χ') (b.comp a) := by
  ext : 2
  funext p
  simp [smul_smul, mul_comm]

end Comp

/-! ### Derivatives -/

section Deriv

/-- The spatial derivative `∂_{x_j} a` of a classical symbol of order `m`: a classical symbol of
order `m`, whose homogeneous terms are the spatial derivatives `∂_{x_j} a_{m-k}` of those of
`a`. -/
def spatialDeriv (j : Fin n) : ClassicalSymbol n V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun a :=
    { toSymbol := Symbol.spatialDeriv j a.toSymbol
      term k := (a.term k).spatialDeriv (EuclideanSpace.single j 1)
      exists_remainder' := ⟨default, fun N => ⟨Symbol.spatialDeriv j (a.remainder default N),
        fun p => by
          -- Differentiate the identity `a = r_N + ∑_{k<N} χ(ξ) a_{m-k}` in the position.
          simpa using
            congrArg (fun s => (Symbol.spatialDeriv j s).coefficient p)
              (a.inclusion_remainder default N)⟩⟩ }
  map_add' a b := ext <| by simp
  map_smul' c a := ext <| by simp

@[simp]
theorem toSymbol_spatialDeriv (j : Fin n) (a : ClassicalSymbol n V W m) :
    (spatialDeriv j a).toSymbol = Symbol.spatialDeriv j a.toSymbol :=
  (rfl)

@[simp]
theorem term_spatialDeriv (j : Fin n) (a : ClassicalSymbol n V W m) (k : ℕ) :
    (spatialDeriv j a).term k = (a.term k).spatialDeriv (EuclideanSpace.single j 1) :=
  (rfl)

/-- The principal symbol of `∂_{x_j} a` is the spatial derivative of the principal symbol of
`a`. -/
@[simp]
theorem principal_spatialDeriv (j : Fin n) (a : ClassicalSymbol n V W m) :
    (spatialDeriv j a).principal = a.principal.spatialDeriv (EuclideanSpace.single j 1) :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ _ => by simp

/-- The remainder of the frequency derivative of a classical symbol after `N` terms has order
`m - 1 - N`. -/
private theorem exists_remainder_frequencyDeriv (a : ClassicalSymbol n V W m) (j : Fin n)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n V W (m - 1 - N), ∀ p, r.coefficient p =
      (Symbol.frequencyDeriv j a.toSymbol).coefficient p - ∑ k ∈ Finset.range N,
        χ p.2 • ((a.term k).frequencyDeriv (EuclideanSpace.single j 1)).coefficient p := by
  -- Differentiating `a = r_N + ∑_{k<N} χ(ξ) a_{m-k}` in the frequency gives `∂_{ξ_j} r_N`, of
  -- order `m - N - 1`, plus the terms `∂_{ξ_j} (χ(ξ) a_{m-k})`, each of which differs from
  -- `χ(ξ) ∂_{ξ_j} a_{m-k}` by a smoothing symbol.
  choose s hs using fun k => Symbol.isSmoothing_iff.1
    (isSmoothing_frequencyDeriv_cutoffSymbol_sub_cutoffSymbol_frequencyDeriv χ j (a.term k))
    (m - 1 - N)
  refine ⟨Symbol.inclusion (le_of_eq (by ring)) (Symbol.frequencyDeriv j (a.remainder χ N)) +
    ∑ k ∈ Finset.range N, s k, fun p => ?_⟩
  have h := congrArg (fun s => (Symbol.frequencyDeriv j s).coefficient p)
    (a.inclusion_remainder χ N)
  simp only [Symbol.frequencyDeriv_inclusion, Symbol.coefficient_inclusion, map_sub, map_sum,
    Symbol.coefficient_sub, Symbol.coefficient_sum, Pi.sub_apply, Finset.sum_apply] at h
  simp only [Symbol.coefficient_add, Symbol.coefficient_inclusion, Symbol.coefficient_sum,
    Pi.add_apply, Finset.sum_apply, hs, h, Symbol.coefficient_sub, Pi.sub_apply,
    Finset.sum_sub_distrib, coefficient_cutoffSymbol]
  abel

/-- The frequency derivative `∂_{ξ_j} a` of a classical symbol of order `m`: a classical symbol of
order `m - 1`, whose homogeneous terms are the frequency derivatives `∂_{ξ_j} a_{m-k}` of those of
`a`. -/
def frequencyDeriv (j : Fin n) : ClassicalSymbol n V W m →ₗ[ℂ] ClassicalSymbol n V W (m - 1) where
  toFun a :=
    { toSymbol := Symbol.frequencyDeriv j a.toSymbol
      term k := ((a.term k).frequencyDeriv (EuclideanSpace.single j 1)).castDegree (by ring)
      exists_remainder' := ⟨default, fun N => by
        simpa using a.exists_remainder_frequencyDeriv j default N⟩ }
  map_add' a b := ext <| by simp
  map_smul' c a := ext <| by simp

@[simp]
theorem toSymbol_frequencyDeriv (j : Fin n) (a : ClassicalSymbol n V W m) :
    (frequencyDeriv j a).toSymbol = Symbol.frequencyDeriv j a.toSymbol :=
  (rfl)

@[simp]
theorem term_frequencyDeriv (j : Fin n) (a : ClassicalSymbol n V W m) (k : ℕ) :
    (frequencyDeriv j a).term k =
      ((a.term k).frequencyDeriv (EuclideanSpace.single j 1)).castDegree (by ring) :=
  (rfl)

/-- The principal symbol of `∂_{ξ_j} a` is the frequency derivative of the principal symbol of
`a`. -/
@[simp]
theorem principal_frequencyDeriv (j : Fin n) (a : ClassicalSymbol n V W m) :
    (frequencyDeriv j a).principal = a.principal.frequencyDeriv (EuclideanSpace.single j 1) :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ => by simp [hξ]

end Deriv

/-! ### Elliptic classical symbols -/

section Elliptic

/-- A classical symbol is *elliptic* if its principal symbol is: its value at every position and
every nonzero frequency is an invertible continuous linear map. -/
def IsElliptic (a : ClassicalSymbol n V W m) : Prop :=
  a.principal.IsElliptic

/-- Ellipticity of a classical symbol is ellipticity of its principal symbol, whose pointwise
inverse is then `HomogeneousSymbol.inverse`. -/
theorem isElliptic_def {a : ClassicalSymbol n V W m} : a.IsElliptic ↔ a.principal.IsElliptic :=
  Iff.rfl

/-- A classical symbol is elliptic when its principal symbol is invertible at every position and
every nonzero frequency. -/
theorem isElliptic_iff {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → (a.principal.coefficient (x, ξ)).IsInvertible :=
  HomogeneousSymbol.isElliptic_iff

/-- The classical symbol `χ(ξ) a(x, ξ)` of a single homogeneous term is elliptic exactly when the
term is. -/
@[simp]
theorem isElliptic_ofHomogeneous_iff (χ : FrequencyCutoff (CoordinateSpace n))
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} :
    (ofHomogeneous χ a).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_ofHomogeneous]

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) {a : ClassicalSymbol n V W m} :
    (c • a).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_smul, HomogeneousSymbol.isElliptic_smul_iff hc, isElliptic_def]

/-- The pointwise composition of elliptic classical symbols is elliptic. -/
theorem IsElliptic.comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    {b : ClassicalSymbol n W U m'} {a : ClassicalSymbol n V W m} (hb : b.IsElliptic)
    (ha : a.IsElliptic) : (b.comp a).IsElliptic := by
  rw [isElliptic_def, principal_comp]
  exact (isElliptic_def.1 hb).comp (isElliptic_def.1 ha)

/-- Between Banach spaces, a classical symbol is elliptic exactly when its principal symbol is
bijective at every position and every nonzero frequency. -/
theorem isElliptic_iff_bijective [CompleteSpace V] [CompleteSpace W]
    {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → Function.Bijective (a.principal.coefficient (x, ξ)) :=
  HomogeneousSymbol.isElliptic_iff_bijective

/-- Adding a classical symbol with vanishing principal symbol, that is, of order `m - 1`
(`TauCeti.ClassicalSymbol.principal_eq_zero_iff`), does not change ellipticity. -/
theorem isElliptic_add_iff {a b : ClassicalSymbol n V W m} (hb : b.principal = 0) :
    (a + b).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, principal_add, hb, add_zero, isElliptic_def]

/-- **The inverse principal symbol.** The principal symbol `a_m` of an elliptic classical symbol of
order `m` has a unique two-sided inverse at every nonzero frequency that is a homogeneous symbol of
degree `-m`, namely `TauCeti.HomogeneousSymbol.inverse`. -/
theorem existsUnique_inversePrincipalSymbol [CompleteSpace V] {a : ClassicalSymbol n V W m}
    (ha : a.IsElliptic) :
    ∃! b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (-m),
      ∀ x ξ, ξ ≠ 0 →
        b.coefficient (x, ξ) ∘L a.principal.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V ∧
          a.principal.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = ContinuousLinearMap.id ℂ W :=
  have hp := isElliptic_def.1 ha
  ⟨a.principal.inverse hp, fun _ _ hξ => ⟨coefficient_inverse_comp_coefficient _ hp hξ,
    coefficient_comp_coefficient_inverse _ hp hξ⟩, fun b hb =>
      eq_inverse_of_comp_eq_id_left _ hp <| ext_of_ne_zero fun x ξ hξ => by
        simpa [hξ] using (hb x ξ hξ).1⟩

/-- **Perturbation of an inverse bounded by `C₀ ⟨ξ⟩^(-m)`.** If `‖A⁻¹‖ ≤ C₀ ⟨ξ⟩^(-m)` and
`‖B - A‖ ≤ C₁ ⟨ξ⟩^(m - 1)` at a frequency of norm at least `R ≥ 2 C₀ C₁`, `R > 0`, then
`C₀ ⟨ξ⟩^(-m) ‖B - A‖ ≤ 1 / 2`, so `B` is invertible with `‖B⁻¹‖ ≤ 2 C₀ ⟨ξ⟩^(-m)`. -/
private theorem isInvertible_and_norm_inverse_le_of_norm_sub_le [CompleteSpace V]
    {A B : V →L[ℂ] W} (hA : A.IsInvertible) {C₀ C₁ R : ℝ} {ξ : CoordinateSpace n}
    (hR : 0 < R) (hCR : 2 * C₀ * C₁ ≤ R) (hξ : R ≤ ‖ξ‖)
    (hM : ‖A.inverse‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (hBA : ‖B - A‖ ≤ C₁ * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) :
    B.IsInvertible ∧ ‖B.inverse‖ ≤ 2 * C₀ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by
  set M := C₀ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)
  have hw₀ := rpow_weight_pos ξ (-m)
  have hw₁ := rpow_weight_pos ξ (m - 1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hC₀ : 0 ≤ C₀ := nonneg_of_mul_nonneg_left hM0 hw₀
  have hC₁ : 0 ≤ C₁ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hBA) hw₁
  -- `⟨ξ⟩^(-m) ⟨ξ⟩^(m - 1) = ⟨ξ⟩^(-1) ≤ R⁻¹`.
  have hw : (1 + ‖ξ‖ ^ 2) ^ (-m / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) ≤ R⁻¹ := by
    have h := rpow_weight_le_rpow_mul_rpow_weight (s := -1) (s' := 0) hR hξ (by norm_num)
    rw [← Real.rpow_add (by positivity)]
    convert h using 2
    · ring
    · simp [Real.rpow_neg_one]
  -- `M ‖B - A‖ ≤ C₀ C₁ ⟨ξ⟩^(-m) ⟨ξ⟩^(m - 1) ≤ C₀ C₁ R⁻¹ ≤ 1 / 2`.
  have hsmall : M * ‖B - A‖ ≤ 1 / 2 := by
    calc M * ‖B - A‖ ≤ M * (C₁ * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) := by gcongr
      _ = C₀ * C₁ * ((1 + ‖ξ‖ ^ 2) ^ (-m / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) := by ring
      _ ≤ C₀ * C₁ * R⁻¹ := by gcongr
      _ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hR]
        linarith
  have hlt : M * ‖B - A‖ < 1 := hsmall.trans_lt (by norm_num)
  refine ⟨hA.of_mul_norm_sub_lt hM hlt,
    (hA.norm_inverse_le_of_mul_norm_sub_lt hM hlt).trans ?_⟩
  rw [div_le_iff₀ (sub_pos.2 hlt), mul_assoc]
  nlinarith

variable [CompleteSpace V]

/-- **Invertibility of an elliptic symbol at large frequencies.** On every compact set `K` of
positions, the full symbol `a(x, ξ)` of an elliptic classical symbol of order `m` is invertible at
all frequencies of norm at least some radius `R`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem IsElliptic.exists_isInvertible_and_norm_inverse_le {a : ClassicalSymbol n V W m}
    (ha : a.IsElliptic) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ R C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by
  -- The inverse of the principal symbol is bounded by `C₀ ⟨ξ⟩^(-m)` at frequencies of norm at
  -- least `2`, where it agrees with its cut-off symbol of order `-m`.
  have ha' := isElliptic_def.1 ha
  obtain ⟨C₀, hC₀⟩ :=
    (cutoffSymbol default (a.principal.inverse ha')).exists_norm_coefficient_le K hK
  obtain ⟨C₁, hC₁⟩ := a.exists_norm_toSymbol_sub_principal_le hK
  refine ⟨max 2 (2 * C₀ * C₁), 2 * C₀, fun x hx ξ hξ ↦ ?_⟩
  have h2 : 2 ≤ ‖ξ‖ := (le_max_left _ _).trans hξ
  have hM := hC₀ x hx ξ
  rw [coefficient_cutoffSymbol_of_two_le_norm _ _ h2, HomogeneousSymbol.coefficient_inverse] at hM
  exact isInvertible_and_norm_inverse_le_of_norm_sub_le
    (isElliptic_iff.1 ha x ξ (norm_pos_iff.1 (by linarith))) (by positivity) (le_max_right _ _) hξ
    hM (hC₁ x hx ξ h2)

/-- **Ellipticity from invertibility at large frequencies.** If at every position `x` the full
symbol `a(x, ξ)` is invertible at all frequencies of norm at least some `R`, with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`, then the classical symbol is elliptic. -/
theorem isElliptic_of_forall_exists_norm_inverse_le {a : ClassicalSymbol n V W m}
    (h : ∀ x, ∃ R C : ℝ, ∀ ξ, R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    a.IsElliptic := by
  -- At `ξ ≠ 0` and large `t`, the principal symbol `a_m(x, t ξ) = t^m a_m(x, ξ)` differs from the
  -- full symbol `a(x, t ξ)` by `O(t^(m - 1))`, small against the bound `O(t^m)` on its inverse.
  refine isElliptic_iff.2 fun x ξ hξ ↦ ?_
  obtain ⟨R, C, hRC⟩ := h x
  obtain ⟨C₁, hC₁⟩ := a.exists_norm_toSymbol_sub_principal_le (isCompact_singleton (x := x))
  -- Rescale `ξ` to the frequency `t • ξ` of norm `T`, beyond `R`, `2` and `2 C C₁`.
  set T := max (max R 2) (2 * C * C₁)
  have hT2 : 2 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have ht : 0 < T / ‖ξ‖ := div_pos (by linarith) hn
  have htξ : ‖(T / ‖ξ‖) • ξ‖ = T := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_cancel₀ _ hn.ne']
  obtain ⟨hB, hM⟩ := hRC ((T / ‖ξ‖) • ξ) (htξ.symm ▸ (le_max_left _ _).trans (le_max_left _ _))
  have hd := hC₁ x rfl ((T / ‖ξ‖) • ξ) (htξ.symm ▸ hT2)
  rw [← norm_neg, neg_sub] at hd
  -- The principal symbol at `t • ξ` is close to the invertible full symbol, hence invertible.
  have hA := (isInvertible_and_norm_inverse_le_of_norm_sub_le hB (by linarith) (le_max_right _ _)
    htξ.ge hM hd).1
  rw [a.principal.homogeneous x ξ _ ht, ← Complex.coe_smul,
    ContinuousLinearMap.isInvertible_smul_iff (by simp [(Real.rpow_pos_of_pos ht m).ne'])] at hA
  exact hA

/-- **Ellipticity as invertibility at large frequencies.** A classical symbol of order `m` is
elliptic exactly when, on every compact set of positions, its full symbol `a(x, ξ)` is invertible
at all frequencies of norm at least some radius `R`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem isElliptic_iff_forall_isCompact {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ R C : ℝ, ∀ x ∈ K, ∀ ξ,
      R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  ⟨fun ha _ hK ↦ ha.exists_isInvertible_and_norm_inverse_le hK, fun h ↦
    isElliptic_of_forall_exists_norm_inverse_le fun x ↦
      (h {x} isCompact_singleton).imp fun _ ↦ .imp fun _ hC ξ ↦ hC x rfl ξ⟩

end Elliptic

/-! ### The homogeneous terms as a linear map -/

section Terms

variable (n V W m) in
/-- The homogeneous terms `(a_{m-j})ⱼ` of a classical symbol of order `m`, as a linear map to the
sequences of homogeneous symbols of degrees `m - j`. -/
def termsLinearMap : ClassicalSymbol n V W m →ₗ[ℂ]
    ∀ j : ℕ, HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j) where
  toFun a := a.term
  map_add' a b := funext fun j => term_add a b j
  map_smul' c a := funext fun j => term_smul a c j

@[simp]
theorem termsLinearMap_apply (a : ClassicalSymbol n V W m) : termsLinearMap n V W m a = a.term :=
  (rfl)

/-- The classical symbols with vanishing homogeneous terms are exactly the smoothing ones. -/
theorem mem_ker_termsLinearMap {a : ClassicalSymbol n V W m} :
    a ∈ LinearMap.ker (termsLinearMap n V W m) ↔ a.toSymbol.IsSmoothing := by
  simp only [LinearMap.mem_ker, termsLinearMap_apply, isSmoothing_toSymbol_iff, funext_iff,
    Pi.zero_apply]

/-- **Uniqueness modulo smoothing.** Two classical symbols of order `m` differ by a smoothing
symbol exactly when they have the same homogeneous terms. -/
theorem isSmoothing_toSymbol_sub_iff {a b : ClassicalSymbol n V W m} :
    (a.toSymbol - b.toSymbol).IsSmoothing ↔ a.term = b.term := by
  rw [← toSymbol_sub, isSmoothing_toSymbol_iff, funext_iff]
  simp [sub_eq_zero]

end Terms

end ClassicalSymbol

end TauCeti
