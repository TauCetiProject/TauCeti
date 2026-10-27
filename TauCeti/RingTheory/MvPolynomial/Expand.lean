/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Expand
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.RingHom.Basis

/-!
# Finiteness and freeness of `MvPolynomial.expand`

The polynomial ring `R[X_i]` is a finite module over its image under `MvPolynomial.expand n`
(the subring `R[X_i ^ n]`), spanned by the monomials whose exponents are all below `n`. These
monomials are in fact a basis: writing each exponent `d` as `n • (d / n) + d % n` identifies
`R[X_i]` with the free `R[X_i ^ n]`-module on the remainders `d % n`. So for `0 < n` the map
`expand n` is flat, and for finitely many variables it is finite of finite presentation, of
constant rank `n ^ Nat.card σ`. Over `𝔽_p` with `n = p`, `expand p` is the Frobenius of
`𝔽_p[X_i]`, so this is the rank computation for the Frobenius of affine space.

Composed with the finiteness of `MvPolynomial.map f` — a separate result, proved in
`TauCeti/RingTheory/MvPolynomial/Basic.lean` and not imported here — this gives that
`k'[X_1, …, X_r]` is a finite module over `k[X_1 ^ q, …, X_r ^ q]` for a finite extension
`k' / k`, the finiteness that Stacks 10.161.13 (tag 032O) records as "`R'[x^{1/q}]` is finite
over `R[x]`" and that the purely inseparable half of normalization-finiteness rests on.

Also here is the coefficient-level Frobenius computation behind Stacks' "some details omitted":
if every coefficient of `g` acquires a `q`-th root in `S`, then `g(X ^ q)` becomes a `q`-th power
in `S[X_i]`.

## Main results

* `TauCeti.MvPolynomial.span_monomial_lt_eq_top`: over the image of `expand n`, the monomials
  with all exponents below `n` span the polynomial ring.
* `TauCeti.MvPolynomial.finite_expand`: `expand n` is a finite ring map for `0 < n`.
* `TauCeti.MvPolynomial.exists_pow_eq_map_expand`: `(map f) (expand (p ^ n) g)` is a
  `p ^ n`-th power once the coefficients of `g` have `p ^ n`-th roots in `S`.
* `TauCeti.MvPolynomial.basisExpand`: the monomials with exponents below `n` are a basis of
  `R[X_i]` over itself along `expand n`, for `0 < n`.
* `TauCeti.MvPolynomial.flat_expand`: `expand n` is flat for `0 < n`.
* `TauCeti.MvPolynomial.finitePresentation_expand`: `expand n` is of finite presentation for
  finitely many variables.
* `TauCeti.MvPolynomial.finrank_expand`: for `0 < n` and finitely many variables, `expand n` has
  rank `n ^ Nat.card σ` at every prime.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`.

All three results are the multivariate form of the univariate argument in Stacks, Lemma 10.161.13
(tag 032O), whose proof records only "`R′[x^{1/q}]` is finite over `R[x]`" for the first two. The
third is the coefficient half of the details that lemma omits: "There exists a finite purely
inseparable field extension `L′/K` and `q = p^e` such that `L ⊂ L′(x^{1/q})`; some details
omitted". Concretely, with `h = ∑ d_α X ^ α` for `d_α ^ (p ^ n) = f (coeff α g)`, Frobenius gives
`h ^ (p ^ n) = ∑ f (coeff α g) X ^ (p ^ n • α)`. The multivariate forms are not claimed as source
material.

The argument is the finiteness sentence of Stacks 10.161.13 (tag 032O). **That lemma is
univariate**: it is stated for the rings `R[x]` and `R'[x^{1/q}]` in a single variable. What is
formalized here is its multivariate form, over a finite variable type `σ`, which is what the
`n`-variable Noether normalization downstream needs. The mathematical content of each step is
Stacks'; the passage to several variables at once is not, and is not claimed as such below.
-/

public section

namespace TauCeti

/-- Every monomial lies in the span, over the image of `MvPolynomial.expand n`, of the monomials
with all exponents below `n`: write each exponent as `n * γ + β` with `β < n`, so that
`X ^ (n • γ + β) = expand n (X ^ γ) * X ^ β`. -/
private theorem MvPolynomial.monomial_mem_span_monomial_lt {σ R : Type*} [CommSemiring R]
    [Finite σ]
    {n : ℕ} (hn : 0 < n) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.monomial d r ∈
      Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
        (Set.range fun β : σ → Fin n =>
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) := by
  classical
  -- the exponent `d i` splits as `n * (d i / n) + d i % n`
  have hexp :
      n • (Finsupp.equivFunOnFinite.symm fun i => d i / n)
        + (Finsupp.equivFunOnFinite.symm fun i =>
            ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) = d := by
    ext i
    simp [Nat.div_add_mod]
  -- the sub-`n` part is one of the generators
  have hmem :
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i =>
          ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) (1 : R) ∈
        Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
          (Set.range fun β : σ → Fin n =>
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) :=
    Submodule.subset_span ⟨fun i => ⟨d i % n, Nat.mod_lt _ hn⟩, rfl⟩
  -- name the scalar, so that the `•`/`*` defeq check stays cheap
  obtain ⟨a, ha⟩ : ∃ a : (MvPolynomial.expand (σ := σ) (R := R) n).range,
      (a : MvPolynomial σ R)
        = (MvPolynomial.expand (σ := σ) (R := R) n)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => d i / n) r) :=
    ⟨⟨_, AlgHom.mem_range_self _ _⟩, rfl⟩
  have key : (MvPolynomial.monomial d r : MvPolynomial σ R)
      = (MvPolynomial.expand (σ := σ) (R := R) n)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => d i / n) r) *
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i =>
            ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) (1 : R) := by
    rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_mul_monomial, mul_one, hexp]
  rw [key, ← ha]
  exact Submodule.smul_mem _ a hmem

/-- Over the image of `MvPolynomial.expand n`, the finitely many monomials with all exponents
below `n` span the whole polynomial ring. -/
theorem MvPolynomial.span_monomial_lt_eq_top {σ R : Type*} [CommSemiring R] [Finite σ] {n : ℕ}
    (hn : 0 < n) :
    Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
      (Set.range fun β : σ → Fin n =>
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  exact MvPolynomial.induction_on' f (fun d r => MvPolynomial.monomial_mem_span_monomial_lt hn d r)
    (fun p q hp hq => Submodule.add_mem _ hp hq)

/-- `MvPolynomial.expand n` is a finite ring map for `0 < n`: the polynomial ring is spanned over
`R[X_i ^ n]` by the monomials with exponents below `n`. -/
theorem MvPolynomial.finite_expand {σ R : Type*} [CommRing R] [Finite σ] {n : ℕ} (hn : 0 < n) :
    (MvPolynomial.expand (σ := σ) (R := R) n).toRingHom.Finite := by
  classical
  -- `MvPolynomial σ R` is a finite module over the subalgebra `R[X_i ^ n]`
  have hfin : Module.Finite (MvPolynomial.expand (σ := σ) (R := R) n).range
      (MvPolynomial σ R) :=
    Module.Finite.of_fg_top (Submodule.fg_def.2 ⟨_, Set.finite_range _,
      MvPolynomial.span_monomial_lt_eq_top hn⟩)
  -- Factor `expand n` as `R[X_i] ↠ R[X_i ^ n] ↪ R[X_i]`. Going through the range keeps the
  -- `Module (MvPolynomial σ R) (MvPolynomial σ R)` diamond out of the way: instance search
  -- picks `Semiring.toModule` (plain multiplication), not the `expand`-algebra the statement
  -- means, and the two are not defeq.
  have h₁ : ((MvPolynomial.expand (σ := σ) (R := R) n).rangeRestrict.toRingHom).Finite :=
    RingHom.Finite.of_surjective _ (AlgHom.rangeRestrict_surjective _)
  have h₂ : ((MvPolynomial.expand (σ := σ) (R := R) n).range.val.toRingHom).Finite := hfin
  -- from Mathlib's `(Subalgebra.val _).comp φ.rangeRestrict = φ`, rather than by `rfl`, so the
  -- factorisation does not depend on how bundled-hom composition happens to be implemented
  have hfac : (MvPolynomial.expand (σ := σ) (R := R) n).toRingHom
      = ((MvPolynomial.expand (σ := σ) (R := R) n).range.val.toRingHom).comp
        ((MvPolynomial.expand (σ := σ) (R := R) n).rangeRestrict.toRingHom) :=
    congrArg AlgHom.toRingHom
      (MvPolynomial.expand (σ := σ) (R := R) n).val_comp_rangeRestrict.symm
  rw [hfac]
  exact RingHom.Finite.comp h₂ h₁

/-- If every coefficient of `g` has a `p ^ n`-th root in `S`, then `g(X ^ (p ^ n))`, read in
`S[X_i]`, is a `p ^ n`-th power. -/
theorem MvPolynomial.exists_pow_eq_map_expand {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : ℕ) [ExpChar S p] (n : ℕ) {g : MvPolynomial σ R}
    (hg : ∀ i ∈ g.support, ∃ d : S, d ^ p ^ n = f (g.coeff i)) :
    ∃ h : MvPolynomial σ S, h ^ p ^ n = MvPolynomial.map f (MvPolynomial.expand (p ^ n) g) := by
  classical
  -- total-ise the choice of roots, so the witness is a plain sum over `g.support`
  have hg' : ∀ i : σ →₀ ℕ, ∃ d : S, i ∈ g.support → d ^ p ^ n = f (g.coeff i) := by
    intro i
    by_cases hi : i ∈ g.support
    · obtain ⟨d, hd⟩ := hg i hi
      exact ⟨d, fun _ ↦ hd⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose d hd using hg'
  refine ⟨∑ α ∈ g.support, MvPolynomial.monomial α (d α), ?_⟩
  -- the chosen-root polynomial maps under the iterated Frobenius to `map f g`
  have hmap : MvPolynomial.map (iterateFrobenius S p n)
      (∑ α ∈ g.support, MvPolynomial.monomial α (d α)) = MvPolynomial.map f g := by
    rw [map_sum]
    conv_rhs => rw [MvPolynomial.as_sum g]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    rw [MvPolynomial.map_monomial, MvPolynomial.map_monomial, iterateFrobenius_def, hd α hα]
  -- so Mathlib's Frobenius/expand identity supplies the power, with `map_expand` moving `map`
  -- past `expand` on each side
  rw [← MvPolynomial.map_iterateFrobenius_expand (p := p) _ n, MvPolynomial.map_expand, hmap,
    ← MvPolynomial.map_expand]

namespace MvPolynomial

open _root_.MvPolynomial

section Repr

variable (σ R : Type*) [CommRing R] (n : ℕ) [NeZero n]

/-- An exponent vector `d` splits as `n • (d / n) + d % n`, with remainders in `Fin n`. -/
private noncomputable def expDivMod : (σ →₀ ℕ) ≃ (σ →₀ Fin n) × (σ →₀ ℕ) where
  toFun d := (d.mapRange (Fin.ofNat n) (Fin.ofNat_zero n), d.mapRange (· / n) (Nat.zero_div n))
  invFun βγ := βγ.1.mapRange Fin.val (Fin.val_zero n) + n • βγ.2
  left_inv d := by
    ext i
    simp [Nat.mod_add_div]
  right_inv βγ := by
    have hn : 0 < n := Nat.pos_of_neZero n
    ext i
    · simp [Nat.mod_eq_of_lt (βγ.1 i).isLt]
    · simp [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (βγ.1 i).isLt]

/-- The coordinates of a polynomial over the image of `expand n`: the coefficient at `β` collects
the monomials whose exponents are `β` modulo `n`, with these remainders removed and the
exponents divided by `n`. -/
private noncomputable def expandRepr : MvPolynomial σ R ≃+ ((σ →₀ Fin n) →₀ MvPolynomial σ R) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <| (Finsupp.domCongr (expDivMod σ n)).trans <|
    Finsupp.curryAddEquiv.trans <| Finsupp.mapRange.addEquiv AddMonoidAlgebra.coeffAddEquiv.symm

variable {σ R n}

private theorem expDivMod_nsmul_add (γ d : σ →₀ ℕ) :
    expDivMod σ n (n • γ + d) = ((expDivMod σ n d).1, γ + (expDivMod σ n d).2) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  ext i
  · simp [expDivMod]
  · simp [expDivMod, Nat.mul_add_div hn]

private theorem expandRepr_monomial (d : σ →₀ ℕ) (r : R) :
    expandRepr σ R n (monomial d r) =
      Finsupp.single (expDivMod σ n d).1 (monomial (expDivMod σ n d).2 r) := by
  simp [expandRepr, ← single_eq_monomial]

/-- The coordinates over the image of `expand n` are linear over that image. -/
private theorem _root_.MvPolynomial.expandRepr_expand_mul (a b : MvPolynomial σ R) :
    expandRepr σ R n (expand n a * b) = a • expandRepr σ R n b := by
  induction a using MvPolynomial.induction_on' with
  | monomial γ r =>
    induction b using MvPolynomial.induction_on' with
    | monomial d s =>
      rw [expand_monomial, monomial_mul_monomial, expandRepr_monomial, expDivMod_nsmul_add,
        expandRepr_monomial, Finsupp.smul_single, smul_eq_mul, monomial_mul_monomial]
    | add b₁ b₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, smul_add]
  | add a₁ a₂ h₁ h₂ => rw [map_add, add_mul, map_add, h₁, h₂, add_smul]

variable (σ R n) in
/-- **The monomial basis along `expand n`.** `R[X_i]` is free over itself along
`X_i ↦ X_i ^ n`, with basis the monomials whose exponents are all below `n`
(`TauCeti.MvPolynomial.basisExpand_apply`). -/
noncomputable def basisExpand :
    @Module.Basis (σ →₀ Fin n) (MvPolynomial σ R) (MvPolynomial σ R) _ _
      (expand n : MvPolynomial σ R →ₐ[R] _).toRingHom.toAlgebra.toModule :=
  RingHom.basisOfAddEquiv _ (expandRepr σ R n) expandRepr_expand_mul

/-- The basis vector of `basisExpand` at `β` is the monomial with exponents `β`. -/
@[simp]
theorem basisExpand_apply (β : σ →₀ Fin n) :
    basisExpand σ R n β = monomial (β.mapRange Fin.val (Fin.val_zero n)) 1 := by
  have hβ : expDivMod σ n (β.mapRange Fin.val (Fin.val_zero n)) = (β, 0) :=
    Prod.ext (by ext i; simp [expDivMod]) (by ext i; simp [expDivMod, Nat.div_eq_of_lt (β i).isLt])
  rw [basisExpand, RingHom.basisOfAddEquiv_apply, AddEquiv.symm_apply_eq, expandRepr_monomial, hβ,
    ← C_apply, C_1]

end Repr

variable {σ R : Type*} [CommRing R] {n : ℕ}

/-- **`MvPolynomial.expand n` is flat** for `0 < n`: `R[X_i]` is flat over `R[X_i]` along
`X_i ↦ X_i ^ n`. -/
theorem flat_expand (hn : 0 < n) : (expand n : MvPolynomial σ R →ₐ[R] _).toRingHom.Flat :=
  have : NeZero n := ⟨hn.ne'⟩
  RingHom.flat_of_addEquiv _ _ expandRepr_expand_mul

/-- `MvPolynomial.expand n` is of finite presentation for finitely many variables. -/
theorem finitePresentation_expand [Finite σ] (n : ℕ) :
    (expand n : MvPolynomial σ R →ₐ[R] _).toRingHom.FinitePresentation := by
  refine .of_comp_finiteType (algebraMap R (MvPolynomial σ R)) ?_
    (RingHom.finiteType_algebraMap.2 inferInstance)
  rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
  exact RingHom.finitePresentation_algebraMap.2 inferInstance

/-- **The rank of `MvPolynomial.expand n`**: for `0 < n` and finitely many variables, the rank
of `R[X_i]` over `R[X_i]` along `X_i ↦ X_i ^ n` is `n ^ Nat.card σ` at every prime. -/
theorem finrank_expand [Finite σ] (hn : 0 < n) :
    (expand n : MvPolynomial σ R →ₐ[R] _).toRingHom.finrank = fun _ ↦ n ^ Nat.card σ := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [RingHom.finrank_of_addEquiv _ _ expandRepr_expand_mul,
    Nat.card_congr Finsupp.equivFunOnFinite, Nat.card_fun, Nat.card_fin]

end MvPolynomial

end TauCeti
