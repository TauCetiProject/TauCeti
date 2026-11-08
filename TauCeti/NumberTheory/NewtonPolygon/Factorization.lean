/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.EvalAt
import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Pure slope factorisations of polynomials and restricted power series

Over any field `K` equipped with `v : AddValuation K (WithTop ℝ)`, nonzero polynomials not both
vanishing at `0` whose finite Newton slope multisets are disjoint are coprime. A *pure slope
factorisation* `Polynomial.IsPureSlopeFactorization f v g` represents a constant-one polynomial `f`
as a finitely supported product `∏ᶠ m, g m` of constant-one polynomials `g m` each pure of slope
`m`. Purity and the constant-term normalisation force `(g m).natDegree = (f.newtonSlopes v).count m`
and `g m = 1` outside `f.newtonSlopes v`, making `g` unique over any field.

When `K` is a complete ultrametric normed field whose norm comes from `v` with base `b > 1`, peeling
off the finite face at any slope threshold `σ` via Weierstrass preparation
(`TauCeti.NumberTheory.NewtonPolygon.Weierstrass`) and polynomial divisibility reflection
(`TauCeti.PowerSeries.IsDistinguished.polynomialToRestricted_dvd_iff`) constructs `g` over `K`
itself, with no splitting or discreteness hypothesis. In particular, any polynomial over `K` whose
finite Newton slopes have multiplicity one splits into linear factors over `K`.

Combining Weierstrass preparation on any closed disc of positive radius with the pure slope
factorisation of its preparation polynomial factors any nonzero restricted power series on that disc
into a restricted unit, `X ^ a` for its order `a` at zero
(`PowerSeries.order_eq_of_isUnit_X_pow_mul_finprod_eq`), and unique pairwise coprime constant-one
pure polynomial factors of slopes within the disc. In any complete normed field extension `L` of
`K`, the zeros of the series on the sphere `‖x‖ = b ^ m` inside the disc are precisely the roots of
the slope-`m` factor.

## Main definitions

* `Polynomial.IsPureSlopeFactorization f v g`: `g : ℝ → R[X]` has finite multiplicative support,
  each `g m` has constant coefficient `1` and all finite Newton slopes equal to `m`, and
  `∏ᶠ m, g m = f`.

## Main results

* `Polynomial.isCoprime_of_disjoint_newtonSlopes` and
  `Polynomial.isCoprime_of_forall_mem_newtonSlopes_eq`: nonzero polynomials over a field with
  disjoint finite slopes (not both vanishing at `0`) are coprime.
* `Polynomial.IsPureSlopeFactorization.natDegree_apply`,
  `Polynomial.IsPureSlopeFactorization.mulSupport_eq`,
  `Polynomial.IsPureSlopeFactorization.pairwise_isCoprime` and
  `Polynomial.IsPureSlopeFactorization.unique`: degree determination, support, pairwise coprimality
  and uniqueness of pure slope factorisations.
* `Polynomial.exists_mul_newtonSlopes_filter_le`: threshold factorisation `f = P * Q` separating
  finite slopes `≤ σ` from finite slopes `> σ`.
* `Polynomial.existsUnique_isPureSlopeFactorization`,
  `Polynomial.existsUnique_C_mul_finprod_eq` and
  `Polynomial.existsUnique_C_mul_X_pow_mul_finprod_eq`: existence and uniqueness of the pure slope
  factorisation over a complete ultrametric normed field.
* `Polynomial.splits_of_nodup_newtonSlopes`: a polynomial over a complete ultrametric normed field
  with distinct finite Newton slopes splits over the base field.
* `PowerSeries.existsUnique_isUnit_X_pow_mul_finprod_eq`,
  `PowerSeries.existsUnique_isUnit_X_pow_mul_finprod_eq_of_pos` and
  `PowerSeries.setOf_norm_eq_and_evalAt_eq_zero`: closed-disc pure slope factorisation of a
  restricted power series and sphere-by-sphere identification of its zeros.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
* K. S. Kedlaya, [*Newton polygons*](https://kskedlaya.org/18.787/newton-poly.pdf),
  MIT 18.787, fall 2007, §§1–2.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer, 1984,
  §5.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
-/

public section

open scoped PowerSeries
open TauCeti

/-! ### Slope coprimality and pure slope factorisations -/

namespace Polynomial

section Coprime

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

/-- Over a field, two nonzero polynomials not both vanishing at zero whose finite Newton slope
multisets are disjoint are coprime. -/
theorem isCoprime_of_disjoint_newtonSlopes {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (h0 : f.coeff 0 ≠ 0 ∨ g.coeff 0 ≠ 0)
    (hdisj : Disjoint (f.newtonSlopes v) (g.newtonSlopes v)) : IsCoprime f g := by
  refine EuclideanDomain.isCoprime_of_dvd (fun h => hf h.1) fun d hdu hd0 hdf hdg => hdu ?_
  have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  have hslopes : d.newtonSlopes v = 0 :=
    le_bot_iff.mp (hdisj (newtonSlopes_le_of_dvd (newtonPolygon_ne_top_of_ne_zero hv0 hf) hdf)
      (newtonSlopes_le_of_dvd (newtonPolygon_ne_top_of_ne_zero hv0 hg) hdg))
  have hd_coeff : d.coeff 0 ≠ 0 := by
    rcases h0 with hf0 | hg0
    · obtain ⟨q, rfl⟩ := hdf
      exact fun hd_zero => hf0 (by rw [mul_coeff_zero, hd_zero, zero_mul])
    · obtain ⟨q, rfl⟩ := hdg
      exact fun hd_zero => hg0 (by rw [mul_coeff_zero, hd_zero, zero_mul])
  have hcard := card_newtonSlopes d v hv0
  rw [hslopes, Multiset.card_zero,
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hd_coeff, Nat.sub_zero] at hcard
  obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hcard.symm
  exact (C_ne_zero.mp hd0).isUnit.map C

/-- Over a field, two nonzero pure polynomials of distinct slopes `m₁ ≠ m₂`, not both vanishing at
zero, are coprime. -/
theorem isCoprime_of_forall_mem_newtonSlopes_eq {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (h0 : f.coeff 0 ≠ 0 ∨ g.coeff 0 ≠ 0) {m₁ m₂ : ℝ}
    (hm₁ : ∀ s ∈ f.newtonSlopes v, s = m₁) (hm₂ : ∀ s ∈ g.newtonSlopes v, s = m₂)
    (hne : m₁ ≠ m₂) : IsCoprime f g :=
  isCoprime_of_disjoint_newtonSlopes v hf hg h0 <|
    Multiset.disjoint_left.mpr fun hs₁ hs₂ => hne ((hm₁ _ hs₁).symm.trans (hm₂ _ hs₂))

end Coprime

section PureSlopeFactorization

/-- A family `g : ℝ → R[X]` is a *pure slope factorisation* of `f` for `v` if `g` has finite
multiplicative support, each `g m` has constant coefficient `1` and all finite Newton slopes equal
to `m`, and `∏ᶠ m, g m = f`. -/
structure IsPureSlopeFactorization {R : Type*} [CommRing R] (f : R[X])
    (v : AddValuation R (WithTop ℝ)) (g : ℝ → R[X]) : Prop where
  /-- Only finitely many factors `g m` differ from `1`. -/
  finite_mulSupport : (Function.mulSupport g).Finite
  /-- Every factor is normalised to have constant coefficient `1`. -/
  coeff_zero : ∀ m, (g m).coeff 0 = 1
  /-- Every finite Newton slope of `g m` equals `m`. -/
  newtonSlopes_eq : ∀ m, ∀ s ∈ (g m).newtonSlopes v, s = m
  /-- The finite product of the family `g` recovers `f`. -/
  finprod_eq : ∏ᶠ m, g m = f

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] {f f₁ f₂ : R[X]}
  {v : AddValuation R (WithTop ℝ)} {g g₁ g₂ : ℝ → R[X]}

/-- Unfolded characterisation of `Polynomial.IsPureSlopeFactorization`. -/
theorem isPureSlopeFactorization_iff :
    f.IsPureSlopeFactorization v g ↔
      (Function.mulSupport g).Finite ∧ (∀ m, (g m).coeff 0 = 1) ∧
        (∀ m, ∀ s ∈ (g m).newtonSlopes v, s = m) ∧ ∏ᶠ m, g m = f :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

namespace IsPureSlopeFactorization

/-- A polynomial admitting a pure slope factorisation has constant coefficient `1`. -/
theorem coeff_zero_eq_one (hg : f.IsPureSlopeFactorization v g) : f.coeff 0 = 1 := by
  rw [← hg.finprod_eq, ← constantCoeff_apply, map_finprod constantCoeff hg.finite_mulSupport]
  exact finprod_eq_one_of_forall_eq_one hg.coeff_zero

/-- The existence of a real additive valuation makes the coefficient ring nontrivial, so every
factor `g m` is nonzero. -/
theorem apply_ne_zero (hg : f.IsPureSlopeFactorization v g) (m : ℝ) : g m ≠ 0 := by
  intro h0
  have h10 : (1 : R) = 0 := by rw [← hg.coeff_zero m, h0, Polynomial.coeff_zero]
  have hv1 : v 1 = ⊤ := by rw [h10, v.map_zero]
  rw [v.map_one] at hv1
  exact WithTop.zero_ne_top hv1

/-- A polynomial admitting a pure slope factorisation is nonzero. -/
theorem ne_zero (hg : f.IsPureSlopeFactorization v g) : f ≠ 0 := by
  intro h0
  have h10 : (1 : R) = 0 := by rw [← hg.coeff_zero_eq_one, h0, Polynomial.coeff_zero]
  have hv1 : v 1 = ⊤ := by rw [h10, v.map_zero]
  rw [v.map_one] at hv1
  exact WithTop.zero_ne_top hv1

/-- Every factor `g m` of a pure slope factorisation has a nonempty Newton polygon. -/
theorem newtonPolygon_ne_top (hg : f.IsPureSlopeFactorization v g) (m : ℝ) :
    (g m).newtonPolygon v ≠ ⊤ := by
  intro htop
  have hle := (g m).newtonPolygon_le v 0
  rw [htop, hg.coeff_zero m, v.map_one] at hle
  exact WithTop.zero_ne_top (top_le_iff.mp hle)

/-- Every factor `g m` divides `f`. -/
theorem dvd (hg : f.IsPureSlopeFactorization v g) (m : ℝ) : g m ∣ f :=
  hg.finprod_eq ▸ finprod_mem_dvd m hg.finite_mulSupport

/-- The constant family `1` is a pure slope factorisation of `1`. -/
theorem one (v : AddValuation R (WithTop ℝ)) : (1 : R[X]).IsPureSlopeFactorization v 1 :=
  ⟨by simp, fun _ => by simp, fun _ _ hs => by
    rw [Pi.one_apply, ← C_1, newtonSlopes_C] at hs
    exact (Multiset.notMem_zero _ hs).elim, finprod_one⟩

/-- A constant-one polynomial pure of slope `m₀` has pure slope factorisation
`Function.update 1 m₀ f`. -/
theorem of_forall_mem_newtonSlopes_eq (hf0 : f.coeff 0 = 1) {m₀ : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m₀) :
    f.IsPureSlopeFactorization v (Function.update 1 m₀ f) := by
  refine ⟨(Set.finite_singleton m₀).subset fun m hm' => ?_, fun m => ?_, fun m s hs => ?_, ?_⟩
  · by_contra hne
    exact hm' (Function.update_of_ne hne f (1 : ℝ → R[X]))
  · rcases eq_or_ne m m₀ with rfl | hne
    · simpa using hf0
    · simp [Function.update_of_ne hne]
  · rcases eq_or_ne m m₀ with rfl | hne
    · exact hm s (by simpa using hs)
    · rw [Function.update_of_ne hne, Pi.one_apply, ← C_1, newtonSlopes_C] at hs
      exact (Multiset.notMem_zero _ hs).elim
  · refine (finprod_eq_single _ m₀ fun m hne => ?_).trans (by simp)
    exact Function.update_of_ne hne f (1 : ℝ → R[X])

/-- Pointwise multiplication of pure slope factorisations gives a pure slope factorisation of the
product. -/
theorem mul (hg₁ : f₁.IsPureSlopeFactorization v g₁) (hg₂ : f₂.IsPureSlopeFactorization v g₂) :
    (f₁ * f₂).IsPureSlopeFactorization v (g₁ * g₂) := by
  have hfin : (Function.mulSupport (g₁ * g₂)).Finite :=
    (hg₁.finite_mulSupport.union hg₂.finite_mulSupport).subset (Function.mulSupport_mul g₁ g₂)
  refine ⟨hfin, fun m => ?_, fun m s hs => ?_, ?_⟩
  · rw [Pi.mul_apply, mul_coeff_zero, hg₁.coeff_zero m, hg₂.coeff_zero m, mul_one]
  · rw [Pi.mul_apply, newtonSlopes_mul _ _ v (hg₁.newtonPolygon_ne_top m)
      (hg₂.newtonPolygon_ne_top m), Multiset.mem_add] at hs
    exact hs.elim (hg₁.newtonSlopes_eq m s) (hg₂.newtonSlopes_eq m s)
  · simp_rw [Pi.mul_apply]
    rw [finprod_mul_distrib hg₁.finite_mulSupport hg₂.finite_mulSupport, hg₁.finprod_eq,
      hg₂.finprod_eq]

/-- A pure slope factorisation is preserved by a ring homomorphism compatible with the
valuations. -/
theorem map (hg : f.IsPureSlopeFactorization v g) (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    (hφ : ∀ x, w (φ x) = v x) :
    (f.map φ).IsPureSlopeFactorization w (fun m => (g m).map φ) := by
  have hfin : (Function.mulSupport fun m => (g m).map φ).Finite :=
    hg.finite_mulSupport.subset fun m hm hgm => hm (by simp [hgm])
  refine ⟨hfin, fun m => by simp [hg.coeff_zero m], fun m s hs => ?_, ?_⟩
  · rw [newtonSlopes_map (g m) v φ hφ] at hs
    exact hg.newtonSlopes_eq m s hs
  · rw [← hg.finprod_eq, ← coe_mapRingHom, map_finprod (mapRingHom φ) hg.finite_mulSupport]

section Nondegenerate

variable (hv : ∀ x, v x = ⊤ → x = 0)
include hv

/-- Each factor `g m` has finite slope multiset `Multiset.replicate (g m).natDegree m`. -/
theorem newtonSlopes_apply (hg : f.IsPureSlopeFactorization v g) (m : ℝ) :
    (g m).newtonSlopes v = Multiset.replicate (g m).natDegree m := by
  have hc0 : (g m).coeff 0 ≠ 0 := by
    rw [hg.coeff_zero m]
    exact fun h => WithTop.zero_ne_top (v.map_one.symm.trans (h ▸ v.map_zero))
  have hcard : ((g m).newtonSlopes v).card = (g m).natDegree := by
    rw [card_newtonSlopes (g m) v hv,
      natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hc0, Nat.sub_zero]
  rw [← hcard, Multiset.eq_replicate_card]
  exact hg.newtonSlopes_eq m

/-- The degree of the slope-`m` factor is the multiplicity of `m` in `f.newtonSlopes v`. -/
theorem natDegree_apply (hg : f.IsPureSlopeFactorization v g) (m : ℝ) :
    (g m).natDegree = (f.newtonSlopes v).count m := by
  have hfin := hg.finite_mulSupport
  have hslopes : f.newtonSlopes v =
      ∑ x ∈ hfin.toFinset, Multiset.replicate (g x).natDegree x := by
    calc f.newtonSlopes v = (∏ᶠ x, g x).newtonSlopes v := by rw [hg.finprod_eq]
      _ = ∑ x ∈ hfin.toFinset, (g x).newtonSlopes v :=
          newtonSlopes_finprod v g hfin fun x _ => hg.newtonPolygon_ne_top x
      _ = ∑ x ∈ hfin.toFinset, Multiset.replicate (g x).natDegree x :=
          Finset.sum_congr rfl fun x _ => hg.newtonSlopes_apply hv x
  rw [hslopes, Multiset.count_sum']
  by_cases hm : m ∈ hfin.toFinset
  · rw [Finset.sum_eq_single m
      (fun x _ hxm => Multiset.count_eq_zero.mpr fun h => hxm (Multiset.eq_of_mem_replicate h).symm)
      (fun h => (h hm).elim), Multiset.count_replicate_self]
  · have hgm : g m = 1 := not_not.mp fun hne => hm (hfin.mem_toFinset.mpr hne)
    rw [hgm, natDegree_one, eq_comm]
    refine Finset.sum_eq_zero fun x _ => Multiset.count_eq_zero.mpr fun h => hm ?_
    rwa [Multiset.eq_of_mem_replicate h]

/-- Outside the finite slopes of `f`, the factor `g m` is `1`. -/
theorem apply_eq_one_iff (hg : f.IsPureSlopeFactorization v g) {m : ℝ} :
    g m = 1 ↔ m ∉ f.newtonSlopes v := by
  rw [← Multiset.count_eq_zero, ← hg.natDegree_apply hv m]
  refine ⟨fun h => by simp [h], fun hdeg => ?_⟩
  rw [eq_C_of_natDegree_eq_zero hdeg, hg.coeff_zero m, C_1]

/-- The multiplicative support of `g` is the set of finite Newton slopes of `f`. -/
theorem mulSupport_eq (hg : f.IsPureSlopeFactorization v g) :
    Function.mulSupport g = {m : ℝ | m ∈ f.newtonSlopes v} := by
  ext m
  simp only [Function.mem_mulSupport, Set.mem_ofPred_eq, ne_eq, hg.apply_eq_one_iff hv, not_not]

/-- The product of `g` over the finset of distinct finite Newton slopes of `f` equals `f`. -/
theorem prod_toFinset_eq (hg : f.IsPureSlopeFactorization v g) :
    ∏ m ∈ (f.newtonSlopes v).toFinset, g m = f := by
  refine (finprod_eq_prod_of_mulSupport_subset g ?_).symm.trans hg.finprod_eq
  intro m hm
  rw [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Set.ext_iff.mp (hg.mulSupport_eq hv) m).mp hm

end Nondegenerate

end IsPureSlopeFactorization

end CommRing

section Field

variable {K : Type*} [Field K] {f : K[X]} {v : AddValuation K (WithTop ℝ)} {g g₁ g₂ : ℝ → K[X]}

namespace IsPureSlopeFactorization

/-- Distinct factors of a pure slope factorisation over a field are coprime. -/
theorem pairwise_isCoprime (hg : f.IsPureSlopeFactorization v g) :
    Pairwise fun m₁ m₂ => IsCoprime (g m₁) (g m₂) := fun m₁ m₂ hne =>
  isCoprime_of_forall_mem_newtonSlopes_eq v (hg.apply_ne_zero m₁) (hg.apply_ne_zero m₂)
    (.inl (by simp [hg.coeff_zero m₁])) (hg.newtonSlopes_eq m₁) (hg.newtonSlopes_eq m₂) hne

/-- Over a field, a polynomial has at most one pure slope factorisation. -/
theorem unique (hg₁ : f.IsPureSlopeFactorization v g₁)
    (hg₂ : f.IsPureSlopeFactorization v g₂) : g₁ = g₂ := by
  have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  funext m
  by_cases hm : m ∈ (f.newtonSlopes v).toFinset
  · set T := (f.newtonSlopes v).toFinset
    have hprod₁ : g₁ m * ∏ x ∈ T.erase m, g₁ x = f := by
      rw [Finset.mul_prod_erase T g₁ hm, hg₁.prod_toFinset_eq hv0]
    have hprod₂ : g₂ m * ∏ x ∈ T.erase m, g₂ x = f := by
      rw [Finset.mul_prod_erase T g₂ hm, hg₂.prod_toFinset_eq hv0]
    have hcop₁₂ : IsCoprime (g₁ m) (∏ x ∈ T.erase m, g₂ x) :=
      IsCoprime.prod_right fun x hx =>
        isCoprime_of_forall_mem_newtonSlopes_eq v (hg₁.apply_ne_zero m) (hg₂.apply_ne_zero x)
          (.inl (by simp [hg₁.coeff_zero m])) (hg₁.newtonSlopes_eq m) (hg₂.newtonSlopes_eq x)
          (Finset.ne_of_mem_erase hx).symm
    have hcop₂₁ : IsCoprime (g₂ m) (∏ x ∈ T.erase m, g₁ x) :=
      IsCoprime.prod_right fun x hx =>
        isCoprime_of_forall_mem_newtonSlopes_eq v (hg₂.apply_ne_zero m) (hg₁.apply_ne_zero x)
          (.inl (by simp [hg₂.coeff_zero m])) (hg₂.newtonSlopes_eq m) (hg₁.newtonSlopes_eq x)
          (Finset.ne_of_mem_erase hx).symm
    have hdvd₁₂ : g₁ m ∣ g₂ m := hcop₁₂.dvd_of_dvd_mul_right ⟨∏ x ∈ T.erase m, g₁ x,
      hprod₂.trans hprod₁.symm⟩
    have hdvd₂₁ : g₂ m ∣ g₁ m := hcop₂₁.dvd_of_dvd_mul_right ⟨∏ x ∈ T.erase m, g₂ x,
      hprod₁.trans hprod₂.symm⟩
    obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁₂ hdvd₂₁
    obtain ⟨c, -, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    rw [← hcu] at hu
    have hc1 : c = 1 := by
      have h0 := congrArg (coeff · 0) hu
      simpa [mul_coeff_zero, hg₁.coeff_zero m, hg₂.coeff_zero m] using h0
    simpa [hc1] using hu
  · have hm' : m ∉ f.newtonSlopes v := by simpa [Multiset.mem_toFinset] using hm
    rw [(hg₁.apply_eq_one_iff hv0).mpr hm', (hg₂.apply_eq_one_iff hv0).mpr hm']

end IsPureSlopeFactorization

/-- Over a field, only the constant family `1` is a pure slope factorisation of `1`. -/
@[simp]
theorem isPureSlopeFactorization_one_iff :
    (1 : K[X]).IsPureSlopeFactorization v g ↔ g = 1 :=
  ⟨fun h => h.unique (.one v), fun h => h ▸ .one v⟩

end Field

end PureSlopeFactorization

/-! ### Existence of pure slope factorisations -/

section Complete

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Threshold slope factorisation.** Over a complete ultrametric normed field, any polynomial `f`
with `f.coeff 0 = 1` factors at any real threshold `σ` as `f = P * Q`, where `P` and `Q` are
coprime constant-one polynomials carrying respectively the finite slopes `≤ σ` and `> σ` of `f`. -/
theorem exists_mul_newtonSlopes_filter_le {f : K[X]} (hf0 : f.coeff 0 = 1) (σ : ℝ) :
    ∃ P Q : K[X], P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧ IsCoprime P Q ∧ P * Q = f ∧
      P.newtonSlopes v = (f.newtonSlopes v).filter (· ≤ σ) ∧
      Q.newtonSlopes v = (f.newtonSlopes v).filter (σ < ·) := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hf_ne : f ≠ 0 := fun h => one_ne_zero (hf0.symm.trans (by simp [h]))
  obtain ⟨l, j, hface⟩ := exists_isFiniteFace_newtonPolygon
    (newtonPolygon_ne_top_of_ne_zero (fun _ => v.top_iff.mp) hf_ne) σ
  have hfd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j (f : K⟦X⟧) :=
    PowerSeries.isDistinguished_of_isFiniteFace v hb hv
      (TauCeti.PowerSeries.isRestricted_polynomial f) (f.newtonPolygon_coe v ▸ hface)
  obtain ⟨e, ω, he, hωm, heω⟩ := hfd.exists_isUnit_isMonicOfDegree_mul_eq
    hfd.coeff_ne_zero.isUnit hc (TauCeti.PowerSeries.isRestricted_polynomial f)
  have hωd : TauCeti.PowerSeries.IsDistinguished (b ^ σ) j (ω : K⟦X⟧) :=
    TauCeti.PowerSeries.IsDistinguished.of_isUnit_mul (heω.symm ▸ hfd) hc he
  have hdvd_sub : TauCeti.PowerSeries.polynomialToRestricted (b ^ σ) ω ∣
      TauCeti.PowerSeries.polynomialToRestricted (b ^ σ) f :=
    ⟨e, Subtype.ext (by simpa [mul_comm] using heω.symm)⟩
  obtain ⟨q, hfq⟩ := (hωd.polynomialToRestricted_dvd_iff hc hωm f).mp hdvd_sub
  have hωq0 : ω.coeff 0 * q.coeff 0 = 1 := by rw [← mul_coeff_zero, ← hfq, hf0]
  have hω0 : ω.coeff 0 ≠ 0 := left_ne_zero_of_mul_eq_one hωq0
  set P := C (ω.coeff 0)⁻¹ * ω
  set Q := C (ω.coeff 0) * q
  have hP0 : P.coeff 0 = 1 := by simp [P, inv_mul_cancel₀ hω0]
  have hQ0 : Q.coeff 0 = 1 := by simp [Q, hωq0]
  have hPQ : P * Q = f := by
    calc P * Q = C ((ω.coeff 0)⁻¹ * ω.coeff 0) * (ω * q) := by simp only [P, Q, map_mul]; ring
      _ = f := by rw [inv_mul_cancel₀ hω0, map_one, one_mul, hfq]
  have hP_slopes : P.newtonSlopes v = (f.newtonSlopes v).filter (· ≤ σ) := by
    rw [newtonSlopes_C_mul ω v (v.ne_top_iff.mpr (inv_ne_zero hω0))]
    exact newtonSlopes_eq_filter_le_of_isFiniteFace v hb hv hface he hωm.natDegree_eq.le heω
  have hPne : P ≠ 0 := fun h => one_ne_zero (hP0.symm.trans (by simp [h]))
  have hQne : Q ≠ 0 := fun h => one_ne_zero (hQ0.symm.trans (by simp [h]))
  have hQ_slopes : Q.newtonSlopes v = (f.newtonSlopes v).filter (σ < ·) := by
    have hsum := newtonSlopes_mul P Q v
      (newtonPolygon_ne_top_of_ne_zero (fun _ => v.top_iff.mp) hPne)
      (newtonPolygon_ne_top_of_ne_zero (fun _ => v.top_iff.mp) hQne)
    rw [hPQ, hP_slopes] at hsum
    have hsplit : f.newtonSlopes v =
        (f.newtonSlopes v).filter (· ≤ σ) + (f.newtonSlopes v).filter (σ < ·) := by
      conv_lhs => rw [← Multiset.filter_add_not (· ≤ σ) (f.newtonSlopes v)]
      congr 2
      ext x
      exact not_le
    exact add_left_cancel (hsum.symm.trans hsplit)
  refine ⟨P, Q, hP0, hQ0, isCoprime_of_disjoint_newtonSlopes v hPne hQne
    (.inl (by simp [hP0])) ?_, hPQ, hP_slopes, hQ_slopes⟩
  rw [hP_slopes, hQ_slopes, Multiset.disjoint_left]
  exact fun hm₁ hm₂ => (Multiset.mem_filter.mp hm₁).2.not_gt (Multiset.mem_filter.mp hm₂).2

/-- **Existence of the pure slope factorisation.** Over a complete ultrametric normed field, every
polynomial `f` with `f.coeff 0 = 1` admits a pure slope factorisation over `K`. -/
theorem exists_isPureSlopeFactorization {f : K[X]} (hf0 : f.coeff 0 = 1) :
    ∃ g : ℝ → K[X], f.IsPureSlopeFactorization v g := by
  suffices ∀ d : ℕ, ∀ f : K[X], f.natDegree = d → f.coeff 0 = 1 →
      ∃ g : ℝ → K[X], f.IsPureSlopeFactorization v g from this f.natDegree f rfl hf0
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro f hdeg hf0
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · have hf1 : f = 1 := by rw [eq_C_of_natDegree_eq_zero hdeg, hf0, C_1]
      exact ⟨1, hf1 ▸ .one v⟩
    · have hf_ne : f ≠ 0 := fun h => one_ne_zero (hf0.symm.trans (by simp [h]))
      have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
      have htr0 : f.natTrailingDegree = 0 :=
        natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [hf0])
      have h0_edge : 0 ∈ finiteEdges (f.newtonPolygon v) := by
        rw [finiteEdges_newtonPolygon_of_ne_top f v
          (v.ne_top_iff.mpr (trailingCoeff_ne_zero.mpr hf_ne))
          (v.ne_top_iff.mpr (leadingCoeff_ne_zero.mpr hf_ne))]
        exact ⟨htr0.le, hdeg ▸ hd_pos⟩
      set σ := unitSlope (f.newtonPolygon v) 0
      have hmin : ∀ m ∈ f.newtonSlopes v, σ ≤ m := by
        rintro m hm
        obtain ⟨i, hi, rfl⟩ := (f.mem_newtonSlopes v).mp hm
        exact (f.isConvexSeq_newtonPolygon v).monotoneOn h0_edge hi (Nat.zero_le i)
      obtain ⟨P, Q, hP0, hQ0, -, hPQ, hP_slopes, -⟩ :=
        exists_mul_newtonSlopes_filter_le v hb hv hf0 σ
      have hP_pure : ∀ s ∈ P.newtonSlopes v, s = σ := by
        intro s hs
        rw [hP_slopes, Multiset.mem_filter] at hs
        exact le_antisymm hs.2 (hmin s hs.1)
      have hσ_mem : σ ∈ P.newtonSlopes v := by
        rw [hP_slopes, Multiset.mem_filter]
        exact ⟨(f.mem_newtonSlopes v).mpr ⟨0, h0_edge, rfl⟩, le_rfl⟩
      have hP_pos : 0 < P.natDegree := by
        have hP_card := card_newtonSlopes P v hv0
        rw [natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [hP0]),
          Nat.sub_zero] at hP_card
        exact hP_card ▸ Multiset.card_pos_iff_exists_mem.mpr ⟨σ, hσ_mem⟩
      have hP_ne : P ≠ 0 := fun h => one_ne_zero (hP0.symm.trans (by simp [h]))
      have hQ_ne : Q ≠ 0 := fun h => one_ne_zero (hQ0.symm.trans (by simp [h]))
      have hQ_lt : Q.natDegree < d := by
        have hdeg_mul := natDegree_mul hP_ne hQ_ne
        rw [hPQ, hdeg] at hdeg_mul
        omega
      obtain ⟨gQ, hgQ⟩ := ih Q.natDegree hQ_lt Q rfl hQ0
      exact ⟨Function.update (1 : ℝ → K[X]) σ P * gQ,
        hPQ ▸ (IsPureSlopeFactorization.of_forall_mem_newtonSlopes_eq hP0 hP_pure).mul hgQ⟩

/-- **Unique existence of the pure slope factorisation.** Over a complete ultrametric normed field,
every polynomial `f` with `f.coeff 0 = 1` has a unique pure slope factorisation over `K`. -/
theorem existsUnique_isPureSlopeFactorization {f : K[X]} (hf0 : f.coeff 0 = 1) :
    ∃! g : ℝ → K[X], f.IsPureSlopeFactorization v g := by
  obtain ⟨g, hg⟩ := exists_isPureSlopeFactorization v hb hv hf0
  exact ⟨g, hg, fun g' hg' => hg'.unique hg⟩

/-- Over a complete ultrametric normed field, any polynomial `f` with nonzero constant coefficient
factors uniquely as `C (f.coeff 0) * ∏ᶠ m, g m`, where `g` is a family of constant-one pure
factors. -/
theorem existsUnique_C_mul_finprod_eq {f : K[X]} (hf0 : f.coeff 0 ≠ 0) :
    ∃! g : ℝ → K[X], (Function.mulSupport g).Finite ∧ (∀ m, (g m).coeff 0 = 1) ∧
      (∀ m, ∀ s ∈ (g m).newtonSlopes v, s = m) ∧ C (f.coeff 0) * ∏ᶠ m, g m = f := by
  have hnorm0 : (C (f.coeff 0)⁻¹ * f).coeff 0 = 1 := by simp [inv_mul_cancel₀ hf0]
  obtain ⟨g, hg, huniq⟩ := existsUnique_isPureSlopeFactorization v hb hv hnorm0
  refine ⟨g, ⟨hg.finite_mulSupport, hg.coeff_zero, hg.newtonSlopes_eq, ?_⟩, fun g' hg' => huniq g'
    ⟨hg'.1, hg'.2.1, hg'.2.2.1, ?_⟩⟩
  · rw [hg.finprod_eq, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one, one_mul]
  · calc ∏ᶠ m, g' m = C ((f.coeff 0)⁻¹ * f.coeff 0) * ∏ᶠ m, g' m := by
          rw [inv_mul_cancel₀ hf0, map_one, one_mul]
      _ = C (f.coeff 0)⁻¹ * f := by rw [map_mul, mul_assoc, hg'.2.2.2]

/-- Over a complete ultrametric normed field, any nonzero polynomial `f` factors uniquely as
`C f.trailingCoeff * X ^ f.natTrailingDegree * ∏ᶠ m, g m`, where `g` is a family of constant-one
pure factors. -/
theorem existsUnique_C_mul_X_pow_mul_finprod_eq {f : K[X]} (hf : f ≠ 0) :
    ∃! g : ℝ → K[X], (Function.mulSupport g).Finite ∧ (∀ m, (g m).coeff 0 = 1) ∧
      (∀ m, ∀ s ∈ (g m).newtonSlopes v, s = m) ∧
      C f.trailingCoeff * X ^ f.natTrailingDegree * ∏ᶠ m, g m = f := by
  obtain ⟨q, hfq⟩ :=
    (X_pow_dvd_iff (f := f)).mpr fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 = f.trailingCoeff := by
    have h : (X ^ f.natTrailingDegree * q).coeff (0 + f.natTrailingDegree) = f.trailingCoeff := by
      rw [zero_add, ← hfq, trailingCoeff]
    rwa [coeff_X_pow_mul] at h
  have htr : f.trailingCoeff ≠ 0 := trailingCoeff_ne_zero.mpr hf
  set f₀ := C f.trailingCoeff⁻¹ * q
  have hf₀_0 : f₀.coeff 0 = 1 := by simp [f₀, hq0, inv_mul_cancel₀ htr]
  obtain ⟨g, hg, huniq⟩ := existsUnique_isPureSlopeFactorization v hb hv hf₀_0
  have hrearr : C f.trailingCoeff * X ^ f.natTrailingDegree * f₀ = f := by
    calc C f.trailingCoeff * X ^ f.natTrailingDegree * f₀
        = X ^ f.natTrailingDegree * (C (f.trailingCoeff * f.trailingCoeff⁻¹) * q) := by
          simp only [f₀, map_mul]
          ring
      _ = f := by rw [mul_inv_cancel₀ htr, map_one, one_mul, ← hfq]
  have hmul_eq (P : K[X]) :
      C f.trailingCoeff * X ^ f.natTrailingDegree * P = f ↔ P = f₀ := by
    refine ⟨fun h => ?_, fun h => h ▸ hrearr⟩
    have hX : C f.trailingCoeff * X ^ f.natTrailingDegree ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr htr) (pow_ne_zero _ X_ne_zero)
    exact mul_left_cancel₀ hX (h.trans hrearr.symm)
  refine ⟨g, ⟨hg.finite_mulSupport, hg.coeff_zero, hg.newtonSlopes_eq,
    (hmul_eq _).mpr hg.finprod_eq⟩, fun g' hg' =>
      huniq g' ⟨hg'.1, hg'.2.1, hg'.2.2.1, (hmul_eq _).mp hg'.2.2.2⟩⟩

/-- **Distinct-slopes splitting theorem.** Over a complete ultrametric normed field, any polynomial
whose finite Newton slopes have multiplicity one splits into linear factors over the base field. -/
theorem splits_of_nodup_newtonSlopes {f : K[X]} (hf : (f.newtonSlopes v).Nodup) : f.Splits := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Splits.zero
  have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  obtain ⟨g, ⟨hfin, hc0, hslopes, hprod⟩, -⟩ :=
    existsUnique_C_mul_X_pow_mul_finprod_eq v hb hv hf0
  set f₀ := ∏ᶠ m, g m
  have hg_fact : f₀.IsPureSlopeFactorization v g := ⟨hfin, hc0, hslopes, rfl⟩
  have hf₀_slopes : f₀.newtonSlopes v = f.newtonSlopes v := by
    rw [← hprod, mul_assoc,
      newtonSlopes_C_mul _ v (v.ne_top_iff.mpr (trailingCoeff_ne_zero.mpr hf0)),
      newtonSlopes_X_pow_mul]
  rw [← hprod, ← hg_fact.prod_toFinset_eq hv0]
  refine ((Splits.C f.trailingCoeff).mul (Splits.X.pow f.natTrailingDegree)).mul ?_
  refine Splits.prod fun m _ => Splits.of_natDegree_le_one ?_
  rw [hg_fact.natDegree_apply hv0 m, hf₀_slopes]
  exact Multiset.nodup_iff_count_le_one.mp hf m

end Complete

end Polynomial

/-! ### Closed-disc pure slope factorisation of restricted power series -/

namespace PowerSeries

section DiscFactorization

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv in
/-- Any factorisation `f = u' * (X ^ a' * ∏ᶠ m, g' m)` on `‖x‖ ≤ b ^ σ` with pure factors of
slopes `≤ σ` induces a monic Weierstrass preparation of `f` at `b ^ σ`. -/
private theorem exists_monic_preparation_of_X_pow_mul_finprod {f : K⟦X⟧} {σ : ℝ}
    {u' : IsRestricted.subring (R := K) (b ^ σ)} (hu' : IsUnit u') {a' : ℕ}
    {g' : ℝ → Polynomial K} (hfin' : (Function.mulSupport g').Finite)
    (hc0' : ∀ m, (g' m).coeff 0 = 1) (hslopes' : ∀ m, ∀ s ∈ (g' m).newtonSlopes v, s = m)
    (hg_le' : ∀ m ∈ Function.mulSupport g', m ≤ σ)
    (hmul' : (u' : K⟦X⟧) * (((Polynomial.X ^ a' * ∏ᶠ m, g' m : Polynomial K) : K⟦X⟧)) = f) :
    ∃ (e' : IsRestricted.subring (R := K) (b ^ σ)) (ω' : Polynomial K),
      IsUnit e' ∧ ω'.Monic ∧ TauCeti.PowerSeries.IsDistinguished (b ^ σ) ω'.natDegree f ∧
      (e' : K⟦X⟧) * (ω' : K⟦X⟧) = f ∧ ω'.natTrailingDegree = a' ∧
      Polynomial.C ω'.trailingCoeff * Polynomial.X ^ ω'.natTrailingDegree * ∏ᶠ m, g' m = ω' := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hg'_fact : (∏ᶠ m, g' m).IsPureSlopeFactorization v g' := ⟨hfin', hc0', hslopes', rfl⟩
  set Q' : Polynomial K := Polynomial.X ^ a' * ∏ᶠ m, g' m
  have hQ'_ne : Q' ≠ 0 := mul_ne_zero (pow_ne_zero a' Polynomial.X_ne_zero) hg'_fact.ne_zero
  set lc' := Q'.leadingCoeff
  have hlc' : lc' ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ'_ne
  set ω' : Polynomial K := Polynomial.C lc'⁻¹ * Q'
  have hω'_monic : ω'.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc']
  have hω'_slopes : ∀ s ∈ ω'.newtonSlopes v, s ≤ σ := by
    intro s hs
    rw [Polynomial.newtonSlopes_C_mul _ v (v.ne_top_iff.mpr (inv_ne_zero hlc')),
      Polynomial.newtonSlopes_X_pow_mul,
      Polynomial.newtonSlopes_finprod v g' hfin' fun m _ => hg'_fact.newtonPolygon_ne_top m,
      Multiset.mem_sum] at hs
    obtain ⟨m, hm, hsm⟩ := hs
    exact hslopes' m s hsm ▸ hg_le' m (hfin'.mem_toFinset.mp hm)
  have hω'_dist := (hω'_monic.isDistinguished_iff_forall_mem_newtonSlopes_le v hb hv).mpr
    hω'_slopes
  set e' : IsRestricted.subring (R := K) (b ^ σ) :=
    u' * TauCeti.PowerSeries.polynomialToRestricted (b ^ σ) (Polynomial.C lc')
  have he' : IsUnit e' := hu'.mul
    ((hlc'.isUnit.map Polynomial.C).map (TauCeti.PowerSeries.polynomialToRestricted (b ^ σ)))
  have he'ω' : (e' : K⟦X⟧) * (ω' : K⟦X⟧) = f := by
    calc (e' : K⟦X⟧) * (ω' : K⟦X⟧)
        = (u' : K⟦X⟧) * ((Polynomial.C (lc' * lc'⁻¹) * Q' : Polynomial K) : K⟦X⟧) := by
          simp only [e', ω', Subring.coe_mul, TauCeti.PowerSeries.coe_polynomialToRestricted,
            Polynomial.coe_mul, map_mul]
          ring
      _ = f := by rw [mul_inv_cancel₀ hlc', map_one, one_mul, hmul']
  have hf_dist' : TauCeti.PowerSeries.IsDistinguished (b ^ σ) ω'.natDegree f := by
    have hd' := (TauCeti.PowerSeries.isDistinguished_zero_of_isUnit hc he').mul hω'_dist hc
      (norm_mul _ _)
    rwa [zero_add, he'ω'] at hd'
  have ha_eq : ω'.natTrailingDegree = a' := by
    rw [Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.mpr (inv_ne_zero hlc')) hQ'_ne,
      Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [hlc']), zero_add,
      Polynomial.natTrailingDegree_mul (pow_ne_zero a' Polynomial.X_ne_zero) hg'_fact.ne_zero,
      Polynomial.natTrailingDegree_X_pow,
      Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
        (by simp [hg'_fact.coeff_zero_eq_one]), add_zero]
  have htr'_eq : ω'.trailingCoeff = lc'⁻¹ := by
    have hQa : Q'.coeff a' = 1 := by
      have h : (Polynomial.X ^ a' * ∏ᶠ m, g' m).coeff (0 + a') = Q'.coeff a' := by rw [zero_add]
      rw [← h, Polynomial.coeff_X_pow_mul, hg'_fact.coeff_zero_eq_one]
    rw [Polynomial.trailingCoeff, ha_eq, Polynomial.coeff_C_mul, hQa, mul_one]
  exact ⟨e', ω', he', hω'_monic, hf_dist', he'ω', ha_eq, by rw [htr'_eq, ha_eq, mul_assoc]⟩

section CompleteBase

variable [CompleteSpace K]
include hb hv

/-- **Closed-disc pure slope factorisation of a restricted power series.** Over a complete
ultrametric normed field `K`, any nonzero power series `f` restricted at the radius `b ^ σ` factors
uniquely as `f = u * (X ^ a * ∏ᶠ m, g m)`, where `u` is a unit of the ring of series restricted at
`b ^ σ`, `a : ℕ` is the order of vanishing of `f` at zero
(`PowerSeries.order_eq_of_isUnit_X_pow_mul_finprod_eq`), and `g : ℝ → K[X]` is a finitely
supported family of constant-one pure polynomials of slopes `m ≤ σ`. -/
theorem existsUnique_isUnit_X_pow_mul_finprod_eq {f : K⟦X⟧} {σ : ℝ}
    (hfr : f.IsRestricted (b ^ σ)) (hf0 : f ≠ 0) :
    ∃! p : IsRestricted.subring (R := K) (b ^ σ) × ℕ × (ℝ → Polynomial K),
      IsUnit p.1 ∧ (Function.mulSupport p.2.2).Finite ∧
      (∀ m, (p.2.2 m).coeff 0 = 1) ∧
      (∀ m, ∀ s ∈ (p.2.2 m).newtonSlopes v, s = m) ∧
      (∀ m ∈ Function.mulSupport p.2.2, m ≤ σ) ∧
      (p.1 : K⟦X⟧) * (((Polynomial.X ^ p.2.1 * ∏ᶠ m, p.2.2 m : Polynomial K) : K⟦X⟧)) = f := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hv0 : ∀ x, v x = ⊤ → x = 0 := fun _ => v.top_iff.mp
  obtain ⟨d, hfd⟩ := TauCeti.PowerSeries.exists_isDistinguished hc hfr hf0
  obtain ⟨e, ω, he, hωm, heω⟩ := hfd.exists_isUnit_isMonicOfDegree_mul_eq
    hfd.coeff_ne_zero.isUnit hc hfr
  obtain ⟨g, ⟨hfin, hc0, hslopes, hω_prod⟩, hguniq⟩ :=
    Polynomial.existsUnique_C_mul_X_pow_mul_finprod_eq v hb hv hωm.ne_zero
  set tr := ω.trailingCoeff
  have htr : tr ≠ 0 := Polynomial.trailingCoeff_ne_zero.mpr hωm.ne_zero
  set u₀ : IsRestricted.subring (R := K) (b ^ σ) :=
    e * TauCeti.PowerSeries.polynomialToRestricted (b ^ σ) (Polynomial.C tr)
  have hu₀ : IsUnit u₀ := he.mul
    ((htr.isUnit.map Polynomial.C).map (TauCeti.PowerSeries.polynomialToRestricted (b ^ σ)))
  have hg_fact : (∏ᶠ m, g m).IsPureSlopeFactorization v g := ⟨hfin, hc0, hslopes, rfl⟩
  have hg_le : ∀ m ∈ Function.mulSupport g, m ≤ σ := by
    intro m hm
    have hm_mem : m ∈ (∏ᶠ m', g m').newtonSlopes v :=
      (Set.ext_iff.mp (hg_fact.mulSupport_eq hv0) m).mp hm
    have hω_slopes : (∏ᶠ m', g m').newtonSlopes v = ω.newtonSlopes v := by
      rw [← hω_prod, mul_assoc, Polynomial.newtonSlopes_C_mul _ v (v.ne_top_iff.mpr htr),
        Polynomial.newtonSlopes_X_pow_mul]
    rw [hω_slopes] at hm_mem
    exact le_of_mem_newtonSlopes_of_isUnit_mul v hb hv hfd he hωm.natDegree_eq.le heω hm_mem
  have hmul₀ : (u₀ : K⟦X⟧) *
      (((Polynomial.X ^ ω.natTrailingDegree * ∏ᶠ m, g m : Polynomial K) : K⟦X⟧)) = f := by
    calc (u₀ : K⟦X⟧) *
          (((Polynomial.X ^ ω.natTrailingDegree * ∏ᶠ m, g m : Polynomial K) : K⟦X⟧))
        = (e : K⟦X⟧) *
            ((Polynomial.C tr * Polynomial.X ^ ω.natTrailingDegree * ∏ᶠ m, g m :
              Polynomial K) : K⟦X⟧) := by
          simp only [u₀, Subring.coe_mul, TauCeti.PowerSeries.coe_polynomialToRestricted,
            Polynomial.coe_mul]
          ring
      _ = f := by rw [hω_prod, heω]
  refine ⟨(u₀, ω.natTrailingDegree, g), ⟨hu₀, hfin, hc0, hslopes, hg_le, hmul₀⟩, ?_⟩
  rintro ⟨u', a', g'⟩ ⟨hu', hfin', hc0', hslopes', hg_le', hmul'⟩
  obtain ⟨e', ω', he', hω'_monic, hf_dist', he'ω', ha_eq, hω'_prod⟩ :=
    exists_monic_preparation_of_X_pow_mul_finprod v hb hv hu' hfin' hc0' hslopes' hg_le' hmul'
  obtain ⟨-, hω_eq⟩ := hfd.eq_and_eq_of_mul_eq_mul hc he' he ⟨hf_dist'.unique hfd, hω'_monic⟩ hωm
    he'ω' heω
  subst hω_eq
  subst ha_eq
  have hg'_eq : g' = g := hguniq g' ⟨hfin', hc0', hslopes', hω'_prod⟩
  subst hg'_eq
  have hQ_ne : (Polynomial.X ^ ω'.natTrailingDegree * ∏ᶠ m, g' m : Polynomial K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hg_fact.ne_zero
  have hu'_eq : u' = u₀ := Subtype.ext <| mul_right_cancel₀
    (Polynomial.coe_eq_zero_iff.not.mpr hQ_ne) (hmul'.trans hmul₀.symm)
  rw [hu'_eq]

/-- **Closed-disc pure slope factorisation at an arbitrary positive radius.** For any `r > 0`, a
nonzero power series `f` restricted at `r` factors uniquely into a unit at radius `r`, `X ^ a`, and
constant-one pure polynomial factors of slopes `m ≤ Real.logb b r`. -/
theorem existsUnique_isUnit_X_pow_mul_finprod_eq_of_pos {f : K⟦X⟧} {r : ℝ} (hr : 0 < r)
    (hfr : f.IsRestricted r) (hf0 : f ≠ 0) :
    ∃! p : IsRestricted.subring (R := K) r × ℕ × (ℝ → Polynomial K),
      IsUnit p.1 ∧ (Function.mulSupport p.2.2).Finite ∧
      (∀ m, (p.2.2 m).coeff 0 = 1) ∧
      (∀ m, ∀ s ∈ (p.2.2 m).newtonSlopes v, s = m) ∧
      (∀ m ∈ Function.mulSupport p.2.2, m ≤ Real.logb b r) ∧
      (p.1 : K⟦X⟧) * (((Polynomial.X ^ p.2.1 * ∏ᶠ m, p.2.2 m : Polynomial K) : K⟦X⟧)) = f := by
  have hrb : b ^ Real.logb b r = r := Real.rpow_logb (zero_lt_one.trans hb) hb.ne' hr
  rw [← hrb] at hfr ⊢
  rw [Real.logb_rpow (zero_lt_one.trans hb) hb.ne']
  exact existsUnique_isUnit_X_pow_mul_finprod_eq v hb hv hfr hf0

end CompleteBase

include hb hv in
/-- **Sphere decomposition of zeros on a closed disc.** Under the hypotheses of
`PowerSeries.evalAt_eq_zero_iff_of_isUnit_X_pow_mul_finprod_eq` with constant-one pure factors
`g m`, for every slope `m` with `b ^ m ≤ r` the zeros of `f` on the sphere `‖x‖ = b ^ m` in `L` are
precisely the roots of the slope-`m` factor `g m` in `L`. -/
theorem setOf_norm_eq_and_evalAt_eq_zero {L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] {f : K⟦X⟧} {r : ℝ}
    {u : IsRestricted.subring (R := K) r} (hu : IsUnit u) {a : ℕ} {g : ℝ → Polynomial K}
    (hfin : (Function.mulSupport g).Finite) (hc0 : ∀ m, (g m).coeff 0 = 1)
    (hslopes : ∀ m, ∀ s ∈ (g m).newtonSlopes v, s = m)
    (hmul : (u : K⟦X⟧) * (((Polynomial.X ^ a * ∏ᶠ m, g m : Polynomial K) : K⟦X⟧)) = f)
    {m : ℝ} (hmr : b ^ m ≤ r) :
    {x : L | ‖x‖ = b ^ m ∧ f.evalAt x = 0} = {x : L | Polynomial.aeval x (g m) = 0} := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  have hg_fact : (∏ᶠ m', g m').IsPureSlopeFactorization v g := ⟨hfin, hc0, hslopes, rfl⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hnorm, hf0⟩
    have hx_le : ‖x‖ ≤ r := hnorm.trans_le hmr
    have hx_ne : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hnorm
      exact (Real.rpow_pos_of_pos (zero_lt_one.trans hb) m).ne hnorm
    rcases (evalAt_eq_zero_iff_of_isUnit_X_pow_mul_finprod_eq hu hfin hmul hx_le).mp hf0 with
      ⟨rfl, -⟩ | ⟨m', -, hm'_root⟩
    · exact (hx_ne rfl).elim
    · have hnorm' := Polynomial.norm_eq_rpow_of_forall_mem_newtonSlopes_eq v hb hv
        (hg_fact.apply_ne_zero m') (hslopes m') hx_ne hm'_root
      have hmm' : m' = m :=
        (Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne').mp (hnorm'.symm.trans hnorm)
      rwa [← hmm']
  · intro hroot
    have hx_ne : x ≠ 0 := by
      rintro rfl
      simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, hc0 m] at hroot
    have hnorm := Polynomial.norm_eq_rpow_of_forall_mem_newtonSlopes_eq v hb hv
      (hg_fact.apply_ne_zero m) (hslopes m) hx_ne hroot
    refine ⟨hnorm, ?_⟩
    have hgm_ne_one : g m ≠ 1 := by
      rintro h1
      rw [h1, map_one] at hroot
      exact one_ne_zero hroot
    exact (evalAt_eq_zero_iff_of_isUnit_X_pow_mul_finprod_eq hu hfin hmul (hnorm.trans_le hmr)).mpr
      (.inr ⟨m, hgm_ne_one, hroot⟩)

end DiscFactorization

end PowerSeries
