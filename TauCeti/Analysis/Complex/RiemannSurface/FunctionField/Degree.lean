/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
public import TauCeti.Analysis.Complex.RiemannSurface.FiberMultiset
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Comap
public import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Separation
import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# The degree of a meromorphic function over `ℂ(t)`

Let `X` be a compact connected Riemann surface and `β : X → OnePoint ℂ` a finite holomorphic map of
degree `n`. Pulling back along `β` embeds the field `M(OnePoint ℂ) ≅ ℂ(t)` of rational functions
into the field `M(X)` of meromorphic functions on `X`
(`TauCeti.RiemannSurface.MeromorphicFunction.comapₐ`). This file proves the first half of the degree
theorem for this extension: **every meromorphic function `f` on `X` is a root of a monic polynomial
of degree `n` over `ℂ(t)`**
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_monic_natDegree_eq_degree_eval₂_eq_zero`),
so it is integral of degree at most `n` over `ℂ(t)`
(`TauCeti.RiemannSurface.MeromorphicFunction.isIntegral_ratFunc` and
`TauCeti.RiemannSurface.MeromorphicFunction.natDegree_minpoly_ratFunc_le`).

The polynomial is the classical one,

```text
P(T) = ∏ (T - f(x)) = Tⁿ - c₁ Tⁿ⁻¹ + ⋯ + (-1)ⁿ cₙ ,     the product over the fibre of β over t,
```

the fibre being counted with multiplicities (`TauCeti.RiemannSurface.fiberMultiset`), so that its
coefficients are, up to sign, the elementary symmetric functions `c_k(t)` of the values of `f` along
the fibres of `β`. At every point of the sphere over which `f` has no poles, these are holomorphic
(`TauCeti.RiemannSurface.analyticAt_esymm_map_fiberMultiset`), including at the branch values of
`β`. Over a point `t₀` where `f` has poles, choose a rational function `u` vanishing at `t₀`. For
`N` large, `f · (u ∘ β) ^ N` has no poles over `t₀`, and near `t₀` the `k`-th symmetric function of
its values is `u ^ (N k)` times that of `f`. So `c_k` is meromorphic at `t₀` too, and each `c_k` is
a meromorphic function on the sphere, that is, a rational function. Finally `P(f)` vanishes at every
point `x` whose fibre carries no pole of `f`, since `f(x)` is one of the values in the product, and
these points are all but finitely many. So `P(f) = 0` in `M(X)`.

Conversely, the values of `f` along a fibre bound its degree from below. If `f` takes `k` pairwise
distinct finite values at points of the fibre of `β` over `t₀`, then every nonzero polynomial over
`ℂ(t)` vanishing at `f` has degree at least `k`
(`TauCeti.RiemannSurface.MeromorphicFunction.ncard_le_natDegree_of_eval₂_eq_zero`): divide it by a
coefficient of least order at `t₀`, so that all its coefficients are finite at `t₀` and one of them
is `1`. Their values at `t₀` then form a nonzero polynomial over `ℂ` which has the `k` values of
`f` as roots. In particular, a function separating the `n` points of an unbranched fibre has degree
exactly `n` over `ℂ(t)`, and such a function exists as soon as the points of that fibre are
pairwise separated by meromorphic functions
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_natDegree_minpoly_ratFunc_eq_degree`).

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.meromorphicAt_esymm_map_finitePart_fiberMultiset`:
  the elementary symmetric functions of the values of a meromorphic function along the fibres of
  `β` are meromorphic on the sphere.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_monic_natDegree_eq_degree_eval₂_eq_zero`:
  a meromorphic function on `X` is a root of a monic polynomial of degree `deg β` over
  `M(OnePoint ℂ)`, pulled back along `β`.
* `TauCeti.RiemannSurface.MeromorphicFunction.isIntegral_ratFunc` and
  `TauCeti.RiemannSurface.MeromorphicFunction.natDegree_minpoly_ratFunc_le`: for the
  `ℂ(t)`-algebra structure on `M(X)` given by `β`, every meromorphic function is integral, of degree
  at most `deg β`.
* `TauCeti.RiemannSurface.MeromorphicFunction.ncard_le_natDegree_of_eval₂_eq_zero` and
  `TauCeti.RiemannSurface.MeromorphicFunction.ncard_le_natDegree_minpoly_ratFunc`: a function
  taking `k` distinct finite values along one fibre of `β` has degree at least `k` over `ℂ(t)`.
* `TauCeti.RiemannSurface.MeromorphicFunction.natDegree_minpoly_ratFunc_eq_degree`: a function
  separating the points of an unbranched fibre has degree exactly `deg β` over `ℂ(t)`.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_natDegree_minpoly_ratFunc_eq_degree`: if the
  points of an unbranched fibre are pairwise separated by meromorphic functions, some meromorphic
  function has degree exactly `deg β` over `ℂ(t)`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8, Theorem 8.2 and Corollary 8.3 (a meromorphic function on `X` satisfies a polynomial equation
  of degree `deg β` over `ℳ(Y)`, with the elementary symmetric functions of its values along the
  fibres as coefficients).
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Proposition 1.89 (the upper bound) and Corollary 1.93 (the equality `[M(S) : ℂ(f)] = deg f`).
-/

public noncomputable section

open Filter Function IsManifold OnePoint Polynomial Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]
  (β : FiniteHolomorphicMap X (OnePoint ℂ)) (f : MeromorphicFunction X)

/-! ### Symmetric functions of the values along the fibres -/

omit [ConnectedSpace X] in
/-- Over a point of the sphere whose fibre carries no pole of `f`, each elementary symmetric
function of the values of `f` along the fibres of `β` is holomorphic, read in the chart there. -/
private theorem analyticAt_esymm {y₀ : OnePoint ℂ} (hy₀ : ∀ x ∈ β ⁻¹' {y₀}, f x ≠ ∞) (k : ℕ) :
    AnalyticAt ℂ ((fun y ↦ ((fiberMultiset β y).map f.finitePart).esymm k) ∘
      (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀) :=
  analyticAt_esymm_map_fiberMultiset β.holomorphic β.not_eventuallyConst
    (chart_mem_maximalAtlas y₀) (mem_chart_source ℂ y₀) (fun x hx ↦ by
      filter_upwards [f.continuous.continuousAt.eventually (isOpen_ne.mem_nhds (hy₀ x hx))]
        with x' hx'
      exact mdifferentiableAt_finitePart hx') k

omit [ConnectedSpace X] in
/-- Over a point of the sphere whose fibre carries no pole of `f`, each elementary symmetric
function of the values of `f` along the fibres of `β` is continuous. -/
private theorem continuousAt_esymm {y₀ : OnePoint ℂ} (hy₀ : ∀ x ∈ β ⁻¹' {y₀}, f x ≠ ∞) (k : ℕ) :
    ContinuousAt (fun y ↦ ((fiberMultiset β y).map f.finitePart).esymm k) y₀ := by
  refine ((analyticAt_esymm β f hy₀ k).continuousAt.comp
    ((chartAt ℂ y₀).continuousAt (mem_chart_source ℂ y₀))).congr ?_
  filter_upwards [(chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy
  simp only [Function.comp_apply, (chartAt ℂ y₀).left_inv hy]

omit [CompactSpace X] [T2Space X] in
/-- Multiplying `f` by a high power of the pullback of a function vanishing at `y₀` removes the
poles of `f` over `y₀`. -/
private theorem exists_mul_comap_pow_ne_infty {u : MeromorphicFunction (OnePoint ℂ)}
    {y₀ : OnePoint ℂ} (hu₀ : u y₀ = ((0 : ℂ) : OnePoint ℂ)) :
    ∃ N : ℕ, ∀ x ∈ β ⁻¹' {y₀}, (f * comap β β.holomorphic β.nonconstant (u ^ N)) x ≠ ∞ := by
  have hev (x : X) (hx : x ∈ β ⁻¹' {y₀}) : ∀ᶠ N in atTop,
      (f * comap β β.holomorphic β.nonconstant (u ^ N)) x ≠ ∞ := by
    have hβx : β x = y₀ := hx
    -- The pullback of `u` vanishes at `x`, so it has positive order there.
    have hpos : 0 < order x (comap β β.holomorphic β.nonconstant u) := by
      rw [order_pos_iff, comap_apply, hβx, hu₀]
    refine Eventually.mono ?_ fun N (hN : 0 ≤ order x f +
        N • order x (comap β β.holomorphic β.nonconstant u)) ↦ by
      rwa [← order_nonneg_iff, (order x).map_mul, comap_pow, (order x).map_pow]
    revert hpos
    induction order x f using WithTop.recTopCoe with
    | top => exact fun _ ↦ .of_forall fun N ↦ by simp
    | coe a =>
      induction order x (comap β β.holomorphic β.nonconstant u) using WithTop.recTopCoe with
      | top =>
        refine fun _ ↦ (eventually_ge_atTop 1).mono fun N hN ↦ ?_
        obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        rw [succ_nsmul, WithTop.add_top, WithTop.add_top]
        exact le_top
      | coe b =>
        refine fun hpos ↦ (eventually_ge_atTop a.natAbs).mono fun N hN ↦ ?_
        have hb : (1 : ℤ) ≤ b := by
          have := WithTop.coe_pos.1 hpos
          omega
        rw [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_nonneg, nsmul_eq_mul]
        have ha : -(a.natAbs : ℤ) ≤ a := by omega
        have hN' : (a.natAbs : ℤ) ≤ N := by exact_mod_cast hN
        have hN₀ : (0 : ℤ) ≤ N := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hb hN₀]
  obtain ⟨N, hN⟩ := ((β.finite_fiber y₀).eventually_all.2 hev).exists
  exact ⟨N, hN⟩

/-- **The elementary symmetric functions of the values along the fibres are meromorphic on the
sphere.** Each elementary symmetric function of the values of a meromorphic function `f` along the
fibres of `β`, counted with multiplicity, is meromorphic at every point of the sphere, poles of `f`
and branch values of `β` included. -/
theorem meromorphicAt_esymm_map_finitePart_fiberMultiset (k : ℕ) (y₀ : OnePoint ℂ) :
    MeromorphicAt (fun y ↦ ((fiberMultiset β y).map f.finitePart).esymm k) y₀ := by
  obtain ⟨u, hu, hu₀⟩ := exists_ne_zero_apply_eq_zero y₀
  obtain ⟨N, hN⟩ := exists_mul_comap_pow_ne_infty β f hu₀
  set g := f * comap β β.holomorphic β.nonconstant (u ^ N)
  have hg : MeromorphicAt (fun y ↦ ((fiberMultiset β y).map g.finitePart).esymm k) y₀ := by
    rw [meromorphicAt_def]
    exact (analyticAt_esymm β g hN k).meromorphicAt
  -- Away from `y₀`, the values of `g` along a fibre are those of `f`, multiplied by `u ^ N`.
  have hpoles : (β '' {x | f x = ∞}).Finite := f.finite_setOf_eq_infty.image β
  refine (hg.mul ((u.meromorphicAt_finitePart y₀).pow (N * k)).inv).congr ?_
  filter_upwards [u.eventually_ne_infty y₀, eventually_finitePart_ne_zero hu y₀,
    mem_codiscrete_iff_forall_mem_nhdsNE.1 hpoles.compl_mem_codiscrete y₀] with y hyu hyu₀ hyf
  have hfib : (fiberMultiset β y).map g.finitePart =
      ((fiberMultiset β y).map f.finitePart).map (u.finitePart y ^ N • ·) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    have hβx : β x = y := ((mem_fiberMultiset (β.finite_fiber y)).1 hx).1
    have hfx : f x ≠ ∞ := fun h ↦ hyf ⟨x, h, hβx⟩
    refine finitePart_of_eq_coe ?_
    rw [mul_apply_of_eq_coe (coe_finitePart hfx).symm
      (by rw [comap_apply, hβx, pow_apply hyu]), Function.comp_apply, smul_eq_mul, mul_comm]
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
  rw [hfib, ← Multiset.pow_smul_esymm, smul_eq_mul, ← pow_mul, mul_right_comm,
    mul_inv_cancel₀ (pow_ne_zero _ hyu₀), one_mul]

/-! ### The polynomial equation -/

/-- **The polynomial equation of a meromorphic function over `ℂ(t)`.** A meromorphic function
`f` on a compact connected Riemann surface `X` is a root of a monic polynomial of degree `deg β`
whose coefficients are meromorphic functions on the sphere, pulled back along a finite holomorphic
map `β : X → OnePoint ℂ`. One such polynomial, built in the proof, has as coefficients, up to
sign, the elementary symmetric functions of the values of `f` along the fibres of `β`. -/
theorem exists_monic_natDegree_eq_degree_eval₂_eq_zero :
    ∃ p : (MeromorphicFunction (OnePoint ℂ))[X], p.Monic ∧ p.natDegree = degree β ∧
      p.eval₂ (comapₐ β β.holomorphic β.nonconstant).toRingHom f = 0 := by
  set n := degree β
  -- The polynomial `∏ (T - f(x))` over the fibre multiset of `y`, and its coefficients.
  set Q : OnePoint ℂ → ℂ[X] := fun y ↦
    (((fiberMultiset β y).map f.finitePart).map fun v ↦ Polynomial.X - C v).prod
  have hcard (y : OnePoint ℂ) : Multiset.card ((fiberMultiset β y).map f.finitePart) = n := by
    rw [Multiset.card_map, β.card_fiberMultiset]
  have hQ (i : ℕ) (hi : i ≤ n) : (fun y ↦ (Q y).coeff i) = fun y ↦
      (-1) ^ (n - i) * ((fiberMultiset β y).map f.finitePart).esymm (n - i) := by
    funext y
    simp only [Q]
    rw [Multiset.prod_X_sub_C_coeff _ (hcard y ▸ hi), hcard]
  have hmero (i : Fin n) (y : OnePoint ℂ) : MeromorphicAt (fun y ↦ (Q y).coeff i) y := by
    rw [hQ i i.2.le]
    exact (meromorphicAt_const _ y).mul (meromorphicAt_esymm_map_finitePart_fiberMultiset β f _ y)
  set A : Fin n → MeromorphicFunction (OnePoint ℂ) := fun i ↦ ofMeromorphic (hmero i)
  refine ⟨TauCeti.Polynomial.monicOfCoeff A, TauCeti.Polynomial.monic_monicOfCoeff A,
    TauCeti.Polynomial.natDegree_monicOfCoeff A, ?_⟩
  -- Compare values at the points whose fibre carries no pole of `f`: all but finitely many.
  refine eq_of_forall_apply_eq (p := fun x ↦ ∀ x' ∈ β ⁻¹' {β x}, f x' ≠ ∞) (fun x₀ ↦ ?_)
    fun x hx ↦ ?_
  · have hB : (β ⁻¹' (β '' {x | f x = ∞})).Finite :=
      (f.finite_setOf_eq_infty.image β).preimage' fun y _ ↦ β.finite_fiber y
    filter_upwards [mem_codiscrete_iff_forall_mem_nhdsNE.1 hB.compl_mem_codiscrete x₀]
      with x hx x' hx' hfx'
    exact hx ⟨x', hfx', hx'⟩
  -- At such a point, the coefficients of the polynomial take the values of those of `Q (β x)`.
  have hcoeff (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      (comapₐ β β.holomorphic β.nonconstant).toRingHom
          ((TauCeti.Polynomial.monicOfCoeff A).coeff i) x = ↑((Q (β x)).coeff i) := by
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, comapₐ_apply, comap_apply]
    rcases hi'.lt_or_eq with hin | rfl
    · have hA := TauCeti.Polynomial.coeff_monicOfCoeff A ⟨i, hin⟩
      rw [Fin.val_mk] at hA
      rw [hA]
      refine ofMeromorphic_apply_of_continuousAt _ ?_
      rw [hQ i hi']
      exact continuousAt_const.mul (continuousAt_esymm β f hx _)
    · rw [TauCeti.Polynomial.coeff_monicOfCoeff_self, coe_one,
        congrFun (hQ n le_rfl) (β x), Nat.sub_self, pow_zero, Multiset.esymm_zero, one_mul]
  rw [eval₂_eq_sum_range, TauCeti.Polynomial.natDegree_monicOfCoeff, coe_zero,
    sum_apply_of_eq_coe fun i hi ↦ mul_apply_of_eq_coe (hcoeff i hi)
      (pow_apply_of_eq_coe (coe_finitePart (hx x rfl)).symm i)]
  -- The value is `Q (β x)` evaluated at `f x`, which is one of its roots.
  rw [← eval_eq_sum_range' (by
      simp only [Q]
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hcard]
      omega),
    eval_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨f.finitePart x, ?_, by simp⟩))
  exact Multiset.mem_map_of_mem _ ((mem_fiberMultiset (β.finite_fiber (β x))).2
    ⟨rfl, localMultiplicity_pos β x⟩)

/-! ### Distinct values along a fibre bound the degree from below -/

/-- Multiplying a nonzero polynomial over `M(OnePoint ℂ)` by the inverse of a coefficient of least
order at `y₀` gives a polynomial whose coefficients are all finite at `y₀`, one of them being
`1`. -/
private theorem exists_coeff_C_mul_eq_one_and_forall_ne_infty
    {p : (MeromorphicFunction (OnePoint ℂ))[X]} (hp : p ≠ 0) (y₀ : OnePoint ℂ) :
    ∃ c : MeromorphicFunction (OnePoint ℂ), ∃ j : ℕ,
      (C c * p).coeff j = 1 ∧ ∀ i, (C c * p).coeff i y₀ ≠ ∞ := by
  obtain ⟨j, hj, hmin⟩ := p.support.exists_min_image (fun i ↦ order y₀ (p.coeff i))
    (nonempty_support_iff.2 hp)
  have ha : p.coeff j ≠ 0 := mem_support_iff.1 hj
  refine ⟨(p.coeff j)⁻¹, j, by rw [coeff_C_mul, inv_mul_cancel₀ ha], fun i ↦ ?_⟩
  rw [← order_nonneg_iff, coeff_C_mul, (order y₀).map_mul, (order y₀).map_inv]
  by_cases hi : p.coeff i = 0
  · simp [hi]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ((order y₀).ne_top_iff.2 ha)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 ((order y₀).ne_top_iff.2 hi)
  have hle := hmin i (mem_support_iff.2 hi)
  rw [← hm, ← hk, WithTop.coe_le_coe] at hle
  rw [← hm, ← hk, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
    WithTop.coe_nonneg]
  omega

omit [CompactSpace X] [T2Space X] in
/-- **Distinct values along a fibre bound the degree from below.** If a meromorphic function `f`
on `X` takes pairwise distinct finite values at the points of a set `s` lying in one fibre of `β`,
then every nonzero polynomial over `M(OnePoint ℂ)` which, pulled back along `β`, vanishes at `f`
has degree at least the number of points of `s`. The fibre may be branched, and may lie over `∞`. -/
theorem ncard_le_natDegree_of_eval₂_eq_zero {p : (MeromorphicFunction (OnePoint ℂ))[X]}
    (hp : p ≠ 0) (hpf : p.eval₂ (comapₐ β β.holomorphic β.nonconstant).toRingHom f = 0)
    {y₀ : OnePoint ℂ} {s : Set X} (hs : s ⊆ β ⁻¹' {y₀}) (hf : ∀ x ∈ s, f x ≠ ∞)
    (hinj : s.InjOn f) : s.ncard ≤ p.natDegree := by
  classical
  -- Rescale `p` to `q`, with every coefficient finite at `y₀` and the one in degree `j` equal
  -- to `1`. The values of these coefficients at `y₀` form a nonzero polynomial `r` over `ℂ`.
  obtain ⟨c, j, hqj, hq⟩ := exists_coeff_C_mul_eq_one_and_forall_ne_infty hp y₀
  set q := C c * p
  set r : ℂ[X] := ∑ i ∈ q.support, monomial i ((q.coeff i).finitePart y₀)
  have hr : r ≠ 0 := by
    refine fun h ↦ one_ne_zero (α := ℂ) ?_
    have := congrArg (fun p : ℂ[X] ↦ p.coeff j) h
    simp [r, Finsupp.single_apply, hqj] at this
  have hrdeg : r.natDegree ≤ p.natDegree :=
    natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (natDegree_monomial_le _).trans
      ((le_natDegree_of_mem_supp i hi).trans (natDegree_C_mul_le _ _))
  -- Evaluating `q(f) = 0` at a point `x` of `s` shows that `f(x)` is a root of `r`.
  have hroot (x : X) (hx : x ∈ s) : r.eval (f.finitePart x) = 0 := by
    have hqf : q.eval₂ (comapₐ β β.holomorphic β.nonconstant).toRingHom f = 0 := by
      rw [eval₂_mul, hpf, mul_zero]
    have hval := congrArg (· x) hqf
    simp only [coe_zero] at hval
    rw [eval₂_eq_sum, Polynomial.sum_def, sum_apply_of_eq_coe fun i _ ↦ mul_apply_of_eq_coe
      (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, comapₐ_apply, comap_apply, hs hx,
        coe_finitePart (hq i)])
      (pow_apply_of_eq_coe (coe_finitePart (hf x hx)).symm i), coe_eq_coe] at hval
    simpa [r, eval_finsetSum] using hval
  -- So the values of `f` on `s`, which are pairwise distinct, are roots of `r`.
  have hsfin : s.Finite := (β.finite_fiber y₀).subset hs
  have hinj' : Set.InjOn f.finitePart s := fun x hx y hy h ↦
    hinj hx hy (by rw [← coe_finitePart (hf x hx), h, coe_finitePart (hf y hy)])
  rw [Set.ncard_eq_toFinset_card s hsfin, ← Finset.card_image_of_injOn (by simpa using hinj')]
  refine (card_le_degree_of_subset_roots fun v hv ↦ ?_).trans hrdeg
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
  exact (mem_roots hr).2 (hroot x (hsfin.mem_toFinset.1 hx))

section RatFunc

variable [Algebra (RatFunc ℂ) (MeromorphicFunction X)]
  (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
    ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)
include h

/-- The polynomial equation of `f`, transported to `ℂ(t)` along `ratFuncEquiv`. -/
private theorem exists_monic_natDegree_eq_degree_aeval_eq_zero :
    ∃ q : (RatFunc ℂ)[X], q.Monic ∧ q.natDegree = degree β ∧ aeval f q = 0 := by
  obtain ⟨p, hp, hdeg, hpf⟩ := exists_monic_natDegree_eq_degree_eval₂_eq_zero β f
  have hcomp : (algebraMap (RatFunc ℂ) (MeromorphicFunction X)).comp
      ratFuncEquiv.symm.toRingEquiv.toRingHom = (comapₐ β β.holomorphic β.nonconstant).toRingHom :=
    RingHom.ext fun g ↦ by simp [h]
  refine ⟨p.map ratFuncEquiv.symm.toRingEquiv.toRingHom, hp.map _, ?_, ?_⟩
  · rw [natDegree_map_eq_of_injective (RingHom.injective _), hdeg]
  · rw [aeval_def, eval₂_map, hcomp, hpf]

/-- **Every meromorphic function is integral over `ℂ(t)`.** For the `ℂ(t)`-algebra structure on the
field of meromorphic functions of a compact connected Riemann surface `X` given by pulling back
along a finite holomorphic map `β : X → OnePoint ℂ`, every meromorphic function is integral. -/
theorem isIntegral_ratFunc : IsIntegral (RatFunc ℂ) f := by
  obtain ⟨q, hq, -, hqf⟩ := exists_monic_natDegree_eq_degree_aeval_eq_zero β f h
  exact ⟨q, hq, hqf⟩

/-- **Every meromorphic function has degree at most `deg β` over `ℂ(t)`.** For the `ℂ(t)`-algebra
structure on the field of meromorphic functions of a compact connected Riemann surface `X` given by
pulling back along a finite holomorphic map `β : X → OnePoint ℂ`, the minimal polynomial of every
meromorphic function has degree at most the degree of `β`. -/
theorem natDegree_minpoly_ratFunc_le : (minpoly (RatFunc ℂ) f).natDegree ≤ degree β := by
  obtain ⟨q, hq, hdeg, hqf⟩ := exists_monic_natDegree_eq_degree_aeval_eq_zero β f h
  exact hdeg ▸ natDegree_le_natDegree (minpoly.min _ _ hq hqf)


/-- **Distinct values along a fibre bound the degree over `ℂ(t)` from below.** If a meromorphic
function `f` takes pairwise distinct finite values at the points of a set `s` lying in one fibre
of `β`, then its minimal polynomial over `ℂ(t)` has degree at least the number of points of
`s`. -/
theorem ncard_le_natDegree_minpoly_ratFunc {y₀ : OnePoint ℂ} {s : Set X} (hs : s ⊆ β ⁻¹' {y₀})
    (hf : ∀ x ∈ s, f x ≠ ∞) (hinj : s.InjOn f) :
    s.ncard ≤ (minpoly (RatFunc ℂ) f).natDegree := by
  have hcomp : (comapₐ β β.holomorphic β.nonconstant).toRingHom.comp
      ratFuncEquiv.toRingEquiv.toRingHom = algebraMap (RatFunc ℂ) (MeromorphicFunction X) :=
    RingHom.ext fun g ↦ by simp [h]
  have hle := ncard_le_natDegree_of_eval₂_eq_zero β f
    (p := (minpoly (RatFunc ℂ) f).map ratFuncEquiv.toRingEquiv.toRingHom)
    ((Polynomial.map_ne_zero_iff (RingHom.injective _)).2
      (minpoly.ne_zero (isIntegral_ratFunc β f h)))
    (by rw [eval₂_map, hcomp, ← aeval_def, minpoly.aeval]) hs hf hinj
  rwa [natDegree_map_eq_of_injective (RingHom.injective _)] at hle

/-- **A function separating an unbranched fibre has degree `deg β` over `ℂ(t)`.** If a
meromorphic function `f` has no poles on the fibre of `β` over a point `y₀` which is not a branch
value, and takes pairwise distinct values at the points of that fibre, then its minimal polynomial
over `ℂ(t)` has degree exactly the degree of `β`. -/
theorem natDegree_minpoly_ratFunc_eq_degree {y₀ : OnePoint ℂ} (hy₀ : y₀ ∉ β.branchValues)
    (hf : ∀ x ∈ β ⁻¹' {y₀}, f x ≠ ∞) (hinj : (β ⁻¹' {y₀}).InjOn f) :
    (minpoly (RatFunc ℂ) f).natDegree = degree β := by
  refine (natDegree_minpoly_ratFunc_le β f h).antisymm ?_
  rw [← (β.card_fiber_eq_degree_iff y₀).2 hy₀, ← Set.ncard_eq_toFinset_card _ (β.finite_fiber y₀)]
  exact ncard_le_natDegree_minpoly_ratFunc β f h subset_rfl hf hinj

/-- **A separating function of degree `deg β`.** If the points of the fibre of `β` over a point
`y₀` which is not a branch value are pairwise separated by meromorphic functions, then some
meromorphic function on `X` has minimal polynomial of degree exactly the degree of `β` over
`ℂ(t)`. -/
theorem exists_natDegree_minpoly_ratFunc_eq_degree {y₀ : OnePoint ℂ} (hy₀ : y₀ ∉ β.branchValues)
    (hsep : (β ⁻¹' {y₀}).Pairwise fun x x' ↦ ∃ g : MeromorphicFunction X, g x ≠ g x') :
    ∃ f : MeromorphicFunction X, (minpoly (RatFunc ℂ) f).natDegree = degree β := by
  obtain ⟨f, hf, hinj⟩ := exists_forall_ne_infty_and_injOn (β.finite_fiber y₀) hsep
  exact ⟨f, natDegree_minpoly_ratFunc_eq_degree β f h hy₀ hf hinj⟩
end RatFunc

end TauCeti.RiemannSurface.MeromorphicFunction
