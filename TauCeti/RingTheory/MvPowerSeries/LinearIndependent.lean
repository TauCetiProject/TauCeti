/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.Adjoin.Transcendental
public import TauCeti.RingTheory.HahnSeries.PowerSeries
public import TauCeti.RingTheory.LaurentSeries.RatFunc
public import TauCeti.RingTheory.MvPowerSeries.Equiv

/-!
# Linear independence of products in separate variables

Let `g_j`, `j ∈ J`, be one-variable power series over a commutative ring `R` that are linearly
independent over `R`. For a finite set of variables `σ`, the products `∏ s, g_{j s}(X_s)`,
indexed by all functions `j : σ → J`, are again linearly independent over `R`: the family of
coefficient sequences of the products is the `σ`-fold tensor power of the family of coefficient
sequences of the `g_j`. The proof peels off one variable at a time. Collecting the terms of a
vanishing combination by the factor in the first variable gives a vanishing combination of the
`g_j` for each fixed monomial in the remaining variables.

Over a field `K`, combined with the tower rule for linear independence, this gives the
separate-variable independence used to build auxiliary functions in transcendence proofs: if
`f_i ∈ K⟦X⟧` are linearly independent over the field `K(q)` generated inside `K⸨X⸩` by a power
series `q` transcendental over `K`, then the products `∏ s, q(X_s)^{k_s} f_{i_s}(X_s)` are
linearly independent over `K`. In the arithmetic algebraicity theorem of Calegari, Dimitrov and
Tang, `q` is the Taylor expansion at `0` of a nonconstant rational function `p`, which is
transcendental by `RatFunc.transcendental_coe`. Any nonzero rational coefficient vector then
gives a nonzero auxiliary function.

Independence over `K(q)` rather than over `K` is essential: `1` and `q` are independent over `K`,
but `q · 1` and `1 · q` are the same product.

## Main results

* `LinearIndependent.prod_toMvPowerSeries`: products of an independent family of one-variable
  series, placed in separate variables, are independent.
* `Transcendental.linearIndependent_prod_toMvPowerSeries_mul_pow`: the products
  `∏ s, f_{i_s}(X_s) q(X_s)^{k_s}` are independent over `K` when the `f_i` are independent over
  `K⟮q⟯` and `q` is transcendental over `K`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), §2.1, proof of Lemma 2.1.2.
-/

public section

open PowerSeries
open scoped IntermediateField LaurentSeries

namespace LinearIndependent

variable {R J : Type*} [CommRing R] {g : J → PowerSeries R}

/-- The case of finitely many series and the variables `Fin d`, by induction on `d`. -/
private theorem prod_toMvPowerSeries_fin [Finite J] (hg : LinearIndependent R g) :
    ∀ d : ℕ, LinearIndependent R fun j : Fin d → J ↦ ∏ s, (g (j s)).toMvPowerSeries s
  | 0 => by
    have := Fintype.ofFinite J
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    simpa [Subsingleton.elim j default] using congrArg (MvPowerSeries.coeff 0) hc
  | d + 1 => by
    have := Fintype.ofFinite J
    have ih := prod_toMvPowerSeries_fin hg d
    rw [Fintype.linearIndependent_iff] at ih hg ⊢
    intro c hc j
    -- Collect the terms whose first index is `a`; each collected sum vanishes, since its
    -- coefficient at a monomial `e'` in the last `d` variables is the `a`-th coefficient of a
    -- vanishing combination of the `g a`.
    have key (a : J) : ∑ j' : Fin d → J, c (Fin.cons a j') •
        ∏ s, (g (j' s)).toMvPowerSeries s = 0 := by
      ext e'
      refine hg (fun a ↦ MvPowerSeries.coeff e' (∑ j' : Fin d → J, c (Fin.cons a j') •
        ∏ s, (g (j' s)).toMvPowerSeries s)) ?_ a
      ext n
      have := congrArg (MvPowerSeries.coeff (Finsupp.cons n e')) hc
      simp only [map_sum, map_smul, coeff_prod_toMvPowerSeries, map_zero, smul_eq_mul] at this
      simp only [Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ] at this
      rw [← (Fin.consEquiv fun _ ↦ J).sum_comp, Fintype.sum_prod_type] at this
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ] at this
      -- Pull the factor `coeff n (g a)` into the inner sum to match `this` term by term.
      simp only [map_sum, map_smul, coeff_prod_toMvPowerSeries, map_zero, smul_eq_mul,
        Finset.sum_mul]
      rw [← this]
      exact Fintype.sum_congr _ _ fun a ↦ Fintype.sum_congr _ _ fun j' ↦ by ring
    simpa using ih _ (key (j 0)) (Fin.tail j)

/-- The case of finitely many series, transported from `Fin (Fintype.card σ)` to `σ`. -/
private theorem prod_toMvPowerSeries_of_finite [Finite J] (hg : LinearIndependent R g)
    (σ : Type*) [Fintype σ] :
    LinearIndependent R fun j : σ → J ↦ ∏ s, (g (j s)).toMvPowerSeries s := by
  let e := Fintype.equivFin σ
  refine .of_comp (MvPowerSeries.renameEquiv R e).toLinearEquiv.toLinearMap ?_
  convert (prod_toMvPowerSeries_fin hg (Fintype.card σ)).comp (fun j ↦ j ∘ e.symm)
    (fun j j' h ↦ funext fun s ↦ by simpa using congrFun h (e s)) using 1
  ext1 j
  simp only [Function.comp_apply]
  rw [← e.prod_comp fun t ↦ (g (j (e.symm t))).toMvPowerSeries t]
  simp [MvPowerSeries.renameEquiv_apply]

/-- **Independence in separate variables.** If the one-variable power series `g j` are linearly
independent over `R`, then so are the products `∏ s, (g (j s))(X_s)` over all `j : σ → J`, for
any finite set of variables `σ`. -/
theorem prod_toMvPowerSeries (hg : LinearIndependent R g) (σ : Type*) [Fintype σ] :
    LinearIndependent R fun j : σ → J ↦ ∏ s, (g (j s)).toMvPowerSeries s := by
  classical
  -- A finite subfamily only involves the finitely many series indexed by the values in `T`.
  rw [linearIndependent_iff_finset_linearIndependent]
  intro S
  let T : Finset J := S.biUnion fun j ↦ Finset.univ.image j
  have hT (j : S) (s : σ) : (j : σ → J) s ∈ T :=
    Finset.mem_biUnion.2 ⟨j, j.property, Finset.mem_image_of_mem _ (Finset.mem_univ s)⟩
  have := (prod_toMvPowerSeries_of_finite (hg.comp ((↑) : T → J) Subtype.val_injective) σ).comp
    (fun j : S ↦ fun s ↦ (⟨j.val s, hT j s⟩ : T))
    (fun j j' h ↦ Subtype.ext (funext fun s ↦ congrArg Subtype.val (congrFun h s)))
  simpa [Function.comp_def] using this

end LinearIndependent

namespace Transcendental

variable {K ι : Type*} [Field K] {q : PowerSeries K} {f : ι → PowerSeries K}

/-- **Independence of auxiliary products.** Let `q` be a power series transcendental over `K`
and let the power series `f i` be linearly independent over the field `K⟮q⟯` generated by `q`
inside `K⸨X⸩`. Then for any finite set of variables `σ`, the products
`∏ s, f_{i_s}(X_s) q(X_s)^{k_s}`, indexed by `j = (i, k) : σ → ι × ℕ`, are linearly
independent over `K`. -/
theorem linearIndependent_prod_toMvPowerSeries_mul_pow (hq : Transcendental K q)
    (hf : LinearIndependent K⟮(q : K⸨X⸩)⟯ fun i ↦ (f i : K⸨X⸩)) (σ : Type*) [Fintype σ] :
    LinearIndependent K fun j : σ → ι × ℕ ↦
      ∏ s, (f (j s).1).toMvPowerSeries s * q.toMvPowerSeries s ^ (j s).2 := by
  -- `K⸨X⸩` carries two `K`-module structures that are not reducibly defeq: the coefficientwise
  -- one found by instance search, and the one of the `K`-algebra structure, which is the one
  -- `Transcendental.linearIndependent_mul_pow` uses. Select the latter.
  let : Module K K⸨X⸩ := Algebra.toModule
  have hq' : Transcendental K (q : K⸨X⸩) :=
    (transcendental_algebraMap_iff HahnSeries.ofPowerSeries_injective).mpr hq
  have h1 : LinearIndependent K fun p : ι × ℕ ↦ f p.1 * q ^ p.2 :=
    .of_comp (IsScalarTower.toAlgHom K (PowerSeries K) K⸨X⸩).toLinearMap (by
      simpa [Function.comp_def] using hq'.linearIndependent_mul_pow hf)
  simpa using h1.prod_toMvPowerSeries σ

end Transcendental

/-! ### Examples -/

/-- Independence of the `f i` over `K` alone does not suffice: for `q = X`, the series `1` and `X`
are independent over `K`, but the one-variable products `X · 1` and `1 · X` coincide. -/
example (K : Type*) [Field K] :
    ¬LinearIndependent K fun j : Fin 1 → Fin 2 × ℕ ↦
      ∏ s, (![1, X] (j s).1 : PowerSeries K).toMvPowerSeries s *
        (X : PowerSeries K).toMvPowerSeries s ^ (j s).2 := by
  intro h
  have := h.injective (a₁ := fun _ ↦ (0, 1)) (a₂ := fun _ ↦ (1, 0)) (by simp)
  simpa using congrFun this 0

/-- The separate-variable independence for the Taylor expansion `pSeries` at `0` of a
nonconstant rational function `p ∈ ℚ(x)` regular at `0`, in `d` variables. -/
example {p : RatFunc ℚ} (hp : ¬∃ c, p = RatFunc.C c) {pSeries : PowerSeries ℚ}
    (hreg : (pSeries : ℚ⸨X⸩) = p) {m d : ℕ} {f : Fin m → PowerSeries ℚ}
    (hf : LinearIndependent ℚ⟮(p : ℚ⸨X⸩)⟯ fun i ↦ (f i : ℚ⸨X⸩)) :
    LinearIndependent ℚ fun j : Fin d → Fin m × ℕ ↦
      ∏ s, (f (j s).1).toMvPowerSeries s * pSeries.toMvPowerSeries s ^ (j s).2 :=
  ((transcendental_algebraMap_iff HahnSeries.ofPowerSeries_injective).mp
    (hreg ▸ RatFunc.transcendental_coe hp)).linearIndependent_prod_toMvPowerSeries_mul_pow
    (by rwa [hreg]) (Fin d)
