/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.HasseDeriv
public import TauCeti.RingTheory.AdjoinRoot.Basic
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.Topology
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Root evaluation and additive Taylor expansion on the cyclotomic completion

Let `n ∈ S` and let `ζ` be a root of the cyclotomic polynomial `Φ_n` in an `R`-algebra `B`. An
element of Habiro's cyclotomic completion `R[q]^S = CycloCompletion R S` can be evaluated at `ζ`
and, more finely, expanded as a power series in `X = q - ζ`:

* `TauCeti.CycloCompletion.evalRoot hn ζ hζ` reduces modulo `Φ_n` and evaluates the class at `ζ`.
  It is an `R`-algebra map agreeing with `Polynomial.aeval ζ` on polynomials, and it is locally
  constant, hence continuous for every topology on `B`. Its universal case is the root of `Φ_n` in
  `AdjoinRoot (cyclotomic n R)`, where it is the projection modulo `Φ_n`.
* `TauCeti.CycloCompletion.taylorAt hn ζ hζ` is the additive Taylor expansion
  `R[q]^S →ₐ[R] B⟦X⟧`. The coefficient of `X ^ k` is the value at `ζ` of the `k`-th Hasse
  derivative of any polynomial representing the completed element modulo `Φ_n ^ (k + 1)`. This is
  independent of the representative: `Φ_n(ζ) = 0`, so `(X - ζ) ^ (k + 1)` divides `Φ_n ^ (k + 1)`
  over `B`, and the Hasse derivatives of order at most `k` of its multiples vanish at `ζ`. On a
  polynomial `p` it is the Taylor expansion `p(ζ + X)`, its constant coefficient is `evalRoot`, and
  each coefficient is locally constant, so the map is continuous for the coefficientwise topology.

The cyclotomic equation `Φ_n(ζ) = 0` cannot be replaced by `ζ` having multiplicative order `n`:
`3` has order two in `ZMod 8`, but `Φ_2(3) = 4 ≠ 0`. Hasse derivatives, rather than ordinary
derivatives divided by factorials, keep the construction valid over every coefficient ring. The
two agree up to the factor `k!` (`TauCeti.CycloCompletion.factorial_mul_coeff_taylorAt`); in
characteristic two the Taylor coefficient of `q ^ 2` at `1` in degree two is `1`, while its
second derivative vanishes.

## Main definitions

* `TauCeti.CycloCompletion.evalRoot`: evaluation `R[q]^S →ₐ[R] B` at a root of `Φ_n`, `n ∈ S`.
* `TauCeti.CycloCompletion.taylorAt`: the additive Taylor expansion `R[q]^S →ₐ[R] B⟦X⟧` at a root
  of `Φ_n`, `n ∈ S`.

## Main results

* `TauCeti.CycloCompletion.evalRoot_fromPoly`, `TauCeti.CycloCompletion.evalRoot_root`:
  evaluation on polynomials and at the universal root.
* `TauCeti.CycloCompletion.coeff_taylorAt_of_proj_eq_mk`: Taylor coefficients through finite
  projections, as Hasse derivatives of representatives.
* `TauCeti.CycloCompletion.taylorAt_fromPoly`: the polynomial Taylor equation.
* `TauCeti.CycloCompletion.constantCoeff_taylorAt`: the constant coefficient is `evalRoot`.
* `TauCeti.CycloCompletion.trunc_taylorAt_of_proj_eq_mk`: truncations of the Taylor expansion are
  computed by any representative modulo the corresponding power of `Φ_n`.
* `TauCeti.CycloCompletion.factorial_mul_coeff_taylorAt`: comparison with ordinary derivatives.
* `TauCeti.CycloCompletion.continuous_evalRoot`, `TauCeti.CycloCompletion.continuous_taylorAt`.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §1.
-/

public section

open Polynomial
open scoped PowerSeries Topology

namespace TauCeti

namespace CycloCompletion

open PolyFamilyLimit

variable {R : Type*} [CommRing R] {S : Set ℕ} {n : ℕ} {B : Type*} [CommRing B] [Algebra R B]

section EvalRoot

/-- The index `Φ_n` of `R[q]^S`. -/
private noncomputable abbrev cyclotomicIndex (hn : n ∈ S) : cycloIndex R S :=
  ⟨cyclotomic n R, cyclotomic_mem_cycloIndex hn⟩

/-- Evaluation of a completed element at a root `ζ` of `Φ_n`, `n ∈ S`, in an `R`-algebra `B`:
reduce modulo `Φ_n` and evaluate the class at `ζ`. -/
noncomputable def evalRoot (hn : n ∈ S) (ζ : B) (hζ : aeval ζ (cyclotomic n R) = 0) :
    CycloCompletion R S →ₐ[R] B :=
  ((AdjoinRoot.algHomEquiv B (cyclotomic n R)).symm ⟨ζ, hζ⟩).comp (proj (cyclotomicIndex hn))

variable (hn : n ∈ S) (ζ : B) (hζ : aeval ζ (cyclotomic n R) = 0)

/-- Root evaluation is the projection modulo `Φ_n` followed by evaluation of the class at `ζ`. -/
theorem evalRoot_apply (x : CycloCompletion R S) :
    evalRoot hn ζ hζ x = (AdjoinRoot.algHomEquiv B (cyclotomic n R)).symm ⟨ζ, hζ⟩
      (proj (g := fun f : cycloIndex R S ↦ (f : R[X]))
        ⟨cyclotomic n R, cyclotomic_mem_cycloIndex hn⟩ x) :=
  (rfl)

/-- Root evaluation can be computed from a representative at any index divisible by `Φ_n`. -/
theorem evalRoot_eq_aeval_of_proj_eq_mk {f : cycloIndex R S} (hf : cyclotomic n R ∣ (f : R[X]))
    {x : CycloCompletion R S} {p : R[X]} (h : proj f x = AdjoinRoot.mk (f : R[X]) p) :
    evalRoot hn ζ hζ x = aeval ζ p := by
  rw [evalRoot_apply, proj_eq_mk_of_dvd (f := cyclotomicIndex hn) hf h, AdjoinRoot.algHom_mk,
    AdjoinRoot.algHomEquiv_symm_apply_root]

/-- Root evaluation agrees with polynomial evaluation. -/
@[simp]
theorem evalRoot_fromPoly (p : R[X]) : evalRoot hn ζ hζ (fromPoly R S p) = aeval ζ p :=
  evalRoot_eq_aeval_of_proj_eq_mk hn ζ hζ (f := cyclotomicIndex hn) dvd_rfl (proj_fromPoly _ p)

/-- Evaluation at the universal root of `Φ_n` in `AdjoinRoot (cyclotomic n R)` is the projection
modulo `Φ_n`. -/
theorem evalRoot_root :
    evalRoot hn (AdjoinRoot.root (cyclotomic n R))
        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) =
      proj (⟨cyclotomic n R, cyclotomic_mem_cycloIndex hn⟩ : cycloIndex R S) := by
  ext x
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj (cyclotomicIndex hn) x)
  rw [evalRoot_eq_aeval_of_proj_eq_mk hn _ _ (f := cyclotomicIndex hn) dvd_rfl hp.symm,
    AdjoinRoot.aeval_eq, hp]

/-- Root evaluation is locally constant: it factors through a discrete quotient. -/
theorem isLocallyConstant_evalRoot : IsLocallyConstant (evalRoot hn ζ hζ) :=
  (isLocallyConstant_proj (cyclotomicIndex hn)).comp _

/-- Root evaluation is continuous for every topology on the target. -/
@[fun_prop, continuity]
theorem continuous_evalRoot [TopologicalSpace B] : Continuous (evalRoot hn ζ hζ) :=
  (isLocallyConstant_evalRoot hn ζ hζ).continuous

end EvalRoot

section Taylor

/-- The index `Φ_n ^ m` of `R[q]^S`. -/
private noncomputable def cyclotomicPowIndex (hn : n ∈ S) (m : ℕ) : cycloIndex R S :=
  ⟨cyclotomic n R ^ m, cyclotomic_pow_mem_cycloIndex hn m⟩

private theorem coe_cyclotomicPowIndex (hn : n ∈ S) (m : ℕ) :
    (cyclotomicPowIndex (R := R) hn m : R[X]) = cyclotomic n R ^ m :=
  (rfl)

/-- The reduced representative of a completed element modulo `Φ_n ^ (k + 1)`. -/
private noncomputable def taylorRep (hn : n ∈ S) (k : ℕ) (x : CycloCompletion R S) : R[X] :=
  AdjoinRoot.modByMonicHom (cycloIndex.monic (cyclotomicPowIndex hn (k + 1)))
    (proj (cyclotomicPowIndex hn (k + 1)) x)

private theorem proj_eq_mk_taylorRep (hn : n ∈ S) (k : ℕ) (x : CycloCompletion R S) :
    proj (cyclotomicPowIndex hn (k + 1)) x =
      AdjoinRoot.mk (cyclotomicPowIndex (R := R) hn (k + 1) : R[X]) (taylorRep hn k x) :=
  (AdjoinRoot.mk_leftInverse (cycloIndex.monic (cyclotomicPowIndex hn (k + 1)))
    (proj (cyclotomicPowIndex hn (k + 1)) x)).symm

/-- The coefficientwise definition of the Taylor expansion. -/
private noncomputable def taylorSeries (hn : n ∈ S) (ζ : B) (x : CycloCompletion R S) : B⟦X⟧ :=
  PowerSeries.mk fun k ↦ aeval ζ (hasseDeriv k (taylorRep hn k x))

private theorem coeff_taylorSeries_of_proj_eq_mk (hn : n ∈ S) {ζ : B}
    (hζ : aeval ζ (cyclotomic n R) = 0) {f : cycloIndex R S} {k : ℕ}
    (hf : cyclotomic n R ^ (k + 1) ∣ (f : R[X])) {x : CycloCompletion R S} {p : R[X]}
    (h : proj f x = AdjoinRoot.mk (f : R[X]) p) :
    PowerSeries.coeff k (taylorSeries hn ζ x) = aeval ζ (hasseDeriv k p) := by
  rw [taylorSeries, PowerSeries.coeff_mk]
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine aeval_hasseDeriv_eq_zero_of_pow_dvd hζ (m := k + 1) ?_ k.lt_succ_self
  rw [← coe_cyclotomicPowIndex hn, ← AdjoinRoot.mk_eq_mk, ← proj_eq_mk_taylorRep]
  exact proj_eq_mk_of_dvd (f := cyclotomicPowIndex hn (k + 1)) hf h

private theorem taylorSeries_fromPoly (hn : n ∈ S) {ζ : B} (hζ : aeval ζ (cyclotomic n R) = 0)
    (p : R[X]) :
    taylorSeries hn ζ (fromPoly R S p) = (taylor ζ (p.map (algebraMap R B)) : B⟦X⟧) := by
  ext k
  rw [coeff_taylorSeries_of_proj_eq_mk hn hζ (f := cyclotomicPowIndex hn (k + 1))
    (coe_cyclotomicPowIndex hn _).symm.dvd (proj_fromPoly _ p), Polynomial.coeff_coe,
    ← coeff_taylor_map_algebraMap]

/-- The Taylor coefficients of order at most `k` are computed by the representative modulo
`Φ_n ^ (k + 1)`. -/
private theorem coeff_taylorSeries_taylorRep (hn : n ∈ S) {ζ : B}
    (hζ : aeval ζ (cyclotomic n R) = 0) {i k : ℕ} (hik : i ≤ k) (x : CycloCompletion R S) :
    PowerSeries.coeff i (taylorSeries hn ζ x) = aeval ζ (hasseDeriv i (taylorRep hn k x)) :=
  coeff_taylorSeries_of_proj_eq_mk hn hζ (f := cyclotomicPowIndex hn (k + 1))
    (by rw [coe_cyclotomicPowIndex]; exact pow_dvd_pow _ (by omega)) (proj_eq_mk_taylorRep hn k x)

private theorem taylorSeries_mul (hn : n ∈ S) {ζ : B} (hζ : aeval ζ (cyclotomic n R) = 0)
    (x y : CycloCompletion R S) :
    taylorSeries hn ζ (x * y) = taylorSeries hn ζ x * taylorSeries hn ζ y := by
  ext k
  have hxy : proj (cyclotomicPowIndex hn (k + 1)) (x * y) =
      AdjoinRoot.mk (cyclotomicPowIndex (R := R) hn (k + 1) : R[X])
        (taylorRep hn k x * taylorRep hn k y) := by
    rw [map_mul, proj_eq_mk_taylorRep, proj_eq_mk_taylorRep, map_mul]
  rw [coeff_taylorSeries_of_proj_eq_mk hn hζ (coe_cyclotomicPowIndex hn _).symm.dvd hxy,
    PowerSeries.coeff_mul, ← coeff_taylor_map_algebraMap, Polynomial.map_mul, taylor_mul,
    coeff_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hk := Finset.mem_antidiagonal.mp hij
  rw [coeff_taylorSeries_taylorRep hn hζ (by omega : ij.1 ≤ k),
    coeff_taylorSeries_taylorRep hn hζ (by omega : ij.2 ≤ k),
    ← coeff_taylor_map_algebraMap, ← coeff_taylor_map_algebraMap]

private theorem taylorSeries_add (hn : n ∈ S) {ζ : B} (hζ : aeval ζ (cyclotomic n R) = 0)
    (x y : CycloCompletion R S) :
    taylorSeries hn ζ (x + y) = taylorSeries hn ζ x + taylorSeries hn ζ y := by
  ext k
  have hxy : proj (cyclotomicPowIndex hn (k + 1)) (x + y) =
      AdjoinRoot.mk (cyclotomicPowIndex (R := R) hn (k + 1) : R[X])
        (taylorRep hn k x + taylorRep hn k y) := by
    rw [map_add, proj_eq_mk_taylorRep, proj_eq_mk_taylorRep, map_add]
  rw [coeff_taylorSeries_of_proj_eq_mk hn hζ (coe_cyclotomicPowIndex hn _).symm.dvd hxy]
  simp only [map_add]
  rw [coeff_taylorSeries_taylorRep hn hζ le_rfl x, coeff_taylorSeries_taylorRep hn hζ le_rfl y]

/-- The additive Taylor expansion of `R[q]^S` at a root `ζ` of `Φ_n`, `n ∈ S`, in an `R`-algebra
`B`, as a power series in `X = q - ζ`. The coefficient of `X ^ k` is the value at `ζ` of the `k`-th
Hasse derivative of any representative modulo `Φ_n ^ (k + 1)`
(`TauCeti.CycloCompletion.coeff_taylorAt_of_proj_eq_mk`). -/
noncomputable def taylorAt (hn : n ∈ S) (ζ : B) (hζ : aeval ζ (cyclotomic n R) = 0) :
    CycloCompletion R S →ₐ[R] B⟦X⟧ where
  toFun := taylorSeries hn ζ
  map_one' := by
    rw [← map_one (fromPoly R S), taylorSeries_fromPoly hn hζ, Polynomial.map_one, taylor_one,
      map_one, Polynomial.coe_one]
  map_mul' := taylorSeries_mul hn hζ
  map_zero' := by
    rw [← map_zero (fromPoly R S), taylorSeries_fromPoly hn hζ, Polynomial.map_zero, map_zero,
      Polynomial.coe_zero]
  map_add' := taylorSeries_add hn hζ
  commutes' r := by
    rw [← fromPoly_C, taylorSeries_fromPoly hn hζ, Polynomial.map_C, taylor_C, Polynomial.coe_C,
      PowerSeries.algebraMap_apply]

variable (hn : n ∈ S) (ζ : B) (hζ : aeval ζ (cyclotomic n R) = 0)

/-- The coefficient of `X ^ k` in the Taylor expansion at `ζ` is the value at `ζ` of the `k`-th
Hasse derivative of a representative at any index divisible by `Φ_n ^ (k + 1)`. -/
theorem coeff_taylorAt_of_proj_eq_mk {f : cycloIndex R S} {k : ℕ}
    (hf : cyclotomic n R ^ (k + 1) ∣ (f : R[X])) {x : CycloCompletion R S} {p : R[X]}
    (h : proj f x = AdjoinRoot.mk (f : R[X]) p) :
    PowerSeries.coeff k (taylorAt hn ζ hζ x) = aeval ζ (hasseDeriv k p) :=
  coeff_taylorSeries_of_proj_eq_mk hn hζ hf h

/-- The polynomial Taylor equation: on a polynomial `p`, the Taylor expansion at `ζ` is
`p(ζ + X)`. -/
@[simp]
theorem taylorAt_fromPoly (p : R[X]) :
    taylorAt hn ζ hζ (fromPoly R S p) = (taylor ζ (p.map (algebraMap R B)) : B⟦X⟧) :=
  taylorSeries_fromPoly hn hζ p

/-- The constant coefficient of the Taylor expansion at `ζ` is the value at `ζ`. -/
@[simp]
theorem constantCoeff_taylorAt (x : CycloCompletion R S) :
    PowerSeries.constantCoeff (taylorAt hn ζ hζ x) = evalRoot hn ζ hζ x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj (cyclotomicIndex hn) x)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_taylorAt_of_proj_eq_mk hn ζ hζ (by rw [zero_add, pow_one]) hp.symm, hasseDeriv_zero,
    LinearMap.id_apply, evalRoot_eq_aeval_of_proj_eq_mk hn ζ hζ dvd_rfl hp.symm]

/-- The truncation below degree `m` of the Taylor expansion at `ζ` is that of any representative
at an index divisible by `Φ_n ^ m`. -/
theorem trunc_taylorAt_of_proj_eq_mk {f : cycloIndex R S} {m : ℕ}
    (hf : cyclotomic n R ^ m ∣ (f : R[X])) {x : CycloCompletion R S} {p : R[X]}
    (h : proj f x = AdjoinRoot.mk (f : R[X]) p) :
    PowerSeries.trunc m (taylorAt hn ζ hζ x) =
      PowerSeries.trunc m (taylor ζ (p.map (algebraMap R B)) : B⟦X⟧) := by
  ext k
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hk
  · rw [coeff_taylorAt_of_proj_eq_mk hn ζ hζ ((pow_dvd_pow _ hk).trans hf) h,
      Polynomial.coeff_coe, ← coeff_taylor_map_algebraMap]
  · rfl

/-- `k!` times the coefficient of `X ^ k` in the Taylor expansion at `ζ` is the value at `ζ` of
the `k`-th derivative of any representative at an index divisible by `Φ_n ^ (k + 1)`. -/
theorem factorial_mul_coeff_taylorAt {f : cycloIndex R S} {k : ℕ}
    (hf : cyclotomic n R ^ (k + 1) ∣ (f : R[X])) {x : CycloCompletion R S} {p : R[X]}
    (h : proj f x = AdjoinRoot.mk (f : R[X]) p) :
    (k.factorial : B) * PowerSeries.coeff k (taylorAt hn ζ hζ x) = aeval ζ (derivative^[k] p) := by
  rw [coeff_taylorAt_of_proj_eq_mk hn ζ hζ hf h]
  simp [← eval_map_algebraMap, ← hasseDeriv_map, ← iterate_derivative_map,
    eval_iterate_derivative_eq_factorial_mul]

/-- Each Taylor coefficient is locally constant: it factors through a discrete quotient. -/
theorem isLocallyConstant_coeff_taylorAt (k : ℕ) :
    IsLocallyConstant fun x : CycloCompletion R S ↦ PowerSeries.coeff k (taylorAt hn ζ hζ x) := by
  have h : (fun x : CycloCompletion R S ↦ PowerSeries.coeff k (taylorAt hn ζ hζ x)) =
      (fun a ↦ aeval ζ (hasseDeriv k
        (AdjoinRoot.modByMonicHom (cycloIndex.monic (cyclotomicPowIndex hn (k + 1))) a))) ∘
        proj (cyclotomicPowIndex hn (k + 1)) :=
    funext fun x ↦ coeff_taylorAt_of_proj_eq_mk hn ζ hζ (coe_cyclotomicPowIndex hn _).symm.dvd
      (proj_eq_mk_taylorRep hn k x)
  rw [h]
  exact (isLocallyConstant_proj (cyclotomicPowIndex hn (k + 1))).comp _

open PowerSeries.WithPiTopology in
/-- The Taylor expansion is continuous for the coefficientwise topology on `B⟦X⟧`, whatever the
topology on `B`. -/
@[fun_prop, continuity]
theorem continuous_taylorAt [TopologicalSpace B] : Continuous (taylorAt hn ζ hζ) :=
  continuous_iff_continuousAt.mpr fun x ↦ (tendsto_iff_coeff_tendsto (R := B) _ _ _).mpr fun k ↦
    ((isLocallyConstant_coeff_taylorAt hn ζ hζ k).continuous).tendsto x

end Taylor

/-! ### Reference values -/

/-- `q` evaluates to the chosen root. -/
example (hn : n ∈ S) (ζ : B) (hζ : aeval ζ (cyclotomic n R) = 0) :
    evalRoot hn ζ hζ (fromPoly R S X) = ζ := by
  simp

/-- The `k`-th Taylor coefficient of `q ^ m` at `ζ` is `binomial(m, k) ζ ^ (m - k)`. -/
example (hn : n ∈ S) (ζ : B) (hζ : aeval ζ (cyclotomic n R) = 0) (m k : ℕ) :
    PowerSeries.coeff k (taylorAt hn ζ hζ (fromPoly R S (X ^ m))) =
      (m.choose k : B) * ζ ^ (m - k) := by
  rw [taylorAt_fromPoly, Polynomial.coeff_coe]
  simp [coeff_X_add_C_pow, mul_comm]

/-- In characteristic two the Taylor coefficient of `q ^ 2` at `1` in degree two is `1`, although
the second derivative of `q ^ 2` vanishes there. -/
example (S : Set ℕ) (h1 : 1 ∈ S) :
    PowerSeries.coeff 2 (taylorAt h1 (1 : ZMod 2) (by simp) (fromPoly (ZMod 2) S (X ^ 2))) = 1 ∧
      aeval (1 : ZMod 2) (derivative^[2] (X ^ 2 : (ZMod 2)[X])) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [taylorAt_fromPoly, Polynomial.coeff_coe]
    simpa using coeff_X_add_C_pow (1 : ZMod 2) 2 2
  · rw [coe_aeval_eq_eval, eval_iterate_derivative_eq_factorial_mul, Nat.factorial_two,
      show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]

end CycloCompletion

end TauCeti
