/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
public import TauCeti.FieldTheory.RatFunc.PowerTower
public import TauCeti.FieldTheory.RatFunc.Transcendental
-- Proof-only: irreducibility of `X ^ p - C a` for prime `p` when `a` is not a `p`-th power.
import Mathlib.FieldTheory.KummerPolynomial

/-!
# The genus can drop under an inseparable constant field extension

A finite separable constant field extension preserves the genus
(`TauCeti.genus_eq_genus_of_constantCompositum_eq_top`). This file records the standard example
showing that separability cannot be dropped (Stichtenoth, Section III.6, which refers to Deuring
for it). Let `p` be an odd prime, `k' = 𝔽_p(s)` and `k = 𝔽_p(t) ⊆ k'` with
`t = s ^ p`, so that `k' / k` is purely inseparable of degree `p`. Let `F' = k'(w)` and, inside it,
`x = w ^ 2 + s` and `y = w ^ p`, which satisfy `y ^ 2 = x ^ p - t`. The subfield `F = k(x, y)` of
`F'` is the function field of the curve `y ^ 2 = x ^ p - t` over `k`: since `X ^ p - t` is
squarefree of degree `p` over `k`, the field `F / k` has genus `(p - 1) / 2` and exact constant
field `k`. The compositum `F · k'` is all of `F'`, because `w = y / (x - s) ^ ((p - 1) / 2)`, and
`F' = k'(w)` has genus `0`.

## Main declarations

* `TauCeti.GenusDrop.constants`: the constant field `k = 𝔽_p(s ^ p)` inside `𝔽_p(s)`.
* `TauCeti.GenusDrop.curveField`: the function field `F = k(x, y)` inside `F' = 𝔽_p(s)(w)`.
* `TauCeti.GenusDrop.genus_curveField`: `F / k` has genus `(p - 1) / 2`.
* `TauCeti.GenusDrop.constantCompositum_eq_top`: `F' = F · k'`.
* `TauCeti.GenusDrop.genus_lt_genus`: `F' / k'` has genus `0`, so the genus drops.
* `TauCeti.GenusDrop.finrank_constants` and `TauCeti.GenusDrop.not_isSeparable_constants`:
  `k' / k` has degree `p` and is not separable (it is purely inseparable).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti.GenusDrop

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The constant fields `k = 𝔽_p(s ^ p) ⊆ k' = 𝔽_p(s)` -/

/-- The constant field `k = 𝔽_p(t)`, realized as the subfield `𝔽_p(s ^ p)` of `k' = 𝔽_p(s)`. -/
noncomputable abbrev constants : IntermediateField (ZMod p) (RatFunc (ZMod p)) :=
  (ZMod p)⟮(RatFunc.X : RatFunc (ZMod p)) ^ p⟯

/-- The radicand `t = s ^ p`, as an element of `k`. -/
noncomputable def radicand : constants p :=
  ⟨RatFunc.X ^ p, IntermediateField.mem_adjoin_simple_self _ _⟩

@[simp]
theorem coe_radicand : (radicand p : RatFunc (ZMod p)) = RatFunc.X ^ p := by rfl

/-- `k' / k` has degree `p`. -/
theorem finrank_constants : Module.finrank (constants p) (RatFunc (ZMod p)) = p :=
  TauCeti.RatFunc.finrank_adjoin_X_pow (ZMod p) p

/-- `k' / k` is a finite extension. -/
instance : FiniteDimensional (constants p) (RatFunc (ZMod p)) :=
  Module.finite_of_finrank_pos (by rw [finrank_constants]; exact hp.out.pos)

/-- `s` does not lie in `k`. -/
theorem X_notMem_constants : (RatFunc.X : RatFunc (ZMod p)) ∉ constants p := by
  intro hX
  have htop : constants p = ⊤ :=
    top_le_iff.mp ((RatFunc.adjoin_X (K := ZMod p)) ▸ IntermediateField.adjoin_simple_le_iff.mpr hX)
  have h := finrank_constants p
  rw [htop, IntermediateField.finrank_top] at h
  exact hp.out.one_lt.ne h

/-- `t` is not a `p`-th power in `k`: a `p`-th root of `s ^ p` in `k'` is `s`, which is not in
`k`. -/
theorem pow_ne_radicand (b : constants p) : b ^ p ≠ radicand p := by
  intro h
  have h' : (b : RatFunc (ZMod p)) ^ p = RatFunc.X ^ p := by
    rw [← coe_radicand, ← h, IntermediateField.coe_pow]
  have hsub := sub_pow_char (b : RatFunc (ZMod p)) RatFunc.X (p := p)
  rw [h', sub_self, pow_eq_zero_iff hp.out.ne_zero, sub_eq_zero] at hsub
  exact X_notMem_constants p (hsub ▸ b.2)

/-- `X ^ p - t` is irreducible over `k`. -/
theorem irreducible_X_pow_sub_C_radicand : Irreducible (X ^ p - C (radicand p)) :=
  X_pow_sub_C_irreducible_of_prime hp.out (pow_ne_radicand p)

/-- `k' / k` is not separable: it is purely inseparable
(`TauCeti.RatFunc.isPurelyInseparable_adjoin_X_pow`) and `s ∉ k`. -/
theorem not_isSeparable_constants : ¬ Algebra.IsSeparable (constants p) (RatFunc (ZMod p)) :=
  fun _ ↦ X_notMem_constants p (by
    obtain ⟨b, hb⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable (constants p)
      (RatFunc (ZMod p)) RatFunc.X
    have hb' : (b : RatFunc (ZMod p)) = RatFunc.X := hb
    exact hb' ▸ b.2)

/-! ### The function fields `F = k(x, y) ⊆ F' = k'(w)` -/

/-- `s`, viewed in `F' = k'(w)`. -/
noncomputable def sElement : RatFunc (RatFunc (ZMod p)) :=
  algebraMap (RatFunc (ZMod p)) _ RatFunc.X

/-- `x = w ^ 2 + s`. -/
noncomputable def genX : RatFunc (RatFunc (ZMod p)) :=
  RatFunc.X ^ 2 + sElement p

/-- `y = w ^ p`. -/
noncomputable def genY : RatFunc (RatFunc (ZMod p)) :=
  RatFunc.X ^ p

/-- `x` is transcendental over `k`: otherwise `w ^ 2 = x - s`, hence `w`, would be algebraic
over `k'`. -/
theorem transcendental_genX : Transcendental (constants p) (genX p) := by
  intro halg
  have h1 : IsAlgebraic (RatFunc (ZMod p)) (genX p) := halg.tower_top (RatFunc (ZMod p))
  have h2 : IsAlgebraic (RatFunc (ZMod p)) ((RatFunc.X : RatFunc (RatFunc (ZMod p))) ^ 2) := by
    have := h1.sub (isAlgebraic_algebraMap (RatFunc.X : RatFunc (ZMod p)))
    rwa [genX, sElement, add_sub_cancel_right] at this
  exact RatFunc.transcendental_X (IsAlgebraic.of_pow two_pos h2)

/-- The `k(x)`-algebra structure of `F'`, with `RatFunc.X` acting as `x`. -/
noncomputable instance instAlgebraRatFunc :
    Algebra (RatFunc (constants p)) (RatFunc (RatFunc (ZMod p))) :=
  ratFuncAlgebraOfTranscendental (transcendental_genX p)

instance instIsScalarTowerRatFunc :
    IsScalarTower (constants p) (RatFunc (constants p)) (RatFunc (RatFunc (ZMod p))) :=
  isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_genX p)

/-- `t`, viewed in `F'`, is `s ^ p`. -/
theorem algebraMap_radicand :
    algebraMap (constants p) (RatFunc (RatFunc (ZMod p))) (radicand p) = sElement p ^ p := by
  rw [IsScalarTower.algebraMap_apply (constants p) (RatFunc (ZMod p)),
    IntermediateField.algebraMap_apply, coe_radicand, map_pow]
  rfl

/-- The equation `y ^ 2 = x ^ p - t` in `F'`: `(w ^ 2 + s) ^ p = w ^ (2 p) + s ^ p` in
characteristic `p`. -/
theorem sq_genY : genY p ^ 2 = genX p ^ p - sElement p ^ p := by
  rw [genX, genY, add_pow_char _ _ p, add_sub_cancel_right, ← pow_mul, ← pow_mul, mul_comm]

/-- The value `f(x)` of `f = X ^ p - C t` at `x`, viewed in `F'`. -/
theorem algebraMap_X_pow_sub_C_radicand :
    algebraMap (RatFunc (constants p)) (RatFunc (RatFunc (ZMod p)))
      (algebraMap (constants p)[X] (RatFunc (constants p)) (X ^ p - C (radicand p))) =
      genX p ^ p - sElement p ^ p := by
  rw [map_sub, map_sub, map_pow, map_pow, RatFunc.algebraMap_X,
    algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_genX p), RatFunc.algebraMap_C,
    ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply, algebraMap_radicand]

/-- The function field `F = k(x, y)` of `y ^ 2 = x ^ p - t`, as the subfield `k(x)(y)` of
`F'`. -/
noncomputable def curveField :
    IntermediateField (RatFunc (constants p)) (RatFunc (RatFunc (ZMod p))) :=
  (RatFunc (constants p))⟮genY p⟯

/-- `y`, as an element of `F`. -/
noncomputable def genY' : curveField p :=
  ⟨genY p, IntermediateField.mem_adjoin_simple_self _ _⟩

@[simp]
theorem coe_genY' : (genY' p : RatFunc (RatFunc (ZMod p))) = genY p := by rfl

/-- `F' / F / k` is a scalar tower. The `k`-algebra structure of `F` is the one of `k(x)`, which
is that of `F'` restricted along `k(x) → F'`, so both composites agree by definition. -/
instance instIsScalarTowerCurveField :
    IsScalarTower (constants p) (curveField p) (RatFunc (RatFunc (ZMod p))) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `x`, as an element of `F`. -/
noncomputable def genX' : curveField p :=
  algebraMap (RatFunc (constants p)) (curveField p) RatFunc.X

/-- The defining equation of `x ∈ F`: it is the image of `X ∈ k(X)`. -/
theorem genX'_def : genX' p = algebraMap (RatFunc (constants p)) (curveField p) RatFunc.X :=
  (rfl)

@[simp]
theorem coe_genX' : (genX' p : RatFunc (RatFunc (ZMod p))) = genX p :=
  algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_genX p)

/-- `x` is transcendental over `k`, as an element of `F`. -/
theorem transcendental_genX' : Transcendental (constants p) (genX' p) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc (constants p)) (curveField p)).injective).mpr
    (RatFunc.transcendental_X (K := constants p))

/-- `y` generates `F` over `k(x)`. -/
theorem adjoin_genY'_eq_top : (RatFunc (constants p))⟮genY' p⟯ = ⊤ :=
  IntermediateField.lift_injective _ (by
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl)

/-- `x` and `y` generate `F` over `k`. -/
theorem adjoin_genX'_genY'_eq_top : (constants p)⟮genX' p, genY' p⟯ = ⊤ := by
  set E := (constants p)⟮genX' p, genY' p⟯
  -- `k(x) ⊆ E`, as the image of `k(X) = k⟮X⟯`
  have hX (f : RatFunc (constants p)) :
      algebraMap (RatFunc (constants p)) (curveField p) f ∈ E := by
    let φ := IsScalarTower.toAlgHom (constants p) (RatFunc (constants p)) (curveField p)
    have hf : φ f ∈ ((constants p)⟮(RatFunc.X : RatFunc (constants p))⟯).map φ :=
      (IntermediateField.map_mem_map _ _).mpr (by rw [RatFunc.adjoin_X]; trivial)
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hf
    exact IntermediateField.adjoin.mono _ _ _ (by simp [genX', φ]) hf
  have hle : ((RatFunc (constants p))⟮genY' p⟯).toSubfield ≤ E.toSubfield := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨f, rfl⟩
      exact hX f
    · simpa using IntermediateField.subset_adjoin (constants p) _
        (Set.mem_insert_of_mem _ (Set.mem_singleton (genY' p)))
  rw [adjoin_genY'_eq_top, IntermediateField.top_toSubfield] at hle
  exact eq_top_iff.mpr fun z _ ↦ hle (Subfield.mem_top z)

/-- The defining equation `y ^ 2 = x ^ p - t` of `F`, in the form `y ^ 2 = f(x)` with
`f = X ^ p - C t`. -/
theorem sq_genY' :
    genY' p ^ 2 = algebraMap (RatFunc (constants p)) (curveField p)
      (algebraMap (constants p)[X] (RatFunc (constants p)) (X ^ p - C (radicand p))) := by
  refine Subtype.ext ?_
  rw [IntermediateField.coe_pow, coe_genY', IntermediateField.coe_algebraMap_apply,
    algebraMap_X_pow_sub_C_radicand, sq_genY]

/-- `k` is the exact constant field of `F`. -/
theorem isIntegrallyClosedIn_curveField (h2 : p ≠ 2) :
    IsIntegrallyClosedIn (constants p) (curveField p) :=
  isIntegrallyClosedIn_of_sq_eq (CharP.cast_ne_zero_of_ne_of_prime (constants p) Nat.prime_two h2)
    (irreducible_X_pow_sub_C_radicand p).squarefree
    (by rw [natDegree_X_pow_sub_C]; exact hp.out.pos) (adjoin_genY'_eq_top p) (sq_genY' p)

/-- **The genus of `y ^ 2 = x ^ p - t` over `k = 𝔽_p(t)` is `(p - 1) / 2`.** -/
theorem genus_curveField (h2 : p ≠ 2) : genus (constants p) (curveField p) = (p - 1) / 2 := by
  rw [genus_eq_of_sq_eq (CharP.cast_ne_zero_of_ne_of_prime (constants p) Nat.prime_two h2)
    (irreducible_X_pow_sub_C_radicand p).squarefree
    (by rw [natDegree_X_pow_sub_C]; exact hp.out.pos) (adjoin_genY'_eq_top p) (sq_genY' p),
    natDegree_X_pow_sub_C]

/-- `w = y / (x - s) ^ ((p - 1) / 2)`. -/
theorem X_eq_genY_div (h2 : p ≠ 2) :
    (RatFunc.X : RatFunc (RatFunc (ZMod p))) = genY p / (genX p - sElement p) ^ ((p - 1) / 2) := by
  have hodd : Even (p - 1) := by
    obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two h2
    exact ⟨m, by omega⟩
  rw [genX, add_sub_cancel_right, genY, ← pow_mul, Nat.two_mul_div_two_of_even hodd,
    eq_div_iff (pow_ne_zero _ RatFunc.X_ne_zero), ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le]

/-- **`F' = F · k'`**: the extension `F' / F` is the constant field extension by `k'`. -/
theorem constantCompositum_eq_top (h2 : p ≠ 2) :
    constantCompositum (curveField p) (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p))) = ⊤ := by
  set C := constantCompositum (curveField p) (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p)))
  have hs : sElement p ∈ C := algebraMap_mem_constantCompositum _ _ _ RatFunc.X
  have hy : genY p ∈ C := IntermediateField.algebraMap_mem C (genY' p)
  have hx : genX p ∈ C := by
    rw [← algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_genX p),
      IsScalarTower.algebraMap_apply (RatFunc (constants p)) (curveField p)]
    exact IntermediateField.algebraMap_mem C _
  have hX : (RatFunc.X : RatFunc (RatFunc (ZMod p))) ∈ C := by
    rw [X_eq_genY_div p h2]
    exact div_mem hy (pow_mem (sub_mem hx hs) _)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  have hle : (RatFunc (ZMod p))⟮(RatFunc.X : RatFunc (RatFunc (ZMod p)))⟯.toSubfield ≤
      C.toSubfield := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (by simpa using hX))
    rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_constantCompositum _ _ _ c
  exact hle (by rw [RatFunc.adjoin_X, IntermediateField.top_toSubfield]; exact Subfield.mem_top z)

/-- **The genus drops**: `F' / k'` is rational, of genus `0`, while `F / k` has genus
`(p - 1) / 2 ≥ 1`. -/
theorem genus_lt_genus (h2 : p ≠ 2) :
    genus (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p))) < genus (constants p) (curveField p) := by
  rw [genus_ratFunc, genus_curveField p h2]
  have := hp.out.two_le
  omega

end TauCeti.GenusDrop
