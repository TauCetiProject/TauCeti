/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.RatFunc.PowerTower

/-!
# Places in a purely inseparable extension

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is purely
inseparable: every `z ∈ F'` has a power `z ^ q ^ n` in `F`, where `q` is the exponential
characteristic. Such an extension is invisible to places in the following sense.

* **A place of `F` has at most one place of `F'` above it.** Whether `z` is regular at a place
  `P'` of `F'` is decided by whether its power `z ^ q ^ n ∈ F` is regular at the place `P` below,
  so the valuation ring of `P'` — and hence `P'` itself — is determined by `P`. Together with the
  existence of extensions of places (`TauCeti.Place.restrict_surjective`), there is exactly one.
* **The fundamental identity has a single term:** at a place of an algebraic function field `F / k`
  and for `F' / F` finite, `e(P' ∣ P) · f(P' ∣ P) = [F' : F]`.
* **The residue extension is purely inseparable**, since the residue of `z` has the residue of
  `z ^ q ^ n` as a `q ^ n`-th power.

In particular, for a purely inseparable step of prime degree `p` the product `e · f` is `p`, so
the place is either totally ramified (`e = p`, `f = 1`) or has residue degree `p` (`e = 1`,
`f = p`). The clean conclusion `e = [F' : F]`, `f = 1` holds as soon as the residue extension is
also separable — for instance when the residue field of `P` is perfect, which is automatic over a
perfect constant field — because an extension that is both separable and purely inseparable is
trivial.

Without that hypothesis the conclusion fails, and the last section proves the standard
counterexample. Let `k` have characteristic `p` and let `s ∈ k` not be a `p`-th power. In
`F' = k(x)` over `F = k(t)` with `t = x ^ p`, the place `P'` of `x ^ p − s` lies over the zero `P`
of `t − s`, and `e(P' ∣ P) = 1`, `f(P' ∣ P) = p`: the residue field of `P` is `k`, while that of
`P'` is `k(s^{1/p})`.

## Main results

* `TauCeti.Place.restrict_injective_of_isPurelyInseparable`: in a purely inseparable extension,
  distinct places lie over distinct places; with the existence of extensions this is
  `TauCeti.Place.restrict_bijective_of_isPurelyInseparable`, a unique place above each place.
* `TauCeti.Place.ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable`:
  `e(P' ∣ P) · f(P' ∣ P) = [F' : F]` for every place `P'` of a finite purely inseparable extension
  of an algebraic function field.
* `TauCeti.Place.isPurelyInseparable_residueField`: the residue extension at a place of a purely
  inseparable extension is purely inseparable.
* `TauCeti.Place.relativeDegree_eq_one_of_isPurelyInseparable` and
  `TauCeti.Place.ramificationIdx_eq_finrank_of_isPurelyInseparable`: `f(P' ∣ P) = 1` and
  `e(P' ∣ P) = [F' : F]` when the residue extension is separable.
* `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_pow_sub_C`,
  `TauCeti.Place.ord_restrict_adicOfIrreducible_X_pow_sub_C` and
  `TauCeti.Place.relativeDegree_adicOfIrreducible_X_pow_sub_C`: the counterexample
  `e = 1`, `f = p` in `k(x) / k(x ^ p)` at the zero of `x ^ p − s`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.10, where the base field is assumed perfect throughout.
-/

public section

open IntermediateField Polynomial

namespace TauCeti

namespace Place

universe u u' v v'

section Extension

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

variable (k F) in
/-- An element `z` of `F'` with a positive power `z ^ m` in `F` is regular at a place `P'` of
`F' / k'` exactly when that power is regular at the place of `F / k` below `P'`. -/
theorem mem_integers_iff_of_algebraMap_eq_pow [Algebra.IsIntegral F F'] (P' : Place k' F')
    {z : F'} {m : ℕ} {a : F} (hm : m ≠ 0) (ha : algebraMap F F' a = z ^ m) :
    z ∈ P'.integers ↔ a ∈ (P'.restrict k F).integers := by
  rw [mem_integers_restrict_iff, ha, mem_integers_iff_ord_nonneg, mem_integers_iff_ord_nonneg,
    ord_pow]
  exact ⟨fun h ↦ by positivity, fun h ↦ nonneg_of_mul_nonneg_right h (by positivity)⟩

variable [IsPurelyInseparable F F']

variable (k F) in
/-- **A place has at most one extension in a purely inseparable extension**: two places of
`F' / k'` lying over the same place of `F / k` are equal. Each element of `F'` has a power in
`F`, and whether it is regular at a place above `P` is read off that power at `P`.

With `TauCeti.Place.restrict_surjective`, every place of `F / k` has exactly one extension; that
is `TauCeti.Place.restrict_bijective_of_isPurelyInseparable`. -/
theorem restrict_injective_of_isPurelyInseparable :
    Function.Injective (fun P' : Place k' F' ↦ P'.restrict k F) := by
  intro P' Q' h
  have h' : P'.restrict k F = Q'.restrict k F := h
  refine eq_of_integers_le fun z hz ↦ ?_
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F (ringExpChar F) z
  have hm : ringExpChar F ^ n ≠ 0 := pow_ne_zero _ (expChar_pos F (ringExpChar F)).ne'
  rw [mem_integers_iff_of_algebraMap_eq_pow k F P' hm ha] at hz
  rwa [mem_integers_iff_of_algebraMap_eq_pow k F Q' hm ha, ← h']

variable (k F) in
/-- **A place has exactly one extension in a purely inseparable extension**: if `F' / k'` is an
algebraic function field and `k' / k` is integral, restriction is a bijection from the places of
`F' / k'` to the places of `F / k`. -/
theorem restrict_bijective_of_isPurelyInseparable [Algebra.IsIntegral k k']
    (hF' : IsFunctionField k' F') :
    Function.Bijective (fun P' : Place k' F' ↦ P'.restrict k F) :=
  ⟨restrict_injective_of_isPurelyInseparable k F, restrict_surjective hF'⟩

variable (k F) in
/-- **The fundamental identity in a purely inseparable extension**: for a finite purely
inseparable extension `F' / F` of an algebraic function field `F / k`, the place `P'` is the only
place over the place `P` below it, so `e(P' ∣ P) · f(P' ∣ P) = [F' : F]`. No separability of the
residue extension is assumed. -/
theorem ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable
    [FiniteDimensional F F'] [Algebra.IsIntegral k k'] (hF : IsFunctionField k F)
    (P' : Place k' F') :
    ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' := by
  have := sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField (k' := k') k F hF
    (P'.restrict k F) (s := {P'}) fun Q' ↦ by
      rw [Finset.mem_singleton]
      exact ⟨fun h ↦ h ▸ rfl, fun h ↦ restrict_injective_of_isPurelyInseparable k F h⟩
  simpa using this

/-- **The residue extension of a purely inseparable extension is purely inseparable**: the
residue of `z ∈ 𝒪_{P'}` has the residue of the power `z ^ q ^ n ∈ F` as its `q ^ n`-th power. -/
instance isPurelyInseparable_residueField (P' : Place k' F') :
    IsPurelyInseparable (P'.restrict k F).ResidueField P'.ResidueField := by
  -- `F` and the residue field of the place below share the exponential characteristic of `k`.
  let q := ringExpChar k
  have : ExpChar F q := expChar_of_injective_algebraMap (algebraMap k F).injective q
  have : ExpChar (P'.restrict k F).ResidueField q :=
    expChar_of_injective_algebraMap (algebraMap k _).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q]
  intro x
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q (z : F')
  have hm : q ^ n ≠ 0 := pow_ne_zero _ (expChar_pos F q).ne'
  have haP : a ∈ (P'.restrict k F).integers :=
    (mem_integers_iff_of_algebraMap_eq_pow k F P' hm ha).mp z.2
  refine ⟨n, IsLocalRing.residue _ ⟨a, haP⟩, ?_⟩
  rw [IsLocalRing.ResidueField.algebraMap_residue, ← map_pow]
  congr 1
  exact Subtype.ext ha

variable (k F) in
/-- In a purely inseparable extension, **a place with separable residue extension has relative
degree one**: the residue extension is then both separable and purely inseparable, hence trivial.
The separability hypothesis holds in particular when the residue field of the place below is
perfect. -/
theorem relativeDegree_eq_one_of_isPurelyInseparable (P' : Place k' F')
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    relativeDegree k F P' = 1 := by
  rw [relativeDegree_def, ← Module.finrank_self (P'.restrict k F).ResidueField]
  exact ((AlgEquiv.ofBijective (Algebra.ofId _ _)
    (IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _)).toLinearEquiv.finrank_eq).symm

variable (k F) in
/-- In a finite purely inseparable extension of an algebraic function field, **a place with
separable residue extension is totally ramified**: `e(P' ∣ P) = [F' : F]`. The separability
hypothesis holds in particular when the residue field of the place below is perfect; without it
the conclusion fails, see `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_pow_sub_C`. -/
theorem ramificationIdx_eq_finrank_of_isPurelyInseparable
    [FiniteDimensional F F'] [Algebra.IsIntegral k k'] (hF : IsFunctionField k F)
    (P' : Place k' F') [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    ramificationIdx F P' = Module.finrank F F' := by
  simpa [relativeDegree_eq_one_of_isPurelyInseparable k F P'] using
    ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable k F hF P'

end Extension

/-! ### An unramified place of a purely inseparable extension

Let `k` have characteristic `p` and let `s ∈ k` not be a `p`-th power, so that `x ^ p − s` is
irreducible. In `k(x)` over `k(t)`, `t = x ^ p`, the place of `x ^ p − s` lies over the zero of
`t − s` with ramification index `1` and relative degree `p`, although the extension is purely
inseparable of degree `p`. The residue field `k` of the place below is not perfect. -/

section Unramified

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {s : k}

local notation "t" => (_root_.RatFunc.X : _root_.RatFunc k) ^ p

omit [CharP k p] in
/-- `t − s` is `x ^ p − s` in `k(x)`, a prime element at its own place. -/
private theorem ord_algebraMap_gen_sub (hs : ∀ c : k, c ^ p ≠ s) :
    (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out hs)).ord
      (algebraMap k⟮t⟯ (_root_.RatFunc k) (AdjoinSimple.gen k t - algebraMap k k⟮t⟯ s)) = 1 := by
  have : algebraMap k⟮t⟯ (_root_.RatFunc k) (AdjoinSimple.gen k t - algebraMap k k⟮t⟯ s) =
      algebraMap k[X] (_root_.RatFunc k) (X ^ p - C s) := by
    simp
  rw [this, ord_adicOfIrreducible_algebraMap_irreducible _
    (X_pow_sub_C_irreducible_of_prime Fact.out hs)]
  simp

/-- In `k(x) / k(x ^ p)`, the place of `x ^ p − s`, for `s` not a `p`-th power, is
**unramified**: `e = 1`, although the extension is purely inseparable of degree `p`. -/
theorem ramificationIdx_adicOfIrreducible_X_pow_sub_C (hs : ∀ c : k, c ^ p ≠ s) :
    ramificationIdx k⟮t⟯ (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out hs)) =
      1 := by
  have h := ord_algebraMap_restrict k k⟮t⟯
    (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out hs))
    (AdjoinSimple.gen k t - algebraMap k k⟮t⟯ s)
  rw [ord_algebraMap_gen_sub hs] at h
  exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h.symm

/-- In `k(x) / k(x ^ p)`, the place of `x ^ p − s`, for `s` not a `p`-th power, lies over the
zero of `t − s`, where `t = x ^ p`: the order of `t − s` at the place below is `1`. -/
theorem ord_restrict_adicOfIrreducible_X_pow_sub_C (hs : ∀ c : k, c ^ p ≠ s) :
    ((adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out hs)).restrict k k⟮t⟯).ord
      (AdjoinSimple.gen k t - algebraMap k k⟮t⟯ s) = 1 := by
  have h := ord_algebraMap_restrict k k⟮t⟯
    (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out hs))
    (AdjoinSimple.gen k t - algebraMap k k⟮t⟯ s)
  rwa [ord_algebraMap_gen_sub hs, ramificationIdx_adicOfIrreducible_X_pow_sub_C hs,
    Nat.cast_one, one_mul, eq_comm] at h

/-- In `k(x) / k(x ^ p)`, the place of `x ^ p − s`, for `s` not a `p`-th power, has
**relative degree `p`**: the whole degree of the purely inseparable extension is carried by the
residue extension. -/
theorem relativeDegree_adicOfIrreducible_X_pow_sub_C (hs : ∀ c : k, c ^ p ≠ s) :
    relativeDegree k k⟮t⟯ (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime Fact.out hs)) =
      p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : FiniteDimensional k⟮t⟯ (_root_.RatFunc k) :=
    Module.finite_of_finrank_pos (by rw [RatFunc.finrank_adjoin_X_pow]; exact hp)
  have := ramificationIdx_mul_relativeDegree_eq_finrank_of_isPurelyInseparable k k⟮t⟯
    (_root_.RatFunc.transcendental_X.pow hp).isFunctionField_adjoin
    (adicOfIrreducible (X_pow_sub_C_irreducible_of_prime (p := p) Fact.out hs))
  rwa [ramificationIdx_adicOfIrreducible_X_pow_sub_C hs, one_mul,
    RatFunc.finrank_adjoin_X_pow] at this

end Unramified

end Place

end TauCeti
