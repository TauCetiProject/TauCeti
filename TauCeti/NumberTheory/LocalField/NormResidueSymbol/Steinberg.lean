/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic
import TauCeti.FieldTheory.Kummer.Norm
import TauCeti.GroupTheory.Abelianization.Basic

/-!
# The Steinberg relation and skew symmetry of the norm-residue symbol

For a nonarchimedean local field `K` containing the `n`-th roots of unity, this file proves the
fundamental algebraic identities of `normResidueSymbol K n` beyond bimultiplicativity:

* **The Steinberg relation** (`normResidueSymbol_eq_one_of_add_eq_one`,
  `normResidueSymbol_one_sub_left`, `normResidueSymbol_one_sub_right`): `(a, b)_{K, n} = 1`
  whenever `(a : K) + b = 1`; equivalently `(1 - a, a)_{K, n} = 1` and `(a, 1 - a)_{K, n} = 1`
  for `(1 : K) - a ≠ 0`.
* **Additive-inverse cancellation** (`normResidueSymbol_neg_self_left`,
  `normResidueSymbol_neg_self_right`): `(-a, a)_{K, n} = 1` and `(a, -a)_{K, n} = 1`, whence
  `(a, a)_{K, n} = (a, -1)_{K, n} = (-1, a)_{K, n}` (`normResidueSymbol_self_eq_neg_one_right`,
  `normResidueSymbol_self_eq_neg_one_left`), which equals `1` when `n` is odd
  (`normResidueSymbol_self_of_odd`).
* **Skew symmetry** (`normResidueSymbol_mul_swap`, `normResidueSymbol_swap`,
  `normResidueSymbolPairing_swap`): `(a, b)_{K, n} * (b, a)_{K, n} = 1`, equivalently
  `(b, a)_{K, n} = (a, b)_{K, n}⁻¹`, both on `Kˣ` and on `Kˣ ⧸ (Kˣ)ⁿ`.

The Steinberg relation is deduced via `Submonoid.mem_of_add_eq_one_of_normUnits_mem` (factored from
`TauCeti/FieldTheory/GaloisCohomology/Steinberg.lean`,
`TauCeti.explicitCup11_kummerMap_eq_zero_of_add_eq_one`) together with local reciprocity for simple
radical extensions `L = K(β)` (`βⁿ = b`). Together with bimultiplicativity and degree/field
functoriality, these identities supply the full algebraic calculus of the local norm-residue symbol
used in nondegeneracy, the norm criterion, and power reciprocity.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, Chapter IV, §5,
  (5.1) Proposition (2)–(4), pp. 143–144.
* J. S. Milne, *Class Field Theory*, Chapter III, §4, Theorem 4.4 (a)–(b), p. 113.
* J. Tate, *Relations between K₂ and Galois cohomology*, Invent. Math. 36 (1976), 257–274.
-/

public section

noncomputable section

open IntermediateField

namespace TauCeti

open ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-- **The Steinberg relation for the norm-residue symbol.** If `a, b ∈ Kˣ` satisfy
`(a : K) + b = 1`, then `(a, b)_{K, n} = 1`. -/
theorem normResidueSymbol_eq_one_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    normResidueSymbol K n a b = 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  let S : Submonoid Kˣ :=
    { carrier := {c : Kˣ | normResidueSymbol K n c b = 1}
      one_mem' := normResidueSymbol_one_left b
      mul_mem' := fun {c₁ c₂} hc₁ hc₂ ↦ by
        simp only [Set.mem_ofPred_eq] at hc₁ hc₂ ⊢
        rw [normResidueSymbol_mul_left, hc₁, hc₂, mul_one] }
  refine S.mem_of_add_eq_one_of_normUnits_mem hζ.neZero'.out hab
    fun L _ _ _ _ β hβ hgen c ↦ ?_
  have hβ_val : (β : L) ^ n = algebraMap K L b := by
    simpa [Units.coe_map] using congrArg Units.val hβ
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ hβ_val hgen
  have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ hβ_val hgen
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap K (Algebra.normUnits K c))
  -- Since `N_{L/K} c ∈ N_{L/K}(Lˣ)`, `Art_K(N_{L/K} c)` acts trivially on `L = K(β)`.
  have hτ1 : ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) = 1 := by
    have h0 := (localArtinMap_eq_zero_iff K L ι (Algebra.normUnits K c)).2
      (normUnits_mem_normGroup K L c)
    rwa [artinMap_restrict K L ι (Algebra.normUnits K c) σ hσ, ofMul_eq_zero,
      ← map_one Group.Abelianization.of, Group.Abelianization.of_injective.eq_iff] at h0
  have hfix : absoluteGaloisGroupRestrictEquiv K σ (ι β) = ι β := by
    rw [← ι.restrictNormalHom_commutes, hτ1, AlgEquiv.one_apply]
  have hspec := normResidueSymbol_spec_separableClosure (Algebra.normUnits K c) b σ hσ (β := ι β)
    (by rw [← map_pow, hβ_val, ι.commutes])
  have hval : algebraMap K (SeparableClosure K)
      ((normResidueSymbol K n (Algebra.normUnits K c) b : Kˣ) : K) = 1 :=
    mul_right_cancel₀ (map_ne_zero_iff ι ι.injective |>.2 β.ne_zero)
      (by simpa [hfix] using hspec.symm)
  exact Subtype.ext (Units.ext ((algebraMap K (SeparableClosure K)).injective
    (by simpa using hval)))

/-- **The Steinberg relation in `(1 - a, a)` form.** For `a ∈ Kˣ` with `(1 : K) - a ≠ 0`,
`(1 - a, a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_one_sub_left (a : Kˣ) (h : (1 : K) - a ≠ 0) :
    normResidueSymbol K n (Units.mk0 (1 - (a : K)) h) a = 1 :=
  normResidueSymbol_eq_one_of_add_eq_one (sub_add_cancel 1 (a : K))

/-- **Additive-inverse cancellation in the Artin argument.** For every `a ∈ Kˣ`,
`(-a, a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_neg_self_left (a : Kˣ) : normResidueSymbol K n (-a) a = 1 := by
  by_cases ha1 : a = 1
  · subst ha1
    exact normResidueSymbol_one_right (-1)
  have h1 : (1 : K) - a ≠ 0 := sub_ne_zero.2 fun h ↦ ha1 (Units.ext h.symm)
  have h2 : (1 : K) - (a⁻¹ : Kˣ) ≠ 0 :=
    sub_ne_zero.2 fun h ↦ ha1 (inv_eq_one.1 (Units.ext h.symm))
  set u₁ : Kˣ := Units.mk0 (1 - (a : K)) h1
  set u₂ : Kˣ := Units.mk0 (1 - ((a⁻¹ : Kˣ) : K)) h2
  -- In `Kˣ`, `(-a) * (1 - a⁻¹) = 1 - a`, and both `1 - a` and `1 - a⁻¹` pair trivially with `a`.
  have hmul : -a * u₂ = u₁ := Units.ext <| by
    simp only [u₁, u₂, Units.val_mul, Units.val_neg, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [mul_sub, mul_one, neg_mul, mul_inv_cancel₀ a.ne_zero]
    ring
  have hu₂ : normResidueSymbol K n u₂ a = 1 := by
    rw [← inv_inv a, normResidueSymbol_inv_right, normResidueSymbol_one_sub_left a⁻¹ h2, inv_one]
  have hprod : normResidueSymbol K n (-a) a * normResidueSymbol K n u₂ a =
      normResidueSymbol K n u₁ a := by
    rw [← normResidueSymbol_mul_left, hmul]
  rwa [hu₂, mul_one, normResidueSymbol_one_sub_left a h1] at hprod

/-- **Skew symmetry of the norm-residue symbol, product form.** For all `a, b ∈ Kˣ`,
`(a, b)_{K, n} * (b, a)_{K, n} = 1`. -/
theorem normResidueSymbol_mul_swap (a b : Kˣ) :
    normResidueSymbol K n a b * normResidueSymbol K n b a = 1 := by
  have hneg (x : Kˣ) : normResidueSymbol K n (-1) x * normResidueSymbol K n x x = 1 := by
    rw [← normResidueSymbol_mul_left, neg_one_mul, normResidueSymbol_neg_self_left]
  -- Expand `1 = (-(a * b), a * b) = ((-1) * a * b, a * b)` by bimultiplicativity.
  have hexp := normResidueSymbol_neg_self_left (n := n) (a * b)
  rw [← neg_one_mul (a * b), normResidueSymbol_mul_left, normResidueSymbol_mul_left,
    normResidueSymbol_mul_right, normResidueSymbol_mul_right, normResidueSymbol_mul_right] at hexp
  have hrearr :
      normResidueSymbol K n (-1) a * normResidueSymbol K n (-1) b *
        ((normResidueSymbol K n a a * normResidueSymbol K n a b) *
          (normResidueSymbol K n b a * normResidueSymbol K n b b)) =
      (normResidueSymbol K n (-1) a * normResidueSymbol K n a a) *
        (normResidueSymbol K n (-1) b * normResidueSymbol K n b b) *
        (normResidueSymbol K n a b * normResidueSymbol K n b a) := by
    ac_rfl
  rwa [hrearr, hneg a, hneg b, one_mul, one_mul] at hexp

/-- **Skew symmetry of the norm-residue symbol.** Swapping the two arguments inverts the symbol:
`(b, a)_{K, n} = (a, b)_{K, n}⁻¹`. -/
theorem normResidueSymbol_swap (a b : Kˣ) :
    normResidueSymbol K n b a = (normResidueSymbol K n a b)⁻¹ :=
  eq_inv_of_mul_eq_one_right (normResidueSymbol_mul_swap a b)

/-- **Additive-inverse cancellation in the radical argument.** For every `a ∈ Kˣ`,
`(a, -a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_neg_self_right (a : Kˣ) : normResidueSymbol K n a (-a) = 1 := by
  rw [normResidueSymbol_swap, normResidueSymbol_neg_self_left, inv_one]

/-- **The Steinberg relation in `(a, 1 - a)` form.** For `a ∈ Kˣ` with `(1 : K) - a ≠ 0`,
`(a, 1 - a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_one_sub_right (a : Kˣ) (h : (1 : K) - a ≠ 0) :
    normResidueSymbol K n a (Units.mk0 (1 - (a : K)) h) = 1 := by
  rw [normResidueSymbol_swap, normResidueSymbol_one_sub_left a h, inv_one]

/-- Pairing a unit with itself equals pairing it with `-1` in the radical argument. -/
theorem normResidueSymbol_self_eq_neg_one_right (a : Kˣ) :
    normResidueSymbol K n a a = normResidueSymbol K n a (-1) := by
  have h : normResidueSymbol K n a (-1) * normResidueSymbol K n a a = 1 := by
    rw [← normResidueSymbol_mul_right, neg_one_mul, normResidueSymbol_neg_self_right]
  rw [eq_inv_of_mul_eq_one_right h, ← normResidueSymbol_inv_right, inv_neg_one]

/-- Pairing a unit with itself equals pairing `-1` with it in the Artin argument. -/
theorem normResidueSymbol_self_eq_neg_one_left (a : Kˣ) :
    normResidueSymbol K n a a = normResidueSymbol K n (-1) a := by
  have h : normResidueSymbol K n (-1) a * normResidueSymbol K n a a = 1 := by
    rw [← normResidueSymbol_mul_left, neg_one_mul, normResidueSymbol_neg_self_left]
  rw [eq_inv_of_mul_eq_one_right h, ← normResidueSymbol_inv_left, inv_neg_one]

/-- When `n` is odd, every unit pairs trivially with itself: `(a, a)_{K, n} = 1`. -/
theorem normResidueSymbol_self_of_odd (hn : Odd n) (a : Kˣ) :
    normResidueSymbol K n a a = 1 := by
  have hpow : (-1 : Kˣ) ^ n = -1 := hn.neg_one_pow
  rw [normResidueSymbol_self_eq_neg_one_right, ← hpow, normResidueSymbol_pow_right_eq_one]

/-- **Skew symmetry of the descended pairing on `n`-th power classes.** -/
theorem normResidueSymbolPairing_swap (x y : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing (K := K) (n := n) y x =
      (normResidueSymbolPairing (K := K) (n := n) x y)⁻¹ := by
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  obtain ⟨b, rfl⟩ := powerClassHom_surjective Kˣ n y
  simp only [powerClassHom_apply, normResidueSymbolPairing_mk]
  exact normResidueSymbol_swap a b

end TauCeti
