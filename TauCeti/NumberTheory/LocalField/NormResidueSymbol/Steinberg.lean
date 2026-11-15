/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.FieldTheory.Kummer.Steinberg
import TauCeti.GroupTheory.Abelianization.Basic

/-!
# The Artin norm criterion, Steinberg relation, and skew symmetry of the norm-residue symbol

Let `K` be a nonarchimedean local field containing the `n`-th roots of unity. The degree-`n`
norm-residue symbol `normResidueSymbol K n a b ∈ rootsOfUnity n K` of
`TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic` puts `a` in the local Artin map and `b`
under the `n`-th radical. Because `a` enters directly through `artinMap K`, local reciprocity for
the cyclic radical extension `L = K(ⁿ√b)` immediately characterizes when `(a, b) = 1` in the first
argument (`normResidueSymbol_eq_one_iff_mem_normGroup`):

`(a, b) = 1 ↔ a ∈ N_{L/K}(Lˣ)`.

Combining this Artin norm criterion with the field-theoretic Steinberg norm identity of
`TauCeti.FieldTheory.Kummer.Steinberg` (`xⁿ - b ∈ N_{L/K}(Lˣ)`) gives `(xⁿ - b, b) = 1` whenever
`xⁿ - b ∈ Kˣ`, and in particular the **Steinberg relation** `(a, b) = 1` for `a + b = 1`
(`normResidueSymbol_eq_one_of_add_eq_one`). From `(1 - a, a) = 1` and `(1 - a⁻¹, a⁻¹) = 1` via
`-a = (1 - a) / (1 - a⁻¹)` follows `(-a, a) = 1` (`normResidueSymbol_neg_self_left`), hence
`(a, a) = (-1, a)` of order dividing `2`, and expanding `(-(a * b), a * b) = 1` yields **skew
symmetry** `(b, a) = (a, b)⁻¹` (`normResidueSymbol_symm`).

## Main results

* `TauCeti.normResidueSymbol_inv_left`, `TauCeti.normResidueSymbol_inv_right`,
  `TauCeti.normResidueSymbol_div_left`, `TauCeti.normResidueSymbol_div_right`,
  `TauCeti.normResidueSymbol_zpow_left`, `TauCeti.normResidueSymbol_zpow_right`: inverses,
  quotients, and integer powers in either argument of `normResidueSymbol`.
* `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup`: for `L = K(s)` with `sⁿ = b`,
  `normResidueSymbol K n a b = 1 ↔ a ∈ normGroup K L`.
* `TauCeti.normResidueSymbol_pow_sub_left` and `TauCeti.normResidueSymbol_eq_one_of_add_eq_one`:
  `(xⁿ - b, b) = 1` and the Steinberg relation `(a, b) = 1` for `(a : K) + b = 1`.
* `TauCeti.normResidueSymbol_neg_self_left`, `TauCeti.normResidueSymbol_neg_self_right`:
  `(-a, a) = 1` and `(a, -a) = 1`.
* `TauCeti.normResidueSymbol_mul_symm`, `TauCeti.normResidueSymbol_symm`,
  `TauCeti.normResidueSymbolPairing_symm`: skew symmetry `(a, b) * (b, a) = 1` and
  `(b, a) = (a, b)⁻¹` on units and on power classes.
* `TauCeti.normResidueSymbol_self_eq_neg_one_left`,
  `TauCeti.normResidueSymbol_self_eq_neg_one_right`, `TauCeti.normResidueSymbol_self_sq`,
  `TauCeti.normResidueSymbol_self_of_odd`: `(a, a) = (-1, a) = (a, -1)`, `(a, a)² = 1`, and
  `(a, a) = 1` for odd `n`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., AMS Translations
  of Mathematical Monographs 121 (2002), Chapter IV, §5, (5.1) Proposition (1)–(6) and Corollary,
  pp. 143–144.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter III, §4, Theorem 4.4.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory _root_.IntermediateField

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-! ### Bimultiplicativity for inverses, quotients, and integer powers -/

/-- Inversion in the Artin argument inverts the norm-residue symbol. -/
@[simp]
theorem normResidueSymbol_inv_left (a b : Kˣ) :
    normResidueSymbol K n a⁻¹ b = (normResidueSymbol K n a b)⁻¹ := by
  rw [← normResidueSymbolPairing_mk, QuotientGroup.mk_inv, map_inv, MonoidHom.inv_apply,
    normResidueSymbolPairing_mk]

/-- Inversion in the radical argument inverts the norm-residue symbol. -/
@[simp]
theorem normResidueSymbol_inv_right (a b : Kˣ) :
    normResidueSymbol K n a b⁻¹ = (normResidueSymbol K n a b)⁻¹ := by
  rw [← normResidueSymbolPairing_mk, QuotientGroup.mk_inv (N := powerSubgroup Kˣ n) b, map_inv,
    normResidueSymbolPairing_mk]

/-- Division in the Artin argument divides the norm-residue symbols. -/
theorem normResidueSymbol_div_left (a a' b : Kˣ) :
    normResidueSymbol K n (a / a') b =
      normResidueSymbol K n a b / normResidueSymbol K n a' b := by
  rw [div_eq_mul_inv, normResidueSymbol_mul_left, normResidueSymbol_inv_left, div_eq_mul_inv]

/-- Division in the radical argument divides the norm-residue symbols. -/
theorem normResidueSymbol_div_right (a b b' : Kˣ) :
    normResidueSymbol K n a (b / b') =
      normResidueSymbol K n a b / normResidueSymbol K n a b' := by
  rw [div_eq_mul_inv, normResidueSymbol_mul_right, normResidueSymbol_inv_right, div_eq_mul_inv]

/-- Integer powers in the Artin argument become integer powers of the norm-residue symbol. -/
theorem normResidueSymbol_zpow_left (a b : Kˣ) (k : ℤ) :
    normResidueSymbol K n (a ^ k) b = normResidueSymbol K n a b ^ k := by
  rw [← normResidueSymbolPairing_mk, QuotientGroup.mk_zpow, map_zpow, MonoidHom.zpow_apply,
    normResidueSymbolPairing_mk]

/-- Integer powers in the radical argument become integer powers of the norm-residue symbol. -/
theorem normResidueSymbol_zpow_right (a b : Kˣ) (k : ℤ) :
    normResidueSymbol K n a (b ^ k) = normResidueSymbol K n a b ^ k := by
  rw [← normResidueSymbolPairing_mk, QuotientGroup.mk_zpow (N := powerSubgroup Kˣ n) b k, map_zpow,
    normResidueSymbolPairing_mk]

/-- An element of `(Kˣ)ⁿ` in the Artin argument pairs trivially with every unit. -/
theorem normResidueSymbol_eq_one_of_mem_powerSubgroup_left {a : Kˣ}
    (ha : a ∈ powerSubgroup Kˣ n) (b : Kˣ) :
    normResidueSymbol K n a b = 1 := by
  obtain ⟨c, rfl⟩ := (mem_powerSubgroup_iff n).1 ha
  exact normResidueSymbol_pow_left_eq_one c b

/-- An element of `(Kˣ)ⁿ` in the radical argument pairs trivially with every unit. -/
theorem normResidueSymbol_eq_one_of_mem_powerSubgroup_right (a : Kˣ) {b : Kˣ}
    (hb : b ∈ powerSubgroup Kˣ n) :
    normResidueSymbol K n a b = 1 := by
  obtain ⟨c, rfl⟩ := (mem_powerSubgroup_iff n).1 hb
  exact normResidueSymbol_pow_right_eq_one a c

/-! ### The norm criterion in the Artin argument -/

/-- **The norm criterion in the Artin argument.** Let `L = K(s)` be a finite radical extension
generated over `K` by an element `s ∈ L` with `sⁿ = b`. Then `(a, b) = 1` if and only if `a` lies
in the norm subgroup `N_{L/K}(Lˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] (a b : Kˣ) {s : L} (hs : s ^ n = algebraMap K L b)
    (hgen : K⟮s⟯ = ⊤) :
    normResidueSymbol K n a b = 1 ↔ a ∈ normGroup K L := by
  -- A representative of `Art_K(a)` fixes `s` precisely when `Art_{L/K}(a) = 1` in the cyclic
  -- Galois group `Gal(L/K)`, which by local reciprocity is equivalent to `a ∈ N_{L/K}(Lˣ)`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ hs hgen
  have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ hs hgen
  let _ : CommGroup Gal(L/K) := IsCyclic.commGroup
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let j : L →ₐ[K] AlgebraicClosure K := (separableClosure K (AlgebraicClosure K)).val.comp ι
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) (artinMap K a)
  set τ : Gal(L/K) := ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ)
  have hjs : j s ^ n = algebraMap K (AlgebraicClosure K) b := by
    rw [← map_pow, hs, AlgHom.commutes]
  -- On the image of `s` in `AlgebraicClosure K`, `σ` acts as `τ`.
  have hστ : σ (j s) = j (τ s) := by
    have hcomm : ((ι (τ s) : SeparableClosure K) : AlgebraicClosure K) = σ (j s) := by
      rw [ι.restrictNormalHom_commutes, coe_absoluteGaloisGroupRestrictEquiv_apply]
      rfl
    exact hcomm.symm
  have htop : Algebra.adjoin K {s} = ⊤ := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.of_pow (NeZero.pos n) (hs ▸ isIntegral_algebraMap)).isAlgebraic, hgen,
      top_toSubalgebra]
  have hsym : normResidueSymbol K n a b = 1 ↔ τ = 1 := by
    rw [← Subtype.coe_inj, ← Units.val_inj, ← (algebraMap K (AlgebraicClosure K)).injective.eq_iff,
      algebraMap_normResidueSymbol a b σ hσ hjs, Subgroup.coe_one, Units.val_one, map_one,
      div_eq_one_iff_eq (ne_zero_of_pow_eq_algebraMap hjs), hστ,
      Function.Injective.eq_iff (f := j) j.injective]
    refine ⟨fun h ↦ AlgEquiv.coe_toAlgHom_injective
      (AlgHom.ext_of_adjoin_eq_top htop (Set.eqOn_singleton.2 h)), fun h ↦ by simp [h]⟩
  rw [hsym, ← Group.Abelianization.of_injective.eq_iff, map_one,
    ← ofMul_eq_zero, ← artinMap_restrict K L ι a σ hσ, localArtinMap_eq_zero_iff]

/-- In any field extension `E/K` containing an `n`-th root `β` of `b`, `(a, b) = 1` holds if and
only if `a` is a unit norm from `K⟮β⟯`. -/
theorem normResidueSymbol_eq_one_iff_mem_range_normUnits_adjoin {E : Type*} [Field E]
    [Algebra K E] (a b : Kˣ) {β : E} (hβ : β ^ n = algebraMap K E b) :
    normResidueSymbol K n a b = 1 ↔ a ∈ (Algebra.normUnits K : K⟮β⟯ˣ →* Kˣ).range := by
  have : FiniteDimensional K K⟮β⟯ :=
    adjoin.finiteDimensional (.of_pow (NeZero.pos n) (hβ ▸ isIntegral_algebraMap))
  have ht : AdjoinSimple.gen K β ^ n = algebraMap K K⟮β⟯ b := Subtype.ext (by simpa using hβ)
  exact (normResidueSymbol_eq_one_iff_mem_normGroup a b ht (adjoin_adjoinSimple_gen_eq_top β)).trans
    mem_normGroup_iff_exists_normUnits

/-! ### The Steinberg relation and skew symmetry -/

/-- **Radical difference relation in the Artin argument.** For `x ∈ K` and `u, b ∈ Kˣ` with
`u = xⁿ - b`, the norm-residue symbol `(u, b)` is `1`. -/
theorem normResidueSymbol_pow_sub_left {x : K} {u b : Kˣ} (hu : (u : K) = x ^ n - b) :
    normResidueSymbol K n u b = 1 := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) b)
    (NeZero.pos n)
  have : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have ht : AdjoinSimple.gen K β ^ n = algebraMap K K⟮β⟯ b := Subtype.ext (by simpa using hβ)
  have hgen := adjoin_adjoinSimple_gen_eq_top (F := K) β
  exact (normResidueSymbol_eq_one_iff_mem_normGroup u b ht hgen).2
    (pow_sub_mem_normGroup_of_pow_eq hu ht hgen)

/-- **The Steinberg relation for the norm-residue symbol.** If `a, b ∈ Kˣ` satisfy `a + b = 1` in
`K`, then `(a, b) = 1`. -/
theorem normResidueSymbol_eq_one_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    normResidueSymbol K n a b = 1 :=
  normResidueSymbol_pow_sub_left (x := 1) (by rw [one_pow]; linear_combination hab)

/-- For `a ∈ Kˣ` with `1 - (a : K) ≠ 0`, the unit `1 - a` pairs trivially on the left with `a`. -/
theorem normResidueSymbol_unitsMk0_one_sub_left {a : Kˣ} (ha : 1 - (a : K) ≠ 0) :
    normResidueSymbol K n (Units.mk0 (1 - (a : K)) ha) a = 1 :=
  normResidueSymbol_eq_one_of_add_eq_one (by simp)

/-- **Triviality on `(-a, a)`.** For every `a ∈ Kˣ`, `(-a, a) = 1`. -/
@[simp]
theorem normResidueSymbol_neg_self_left (a : Kˣ) :
    normResidueSymbol K n (-a) a = 1 := by
  -- For `a ≠ 1`, write `-a = (1 - a) / (1 - a⁻¹)` and apply the Steinberg relation to `a` and
  -- `a⁻¹`.
  by_cases ha : (a : K) = 1
  · obtain rfl : a = 1 := Units.ext ha
    exact normResidueSymbol_one_right (-1)
  have h1 : 1 - (a : K) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h2 : 1 - ((a⁻¹ : Kˣ) : K) ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Units.val_inv_eq_inv_val]
    exact inv_ne_one.2 ha
  set u₁ : Kˣ := Units.mk0 (1 - (a : K)) h1
  set u₂ : Kˣ := Units.mk0 (1 - ((a⁻¹ : Kˣ) : K)) h2
  have hdiv : -a = u₁ / u₂ := by
    apply Units.ext
    rw [Units.val_div_eq_div_val, Units.val_neg, Units.val_mk0, Units.val_mk0, eq_div_iff h2]
    simp only [mul_sub, mul_one, Units.val_inv_eq_inv_val, neg_mul, mul_inv_cancel₀ a.ne_zero]
    ring
  have hinv : normResidueSymbol K n u₂ a = 1 := by
    rw [← inv_inv a, normResidueSymbol_inv_right u₂ a⁻¹,
      normResidueSymbol_unitsMk0_one_sub_left h2, inv_one]
  rw [hdiv, normResidueSymbol_div_left, normResidueSymbol_unitsMk0_one_sub_left h1, hinv, div_self']

/-- **Skew symmetry of the norm-residue symbol, product form.** For all `a, b ∈ Kˣ`,
`(a, b) * (b, a) = 1`. -/
theorem normResidueSymbol_mul_symm (a b : Kˣ) :
    normResidueSymbol K n a b * normResidueSymbol K n b a = 1 := by
  have hneg (x : Kˣ) : normResidueSymbol K n (-1) x * normResidueSymbol K n x x = 1 := by
    rw [← normResidueSymbol_mul_left, neg_one_mul, normResidueSymbol_neg_self_left]
  have hab := hneg (a * b)
  rw [normResidueSymbol_mul_right, normResidueSymbol_mul_left, normResidueSymbol_mul_right,
    normResidueSymbol_mul_right] at hab
  calc
    normResidueSymbol K n a b * normResidueSymbol K n b a =
        (normResidueSymbol K n (-1) a * normResidueSymbol K n a a) *
          (normResidueSymbol K n (-1) b * normResidueSymbol K n b b) *
          (normResidueSymbol K n a b * normResidueSymbol K n b a) := by
      rw [hneg a, hneg b, one_mul, one_mul]
    _ = (normResidueSymbol K n (-1) a * normResidueSymbol K n (-1) b) *
          (normResidueSymbol K n a a * normResidueSymbol K n a b *
            (normResidueSymbol K n b a * normResidueSymbol K n b b)) := by
      ac_rfl
    _ = 1 := hab

/-- **Skew symmetry of the norm-residue symbol.** Swapping the two arguments inverts the symbol:
`(b, a) = (a, b)⁻¹`. -/
theorem normResidueSymbol_symm (a b : Kˣ) :
    normResidueSymbol K n b a = (normResidueSymbol K n a b)⁻¹ :=
  mul_eq_one_iff_eq_inv'.1 (normResidueSymbol_mul_symm a b)

/-- Triviality of the norm-residue symbol is symmetric in the two arguments. -/
theorem normResidueSymbol_eq_one_comm (a b : Kˣ) :
    normResidueSymbol K n a b = 1 ↔ normResidueSymbol K n b a = 1 := by
  rw [normResidueSymbol_symm, inv_eq_one]

/-- **Radical difference relation in the radical argument.** For `x ∈ K` and `a, u ∈ Kˣ` with
`u = xⁿ - a`, the norm-residue symbol `(a, u)` is `1`. -/
theorem normResidueSymbol_pow_sub_right {x : K} {a u : Kˣ} (hu : (u : K) = x ^ n - a) :
    normResidueSymbol K n a u = 1 :=
  (normResidueSymbol_eq_one_comm u a).1 (normResidueSymbol_pow_sub_left hu)

/-- For `a ∈ Kˣ` with `1 - (a : K) ≠ 0`, the unit `1 - a` pairs trivially on the right with `a`. -/
theorem normResidueSymbol_unitsMk0_one_sub_right {a : Kˣ} (ha : 1 - (a : K) ≠ 0) :
    normResidueSymbol K n a (Units.mk0 (1 - (a : K)) ha) = 1 :=
  (normResidueSymbol_eq_one_comm _ a).1 (normResidueSymbol_unitsMk0_one_sub_left ha)

/-- **Triviality on `(a, -a)`.** For every `a ∈ Kˣ`, `(a, -a) = 1`. -/
@[simp]
theorem normResidueSymbol_neg_self_right (a : Kˣ) :
    normResidueSymbol K n a (-a) = 1 :=
  (normResidueSymbol_eq_one_comm (-a) a).1 (normResidueSymbol_neg_self_left a)

/-- **Diagonal value of the norm-residue symbol, left form.** For every `a ∈ Kˣ`,
`(a, a) = (-1, a)`. -/
theorem normResidueSymbol_self_eq_neg_one_left (a : Kˣ) :
    normResidueSymbol K n a a = normResidueSymbol K n (-1) a := by
  have h1 : normResidueSymbol K n (-1) a * normResidueSymbol K n a a = 1 := by
    rw [← normResidueSymbol_mul_left, neg_one_mul, normResidueSymbol_neg_self_left]
  have hinv : (normResidueSymbol K n (-1) a)⁻¹ = normResidueSymbol K n (-1) a := by
    rw [← normResidueSymbol_inv_left, inv_neg, inv_one]
  rw [mul_eq_one_iff_eq_inv'.1 h1, hinv]

/-- **Diagonal value of the norm-residue symbol, right form.** For every `a ∈ Kˣ`,
`(a, a) = (a, -1)`. -/
theorem normResidueSymbol_self_eq_neg_one_right (a : Kˣ) :
    normResidueSymbol K n a a = normResidueSymbol K n a (-1) := by
  rw [normResidueSymbol_symm (-1) a, ← normResidueSymbol_inv_left, inv_neg, inv_one,
    normResidueSymbol_self_eq_neg_one_left]

/-- Every diagonal value `(a, a)` of the norm-residue symbol has square `1`. -/
@[simp]
theorem normResidueSymbol_self_sq (a : Kˣ) :
    normResidueSymbol K n a a ^ 2 = 1 := by
  rw [sq, ← normResidueSymbol_mul_symm a a]

/-- When `n` is odd, the norm-residue symbol is alternating: `(a, a) = 1` for every `a ∈ Kˣ`. -/
theorem normResidueSymbol_self_of_odd (hn : Odd n) (a : Kˣ) :
    normResidueSymbol K n a a = 1 := by
  obtain ⟨k, hk⟩ := hn
  apply Subtype.ext
  have hpow : (normResidueSymbol K n a a : Kˣ) ^ n = 1 := (normResidueSymbol K n a a).property
  have hsq : (normResidueSymbol K n a a : Kˣ) ^ 2 = 1 := by
    exact_mod_cast normResidueSymbol_self_sq (n := n) a
  generalize (normResidueSymbol K n a a : Kˣ) = u at hpow hsq ⊢
  rw [hk, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one] at hpow
  exact hpow

/-! ### Skew symmetry on power classes -/

/-- Skew symmetry of `normResidueSymbolPairing` on `Kˣ ⧸ (Kˣ)ⁿ`, in product form. -/
theorem normResidueSymbolPairing_mul_symm (x y : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing x y * normResidueSymbolPairing y x = 1 := by
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  obtain ⟨b, rfl⟩ := powerClassHom_surjective Kˣ n y
  simpa only [powerClassHom_apply, normResidueSymbolPairing_mk] using
    normResidueSymbol_mul_symm (n := n) a b

/-- Skew symmetry of `normResidueSymbolPairing` on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_symm (x y : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing y x = (normResidueSymbolPairing x y)⁻¹ :=
  mul_eq_one_iff_eq_inv'.1 (normResidueSymbolPairing_mul_symm x y)

/-- Every diagonal value of `normResidueSymbolPairing` has square `1`. -/
@[simp]
theorem normResidueSymbolPairing_self_sq (x : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing x x ^ 2 = 1 := by
  rw [sq, ← normResidueSymbolPairing_mul_symm x x]

/-- When `n` is odd, `normResidueSymbolPairing` is alternating on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_self_of_odd (hn : Odd n) (x : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing x x = 1 := by
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  simpa only [powerClassHom_apply, normResidueSymbolPairing_mk] using
    normResidueSymbol_self_of_odd hn a

end TauCeti
