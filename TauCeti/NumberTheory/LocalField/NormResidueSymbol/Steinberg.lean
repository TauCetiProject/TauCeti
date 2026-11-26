/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.FieldTheory.Kummer.Steinberg

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
`xⁿ - b ∈ Kˣ`. Specializing to `x = 1` and `x = 0` yields the **Steinberg relation** `(a, b) = 1`
for `a + b = 1` (`normResidueSymbol_eq_one_of_add_eq_one`) and `(-a, a) = 1`
(`normResidueSymbol_neg_self_left`), hence `(a, a) = (-1, a)` of order dividing `2`. Expanding
`(-(a * b), a * b) = 1` then yields **skew symmetry** `(b, a) = (a, b)⁻¹`
(`normResidueSymbol_swap`), which transposes the norm criterion to the radical argument
(`normResidueSymbol_eq_one_iff_mem_normGroup_of_pow_eq_left`).

## Main results

* `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup`,
  `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_of_pow_eq_left`: the norm criterion in both
  arguments, `(a, b) = 1 ↔ a ∈ normGroup K K(ⁿ√b)` and `(a, b) = 1 ↔ b ∈ normGroup K K(ⁿ√a)`.
* `TauCeti.normResidueSymbol_eq_one_of_eq_pow_sub_left`,
  `TauCeti.normResidueSymbol_eq_one_of_eq_pow_sub_right`, and
  `TauCeti.normResidueSymbol_eq_one_of_add_eq_one`: `(xⁿ - b, b) = 1`, `(a, xⁿ - a) = 1`, and the
  Steinberg relation `(a, b) = 1` for `(a : K) + b = 1`.
* `TauCeti.normResidueSymbol_neg_self_left`, `TauCeti.normResidueSymbol_neg_self_right`:
  `(-a, a) = 1` and `(a, -a) = 1`.
* `TauCeti.normResidueSymbol_mul_swap`, `TauCeti.normResidueSymbol_swap`,
  `TauCeti.normResidueSymbolPairing_mul_swap`, `TauCeti.normResidueSymbolPairing_swap`: skew
  symmetry `(a, b) * (b, a) = 1` and `(b, a) = (a, b)⁻¹` on units and on power classes.
* `TauCeti.normResidueSymbol_self_eq_normResidueSymbol_neg_one_left`,
  `TauCeti.normResidueSymbol_self_eq_normResidueSymbol_neg_one_right`,
  `TauCeti.normResidueSymbol_self_sq`, `TauCeti.normResidueSymbol_self_of_odd`:
  `(a, a) = (-1, a) = (a, -1)`, `(a, a)² = 1`, and `(a, a) = 1` for odd `n`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., AMS Translations
  of Mathematical Monographs 121 (2002), Chapter IV, §5, (5.1) Proposition (1)–(5), pp. 143–144.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter III, §4, Theorem 4.4.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory _root_.IntermediateField

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-! ### The norm criterion in the Artin argument -/

/-- **The norm criterion in the Artin argument.** Let `L = K(s)` be a finite radical extension
generated over `K` by an element `s ∈ L` with `sⁿ = b`. Then `(a, b) = 1` if and only if `a` lies
in the norm subgroup `N_{L/K}(Lˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] (a b : Kˣ) {s : L} (hs : s ^ n = algebraMap K L b)
    (hgen : K⟮s⟯ = ⊤) :
    normResidueSymbol K n a b = 1 ↔ a ∈ normGroup K L := by
  -- A representative of `Art_K(a)` fixes `s` precisely when its restriction to the cyclic
  -- extension `L/K` is `1`, which by local reciprocity is equivalent to `a ∈ N_{L/K}(Lˣ)`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ hs hgen
  have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ hs hgen
  let _ : CommGroup Gal(L/K) := IsCyclic.commGroup
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) (artinMap K a)
  rw [mem_normGroup_iff_restrictNormalHom_eq_one_of_mk_eq_artinMap K L ι σ hσ]
  have hact := ι.restrictNormalHom_apply_eq_algebraMap_normResidueSymbol_mul_of_pow_eq a b σ hσ hs
  have hs0 : s ≠ 0 := ne_zero_of_pow_eq_algebraMap hs
  refine ⟨fun h ↦ TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top hgen ?_, fun h ↦ ?_⟩
  · rintro _ rfl
    simp [hact, h]
  · simpa [h, hs0] using hact.symm

/-- In any field extension `E/K` containing an `n`-th root `β` of `b`, `(a, b) = 1` holds if and
only if `a` is a unit norm from `K⟮β⟯`. -/
theorem normResidueSymbol_eq_one_iff_mem_range_normUnits_adjoin {E : Type*} [Field E]
    [Algebra K E] (a b : Kˣ) {β : E} (hβ : β ^ n = algebraMap K E b) :
    normResidueSymbol K n a b = 1 ↔ a ∈ (Algebra.normUnits K : K⟮β⟯ˣ →* Kˣ).range := by
  have : FiniteDimensional K K⟮β⟯ :=
    adjoin.finiteDimensional (.of_pow (NeZero.pos n) (hβ ▸ isIntegral_algebraMap))
  have ht : AdjoinSimple.gen K β ^ n = algebraMap K K⟮β⟯ b := Subtype.ext (by simpa using hβ)
  exact (normResidueSymbol_eq_one_iff_mem_normGroup a b ht (adjoin_adjoinSimple_gen_eq_top β)).trans
    (mem_normGroup_iff_exists_normUnits.trans MonoidHom.mem_range.symm)

/-! ### The Steinberg relation and skew symmetry -/

/-- **Radical difference relation in the Artin argument.** For `x ∈ K` and `u, b ∈ Kˣ` with
`u = xⁿ - b`, the norm-residue symbol `(u, b)` is `1`. -/
theorem normResidueSymbol_eq_one_of_eq_pow_sub_left {x : K} {u b : Kˣ} (hu : (u : K) = x ^ n - b) :
    normResidueSymbol K n u b = 1 := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) b)
    (NeZero.pos n)
  have : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have ht : AdjoinSimple.gen K β ^ n = algebraMap K K⟮β⟯ b := Subtype.ext (by simpa using hβ)
  have hgen := adjoin_adjoinSimple_gen_eq_top (F := K) β
  exact (normResidueSymbol_eq_one_iff_mem_normGroup u b ht hgen).2
    (mem_normGroup_of_eq_pow_sub_of_pow_eq hu ht hgen)

/-- **The Steinberg relation for the norm-residue symbol.** If `a, b ∈ Kˣ` satisfy `a + b = 1` in
`K`, then `(a, b) = 1`. -/
theorem normResidueSymbol_eq_one_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    normResidueSymbol K n a b = 1 :=
  normResidueSymbol_eq_one_of_eq_pow_sub_left (x := 1) (by rw [one_pow]; linear_combination hab)

/-- For `a ∈ Kˣ` with `1 - (a : K) ≠ 0`, the unit `1 - a` pairs trivially on the left with `a`. -/
@[simp]
theorem normResidueSymbol_unitsMk0_one_sub_left {a : Kˣ} (ha : 1 - (a : K) ≠ 0) :
    normResidueSymbol K n (Units.mk0 (1 - (a : K)) ha) a = 1 :=
  normResidueSymbol_eq_one_of_add_eq_one (by simp)

/-- **Triviality on `(-a, a)`.** For every `a ∈ Kˣ`, `(-a, a) = 1`. -/
@[simp]
theorem normResidueSymbol_neg_self_left (a : Kˣ) :
    normResidueSymbol K n (-a) a = 1 :=
  normResidueSymbol_eq_one_of_eq_pow_sub_left (x := 0) (by simp [zero_pow (NeZero.ne n)])

/-- **Skew symmetry of the norm-residue symbol, product form.** For all `a, b ∈ Kˣ`,
`(a, b) * (b, a) = 1`. -/
@[simp]
theorem normResidueSymbol_mul_swap (a b : Kˣ) :
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
theorem normResidueSymbol_swap (a b : Kˣ) :
    normResidueSymbol K n b a = (normResidueSymbol K n a b)⁻¹ :=
  mul_eq_one_iff_eq_inv'.1 (normResidueSymbol_mul_swap a b)

/-- Triviality of the norm-residue symbol is symmetric in the two arguments. -/
theorem normResidueSymbol_eq_one_comm (a b : Kˣ) :
    normResidueSymbol K n a b = 1 ↔ normResidueSymbol K n b a = 1 := by
  rw [normResidueSymbol_swap, inv_eq_one]

/-- **The norm criterion in the radical argument.** Let `L = K(s)` be a finite radical extension
generated over `K` by an element `s ∈ L` with `sⁿ = a`. Then `(a, b) = 1` if and only if
`b ∈ N_{L/K}(Lˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup_of_pow_eq_left {L : Type*} [Field L]
    [Algebra K L] [FiniteDimensional K L] (a b : Kˣ) {s : L} (hs : s ^ n = algebraMap K L a)
    (hgen : K⟮s⟯ = ⊤) :
    normResidueSymbol K n a b = 1 ↔ b ∈ normGroup K L :=
  (normResidueSymbol_eq_one_comm a b).trans (normResidueSymbol_eq_one_iff_mem_normGroup b a hs hgen)

/-- In any field extension `E/K` containing an `n`-th root `α` of `a`, `(a, b) = 1` holds if and
only if `b` is a unit norm from `K⟮α⟯`. -/
theorem normResidueSymbol_eq_one_iff_mem_range_normUnits_adjoin_of_pow_eq_left {E : Type*}
    [Field E] [Algebra K E] (a b : Kˣ) {α : E} (hα : α ^ n = algebraMap K E a) :
    normResidueSymbol K n a b = 1 ↔ b ∈ (Algebra.normUnits K : K⟮α⟯ˣ →* Kˣ).range :=
  (normResidueSymbol_eq_one_comm a b).trans
    (normResidueSymbol_eq_one_iff_mem_range_normUnits_adjoin b a hα)

/-- **Radical difference relation in the radical argument.** For `x ∈ K` and `a, u ∈ Kˣ` with
`u = xⁿ - a`, the norm-residue symbol `(a, u)` is `1`. -/
theorem normResidueSymbol_eq_one_of_eq_pow_sub_right {x : K} {a u : Kˣ} (hu : (u : K) = x ^ n - a) :
    normResidueSymbol K n a u = 1 :=
  (normResidueSymbol_eq_one_comm u a).1 (normResidueSymbol_eq_one_of_eq_pow_sub_left hu)

/-- For `a ∈ Kˣ` with `1 - (a : K) ≠ 0`, the unit `1 - a` pairs trivially on the right with `a`. -/
@[simp]
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
theorem normResidueSymbol_self_eq_normResidueSymbol_neg_one_left (a : Kˣ) :
    normResidueSymbol K n a a = normResidueSymbol K n (-1) a := by
  have h1 : normResidueSymbol K n (-1) a * normResidueSymbol K n a a = 1 := by
    rw [← normResidueSymbol_mul_left, neg_one_mul, normResidueSymbol_neg_self_left]
  have hinv : (normResidueSymbol K n (-1) a)⁻¹ = normResidueSymbol K n (-1) a := by
    rw [← normResidueSymbol_inv_left, inv_neg, inv_one]
  rw [mul_eq_one_iff_eq_inv'.1 h1, hinv]

/-- **Diagonal value of the norm-residue symbol, right form.** For every `a ∈ Kˣ`,
`(a, a) = (a, -1)`. -/
theorem normResidueSymbol_self_eq_normResidueSymbol_neg_one_right (a : Kˣ) :
    normResidueSymbol K n a a = normResidueSymbol K n a (-1) := by
  rw [normResidueSymbol_swap (-1) a, ← normResidueSymbol_inv_left, inv_neg, inv_one,
    normResidueSymbol_self_eq_normResidueSymbol_neg_one_left]

/-- Every diagonal value `(a, a)` of the norm-residue symbol has square `1`. -/
@[simp]
theorem normResidueSymbol_self_sq (a : Kˣ) :
    normResidueSymbol K n a a ^ 2 = 1 := by
  rw [sq, ← normResidueSymbol_mul_swap a a]

/-- When `n` is odd, the norm-residue symbol is alternating: `(a, a) = 1` for every `a ∈ Kˣ`. -/
theorem normResidueSymbol_self_of_odd (hn : Odd n) (a : Kˣ) :
    normResidueSymbol K n a a = 1 := by
  obtain ⟨k, hk⟩ := hn
  have hpow : normResidueSymbol K n a a ^ n = 1 := by
    rw [← normResidueSymbol_pow_left, normResidueSymbol_pow_left_eq_one]
  simpa [hk, pow_add, pow_mul, normResidueSymbol_self_sq] using hpow

/-! ### Skew symmetry on power classes -/

/-- Skew symmetry of `normResidueSymbolPairing` on `Kˣ ⧸ (Kˣ)ⁿ`, in product form. -/
@[simp]
theorem normResidueSymbolPairing_mul_swap (x y : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing x y * normResidueSymbolPairing y x = 1 := by
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  obtain ⟨b, rfl⟩ := powerClassHom_surjective Kˣ n y
  simpa only [powerClassHom_apply, normResidueSymbolPairing_mk] using
    normResidueSymbol_mul_swap (n := n) a b

/-- Skew symmetry of `normResidueSymbolPairing` on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_swap (x y : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing y x = (normResidueSymbolPairing x y)⁻¹ :=
  mul_eq_one_iff_eq_inv'.1 (normResidueSymbolPairing_mul_swap x y)

/-- Every diagonal value of `normResidueSymbolPairing` has square `1`. -/
@[simp]
theorem normResidueSymbolPairing_self_sq (x : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing x x ^ 2 = 1 := by
  rw [sq, ← normResidueSymbolPairing_mul_swap x x]

/-- When `n` is odd, `normResidueSymbolPairing` is alternating on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_self_of_odd (hn : Odd n) (x : powerClassQuotient Kˣ n) :
    normResidueSymbolPairing x x = 1 := by
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  simpa only [powerClassHom_apply, normResidueSymbolPairing_mk] using
    normResidueSymbol_self_of_odd hn a

end TauCeti
