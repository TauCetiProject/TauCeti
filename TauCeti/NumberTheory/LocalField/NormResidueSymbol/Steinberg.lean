/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Functoriality
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# The Steinberg relation and skew symmetry of the norm-residue symbol

For a nonarchimedean local field `K` containing the `n`-th roots of unity, this file proves the
fundamental algebraic identities of `normResidueSymbol K n` beyond bimultiplicativity:

* **The Steinberg relation** (`normResidueSymbol_eq_one_of_add_eq_one`,
  `normResidueSymbol_one_sub_left`, `normResidueSymbol_one_sub_right`): `(a, b)_{K, n} = 1`
  whenever `(a : K) + b = 1`; equivalently `(1 - a, a)_{K, n} = 1` and `(a, 1 - a)_{K, n} = 1`
  for `(a : K) ≠ 1`.
* **Additive-inverse cancellation** (`normResidueSymbol_neg_self_left`,
  `normResidueSymbol_neg_self_right`): `(-a, a)_{K, n} = 1` and `(a, -a)_{K, n} = 1`, whence
  `(a, a)_{K, n} = (a, -1)_{K, n} = (-1, a)_{K, n}` (`normResidueSymbol_self_eq_neg_one_right`,
  `normResidueSymbol_self_eq_neg_one_left`), which equals `1` when `n` is odd
  (`normResidueSymbol_self_of_odd`).
* **Skew symmetry** (`normResidueSymbol_mul_swap`, `normResidueSymbol_swap`,
  `normResidueSymbolPairing_swap`): `(a, b)_{K, n} * (b, a)_{K, n} = 1`, equivalently
  `(b, a)_{K, n} = (a, b)_{K, n}⁻¹`, both on `Kˣ` and on `Kˣ ⧸ (Kˣ)ⁿ`.
* **Norm functoriality in the radical argument**
  (`restrictRootsOfUnity_normResidueSymbol_normUnits_right`): for a separable extension `L / K` of
  nonarchimedean local fields with `a ∈ Kˣ` and `b ∈ Lˣ`, `(a, N_{L/K} b)_{K, n} = (a, b)_{L, n}`.

Together with bimultiplicativity and degree/field functoriality, these identities supply the full
algebraic calculus of the local norm-residue symbol used in nondegeneracy, the norm criterion, and
power reciprocity.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, Chapter IV, §5,
  (5.1) Proposition (2)–(4), pp. 143–144.
* J. S. Milne, *Class Field Theory*, Chapter III, §4, Theorem 4.4 (a)–(b), p. 113.
* A. R. Shastri, *Reciprocity Laws*, §6.2, Theorem 6.2.1 (iii)–(iv), pp. 214–215.
* J. Tate, *Relations between K₂ and Galois cohomology*, Invent. Math. 36 (1976), 257–274.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-- For a monic irreducible factor `f` of `X ^ n - b` with `(b : K) ≠ 1`, `f(1)` is a unit of `K`
pairing trivially with `b` in the Artin argument. -/
private theorem exists_eval_one_normResidueSymbol_eq_one {b : Kˣ} (hb : (b : K) ≠ 1) {f : K[X]}
    (hirr : Irreducible f) (hmonic : f.Monic) (hdvd : f ∣ X ^ n - C (b : K)) :
    ∃ c : Kˣ, (c : K) = f.eval 1 ∧ normResidueSymbol K n c b = 1 := by
  -- In `K[X]/(f)`, the root `θ` satisfies `θ ^ n = b` and `f(1) = N_{K[X]/(f)/K}(1 - θ)`.
  have := Fact.mk hirr
  have : FiniteDimensional K (AdjoinRoot f) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have := hζ.neZero'
  -- `f` divides the separable polynomial `X ^ n - b`, so `K[X]/(f) / K` is separable.
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero (SeparableClosure K) f
    (degree_pos_of_irreducible hirr).ne'
    ((separable_X_pow_sub_C (b : K) (NeZero.ne (n : K)) b.ne_zero).of_dvd hdvd)
  let ι : AdjoinRoot f →ₐ[K] SeparableClosure K := AdjoinRoot.liftAlgHom f (Algebra.ofId K _) x
    (by rw [Algebra.toRingHom_ofId, ← aeval_def]; exact hx)
  have : Algebra.IsSeparable K (AdjoinRoot f) :=
    Algebra.IsSeparable.of_algHom K (SeparableClosure K) ι
  let _ := algebraicExtensionValuativeRel K (AdjoinRoot f)
  let _ := algebraicExtensionNormedFieldTopology K (AdjoinRoot f)
  have := finiteExtension_isNonarchimedeanLocalField K (AdjoinRoot f)
  have := algebraicExtension_valuativeExtension K (AdjoinRoot f)
  have : HasEnoughRootsOfUnity (AdjoinRoot f) n :=
    .of_injective (algebraMap K (AdjoinRoot f)).injective
  have hθ : AdjoinRoot.root f ^ n = AdjoinRoot.of f (b : K) := by
    have h := AdjoinRoot.mk_eq_zero.2 hdvd
    rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, aeval_X, aeval_C] at h
    exact sub_eq_zero.1 h
  have hθ0 : AdjoinRoot.root f ≠ 0 := fun h ↦ by
    rw [h, zero_pow (NeZero.ne n), eq_comm, map_eq_zero_iff _ (AdjoinRoot.of f).injective] at hθ
    exact b.ne_zero hθ
  have hθ1 : (1 : AdjoinRoot f) - AdjoinRoot.root f ≠ 0 := fun h ↦ by
    rw [← sub_eq_zero.1 h, one_pow, eq_comm, map_eq_one_iff _ (AdjoinRoot.of f).injective] at hθ
    exact hb hθ
  refine ⟨Algebra.normUnits K (Units.mk0 (1 - AdjoinRoot.root f) hθ1), ?_, ?_⟩
  · rw [Algebra.coe_normUnits, Units.val_mk0, ← map_one (AdjoinRoot.of f),
      AdjoinRoot.norm_algebraMap_sub_root hmonic]
  · apply restrictRootsOfUnity_injective (algebraMap K (AdjoinRoot f)) n
      (algebraMap K (AdjoinRoot f)).injective
    rw [map_one, restrictRootsOfUnity_normResidueSymbol_normUnits_left]
    have hbL : Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom b =
        Units.mk0 (AdjoinRoot.root f) hθ0 ^ n :=
      Units.ext (by simpa [AdjoinRoot.algebraMap_eq] using hθ.symm)
    rw [hbL, normResidueSymbol_pow_right_eq_one]

/-- **The Steinberg relation for the norm-residue symbol.** If `a, b ∈ Kˣ` satisfy
`(a : K) + b = 1`, then `(a, b)_{K, n} = 1`. -/
theorem normResidueSymbol_eq_one_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    normResidueSymbol K n a b = 1 := by
  classical
  have hb : (b : K) ≠ 1 := fun hb1 ↦ a.ne_zero (by linear_combination hab - hb1)
  set p : K[X] := X ^ n - C (b : K) with hp
  have hpmonic : p.Monic := monic_X_pow_sub_C (b : K) (NeZero.ne n)
  -- `p(1) = 1 - b = a` is the product of `f(1)` over the monic irreducible factors `f` of `p`.
  obtain ⟨c, hc, hc1⟩ : ∃ c : Kˣ, (c : K) = p.eval 1 ∧ normResidueSymbol K n c b = 1 := by
    have hprod := leadingCoeff_mul_prod_normalizedFactors p
    rw [hpmonic.leadingCoeff, C_1, one_mul] at hprod
    rw [← hprod, eval_multiset_prod]
    refine Multiset.prod_induction
      (fun y ↦ ∃ c : Kˣ, (c : K) = y ∧ normResidueSymbol K n c b = 1) _ ?_
      ⟨1, Units.val_one, normResidueSymbol_one_left b⟩ ?_
    · rintro _ _ ⟨c₁, rfl, hc₁⟩ ⟨c₂, rfl, hc₂⟩
      refine ⟨c₁ * c₂, Units.val_mul c₁ c₂, ?_⟩
      rw [normResidueSymbol_mul_left, hc₁, hc₂, mul_one]
    · intro y hy
      obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨hirr, hmonic, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hpmonic.ne_zero).1 hf
      exact exists_eval_one_normResidueSymbol_eq_one hb hirr hmonic hdvd
  have hca : c = a := Units.ext (by
    rw [hc, hp, eval_sub, eval_pow, eval_X, eval_C, one_pow, ← hab, add_sub_cancel_right])
  exact hca ▸ hc1

/-- **The Steinberg relation in `(1 - a, a)` form.** For `a ∈ Kˣ` with `(a : K) ≠ 1`,
`(1 - a, a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_one_sub_left {a : Kˣ} (ha : (a : K) ≠ 1) :
    normResidueSymbol K n (Units.mk0 (1 - (a : K)) (sub_ne_zero.2 ha.symm)) a = 1 :=
  normResidueSymbol_eq_one_of_add_eq_one (sub_add_cancel 1 (a : K))

/-- **Additive-inverse cancellation in the Artin argument.** For every `a ∈ Kˣ`,
`(-a, a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_neg_self_left (a : Kˣ) : normResidueSymbol K n (-a) a = 1 := by
  by_cases ha1 : a = 1
  · subst ha1
    exact normResidueSymbol_one_right (-1)
  have ha : (a : K) ≠ 1 := fun h ↦ ha1 (Units.ext h)
  have hainv : ((a⁻¹ : Kˣ) : K) ≠ 1 := fun h ↦ ha1 (inv_eq_one.1 (Units.ext h))
  set u₁ : Kˣ := Units.mk0 (1 - (a : K)) (sub_ne_zero.2 ha.symm)
  set u₂ : Kˣ := Units.mk0 (1 - ((a⁻¹ : Kˣ) : K)) (sub_ne_zero.2 hainv.symm)
  -- In `Kˣ`, `(-a) * (1 - a⁻¹) = 1 - a`, and both `1 - a` and `1 - a⁻¹` pair trivially with `a`.
  have hmul : -a * u₂ = u₁ := Units.ext <| by
    simp only [u₁, u₂, Units.val_mul, Units.val_neg, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [mul_sub, mul_one, neg_mul, mul_inv_cancel₀ a.ne_zero]
    ring
  have hu₂ : normResidueSymbol K n u₂ a = 1 := by
    rw [← inv_inv a, normResidueSymbol_inv_right, normResidueSymbol_one_sub_left hainv, inv_one]
  have hprod : normResidueSymbol K n (-a) a * normResidueSymbol K n u₂ a =
      normResidueSymbol K n u₁ a := by
    rw [← normResidueSymbol_mul_left, hmul]
  rwa [hu₂, mul_one, normResidueSymbol_one_sub_left ha] at hprod

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

/-- **The Steinberg relation in `(a, 1 - a)` form.** For `a ∈ Kˣ` with `(a : K) ≠ 1`,
`(a, 1 - a)_{K, n} = 1`. -/
@[simp]
theorem normResidueSymbol_one_sub_right {a : Kˣ} (ha : (a : K) ≠ 1) :
    normResidueSymbol K n a (Units.mk0 (1 - (a : K)) (sub_ne_zero.2 ha.symm)) = 1 := by
  rw [normResidueSymbol_swap, normResidueSymbol_one_sub_left ha, inv_one]

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

/-- **Norm functoriality of the norm-residue symbol in the radical argument.** For a separable
extension `L / K` of nonarchimedean local fields with `a ∈ Kˣ` and `b ∈ Lˣ`, the symbol
`(a, N_{L/K} b)_{K, n}` mapped into `μ_n(L)` equals `(a, b)_{L, n}`. -/
theorem restrictRootsOfUnity_normResidueSymbol_normUnits_right {L : Type} [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [HasEnoughRootsOfUnity L n] (a : Kˣ) (b : Lˣ) :
    restrictRootsOfUnity (algebraMap K L) n (normResidueSymbol K n a (Algebra.normUnits K b)) =
      normResidueSymbol L n (Units.map (algebraMap K L).toMonoidHom a) b := by
  rw [normResidueSymbol_swap (n := n) (Algebra.normUnits K b) a, map_inv,
    restrictRootsOfUnity_normResidueSymbol_normUnits_left, ← normResidueSymbol_swap]

end TauCeti
