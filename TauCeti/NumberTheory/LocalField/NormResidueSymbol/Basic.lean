/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.Algebra.Group.PowerClassGroup.Basic
import TauCeti.FieldTheory.Kummer.AbsoluteGalois

/-!
# The Artin-defined norm-residue symbol

For a nonarchimedean local field `K` containing the `n`-th roots of unity, the symbol
`normResidueSymbol K n a b` is the root of unity by which the arithmetic Artin symbol of `a`
moves an `n`-th root of `b`. Its value lies in `rootsOfUnity n K`, without choosing a primitive
root as a coordinate. The first argument enters the Artin map; the second supplies the radical.

The characterization `normResidueSymbol_spec` works with every radical and every representative
of the absolute Artin symbol in the absolute Galois group. The symbol is bimultiplicative and
is trivial on `n`-th powers in either argument. `normResidueSymbolPairing` is the resulting
bimultiplicative pairing on the existing power-class quotient `Kˣ ⧸ (Kˣ)ⁿ`.

The construction uses the absolute local Artin map of `TauCeti.ClassFieldTheory` and
`TauCeti.abelianizedKummerPairing`. It does not identify this symbol with a cohomological cup
product or assert a tame formula.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, Chapter IV, §5,
  (5.1), p. 143, for this Artin orientation and independence of the radical.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

/-- The **degree-`n` norm-residue symbol**, normalized by arithmetic Frobenius.
The first argument enters the absolute local Artin map, and the second supplies an `n`-th root.
No primitive root of unity is chosen as a coordinate. -/
def normResidueSymbol (a b : Kˣ) : rootsOfUnity n K :=
  abelianizedKummerPairing K n b (artinMap K a)

variable {K n}

/-- The norm-residue symbol, read in the algebraic closure, is `σ β / β` for every
representative `σ` of the Artin symbol of `a` and every `n`-th root `β` of `b`. -/
theorem algebraMap_normResidueSymbol (a b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) = artinMap K a)
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    algebraMap K (AlgebraicClosure K) ((normResidueSymbol K n a b : Kˣ) : K) =
      σ β / β := by
  rw [normResidueSymbol, ← hσ]
  exact algebraMap_abelianizedKummerPairing b σ hβ

/-- **The Artin characterization of the norm-residue symbol.** Every representative of
`Art_K(a)` moves every `n`-th root of `b` by the root of unity `(a,b)`. -/
theorem normResidueSymbol_spec (a b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) = artinMap K a)
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    σ β =
      algebraMap K (AlgebraicClosure K) ((normResidueSymbol K n a b : Kˣ) : K) * β := by
  rw [normResidueSymbol, ← hσ]
  exact abelianizedKummerPairing_spec b σ hβ

/-- **The Artin characterization of the norm-residue symbol in a normal extension.** Every
representative of `Art_K(a)` restricts along any `K`-embedding `ι : L →ₐ[K] SeparableClosure K` of
a normal extension `L/K` to move every `n`-th root `y ∈ L` of `b` by `(a, b)`. -/
theorem _root_.AlgHom.restrictNormalHom_apply_eq_algebraMap_normResidueSymbol_mul_of_pow_eq
    {L : Type*} [Field L] [Algebra K L] [Normal K L] (ι : L →ₐ[K] SeparableClosure K) (a b : Kˣ)
    (σ : Gal(AlgebraicClosure K/K))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) = artinMap K a) {y : L}
    (hy : y ^ n = algebraMap K L b) :
    ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) y =
      algebraMap K L ((normResidueSymbol K n a b : Kˣ) : K) * y := by
  let j : L →ₐ[K] AlgebraicClosure K := (separableClosure K (AlgebraicClosure K)).val.comp ι
  have hj : Function.Injective j := j.toRingHom.injective
  apply hj
  have hjy : j y ^ n = algebraMap K (AlgebraicClosure K) b := by
    rw [← map_pow, hy, AlgHom.commutes]
  have hcomm : j (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) y) = σ (j y) := by
    simp only [j, AlgHom.comp_apply, IntermediateField.coe_val, ι.restrictNormalHom_commutes,
      coe_absoluteGaloisGroupRestrictEquiv_apply]
  rw [hcomm, normResidueSymbol_spec a b σ hσ hjy, map_mul, AlgHom.commutes]

/-- **The Artin characterization of the norm-residue symbol in the separable closure.** Every
representative `σ` of `Art_K(a)` acts on any `n`-th root `β ∈ SeparableClosure K` of `b` by
multiplication by `(a, b)_{K, n}`. -/
theorem normResidueSymbol_spec_separableClosure (a b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) = artinMap K a)
    {β : SeparableClosure K} (hβ : β ^ n = algebraMap K (SeparableClosure K) (b : K)) :
    absoluteGaloisGroupRestrictEquiv K σ β =
      algebraMap K (SeparableClosure K) ((normResidueSymbol K n a b : Kˣ) : K) * β := by
  apply Subtype.ext
  rw [coe_absoluteGaloisGroupRestrictEquiv_apply K σ β,
    normResidueSymbol_spec a b σ hσ (by
      rw [← IntermediateField.algebraMap_apply, ← map_pow, hβ,
        ← IsScalarTower.algebraMap_apply]),
    IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply]

/-- The norm-residue symbol is multiplicative in the Artin argument. -/
theorem normResidueSymbol_mul_left (a a' b : Kˣ) :
    normResidueSymbol K n (a * a') b =
      normResidueSymbol K n a b * normResidueSymbol K n a' b :=
  map_mul ((abelianizedKummerPairing K n b).comp (artinMap K)) a a'

/-- The norm-residue symbol is multiplicative in the radical argument. -/
theorem normResidueSymbol_mul_right (a b b' : Kˣ) :
    normResidueSymbol K n a (b * b') =
      normResidueSymbol K n a b * normResidueSymbol K n a b' :=
  map_mul ((abelianizedKummerPairing K n).flip (artinMap K a)) b b'

/-- The symbol is trivial when the Artin argument is one. -/
@[simp]
theorem normResidueSymbol_one_left (b : Kˣ) : normResidueSymbol K n 1 b = 1 :=
  map_one ((abelianizedKummerPairing K n b).comp (artinMap K))

/-- The symbol is trivial when the radical argument is one. -/
@[simp]
theorem normResidueSymbol_one_right (a : Kˣ) : normResidueSymbol K n a 1 = 1 :=
  map_one ((abelianizedKummerPairing K n).flip (artinMap K a))

/-- Powers in the Artin argument become powers of the symbol. -/
theorem normResidueSymbol_pow_left (a b : Kˣ) (k : ℕ) :
    normResidueSymbol K n (a ^ k) b = normResidueSymbol K n a b ^ k :=
  map_pow ((abelianizedKummerPairing K n b).comp (artinMap K)) a k

/-- Powers in the radical argument become powers of the symbol. -/
theorem normResidueSymbol_pow_right (a b : Kˣ) (k : ℕ) :
    normResidueSymbol K n a (b ^ k) = normResidueSymbol K n a b ^ k :=
  map_pow ((abelianizedKummerPairing K n).flip (artinMap K a)) b k

/-- An `n`-th power in the Artin argument pairs trivially with every radical. -/
@[simp]
theorem normResidueSymbol_pow_left_eq_one (a b : Kˣ) :
    normResidueSymbol K n (a ^ n) b = 1 := by
  rw [normResidueSymbol_pow_left]
  exact Subtype.ext (normResidueSymbol K n a b).property

/-- An `n`-th power in the radical argument pairs trivially with every Artin argument. -/
@[simp]
theorem normResidueSymbol_pow_right_eq_one (a b : Kˣ) :
    normResidueSymbol K n a (b ^ n) = 1 := by
  rw [normResidueSymbol_pow_right]
  exact Subtype.ext (normResidueSymbol K n a b).property

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

/-- In degree one the norm-residue symbol is trivial. -/
@[simp]
theorem normResidueSymbol_degree_one (a b : Kˣ) : normResidueSymbol K 1 a b = 1 := by
  have h := (normResidueSymbol K 1 a b).property
  simpa using h

/-- Descent in the Artin argument, with the radical argument still a unit. -/
private def symbolLeftQuotient :
    powerClassQuotient Kˣ n →* (Kˣ →* rootsOfUnity n K) :=
  QuotientGroup.lift (powerSubgroup Kˣ n)
    { toFun a :=
        { toFun b := normResidueSymbol K n a b
          map_one' := normResidueSymbol_one_right a
          map_mul' := normResidueSymbol_mul_right a }
      map_one' := MonoidHom.ext (normResidueSymbol_one_left (K := K) (n := n))
      map_mul' a a' := MonoidHom.ext (normResidueSymbol_mul_left a a') }
    (fun _ ha ↦ MonoidHom.mem_ker.2 <|
      MonoidHom.ext (normResidueSymbol_eq_one_of_mem_powerSubgroup_left ha))

private theorem symbolLeftQuotient_mk (a b : Kˣ) :
    symbolLeftQuotient (K := K) (n := n) (QuotientGroup.mk a) b = normResidueSymbol K n a b := by
  simp only [symbolLeftQuotient, QuotientGroup.lift_mk', MonoidHom.coe_mk, OneHom.coe_mk]

/-- The **norm-residue pairing on power classes**. Its two arguments are classes in
`Kˣ ⧸ (Kˣ)ⁿ`, and it is multiplicative in both arguments. No nondegeneracy assertion is
needed to construct this pairing. -/
def normResidueSymbolPairing :
    powerClassQuotient Kˣ n →* (powerClassQuotient Kˣ n →* rootsOfUnity n K) :=
  (QuotientGroup.lift (powerSubgroup Kˣ n) (symbolLeftQuotient (K := K) (n := n)).flip
    (fun b hb ↦ MonoidHom.mem_ker.2 <| MonoidHom.ext fun q ↦ by
      obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n q
      rw [MonoidHom.flip_apply, powerClassHom_apply, symbolLeftQuotient_mk, MonoidHom.one_apply]
      exact normResidueSymbol_eq_one_of_mem_powerSubgroup_right a hb)).flip

/-- On classes of units the descended pairing is the norm-residue symbol. -/
@[simp]
theorem normResidueSymbolPairing_mk (a b : Kˣ) :
    normResidueSymbolPairing (K := K) (n := n) (QuotientGroup.mk a) (QuotientGroup.mk b) =
      normResidueSymbol K n a b := by
  rw [normResidueSymbolPairing, MonoidHom.flip_apply, QuotientGroup.lift_mk',
    MonoidHom.flip_apply, symbolLeftQuotient_mk]

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

end TauCeti
