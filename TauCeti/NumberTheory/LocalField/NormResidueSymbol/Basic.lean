/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.Algebra.Group.PowerClassGroup.Basic
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

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

The construction uses the absolute local Artin map of `TauCeti.ClassFieldTheory` and the Kummer
ratio identities in `TauCeti.FieldTheory.Kummer.Degree`. It does not identify this symbol with a
cohomological cup product or assert a tame formula.

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

/-- The roots of unity in the algebraic closure descend to the base field. -/
private def symbolRootsEquiv : rootsOfUnity n K ≃* rootsOfUnity n (AlgebraicClosure K) :=
  rootsOfUnityEquivOfPrimitiveRoots (algebraMap K (AlgebraicClosure K)).injective (by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
    exact ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).2 hζ⟩)

/-- An auxiliary radical used only to construct the symbol. -/
private def symbolRoot (b : Kˣ) : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (b : K))
    (NeZero.pos n)).choose

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [HasEnoughRootsOfUnity K n] in
private theorem symbolRoot_pow (b : Kˣ) :
    symbolRoot K n b ^ n = algebraMap K (AlgebraicClosure K) (b : K) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (b : K))
    (NeZero.pos n)).choose_spec

/-- The radical character, before descent through the topological abelianization. -/
private def symbolCharacter (b : Kˣ) :
    Gal(AlgebraicClosure K/K) →* rootsOfUnity n K :=
  (symbolRootsEquiv K n).symm.toMonoidHom.comp
    { toFun σ := rootsOfUnity.mkOfPowEq (σ (symbolRoot K n b) / symbolRoot K n b)
        (by
          rw [div_pow, ← map_pow, symbolRoot_pow, AlgEquiv.commutes, div_self (by simp)])
      map_one' := by
        ext
        simp [ne_zero_of_pow_eq_algebraMap (symbolRoot_pow K n b)]
      map_mul' σ τ := by
        ext
        simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
        exact σ.mul_apply_div_self_of_pow_eq τ (symbolRoot_pow K n b) }

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem algebraMap_symbolCharacter (b : Kˣ) (σ : Gal(AlgebraicClosure K/K)) :
    algebraMap K (AlgebraicClosure K) ((symbolCharacter K n b σ : Kˣ) : K) =
      σ (symbolRoot K n b) / symbolRoot K n b := by
  simp [symbolCharacter, symbolRootsEquiv, rootsOfUnityEquivOfPrimitiveRoots_symm_apply]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem symbolCharacter_eq_one_iff (b : Kˣ) (σ : Gal(AlgebraicClosure K/K)) :
    symbolCharacter K n b σ = 1 ↔ σ (symbolRoot K n b) = symbolRoot K n b := by
  rw [← Subtype.coe_inj, ← Units.val_inj,
    ← (algebraMap K (AlgebraicClosure K)).injective.eq_iff,
    algebraMap_symbolCharacter]
  simp only [Subgroup.coe_one, Units.val_one, map_one,
    div_eq_one_iff_eq (ne_zero_of_pow_eq_algebraMap (symbolRoot_pow K n b))]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The radical character has open kernel, the stabilizer of the radical. -/
private theorem continuous_symbolCharacter (b : Kˣ) : Continuous (symbolCharacter K n b) := by
  apply MonoidHom.continuous_of_isOpen_ker
  have hker : (symbolCharacter K n b).ker =
      MulAction.stabilizer Gal(AlgebraicClosure K/K) (symbolRoot K n b) := by
    ext σ
    exact symbolCharacter_eq_one_iff K n b σ
  rw [hker]
  exact stabilizer_isOpen_of_isIntegral (K := K) (symbolRoot K n b)

/-- The radical character descends to the topological abelianization. -/
private def symbolCharacterAb (b : Kˣ) :
    TopologicalAbelianization Gal(AlgebraicClosure K/K) →ₜ* rootsOfUnity n K :=
  TopologicalAbelianization.lift
    ⟨symbolCharacter K n b, continuous_symbolCharacter K n b⟩

/-- The **degree-`n` norm-residue symbol**, normalized by arithmetic Frobenius.
The first argument enters the absolute local Artin map, and the second supplies an `n`-th root.
No primitive root of unity is chosen as a coordinate. -/
def normResidueSymbol (a b : Kˣ) : rootsOfUnity n K :=
  symbolCharacterAb K n b (artinMap K a)

variable {K n}

/-- The norm-residue symbol, read in the algebraic closure, is `σ β / β` for every
representative `σ` of the Artin symbol of `a` and every `n`-th root `β` of `b`. -/
theorem algebraMap_normResidueSymbol (a b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) = artinMap K a)
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    algebraMap K (AlgebraicClosure K) ((normResidueSymbol K n a b : Kˣ) : K) =
      σ β / β := by
  rw [normResidueSymbol, ← hσ, symbolCharacterAb, TopologicalAbelianization.lift_mk,
    ContinuousMonoidHom.coe_mk, algebraMap_symbolCharacter]
  exact σ.apply_div_self_eq_of_pow_eq ((symbolRoot_pow K n b).trans hβ.symm)

/-- **The Artin characterization of the norm-residue symbol.** Every representative of
`Art_K(a)` moves every `n`-th root of `b` by the root of unity `(a,b)`. -/
theorem normResidueSymbol_spec (a b : Kˣ) (σ : Gal(AlgebraicClosure K/K))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure K/K)) = artinMap K a)
    {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) (b : K)) :
    σ β =
      algebraMap K (AlgebraicClosure K) ((normResidueSymbol K n a b : Kˣ) : K) * β := by
  rw [algebraMap_normResidueSymbol a b σ hσ hβ,
    div_mul_cancel₀ _ (ne_zero_of_pow_eq_algebraMap hβ)]

/-- The norm-residue symbol is multiplicative in the Artin argument. -/
theorem normResidueSymbol_mul_left (a a' b : Kˣ) :
    normResidueSymbol K n (a * a') b =
      normResidueSymbol K n a b * normResidueSymbol K n a' b := by
  rw [normResidueSymbol, map_mul]
  exact map_mul (symbolCharacterAb K n b) _ _

/-- The norm-residue symbol is multiplicative in the radical argument. -/
theorem normResidueSymbol_mul_right (a b b' : Kˣ) :
    normResidueSymbol K n a (b * b') =
      normResidueSymbol K n a b * normResidueSymbol K n a b' := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) (artinMap K a)
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  rw [algebraMap_normResidueSymbol a (b * b') σ hσ
    (β := symbolRoot K n b * symbolRoot K n b') (by
      rw [mul_pow, symbolRoot_pow, symbolRoot_pow, Units.val_mul, map_mul]),
    algebraMap_normResidueSymbol a b σ hσ (symbolRoot_pow K n b),
    algebraMap_normResidueSymbol a b' σ hσ (symbolRoot_pow K n b'),
    map_mul, mul_div_mul_comm]

/-- The symbol is trivial when the Artin argument is one. -/
@[simp]
theorem normResidueSymbol_one_left (b : Kˣ) : normResidueSymbol K n 1 b = 1 := by
  rw [normResidueSymbol, map_one]
  exact map_one (symbolCharacterAb K n b)

/-- The symbol is trivial when the radical argument is one. -/
@[simp]
theorem normResidueSymbol_one_right (a : Kˣ) : normResidueSymbol K n a 1 = 1 := by
  have h := normResidueSymbol_mul_right (n := n) a 1 1
  apply mul_left_cancel (a := normResidueSymbol K n a 1)
  simpa only [mul_one, one_mul] using h.symm

/-- Powers in the Artin argument become powers of the symbol. -/
theorem normResidueSymbol_pow_left (a b : Kˣ) (k : ℕ) :
    normResidueSymbol K n (a ^ k) b = normResidueSymbol K n a b ^ k := by
  rw [normResidueSymbol, map_pow]
  exact map_pow (symbolCharacterAb K n b) _ _

/-- Powers in the radical argument become powers of the symbol. -/
theorem normResidueSymbol_pow_right (a b : Kˣ) (k : ℕ) :
    normResidueSymbol K n a (b ^ k) = normResidueSymbol K n a b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, normResidueSymbol_mul_right, ih, pow_succ]

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
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := (mem_powerSubgroup_iff n).1 ha
      exact MonoidHom.ext (normResidueSymbol_pow_left_eq_one c))

/-- The **norm-residue pairing on power classes**. Its two arguments are classes in
`Kˣ ⧸ (Kˣ)ⁿ`, and it is multiplicative in both arguments. No nondegeneracy assertion is
needed to construct this pairing. -/
def normResidueSymbolPairing :
    powerClassQuotient Kˣ n →* (powerClassQuotient Kˣ n →* rootsOfUnity n K) :=
  (QuotientGroup.lift (powerSubgroup Kˣ n) (symbolLeftQuotient (K := K) (n := n)).flip (by
    intro b hb
    obtain ⟨c, rfl⟩ := (mem_powerSubgroup_iff n).1 hb
    apply MonoidHom.ext
    intro q
    obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n q
    simpa only [MonoidHom.flip_apply, powerClassHom_apply, symbolLeftQuotient,
      QuotientGroup.lift_mk, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply] using
      normResidueSymbol_pow_right_eq_one (n := n) a c)).flip

/-- On classes of units the descended pairing is the norm-residue symbol. -/
@[simp]
theorem normResidueSymbolPairing_mk (a b : Kˣ) :
    normResidueSymbolPairing (K := K) (n := n) (QuotientGroup.mk a) (QuotientGroup.mk b) =
      normResidueSymbol K n a b := by
  simp only [normResidueSymbolPairing, MonoidHom.flip_apply, QuotientGroup.lift_mk,
    symbolLeftQuotient, MonoidHom.coe_mk, OneHom.coe_mk]

end TauCeti
