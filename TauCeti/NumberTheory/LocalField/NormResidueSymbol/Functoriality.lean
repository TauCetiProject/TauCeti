/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Steinberg
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Functoriality of the norm-residue symbol

This file establishes the compatibility of the Artin-defined norm-residue symbol of a
nonarchimedean local field with changes of the root-of-unity degree, with finite separable field
extensions, and with continuous or base-preserving field isomorphisms:

* **Degree transition** (`rootsOfUnityPowOfDvd_normResidueSymbol`,
  `coe_normResidueSymbol_mul_pow`): when `n ∣ m` and `K` contains the `m`-th roots of unity,
  raising the degree-`m` symbol to the `(m / n)`-th power gives the degree-`n` symbol; in
  particular `(a, b)_{K, n * m} ^ m = (a, b)_{K, n}`.
* **Norm functoriality** (`restrictRootsOfUnity_normResidueSymbol_normUnits_left`,
  `restrictRootsOfUnity_normResidueSymbol_normUnits_right`,
  `normResidueSymbol_unitsMap_algebraMap`): for a separable extension `L / K` of nonarchimedean
  local fields, `(N_{L/K} a, b)_{K, n} = (a, b)_{L, n}` for `a ∈ Lˣ, b ∈ Kˣ`,
  `(a, N_{L/K} b)_{K, n} = (a, b)_{L, n}` for `a ∈ Kˣ, b ∈ Lˣ`, and on base units
  `(a, b)_{L, n} = (a, b)_{K, n} ^ [L : K]`.
* **Transport under isomorphisms** (`restrictRootsOfUnity_normResidueSymbol_of_vle_iff`,
  `restrictRootsOfUnity_normResidueSymbol_of_continuous`,
  `restrictRootsOfUnity_normResidueSymbol_algEquiv`, `algHom_coe_normResidueSymbol`): a
  valuation-preserving or continuous ring isomorphism `e : K ≃+* K'` satisfies
  `e ((a, b)_{K, n}) = (e a, e b)_{K', n}`, and an `F`-algebra equivalence `L ≃ₐ[F] L'` (or an
  `F`-algebra homomorphism `f : E →ₐ[F] E'` restricting to `L ≃ₐ[F] f(L)`, including Galois
  transport `L ≃ₐ[F] σ(L)`, without assuming `μ_n ⊆ F`) transports the symbol without an explicit
  continuity hypothesis.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, Chapter IV, §5,
  (5.1) Proposition (7)–(9), pp. 143–145.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory

section DegreeAndNorm

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Degree functoriality of the norm-residue symbol.** When `n ∣ m` and `K` contains the `m`-th
roots of unity, the power transition `rootsOfUnityPowOfDvd h : μ_m(K) →* μ_n(K)` sends the
degree-`m` symbol `(a, b)_{K, m}` to the degree-`n` symbol `(a, b)_{K, n}`. -/
theorem rootsOfUnityPowOfDvd_normResidueSymbol {n m : ℕ} [NeZero n] [NeZero m]
    [HasEnoughRootsOfUnity K n] [HasEnoughRootsOfUnity K m] (h : n ∣ m) (a b : Kˣ) :
    rootsOfUnityPowOfDvd h (normResidueSymbol K m a b) = normResidueSymbol K n a b := by
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) (artinMap K a)
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (b : K))
    (NeZero.pos m)
  -- `γ ^ (m / n)` is an `n`-th root of `b`, so its Kummer ratio computes the degree-`n` symbol.
  have hγn : (γ ^ (m / n)) ^ n = algebraMap K (AlgebraicClosure K) (b : K) := by
    rw [← pow_mul, Nat.div_mul_cancel h, hγ]
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [coe_rootsOfUnityPowOfDvd_apply, Units.val_pow_eq_pow_val, map_pow,
    algebraMap_normResidueSymbol a b σ hσ hγ, algebraMap_normResidueSymbol a b σ hσ hγn,
    div_pow, map_pow]

/-- Raising the degree-`(n * m)` norm-residue symbol to the `m`-th power recovers the degree-`n`
norm-residue symbol. -/
theorem coe_normResidueSymbol_mul_pow {n m : ℕ} [NeZero n] [NeZero (n * m)]
    [HasEnoughRootsOfUnity K n] [HasEnoughRootsOfUnity K (n * m)] (a b : Kˣ) :
    (normResidueSymbol K (n * m) a b : Kˣ) ^ m = (normResidueSymbol K n a b : Kˣ) := by
  have h := congrArg Subtype.val
    (rootsOfUnityPowOfDvd_normResidueSymbol (K := K) (dvd_mul_right n m) a b)
  rwa [coe_rootsOfUnityPowOfDvd_apply, Nat.mul_div_cancel_left _ (NeZero.pos n)] at h

/-- **Norm functoriality of the norm-residue symbol in the Artin argument.** For a separable
extension `L / K` of nonarchimedean local fields with `a ∈ Lˣ` and `b ∈ Kˣ`, the symbol
`(N_{L/K} a, b)_{K, n}` mapped into `μ_n(L)` equals `(a, b)_{L, n}`. -/
theorem restrictRootsOfUnity_normResidueSymbol_normUnits_left {L : Type} [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    [HasEnoughRootsOfUnity L n] (a : Lˣ) (b : Kˣ) :
    restrictRootsOfUnity (algebraMap K L) n (normResidueSymbol K n (Algebra.normUnits K a) b) =
      normResidueSymbol L n a (Units.map (algebraMap K L).toMonoidHom b) := by
  have := finite_of_valuativeExtension K L
  let iota : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap L a)
  set σ := absoluteGaloisGroupExtend K L iota τ
  have hσ : (σ : Field.absoluteGaloisGroupAbelianization K) =
      artinMap K (Algebra.normUnits K a) := artinMap_norm L iota a τ hτ
  -- Since `n` is invertible in `L`, `b` has an `n`-th root `β` in the separable closure `Lˢ`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L n
  have := hζ.neZero'
  have : NeZero (n : SeparableClosure L) := .nat_of_injective (algebraMap L _).injective
  set bL : Lˣ := Units.map (algebraMap K L).toMonoidHom b
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap L (SeparableClosure L) (bL : L)) n
  let s := separableClosureRingEquiv K L iota
  set γ : SeparableClosure K := s β
  have hbL_val : (bL : L) = algebraMap K L (b : K) := by simp [bL]
  have hγ : γ ^ n = algebraMap K (SeparableClosure K) (b : K) := by
    rw [← map_pow, hβ, hbL_val, ← IsScalarTower.algebraMap_apply K L (SeparableClosure L),
      separableClosureRingEquiv_algebraMap_base]
  -- Read both Artin actions in `SeparableClosure K` along the identification `s : Lˢ ≃+* Kˢ`.
  have hactL := normResidueSymbol_spec_separableClosure a bL τ hτ hβ
  have hactK : absoluteGaloisGroupRestrictEquiv K σ γ =
      iota (algebraMap K L ((normResidueSymbol K n (Algebra.normUnits K a) b : Kˣ) : K)) * γ := by
    rw [normResidueSymbol_spec_separableClosure (Algebra.normUnits K a) b σ hσ hγ, iota.commutes]
  have hcmp : iota (algebraMap K L ((normResidueSymbol K n (Algebra.normUnits K a) b : Kˣ) : K)) *
      γ = iota ((normResidueSymbol L n a bL : Lˣ) : L) * γ := by
    rw [← hactK, absoluteGaloisGroupExtend_apply_separableClosureRingEquiv K L iota τ β,
      hactL, map_mul, separableClosureRingEquiv_algebraMap]
  apply Subtype.ext
  apply Units.ext
  rw [restrictRootsOfUnity_coe_apply]
  exact iota.injective (mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hγ) hcmp)

/-- **Norm functoriality of the norm-residue symbol in the radical argument.** For a separable
extension `L / K` of nonarchimedean local fields with `a ∈ Kˣ` and `b ∈ Lˣ`, the symbol
`(a, N_{L/K} b)_{K, n}` mapped into `μ_n(L)` equals `(a, b)_{L, n}`. -/
theorem restrictRootsOfUnity_normResidueSymbol_normUnits_right {L : Type} [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    [HasEnoughRootsOfUnity L n] (a : Kˣ) (b : Lˣ) :
    restrictRootsOfUnity (algebraMap K L) n (normResidueSymbol K n a (Algebra.normUnits K b)) =
      normResidueSymbol L n (Units.map (algebraMap K L).toMonoidHom a) b := by
  rw [normResidueSymbol_swap (n := n) (Algebra.normUnits K b) a, map_inv,
    restrictRootsOfUnity_normResidueSymbol_normUnits_left, ← normResidueSymbol_swap]

/-- On units coming from the base field `K`, passing to a separable local-field extension `L / K`
raises the norm-residue symbol to the degree `[L : K]`. -/
theorem normResidueSymbol_unitsMap_algebraMap {L : Type} [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    [HasEnoughRootsOfUnity L n] (a b : Kˣ) :
    normResidueSymbol L n (Units.map (algebraMap K L).toMonoidHom a)
        (Units.map (algebraMap K L).toMonoidHom b) =
      restrictRootsOfUnity (algebraMap K L) n (normResidueSymbol K n a b) ^
        Module.finrank K L := by
  rw [← restrictRootsOfUnity_normResidueSymbol_normUnits_left, RingHom.toMonoidHom_eq_coe,
    Algebra.normUnits_unitsMap_algebraMap, normResidueSymbol_pow_left, map_pow]

end DegreeAndNorm

/-! ### Transport along field isomorphisms and Galois automorphisms -/

section Isomorphism

/-- **Valuation-preserving ring isomorphisms preserve the norm-residue symbol.** For a ring
isomorphism `e : K ≃+* K'` between nonarchimedean local fields that preserves the valuative
preorder, `e ((a, b)_{K, n}) = (e a, e b)_{K', n}`. -/
theorem restrictRootsOfUnity_normResidueSymbol_of_vle_iff {K K' : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K']
    [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity K n] [HasEnoughRootsOfUnity K' n] (e : K ≃+* K')
    (hvle : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y) (a b : Kˣ) :
    restrictRootsOfUnity e.toMonoidHom n (normResidueSymbol K n a b) =
      normResidueSymbol K' n (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom b) := by
  -- Regard `K` as a degree-one extension of `K'` along `e⁻¹` (as in `artinMap_congr`), whose norm
  -- on units is `e`.
  let _ : Algebra K' K := e.symm.toRingHom.toAlgebra
  have hf : ∀ x : K', e.symm (algebraMap K' K' x) = algebraMap K' K x :=
    fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  let eA : K' ≃ₐ[K'] K := AlgEquiv.ofRingEquiv (f := e.symm) hf
  have : Algebra.IsSeparable K' K := Algebra.IsSeparable.of_algHom K' K' eA.symm.toAlgHom
  have : ValuativeExtension K' K := ⟨fun {x y} ↦ by
    rw [RingHom.algebraMap_toAlgebra, ← hvle]
    simp⟩
  have hnorm : Algebra.normUnits K' a = Units.map e.toMonoidHom a := by
    ext
    rw [Algebra.coe_normUnits, ← eA.apply_symm_apply (a : K), Algebra.norm_eq_of_algEquiv,
      Algebra.norm_self, MonoidHom.id_apply, Units.coe_map]
    simp [eA]
  have hb : Units.map (algebraMap K' K).toMonoidHom (Units.map e.toMonoidHom b) = b := by
    ext
    simp [RingHom.algebraMap_toAlgebra]
  have key := restrictRootsOfUnity_normResidueSymbol_normUnits_left (K := K') (L := K) (n := n)
    a (Units.map e.toMonoidHom b)
  rw [hnorm, hb] at key
  apply restrictRootsOfUnity_injective (algebraMap K' K) n (algebraMap K' K).injective
  rw [key]
  apply Subtype.ext
  apply Units.ext
  simp [restrictRootsOfUnity_coe_apply, RingHom.algebraMap_toAlgebra]

/-- **Naturality of the norm-residue symbol under continuous field isomorphisms.** If
`e : K ≃+* K'` is a continuous ring isomorphism between nonarchimedean local fields, then
`e ((a, b)_{K, n}) = (e a, e b)_{K', n}`. -/
theorem restrictRootsOfUnity_normResidueSymbol_of_continuous {K K' : Type} [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field K']
    [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity K n] [HasEnoughRootsOfUnity K' n] (e : K ≃+* K') (he : Continuous e)
    (a b : Kˣ) :
    restrictRootsOfUnity e.toMonoidHom n (normResidueSymbol K n a b) =
      normResidueSymbol K' n (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom b) :=
  restrictRootsOfUnity_normResidueSymbol_of_vle_iff e
    (e.toRingHom.map_vle_map_iff_of_continuous he) a b

/-- **Transport of the norm-residue symbol along an `F`-algebra isomorphism of local-field
extensions.** Let `F` be a nonarchimedean local field (not required to contain `μ_n`), and let `L`
and `L'` be compatible local-field extensions of `F` containing `μ_n`. Any `F`-algebra equivalence
`e : L ≃ₐ[F] L'` transports the symbol without an explicit continuity or valuation hypothesis:
`e ((a, b)_{L, n}) = (e a, e b)_{L', n}`. -/
theorem restrictRootsOfUnity_normResidueSymbol_algEquiv {F : Type*} {L L' : Type} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    [Field L'] [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
    [Algebra F L'] [ValuativeExtension F L'] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity L n]
    [HasEnoughRootsOfUnity L' n] (e : L ≃ₐ[F] L') (a b : Lˣ) :
    restrictRootsOfUnity e.toMonoidHom n (normResidueSymbol L n a b) =
      normResidueSymbol L' n (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom b) := by
  have := finite_of_valuativeExtension F L
  exact restrictRootsOfUnity_normResidueSymbol_of_vle_iff e.toRingEquiv
    (e.toRingHom.map_vle_map_iff_of_vle_iff (RingHom.id F) (fun _ _ ↦ Iff.rfl) e.commutes) a b

/-- **Transport of the norm-residue symbol under an `F`-algebra homomorphism** (in particular,
Galois conjugation `σ : E ≃ₐ[F] E`; Fesenko–Vostokov, IV §5, Proposition (9)). For a
nonarchimedean local field `F` (not required to contain `μ_n`), extensions `E / F` and `E' / F`, a
compatible local-field subextension `L` of `E / F` containing `μ_n`, and an `F`-algebra
homomorphism `f : E →ₐ[F] E'` whose image `f(L)` carries a compatible local-field structure,
`f ((a, b)_{L, n}) = (f a, f b)_{f(L), n}`. -/
theorem algHom_coe_normResidueSymbol {F : Type*} {E E' : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] [Field E']
    [Algebra F E'] (L : IntermediateField F E) [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension F L] (f : E →ₐ[F] E')
    [ValuativeRel (L.map f)] [TopologicalSpace (L.map f)] [IsNonarchimedeanLocalField (L.map f)]
    [ValuativeExtension F (L.map f)] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity L n]
    [HasEnoughRootsOfUnity (L.map f) n] (a b : Lˣ) :
    f (((normResidueSymbol L n a b : Lˣ) : L) : E) =
      (((normResidueSymbol (L.map f) n
        (Units.map (IntermediateField.equivMap L f).toMonoidHom a)
        (Units.map (IntermediateField.equivMap L f).toMonoidHom b) :
          (L.map f)ˣ) : L.map f) : E') := by
  simpa [restrictRootsOfUnity_coe_apply, IntermediateField.coe_equivMap_apply] using
    congrArg
      (fun ζ : rootsOfUnity n (L.map f) ↦ (((ζ : (L.map f)ˣ) : L.map f) : E'))
      (restrictRootsOfUnity_normResidueSymbol_algEquiv (F := F)
        (IntermediateField.equivMap L f) a b)

end Isomorphism

end TauCeti
