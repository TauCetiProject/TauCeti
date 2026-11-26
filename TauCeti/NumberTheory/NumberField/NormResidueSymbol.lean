/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.FinitePlace
public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Basic
public import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Tame
import TauCeti.RingTheory.DedekindDomain.SelmerGroup
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Norm-residue symbols at finite places of a number field

For a number field `K` containing the `n`-th roots of unity, we read the norm-residue symbol of
the images of `a, b ∈ Kˣ` in a completion `K_v` as an element of `rootsOfUnity n K`. All the
values then belong to the same group, as required to take their product. At a place where `n`,
`a` and `b` are units, the symbol is trivial, so only finitely many finite places contribute.

The first argument acts through arithmetic local reciprocity, as in `TauCeti.normResidueSymbol`.
The Artin characterization expresses each value by the action of
`TauCeti.ClassFieldTheory.localArtinAt` on an `n`-th root of the second argument in a finite normal
extension of `K`.

## References

* Parvati Shastri, *Reciprocity Laws: Artin–Hilbert*, §§5–8.
-/

public section

noncomputable section

open IsDedekindDomain NumberField TauCeti TauCeti.ClassFieldTheory

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-- The degree-`n` norm-residue symbol at the finite place `v`, with values in the roots of unity
of the number field. The first argument acts through the local Artin map. -/
def normResidueSymbolAtFinitePlace (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity K n] (a b : Kˣ) : rootsOfUnity n K :=
  v.adicCompletionRootsOfUnityEquiv.symm (normResidueSymbol (v.adicCompletion K) n
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b))

variable (v : HeightOneSpectrum (𝓞 K))

/-- Under the algebra map to the completion, the finite-place symbol is the local symbol of
the images of the two arguments. -/
@[simp]
theorem restrictRootsOfUnity_normResidueSymbolAtFinitePlace (a b : Kˣ) :
    restrictRootsOfUnity (algebraMap K (v.adicCompletion K)) n
        (v.normResidueSymbolAtFinitePlace n a b) =
      normResidueSymbol (v.adicCompletion K) n
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b) := by
  rw [normResidueSymbolAtFinitePlace,
    restrictRootsOfUnity_adicCompletionRootsOfUnityEquiv_symm_apply]

/-- The finite-place symbol is trivial when the Artin argument is `1`. -/
@[simp]
theorem normResidueSymbolAtFinitePlace_one_left (b : Kˣ) :
    v.normResidueSymbolAtFinitePlace n 1 b = 1 := by
  simp only [normResidueSymbolAtFinitePlace, map_one, normResidueSymbol_one_left]

/-- The finite-place symbol is trivial when the radical argument is `1`. -/
@[simp]
theorem normResidueSymbolAtFinitePlace_one_right (a : Kˣ) :
    v.normResidueSymbolAtFinitePlace n a 1 = 1 := by
  simp only [normResidueSymbolAtFinitePlace, map_one, normResidueSymbol_one_right]

/-- The finite-place symbol is multiplicative in the Artin argument. -/
theorem normResidueSymbolAtFinitePlace_mul_left (a a' b : Kˣ) :
    v.normResidueSymbolAtFinitePlace n (a * a') b =
      v.normResidueSymbolAtFinitePlace n a b * v.normResidueSymbolAtFinitePlace n a' b := by
  simp only [normResidueSymbolAtFinitePlace, map_mul, normResidueSymbol_mul_left]

/-- The finite-place symbol is multiplicative in the radical argument. -/
theorem normResidueSymbolAtFinitePlace_mul_right (a b b' : Kˣ) :
    v.normResidueSymbolAtFinitePlace n a (b * b') =
      v.normResidueSymbolAtFinitePlace n a b * v.normResidueSymbolAtFinitePlace n a b' := by
  simp only [normResidueSymbolAtFinitePlace, map_mul, normResidueSymbol_mul_right]

/-- An automorphism representing the local Artin symbol of `a` at `v` acts on every
`n`-th root of `b` in a finite normal extension by multiplication by the finite-place symbol. -/
theorem normResidueSymbolAtFinitePlace_spec {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Normal K L] (a b : Kˣ) (σ : Gal(L/K))
    (hσ : Group.Abelianization.of σ =
      localArtinAt K L v (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a))
    {β : L} (hβ : β ^ n = algebraMap K L (b : K)) :
    σ β = algebraMap K L ((v.normResidueSymbolAtFinitePlace n a b : Kˣ) : K) * β := by
  let F := v.adicCompletion K
  let j : L →ₐ[K] AlgebraicClosure F := IsAlgClosed.lift
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective
    (artinMap F (Units.map (algebraMap K F).toMonoidHom a))
  let σ' := j.restrictNormalHom (AlgEquiv.restrictScalarsHom K τ)
  have hab : Group.Abelianization.of σ = Group.Abelianization.of σ' := by
    rw [hσ, localArtinAt_apply, ← hτ, decompositionRestrict_mk_eq_restrictNormalHom j]
  -- The action on the radical already factors through the abelianization via its Kummer character.
  have hβ₀ := ne_zero_of_pow_eq_algebraMap hβ
  let χ : Gal(L/K) →* Lˣ :=
    MonoidHom.mk' (fun g ↦ Units.mk0 (g β / β) (div_ne_zero (by simpa using hβ₀) hβ₀))
      (fun g h ↦ Units.ext (g.mul_apply_div_self_of_pow_eq h hβ))
  have hχ : χ σ = χ σ' := congrArg (Group.Abelianization.lift χ) hab
  have hact : σ β = σ' β := by
    exact (div_left_inj₀ hβ₀).mp (congrArg Units.val hχ)
  have hjβ : j β ^ n = algebraMap F (AlgebraicClosure F)
      (Units.map (algebraMap K F).toMonoidHom b : F) := by
    rw [← map_pow, hβ, AlgHom.commutes, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, IsScalarTower.algebraMap_apply K F (AlgebraicClosure F)]
  have hμ := congrArg (fun z : rootsOfUnity n F ↦ ((z : Fˣ) : F))
    (v.restrictRootsOfUnity_normResidueSymbolAtFinitePlace a b)
  rw [restrictRootsOfUnity_coe_apply] at hμ
  refine j.injective (calc
    j (σ β) = τ.toRingEquiv (j β) := (congrArg j hact).trans
      (j.restrictNormalHom_commutes (AlgEquiv.restrictScalarsHom K τ) β)
    _ = j (algebraMap K L ((v.normResidueSymbolAtFinitePlace n a b : Kˣ) : K) * β) := by
      rw [map_mul, AlgHom.commutes,
        IsScalarTower.algebraMap_apply K F (AlgebraicClosure F), hμ]
      exact normResidueSymbol_spec _ _ τ hτ hjβ)

/-- If `v` does not divide `n` and both arguments are units at `v`, the finite-place symbol is
trivial. -/
theorem normResidueSymbolAtFinitePlace_eq_one (hn : (n : 𝓞 K) ∉ v.asIdeal) {a b : Kˣ}
    (ha : v.valuation K (a : K) = 1) (hb : v.valuation K (b : K) = 1) :
    v.normResidueSymbolAtFinitePlace n a b = 1 := by
  have heq := normResidueSymbol_eq_one_of_mem_unitFiltration_zero (n := n)
    (fun h ↦ hn (v.ringChar_residueField_adicCompletion_dvd_iff.mp h))
    ((v.unitsMap_algebraMap_mem_unitFiltration_zero_iff a).mpr ha)
    ((v.unitsMap_algebraMap_mem_unitFiltration_zero_iff b).mpr hb)
  apply restrictRootsOfUnity_injective (algebraMap K (v.adicCompletion K)) n
    (algebraMap K (v.adicCompletion K)).injective
  rw [v.restrictRootsOfUnity_normResidueSymbolAtFinitePlace, map_one]
  exact heq

/-- The degree-`n` norm-residue symbol of two global elements is trivial at all but finitely
many finite places. -/
theorem hasFiniteMulSupport_normResidueSymbolAtFinitePlace (a b : Kˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.normResidueSymbolAtFinitePlace n a b := by
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  refine (((finite_setOfPred_valuation_ne_one (R := 𝓞 K) hn).union
    (finite_setOfPred_valuation_ne_one a.ne_zero)).union
    (finite_setOfPred_valuation_ne_one b.ne_zero)).subset fun v hv ↦ ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  obtain ⟨⟨hn, ha⟩, hb⟩ := h
  apply hv (v.normResidueSymbolAtFinitePlace_eq_one _ ha hb)
  rw [← v.intValuation_eq_one_iff, ← v.valuation_of_algebraMap (K := K)]
  simpa only [← map_natCast (algebraMap (𝓞 K) K) n] using hn

end IsDedekindDomain.HeightOneSpectrum
