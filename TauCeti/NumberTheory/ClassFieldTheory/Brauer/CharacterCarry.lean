/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified

/-!
# The local invariant of the carry class of an unramified character

Let `F` be a nonarchimedean local field, `E/F` a finite unramified Galois extension inside `Fˢ`
with arithmetic Frobenius `φ`, `χ : Gal(E/F) → ℚ/ℤ` a character and `a ∈ Fˣ`. Read on `G_F`
through restriction to `E`, the character has open kernel
(`IntermediateField.isOpen_ker_comp_restrictNormalHom`), and its carry cocycle with the invariant
`a ∈ ((Fˢ)ˣ)^{G_F}`,

```text
(g, h) ↦ a ^ ⌊χ'(g|_E) + χ'(h|_E)⌋,
```

is a class of `Br F`: classically, the cup product `a ∪ δχ`, the class of the cyclic algebra of
`a` and `χ`. Its local invariant is

```text
inv_F (a ∪ δχ) = v_F(a) · χ(φ)       (invMap_characterCarryCocycle).
```

For the character with `χ(φ) = 1 / [E : F]`, the Frobenius character
`TauCeti.ClassFieldTheory.frobeniusCharacter` read on `Gal(E/F)`, the carry cocycle is the
inflation of the carry cocycle of `a` at `φ`, which represents the unramified class
`unramifiedClass F E a` of invariant `v_F(a) / [E : F]`
(`TauCeti.ClassFieldTheory.unramifiedInv_unramifiedClass`). Every character of the cyclic group
`Gal(E/F)` is an integer multiple of that one, and the class of the carry cocycle is additive in
the character (`TauCeti.ContCohomology.characterCarryCocycle_zsmul_character`).

This is the local computation behind the global classes with prescribed local invariants: the
carry cocycle of a global character and an idele localizes, by naturality along the decomposition
maps (`TauCeti.ContCohomology.cocyclesMap2_characterCarryCocycle`), to the carry cocycles of the
local characters and the components of the idele.

## Main results

* `TauCeti.ClassFieldTheory.invMap_characterCarryCocycle`: the local invariant of the carry class
  of an unramified character `χ` and `a ∈ Fˣ` is `v_F(a) · χ(φ)`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §1, Proposition 2.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter VI (Serre, *Local
  Class Field Theory*), §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension F E]
  [IsUnramified F E]

/-- Arithmetic Frobenius generates `Gal(E/F)`. -/
private theorem mem_zmultiples_ofMul_frobeniusAlgEquiv (x : Additive Gal(E/F)) :
    x ∈ AddSubgroup.zmultiples (Additive.ofMul (frobeniusAlgEquiv (K := F) (L := E))) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    ((zpowers_frobeniusAlgEquiv (K := F) (L := E)).symm ▸ Subgroup.mem_top x.toMul)
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [← ofMul_zpow, hk, ofMul_toMul]⟩

/-- **The invariant of the carry class of a Frobenius character** is `v_F(a) / [E : F]`: for a
character `χ₀` sending arithmetic Frobenius to `1 / [E : F]`, the carry cocycle is the inflation
of the carry cocycle of `a` at Frobenius, which represents the unramified class of `a`. -/
private theorem invMap_characterCarryCocycle_of_apply_frobenius
    (χ₀ : Additive Gal(E/F) →+ AddCircle (1 : ℚ))
    (hχ₀ : χ₀ (.ofMul (frobeniusAlgEquiv (K := F) (L := E))) =
      ((1 / Module.finrank F E : ℚ) : AddCircle (1 : ℚ))) (a : Fˣ) :
    invMap F (unitsRepH2Equiv F (characterCarryCocycle
      (χ₀.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure F) E).toAdditive)
      (E.isOpen_ker_comp_restrictNormalHom χ₀) (baseUnitsEquivInvariants F (.ofMul a)))) =
      (((normalizedValuation F a).toAdd / Module.finrank F E : ℚ) : AddCircle (1 : ℚ)) := by
  set n := Module.finrank F E
  set φ := frobeniusAlgEquiv (K := F) (L := E)
  have hpow (i : ℕ) : χ₀ (.ofMul (φ ^ i)) = ((i / n : ℚ) : AddCircle (1 : ℚ)) := by
    rw [ofMul_pow, map_nsmul, hχ₀, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div]
  set b : Eˣ := Units.map (algebraMap F E : F →* E) a
  -- The carry cocycle is read off `Gal(E/F)`, with the value `b ^ carry` at `(s, t)`.
  obtain ⟨c, hcu, hc⟩ := exists_relBrCocycle_eq F E E.val
    (characterCarryCocycle _ (E.isOpen_ker_comp_restrictNormalHom χ₀)
      (baseUnitsEquivInvariants F (.ofMul a)))
    (fun p ↦ b ^ characterCarry χ₀ p.1 p.2) fun g h ↦ by
      apply Additive.toMul.injective
      apply Units.ext
      simp [characterCarryCocycle_apply, b]
  rw [← hc, ← relBrInfl_H2π, invMap_relBrInfl]
  -- The cocycle `c` is the carry cocycle of `a` at Frobenius.
  have hφ (σ : Gal(E/F)) : σ ∈ Subgroup.zpowers φ := by
    rw [zpowers_frobeniusAlgEquiv]
    exact Subgroup.mem_top σ
  have horder : orderOf φ = n := by
    rw [orderOf_frobeniusAlgEquiv, IsUnramified.inertiaDegree_eq_finrank]
  rw [H2π_eq_cyclicClass hφ c a fun i j hi hj ↦ ?_, ← unramifiedClass_eq_cyclicClass]
  · exact unramifiedInv_unramifiedClass a
  rw [horder] at hi hj ⊢
  -- The values of `c` are read in `Eˣ` through `Rep.toAdditive`, which is the identity.
  refine (hcu (φ ^ i, φ ^ j)).trans ?_
  rw [characterCarry_eq_ite _ hi hj (hpow i) (hpow j)]
  split_ifs <;> simp [b]

/-- **The local invariant of the carry class of an unramified character.** For a character `χ` of
the Galois group of a finite unramified Galois extension `E/F` inside `Fˢ`, read on `G_F`, and
`a ∈ Fˣ`, the class in `Br F` of the carry cocycle of `χ` and `a`, classically the cup product
`a ∪ δχ`, has invariant `v_F(a) · χ(φ)`, where `φ` is arithmetic Frobenius. -/
theorem invMap_characterCarryCocycle (χ : Additive Gal(E/F) →+ AddCircle (1 : ℚ)) (a : Fˣ) :
    invMap F (unitsRepH2Equiv F (characterCarryCocycle
      (χ.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure F) E).toAdditive)
      (E.isOpen_ker_comp_restrictNormalHom χ) (baseUnitsEquivInvariants F (.ofMul a)))) =
      (normalizedValuation F a).toAdd • χ (.ofMul (frobeniusAlgEquiv (K := F) (L := E))) := by
  set n := Module.finrank F E
  set φ := frobeniusAlgEquiv (K := F) (L := E)
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  -- `χ(φ)` is killed by `n`, so it is `k / n` for an integer `k`, and `χ = k • χ₀` for the
  -- Frobenius character `χ₀`, read on `Gal(E/F)`.
  set χ₀ := (frobeniusCharacter F E).comp (Abelianization.of (G := Gal(E/F))).toAdditive
  have hχ₀ : χ₀ (.ofMul φ) = ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
    rw [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul]
    exact frobeniusCharacter_frobenius F E
  have hmem : χ (.ofMul φ) ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) n := by
    have horder : n = orderOf φ := by
      rw [orderOf_frobeniusAlgEquiv, IsUnramified.inertiaDegree_eq_finrank]
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, ← ofMul_pow, horder, pow_orderOf_eq_one,
      ofMul_one, map_zero]
  obtain ⟨k, hk⟩ := AddCircle.exists_zsmul_eq_of_mem_torsionBy (p := (1 : ℚ)) hn hmem
  have hχ : χ = k • χ₀ :=
    (AddMonoidHom.eq_iff_eq_on_generator (mem_zmultiples_ofMul_frobeniusAlgEquiv E) _ _).2 <| by
      rw [AddMonoidHom.smul_apply, hχ₀, hk]
  have hcomp : χ.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure F) E).toAdditive =
      k • χ₀.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure F) E).toAdditive := by
    rw [hχ, AddMonoidHom.smul_comp]
  simp only [hcomp]
  rw [characterCarryCocycle_zsmul_character (E.isOpen_ker_comp_restrictNormalHom _) k, map_zsmul,
    map_zsmul, invMap_characterCarryCocycle_of_apply_frobenius E χ₀ hχ₀, ← hk,
    ← AddCircle.coe_zsmul, ← AddCircle.coe_zsmul, ← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  ring

end TauCeti.ClassFieldTheory
