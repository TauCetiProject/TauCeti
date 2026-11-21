/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Highest
public import TauCeti.RepresentationTheory.LSPath.Dual
public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Raise
public import TauCeti.RepresentationTheory.LSPath.Realization

import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The normal crystal of Lakshmibai–Seshadri paths

For a finite reduced root datum `P : RootDatum ι X Y` with base `b` and dominant weight `λ : X`,
Littelmann's path model equips `LSPath P b λ` with a connected normal crystal `LSPath.crystal`
whose unique highest element is `LSPath.straight λ`. We transport `PLPath.normalCrystalOn` from
the canonical rational realization `X → ℚ ⊗[ℤ] X` along `LSPath.toPLPath`.

Given a realization `(𝕜, V, f, F)` consisting of `f : X →+ V` and height forms
`F : b.support → Module.Dual 𝕜 V`, we say it is **compatible** (with the simple coroots) when
`F i (f x) = (P.coroot' i x : 𝕜)` for every `i : b.support` and `x : X` (or
`F (f x) = (P.coroot' i x : 𝕜)` for a single root `i`). Pushing forward along
`PLPath.mapSemilinear` and `AddMonoidHom.liftBaseChangeSemilinear` gives universal compatibility
of `LSPath.crystal` with `PLPath.raise`, `PLPath.lower`, and `PLPath.minHeight` in every
compatible realization.

## Main definitions and results

* `TauCeti.LSPath.crystal`, `TauCeti.LSPath.raise_toPLPath`, `TauCeti.LSPath.lower_toPLPath`,
  `TauCeti.LSPath.toPLPathHom`, `TauCeti.LSPath.toPLPathComponentIso`.
* `TauCeti.LSPath.congrIso`, `TauCeti.LSPath.dualIso`: shape transport and path duality.
* `TauCeti.LSPath.forall_crystal_e_eq_none_iff`, `TauCeti.LSPath.exists_fWord_straight_eq_some`,
  `TauCeti.LSPath.connected_crystal_graph`,
  `TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord`,
  `TauCeti.LSPath.mem_range_toPLPath_iff_reflTransGen`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Sections 2 and 4.
-/

public section

open scoped TensorProduct

namespace TauCeti.LSPath

open RootPairing

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

/-! ### Construction of the normal crystal on `LSPath P b λ` -/

private noncomputable abbrev ratCrystalOn (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (Set.range (toRatPLPath (P := P) (b := b) (lam := lam))) :=
  PLPath.normalCrystalOn (P := P) (b := b) (𝕜 := ℚ) (V := ℚ ⊗[ℤ] X)
    (f := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom)
    (F := fun i ↦ Module.Dual.baseChange ℚ (P.coroot' i))
    (by simpa only [LinearMap.toAddMonoidHom_coe] using P.tensorProduct_mk_injective ℚ)
    (fun (i : b.support) (x : X) ↦ by
      rw [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Module.Dual.baseChange_apply_tmul,
        zsmul_eq_mul, mul_one])
    (isCrystalSet_range_toPLPath hlam _ fun (i : b.support) (x : X) ↦ by
      rw [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Module.Dual.baseChange_apply_tmul,
        zsmul_eq_mul, mul_one])

private noncomputable abbrev toRatRangeEquiv (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ Set.range (toRatPLPath (P := P) (b := b) (lam := lam)) :=
  Equiv.ofInjective toRatPLPath (toRatPLPath_injective hlam)

/-- **The normal crystal of Lakshmibai–Seshadri paths of dominant shape `λ`**, with weight map
`LSPath.weight` and root operators realizing Littelmann's path root operators in every compatible
realization. -/
noncomputable def crystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (ratCrystalOn hlam).transport (toRatRangeEquiv hlam).symm

private theorem map_toRatPLPath_symm (hlam : lam ∈ dominantChamber P b)
    (y : Option (Set.range (toRatPLPath (P := P) (b := b) (lam := lam)))) :
    (y.map (toRatRangeEquiv hlam).symm).map toRatPLPath = y.unattach := by
  rw [Option.map_map, toRatRangeEquiv, Equiv.self_comp_ofInjective_symm, ← Option.unattach]

private theorem map_toRatPLPath_crystal_e (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    ((crystal hlam).e i π).map toRatPLPath =
      PLPath.raise (Module.Dual.baseChange ℚ (P.coroot' i))
        ((TensorProduct.mk ℤ ℚ X 1) (P.root i)) (toRatPLPath π) := by
  rw [crystal, NormalCrystal.transport_e, Equiv.symm_symm, map_toRatPLPath_symm, ratCrystalOn,
    PLPath.unattach_normalCrystalOn_e, toRatRangeEquiv, Equiv.ofInjective_apply,
    LinearMap.toAddMonoidHom_coe]

private theorem map_toRatPLPath_crystal_f (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (π : LSPath P b lam) :
    ((crystal hlam).f i π).map toRatPLPath =
      PLPath.lower (Module.Dual.baseChange ℚ (P.coroot' i))
        ((TensorProduct.mk ℤ ℚ X 1) (P.root i)) (toRatPLPath π) := by
  rw [crystal, NormalCrystal.transport_f, Equiv.symm_symm, map_toRatPLPath_symm, ratCrystalOn,
    PLPath.unattach_normalCrystalOn_f, toRatRangeEquiv, Equiv.ofInjective_apply,
    LinearMap.toAddMonoidHom_coe]

/-! ### Universal compatibility with realizations -/

@[simp]
theorem crystal_wt (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (crystal hlam).wt π = π.weight hlam := by
  rw [crystal, NormalCrystal.transport_wt, Equiv.symm_symm, ratCrystalOn,
    PLPath.normalCrystalOn_wt_eq_iff, toRatRangeEquiv, Equiv.ofInjective_apply,
    apply_weight ℚ (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom hlam π]

section Realization

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (hlam : lam ∈ dominantChamber P b)

section ArbitraryRealization

variable (f : X →+ V)

section SingleRoot

variable (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))

include hF

/-- **Universal compatibility of `crystal.e` with `PLPath.raise`** in any compatible realization
`(𝕜, V, f, F)` (`∀ x, F (f x) = (P.coroot' i x : 𝕜)`). -/
theorem raise_toPLPath (π : LSPath P b lam) :
    PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((crystal hlam).e i π).map (·.toPLPath 𝕜 f) := by
  have hFG := f.apply_liftBaseChangeSemilinear (Rat.castHom 𝕜) F
    (Module.Dual.baseChange ℚ (P.coroot' i)) fun x ↦ by
      simp [hF x]
  rw [← mapSemilinear_toRatPLPath f π,
    ← f.liftBaseChangeSemilinear_mk_one (Rat.castHom 𝕜) (P.root i),
    PLPath.raise_mapSemilinear _ (Rat.cast_mono (K := 𝕜)) hFG, ← map_toRatPLPath_crystal_e hlam,
    Option.map_map]
  exact congrArg (Option.map · _) (funext fun ρ ↦ mapSemilinear_toRatPLPath (𝕜 := 𝕜) f ρ)

/-- **Universal compatibility of `crystal.f` with `PLPath.lower`** in any compatible realization
`(𝕜, V, f, F)` (`∀ x, F (f x) = (P.coroot' i x : 𝕜)`). -/
theorem lower_toPLPath (π : LSPath P b lam) :
    PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((crystal hlam).f i π).map (·.toPLPath 𝕜 f) := by
  have hFG := f.apply_liftBaseChangeSemilinear (Rat.castHom 𝕜) F
    (Module.Dual.baseChange ℚ (P.coroot' i)) fun x ↦ by
      simp [hF x]
  rw [← mapSemilinear_toRatPLPath f π,
    ← f.liftBaseChangeSemilinear_mk_one (Rat.castHom 𝕜) (P.root i),
    PLPath.lower_mapSemilinear _ (Rat.cast_mono (K := 𝕜)) hFG, ← map_toRatPLPath_crystal_f hlam,
    Option.map_map]
  exact congrArg (Option.map · _) (funext fun ρ ↦ mapSemilinear_toRatPLPath (𝕜 := 𝕜) f ρ)

/-- Universal compatibility of `crystal.ε` with `PLPath.minHeight` in any compatible realization
`(𝕜, V, f, F)` (`∀ x, F (f x) = (P.coroot' i x : 𝕜)`). -/
theorem minHeight_toPLPath_eq_neg_crystal_ε (π : LSPath P b lam) :
    (π.toPLPath 𝕜 f).minHeight F = -((crystal hlam).ε i π : 𝕜) := by
  have hFG := f.apply_liftBaseChangeSemilinear (Rat.castHom 𝕜) F
    (Module.Dual.baseChange ℚ (P.coroot' i)) fun x ↦ by
      simp [hF x]
  have hε : ((crystal hlam).ε i π : ℚ) =
      -(toRatPLPath π).minHeight (Module.Dual.baseChange ℚ (P.coroot' i)) := by
    rw [crystal, NormalCrystal.transport_ε, Equiv.symm_symm, ratCrystalOn,
      PLPath.cast_normalCrystalOn_ε]
    simp [toRatRangeEquiv]
  rw [← mapSemilinear_toRatPLPath f π, PLPath.minHeight_mapSemilinear (Rat.cast_mono (K := 𝕜)) hFG]
  simpa using congrArg (fun q : ℚ ↦ -(q : 𝕜)) hε.symm

/-- Universal compatibility of `crystal.φ` with `PLPath.minHeight` in any compatible realization
`(𝕜, V, f, F)` (`∀ x, F (f x) = (P.coroot' i x : 𝕜)`). -/
theorem apply_endpoint_sub_minHeight_toPLPath_eq_crystal_φ (π : LSPath P b lam) :
    F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F = ((crystal hlam).φ i π : 𝕜) := by
  rw [← apply_weight 𝕜 f hlam, hF, minHeight_toPLPath_eq_neg_crystal_ε hlam f i F hF]
  have hcast : (((crystal hlam).φ i π : 𝕜) - ((crystal hlam).ε i π : 𝕜)) =
      (P.coroot' i (π.weight hlam) : 𝕜) := by
    simpa [crystal_wt] using congrArg (Int.cast (R := 𝕜)) ((crystal hlam).φ_sub_ε i π)
  linarith

end SingleRoot

/-- Raising along a word on realized LS paths agrees with `(crystal hlam).eWord`, requiring
compatibility `F i (f x) = (P.coroot' i x : 𝕜)` only for indices appearing in `w`. -/
theorem raiseWord_toPLPath (F : b.support → Module.Dual 𝕜 V) (w : List b.support)
    (hF : ∀ i ∈ w, ∀ x, F i (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    PLPath.raiseWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((crystal hlam).eWord w π).map (·.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [PLPath.raiseWord_cons, NormalCrystal.eWord_cons,
      raise_toPLPath hlam f i (F i) (hF i List.mem_cons_self)]
    cases (crystal hlam).e i π <;> simp [ih fun j hj ↦ hF j (List.mem_cons_of_mem i hj)]

/-- Lowering along a word on realized LS paths agrees with `(crystal hlam).fWord`, requiring
compatibility `F i (f x) = (P.coroot' i x : 𝕜)` only for indices appearing in `w`. -/
theorem lowerWord_toPLPath (F : b.support → Module.Dual 𝕜 V) (w : List b.support)
    (hF : ∀ i ∈ w, ∀ x, F i (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    PLPath.lowerWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((crystal hlam).fWord w π).map (·.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [PLPath.lowerWord_cons, NormalCrystal.fWord_cons,
      lower_toPLPath hlam f i (F i) (hF i List.mem_cons_self)]
    cases (crystal hlam).f i π <;> simp [ih fun j hj ↦ hF j (List.mem_cons_of_mem i hj)]

/-- Iterated raising on realized LS paths agrees with `(crystal hlam).eIter`. -/
theorem raiseIter_toPLPath (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (n : ℕ) (π : LSPath P b lam) :
    PLPath.raiseIter F (f (P.root i)) n (π.toPLPath 𝕜 f) =
      ((crystal hlam).eIter i n π).map (·.toPLPath 𝕜 f) := by
  simpa [PLPath.raiseWord_replicate, NormalCrystal.eWord_replicate] using
    raiseWord_toPLPath hlam f (fun _ ↦ F) (List.replicate n i)
      (fun _ hj x ↦ (List.mem_replicate.mp hj).2 ▸ hF x) π

/-- Iterated lowering on realized LS paths agrees with `(crystal hlam).fIter`. -/
theorem lowerIter_toPLPath (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (n : ℕ) (π : LSPath P b lam) :
    PLPath.lowerIter F (f (P.root i)) n (π.toPLPath 𝕜 f) =
      ((crystal hlam).fIter i n π).map (·.toPLPath 𝕜 f) := by
  simpa [PLPath.lowerWord_replicate, NormalCrystal.fWord_replicate] using
    lowerWord_toPLPath hlam f (fun _ ↦ F) (List.replicate n i)
      (fun _ hj x ↦ (List.mem_replicate.mp hj).2 ▸ hF x) π

end ArbitraryRealization

section FaithfulRealization

variable {f : X →+ V}

/-- Characterization of `(crystal hlam).e i π = some ρ` in a faithful, ray-separating,
compatible realization `(𝕜, V, f, F)`. -/
theorem crystal_e_eq_some_iff (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    {π ρ : LSPath P b lam} :
    (crystal hlam).e i π = some ρ ↔
      PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [raise_toPLPath hlam f i F hF,
    ← (Option.map_injective (toPLPath_injective hlam hf hS)).eq_iff, Option.map_some]

/-- Characterization of `(crystal hlam).f i π = some ρ` in a faithful, ray-separating,
compatible realization `(𝕜, V, f, F)`. -/
theorem crystal_f_eq_some_iff (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜))
    {π ρ : LSPath P b lam} :
    (crystal hlam).f i π = some ρ ↔
      PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [lower_toPLPath hlam f i F hF,
    ← (Option.map_injective (toPLPath_injective hlam hf hS)).eq_iff, Option.map_some]

/-- Realization `LSPath.toPLPath` as a strict crystal morphism into `PLPath.normalCrystal`,
for any injective compatible realization `(𝕜, V, f, F)` (`∀ i x, F i (f x) = (P.coroot' i x : 𝕜)`).
-/
noncomputable def toPLPathHom (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    NormalCrystal.StrictHom (crystal hlam) (PLPath.normalCrystal hf hF) where
  toFun π := ⟨π.toPLPath 𝕜 f, isIntegralPath_toPLPath hlam f F hF π⟩
  wt_toFun π := (PLPath.normalCrystalOn_wt_eq_iff (hf := hf) (hF := hF)
    (hS := PLPath.isCrystalSet_setOf_isIntegralPath)).mpr (by simp [apply_weight 𝕜 f hlam π])
  e_toFun i π := by rw [PLPath.normalCrystalOn_e_eq_map_iff, raise_toPLPath hlam f i (F i) (hF i)]

@[simp]
theorem toPLPathHom_apply (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    (toPLPathHom hlam hf hF π).val = π.toPLPath 𝕜 f := (rfl)

end FaithfulRealization

end Realization

/-! ### Shape congruence and Littelmann's path duality as strict crystal isomorphisms -/

/-- Shape transport `LSPath.congr` along `λ = λ'` is a strict isomorphism of normal crystals. -/
noncomputable def congrIso {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b)
    (hlam' : lam' ∈ dominantChamber P b := h ▸ hlam) :
    NormalCrystal.StrictIso (crystal hlam) (crystal hlam') where
  toEquiv := congr h
  wt_toFun π := by subst h; simp
  e_toFun i π := by subst h; simp

@[simp]
theorem coe_congrIso {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b)
    (hlam' : lam' ∈ dominantChamber P b) : ⇑(congrIso h hlam hlam') = congr h := (rfl)

@[simp]
theorem congrIso_refl (hlam : lam ∈ dominantChamber P b) :
    congrIso (rfl : lam = lam) hlam hlam = NormalCrystal.StrictIso.refl (crystal hlam) :=
  NormalCrystal.StrictIso.ext fun _ ↦ by simp

@[simp]
theorem congrIso_symm {lam' : X} (h : lam = lam') (hlam : lam ∈ dominantChamber P b)
    (hlam' : lam' ∈ dominantChamber P b) :
    (congrIso h hlam hlam').symm = congrIso h.symm hlam' hlam := by
  subst h
  exact NormalCrystal.StrictIso.ext fun π ↦ EquivLike.injective (congrIso rfl hlam hlam') (by simp)

@[simp]
theorem congrIso_trans {lam₁ lam₂ lam₃ : X} (h₁ : lam₁ = lam₂) (h₂ : lam₂ = lam₃)
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (hlam₃ : lam₃ ∈ dominantChamber P b) :
    (congrIso h₁ hlam₁ hlam₂).trans (congrIso h₂ hlam₂ hlam₃) =
      congrIso (h₁.trans h₂) hlam₁ hlam₃ := by
  subst h₁ h₂; exact NormalCrystal.StrictIso.ext fun _ ↦ by simp

/-- **Littelmann's path duality `LSPath.dual` is a strict crystal isomorphism**
`(crystal hlam).dual ≃ crystal hlam'`. -/
noncomputable def dualIso (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b := by
      have := P.flip_isReduced; exact neg_smul_mem_dominantChamber_longestElement hlam) :
    NormalCrystal.StrictIso (crystal hlam).dual (crystal hlam') where
  toEquiv := dual
  wt_toFun π := by simp [weight_dual π hlam hlam']
  e_toFun i π := by
    simp only [Equiv.toFun_as_coe]
    apply Option.map_injective (toRatPLPath_injective hlam')
    have hcompat : ∀ x, Module.Dual.baseChange ℚ (P.coroot' i)
        ((TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom x) = (P.coroot' i x : ℚ) := fun x ↦ by
      simp [TensorProduct.mk_apply]
    rw [← raise_toPLPath hlam' _ i _ hcompat, toPLPath_dual, PLPath.raise_reverse,
      lower_toPLPath hlam _ i _ hcompat, NormalCrystal.dual_e, Option.map_map, Option.map_map]
    exact congrArg (Option.map · _) (funext fun ρ : LSPath P b lam ↦ (toPLPath_dual ρ ℚ _).symm)

@[simp]
theorem coe_dualIso (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b) :
    ⇑(dualIso hlam hlam') = dual := (rfl)

@[simp]
theorem coe_dualIso_symm (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b) :
    ⇑(dualIso hlam hlam').symm = dual.symm :=
  funext fun π ↦ EquivLike.injective (dualIso hlam hlam') (by simp)

/-! ### Highest element, connectedness, and comparison with the operator-generated component -/

section Component

variable (hlam : lam ∈ dominantChamber P b)
include hlam

/-- **Uniqueness of the highest LS path:** `(∀ i, e_i π = none) ↔ π = straight λ`. -/
theorem forall_crystal_e_eq_none_iff (π : LSPath P b lam) :
    (∀ i, (crystal hlam).e i π = none) ↔ π = straight lam := by
  have := P.flip_isReduced
  have hcompat : ∀ (i : b.support) (x : X), Module.Dual.baseChange ℚ (P.coroot' i)
      ((TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom x) = (P.coroot' i x : ℚ) := fun i x ↦ by
    simp [TensorProduct.mk_apply]
  rw [← π.forall_raise_eq_none_iff hlam (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
    (fun i ↦ Module.Dual.baseChange ℚ (P.coroot' i)) hcompat]
  exact forall_congr' fun i ↦ by
    rw [raise_toPLPath hlam _ i _ (hcompat i), Option.map_eq_none_iff]

@[simp]
theorem crystal_e_straight (i : b.support) : (crystal hlam).e i (straight lam) = none :=
  (forall_crystal_e_eq_none_iff hlam (straight lam)).mpr rfl i

@[simp]
theorem crystal_ε_straight (i : b.support) : (crystal hlam).ε i (straight lam) = 0 :=
  ((crystal hlam).ε_eq_zero_iff).mpr (crystal_e_straight hlam i)

/-- The lowering string length of `straight λ` along a simple root `αᵢ` equals `⟨λ, αᵢ^∨⟩`. -/
theorem natCast_crystal_φ_straight (i : b.support) :
    ((crystal hlam).φ i (straight lam) : ℤ) = P.coroot' i lam := by
  simpa [RootPairing.coroot'] using (crystal hlam).φ_sub_ε i (straight lam)

@[simp]
theorem crystal_φ_straight (i : b.support) :
    (crystal hlam).φ i (straight lam) = (P.coroot' i lam).toNat := by
  rw [← natCast_crystal_φ_straight hlam i, Int.toNat_natCast]

/-- **Every LS path of dominant shape `λ` is obtained from `straight λ` by a lowering word.** -/
theorem exists_fWord_straight_eq_some (π : LSPath P b lam) :
    ∃ w : List b.support, (crystal hlam).fWord w (straight lam) = some π := by
  have := P.flip_isReduced; have := finite hlam
  exact (crystal hlam).exists_fWord_eq_some_of_unique_highest
    (fun x hx ↦ (forall_crystal_e_eq_none_iff hlam x).mp hx) π

/-- **The crystal graph of `LSPath P b λ` is connected** for every dominant weight `λ`. -/
theorem connected_crystal_graph : (crystal hlam).graph.Connected :=
  (crystal hlam).graph.connected_iff_exists_forall_reachable.mpr ⟨straight lam, fun π ↦
    let ⟨_, hw⟩ := exists_fWord_straight_eq_some hlam π
    (crystal hlam).graph_reachable_of_fWord_eq_some hw⟩

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- **Littelmann's path-model theorem (lowering-word form).** In every compatible realization
`(𝕜, V, f, F)` (`∀ i x, F i (f x) = (P.coroot' i x : 𝕜)`), the realized LS paths of dominant
shape `λ` are the paths obtained from `PLPath.straight 𝕜 (f λ)` by a lowering word along the
simple roots. -/
theorem mem_range_toPLPath_iff_exists_lowerWord (f : X →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜)) {p : PLPath 𝕜 V} :
    (p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      ∃ w : List b.support,
        PLPath.lowerWord F (fun i ↦ f (P.root i)) w (PLPath.straight 𝕜 (f lam)) = some p := by
  refine ⟨fun ⟨π, hπ⟩ ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
  · subst hπ; obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
    exact ⟨w, by rw [← toPLPath_straight (P := P) (b := b) 𝕜 f,
      lowerWord_toPLPath hlam f F w (fun i _ ↦ hF i) (straight lam), hw, Option.map_some]⟩
  · rw [← toPLPath_straight (P := P) (b := b) 𝕜 f,
      lowerWord_toPLPath hlam f F w (fun i _ ↦ hF i) (straight lam), Option.map_eq_some_iff] at hw
    exact let ⟨π, _, hπ⟩ := hw; ⟨π, hπ⟩

/-- **Littelmann's path-model theorem (component form).** In every compatible realization
`(𝕜, V, f, F)` (`∀ i x, F i (f x) = (P.coroot' i x : 𝕜)`), the realized LS paths of dominant
shape `λ` are precisely the paths reachable from `PLPath.straight 𝕜 (f λ)` by arbitrary sequences
of simple-root lowering and raising steps. -/
theorem mem_range_toPLPath_iff_reflTransGen (f : X →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i x, F i (f x) = (P.coroot' i x : 𝕜)) {p : PLPath 𝕜 V} :
    (p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      Relation.ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) p :=
  ⟨fun hp ↦ let ⟨_, hw⟩ := (mem_range_toPLPath_iff_exists_lowerWord hlam f F hF).mp hp
    PLPath.reflTransGen_rootStep_of_lowerWord_eq_some hw,
    fun h ↦ (isCrystalSet_range_toPLPath hlam f hF).mem_of_reflTransGen_rootStep h
      ⟨straight lam, toPLPath_straight 𝕜 f⟩⟩

section ComponentIso

variable {f : X →+ V} (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
  (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
  (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)

/-- **Littelmann's path-model theorem as a strict crystal isomorphism.** In every injective,
ray-separating, compatible realization `(𝕜, V, f, F)` (`∀ i x, F i (f x) = (P.coroot' i x : 𝕜)`),
`TauCeti.LSPath.crystal` is strictly isomorphic to the connected component of
`PLPath.straight 𝕜 (f λ)` in `TauCeti.PLPath.normalCrystal`. -/
noncomputable def toPLPathComponentIso :
    NormalCrystal.StrictIso (crystal hlam) (PLPath.normalCrystalComponent hf hF
      ⟨PLPath.straight 𝕜 (f lam), isIntegralPath_straight hlam f F hF⟩) where
  toEquiv := Equiv.ofBijective
    (fun π ↦ ⟨toPLPathHom hlam hf hF π,
      (PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff _ _).mpr
        ((mem_range_toPLPath_iff_reflTransGen hlam f F hF).mp
          ⟨π, (toPLPathHom_apply hlam hf hF π).symm⟩)⟩)
    ⟨fun _ _ h ↦ toPLPath_injective hlam hf.injOn hS (congrArg (fun x ↦ x.val.val) h), fun y ↦ by
      obtain ⟨π, hπ⟩ := (mem_range_toPLPath_iff_reflTransGen hlam f F hF).mpr
        ((PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff _ y.val).mp y.property)
      exact ⟨π, Subtype.ext (Subtype.ext hπ)⟩⟩
  wt_toFun π := by
    rw [PLPath.normalCrystalComponent, NormalCrystal.component_eq_restrict,
      NormalCrystal.restrict_wt]
    exact (toPLPathHom hlam hf hF).wt_apply π
  e_toFun i π := by
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_map, Function.comp_def, ← Option.unattach, PLPath.normalCrystalComponent,
      NormalCrystal.component_eq_restrict, NormalCrystal.unattach_restrict_e]
    exact (toPLPathHom hlam hf hF).e_apply i π

@[simp]
theorem toPLPathComponentIso_apply (π : LSPath P b lam) :
    (toPLPathComponentIso hlam hf hF hS π).val = toPLPathHom hlam hf hF π := (rfl)

@[simp]
theorem toPLPathHom_toPLPathComponentIso_symm
    (y : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), isIntegralPath_straight hlam f F hF⟩) :
    toPLPathHom hlam hf hF ((toPLPathComponentIso hlam hf hF hS).symm y) = y.val := by
  simpa only [toPLPathComponentIso_apply] using
    congrArg Subtype.val ((toPLPathComponentIso hlam hf hF hS).apply_symm_apply y)

@[simp]
theorem toPLPath_toPLPathComponentIso_symm
    (y : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), isIntegralPath_straight hlam f F hF⟩) :
    ((toPLPathComponentIso hlam hf hF hS).symm y).toPLPath 𝕜 f = y.val.val := by
  simpa only [toPLPathHom_apply] using
    congrArg Subtype.val (toPLPathHom_toPLPathComponentIso_symm hlam hf hF hS y)

end ComponentIso

end Component

end TauCeti.LSPath
