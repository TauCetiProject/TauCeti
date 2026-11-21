/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.Crystal.Word
public import TauCeti.RepresentationTheory.LSPath.Raise
public import TauCeti.RepresentationTheory.LSPath.Word

import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.Crystal.Highest
import TauCeti.RepresentationTheory.LSPath.Highest
import TauCeti.RepresentationTheory.LSPath.Realization
import TauCeti.RepresentationTheory.LSPath.SimpleRootString
import TauCeti.RepresentationTheory.LSPath.Weight

/-!
# The highest-weight normal crystal `B(λ)` of Lakshmibai–Seshadri paths

For a finite reduced root datum `P : RootDatum ι X Y` with base `b : P.Base` and dominant weight
`λ ∈ dominantChamber P b`, this file equips `LSPath P b λ` with its realization-free normal crystal
structure `TauCeti.LSPath.normalCrystal` via `ℚ ⊗[ℤ] X`, proves compatibility with every
ordered-field simple-coroot realization, shows `straight λ` is the unique highest element
generating the connected crystal graph, and constructs the strict crystal isomorphism
`TauCeti.LSPath.normalCrystalComponentIso` onto the straight-path component `B(λ)`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499–525, §§2, 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

namespace TauCeti.LSPath

section QRealization

open Module RootPairing
open scoped TensorProduct

/-- The canonical additive map `X →+ ℚ ⊗[ℤ] X` into the rational weight space. -/
noncomputable def qHom (X : Type*) [AddCommGroup X] : X →+ ℚ ⊗[ℤ] X :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

theorem qHom_apply (X : Type*) [AddCommGroup X] (x : X) :
    qHom X x = (1 : ℚ) ⊗ₜ[ℤ] x := (rfl)

theorem qHom_injective {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum ι X Y) : Function.Injective (qHom X) :=
  P.tensorProduct_mk_injective ℚ

/-- The rational linear form on `ℚ ⊗[ℤ] X` extending the simple coroot `P.coroot' i`. -/
noncomputable def qForm {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum ι X Y) (b : P.Base) : b.support → Dual ℚ (ℚ ⊗[ℤ] X) :=
  fun i ↦ ((Algebra.linearMap ℤ ℚ).comp (P.coroot' i.val)).liftBaseChange ℚ

theorem qForm_apply {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootDatum ι X Y} {b : P.Base} (i : b.support) (x : X) :
    qForm P b i (qHom X x) = (P.coroot' i x : ℚ) := by
  simp [qHom, qForm]

end QRealization

end TauCeti.LSPath

public section

namespace TauCeti

open Module Relation RootPairing Set
open scoped TensorProduct

namespace LSPath

section NormalCrystal

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

private noncomputable def qEquiv (hlam : lam ∈ dominantChamber P b) :=
  Equiv.ofInjective (fun ρ : LSPath P b lam ↦ ρ.toPLPath ℚ (qHom X))
    (toPLPath_injective_of_coroot' hlam qForm_apply)

private theorem qEquiv_val (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (qEquiv hlam π).val = π.toPLPath ℚ (qHom X) := (rfl)

private theorem qEquiv_symm_toPLPath (hlam : lam ∈ dominantChamber P b)
    (y : range fun ρ : LSPath P b lam ↦ ρ.toPLPath ℚ (qHom X)) :
    ((qEquiv hlam).symm y).toPLPath ℚ (qHom X) = y.val :=
  Equiv.apply_ofInjective_symm (toPLPath_injective_of_coroot' hlam qForm_apply) y

/-- **The canonical normal crystal of Lakshmibai–Seshadri paths of dominant shape `λ`.** -/
noncomputable def normalCrystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (PLPath.normalCrystalOn (qHom_injective P) qForm_apply
      (isCrystalSet_range_toPLPath hlam (qHom X) qForm_apply)).transport (qEquiv hlam).symm

section UniversalRealization

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (hlam : lam ∈ dominantChamber P b)

/-- The image of `(normalCrystal hlam).wt π` under `f` is the endpoint of `π.toPLPath 𝕜 f`. -/
theorem apply_normalCrystal_wt (f : X →+ V) (π : LSPath P b lam) :
    f ((normalCrystal hlam).wt π) = (π.toPLPath 𝕜 f).endpoint := by
  have hwt₀ : qHom X ((normalCrystal hlam).wt π) = (π.toPLPath ℚ (qHom X)).endpoint := by
    rw [normalCrystal, NormalCrystal.transport_wt, Equiv.symm_symm,
      PLPath.apply_normalCrystalOn_wt, qEquiv_val]
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ 𝕜)
  have : IsScalarTower ℤ ℚ V := IsScalarTower.of_algebraMap_smul fun n v ↦ by
    dsimp [Module.compHom]
    simp [Int.cast_smul_eq_zsmul]
  let ψ : ℚ ⊗[ℤ] X →ₗ[ℚ] V := f.toIntLinearMap.liftBaseChange ℚ
  have hψ_f₀ (x : X) : ψ (qHom X x) = f x := by
    rw [qHom_apply, LinearMap.liftBaseChange_tmul, one_smul, AddMonoidHom.coe_toIntLinearMap]
  rw [← hψ_f₀, hwt₀, endpoint_toPLPath, endpoint_toPLPath, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [qHom_apply, Rat.cast_id, map_smul, LinearMap.liftBaseChange_tmul, one_smul,
    AddMonoidHom.coe_toIntLinearMap]
  rfl

/-- The crystal weight of an LS path differs from its final orbit weight by a root-lattice element.
-/
theorem normalCrystal_wt_sub_smul_mem_rootSpan (π : LSPath P b lam) :
    (normalCrystal hlam).wt π - (π.dir (Fin.last _)).val • lam ∈ P.rootSpan ℤ := by
  obtain ⟨m, hm, hend⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ) hlam (qHom X)
  have hwt : (normalCrystal hlam).wt π = (π.dir (Fin.last _)).val • lam + m :=
    (qHom_injective P) ((apply_normalCrystal_wt (𝕜 := ℚ) hlam (qHom X) π).trans hend)
  simpa [hwt] using hm

@[simp]
theorem normalCrystal_wt_straight : (normalCrystal hlam).wt (straight lam) = lam :=
  (qHom_injective P)
    (by simpa [qHom] using apply_normalCrystal_wt (𝕜 := ℚ) hlam (qHom X) (straight lam))

variable {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Normal-crystal raising string length**: `ε_i(π) = -min H_i(π)`. -/
theorem cast_normalCrystal_ε (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).ε i π : 𝕜) = -(π.toPLPath 𝕜 f).minHeight (F i) := by
  have hε₀ : ((normalCrystal hlam).ε i π : ℚ) =
      -(π.toPLPath ℚ (qHom X)).minHeight (qForm P b i) := by
    rw [normalCrystal, NormalCrystal.transport_ε, Equiv.symm_symm,
      PLPath.cast_normalCrystalOn_ε, qEquiv_val]
  obtain ⟨z, hz₀, hz⟩ := π.exists_minHeight_eq_intCast_and_eq_intCast hlam i (qHom X)
    (qForm P b i) (qForm_apply i) f (F i) (hF i)
  have hεz : ((normalCrystal hlam).ε i π : ℤ) = -z :=
    Int.cast_injective (α := ℚ) (by rw [Int.cast_natCast, hε₀, hz₀, Int.cast_neg])
  rw [hz, ← Int.cast_neg, ← hεz, Int.cast_natCast]

/-- **Normal-crystal lowering string length**: `φ_i(π) = H_i(π)(1) - min H_i(π)`. -/
theorem cast_normalCrystal_φ (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).φ i π : 𝕜) =
      F i (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight (F i) := by
  have hcast : (((normalCrystal hlam).φ i π : ℤ) : 𝕜) =
      (P.coroot' i ((normalCrystal hlam).wt π) : 𝕜) + ((normalCrystal hlam).ε i π : 𝕜) := by
    exact_mod_cast sub_eq_iff_eq_add.mp ((normalCrystal hlam).φ_sub_ε i π)
  rw [Int.cast_natCast, ← hF i, apply_normalCrystal_wt (𝕜 := 𝕜) hlam f π,
    cast_normalCrystal_ε hlam hF] at hcast
  linarith

/-- **Raising in any simple-coroot realization agrees with `(normalCrystal hlam).e`.** -/
theorem raise_toPLPath_eq_map_normalCrystal_e
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).e i π).map (fun π' ↦ π'.toPLPath 𝕜 f) := by
  have he₀ : PLPath.raise (qForm P b i) (qHom X (P.root i)) (π.toPLPath ℚ (qHom X)) =
      ((normalCrystal hlam).e i π).map (fun π' ↦ π'.toPLPath ℚ (qHom X)) := by
    rw [← qEquiv_val hlam π, ← PLPath.unattach_normalCrystalOn_e (hf := qHom_injective P)
      (hF := qForm_apply) (hS := isCrystalSet_range_toPLPath hlam (qHom X) qForm_apply) i
      (qEquiv hlam π), normalCrystal, NormalCrystal.transport_e, Equiv.symm_symm,
      Option.unattach, Option.map_map]
    exact Option.map_congr fun y _ ↦ (qEquiv_symm_toPLPath hlam y).symm
  rcases π.raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some hlam i (qHom X) (qForm P b i)
      (qForm_apply i) f (F i) (hF i) with ⟨hnone₀, hnone⟩ | ⟨π', hsome₀, hsome⟩
  · rw [Option.map_eq_none_iff.mp (he₀.symm.trans hnone₀), Option.map_none, hnone]
  · obtain ⟨ρ, hρ, hρeq⟩ := Option.map_eq_some_iff.mp (he₀.symm.trans hsome₀)
    rw [hρ.trans (congrArg some (toPLPath_injective_of_coroot' hlam qForm_apply hρeq)),
      Option.map_some, hsome]

theorem normalCrystal_e_eq_some_iff
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).e i π = some π' ↔
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  rw [raise_toPLPath_eq_map_normalCrystal_e hlam hF, Option.map_eq_some_iff]
  exact ⟨fun h ↦ ⟨π', h, rfl⟩,
    fun ⟨ρ, hρ, heq⟩ ↦ hρ.trans (congrArg some (toPLPath_injective_of_coroot' hlam hF heq))⟩

theorem normalCrystal_e_eq_none_iff
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).e i π = none ↔
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none := by
  rw [raise_toPLPath_eq_map_normalCrystal_e hlam hF, Option.map_eq_none_iff]

theorem normalCrystal_f_eq_some_iff
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).f i π = some π' ↔
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  rw [(normalCrystal hlam).f_eq_some_iff, normalCrystal_e_eq_some_iff hlam hF,
    PLPath.lower_eq_some_iff (PLPath.apply_root_eq_two hF i)]

/-- **Lowering in any simple-coroot realization agrees with `(normalCrystal hlam).f`.** -/
theorem lower_toPLPath_eq_map_normalCrystal_f
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).f i π).map (fun π' ↦ π'.toPLPath 𝕜 f) := by
  rcases hf_opt : (normalCrystal hlam).f i π with _ | π'
  · simp only [Option.map_none]
    refine Option.eq_none_iff_forall_not_mem.mpr fun q hq ↦ ?_
    obtain ⟨ρ, rfl⟩ := π.exists_toPLPath_eq_of_lower_eq_some hlam f i (F i) (hF i) hq
    exact Option.some_ne_none _ (((normalCrystal_f_eq_some_iff hlam hF).mpr hq).symm.trans hf_opt)
  · exact (normalCrystal_f_eq_some_iff hlam hF).mp hf_opt

theorem normalCrystal_f_eq_none_iff
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).f i π = none ↔
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none := by
  rw [lower_toPLPath_eq_map_normalCrystal_f hlam hF, Option.map_eq_none_iff]

/-- Words of raising operators on `LSPath.normalCrystal` agree with `PLPath.raiseWord`. -/
theorem raiseWord_toPLPath_eq_map_normalCrystal_eWord
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    PLPath.raiseWord F (fun i : b.support ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).eWord w π).map (fun π' ↦ π'.toPLPath 𝕜 f) :=
  List.rec (by simp) (fun i _ ih π ↦ by
    rw [PLPath.raiseWord_cons, NormalCrystal.eWord_cons,
      raise_toPLPath_eq_map_normalCrystal_e hlam hF]
    cases (normalCrystal hlam).e i π <;> simp [ih]) w π

/-- Words of lowering operators on `LSPath.normalCrystal` agree with `PLPath.lowerWord`. -/
theorem lowerWord_toPLPath_eq_map_normalCrystal_fWord
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    PLPath.lowerWord F (fun i : b.support ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).fWord w π).map (fun π' ↦ π'.toPLPath 𝕜 f) :=
  List.rec (by simp) (fun i _ ih π ↦ by
    rw [PLPath.lowerWord_cons, NormalCrystal.fWord_cons,
      lower_toPLPath_eq_map_normalCrystal_f hlam hF]
    cases (normalCrystal hlam).f i π <;> simp [ih]) w π

end UniversalRealization

section HighestAndConnected

variable (hlam : lam ∈ dominantChamber P b)

@[simp]
theorem normalCrystal_ε_straight (i : b.support) :
    (normalCrystal hlam).ε i (straight lam) = 0 := by
  have hnonneg : (0 : ℚ) ≤ qForm P b i (qHom X lam) := by
    rw [qForm_apply]; exact_mod_cast (mem_dominantChamber P b lam).mp hlam i.val i.property
  have hε := cast_normalCrystal_ε hlam qForm_apply i (straight lam)
  rw [toPLPath_straight, PLPath.minHeight_straight, min_eq_left hnonneg, neg_zero] at hε
  exact_mod_cast hε

@[simp]
theorem normalCrystal_e_straight (i : b.support) :
    (normalCrystal hlam).e i (straight lam) = none :=
  (normalCrystal hlam).ε_eq_zero_iff.mp (normalCrystal_ε_straight hlam i)

@[simp]
theorem normalCrystal_φ_straight (i : b.support) :
    (normalCrystal hlam).φ i (straight lam) = (P.coroot' i lam).toNat := by
  have hdiff := (normalCrystal hlam).φ_sub_ε i (straight lam)
  rw [normalCrystal_ε_straight, normalCrystal_wt_straight, Nat.cast_zero, sub_zero] at hdiff
  exact Int.ofNat.inj <|
    hdiff.trans (Int.toNat_of_nonneg ((mem_dominantChamber P b lam).mp hlam i.val i.property)).symm

/-- **`straight lam` is the unique highest element of `LSPath.normalCrystal`.** -/
theorem forall_normalCrystal_e_eq_none_iff {π : LSPath P b lam} :
    (∀ i, (normalCrystal hlam).e i π = none) ↔ π = straight lam := by
  have := P.flip_isReduced
  simpa only [normalCrystal_e_eq_none_iff hlam qForm_apply] using
    π.forall_raise_eq_none_iff hlam (qHom X) (qForm P b) qForm_apply

/-- **Every LS path of dominant shape `λ` is obtained from `straight λ` by a lowering word.** -/
theorem exists_fWord_straight_eq_some (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).fWord w (straight lam) = some π := by
  have := LSPath.finite (P := P) (b := b) hlam
  exact (normalCrystal hlam).exists_fWord_eq_some_of_unique_highest
    (fun _ hx ↦ (forall_normalCrystal_e_eq_none_iff hlam).mp hx) π

/-- Every Lakshmibai–Seshadri path of dominant shape `λ` can be raised to `straight λ`. -/
theorem exists_eWord_eq_some_straight (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).eWord w π = some (straight lam) :=
  let ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
  ⟨w.reverse, (normalCrystal hlam).fWord_eq_some_iff.mp hw⟩

/-- **The crystal graph of `LSPath.normalCrystal` is connected.** -/
theorem connected_normalCrystal_graph : (normalCrystal hlam).graph.Connected :=
  (normalCrystal hlam).graph.connected_iff_exists_forall_reachable.mpr ⟨straight lam, fun π ↦
    let ⟨_, hw⟩ := exists_fWord_straight_eq_some hlam π
    (normalCrystal hlam).reachable_of_fWord_eq_some hw⟩

end HighestAndConnected

/-- For a weight `χ` annihilating the simple coroots, `straight χ` is the only LS path. -/
theorem eq_straight_of_forall_coroot_eq_zero {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (π : LSPath P b χ) :
    π = straight χ := by
  have hdom : χ ∈ dominantChamber P b :=
    mem_dominantChamber_of_forall_coroot'_eq_zero P b fun i hi ↦ hχ ⟨i, hi⟩
  obtain ⟨_ | ⟨i, w⟩, hw⟩ := exists_fWord_straight_eq_some hdom π
  · rw [NormalCrystal.fWord_nil] at hw; exact (Option.some.inj hw).symm
  · have hf0 : (normalCrystal hdom).f i (straight χ) = none := (normalCrystal hdom).φ_eq_zero_iff.mp
      (by simp [normalCrystal_φ_straight, RootPairing.coroot', hχ i])
    simp [NormalCrystal.fWord_cons, hf0] at hw

/-- For a central weight `χ`, `LSPath.normalCrystal` is strictly isomorphic to the one-element
central crystal `NormalCrystal.central χ hχ`. -/
noncomputable def centralIso {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      (normalCrystal (mem_dominantChamber_of_forall_coroot'_eq_zero P b fun i hi ↦ hχ ⟨i, hi⟩))
      (NormalCrystal.central χ hχ) where
  toEquiv := ⟨fun _ ↦ PUnit.unit, fun _ ↦ straight χ,
    fun π ↦ (eq_straight_of_forall_coroot_eq_zero hχ π).symm, fun _ ↦ rfl⟩
  wt_toFun π := by rw [eq_straight_of_forall_coroot_eq_zero hχ π]; simp
  e_toFun i π := by rw [eq_straight_of_forall_coroot_eq_zero hχ π]; simp

/-- When `b` has empty support, `straight λ` is the unique LS path of shape `λ`. -/
theorem eq_straight_of_isEmpty [IsEmpty b.support] (π : LSPath P b lam) : π = straight lam :=
  eq_straight_of_forall_coroot_eq_zero (fun i ↦ IsEmpty.elim ‹IsEmpty b.support› i) π

noncomputable instance [IsEmpty b.support] : Unique (LSPath P b lam) where
  default := straight lam
  uniq := eq_straight_of_isEmpty

end NormalCrystal

section ComponentEquivalence

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Equivalence of the `a`-chain LS encoding with lowering-word generation from `straight λ`.** -/
theorem range_toPLPath_eq_setOf_exists_lowerWord_straight (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) =
      {q | ∃ w : List b.support,
        PLPath.lowerWord F (fun i : b.support ↦ f (P.root i)) w
          (PLPath.straight 𝕜 (f lam)) = some q} := by
  ext q
  simp only [mem_range, mem_ofPred_eq, ← toPLPath_straight (P := P) (b := b) (lam := lam) 𝕜 f,
    lowerWord_toPLPath_eq_map_normalCrystal_fWord hlam hF, Option.map_eq_some_iff]
  exact ⟨fun ⟨π, hπ⟩ ↦ let ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π; ⟨w, π, hw, hπ⟩,
    fun ⟨_, π, _, hπ⟩ ↦ ⟨π, hπ⟩⟩

/-- Realized LS paths of dominant shape `λ` are precisely those reachable from `straight` by
finite sequences of simple-root steps. -/
theorem range_toPLPath_eq_setOf_reflTransGen_rootStep_straight (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) =
      {q | ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) q} := by
  ext q; refine ⟨fun hq ↦ ?_, fun hw ↦
    (isCrystalSet_range_toPLPath hlam f hF).mem_of_reflTransGen_rootStep
      hw ⟨straight lam, toPLPath_straight (lam := lam) 𝕜 f⟩⟩
  rw [range_toPLPath_eq_setOf_exists_lowerWord_straight hlam hF] at hq
  exact let ⟨_, hw⟩ := hq; PLPath.reflTransGen_rootStep_of_lowerWord_eq_some hw

variable (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
  (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))

/-- When `f` is injective, `toPLPath` induces a strict crystal isomorphism onto
`PLPath.normalCrystalOn` of the realized LS paths. -/
noncomputable def toPLPathCrystalIso :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalOn hf hF (isCrystalSet_range_toPLPath hlam f hF)) where
  toEquiv := Equiv.ofInjective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (toPLPath_injective_of_coroot' (𝕜 := 𝕜) hlam hF)
  wt_toFun π := hf <| by
    rw [PLPath.apply_normalCrystalOn_wt, apply_normalCrystal_wt (𝕜 := 𝕜) hlam f π]; rfl
  e_toFun i π := PLPath.normalCrystalOn_e_eq_map_iff.mpr
    (raise_toPLPath_eq_map_normalCrystal_e hlam hF i π)

@[simp]
theorem toPLPathCrystalIso_apply (π : LSPath P b lam) :
    (toPLPathCrystalIso hlam hf hF π).val = π.toPLPath 𝕜 f := (rfl)

/-- Strict crystal embedding of `LSPath.normalCrystal` into `PLPath.normalCrystal`. -/
noncomputable def toPLPathCrystalHom :
    NormalCrystal.StrictHom (normalCrystal hlam) (PLPath.normalCrystal hf hF) :=
  (PLPath.embedHom (isCrystalSet_range_toPLPath hlam f hF)).comp
    (toPLPathCrystalIso hlam hf hF).toStrictHom

@[simp]
theorem toPLPathCrystalHom_apply (π : LSPath P b lam) :
    (toPLPathCrystalHom hlam hf hF π).val = π.toPLPath 𝕜 f := by simp [toPLPathCrystalHom]

/-- Membership in the connected crystal component of `PLPath.straight 𝕜 (f λ)` inside
`PLPath.normalCrystal` is equivalent to being the realization of an LS path of shape `λ`. -/
theorem mem_supp_connectedComponentMk_straight_iff
    (x : {q : PLPath 𝕜 V | PLPath.IsIntegralPath b f F q}) :
    x ∈ ((PLPath.normalCrystal hf hF).graph.connectedComponentMk
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).supp ↔
      x.val ∈ range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
  rw [PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff,
    range_toPLPath_eq_setOf_reflTransGen_rootStep_straight hlam hF, mem_ofPred_eq]

private noncomputable def normalCrystalComponentHom :
    NormalCrystal.StrictHom (normalCrystal hlam)
      (PLPath.normalCrystalComponent hf hF
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) where
  toFun π := ⟨toPLPathCrystalHom hlam hf hF π,
    (mem_supp_connectedComponentMk_straight_iff hlam hf hF _).mpr
      ⟨π, (toPLPathCrystalHom_apply hlam hf hF π).symm⟩⟩
  wt_toFun π := by
    have h := ((PLPath.normalCrystal hf hF).componentHom _).wt_apply
      ⟨toPLPathCrystalHom hlam hf hF π,
        (mem_supp_connectedComponentMk_straight_iff hlam hf hF _).mpr
          ⟨π, (toPLPathCrystalHom_apply hlam hf hF π).symm⟩⟩
    rw [NormalCrystal.componentHom_apply] at h
    exact h.symm.trans ((toPLPathCrystalHom hlam hf hF).wt_apply π)
  e_toFun i π := by
    have hcomp : ⇑((PLPath.normalCrystal hf hF).componentHom
        ((PLPath.normalCrystal hf hF).graph.connectedComponentMk
          ⟨PLPath.straight 𝕜 (f lam),
            PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩)) = Subtype.val :=
      funext ((PLPath.normalCrystal hf hF).componentHom_apply _)
    apply Option.map_injective Subtype.val_injective
    rw [← hcomp, ← ((PLPath.normalCrystal hf hF).componentHom _).e_apply i
      ⟨toPLPathCrystalHom hlam hf hF π,
        (mem_supp_connectedComponentMk_straight_iff hlam hf hF _).mpr
          ⟨π, (toPLPathCrystalHom_apply hlam hf hF π).symm⟩⟩,
      NormalCrystal.componentHom_apply, (toPLPathCrystalHom hlam hf hF).e_apply i π,
      Option.map_map, hcomp]; rfl

private theorem normalCrystalComponentHom_bijective :
    Function.Bijective (normalCrystalComponentHom hlam hf hF) :=
  ⟨fun _ _ h ↦ toPLPath_injective_of_coroot' (𝕜 := 𝕜) hlam hF <| by
    have h' : (toPLPathCrystalHom hlam hf hF _).val = (toPLPathCrystalHom hlam hf hF _).val :=
      congrArg (fun z ↦ z.val.val) h
    rwa [toPLPathCrystalHom_apply, toPLPathCrystalHom_apply] at h',
   fun y ↦
    let ⟨π, hπ⟩ := (mem_supp_connectedComponentMk_straight_iff hlam hf hF y.val).mp y.property
    ⟨π, Subtype.ext (Subtype.ext ((toPLPathCrystalHom_apply hlam hf hF π).trans hπ))⟩⟩

/-- **Main crystal isomorphism `LSPath P b λ ≃ B(λ)`** onto the straight-path component. -/
noncomputable def normalCrystalComponentIso :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalComponent hf hF
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :=
  NormalCrystal.StrictIso.ofBijective (normalCrystalComponentHom hlam hf hF)
    (normalCrystalComponentHom_bijective hlam hf hF)

@[simp]
theorem normalCrystalComponentIso_apply (π : LSPath P b lam) :
    (normalCrystalComponentIso hlam hf hF π).val.val = π.toPLPath 𝕜 f := by
  rw [normalCrystalComponentIso, congrFun (NormalCrystal.StrictIso.coe_ofBijective _ _) π]
  exact toPLPathCrystalHom_apply hlam hf hF π

@[simp]
theorem normalCrystalComponentIso_straight :
    (normalCrystalComponentIso hlam hf hF (straight lam)).val =
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩ :=
  Subtype.ext (by rw [normalCrystalComponentIso_apply, toPLPath_straight])

@[simp]
theorem toPLPath_normalCrystalComponentIso_symm
    (y : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    ((normalCrystalComponentIso hlam hf hF).symm y).toPLPath 𝕜 f = y.val.val := by
  have h := congrArg (fun z ↦ z.val.val) ((normalCrystalComponentIso hlam hf hF).apply_symm_apply y)
  rwa [normalCrystalComponentIso_apply] at h

end ComponentEquivalence

end LSPath

end TauCeti
