/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.Crystal.Word
public import TauCeti.RepresentationTheory.LSPath.Basic
public import TauCeti.RepresentationTheory.LSPath.Crystal.Basic
public import TauCeti.RepresentationTheory.LSPath.Word

import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.Crystal.Highest
import TauCeti.RepresentationTheory.LSPath.Highest
import TauCeti.RepresentationTheory.LSPath.Lower
import TauCeti.RepresentationTheory.LSPath.PartialInverse
import TauCeti.RepresentationTheory.LSPath.Raise
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

public section

namespace TauCeti

open Module Relation RootPairing Set
open scoped TensorProduct

section CrystalAdmissibility

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Realized Lakshmibai–Seshadri paths of dominant shape form a crystal-admissible set.** -/
theorem LSPath.isCrystalSet_range_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsCrystalSet b f F (range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :=
  { endpoint_mem_range := by
      rintro _ ⟨π, rfl⟩; obtain ⟨_, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) hlam f
      exact ⟨_, hm.symm⟩
    exists_minHeight_eq_intCast := by
      rintro _ ⟨π, rfl⟩ i; exact π.exists_minHeight_eq_intCast hlam f i (F i) (hF i)
    mem_of_raise_eq_some := by
      rintro i _ _ hq ⟨π, rfl⟩; exact π.exists_toPLPath_eq_of_raise_eq_some hlam f i (F i) (hF i) hq
    mem_of_lower_eq_some := by
      rintro i _ _ hq ⟨π, rfl⟩
      exact π.exists_toPLPath_eq_of_lower_eq_some hlam f i (F i) (hF i) hq }

/-- Every realized Lakshmibai–Seshadri path of dominant shape is an integral path. -/
theorem LSPath.isIntegralPath_toPLPath (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (π.toPLPath 𝕜 f) :=
  (LSPath.isCrystalSet_range_toPLPath hlam hF).subset_isIntegralPath ⟨π, rfl⟩

/-- **Every straight path along a dominant weight is an integral path.** -/
theorem PLPath.isIntegralPath_straight_of_mem_dominantChamber (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (PLPath.straight 𝕜 (f lam)) :=
  LSPath.toPLPath_straight (P := P) (b := b) (lam := lam) 𝕜 f ▸
    (LSPath.straight lam).isIntegralPath_toPLPath hlam hF

end CrystalAdmissibility

namespace LSPath

section NormalCrystal

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

private noncomputable def qHom (X : Type*) [AddCommGroup X] : X →+ ℚ ⊗[ℤ] X :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

private noncomputable def qForm (P : RootDatum ι X Y) (b : P.Base) :
    b.support → Dual ℚ (ℚ ⊗[ℤ] X) :=
  fun i ↦ ((Algebra.linearMap ℤ ℚ).comp (P.coroot' i.1)).liftBaseChange ℚ

omit [Finite ι] [P.IsReduced] in
private theorem qForm_apply (i : b.support) (x : X) :
    qForm P b i (qHom X x) = (P.coroot' i x : ℚ) := by simp [qHom, qForm]

private noncomputable def qEquiv (hlam : lam ∈ dominantChamber P b) :=
  Equiv.ofInjective (fun ρ : LSPath P b lam ↦ ρ.toPLPath ℚ (qHom X))
    (toPLPath_injective_of_coroot' hlam qForm_apply)

/-- **The canonical normal crystal of Lakshmibai–Seshadri paths of dominant shape `λ`.** -/
noncomputable def normalCrystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (PLPath.normalCrystalOn (P.tensorProduct_mk_injective ℚ) qForm_apply
      (isCrystalSet_range_toPLPath hlam qForm_apply)).transport (qEquiv hlam).symm

section UniversalRealization

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (hlam : lam ∈ dominantChamber P b)

/-- The image of `(normalCrystal hlam).wt π` under `f` is the endpoint of `π.toPLPath 𝕜 f`. -/
theorem apply_normalCrystal_wt (f : X →+ V) (π : LSPath P b lam) :
    f ((normalCrystal hlam).wt π) = (π.toPLPath 𝕜 f).endpoint := by
  have hwt₀ : qHom X ((normalCrystal hlam).wt π) = (π.toPLPath ℚ (qHom X)).endpoint := by
    simpa [normalCrystal, qEquiv] using PLPath.apply_normalCrystalOn_wt
      (hf := P.tensorProduct_mk_injective ℚ) (hF := qForm_apply)
      (hS := isCrystalSet_range_toPLPath hlam qForm_apply) (qEquiv hlam π)
  let B : ℚ →ₗ[ℤ] X →ₗ[ℤ] V := LinearMap.mk₂' ℤ ℤ (fun q x ↦ (q : 𝕜) • f x)
    (fun _ _ _ ↦ by push_cast; exact add_smul _ _ _)
    (fun _ _ _ ↦ by simp [mul_smul, Int.cast_smul_eq_zsmul])
    (fun _ _ _ ↦ by rw [map_add, smul_add]) (fun _ _ _ ↦ by rw [map_zsmul, smul_comm])
  let ψ : ℚ ⊗[ℤ] X →ₗ[ℤ] V := TensorProduct.lift B
  have hψ_f₀ (x : X) : ψ (qHom X x) = f x :=
    (TensorProduct.lift.tmul (f' := B) (1 : ℚ) x).trans (by simp [B])
  rw [← hψ_f₀, hwt₀, endpoint_toPLPath, endpoint_toPLPath, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change ψ ((π.duration j) • ((1 : ℚ) ⊗ₜ[ℤ] ((π.dir j).1 • lam))) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact TensorProduct.lift.tmul (f' := B) (π.duration j) ((π.dir j).1 • lam)

/-- The crystal weight of an LS path differs from its final orbit weight by a root-lattice element.
-/
theorem normalCrystal_wt_sub_smul_mem_rootSpan (π : LSPath P b lam) :
    (normalCrystal hlam).wt π - (π.dir (Fin.last _)).1 • lam ∈ P.rootSpan ℤ := by
  obtain ⟨m, hm, hend⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ) hlam (qHom X)
  have hwt : (normalCrystal hlam).wt π = (π.dir (Fin.last _)).1 • lam + m :=
    (P.tensorProduct_mk_injective ℚ) ((apply_normalCrystal_wt (𝕜 := ℚ) hlam (qHom X) π).trans hend)
  simpa [hwt] using hm

@[simp]
theorem normalCrystal_wt_straight : (normalCrystal hlam).wt (straight lam) = lam :=
  (P.tensorProduct_mk_injective ℚ)
    (by simpa [qHom] using apply_normalCrystal_wt (𝕜 := ℚ) hlam (qHom X) (straight lam))

variable {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Normal-crystal raising string length**: `ε_i(π) = -min H_i(π)`. -/
theorem cast_normalCrystal_ε (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).ε i π : 𝕜) = -(π.toPLPath 𝕜 f).minHeight (F i) := by
  have hε₀ : ((normalCrystal hlam).ε i π : ℚ) =
      -(π.toPLPath ℚ (qHom X)).minHeight (qForm P b i) := by
    simpa [normalCrystal, qEquiv] using PLPath.cast_normalCrystalOn_ε
      (hf := P.tensorProduct_mk_injective ℚ) (hF := qForm_apply)
      (hS := isCrystalSet_range_toPLPath hlam qForm_apply) i (qEquiv hlam π)
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
  have hq : π.toPLPath ℚ (qHom X) = (qEquiv hlam π).1 := by simp [qEquiv]
  have he₀ : PLPath.raise (qForm P b i) (qHom X (P.root i)) (π.toPLPath ℚ (qHom X)) =
      ((normalCrystal hlam).e i π).map (fun π' ↦ π'.toPLPath ℚ (qHom X)) := by
    rw [hq, ← PLPath.unattach_normalCrystalOn_e (hf := P.tensorProduct_mk_injective ℚ)
      (hF := qForm_apply) (hS := isCrystalSet_range_toPLPath hlam qForm_apply) i (qEquiv hlam π)]
    simp only [normalCrystal, NormalCrystal.transport_e, Equiv.symm_symm, Option.map_map,
      Option.unattach, qEquiv]
    exact Option.map_congr fun y _ ↦ (Equiv.apply_ofInjective_symm _ y).symm
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
    rw [qForm_apply]; exact_mod_cast (mem_dominantChamber P b lam).mp hlam i.1 i.2
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
  exact Int.ofNat.inj
    (hdiff.trans (Int.toNat_of_nonneg ((mem_dominantChamber P b lam).mp hlam i.1 i.2)).symm)

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
theorem connected_normalCrystal_graph : (normalCrystal hlam).graph.Connected := by
  refine (normalCrystal hlam).graph.connected_iff_exists_forall_reachable.mpr ⟨straight lam, ?_⟩
  have hreach {w} : ∀ {x y}, (normalCrystal hlam).fWord w x = some y →
      (normalCrystal hlam).graph.Reachable x y := by
    induction w with
    | nil => intro _ _ h; rw [NormalCrystal.fWord_nil] at h; exact Option.some.inj h ▸ .rfl
    | cons i w ih =>
      intro x _ h; obtain ⟨_, hz, hy⟩ :=
        Option.bind_eq_some_iff.mp ((normalCrystal hlam).fWord_cons i w x ▸ h)
      exact ((normalCrystal hlam).graph_adj_of_f_eq_some hz).reachable.trans (ih hy)
  exact fun π ↦ let ⟨_, hw⟩ := exists_fWord_straight_eq_some hlam π; hreach hw

end HighestAndConnected

omit [Finite ι] [P.IsReduced] in
/-- Every weight annihilating the simple coroots lies in the dominant chamber. -/
theorem mem_dominantChamber_of_forall_coroot_eq_zero {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    χ ∈ dominantChamber P b :=
  (mem_dominantChamber P b χ).mpr fun i hi ↦ by simpa [RootPairing.coroot'] using (hχ ⟨i, hi⟩).ge

/-- For a weight `χ` annihilating the simple coroots, `straight χ` is the only LS path. -/
theorem eq_straight_of_forall_coroot_eq_zero {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (π : LSPath P b χ) :
    π = straight χ := by
  have hdom := mem_dominantChamber_of_forall_coroot_eq_zero hχ
  obtain ⟨_ | ⟨i, w⟩, hw⟩ := exists_fWord_straight_eq_some hdom π
  · rw [NormalCrystal.fWord_nil] at hw; exact (Option.some.inj hw).symm
  · have hf0 : (normalCrystal hdom).f i (straight χ) = none := (normalCrystal hdom).φ_eq_zero_iff.mp
      (by simp [normalCrystal_φ_straight, RootPairing.coroot', hχ i])
    simp [NormalCrystal.fWord_cons, hf0] at hw

/-- For a central weight `χ`, `LSPath.normalCrystal` is strictly isomorphic to the one-element
central crystal `NormalCrystal.central χ hχ`. -/
noncomputable def centralIso {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictIso (normalCrystal (mem_dominantChamber_of_forall_coroot_eq_zero hχ))
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
  have hwalk {w} : ∀ {p r : PLPath 𝕜 V},
      PLPath.lowerWord F (fun i : b.support ↦ f (P.root i)) w p = some r →
        ReflTransGen (PLPath.RootStep b f F) p r := by
    induction w with
    | nil => intro _ _ h; rw [PLPath.lowerWord_nil] at h; exact Option.some.inj h ▸ .refl
    | cons i w ih =>
      intro p _ h; obtain ⟨_, hs, hr⟩ :=
        Option.bind_eq_some_iff.mp (PLPath.lowerWord_cons i w p ▸ h)
      exact .head (.of_lower_eq_some hs) (ih hr)
  ext q; refine ⟨fun hq ↦ ?_, fun hw ↦
    (isCrystalSet_range_toPLPath hlam hF).mem_of_reflTransGen_rootStep
      hw ⟨straight lam, toPLPath_straight (lam := lam) 𝕜 f⟩⟩
  rw [range_toPLPath_eq_setOf_exists_lowerWord_straight hlam hF] at hq
  exact let ⟨_, hw⟩ := hq; hwalk hw

variable (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
  (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))

/-- When `f` is injective, `toPLPath` induces a strict crystal isomorphism onto
`PLPath.normalCrystalOn` of the realized LS paths. -/
noncomputable def toPLPathCrystalIso :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalOn hf hF (isCrystalSet_range_toPLPath hlam hF)) where
  toEquiv := Equiv.ofInjective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (toPLPath_injective_of_coroot' (𝕜 := 𝕜) hlam hF)
  wt_toFun π := hf <| by
    rw [PLPath.apply_normalCrystalOn_wt, apply_normalCrystal_wt (𝕜 := 𝕜) hlam f π]; rfl
  e_toFun i π := PLPath.normalCrystalOn_e_eq_map_iff.mpr
    (raise_toPLPath_eq_map_normalCrystal_e hlam hF i π)

@[simp]
theorem toPLPathCrystalIso_apply (π : LSPath P b lam) :
    (toPLPathCrystalIso hlam hf hF π).1 = π.toPLPath 𝕜 f := (rfl)

/-- Strict crystal embedding of `LSPath.normalCrystal` into `PLPath.normalCrystal`. -/
noncomputable def toPLPathCrystalHom :
    NormalCrystal.StrictHom (normalCrystal hlam) (PLPath.normalCrystal hf hF) :=
  (PLPath.embedHom (isCrystalSet_range_toPLPath hlam hF)).comp
    (toPLPathCrystalIso hlam hf hF).toStrictHom

@[simp]
theorem toPLPathCrystalHom_apply (π : LSPath P b lam) :
    (toPLPathCrystalHom hlam hf hF π).1 = π.toPLPath 𝕜 f := by simp [toPLPathCrystalHom]

/-- Membership in the connected crystal component of `PLPath.straight 𝕜 (f λ)` inside
`PLPath.normalCrystal` is equivalent to being the realization of an LS path of shape `λ`. -/
theorem mem_supp_connectedComponentMk_straight_iff
    (x : {q : PLPath 𝕜 V | PLPath.IsIntegralPath b f F q}) :
    x ∈ ((PLPath.normalCrystal hf hF).graph.connectedComponentMk
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).supp ↔
      x.1 ∈ range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
  rw [PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff,
    range_toPLPath_eq_setOf_reflTransGen_rootStep_straight hlam hF, mem_ofPred_eq]

/-- **Main crystal isomorphism `LSPath P b λ ≃ B(λ)`** onto the straight-path component. -/
noncomputable def normalCrystalComponentIso :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalComponent hf hF
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :=
  let C := (PLPath.normalCrystal hf hF).graph.connectedComponentMk
    ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩
  let mkElem (π : LSPath P b lam) : C := ⟨toPLPathCrystalHom hlam hf hF π,
    (mem_supp_connectedComponentMk_straight_iff hlam hf hF _).mpr
      ⟨π, (toPLPathCrystalHom_apply hlam hf hF π).symm⟩⟩
  NormalCrystal.StrictIso.ofBijective
    { toFun := mkElem
      wt_toFun π := by
        have h := ((PLPath.normalCrystal hf hF).componentHom C).wt_apply (mkElem π)
        rw [NormalCrystal.componentHom_apply] at h
        exact h.symm.trans ((toPLPathCrystalHom hlam hf hF).wt_apply π)
      e_toFun i π := by
        have hcomp : ⇑((PLPath.normalCrystal hf hF).componentHom C) = Subtype.val :=
          funext ((PLPath.normalCrystal hf hF).componentHom_apply C)
        apply Option.map_injective Subtype.val_injective
        rw [← hcomp, ← ((PLPath.normalCrystal hf hF).componentHom C).e_apply i (mkElem π),
          NormalCrystal.componentHom_apply, (toPLPathCrystalHom hlam hf hF).e_apply i π,
          Option.map_map, hcomp]; rfl }
    (show Function.Bijective _ from
      ⟨fun _ _ h ↦ toPLPath_injective_of_coroot' (𝕜 := 𝕜) hlam hF <| by
        have h' : (toPLPathCrystalHom hlam hf hF _).1 = (toPLPathCrystalHom hlam hf hF _).1 :=
          congrArg (fun z ↦ z.1.1) h
        rwa [toPLPathCrystalHom_apply, toPLPathCrystalHom_apply] at h',
       fun y ↦ let ⟨π, hπ⟩ := (mem_supp_connectedComponentMk_straight_iff hlam hf hF y.1).mp y.2
        ⟨π, Subtype.ext (Subtype.ext ((toPLPathCrystalHom_apply hlam hf hF π).trans hπ))⟩⟩)

@[simp]
theorem normalCrystalComponentIso_apply (π : LSPath P b lam) :
    (normalCrystalComponentIso hlam hf hF π).1.1 = π.toPLPath 𝕜 f := by
  dsimp only [normalCrystalComponentIso]
  rw [congrFun (NormalCrystal.StrictIso.coe_ofBijective _ _) π]
  exact toPLPathCrystalHom_apply hlam hf hF π

@[simp]
theorem normalCrystalComponentIso_straight :
    (normalCrystalComponentIso hlam hf hF (straight lam)).1 =
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩ :=
  Subtype.ext (by rw [normalCrystalComponentIso_apply, toPLPath_straight])

@[simp]
theorem toPLPath_normalCrystalComponentIso_symm
    (y : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    ((normalCrystalComponentIso hlam hf hF).symm y).toPLPath 𝕜 f = y.1.1 := by
  have h := congrArg (fun z ↦ z.1.1) ((normalCrystalComponentIso hlam hf hF).apply_symm_apply y)
  rwa [normalCrystalComponentIso_apply] at h

end ComponentEquivalence

end LSPath

end TauCeti
