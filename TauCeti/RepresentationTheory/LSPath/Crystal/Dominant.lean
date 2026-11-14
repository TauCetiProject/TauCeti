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

import Mathlib.LinearAlgebra.TensorProduct.Lift
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.Crystal.Highest
import TauCeti.RepresentationTheory.LSPath.Highest
import TauCeti.RepresentationTheory.LSPath.Lower
import TauCeti.RepresentationTheory.LSPath.Raise
import TauCeti.RepresentationTheory.LSPath.Realization
import TauCeti.RepresentationTheory.LSPath.Weight

/-!
# Littelmann's normal crystal `B(λ)` of Lakshmibai–Seshadri paths

Let `P : RootDatum ι X Y` be a finite reduced root datum with base `b`, and let `λ ∈ X` lie in the
dominant chamber of `b`. Combining:
* lattice-valued endpoints (`TauCeti.LSPath.exists_mem_rootSpan_endpoint_eq_add`),
* realization-independent integral minimum simple-coroot heights
  (`TauCeti.LSPath.exists_intCast_minHeight_eq_and_minHeight_eq`),
* closure of Lakshmibai–Seshadri paths under Littelmann's raising and lowering operators uniformly
  across realizations (`TauCeti.LSPath.exists_raise_toPLPath_eq_some_and_eq_some`,
  `TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`),
* faithful realization in any injective coroot-compatible vector space
  (`TauCeti.LSPath.toPLPath_injective_of_coroot'`),
* finiteness (`TauCeti.LSPath.finite`) and uniqueness of the highest path `straight λ`
  (`TauCeti.LSPath.forall_raise_eq_none_iff`),

this file constructs the canonical **realization-free normal crystal**
`TauCeti.LSPath.normalCrystal hlam : NormalCrystal P b (LSPath P b lam)` directly on the type of
Lakshmibai–Seshadri paths of shape `λ`, without assuming that `Y` is free or finitely generated or
that the roots span `X`.

Every coroot-compatible realization `(𝕜, V, f, F)` (even when `f : X →+ V` is not injective)
commutes with the weight map, string lengths, and partial raising and lowering operators of
`normalCrystal hlam`, and realizes `Set.range (·.toPLPath 𝕜 f)` as both the set of paths lowered
from `PLPath.straight 𝕜 (f lam)` by words of simple roots and the connected root-step component of
`PLPath.straight 𝕜 (f lam)`. When `f` is injective, `toPLPath 𝕜 f` induces strict crystal
isomorphisms onto `PLPath.normalCrystalOn` on `Set.range (·.toPLPath 𝕜 f)` (`toPLPathIso`) and onto
Littelmann's connected path crystal component `PLPath.normalCrystalComponent` of the dominant
straight path (`toComponentIso`).

## Main definitions

* `TauCeti.LSPath.normalCrystal`: the canonical normal crystal `B(λ)` on `LSPath P b lam` for
  dominant `λ`.
* `TauCeti.LSPath.centralShapeIso`: when `λ` annihilates all simple coroots (including `λ = 0` and
  empty root systems), `normalCrystal` is strictly isomorphic to `NormalCrystal.central λ`.
* `TauCeti.LSPath.toPLPathIso`: strict crystal isomorphism from `normalCrystal hlam` onto
  `PLPath.normalCrystalOn` on `Set.range (·.toPLPath 𝕜 f)` for any injective coroot-compatible
  realization `(f, F)`.
* `TauCeti.LSPath.toComponentIso`: strict crystal isomorphism from `normalCrystal hlam` onto the
  connected component of `PLPath.straight 𝕜 (f lam)` in `PLPath.normalCrystal hf hF`.

## Main results

* `TauCeti.LSPath.isCrystalSet_range_toPLPath`, `TauCeti.LSPath.isIntegralPath_toPLPath`: the
  realized LS paths of dominant shape form a crystal-admissible set of integral paths.
* `TauCeti.LSPath.endpoint_toPLPath_eq_apply_wt`, `TauCeti.LSPath.cast_normalCrystal_ε`,
  `TauCeti.LSPath.cast_normalCrystal_φ`, `TauCeti.LSPath.raise_toPLPath`,
  `TauCeti.LSPath.lower_toPLPath`: universal compatibility of `normalCrystal` with any realization.
* `TauCeti.LSPath.forall_normalCrystal_e_eq_none_iff`,
  `TauCeti.LSPath.exists_fWord_straight_eq_some`, `TauCeti.LSPath.connected_normalCrystal_graph`:
  `straight λ` is the unique highest element of `B(λ)`, generates `B(λ)` by lowering words, and
  `B(λ)` has connected crystal graph.
* `TauCeti.LSPath.range_toPLPath_eq_setOf_exists_lowerWord`,
  `TauCeti.LSPath.range_toPLPath_eq_setOf_reflTransGen_rootStep`: equality of the realized LS path
  set with the paths lowered from `PLPath.straight 𝕜 (f lam)` and with its connected root-step
  component.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent. Math.
  116 (1994), §§2–4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§2, 4.
-/

public section

namespace TauCeti.LSPath

open Module Relation RootPairing Set
open scoped TensorProduct

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

/-! ### Crystal-admissibility and integrality of realized LS paths -/

section Admissible

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- In any coroot-compatible realization `(f, F)` (injective or not), the realized
Lakshmibai–Seshadri paths of a dominant shape `λ` form a crystal-admissible set of piecewise-linear
paths. -/
theorem isCrystalSet_range_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsCrystalSet b f F (range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
  have := P.flip_isReduced
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨π, rfl⟩
    obtain ⟨m, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) hlam f
    exact ⟨_, hm.symm⟩
  · rintro _ ⟨π, rfl⟩ i
    exact π.exists_minHeight_eq_intCast hlam f i (F i) (hF i)
  · rintro i _ π' hr ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_raise_eq_some hlam f i (F i) (hF i) hr
  · rintro i _ π' hl ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_lower_eq_some hlam f i (F i) (hF i) hl

/-- Every realized Lakshmibai–Seshadri path of dominant shape is an integral path. -/
theorem isIntegralPath_toPLPath (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (π.toPLPath 𝕜 f) :=
  (isCrystalSet_range_toPLPath hlam hF).subset_isIntegralPath ⟨π, rfl⟩

/-- The straight path along a dominant weight is an integral path. -/
theorem isIntegralPath_straight_of_mem_dominantChamber (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (PLPath.straight 𝕜 (f lam)) := by
  rw [← toPLPath_straight (P := P) (b := b) 𝕜 f]
  exact (straight (P := P) (b := b) lam).isIntegralPath_toPLPath hlam hF

end Admissible

/-! ### Reference realization in `ℚ ⊗[ℤ] X` and the canonical crystal `B(λ)` -/

section Reference

omit [Finite ι] [P.IsReduced] in
private noncomputable def refHom (X : Type*) [AddCommGroup X] : X →+ (ℚ ⊗[ℤ] X) :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

omit [Finite ι] [P.IsReduced] in
private theorem refHom_injective (P : RootDatum ι X Y) : Function.Injective (refHom X) :=
  P.tensorProduct_mk_injective ℚ

omit [Finite ι] [P.IsReduced] in
private noncomputable def refForm (b : P.Base) (i : b.support) : Dual ℚ (ℚ ⊗[ℤ] X) :=
  LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ).comp (P.coroot' i))

omit [Finite ι] [P.IsReduced] in
private theorem refForm_refHom (b : P.Base) (i : b.support) (x : X) :
    refForm b i (refHom X x) = (P.coroot' i x : ℚ) := by
  simp [refForm, refHom]

private theorem toPLPath_refHom_injective (hlam : lam ∈ dominantChamber P b) :
    Function.Injective (fun π : LSPath P b lam ↦ π.toPLPath ℚ (refHom X)) := by
  have := P.flip_isReduced
  exact toPLPath_injective_of_coroot' hlam (refHom_injective P).injOn (refForm_refHom b)

private noncomputable def refEquiv (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ range (fun π : LSPath P b lam ↦ π.toPLPath ℚ (refHom X)) :=
  Equiv.ofInjective _ (toPLPath_refHom_injective hlam)

/-- **Littelmann's normal crystal `B(λ)` of Lakshmibai–Seshadri paths** of dominant shape `λ`.
Its weight map, raising and lowering operators, and string lengths are canonical and independent of
any choice of ambient vector space realization. -/
noncomputable def normalCrystal (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (PLPath.normalCrystalOn (refHom_injective P) (refForm_refHom b)
    (isCrystalSet_range_toPLPath hlam (refForm_refHom b))).transport (refEquiv hlam).symm

end Reference

/-! ### Universal compatibility with realizations -/

section Compatibility

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

omit [Finite ι] [P.IsReduced] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private noncomputable def evalTensor [CharZero 𝕜] (f : X →+ V) : (ℚ ⊗[ℤ] X) →+ V :=
  let g : ℚ → X →ₗ[ℤ] V := fun q ↦
    { toFun x := (q : 𝕜) • f x
      map_add' x y := by rw [map_add, smul_add]
      map_smul' n x := by
        dsimp only [RingHom.id_apply]
        rw [f.map_zsmul, smul_comm] }
  let B : ℚ →ₗ[ℤ] X →ₗ[ℤ] V :=
    { toFun := g
      map_add' p q := LinearMap.ext fun x ↦ by
        dsimp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [Rat.cast_add, add_smul]
      map_smul' n q := LinearMap.ext fun x ↦ by
        dsimp only [g, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
        rw [zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul, Int.cast_smul_eq_zsmul] }
  (TensorProduct.lift B).toAddMonoidHom

omit [Finite ι] [P.IsReduced] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem evalTensor_refHom [CharZero 𝕜] (f : X →+ V) (x : X) :
    evalTensor (𝕜 := 𝕜) f (refHom X x) = f x := by
  simp [evalTensor, refHom]

omit [Finite ι] [P.IsReduced] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem evalTensor_smul_refHom [CharZero 𝕜] (f : X →+ V) (q : ℚ) (x : X) :
    evalTensor (𝕜 := 𝕜) f (q • refHom X x) = (q : 𝕜) • f x := by
  change evalTensor (𝕜 := 𝕜) f (q • (1 ⊗ₜ[ℤ] x)) = (q : 𝕜) • f x
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [evalTensor]

/-- In any realization `f : X →+ V`, the endpoint of `π.toPLPath 𝕜 f` is the image of the crystal
weight `(normalCrystal hlam).wt π`. Neither injectivity of `f` nor coroot height forms on `V` are
needed. -/
theorem endpoint_toPLPath_eq_apply_wt (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam)
    (f : X →+ V) :
    (π.toPLPath 𝕜 f).endpoint = f ((normalCrystal hlam).wt π) := by
  have href : refHom X ((normalCrystal hlam).wt π) = (π.toPLPath ℚ (refHom X)).endpoint := by
    simp [normalCrystal, refEquiv]
  have heval := congrArg (evalTensor (𝕜 := 𝕜) f) href
  rw [evalTensor_refHom, endpoint_toPLPath, map_sum] at heval
  simp only [Rat.cast_id] at heval
  have hsum : ∑ j, evalTensor (𝕜 := 𝕜) f (π.duration j • refHom X ((π.dir j).1 • lam)) =
      ∑ j, (π.duration j : 𝕜) • f ((π.dir j).1 • lam) :=
    Finset.sum_congr rfl fun j _ ↦ evalTensor_smul_refHom f _ _
  rw [endpoint_toPLPath, ← hsum, ← heval]

/-- When `f` is injective, `(normalCrystal hlam).wt π` is characterized by the endpoint of
`π.toPLPath 𝕜 f`. -/
theorem normalCrystal_wt_eq_iff {f : X →+ V} (hlam : lam ∈ dominantChamber P b)
    (hf : Function.Injective f) {π : LSPath P b lam} {μ : X} :
    (normalCrystal hlam).wt π = μ ↔ (π.toPLPath 𝕜 f).endpoint = f μ := by
  rw [endpoint_toPLPath_eq_apply_wt hlam π f, hf.eq_iff]

variable {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- In any coroot-compatible realization, `(normalCrystal hlam).ε i π` is `-min H_i(π)`. -/
theorem cast_normalCrystal_ε (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).ε i π : 𝕜) = -(π.toPLPath 𝕜 f).minHeight (F i) := by
  have href : ((normalCrystal hlam).ε i π : ℚ) =
      -(π.toPLPath ℚ (refHom X)).minHeight (refForm b i) := by
    simp [normalCrystal, refEquiv]
  obtain ⟨z, -, hz₀, hz⟩ := π.exists_intCast_minHeight_eq_and_minHeight_eq hlam i
    (refHom X) (refForm b i) (refForm_refHom b i) f (F i) (hF i)
  have hεq : (((normalCrystal hlam).ε i π : ℤ) : ℚ) = ((-z : ℤ) : ℚ) := by
    rw [Int.cast_natCast, href, hz₀, Int.cast_neg]
  have hε : ((normalCrystal hlam).ε i π : ℤ) = -z := Int.cast_injective hεq
  rw [hz, ← Int.cast_neg, ← hε, Int.cast_natCast]

/-- In any coroot-compatible realization, `(normalCrystal hlam).φ i π` is
`H_i(π)(1) - min H_i(π)`. -/
theorem cast_normalCrystal_φ (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).φ i π : 𝕜) =
      F i (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight (F i) := by
  have hdiff := congrArg (Int.cast (R := 𝕜)) ((normalCrystal hlam).φ_sub_ε i π)
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, cast_normalCrystal_ε hlam hF i π] at hdiff
  rw [endpoint_toPLPath_eq_apply_wt hlam π f, hF i]
  dsimp only [RootPairing.coroot', LinearMap.flip_apply] at hdiff ⊢
  linarith

/-- Littelmann's path raising operator on `π.toPLPath 𝕜 f` agrees with the canonical raising
operator `(normalCrystal hlam).e i` in every coroot-compatible realization. -/
theorem raise_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).e i π).map (·.toPLPath 𝕜 f) := by
  cases he : (normalCrystal hlam).e i π with
  | none =>
    rw [Option.map_none, PLPath.raise_eq_none_iff]
    have hε0 : (normalCrystal hlam).ε i π = 0 := (normalCrystal hlam).ε_eq_zero_iff.mpr he
    have hmin := cast_normalCrystal_ε hlam hF i π
    rw [hε0, Nat.cast_zero] at hmin
    linarith
  | some π' =>
    have href : PLPath.raise (refForm b i) (refHom X (P.root i)) (π.toPLPath ℚ (refHom X)) =
        some (π'.toPLPath ℚ (refHom X)) := by
      have he' : ((PLPath.normalCrystalOn (refHom_injective P) (refForm_refHom b)
          (isCrystalSet_range_toPLPath hlam (refForm_refHom b))).e i
          (refEquiv hlam π)).map (refEquiv hlam).symm = some π' := by
        simpa [normalCrystal] using he
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp he'
      have hy' : ((refEquiv hlam).symm y).toPLPath ℚ (refHom X) = y.1 :=
        congrArg Subtype.val ((refEquiv hlam).apply_symm_apply y)
      rw [hy']
      exact PLPath.normalCrystalOn_e_eq_some_iff.mp hy
    obtain ⟨π'', hπ'', hr⟩ := π.exists_raise_toPLPath_eq_some_and_eq_some hlam i
      (refHom X) (refForm b i) (refForm_refHom b i) f (F i) (hF i) href
    obtain rfl : π'' = π' := toPLPath_refHom_injective hlam hπ''
    simpa using hr

/-- Littelmann's path lowering operator on `π.toPLPath 𝕜 f` agrees with the canonical lowering
operator `(normalCrystal hlam).f i` in every coroot-compatible realization. -/
theorem lower_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).f i π).map (·.toPLPath 𝕜 f) := by
  cases hf' : (normalCrystal hlam).f i π with
  | none =>
    rw [Option.map_none, PLPath.lower_eq_none_iff]
    have hφ0 : (normalCrystal hlam).φ i π = 0 := (normalCrystal hlam).φ_eq_zero_iff.mpr hf'
    have hφ := cast_normalCrystal_φ hlam hF i π
    rw [hφ0, Nat.cast_zero] at hφ
    linarith
  | some π' =>
    have he : (normalCrystal hlam).e i π' = some π :=
      (normalCrystal hlam).f_eq_some_iff.mp hf'
    have hr : PLPath.raise (F i) (f (P.root i)) (π'.toPLPath 𝕜 f) = some (π.toPLPath 𝕜 f) := by
      rw [raise_toPLPath hlam hF i π', he, Option.map_some]
    have h2 : F i (f (P.root i)) = 2 := by simp [hF i]
    rw [Option.map_some, PLPath.lower_eq_some_iff h2]
    exact hr

/-- Iterated path raising commutes with `toPLPath 𝕜 f`. -/
theorem raiseIter_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (n : ℕ) (π : LSPath P b lam) :
    PLPath.raiseIter (F i) (f (P.root i)) n (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).eIter i n π).map (·.toPLPath 𝕜 f) := by
  induction n generalizing π with
  | zero => simp
  | succ n ih =>
    rw [PLPath.raiseIter_succ, NormalCrystal.eIter_succ, raise_toPLPath hlam hF i π]
    cases (normalCrystal hlam).e i π <;> simp [ih]

/-- Iterated path lowering commutes with `toPLPath 𝕜 f`. -/
theorem lowerIter_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (n : ℕ) (π : LSPath P b lam) :
    PLPath.lowerIter (F i) (f (P.root i)) n (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).fIter i n π).map (·.toPLPath 𝕜 f) := by
  induction n generalizing π with
  | zero => simp
  | succ n ih =>
    rw [PLPath.lowerIter_succ, NormalCrystal.fIter_succ, lower_toPLPath hlam hF i π]
    cases (normalCrystal hlam).f i π <;> simp [ih]

/-- Word raising commutes with `toPLPath 𝕜 f`. -/
theorem raiseWord_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    PLPath.raiseWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).eWord w π).map (·.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [PLPath.raiseWord_cons, NormalCrystal.eWord_cons, raise_toPLPath hlam hF i π]
    cases (normalCrystal hlam).e i π <;> simp [ih]

/-- Word lowering commutes with `toPLPath 𝕜 f`. -/
theorem lowerWord_toPLPath (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (w : List b.support) (π : LSPath P b lam) :
    PLPath.lowerWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) =
      ((normalCrystal hlam).fWord w π).map (·.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [PLPath.lowerWord_cons, NormalCrystal.fWord_cons, lower_toPLPath hlam hF i π]
    cases (normalCrystal hlam).f i π <;> simp [ih]

end Compatibility

/-! ### Highest-weight generation, connectedness, and pure-central shapes -/

section HighestAndConnected

/-- The straight path `straight λ` has crystal weight `λ`. -/
@[simp]
theorem normalCrystal_wt_straight (hlam : lam ∈ dominantChamber P b) :
    (normalCrystal hlam).wt (straight lam) = lam :=
  refHom_injective P <| by
    rw [← endpoint_toPLPath_eq_apply_wt (𝕜 := ℚ) hlam, toPLPath_straight, PLPath.endpoint_straight]

/-- **Uniqueness of the highest element of `B(λ)`**: an LS path of dominant shape `λ` is annihilated
by all raising operators if and only if it is `straight λ`. -/
theorem forall_normalCrystal_e_eq_none_iff (hlam : lam ∈ dominantChamber P b)
    {π : LSPath P b lam} :
    (∀ i, (normalCrystal hlam).e i π = none) ↔ π = straight lam := by
  have := P.flip_isReduced
  rw [← π.forall_raise_eq_none_iff hlam (refHom X) (refForm b) (refForm_refHom b)]
  refine forall_congr' fun i ↦ ?_
  rw [raise_toPLPath hlam (refForm_refHom b), Option.map_eq_none_iff]

@[simp]
theorem normalCrystal_e_straight (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (normalCrystal hlam).e i (straight lam) = none :=
  (forall_normalCrystal_e_eq_none_iff hlam).mpr rfl i

@[simp]
theorem normalCrystal_ε_straight (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (normalCrystal hlam).ε i (straight lam) = 0 :=
  (normalCrystal hlam).ε_eq_zero_iff.mpr (normalCrystal_e_straight hlam i)

@[simp]
theorem normalCrystal_φ_straight (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (normalCrystal hlam).φ i (straight lam) = (P.coroot' i lam).toNat := by
  have h := (normalCrystal hlam).φ_sub_ε i (straight lam)
  rw [normalCrystal_ε_straight, normalCrystal_wt_straight] at h
  dsimp only [RootPairing.coroot', LinearMap.flip_apply]
  omega

/-- **Highest-weight generation of `B(λ)`**: every Lakshmibai–Seshadri path of dominant shape `λ`
is obtained from `straight λ` by a word of lowering operators. -/
theorem exists_fWord_straight_eq_some (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).fWord w (straight lam) = some π := by
  have := P.flip_isReduced
  have := LSPath.finite (P := P) (b := b) hlam
  exact (normalCrystal hlam).exists_fWord_eq_some_of_unique_highest
    (fun _ hx ↦ (forall_normalCrystal_e_eq_none_iff hlam).mp hx) π

/-- Every Lakshmibai–Seshadri path of dominant shape `λ` can be raised to `straight λ` by a word of
raising operators. -/
theorem exists_eWord_eq_some_straight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).eWord w π = some (straight lam) := by
  obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
  exact ⟨w.reverse, (normalCrystal hlam).fWord_eq_some_iff.mp hw⟩

omit [Finite ι] [P.IsReduced] in
private theorem reachable_of_fWord_eq_some {B : Type*} (c : NormalCrystal P b B) :
    ∀ {w : List b.support} {x y : B}, c.fWord w x = some y → c.graph.Reachable x y
  | [], x, y, h => by
    rw [NormalCrystal.fWord_nil] at h
    obtain rfl := Option.some.inj h
    rfl
  | i :: w, x, y, h => by
    rw [NormalCrystal.fWord_cons] at h
    obtain ⟨z, hz, hw⟩ := Option.bind_eq_some_iff.mp h
    exact (c.graph_adj_of_f_eq_some hz).reachable.trans (reachable_of_fWord_eq_some c hw)

/-- Every Lakshmibai–Seshadri path of dominant shape `λ` is reachable from `straight λ` in the
crystal graph of `B(λ)`. -/
theorem reachable_straight_normalCrystal_graph (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (normalCrystal hlam).graph.Reachable (straight lam) π := by
  obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
  exact reachable_of_fWord_eq_some (normalCrystal hlam) hw

/-- **Connectedness of `B(λ)`**: the crystal graph of `normalCrystal hlam` is connected. -/
theorem connected_normalCrystal_graph (hlam : lam ∈ dominantChamber P b) :
    (normalCrystal hlam).graph.Connected where
  preconnected x y := (reachable_straight_normalCrystal_graph hlam x).symm.trans
    (reachable_straight_normalCrystal_graph hlam y)
  nonempty := ⟨straight lam⟩

/-- The crystal weight of `π` differs from its final orbit direction `(π.dir (Fin.last _)).1 • λ`
by an integral root-lattice vector. -/
theorem exists_mem_rootSpan_normalCrystal_wt_eq_add (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    ∃ m ∈ P.rootSpan ℤ, (normalCrystal hlam).wt π = (π.dir (Fin.last _)).1 • lam + m := by
  obtain ⟨m, hm, hend⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ) hlam (refHom X)
  rw [endpoint_toPLPath_eq_apply_wt hlam π (refHom X)] at hend
  exact ⟨m, hm, refHom_injective P hend⟩

/-- **Weight dominance in `B(λ)`**: for every `π : LSPath P b lam`, `λ - wt(π)` lies in the
nonnegative cone `Submodule.span ℕ (P.root '' b.support)` of simple roots. -/
theorem lam_sub_normalCrystal_wt_mem_span (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    lam - (normalCrystal hlam).wt π ∈ Submodule.span ℕ (P.root '' b.support) := by
  obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
  have hwt := (normalCrystal hlam).wt_of_fWord_eq_some hw
  rw [normalCrystal_wt_straight] at hwt
  have hsub : lam - (normalCrystal hlam).wt π = (w.map fun i : b.support ↦ P.root i).sum := by
    rw [hwt, sub_sub_cancel]
  rw [hsub]
  clear hwt hsub hw
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i.1, i.2, rfl⟩) ih

omit [Finite ι] [P.IsReduced] in
/-- A weight annihilating the simple coroots lies in the dominant chamber. -/
theorem mem_dominantChamber_of_forall_coroot_eq_zero
    (hlam₀ : ∀ i : b.support, P.toLinearMap lam (P.coroot i) = 0) :
    lam ∈ dominantChamber P b :=
  (mem_dominantChamber P b lam).mpr fun i hi ↦ by simp [RootPairing.coroot', hlam₀ ⟨i, hi⟩]

/-- When `λ` annihilates all simple coroots (including `λ = 0` and empty root systems), `straight λ`
is the unique Lakshmibai–Seshadri path of shape `λ`. -/
theorem eq_straight_of_forall_coroot_eq_zero
    (hlam₀ : ∀ i : b.support, P.toLinearMap lam (P.coroot i) = 0) (π : LSPath P b lam) :
    π = straight lam := by
  let hlam := mem_dominantChamber_of_forall_coroot_eq_zero hlam₀
  obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
  cases w with
  | nil =>
    rw [NormalCrystal.fWord_nil] at hw
    exact (Option.some.inj hw).symm
  | cons i w =>
    have hf0 : (normalCrystal hlam).f i (straight lam) = none := by
      rw [← (normalCrystal hlam).φ_eq_zero_iff, normalCrystal_φ_straight]
      simp [RootPairing.coroot', hlam₀ i]
    simp [NormalCrystal.fWord_cons, hf0] at hw

/-- When `λ` annihilates all simple coroots, `B(λ)` is strictly isomorphic to the one-element
central crystal `NormalCrystal.central λ`. -/
noncomputable def centralShapeIso
    (hlam₀ : ∀ i : b.support, P.toLinearMap lam (P.coroot i) = 0) :
    NormalCrystal.StrictIso (normalCrystal (mem_dominantChamber_of_forall_coroot_eq_zero hlam₀))
      (NormalCrystal.central lam hlam₀) where
  toEquiv :=
    { toFun := fun _ ↦ PUnit.unit
      invFun := fun _ ↦ straight lam
      left_inv := fun π ↦ (eq_straight_of_forall_coroot_eq_zero hlam₀ π).symm
      right_inv := fun _ ↦ rfl }
  wt_toFun π := by
    rw [eq_straight_of_forall_coroot_eq_zero hlam₀ π]
    simp
  e_toFun i π := by
    rw [eq_straight_of_forall_coroot_eq_zero hlam₀ π]
    simp

@[simp]
theorem centralShapeIso_symm_apply
    (hlam₀ : ∀ i : b.support, P.toLinearMap lam (P.coroot i) = 0) (u : PUnit) :
    (centralShapeIso hlam₀).symm u = straight lam :=
  eq_straight_of_forall_coroot_eq_zero hlam₀ _

end HighestAndConnected

/-! ### Path-set identifications and strict crystal isomorphisms into path crystals -/

section PathComparison

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}

omit [Finite ι] [P.IsReduced] in
private theorem reflTransGen_rootStep_of_lowerWord_eq_some :
    ∀ {w : List b.support} {p q : PLPath 𝕜 V},
      PLPath.lowerWord F (fun i ↦ f (P.root i)) w p = some q →
        ReflTransGen (PLPath.RootStep b f F) p q
  | [], p, q, h => by
    rw [PLPath.lowerWord_nil] at h
    obtain rfl := Option.some.inj h
    exact .refl
  | i :: w, p, q, h => by
    rw [PLPath.lowerWord_cons] at h
    obtain ⟨r, hr, hw⟩ := Option.bind_eq_some_iff.mp h
    exact .head (.of_lower_eq_some hr) (reflTransGen_rootStep_of_lowerWord_eq_some hw)

/-- **Generation of realized LS paths from the straight path**: in any coroot-compatible realization
`(f, F)` (injective or not), `Set.range (·.toPLPath 𝕜 f)` equals the set of piecewise-linear paths
obtained from `PLPath.straight 𝕜 (f lam)` by lowering along words of simple roots. -/
theorem range_toPLPath_eq_setOf_exists_lowerWord (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) =
      {p | ∃ w : List b.support,
        PLPath.lowerWord F (fun i ↦ f (P.root i)) w (PLPath.straight 𝕜 (f lam)) = some p} := by
  ext p
  constructor
  · rintro ⟨π, rfl⟩
    obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hlam π
    refine ⟨w, ?_⟩
    rw [← toPLPath_straight (P := P) (b := b) 𝕜 f,
      lowerWord_toPLPath hlam hF w (straight (P := P) (b := b) lam), hw, Option.map_some]
  · rintro ⟨w, hw⟩
    exact (isCrystalSet_range_toPLPath hlam hF).mem_of_reflTransGen_rootStep
      (reflTransGen_rootStep_of_lowerWord_eq_some hw)
      ⟨straight (P := P) (b := b) lam, toPLPath_straight (P := P) (b := b) 𝕜 f⟩

/-- **Component identification of realized LS paths**: in any coroot-compatible realization `(f, F)`
(injective or not), `Set.range (·.toPLPath 𝕜 f)` equals the connected root-step component of
`PLPath.straight 𝕜 (f lam)`. -/
theorem range_toPLPath_eq_setOf_reflTransGen_rootStep (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) =
      {p | ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) p} := by
  ext p
  constructor
  · intro hp
    rw [range_toPLPath_eq_setOf_exists_lowerWord hlam hF] at hp
    obtain ⟨w, hw⟩ := hp
    exact reflTransGen_rootStep_of_lowerWord_eq_some hw
  · intro hwalk
    exact (isCrystalSet_range_toPLPath hlam hF).mem_of_reflTransGen_rootStep hwalk
      ⟨straight (P := P) (b := b) lam, toPLPath_straight (P := P) (b := b) 𝕜 f⟩

/-- In any injective coroot-compatible realization `(f, F)`, `toPLPath 𝕜 f` is a strict crystal
isomorphism from `normalCrystal hlam` onto `PLPath.normalCrystalOn` on the realized LS paths. -/
noncomputable def toPLPathIso (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalOn hf hF (isCrystalSet_range_toPLPath hlam hF)) :=
  have := P.flip_isReduced
  let g : LSPath P b lam → range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :=
    fun π ↦ ⟨π.toPLPath 𝕜 f, mem_range_self π⟩
  have hg_bij : Function.Bijective g :=
    ⟨fun _ _ h ↦ toPLPath_injective_of_coroot' hlam hf.injOn hF (congrArg Subtype.val h),
      fun ⟨_, π, hπ⟩ ↦ ⟨π, Subtype.ext hπ⟩⟩
  { toEquiv := Equiv.ofBijective g hg_bij
    wt_toFun := fun π ↦ hf <| by
      rw [Equiv.toFun_as_coe, Equiv.ofBijective_apply, PLPath.apply_normalCrystalOn_wt]
      exact endpoint_toPLPath_eq_apply_wt hlam π f
    e_toFun := fun i π ↦ by
      rw [Equiv.toFun_as_coe, PLPath.normalCrystalOn_e_eq_map_iff, Equiv.ofBijective_apply]
      simpa [Equiv.ofBijective_apply, g] using raise_toPLPath hlam hF i π }

@[simp]
theorem toPLPathIso_apply (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    (toPLPathIso hlam hf hF π).1 = π.toPLPath 𝕜 f :=
  (rfl)

/-- **Comparison with Littelmann's path crystal component**: in any injective coroot-compatible
realization `(f, F)`, `toPLPath 𝕜 f` induces a strict crystal isomorphism from `normalCrystal hlam`
onto the connected component `PLPath.normalCrystalComponent` generated by
`PLPath.straight 𝕜 (f lam)` inside Littelmann's crystal of integral paths. -/
noncomputable def toComponentIso (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalComponent hf hF
        ⟨PLPath.straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :=
  have := P.flip_isReduced
  let x₀ : {p : PLPath 𝕜 V | PLPath.IsIntegralPath b f F p} :=
    ⟨PLPath.straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩
  have hmem (π : LSPath P b lam) :
      (⟨π.toPLPath 𝕜 f, π.isIntegralPath_toPLPath hlam hF⟩ :
        {p : PLPath 𝕜 V | PLPath.IsIntegralPath b f F p}) ∈
        ((PLPath.normalCrystal hf hF).graph.connectedComponentMk x₀).supp := by
    rw [PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff]
    change π.toPLPath 𝕜 f ∈ {p | ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) p}
    rw [← range_toPLPath_eq_setOf_reflTransGen_rootStep hlam hF]
    exact ⟨π, rfl⟩
  let g : LSPath P b lam → (PLPath.normalCrystal hf hF).graph.connectedComponentMk x₀ :=
    fun π ↦ ⟨⟨π.toPLPath 𝕜 f, π.isIntegralPath_toPLPath hlam hF⟩, hmem π⟩
  have hg_bij : Function.Bijective g :=
    ⟨fun _ _ h ↦ toPLPath_injective_of_coroot' hlam hf.injOn hF (congrArg (fun z ↦ z.1.1) h),
      fun ⟨⟨p, hp⟩, hc⟩ ↦ by
        have hwalk : ReflTransGen (PLPath.RootStep b f F) (PLPath.straight 𝕜 (f lam)) p :=
          (PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff x₀ ⟨p, hp⟩).mp hc
        have hr : p ∈ range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
          rw [range_toPLPath_eq_setOf_reflTransGen_rootStep hlam hF]
          exact hwalk
        obtain ⟨π, rfl⟩ := hr
        exact ⟨π, Subtype.ext (Subtype.ext rfl)⟩⟩
  { toEquiv := Equiv.ofBijective g hg_bij
    wt_toFun := fun π ↦ hf <| by
      rw [Equiv.toFun_as_coe, Equiv.ofBijective_apply, PLPath.normalCrystalComponent,
        NormalCrystal.component_eq_restrict, NormalCrystal.restrict_wt,
        PLPath.apply_normalCrystalOn_wt]
      exact endpoint_toPLPath_eq_apply_wt hlam π f
    e_toFun := fun i π ↦ by
      rw [Equiv.toFun_as_coe, Equiv.ofBijective_apply, PLPath.normalCrystalComponent,
        NormalCrystal.component_eq_restrict]
      cases he : (normalCrystal hlam).e i π with
      | none =>
        rw [Option.map_none]
        cases hr : ((PLPath.normalCrystal hf hF).restrict _ _).e i (g π) with
        | none => rfl
        | some y =>
          have hy := (PLPath.normalCrystalOn_e_eq_some_iff.mp
            (NormalCrystal.restrict_e_eq_some_iff.mp hr))
          dsimp only [g] at hy
          rw [raise_toPLPath hlam hF i π, he] at hy
          simp at hy
      | some π' =>
        rw [Option.map_some, Equiv.ofBijective_apply, NormalCrystal.restrict_e_eq_some_iff,
          PLPath.normalCrystalOn_e_eq_some_iff]
        dsimp only [g]
        rw [raise_toPLPath hlam hF i π, he, Option.map_some] }

@[simp]
theorem toComponentIso_apply (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    (toComponentIso hlam hf hF π).1.1 = π.toPLPath 𝕜 f :=
  (rfl)

end PathComparison

end TauCeti.LSPath
